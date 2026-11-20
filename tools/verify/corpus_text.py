"""Searchable text for the local paper corpora, one index over all of them.

Two corpora feed it: the q-fin arXiv papers (``arxiv_scan``) and the field's open-access papers
outside arXiv (``openalex_corpus``). Each lives in its own directory, with its manifest, ``pdf/``
and ``txt/``:

    <arxiv dir>/papers.jsonl     <arxiv dir>/pdf/2101/2101.00001v2.pdf
    <openalex dir>/works.jsonl   <openalex dir>/pdf/W12/W1234567.pdf

    python3 -m tools.verify.corpus_text text  --arxiv <dir> --openalex <dir>
    python3 -m tools.verify.corpus_text index --arxiv <dir> --openalex <dir> --db <corpus.db>
    python3 -m tools.verify.corpus_text search --db <corpus.db> '"remains open" NEAR uniqueness'

``text`` turns every kept PDF into text with Poppler's ``pdftotext``. Pages are separated by form
feeds, and each text sits beside its PDF's path under ``txt/``. The run is resumable. ``index``
loads all texts into one SQLite FTS5 index, one row per page, so a phrase finds its paper and
page in either corpus. ``search`` queries it. Texts and index stay local, like the PDFs.
"""

from __future__ import annotations

import argparse
import json
import re
import sqlite3
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from tools.verify import arxiv_scan, openalex_corpus


def arxiv_docs(root: Path) -> list[dict]:
    """The arXiv corpus in `root`: each paper's newest version on disk, and where its text goes."""
    docs = []
    for p in map(json.loads, (root / "papers.jsonl").open()):
        for v in range(p["version"], 0, -1):
            pdf = arxiv_scan.local_path(root / "pdf", p["id"], v)
            if pdf.exists():
                docs.append({"id": p["id"], "source": "arxiv", "pdf": pdf,
                             "txt": arxiv_scan.local_path(root / "txt", p["id"], v)
                                    .with_suffix(".txt"),
                             "title": p.get("title"), "published": p.get("published"),
                             "primary": p.get("primary"),
                             "categories": " ".join(p.get("categories", []))})
                break
    return docs


def openalex_docs(root: Path) -> list[dict]:
    """The OpenAlex corpus in `root`: each work whose PDF is on disk, and where its text goes."""
    docs = []
    for w in map(json.loads, (root / "works.jsonl").open()):
        pdf = openalex_corpus.local_path(root / "pdf", w)
        if pdf.exists():
            topic = w.get("primary_topic") or {}
            docs.append({"id": openalex_corpus.wid(w), "source": "openalex", "pdf": pdf,
                         "txt": openalex_corpus.local_path(root / "txt", w).with_suffix(".txt"),
                         "title": w.get("title"), "published": str(w.get("publication_year")),
                         "primary": topic.get("display_name"),
                         "categories": (topic.get("id") or "").rsplit("/", 1)[-1]})
    return docs


def text_one(doc: dict) -> str:
    """`pdftotext` one document, unless its text is already there; the status."""
    txt: Path = doc["txt"]
    if txt.exists():
        return "ok"
    txt.parent.mkdir(parents=True, exist_ok=True)
    part = txt.with_suffix(".part")
    try:
        run = subprocess.run(["pdftotext", "-enc", "UTF-8", str(doc["pdf"]), str(part)],
                             capture_output=True, timeout=300)
    except subprocess.TimeoutExpired:
        part.unlink(missing_ok=True)
        return "timeout"
    if run.returncode != 0 or not part.exists():
        part.unlink(missing_ok=True)
        return "pdftotext-failed"
    part.rename(txt)
    return "ok"


def text(docs: list[dict], workers: int = 8) -> dict:
    """Extract every document's text (resumable)."""
    status: dict[str, int] = {}
    with ThreadPoolExecutor(workers) as pool:
        for i, st in enumerate(pool.map(text_one, docs), 1):
            status[st] = status.get(st, 0) + 1
            if i % 1000 == 0:
                print(f"{i}/{len(docs)} {status}", file=sys.stderr)
    return status


SCHEMA = """
CREATE TABLE papers (id TEXT PRIMARY KEY, source TEXT, title TEXT, published TEXT,
    primary_category TEXT, categories TEXT);
CREATE VIRTUAL TABLE pages USING fts5(id UNINDEXED, page UNINDEXED, body,
    tokenize = 'porter unicode61 remove_diacritics 2');
"""


def pages_of(raw: str) -> list[str]:
    """A text's pages as searchable prose: hyphenated line breaks rejoined, lines joined."""
    return [re.sub(r"\s*\n\s*", " ", re.sub(r"(\w)-\n(\w)", r"\1\2", p)).strip()
            for p in raw.split("\f")]


def index(docs: list[dict], db: Path) -> dict:
    """Load every extracted text into `db`, one FTS5 row per page (rebuilt from scratch)."""
    db.unlink(missing_ok=True)
    con = sqlite3.connect(db)
    con.executescript(SCHEMA)
    counts: dict[str, int] = {"pages": 0}
    for d in docs:
        if not d["txt"].exists():
            continue
        con.execute("INSERT INTO papers VALUES (?,?,?,?,?,?)",
                    (d["id"], d["source"], d["title"], d["published"], d["primary"],
                     d["categories"]))
        rows = [(d["id"], k, body) for k, body in
                enumerate(pages_of(d["txt"].read_text("utf-8", "replace")), 1) if body]
        con.executemany("INSERT INTO pages VALUES (?,?,?)", rows)
        counts[d["source"]] = counts.get(d["source"], 0) + 1
        counts["pages"] += len(rows)
    con.commit()
    con.execute("INSERT INTO pages(pages) VALUES ('optimize')")
    con.commit()
    con.close()
    return counts


def search(db: Path, query: str, limit: int = 20) -> list[dict]:
    """FTS5 query (phrases in double quotes, NEAR, AND/OR/NOT, prefix*) over the pages, best
    match first: each hit's paper, source, page, title and a snippet with the match in
    [brackets]."""
    con = sqlite3.connect(db)
    rows = con.execute(
        "SELECT pages.id, papers.source, pages.page, papers.title, papers.published, "
        "snippet(pages, 2, '[', ']', ' … ', 24) FROM pages JOIN papers USING (id) "
        "WHERE pages MATCH ? ORDER BY rank LIMIT ?", (query, limit)).fetchall()
    con.close()
    return [dict(zip(("id", "source", "page", "title", "published", "snippet"), r))
            for r in rows]


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="corpus_text")
    sub = ap.add_subparsers(dest="cmd", required=True)
    for name in ("text", "index"):
        p = sub.add_parser(name)
        p.add_argument("--arxiv", type=Path, help="the arXiv corpus directory")
        p.add_argument("--openalex", type=Path, help="the OpenAlex corpus directory")
        if name == "text":
            p.add_argument("--workers", type=int, default=8)
        else:
            p.add_argument("--db", type=Path, required=True)
    q = sub.add_parser("search")
    q.add_argument("--db", type=Path, required=True)
    q.add_argument("query")
    q.add_argument("--limit", type=int, default=20)
    args = ap.parse_args(argv)
    if args.cmd == "search":
        for h in search(args.db, args.query, args.limit):
            print(f"{h['id']} p.{h['page']}  {h['title']} ({(h['published'] or '')[:4]}, "
                  f"{h['source']})\n    {h['snippet']}")
        return 0
    docs = (arxiv_docs(args.arxiv) if args.arxiv else []) + \
           (openalex_docs(args.openalex) if args.openalex else [])
    if args.cmd == "text":
        print(json.dumps(text(docs, args.workers)))
    else:
        print(json.dumps(index(docs, args.db)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
