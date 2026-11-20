"""Find the sentences where finance papers say something is open.

Web search returns what a field works on, not what it admits it cannot do
(docs/open-problems.md, round 5). An author's sentence "it remains open whether ..." is
itself class-A evidence, so this scans full texts for such sentences instead.

    python3 -m tools.verify.arxiv_scan list --out scan/papers.jsonl
    python3 -m tools.verify.arxiv_scan scan --papers scan/papers.jsonl --out scan/
    python3 -m tools.verify.arxiv_scan fetch --papers scan/papers.jsonl --dir <pdf dir>

``list`` pages through the arXiv API for the q-fin categories that carry mathematical
finance (cross-lists included), one request every three seconds as the API terms ask.
``scan`` reads each paper's PDF from the public ``arxiv-dataset`` bucket on Google Cloud
Storage, the full-text copy behind arXiv's Kaggle dataset, which arXiv's bulk-data page
names as a sanctioned source. Only the matching passages are kept, with the paper's id and
page: full texts are never stored or redistributed (arXiv's terms of use). The passages are
leads for the catalogue (docs/research-problems/), each still to be checked for a later
resolution. ``fetch`` downloads and keeps the PDFs instead, for local research use (arXiv's
terms allow storing them for research; they are not to be redistributed, so never commit them).
"""

from __future__ import annotations

import argparse
import http.client
import json
import re
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

CATEGORIES = ("q-fin.MF", "q-fin.PR", "q-fin.RM", "q-fin.PM", "q-fin.TR")
API = "https://export.arxiv.org/api/query"
BUCKET = "https://storage.googleapis.com/arxiv-dataset/arxiv"
AGENT = "mathfin-arxiv-scan/0.1"
ATOM = {"a": "http://www.w3.org/2005/Atom", "arxiv": "http://arxiv.org/schemas/atom"}

# Each pattern is an author's own statement that something is not known. Case-insensitive
# unless the pattern says otherwise; "is open" alone is left out (open sets, open intervals).
PATTERNS: dict[str, re.Pattern[str]] = {k: re.compile(v, re.I) for k, v in {
    "remains-open": r"\b(?:remains?|remained|is still|are still|is currently|stays?)\s+"
                    r"(?:an?\s+|largely\s+|completely\s+|widely\s+|wide\s+)?open\b",
    "open-problem": r"\bopen\s+(?:problems?|questions?|conjectures?|issues?)\b",
    "conjecture": r"\b(?:we|i)\s+conjecture\b|\bconjectured?\s+that\b|\bit\s+is\s+conjectured\b",
    "not-known": r"\bit\s+is\s+(?:not\s+known|unknown|unclear|not\s+clear)\s+(?:whether|if|how)\b"
                 r"|\bwe\s+do\s+not\s+know\s+(?:whether|if|how)\b"
                 r"|\b(?:has|have)\s+not\s+(?:yet\s+)?been\s+(?:proved|proven|established|"
                 r"resolved|settled|answered)\b",
    "unsolved": r"\b(?:unsolved|unanswered|unresolved)\b",
    "left-open": r"\bleft\s+(?:as\s+an?\s+)?open\b|\bleave\s+(?:this|it|the\s+\w+)\s+"
                 r"(?:as\s+an?\s+)?open\b",
}.items()}
# Numbered statements: "Conjecture 3.1", "Open Problem 2" (case-sensitive: headings).
PATTERNS["numbered"] = re.compile(r"\b(?:Conjecture|Open\s+Problem|Open\s+Question)\s+\d+(?:\.\d+)*\b")

_REFERENCES = re.compile(r"^\s*(?:References|REFERENCES|Bibliography|BIBLIOGRAPHY)\s*$", re.M)
_SENTENCE_END = re.compile(r"(?<=[.!?])\s+(?=[A-Z(\[])")


def clean(text: str) -> str:
    """pdftotext output as running prose: rejoin hyphenated line breaks and lines, and cut
    the bibliography (its titles are full of 'open problem')."""
    cut = [m.start() for m in _REFERENCES.finditer(text)]
    if cut and cut[-1] > len(text) // 3:
        text = text[:cut[-1]]
    text = re.sub(r"(\w)-\n(\w)", r"\1\2", text)
    return text


def hits(text: str, width: int = 1) -> list[dict]:
    """Every passage matching a pattern: the sentence with `width` sentences either side, its
    page (pdftotext separates pages by form feeds), and which patterns it matched."""
    out: list[dict] = []
    for page_no, page in enumerate(clean(text).split("\f"), start=1):
        prose = re.sub(r"\s*\n\s*", " ", page)
        sents = _SENTENCE_END.split(prose)
        for i, s in enumerate(sents):
            keys = [k for k, p in PATTERNS.items() if p.search(s)]
            if not keys:
                continue
            ctx = " ".join(sents[max(0, i - width): i + width + 1]).strip()
            if out and out[-1]["page"] == page_no and s in out[-1]["context"]:
                out[-1]["patterns"] = sorted(set(out[-1]["patterns"]) | set(keys))
                continue
            out.append({"page": page_no, "patterns": keys, "context": ctx[:900]})
    return out


def _get(url: str, timeout: float = 60) -> bytes:
    req = urllib.request.Request(url, headers={"User-Agent": AGENT})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read()


def _get_retrying(url: str, tries: int = 4) -> bytes:
    """`_get`, retrying a dropped connection or a server error with backoff (a 404 is final)."""
    for attempt in range(tries):
        try:
            return _get(url, timeout=120)
        except urllib.error.HTTPError as err:
            if err.code < 500 or attempt == tries - 1:
                raise
        except (OSError, http.client.HTTPException):
            if attempt == tries - 1:
                raise
        time.sleep(5 * 2 ** attempt)
    raise AssertionError("unreachable")


def list_papers(categories=CATEGORIES, page: int = 1000, delay: float = 3.1) -> dict[str, dict]:
    """Every paper listed in the categories (cross-lists included), newest version, by id."""
    papers: dict[str, dict] = {}
    for cat in categories:
        start = 0
        while True:
            q = urllib.parse.urlencode({"search_query": f"cat:{cat}", "start": start,
                                        "max_results": page, "sortBy": "submittedDate",
                                        "sortOrder": "ascending"})
            for attempt in range(6):
                time.sleep(delay * (1 + 3 * attempt))
                try:
                    root = ET.fromstring(_get(f"{API}?{q}"))
                except (urllib.error.URLError, ET.ParseError, TimeoutError):
                    continue
                entries = root.findall("a:entry", ATOM)
                if entries and entries[0].findtext("a:title", "", ATOM) == "Error":
                    continue
                break
            else:
                raise RuntimeError(f"arXiv API failed for {cat} at {start}")
            if not entries:
                break
            for e in entries:
                full = e.findtext("a:id", "", ATOM).rsplit("/abs/", 1)[-1]
                m = re.match(r"(.+?)v(\d+)$", full)
                pid, ver = (m.group(1), int(m.group(2))) if m else (full, 1)
                rec = papers.setdefault(pid, {
                    "id": pid, "version": ver,
                    "title": " ".join(e.findtext("a:title", "", ATOM).split()),
                    "published": e.findtext("a:published", "", ATOM)[:10],
                    "primary": e.find("arxiv:primary_category", ATOM).get("term"),
                    "categories": [c.get("term") for c in e.findall("a:category", ATOM)]})
                rec["version"] = max(rec["version"], ver)
            print(f"{cat}: {start + len(entries)} listed, {len(papers)} distinct", file=sys.stderr)
            start += len(entries)
    return papers


def pdf_url(pid: str, version: int) -> str:
    """The bucket's path: new ids `2101.00001` sit under arxiv/pdf/2101/, old ids
    `math/0501001` under math/pdf/0501/."""
    if "/" in pid:
        archive, num = pid.split("/")
        return f"{BUCKET}/{archive}/pdf/{num[:4]}/{num}v{version}.pdf"
    return f"{BUCKET}/arxiv/pdf/{pid.split('.')[0]}/{pid}v{version}.pdf"


def scan_one(paper: dict) -> dict:
    """Fetch the newest version the bucket has, extract its text, and return its hits."""
    for v in range(paper["version"], 0, -1):
        try:
            pdf = _get(pdf_url(paper["id"], v), timeout=120)
        except urllib.error.HTTPError as err:
            if err.code == 404:
                continue
            return {"id": paper["id"], "status": f"http-{err.code}"}
        except (urllib.error.URLError, TimeoutError) as err:
            return {"id": paper["id"], "status": f"error: {err}"}
        with tempfile.NamedTemporaryFile(suffix=".pdf") as f:
            f.write(pdf)
            f.flush()
            run = subprocess.run(["pdftotext", "-enc", "UTF-8", f.name, "-"],
                                 capture_output=True, timeout=180)
        if run.returncode != 0:
            return {"id": paper["id"], "status": "pdftotext-failed", "version": v}
        return {"id": paper["id"], "status": "ok", "version": v,
                "hits": hits(run.stdout.decode("utf-8", "replace"))}
    return {"id": paper["id"], "status": "missing"}


def local_path(root: Path, pid: str, version: int) -> Path:
    """Where `fetch` keeps a paper: `<root>/2101/2101.00001v2.pdf`, `<root>/math/0501/0501001v1.pdf`."""
    if "/" in pid:
        archive, num = pid.split("/")
        return root / archive / num[:4] / f"{num}v{version}.pdf"
    return root / pid.split(".")[0] / f"{pid}v{version}.pdf"


def fetch_one(paper: dict, root: Path) -> dict:
    """Download the newest version the bucket has into `root`, unless it is already there."""
    for v in range(paper["version"], 0, -1):
        dest = local_path(root, paper["id"], v)
        if dest.exists():
            return {"id": paper["id"], "status": "ok", "version": v, "path": str(dest)}
    for v in range(paper["version"], 0, -1):
        try:
            pdf = _get_retrying(pdf_url(paper["id"], v))
        except urllib.error.HTTPError as err:
            if err.code == 404:
                continue
            return {"id": paper["id"], "status": f"http-{err.code}"}
        except (OSError, http.client.HTTPException) as err:
            return {"id": paper["id"], "status": f"error: {err}"}
        dest = local_path(root, paper["id"], v)
        dest.parent.mkdir(parents=True, exist_ok=True)
        tmp = dest.with_suffix(".part")
        tmp.write_bytes(pdf)
        tmp.rename(dest)
        return {"id": paper["id"], "status": "ok", "version": v, "path": str(dest)}
    return {"id": paper["id"], "status": "missing"}


def fetch(papers: list[dict], root: Path, workers: int = 4) -> dict:
    """Download every paper's PDF into `root` (resumable: present files are skipped), and write
    `root/fetched.jsonl`, one status line per paper."""
    root.mkdir(parents=True, exist_ok=True)
    status: dict[str, int] = {}
    with ThreadPoolExecutor(workers) as pool, (root / "fetched.jsonl").open("w") as log:
        for i, r in enumerate(pool.map(lambda p: fetch_one(p, root), papers), start=1):
            log.write(json.dumps(r) + "\n")
            key = r["status"] if r["status"] in ("ok", "missing") else "error"
            status[key] = status.get(key, 0) + 1
            if i % 200 == 0:
                log.flush()
                print(f"{i}/{len(papers)} {status}", file=sys.stderr)
    return status


def scan(papers: list[dict], out: Path, workers: int = 4, minutes: float = 330) -> dict:
    """Scan the papers not yet in `out/done.jsonl`, appending as it goes, until done or out
    of time. Resumable: a rerun skips what is done."""
    out.mkdir(parents=True, exist_ok=True)
    done_path, hits_path = out / "done.jsonl", out / "hits.jsonl"
    done = {json.loads(l)["id"] for l in done_path.open()} if done_path.exists() else set()
    todo = [p for p in papers if p["id"] not in done]
    meta = {p["id"]: p for p in papers}
    deadline = time.monotonic() + 60 * minutes
    with ThreadPoolExecutor(workers) as pool, done_path.open("a") as dl, hits_path.open("a") as hl:
        for chunk in range(0, len(todo), 200):
            if time.monotonic() > deadline:
                break
            for r in pool.map(scan_one, todo[chunk:chunk + 200]):
                for h in r.pop("hits", []):
                    p = meta[r["id"]]
                    hl.write(json.dumps({"id": r["id"], "version": r["version"],
                                         "title": p["title"], "published": p["published"],
                                         "primary": p["primary"], **h}, ensure_ascii=False) + "\n")
                dl.write(json.dumps(r) + "\n")
            dl.flush()
            hl.flush()
            print(f"{min(chunk + 200, len(todo))}/{len(todo)} scanned", file=sys.stderr)
    return summarize(out)


def summarize(out: Path) -> dict:
    done = [json.loads(l) for l in (out / "done.jsonl").open()]
    hs = [json.loads(l) for l in (out / "hits.jsonl").open()] if (out / "hits.jsonl").exists() else []
    status: dict[str, int] = {}
    for d in done:
        key = d["status"] if d["status"] in ("ok", "missing", "pdftotext-failed") else "error"
        status[key] = status.get(key, 0) + 1
    by_pattern: dict[str, int] = {}
    for h in hs:
        for k in h["patterns"]:
            by_pattern[k] = by_pattern.get(k, 0) + 1
    s = {"papers_scanned": len(done), "status": status, "hits": len(hs),
         "papers_with_hits": len({h["id"] for h in hs}), "hits_by_pattern": by_pattern}
    (out / "summary.json").write_text(json.dumps(s, indent=2) + "\n")
    return s


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="arxiv_scan")
    sub = ap.add_subparsers(dest="cmd", required=True)
    a = sub.add_parser("list")
    a.add_argument("--out", type=Path, required=True)
    a.add_argument("--categories", nargs="*", default=list(CATEGORIES))
    f = sub.add_parser("fetch", help="download and keep the PDFs (no scanning)")
    f.add_argument("--papers", type=Path, required=True)
    f.add_argument("--dir", type=Path, required=True)
    f.add_argument("--workers", type=int, default=4)
    b = sub.add_parser("scan")
    b.add_argument("--papers", type=Path, required=True)
    b.add_argument("--out", type=Path, required=True)
    b.add_argument("--limit", type=int, default=0, help="scan at most this many (0: all)")
    b.add_argument("--workers", type=int, default=4)
    b.add_argument("--minutes", type=float, default=330)
    args = ap.parse_args(argv)
    if args.cmd == "list":
        papers = list_papers(args.categories)
        args.out.parent.mkdir(parents=True, exist_ok=True)
        with args.out.open("w") as f:
            for p in sorted(papers.values(), key=lambda p: p["id"]):
                f.write(json.dumps(p, ensure_ascii=False) + "\n")
        print(f"{len(papers)} papers", file=sys.stderr)
        return 0
    papers = [json.loads(l) for l in args.papers.open()]
    if args.cmd == "fetch":
        print(json.dumps(fetch(papers, args.dir, args.workers)))
        return 0
    if args.limit:
        papers = papers[:args.limit]
    print(json.dumps(scan(papers, args.out, args.workers, args.minutes), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
