"""Open-access mathematical-finance papers that are not on arXiv, through OpenAlex.

The arXiv corpus (``arxiv_scan``) holds the q-fin categories. Much of the field is published
elsewhere: journals, repositories, theses, SSRN. OpenAlex indexes it, so this lists the
open-access works of the field's topics that have no arXiv copy, and downloads a PDF for each
from where it is legally open.

    python3 -m tools.verify.openalex_corpus list --out <dir>/works.jsonl
    python3 -m tools.verify.openalex_corpus fetch --works <dir>/works.jsonl --dir <dir>/pdf
    python3 -m tools.verify.openalex_corpus cached --works <dir>/works.jsonl --dir <dir>/pdf

``list`` pages through OpenAlex (``OPENALEX_KEY_FILE``, a key file outside the repo). Listing
costs $0.10 per 1,000 calls, so the whole field costs about five cents. ``fetch`` downloads each
work's direct open-access PDF link, with one request every ``DELAY`` seconds per host (longer if
the host's robots.txt sets a Crawl-delay). It honours each host's robots.txt and keeps a file only
if it is a PDF. ``cached`` downloads OpenAlex's own cached copy for the works ``fetch`` could not
get. That costs $10 per 1,000 files, so it stops at ``--budget`` dollars a run.

SSRN is never fetched directly: its robots.txt bars AI crawlers. An SSRN paper is fetched only
through an open copy elsewhere or OpenAlex's cache. The PDFs are kept for local research and
never committed or redistributed.
"""

from __future__ import annotations

import argparse
import json
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import urllib.robotparser
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

API = "https://api.openalex.org/works"
CONTENT = "https://content.openalex.org/works"
OPENALEX_KEY_FILE = Path("/home/raphael/.config/openalex/key")
AGENT = "mathfin-corpus/0.1"
ARXIV = "S4306400194"  # OpenAlex's source id for arXiv
# Stochastic processes and financial applications; probability and risk models (actuarial).
TOPICS = ("T10067", "T11720")
DELAY = 2.0
NEVER = ("ssrn.com",)  # hosts whose robots.txt bars AI crawlers: never fetched directly
SELECT = ("id,doi,title,publication_year,type,language,primary_topic,primary_location,"
          "best_oa_location,locations,has_content,ids")


def _key() -> str:
    return OPENALEX_KEY_FILE.read_text().strip()


def _get(url: str, headers: dict | None = None, timeout: float = 60) -> tuple[bytes, str]:
    req = urllib.request.Request(url, headers={"User-Agent": AGENT, **(headers or {})})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read(), r.headers.get("Content-Type", "")


def list_works(topics=TOPICS, out: Path | None = None) -> int:
    """Every open-access work whose primary topic is one of `topics` and that has no arXiv
    location, one JSON line each (cursor paging, 100 per call)."""
    flt = f"primary_topic.id:{'|'.join(topics)},is_oa:true,locations.source.id:!{ARXIV}"
    cursor, n, cost = "*", 0, 0.0
    with out.open("w") as f:
        while cursor:
            q = urllib.parse.urlencode({"filter": flt, "per_page": 100, "cursor": cursor,
                                        "select": SELECT})
            for attempt in range(5):
                try:
                    body, _ = _get(f"{API}?{q}", {"Authorization": f"Bearer {_key()}"})
                    break
                except (OSError, urllib.error.HTTPError):
                    time.sleep(5 * 2 ** attempt)
            else:
                raise SystemExit("OpenAlex listing failed")
            d = json.loads(body)
            cost += d["meta"].get("cost_usd") or 0
            for w in d["results"]:
                f.write(json.dumps(w, ensure_ascii=False) + "\n")
                n += 1
            cursor = d["meta"].get("next_cursor")
    print(f"{n} works, ${cost:.4f}", file=sys.stderr)
    return n


def wid(work: dict) -> str:
    """`https://openalex.org/W123` → `W123`."""
    return work["id"].rsplit("/", 1)[-1]


def local_path(root: Path, work: dict) -> Path:
    """`<root>/W12/W123456.pdf`: a hundred-odd subdirectories by id prefix."""
    w = wid(work)
    return root / w[:3] / f"{w}.pdf"


def pdf_links(work: dict) -> list[str]:
    """The work's direct PDF links, best open-access location first, never an SSRN host."""
    links = [(work.get("best_oa_location") or {}).get("pdf_url")]
    links += [loc.get("pdf_url") for loc in work.get("locations") or []]
    out: list[str] = []
    for u in links:
        if u and u not in out and not any(h in urllib.parse.urlparse(u).netloc for h in NEVER):
            out.append(u)
    return out


def is_pdf(body: bytes) -> bool:
    return body[:1024].lstrip().startswith(b"%PDF")


class Robots:
    """robots.txt per host, fetched once; an unreadable robots.txt allows (the convention)."""

    def __init__(self) -> None:
        self.cache: dict[str, urllib.robotparser.RobotFileParser | None] = {}

    def allowed(self, url: str) -> bool:
        p = urllib.parse.urlparse(url)
        host = f"{p.scheme}://{p.netloc}"
        if host not in self.cache:
            rp = urllib.robotparser.RobotFileParser()
            try:
                body, _ = _get(f"{host}/robots.txt", timeout=20)
                rp.parse(body.decode("utf-8", "replace").splitlines())
                self.cache[host] = rp
            except (OSError, urllib.error.HTTPError, ValueError):
                self.cache[host] = None
        rp = self.cache[host]
        return rp is None or rp.can_fetch(AGENT, url)

    def delay(self, url: str) -> float:
        """The host's Crawl-delay, if its robots.txt sets one longer than `DELAY`."""
        p = urllib.parse.urlparse(url)
        rp = self.cache.get(f"{p.scheme}://{p.netloc}")
        asked = rp.crawl_delay(AGENT) if rp else None
        return max(DELAY, float(asked or 0))


def _save(dest: Path, body: bytes) -> None:
    dest.parent.mkdir(parents=True, exist_ok=True)
    tmp = dest.with_suffix(".part")
    tmp.write_bytes(body)
    tmp.rename(dest)


def fetch_host(jobs: list[tuple[dict, str]], root: Path, robots: Robots, delay: float = DELAY):
    """One host's downloads, one at a time, `delay` seconds apart."""
    for work, url in jobs:
        dest = local_path(root, work)
        if dest.exists():
            yield {"id": wid(work), "status": "ok", "url": url}
            continue
        if not robots.allowed(url):
            yield {"id": wid(work), "status": "robots", "url": url}
            continue
        try:
            body, ctype = _get(url, timeout=90)
            status = "ok" if is_pdf(body) else f"not-pdf ({ctype.split(';')[0]})"
        except urllib.error.HTTPError as err:
            body, status = b"", f"http-{err.code}"
        except (OSError, ValueError) as err:
            body, status = b"", f"error: {type(err).__name__}"
        if status == "ok":
            _save(dest, body)
        yield {"id": wid(work), "status": status, "url": url}
        time.sleep(max(delay, robots.delay(url)))


def fetch(works: list[dict], root: Path, workers: int = 16) -> dict:
    """Download each work's first direct PDF link, hosts in parallel and each host politely.
    Resumable: present files count as done, and a link that was refused (robots.txt, 4xx, not a
    PDF) is not asked again; a network error is retried. `root/fetched.jsonl` gets one line per
    attempt as it happens."""
    root.mkdir(parents=True, exist_ok=True)
    log_path = root / "fetched.jsonl"
    refused = set()
    if log_path.exists():
        refused = {r["id"] for r in map(json.loads, log_path.open())
                   if not r["status"].startswith(("ok", "error"))}
    by_host: dict[str, list[tuple[dict, str]]] = {}
    for w in works:
        links = pdf_links(w)
        if links and wid(w) not in refused:
            by_host.setdefault(urllib.parse.urlparse(links[0]).netloc, []).append((w, links[0]))
    robots, status, lock = Robots(), {}, threading.Lock()
    with log_path.open("a") as log:
        def run(jobs: list[tuple[dict, str]]) -> None:
            for r in fetch_host(jobs, root, robots):
                with lock:
                    log.write(json.dumps(r) + "\n")
                    log.flush()
                    key = r["status"].split(" ")[0]
                    status[key] = status.get(key, 0) + 1
                    if sum(status.values()) % 500 == 0:
                        print(json.dumps(status), file=sys.stderr, flush=True)
        with ThreadPoolExecutor(workers) as pool:
            list(pool.map(run, sorted(by_host.values(), key=len, reverse=True)))
    print(json.dumps(status), file=sys.stderr, flush=True)
    return status


def _cached_pdf(work_id: str, tries: int = 4) -> tuple[bytes, str]:
    """One cached PDF from the content API. A 429 is first a per-second rate limit: wait as
    OpenAlex's Retry-After says (10 s if it says nothing) and try again."""
    for attempt in range(tries):
        try:
            body, _ = _get(f"{CONTENT}/{work_id}.pdf", {"Authorization": f"Bearer {_key()}"},
                           timeout=120)
            return body, "ok" if is_pdf(body) else "not-pdf"
        except urllib.error.HTTPError as err:
            if err.code != 429 or attempt == tries - 1:
                return b"", f"http-{err.code}"
            time.sleep(float(err.headers.get("Retry-After") or 10))
        except (OSError, ValueError) as err:
            return b"", f"error: {type(err).__name__}"
    return b"", "http-429"


def cached(works: list[dict], root: Path, budget: float = 0.9) -> dict:
    """OpenAlex's cached PDF for each work that has one and is not yet on disk, until `budget`
    dollars are spent ($0.01 a file) or OpenAlex refuses (the day's allowance is gone). A work
    with a direct link is taken only once `fetch` has tried that link and failed, so nothing free
    is paid for; works with no direct link come first."""
    failed = set()  # direct downloads that were tried and did not give a PDF
    if (root / "fetched.jsonl").exists():
        failed = {r["id"] for r in map(json.loads, (root / "fetched.jsonl").open())
                  if r["status"] != "ok"}
    todo = [w for w in works if (w.get("has_content") or {}).get("pdf")
            and not local_path(root, w).exists()
            and (not pdf_links(w) or wid(w) in failed)]
    todo.sort(key=lambda w: bool(pdf_links(w)))  # the cache is the only route for these: first
    spent, attempted, status = 0.0, 0, {}
    with (root / "cached.jsonl").open("a") as log:
        for w in todo:
            if spent + 0.01 > budget + 1e-9:
                break
            body, st = _cached_pdf(wid(w))
            if st in ("http-402", "http-429"):
                status[st] = status.get(st, 0) + 1
                break  # refused even after waiting: the day's allowance is spent
            spent += 0.01
            attempted += 1
            if st == "ok":
                _save(local_path(root, w), body)
            log.write(json.dumps({"id": wid(w), "status": st}) + "\n")
            status[st] = status.get(st, 0) + 1
    status["remaining"] = len(todo) - attempted
    return status


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="openalex_corpus")
    sub = ap.add_subparsers(dest="cmd", required=True)
    a = sub.add_parser("list")
    a.add_argument("--out", type=Path, required=True)
    a.add_argument("--topics", nargs="*", default=list(TOPICS))
    f = sub.add_parser("fetch", help="download direct open-access PDFs (free)")
    f.add_argument("--works", type=Path, required=True)
    f.add_argument("--dir", type=Path, required=True)
    f.add_argument("--workers", type=int, default=16)
    c = sub.add_parser("cached", help="download OpenAlex's cached PDFs ($0.01 each)")
    c.add_argument("--works", type=Path, required=True)
    c.add_argument("--dir", type=Path, required=True)
    c.add_argument("--budget", type=float, default=0.9)
    args = ap.parse_args(argv)
    if args.cmd == "list":
        args.out.parent.mkdir(parents=True, exist_ok=True)
        list_works(tuple(args.topics), args.out)
        return 0
    works = [json.loads(line) for line in args.works.open()]
    if args.cmd == "fetch":
        print(json.dumps(fetch(works, args.dir, args.workers)))
    else:
        print(json.dumps(cached(works, args.dir, args.budget)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
