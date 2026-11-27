"""The cátedra's state in the catalogue: pins, Referee verdicts, attempts, and the next chair.

The cátedra (`docs/specs/2026-11-20-catedra-design.md`) is six agent chairs working the
open-problem catalogue, `docs/research-problems/problems.json`. Three record fields carry its
state:

- `formalization.lean_statement.pinned`: the merge that pinned the Lean statement
  (`commit`, `pr`) and `statement_sha256`, the hash of the declaration's text from `theorem`
  to its `:=`, whitespace collapsed. A statement changes only through a pull request that says
  why, and that pull request updates the hash; `check` fails on any other change.
- `review.referee`: the Referee's verdict on faithfulness (`faithful`,
  `faithful_with_narrowing`, `not_faithful`), its `date` and the `comment` URL.
- `attempts`: how many times each chair has worked the problem.

Every stated problem also has a comparator config, `comparator/<id>.json`, which `lake comparator`
reads once a solution module exists (`.github/workflows/comparator.yml`).

`next_chair` is the rule the `/catedra` skill follows. `check` holds the fields to their shapes.

    python3 -m tools.verify.catedra status MF-OP-017
    python3 -m tools.verify.catedra check
    python3 -m tools.verify.catedra hash MF-OP-017
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

from . import research_problems as rp

CHAIRS = ("scout", "formalizer", "referee", "prover", "disprover", "builder")
VERDICTS = frozenset({"faithful", "faithful_with_narrowing", "not_faithful"})
FRONTIER = Path("MathFinFrontier")
COMPARATOR = Path("comparator")
REFEREE_ROUNDS = 2  # a not-faithful verdict goes back to the Formalizer twice, then to the maintainer


def declaration(name: str, root: Path = FRONTIER) -> tuple[Path, str] | None:
    """The file stating `theorem <name>`, and the declaration's text up to its `:=`."""
    pat = re.compile(rf"^theorem {re.escape(name)}\b(.*?):=", re.S | re.M)
    for p in sorted(root.rglob("*.lean")):
        m = pat.search(p.read_text(encoding="utf-8"))
        if m:
            return p, m.group(0)
    return None


def statement_hash(text: str) -> str:
    return hashlib.sha256(" ".join(text.split()).encode()).hexdigest()


def module_of(path: Path) -> str:
    return ".".join(path.with_suffix("").parts)


def next_chair(r: dict) -> tuple[str | None, str]:
    """The chair that works the record next, and why."""
    ls = r["formalization"]["lean_statement"]
    status, ref = ls["status"], (r.get("review") or {}).get("referee")
    if status in ("proved", "not_a_proposition"):
        return None, f"lean status `{status}`: nothing to do"
    if status == "blocked":
        return "builder", f"blocked on {', '.join(ls['needs'])}"
    if status == "statable":
        return "formalizer", "statable, not yet stated"
    if not ls.get("pinned"):
        return "referee", "stated in an open pull request: review it before the maintainer pins it"
    if ref is None:
        return "referee", "pinned, never refereed"
    if ref["verdict"] == "not_faithful":
        if r.get("attempts", {}).get("referee", 0) > REFEREE_ROUNDS:
            return None, "not faithful after two rounds: the maintainer decides"
        return "formalizer", "the Referee found it not faithful"
    return "prover", (f"pinned and refereed ({ref['verdict']}); name the disprover instead "
                      "when the conjectured direction is in doubt")


def problems(records: list[dict], root: Path = FRONTIER,
             comparator: Path = COMPARATOR) -> list[str]:
    """What is wrong with the records' cátedra fields, as messages."""
    out = []
    for r in records:
        rid, ls = r["id"], r["formalization"]["lean_statement"]
        pin, ref = ls.get("pinned"), (r.get("review") or {}).get("referee")
        for chair, n in (r.get("attempts") or {}).items():
            if chair not in CHAIRS or not isinstance(n, int) or n < 0:
                out.append(f"{rid}: attempts `{chair}: {n}` (chairs are {', '.join(CHAIRS)})")
        if ref is not None and (ref.get("verdict") not in VERDICTS or not ref.get("comment")
                                or not ref.get("date")):
            out.append(f"{rid}: review.referee needs a verdict in {sorted(VERDICTS)}, "
                       "a date and a comment URL")
        if ls["status"] != "stated":
            if pin:
                out.append(f"{rid}: pinned, but the lean status is {ls['status']}")
            continue
        found = declaration(ls["lean"], root)
        if found is None:
            continue  # research_problems.problems reports a missing statement
        path, text = found
        if pin:
            if not re.fullmatch(r"[0-9a-f]{40}", pin.get("commit", "")) or \
                    not isinstance(pin.get("pr"), int):
                out.append(f"{rid}: pinned needs the full merge `commit` and the `pr` number")
            if pin.get("statement_sha256") != statement_hash(text):
                out.append(f"{rid}: `{ls['lean']}` no longer matches its pinned statement; a "
                           "statement changes only through a pull request that says why and "
                           "updates `statement_sha256`")
        cfg_path = comparator / f"{rid}.json"
        if not cfg_path.exists():
            out.append(f"{rid}: stated, but has no comparator config {cfg_path}")
            continue
        cfg = json.loads(cfg_path.read_text(encoding="utf-8"))
        if cfg.get("challenge_module") != module_of(path) or ls["lean"] not in cfg.get(
                "theorem_names", []):
            out.append(f"{rid}: {cfg_path} must name the challenge {module_of(path)} and the "
                       f"theorem {ls['lean']}")
    return out


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="catedra")
    ap.add_argument("cmd", choices=["status", "check", "hash"])
    ap.add_argument("id", nargs="?")
    args = ap.parse_args(argv)
    records = rp.load()
    if args.cmd == "check":
        errs = problems(records)
        for e in errs:
            print(e)
        print(f"cátedra fields: {len(records)} records, {len(errs)} problem(s)")
        return 1 if errs else 0
    r = next((x for x in records if x["id"] == args.id), None)
    if r is None:
        ap.error(f"no record {args.id}")
    ls = r["formalization"]["lean_statement"]
    found = ls.get("lean") and declaration(ls["lean"])
    if args.cmd == "hash":
        if not found:
            ap.error(f"{args.id} has no statement in {FRONTIER}/")
        print(statement_hash(found[1]))
        return 0
    chair, why = next_chair(r)
    print(json.dumps({"id": r["id"], "title": r["title"],
                      "mathematical_status": r["mathematical_status"],
                      "lean_status": ls["status"], "lean": ls.get("lean"),
                      "file": str(found[0]) if found else None,
                      "blueprint": ls.get("blueprint"), "pinned": ls.get("pinned"),
                      "referee": (r.get("review") or {}).get("referee"),
                      "attempts": r.get("attempts", {}), "issue": r.get("issue_url"),
                      "next": chair, "why": why}, indent=1, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
