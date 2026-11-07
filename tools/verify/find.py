"""Search the library before writing anything: ``python3 -m tools.verify.find TERM…``.

The first step of every development (CLAUDE.md) is to find what the library already
has. This searches the declaration index (``tools/verify/decl_index.py``) by name,
docstring and statement, so a search for ``forward measure`` finds the declaration
whose docstring says so even when its name does not.

    python3 -m tools.verify.find forward measure
    python3 -m tools.verify.find --kind def numeraire
    python3 -m tools.verify.find --mentions IsEMM            # everything stated about IsEMM
    python3 -m tools.verify.find --used-by MathFin.IsExpQMartingale

``--index`` defaults to ``decl-index.json`` at the repo root (download the
``decl-index`` artifact of the latest ``build`` run on main, or build it with
``lake exe mathfin_index > decl-index.json`` with the daemon down).
"""

from __future__ import annotations

import argparse
import sys

from .decl_index import DeclIndex

DEFAULT_INDEX = "decl-index.json"


def _first_line(doc: str | None) -> str:
    if not doc:
        return ""
    line = doc.strip().splitlines()[0]
    return line if len(line) <= 110 else line[:107] + "…"


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="python3 -m tools.verify.find")
    ap.add_argument("terms", nargs="*")
    ap.add_argument("--index", default=DEFAULT_INDEX)
    ap.add_argument("--kind", help="theorem, def, structure, inductive, …")
    ap.add_argument("--mentions", help="a constant the statement or proof uses")
    ap.add_argument("--used-by", dest="used_by", help="list what uses this declaration")
    ap.add_argument("--limit", type=int, default=40)
    ap.add_argument("--types", action="store_true", help="print each statement")
    args = ap.parse_args(argv)

    idx = DeclIndex.load(args.index)
    if args.used_by:
        users = sorted(idx.used_by.get(args.used_by, ()))
        for u in users:
            d = idx.decls[u]
            print(f"{d.short_name}  ({d.path}:{d.line})")
        print(f"-- {len(users)} declaration(s) use {args.used_by}", file=sys.stderr)
        return 0
    if not args.terms and not args.mentions:
        ap.error("give search terms, --mentions or --used-by")
    hits = idx.find(*args.terms, kind=args.kind, mentions=args.mentions, limit=args.limit)
    for d in hits:
        flag = " [private]" if d.private else ""
        n_users = len(idx.used_by.get(d.name, ()))
        print(f"{d.kind:9} {d.short_name}{flag}  ({d.path}:{d.line}, used by {n_users})")
        if line := _first_line(d.doc):
            print(f"          {line}")
        if args.types:
            print(f"          : {d.type}")
    if not hits:
        print("-- no match", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
