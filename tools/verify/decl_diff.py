"""What a change did to the library's declarations: ``decl_diff BASE HEAD``.

Physlib's ``check_golf`` (a PR changes proofs, not statements) and ``pr_summary`` (a
declaration-level changelog) are both a diff of two declaration indexes, so they are one
tool here. Given the ``decl-index.json`` of the base and of the head:

* **added** / **removed** declarations;
* **renamed**: removed and added with the same statement hash and kind (the release
  notes list renames, since CLAUDE.md leaves no alias behind);
* **statement changed**: same name, different statement hash. A golf or refactor PR
  should have none; an entry here is a changed claim, and the ledger re-verifies its
  corpus entries.

    python3 -m tools.verify.decl_diff base.json head.json            # markdown summary
    python3 -m tools.verify.decl_diff base.json head.json --no-statement-changes   # gate

Exit status 1 under ``--no-statement-changes`` when any public statement changed.
Statement hashes are stable within a toolchain; across a pin bump every hash may move,
so the diff refuses to compare indexes built on different toolchains.
"""

from __future__ import annotations

import argparse
from collections import defaultdict

from .decl_index import DeclIndex, IndexedDecl


def diff(base: DeclIndex, head: DeclIndex):
    b, h = base.decls, head.decls
    removed = [b[n] for n in b.keys() - h.keys()]
    added = [h[n] for n in h.keys() - b.keys()]
    changed = [(b[n], h[n]) for n in b.keys() & h.keys()
               if b[n].type_hash != h[n].type_hash]

    by_sig: dict[tuple[str, str], list[IndexedDecl]] = defaultdict(list)
    for d in added:
        by_sig[(d.kind, d.type_hash)].append(d)
    renamed: list[tuple[IndexedDecl, IndexedDecl]] = []
    for d in sorted(removed, key=lambda d: d.name):
        cands = by_sig.get((d.kind, d.type_hash))
        if cands:
            renamed.append((d, cands.pop(0)))
    renamed_old = {o.name for o, _ in renamed}
    renamed_new = {n.name for _, n in renamed}
    removed = sorted((d for d in removed if d.name not in renamed_old), key=lambda d: d.name)
    added = sorted((d for d in added if d.name not in renamed_new), key=lambda d: d.name)
    changed.sort(key=lambda p: p[0].name)
    return added, removed, renamed, changed


def _public(ds):
    return [d for d in ds if not d.private]


def render(added, removed, renamed, changed) -> str:
    out = ["## Declaration changes", ""]
    pub_changed = [(o, n) for o, n in changed if not n.private]
    out.append(
        f"{len(_public(added))} added, {len(_public(removed))} removed, "
        f"{len([1 for o, n in renamed if not n.private])} renamed, "
        f"**{len(pub_changed)} statement(s) changed** (public declarations; private ones "
        "are listed but not counted).")

    def section(title, rows):
        if rows:
            out.extend(["", f"### {title}", ""])
            out.extend(rows)

    section("Statement changed", [
        f"- `{n.short_name}`{' (private)' if n.private else ''} — `{n.path}:{n.line}`"
        for o, n in changed])
    section("Renamed", [
        f"- `{o.short_name}` → `{n.short_name}`{' (private)' if n.private else ''}"
        for o, n in renamed])
    section("Removed", [f"- `{d.short_name}` ({d.kind})" for d in _public(removed)])
    section("Added", [f"- `{d.short_name}` ({d.kind}) — `{d.path}:{d.line}`"
                      for d in _public(added)])
    return "\n".join(out) + "\n"


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="python3 -m tools.verify.decl_diff")
    ap.add_argument("base")
    ap.add_argument("head")
    ap.add_argument("--no-statement-changes", action="store_true",
                    help="exit 1 if any public statement changed (golf/refactor gate)")
    args = ap.parse_args(argv)
    base, head = DeclIndex.load(args.base), DeclIndex.load(args.head)
    if base.toolchain != head.toolchain:
        print(f"toolchains differ ({base.toolchain} vs {head.toolchain}): statement hashes "
              "are not comparable across a pin bump.")
        return 2
    added, removed, renamed, changed = diff(base, head)
    print(render(added, removed, renamed, changed), end="")
    if args.no_statement_changes and any(not n.private for _, n in changed):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
