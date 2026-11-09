"""How much of the library grows from the pricing functional.

The one-trunk plan (``docs/specs/2026-11-07-one-trunk-design.md``) asks that everything the
library calls a price reaches the pricing functional. This module measures it from the
declaration index and the table in ``tools/verify/trunk.toml``:

* ``prices_off_trunk`` — price definitions whose definition does not reach the trunk;
* ``price_entries_off_trunk`` — corpus entries whose proof reaches a price definition but
  not the trunk;
* ``pricing_devices_unbridged`` — parallel pricing devices with no proved instance theorem;
* ``concept_duplicates`` — encodings of one concept with no theorem tying them to the
  canonical one.

Each is a ratchet count (``tools/verify/ratchet.py``): it may fall and may not rise.

    python3 -m tools.verify.trunk_reach decl-index.json [--list]
"""

from __future__ import annotations

import argparse
import tomllib
from pathlib import Path

from .corpus import iter_entries
from .decl_index import DeclIndex
from .mathfin_index import cited_constants, declaration_index

TRUNK_TOML = Path(__file__).with_name("trunk.toml")


def load_table(path: Path = TRUNK_TOML) -> dict:
    raw = tomllib.loads(path.read_text(encoding="utf-8"))
    return dict(anchors=frozenset(raw["trunk"]["anchors"]), prices=list(raw["prices"]["names"]),
                devices=raw.get("device", []), duplicates=raw.get("duplicate", []))


class Reach:
    """The transitive dependencies of declarations, memoised."""

    def __init__(self, idx: DeclIndex) -> None:
        self.idx = idx
        self.memo: dict[str, frozenset[str]] = {}

    def closure(self, name: str) -> frozenset[str]:
        if name in self.memo:
            return self.memo[name]
        seen: set[str] = set()
        stack = [name]
        while stack:
            x = stack.pop()
            if x in seen:
                continue
            seen.add(x)
            if x != name and x in self.memo:
                seen |= self.memo[x]
                continue
            d = self.idx.decls.get(x)
            stack.extend(d.uses if d else ())
        self.memo[name] = frozenset(seen)
        return self.memo[name]


def offenders(idx: DeclIndex, table: dict | None = None) -> dict[str, list[str]]:
    """The declarations and entries behind each count, by count."""
    table = load_table() if table is None else table
    anchors, reach = table["anchors"], Reach(idx)
    present = [p for p in table["prices"] if p in idx.decls]
    off_prices = [p for p in present if not reach.closure(p) & anchors]

    price_set = frozenset(present)
    source = declaration_index()
    off_entries = []
    for _, t in iter_entries():
        cited = cited_constants(t.get("code", {}).get("lean", ""), source)
        closure: set[str] = set()
        for c in cited:
            closure |= reach.closure(c)
        if closure & price_set and not closure & anchors:
            off_entries.append(t["id"])

    devices = [d["name"] for d in table["devices"]
               if d["name"] in idx.decls and not (d.get("instance") and d["instance"] in idx.decls)]

    users = idx.used_by
    dups = []
    for g in table["duplicates"]:
        canon = g["canonical"]
        for m in g["members"]:
            if m not in idx.decls:
                continue
            tied = any(idx.decls[u].kind == "theorem" and canon in idx.decls[u].uses
                       for u in users.get(m, ()) if u in idx.decls)
            if not tied:
                dups.append(f"{g['concept']}: {m}")
    return {"prices_off_trunk": off_prices, "price_entries_off_trunk": off_entries,
            "pricing_devices_unbridged": devices, "concept_duplicates": dups}


def metrics(index_path: str | Path) -> dict[str, int]:
    return {k: len(v) for k, v in offenders(DeclIndex.load(index_path)).items()}


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="python3 -m tools.verify.trunk_reach")
    ap.add_argument("index")
    ap.add_argument("--list", action="store_true", help="list the offenders behind each count")
    args = ap.parse_args(argv)
    for k, v in offenders(DeclIndex.load(args.index)).items():
        print(f"{k:28} {len(v)}")
        if args.list:
            for x in v:
                print(f"    {x}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
