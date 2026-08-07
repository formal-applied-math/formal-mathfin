"""Git merge driver for ``verification_ledger.json``.

The ledger is a flat ``{"entries": {id: row}}`` map, so git's default text merge
combines two branches without conflicting whenever they touch different regions
of the file. That is silent and occasionally wrong: on 2026-08-07 the merge of
PR #173 into main dropped the row for ``mf-vnm-expected-utility`` while the
corpus side kept the entry, and main went red on
``tests/test_ledger.py::test_every_benchmark_entry_has_a_ledger_row``.

The ledger is *derived state*, not content, so the right merge is semantic
rather than textual:

* an id on only one side          -> take it
* an id on both, same input_hash  -> take it (pick the earlier verification)
* an id on both, DIFFERENT hashes -> **drop it**
* an id deleted on one side       -> respect the deletion

Dropping is always safe and never a guess. ``ledger status`` recomputes every
input hash from the working tree, so a dropped row reports MISSING, fails the
gate loudly, and ``ledger verify`` re-runs exactly that entry. Keeping either
side would instead assert a verification that this merged tree never had. The
failure mode is therefore "one entry re-verifies", not "the ledger lies".

Install (per clone, since git config is not versioned)::

    git config merge.mathfin-ledger.name "semantic merge for verification_ledger.json"
    git config merge.mathfin-ledger.driver "python3 tools/verify/ledger_merge.py %O %A %B %L %P"

``.gitattributes`` already routes the file here. Without the config git falls
back to the default text merge — which is why ``tests/test_ledger.py`` remains
the real safety net and this driver is the thing that keeps it from firing.

Pure stdlib; runs on the host during a merge.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path


def _load(path: str) -> dict:
    text = Path(path).read_text(encoding="utf-8")
    return json.loads(text) if text.strip() else {"_meta": {}, "entries": {}}


def merge_entries(base: dict, ours: dict, theirs: dict) -> tuple[dict, list[str]]:
    """Semantic three-way merge of the id -> row maps. Returns (merged, dropped)."""
    merged: dict = {}
    dropped: list[str] = []
    for key in sorted(set(ours) | set(theirs)):
        in_ours, in_theirs = key in ours, key in theirs
        if in_ours and in_theirs:
            if ours[key].get("input_hash") == theirs[key].get("input_hash"):
                merged[key] = ours[key]
            else:
                # both sides verified this entry under different inputs; neither
                # verdict describes the merged tree, so make it re-verify
                dropped.append(key)
        elif in_ours:
            # kept only if the other side did not delete it relative to the base
            if key not in base:
                merged[key] = ours[key]
        else:
            if key not in base:
                merged[key] = theirs[key]
    return merged, dropped


def main(argv: list[str]) -> int:
    if len(argv) < 4:
        print("usage: ledger_merge.py %O %A %B [%L %P]", file=sys.stderr)
        return 2
    base_path, ours_path, theirs_path = argv[1], argv[2], argv[3]
    try:
        base, ours, theirs = _load(base_path), _load(ours_path), _load(theirs_path)
    except json.JSONDecodeError as exc:
        # a malformed side means we cannot reason semantically; let git conflict
        print(f"ledger_merge: cannot parse a side ({exc}) — falling back to conflict",
              file=sys.stderr)
        return 1

    merged, dropped = merge_entries(
        base.get("entries", {}), ours.get("entries", {}), theirs.get("entries", {}))

    out = dict(ours)
    out["entries"] = merged
    # _meta describes the sweep that produced the file; after a merge it
    # describes neither side, so carry ours and let the next sweep rewrite it.
    Path(ours_path).write_text(
        json.dumps(out, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    if dropped:
        print(f"ledger_merge: {len(dropped)} entr{'y' if len(dropped) == 1 else 'ies'} "
              f"verified differently on each side — dropped so they re-verify: "
              f"{', '.join(dropped[:8])}{' …' if len(dropped) > 8 else ''}",
              file=sys.stderr)
    print(f"ledger_merge: merged {len(merged)} rows; run "
          f"`python3 -m tools.verify.ledger status` before trusting this tree",
          file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
