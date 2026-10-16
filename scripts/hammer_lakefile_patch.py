"""Insert an ephemeral `require Hammer` into lakefile.lean, BEFORE mathlib.

Used only by `scripts/hammer-retest.sh`, inside the CI container, against the
image's baked `/app` — never against a tracked checkout.

The ordering is the whole point. `lakefile.lean` says, of the mathlib require:

    KEEP LAST: Lake resolves transitive-dependency conflicts in favor of later
    requires, so mathlib-last pins batteries/Cli/etc. at Mathlib's revs.

Appending the Hammer require would therefore let *Hammer's* batteries/Cli pins
win, invalidating the baked Mathlib and triggering a full rebuild — an hours-long
job on a 4-core runner, which is how a 3-hour budget silently evaporates. The
2026-06-06 pilot recorded the same finding as "mathlib-last ordering (batteries
kept at Mathlib's rev — no Mathlib rebuild)".
"""

from __future__ import annotations

import argparse
import sys

ANCHOR = "require mathlib from git"
MARKER = "require Hammer from git"


def patched(source: str, rev: str) -> str:
    """`source` with a Hammer require inserted immediately before the mathlib one."""
    if MARKER in source:
        raise ValueError("lakefile already requires Hammer — refusing to double-insert")
    if ANCHOR not in source:
        raise ValueError(f"anchor {ANCHOR!r} not found — lakefile shape changed")
    block = (
        "-- EPHEMERAL (CI hammer re-test only; never committed to the tracked\n"
        "-- lakefile). Declared BEFORE mathlib so mathlib-last still wins on\n"
        "-- transitive conflicts and the baked Mathlib is not rebuilt.\n"
        f'require Hammer from git\n'
        f'  "https://github.com/JOSHCLUNE/LeanHammer.git" @\n'
        f'  "{rev}"\n\n'
    )
    return source.replace(ANCHOR, block + ANCHOR, 1)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="hammer_lakefile_patch")
    ap.add_argument("rev", help="LeanHammer git rev (must target our lean-toolchain)")
    ap.add_argument("--path", default="lakefile.lean")
    args = ap.parse_args(argv)
    with open(args.path, encoding="utf-8") as f:
        src = f.read()
    try:
        out = patched(src, args.rev)
    except ValueError as e:
        print(f"[hammer-retest] {e}", file=sys.stderr)
        return 1
    with open(args.path, "w", encoding="utf-8") as f:
        f.write(out)
    print(f"[hammer-retest] inserted require Hammer @ {args.rev} before mathlib")
    return 0


if __name__ == "__main__":
    sys.exit(main())
