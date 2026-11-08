"""The v2 module move (docs/specs/2026-11-07-one-trunk-design.md, Phase 1).

Moves every module to its place in the layered layout (`Probability/` → `Contracts/` →
`Pricing/` → the limbs) and rewrites what names it. The map is `move_v2.json`, old module →
new module, fixed once, so the same script rebases a branch cut before the move:

    python3 -m tools.verify.move_v2 apply     # git mv + rewrite, on a tree still in the old layout
    python3 -m tools.verify.move_v2 rewrite   # rewrite only: a rebased branch's new files and snippets
    python3 -m tools.verify.move_v2 stray     # list modules still under an old top-level directory

The move changes no declaration. Module names change; declaration names and namespaces do not
(`MathFin.DeFi.Aave.healthFactorV1` lives in `MathFin.Markets.DeFi.Aave`). What is rewritten:

* `import` lines, in Lean files and in benchmark snippets;
* module names written out (`MathFin.Foundations.FTAP`) in prose, docstrings and tooling, where
  the name is the whole token, so a declaration inside a namespace of the same spelling is left
  alone, and never on a Lean `namespace`/`end`/`open`/`section` line;
* file paths (`MathFin/Foundations/FTAP.lean`, `Foundations/FTAP`).

Dated records (`docs/archive/`, `docs/plans/`, `docs/specs/`, release notes) describe the
layout of their day and are not rewritten. Neither is the verification ledger: its inputs change,
and the rows re-verify.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MAP = Path(__file__).with_name("move_v2.json")
OLD_TOPS = ("Foundations", "BlackScholes", "Bridges", "FixedIncome", "Binomial", "Actuarial",
            "Performance", "Portfolio", "RiskMeasures", "DeFi", "Execution", "Futures",
            "Commodities")
TEXT = {".lean", ".json", ".md", ".py", ".toml", ".yml", ".yaml", ".sh", ".js", ".txt", ".bib",
        ".html", ".css", ".cfg"}
SKIP = ("docs/archive/", "docs/plans/", "docs/specs/", "docs/releases/", "verification_ledger.json",
        "tools/verify/move_v2.json", "tools/verify/move_v2.py", ".claude/", ".lake/")


def load_map() -> dict[str, str]:
    return json.loads(MAP.read_text(encoding="utf-8"))


def _path(mod: str) -> str:
    return mod.removeprefix("MathFin.").replace(".", "/")


def rewriter(mp: dict[str, str]):
    """A function rewriting one file's text, and whether it is Lean-like (imports only)."""
    dots = {k: v for k, v in mp.items()}
    paths = {_path(k): _path(v) for k, v in mp.items()}
    alt_dot = "|".join(re.escape(k) for k in sorted(dots, key=len, reverse=True))
    alt_path = "|".join(re.escape(k) for k in sorted(paths, key=len, reverse=True))
    imp = re.compile(rf"(\bimport\s+)({alt_dot})(?![\w.]|\.\w)")
    dot = re.compile(rf"(?<![\w.])({alt_dot})(?!\w|\.[A-Za-z_])")
    path = re.compile(rf"(?<![\w.])(MathFin/)?({alt_path})(?=\.lean\b|(?![\w/]))")

    scope = re.compile(r"^\s*(namespace|end|open|section|export)\b")

    def go(text: str, lean: bool) -> str:
        text = imp.sub(lambda m: m[1] + dots[m[2]], text)
        # in Lean a namespace may share a module's spelling (`MathFin.DeFi.Aave`): leave the
        # lines that name namespaces alone
        text = "".join(ln if lean and scope.match(ln) else dot.sub(lambda m: dots[m[1]], ln)
                       for ln in text.splitlines(keepends=True))
        return path.sub(lambda m: (m[1] or "") + paths[m[2]], text)
    return go


def tracked() -> list[Path]:
    out = subprocess.run(["git", "ls-files"], cwd=ROOT, capture_output=True, text=True,
                         check=True).stdout.split("\n")
    return [ROOT / p for p in out if p and Path(p).suffix in TEXT
            and not any(p.startswith(s) or p == s.rstrip("/") for s in SKIP)]


def rewrite(mp: dict[str, str]) -> int:
    go, n = rewriter(mp), 0
    for f in tracked():
        if not f.exists():
            continue
        old = f.read_text(encoding="utf-8")
        new = go(old, lean=f.suffix == ".lean")
        if new != old:
            f.write_text(new, encoding="utf-8")
            n += 1
    return n


def apply(mp: dict[str, str]) -> None:
    moves = {o: n for o, n in mp.items() if o != n}
    for old, new in sorted(moves.items()):
        src = ROOT / "MathFin" / (_path(old) + ".lean")
        dst = ROOT / "MathFin" / (_path(new) + ".lean")
        dst.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["git", "mv", str(src), str(dst)], cwd=ROOT, check=True)
    print(f"moved {len(moves)} modules; rewrote {rewrite(mp)} files")


def stray() -> list[str]:
    return sorted(str(p.relative_to(ROOT)) for t in OLD_TOPS for p in (ROOT / "MathFin" / t).rglob("*.lean"))


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="python3 -m tools.verify.move_v2")
    ap.add_argument("action", choices=["apply", "rewrite", "stray"])
    args = ap.parse_args(argv)
    mp = load_map()
    if args.action == "apply":
        apply(mp)
    elif args.action == "rewrite":
        print(f"rewrote {rewrite(mp)} files")
    left = stray()
    for p in left:
        print(f"not placed: {p} (give it a place in move_v2.json, or move it to its layer)")
    return 1 if left and args.action == "stray" else 0


if __name__ == "__main__":
    raise SystemExit(main())
