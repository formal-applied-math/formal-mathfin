"""How the library organizes financial mathematics, read from ``docs/taxonomy.toml``.

The taxonomy is the one source: a **cell** answers where a result sits (a root, the trunk, or a
branch of one of the three limbs), a **family** answers which randomness it is about, a **joint**
is a theorem between two limbs. Every tool that groups the library (the tree, the docs site, the
frontier's ``area``, the dataset's ``cell``/``family``) reads it here and keeps no table of its own.

Module prefixes match by dotted component (``M == p`` or ``M.startswith(p + ".")``); a module
belongs to the cell (or family) of its longest matching prefix.
"""

from __future__ import annotations

import tomllib
from functools import cache
from pathlib import Path

TAXONOMY = Path(__file__).resolve().parents[2] / "docs" / "taxonomy.toml"


def _matches(module: str, prefix: str) -> bool:
    return module == prefix or module.startswith(prefix + ".")


def _longest(module: str, table: list[tuple[str, str]]) -> str | None:
    best = max((p for p, _ in table if _matches(module, p)), key=len, default=None)
    return next((k for p, k in table if p == best), None) if best else None


@cache
def load(path: Path = TAXONOMY) -> dict:
    return tomllib.loads(path.read_text(encoding="utf-8"))


def cells() -> dict[str, dict]:
    return {c["key"]: c for c in load()["cell"]}


def families() -> dict[str, dict]:
    return {f["key"]: f for f in load()["family"]}


def joints() -> list[dict]:
    return list(load().get("joint", []))


def towers() -> list[dict]:
    return list(load().get("tower", []))


def standalones() -> list[dict]:
    return list(load().get("standalone", []))


def in_prefixes(module: str, prefixes: list[str]) -> bool:
    return any(_matches(module, p) for p in prefixes)


def meta() -> list[str]:
    return list(load().get("meta", []))


def _prefixes(items: list[dict], field: str = "modules") -> list[tuple[str, str]]:
    return [(p, i["key"]) for i in items for p in i.get(field, [])]


def cell_of(module: str) -> str | None:
    """The key of the cell holding ``module`` (longest prefix), or None."""
    return _longest(module, _prefixes(load()["cell"]))


def family_of(module: str) -> str | None:
    """The key of the family of ``module`` (longest prefix), or None: general theory."""
    return _longest(module, _prefixes(load()["family"]))


def place_of(modules: list[str]) -> tuple[str | None, str | None]:
    """The (cell, family) of a corpus entry, from the library modules its snippet imports: the
    cell most of them share (ties to the first imported), and the first family any of them has.
    The umbrella ``MathFin`` and the meta modules place nothing."""
    skip = {"MathFin", *(f"MathFin.{m}" for m in meta())}
    placed = [m for m in modules if m not in skip]
    cs = [c for c in map(cell_of, placed) if c]
    cell = max(cs, key=cs.count) if cs else None  # max keeps the first of equal counts
    family = next((f for f in map(family_of, placed) if f), None)
    return cell, family


def part_of(cell: str) -> str:
    return cell.partition("/")[0]


def parts() -> list[dict]:
    """The parts in drawing order: roots, the trunk, then the limbs (choice, valuation, risk is
    the page's business; here the file's order). Each is ``dict(key, kind, title, blurb,
    branches=[dict(key, title, blurb)])``; a part without branches is a single cell."""
    out: dict[str, dict] = {}
    for c in load()["cell"]:
        part, _, branch = c["key"].partition("/")
        if not branch:
            out[part] = dict(key=part, kind=c.get("kind", "root"), title=c["title"],
                             blurb=c["blurb"], branches=[])
        else:
            out[part]["branches"].append(dict(key=branch, title=c["title"], blurb=c["blurb"]))
    return list(out.values())


def label(cell: str) -> str:
    """A cell's name for a reader who sees it out of context: ``Valuation · Trees``."""
    cs = cells()
    title = cs[cell]["title"]
    part = part_of(cell)
    return title if part == cell else f"{cs[part]['title']} · {title}"
