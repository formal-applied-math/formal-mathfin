"""The layers of the library and the direction its imports point
(docs/specs/2026-11-07-one-trunk-design.md, §3 I4).

    Probability/  →  Contracts/  →  Pricing/  →  the limbs: Models/ Risk/ Choice/ Insurance/ Markets/

A module imports Mathlib, BrownianMotion, its own layer and the layers before it. A limb imports
another limb only through a declared edge, named with the reason it exists. The edges form a
DAG, with `Models/` at its foot: the models are what the other limbs price, discount or measure
with.

``against_direction`` lists the imports that break the rule; their number is the ratchet count
``layer_violations`` (``tools/verify/ratchet.py``), which falls to zero.

Pure stdlib; safe on the host.
"""

from __future__ import annotations

from collections.abc import Iterable

from . import library

CORE = ("Probability", "Contracts", "Pricing")
LIMBS = ("Models", "Risk", "Choice", "Insurance", "Markets")
LAYERS = CORE + LIMBS

# limb → limb, and why
EDGES: dict[tuple[str, str], str] = {
    ("Markets", "Models"): "an AMM position or a lending rate is priced or discounted in a model",
    ("Insurance", "Models"): "premiums are discounted on a rate curve; survival is a credit intensity",
    ("Insurance", "Risk"): "a premium principle is a risk measure",
    ("Risk", "Models"): "the risk of a position is the law of its value in a model",
    ("Risk", "Choice"): "risk allocation is portfolio variance",
}


def layer(module: str) -> str | None:
    parts = module.split(".")
    return parts[1] if len(parts) > 2 and parts[0] == "MathFin" and parts[1] in LAYERS else None


def allowed(src: str, dst: str) -> bool:
    if src in CORE:
        return dst in CORE and CORE.index(dst) <= CORE.index(src)
    return dst in CORE or dst == src or (src, dst) in EDGES


def against_direction(graph: dict[str, Iterable[str]]) -> list[tuple[str, str]]:
    """The imports `(module, imported)` between two layers that the direction forbids."""
    out = []
    for m, imps in graph.items():
        a = layer(m)
        if a is None:
            continue
        out += [(m, i) for i in imps if (b := layer(i)) is not None and not allowed(a, b)]
    return sorted(out)


def import_graph() -> dict[str, list[str]]:
    return {library.module_name(p): library.library_imports(p.read_text(encoding="utf-8"))
            for p in library.modules()}


def metrics() -> dict[str, int]:
    return {"layer_violations": len(against_direction(import_graph()))}
