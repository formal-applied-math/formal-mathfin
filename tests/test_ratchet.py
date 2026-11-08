"""The ratchet's source metrics may fall and may not rise.

``ratchet.json`` holds one baseline per debt count (``tools/verify/ratchet.py``). This
test checks the counts computed from ``MathFin/`` text; the counts computed from the
declaration index are checked in ``build.yml`` once the index is built. After an
improvement, lower the baseline with ``python3 -m tools.verify.ratchet update``.
"""

from __future__ import annotations

from tools.verify import ratchet


def test_source_metrics_do_not_rise() -> None:
    baseline = ratchet.load_baseline()
    vals = ratchet.source_metrics()
    missing = sorted(set(vals) - set(baseline))
    assert not missing, f"metrics with no baseline in ratchet.json: {missing}"
    rose = ratchet.check(vals, baseline)
    assert not rose, (
        "a debt count rose above its ratchet baseline:\n  " + "\n  ".join(rose)
        + "\nRemove what the change added; a baseline is never raised.")


def test_check_and_improvements_are_strict() -> None:
    base = {"a": 3, "b": 3}
    assert ratchet.check({"a": 4, "b": 3}, base) == ["a: 4 > baseline 3"]
    assert ratchet.check({"a": 3, "b": 2}, base) == []
    assert ratchet.improvements({"a": 3, "b": 2}, base) == ["b: 2 < baseline 3"]


def test_trunk_table_names_real_declarations() -> None:
    """Every constant `tools/verify/trunk.toml` names is declared in `MathFin/`, so a rename
    cannot silently drop it from the one-trunk counts."""
    from tools.verify import trunk_reach
    from tools.verify.mathfin_index import declaration_index

    table, decls = trunk_reach.load_table(), declaration_index()
    names = [*table["anchors"], *table["prices"], *(d["name"] for d in table["devices"]),
             *(d["instance"] for d in table["devices"] if d.get("instance")),
             *(g["canonical"] for g in table["duplicates"]),
             *(m for g in table["duplicates"] for m in g["members"])]
    missing = sorted({n for n in names if n not in decls})
    assert not missing, f"trunk.toml names no declaration: {missing}"
