"""The declaration-index consumers, on a small hand-written index.

The index itself is built by ``lake exe mathfin_index`` (``MathFinTools/Index.lean``)
on the runner; these tests pin what ``decl_index``, ``decl_diff`` and ``find`` do with
one, so the host-side tools stay correct without a Lean environment.
"""

from __future__ import annotations

import json
from pathlib import Path

from tools.verify import decl_diff
from tools.verify.decl_index import DeclIndex


def _rec(name, kind="theorem", h="1", private=False, mathfin=True, uses=(), doc=None,
         typ="P"):
    return {"name": name, "kind": kind, "module": "MathFin.Foundations.X", "line": 1,
            "private": private, "doc": doc, "type": typ, "type_hash": h,
            "type_uses_mathfin": mathfin, "uses": list(uses), "attrs": []}


def _index(tmp_path: Path, recs, name="i.json", toolchain="v4.35.0") -> DeclIndex:
    p = tmp_path / name
    p.write_text(json.dumps({"toolchain": toolchain, "decls": recs}))
    return DeclIndex.load(p)


def test_used_by_reverses_uses(tmp_path: Path) -> None:
    idx = _index(tmp_path, [_rec("MathFin.a", uses=["MathFin.b"]), _rec("MathFin.b", h="2")])
    assert idx.used_by["MathFin.b"] == {"MathFin.a"}
    assert "MathFin.a" not in idx.used_by


def test_duplicates_are_theorems_with_one_statement(tmp_path: Path) -> None:
    idx = _index(tmp_path, [
        _rec("MathFin.a", h="7"), _rec("MathFin.b", h="7"),
        _rec("MathFin.f", kind="def", h="9"), _rec("MathFin.g", kind="def", h="9"),
    ])
    assert [[d.name for d in g] for g in idx.duplicate_statements()] == [["MathFin.a", "MathFin.b"]]


def test_mathlib_shaped_private(tmp_path: Path) -> None:
    idx = _index(tmp_path, [
        _rec("_private.MathFin.X.0.MathFin.helper", private=True, mathfin=False),
        _rec("_private.MathFin.X.0.MathFin.local", private=True, mathfin=True, h="2"),
        _rec("MathFin.public", mathfin=False, h="3"),
    ])
    assert [d.short_name for d in idx.mathlib_shaped_private()] == ["MathFin.helper"]


def test_find_ranks_name_over_doc(tmp_path: Path) -> None:
    idx = _index(tmp_path, [
        _rec("MathFin.other", doc="the forward measure of a bond", h="1"),
        _rec("MathFin.forwardMeasure", kind="def", h="2"),
    ])
    assert [d.name for d in idx.find("forward")] == ["MathFin.forwardMeasure", "MathFin.other"]
    assert [d.name for d in idx.find("forward", kind="def")] == ["MathFin.forwardMeasure"]


def test_diff_separates_renames_from_statement_changes(tmp_path: Path) -> None:
    base = _index(tmp_path, [_rec("MathFin.old", h="1"), _rec("MathFin.same", h="2"),
                             _rec("MathFin.gone", h="3")], "b.json")
    head = _index(tmp_path, [_rec("MathFin.new", h="1"), _rec("MathFin.same", h="22"),
                             _rec("MathFin.added", h="4")], "h.json")
    added, removed, renamed, changed = decl_diff.diff(base, head)
    assert [(o.name, n.name) for o, n in renamed] == [("MathFin.old", "MathFin.new")]
    assert [n.name for _, n in changed] == ["MathFin.same"]
    assert [d.name for d in added] == ["MathFin.added"]
    assert [d.name for d in removed] == ["MathFin.gone"]


def test_diff_gate_and_toolchain_guard(tmp_path: Path) -> None:
    (tmp_path / "b.json").write_text(json.dumps(
        {"toolchain": "v4.35.0", "decls": [_rec("MathFin.s", h="1")]}))
    (tmp_path / "h.json").write_text(json.dumps(
        {"toolchain": "v4.35.0", "decls": [_rec("MathFin.s", h="2")]}))
    (tmp_path / "o.json").write_text(json.dumps(
        {"toolchain": "v4.36.0", "decls": [_rec("MathFin.s", h="1")]}))
    b, h, o = (str(tmp_path / f) for f in ("b.json", "h.json", "o.json"))
    assert decl_diff.main([b, h]) == 0
    assert decl_diff.main([b, h, "--no-statement-changes"]) == 1
    assert decl_diff.main([b, o]) == 2
