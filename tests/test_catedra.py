"""The cátedra's catalogue fields keep their shapes, pinned statements stay pinned, and every
stated problem has a comparator config (docs/specs/2026-11-20-catedra-design.md)."""

from __future__ import annotations

import json

from tools.verify import catedra as c
from tools.verify import research_problems as rp


def test_catalogue_fields_hold():
    assert c.problems(rp.load()) == []


def _record(status="stated", pinned=None, referee=None, attempts=None, lean="MathFinFrontier.q"):
    ls = {"status": status, "needs": ["def:x"] if status == "blocked" else [], "lean": lean}
    if pinned:
        ls["pinned"] = pinned
    r = {"id": "MF-OP-999", "formalization": {"lean_statement": ls}, "review": {}}
    if referee:
        r["review"]["referee"] = referee
    if attempts is not None:
        r["attempts"] = attempts
    return r


STATEMENT = "theorem MathFinFrontier.q (n : ℕ) :\n    n = n :="


def _tree(tmp_path, statement=STATEMENT, cfg=True):
    root, comp = tmp_path / "MathFinFrontier", tmp_path / "comparator"
    root.mkdir()
    comp.mkdir()
    (root / "Q.lean").write_text(f"module\n\n{statement} by\n  sorry\n")
    if cfg:
        (comp / "MF-OP-999.json").write_text(json.dumps(
            {"challenge_module": c.module_of((root / "Q.lean").relative_to(tmp_path)),
             "theorem_names": ["MathFinFrontier.q"]}))
    return root, comp


def test_a_changed_statement_breaks_its_pin(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    root, comp = _tree(tmp_path)
    pin = {"commit": "0" * 40, "pr": 1, "statement_sha256": c.statement_hash(STATEMENT)}
    root_rel, comp_rel = root.relative_to(tmp_path), comp.relative_to(tmp_path)
    assert c.problems([_record(pinned=pin)], root_rel, comp_rel) == []
    (root / "Q.lean").write_text("module\n\ntheorem MathFinFrontier.q (n : ℕ) :\n  n ≤ n := sorry\n")
    assert any("no longer matches" in e for e in c.problems([_record(pinned=pin)], root_rel, comp_rel))


def test_shapes_and_missing_config(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    root, comp = _tree(tmp_path, cfg=False)
    root_rel, comp_rel = root.relative_to(tmp_path), comp.relative_to(tmp_path)
    bad = {
        "no comparator config": _record(),
        "attempts": _record(attempts={"reviewer": 1}),
        "review.referee": _record(referee={"verdict": "fine", "date": "2026-11-26", "comment": "u"}),
        "pinned, but": _record(status="blocked", lean=None, pinned={"commit": "0" * 40}),
    }
    for fragment, rec in bad.items():
        errs = c.problems([rec], root_rel, comp_rel)
        assert any(fragment in e for e in errs), (fragment, errs)


def test_next_chair_follows_the_life_of_a_problem():
    ref = lambda v: {"verdict": v, "date": "2026-11-26", "comment": "u"}
    pin = {"commit": "0" * 40, "pr": 1, "statement_sha256": ""}
    cases = [(_record(status="blocked", lean=None), "builder"),
             (_record(status="statable", lean=None), "formalizer"),
             (_record(), "referee"),
             (_record(pinned=pin), "referee"),
             (_record(pinned=pin, referee=ref("not_faithful")), "formalizer"),
             (_record(pinned=pin, referee=ref("not_faithful"), attempts={"referee": 3}), None),
             (_record(pinned=pin, referee=ref("faithful_with_narrowing")), "prover"),
             (_record(status="proved", lean=None), None)]
    for rec, chair in cases:
        assert c.next_chair(rec)[0] == chair, (rec, c.next_chair(rec))
