"""The semantic merge driver for ``verification_ledger.json``.

Regression cover for 2026-08-07: the merge of PR #173 into main auto-merged the
ledger textually and dropped the row for ``mf-vnm-expected-utility`` while the
corpus side kept the entry, so main went red on
``test_every_benchmark_entry_has_a_ledger_row``. The driver in
``tools/verify/ledger_merge.py`` makes that merge semantic.

The rule under test is that a genuine disagreement DROPS the row rather than
picking a side. Dropping is recoverable and honest — ``ledger status`` recomputes
every hash from the tree, so the entry reports MISSING and re-verifies. Picking a
side would assert a verification the merged tree never had.
"""

from tools.verify.ledger_merge import merge_entries


def row(h: str) -> dict:
    return {"input_hash": h, "date": "2026-08-07"}


def test_disjoint_additions_both_survive() -> None:
    """The #173 regression: each side adds a different entry; neither is lost."""
    base = {"a": row("h_a")}
    ours = {"a": row("h_a"), "X": row("h_x")}
    theirs = {"a": row("h_a"), "mf-vnm-expected-utility": row("h_v")}
    merged, dropped = merge_entries(base, ours, theirs)
    assert set(merged) == {"a", "X", "mf-vnm-expected-utility"}
    assert dropped == []


def test_same_hash_on_both_sides_is_kept() -> None:
    base: dict = {}
    ours = {"a": row("same")}
    theirs = {"a": row("same")}
    merged, dropped = merge_entries(base, ours, theirs)
    assert merged["a"]["input_hash"] == "same"
    assert dropped == []


def test_conflicting_hashes_drop_the_row_rather_than_guess() -> None:
    """Neither verdict describes the merged tree, so the entry must re-verify."""
    base = {"a": row("h_old")}
    ours = {"a": row("h_ours")}
    theirs = {"a": row("h_theirs")}
    merged, dropped = merge_entries(base, ours, theirs)
    assert "a" not in merged, "a contested row must not survive with either hash"
    assert dropped == ["a"]


def test_deletion_on_one_side_is_respected() -> None:
    """An entry removed from the corpus must not be resurrected by the merge."""
    base = {"gone": row("h"), "kept": row("h2")}
    ours = {"kept": row("h2")}                      # deleted `gone`
    theirs = {"gone": row("h"), "kept": row("h2")}  # untouched
    merged, _ = merge_entries(base, ours, theirs)
    assert "gone" not in merged
    assert "kept" in merged


def test_addition_is_distinguished_from_survival_of_a_deletion() -> None:
    """Absent-from-base means added; absent-from-base on both sides unions."""
    base: dict = {}
    ours = {"new_ours": row("h1")}
    theirs = {"new_theirs": row("h2")}
    merged, dropped = merge_entries(base, ours, theirs)
    assert set(merged) == {"new_ours", "new_theirs"}
    assert dropped == []
