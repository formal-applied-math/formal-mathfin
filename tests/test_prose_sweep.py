"""The prose sweep's statement extraction — the part of it that fails silently.

Every extraction defect in the 2026-09-18 pilot presented as a finding: a
snippet's second theorem went unread, `(μ := μ)` ended a statement early, a
`let` binding cut the conclusion off, an `example` was never seen, a `class`
in a comment became a definition. Each made a faithful description look like
an overclaim. No network here; the scoring itself is advisory and untested.
"""

from tools.verify.corpus import iter_entries
from tools.verify.prose_sweep import CLOSE, OPEN, _declarations, named_definitions, statements


def test_a_named_argument_does_not_end_the_statement() -> None:
    code = "theorem t (h : P) :\n    f (μ := μ) x = 0 :=\n  proof\n"
    assert statements(code) == ["theorem t (h : P) :\n    f (μ := μ) x = 0"]


def test_a_let_binding_does_not_end_the_statement() -> None:
    code = "theorem t (h : P) :\n    let Δ : ℝ := a / b\n    Δ * b = a :=\n  proof\n"
    assert statements(code) == ["theorem t (h : P) :\n    let Δ : ℝ := a / b\n    Δ * b = a"]


def test_every_declaration_is_read_and_docstrings_are_not() -> None:
    code = (
        "/-- mentions `theorem fake : False := trivial` -/\n"
        "theorem one : 1 = 1 := rfl\n\n"
        "example : 2 = 2 :=\n  rfl\n"
    )
    assert statements(code) == ["theorem one : 1 = 1", "example : 2 = 2"]


def test_a_word_in_a_comment_is_not_a_definition() -> None:
    text = "-- the class MeasurableSpace from trim\ndef foo : ℕ := 1\n"
    assert [name for name, _ in _declarations(text)] == ["foo"]


def test_a_scope_word_in_a_comment_does_not_move_the_namespace() -> None:
    text = "namespace A\n/-- a docstring whose second line\nend s early -/\ndef Foo : ℕ := 1\nend A\n"
    assert [name for name, _ in _declarations(text)] == ["A.Foo"]


def test_a_name_two_namespaces_declare_resolves_through_the_open() -> None:
    # The 2026-09-18 pilot keyed definitions by short name and fed the one-period
    # FTAP entries the continuous-time `IsEMM`; both read as overclaims.
    index = dict(_declarations("namespace A\ndef Foo : ℕ := 1\nend A\n\nnamespace B\ndef Foo : ℕ := 2\nend B\n"))
    assert set(index) == {"A.Foo", "B.Foo"}
    opened = named_definitions(["theorem t : Foo = 2"], "open B\n\ntheorem t : Foo = 2 := rfl\n", index)
    qualified = named_definitions(["theorem t : A.Foo = 1"], "theorem t : A.Foo = 1 := rfl\n", index)
    assert opened["Foo"].startswith("def Foo : ℕ := 2")
    assert qualified["Foo"].startswith("def Foo : ℕ := 1")
    assert named_definitions(["theorem t : Foo = 2"], "theorem t : Foo = 2 := rfl\n", index) == {}


def test_every_corpus_snippet_yields_whole_statements() -> None:
    for _path, entry in iter_entries():
        stmts = statements(entry["code"]["lean"])
        assert stmts, f"{entry['id']}: no statement extracted"
        for stmt in stmts:
            depth = 0
            for ch in stmt:
                depth += (ch in OPEN) - (ch in CLOSE)
                assert depth >= 0, f"{entry['id']}: unbalanced brackets in …{stmt[-60:]}"
            assert depth == 0, f"{entry['id']}: statement cut inside a bracket: …{stmt[-60:]}"
