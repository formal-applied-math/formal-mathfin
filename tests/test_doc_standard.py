"""The doc standard's rules, on fixtures (the whole-library gate is in ``test_values.py``)."""

from __future__ import annotations

from pathlib import Path

from tools.verify import doc_standard as ds

REPO = Path(__file__).resolve().parent.parent
KEYS = {"Hull"}
SUBJECTS = {"JEL G13": "Contingent Pricing; Futures Pricing",
            "MSC 91G20": "Derivative securities (option pricing, hedging, etc.)"}

GOOD = """/-!
# Black–Scholes call

Summary.

## Main results

* `bs_call_formula`: the closed form.

## Scope

Prose.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], §15.8

## Tags

Black–Scholes, call price, lognormal,
JEL G13, MSC 91G20
-/
"""


def _doc(src: str, path: str = "MathFin/X.lean") -> ds.ModuleDoc:
    doc = ds.module_doc(Path(path), src)
    assert doc is not None
    return doc


def test_the_standard_layout_passes() -> None:
    doc = _doc(GOOD)
    assert doc.title == "Black–Scholes call"
    assert doc.headings == ["Main results", "Scope", "References", "Tags"]
    assert doc.citations == ["Hull"]
    assert doc.subjects == ["JEL G13", "MSC 91G20"]
    assert ds.problems(doc, KEYS, SUBJECTS) == []


def test_a_one_line_title_counts() -> None:
    assert _doc("/-! # Title\n\nText. -/").title == "Title"


def test_each_rule_fires() -> None:
    bad = (GOOD.replace("# Black–Scholes call\n", "")
           .replace("## Main results", "## Results")
           .replace("][Hull]", "][Hul]")
           .replace("JEL G13", "JEL G130").replace("MSC 91G20", "MSC 91G99"))
    msgs = ds.problems(_doc(bad), KEYS, SUBJECTS)
    assert any("`# Title`" in m for m in msgs)
    assert any("write `## Main results`" in m for m in msgs)
    assert any("`Hul` is not in docs/references.bib" in m for m in msgs)
    assert any("malformed JEL code `JEL G130`" in m for m in msgs)
    assert any("`MSC 91G99` is not in docs/subjects.toml" in m for m in msgs)


def test_references_and_tags_close_the_docstring() -> None:
    moved = GOOD.replace("## Scope\n\nProse.\n\n", "").replace("-/\n", "\n## Scope\n\nProse.\n-/\n")
    assert any("close the docstring" in m for m in ds.problems(_doc(moved), KEYS, SUBJECTS))
    unkeyed = GOOD.replace("][Hull], §15.8", "], §15.8")
    assert any("without a bibliography key" in m for m in ds.problems(_doc(unkeyed), KEYS, SUBJECTS))


def test_coverage_counts_what_a_module_owes() -> None:
    bare = _doc("/-!\n# T\n\nText.\n-/", "MathFin/Bare.lean")
    good = _doc(GOOD)
    # `bare` declares a theorem and a def and formalizes a corpus entry citing Hull; `good`
    # declares a theorem only, and its References already cite Hull.
    kinds = {bare.path: {"theorem", "def"}, good.path: {"theorem"}}
    cited = {bare.path: {"Hull"}, good.path: {"Hull"}}
    assert ds.coverage([good, bare], kinds, cited) == {
        "modules_without_main_results": 1, "modules_without_main_definitions": 1,
        "modules_with_uncited_sources": 1, "modules_without_tags": 1}
    # a helper module no corpus entry formalizes owes no References, and one with no
    # definitions owes no Main definitions
    assert ds.coverage([bare], {bare.path: {"theorem"}}, {}) == {
        "modules_without_main_results": 1, "modules_without_main_definitions": 0,
        "modules_with_uncited_sources": 0, "modules_without_tags": 1}


def test_bibliography_and_vocabulary_parse() -> None:
    keys = ds.bib_keys(REPO / ds.BIB)
    assert {"Hull", "BagariaFIDP", "GlostenMilgrom1985"} <= keys
    names = ds.subject_names(REPO / ds.SUBJECTS)
    assert names["JEL G13"] == "Contingent Pricing; Futures Pricing"
    assert all(ds._JEL.match(c) or ds._MSC.match(c) for c in names)


def test_headings_are_spaced_and_ordered() -> None:
    cramped = GOOD.replace("## Main results\n\n", "## Main results\n")
    assert any("not followed by a blank line" in m
               for m in ds.problems(_doc(cramped), KEYS, SUBJECTS))
    swapped = GOOD.replace("## Main results", "## Main definitions\n\n* `x`: a definition.\n\n"
                           "## Main results", 1).replace("## Main definitions", "## Notation", 1)
    assert any("out of order" in m for m in ds.problems(_doc(swapped), KEYS, SUBJECTS))
    title_line = GOOD.replace("/-!\n# ", "/-! # ", 1)
    title_line = title_line.replace("\n\n", "\n", 1)
    assert any("not followed by a blank line" in m
               for m in ds.problems(_doc(title_line), KEYS, SUBJECTS))


def test_corpus_citations_resolve_against_the_bibliography() -> None:
    """One bibliography for corpus and library: an entry that names a source carries
    `metadata.citations` (empty when the source names no work), and every key resolves."""
    from tools.verify.corpus import iter_entries

    keys = ds.bib_keys(REPO / ds.BIB)
    missing, unknown = [], []
    for _, t in iter_entries():
        md = t.get("metadata", {})
        if md.get("reference") and "citations" not in md:
            missing.append(t["id"])
        unknown += [f"{t['id']}: {c['key']}" for c in md.get("citations", [])
                    if c["key"] not in keys]
    assert not missing, f"entries with a reference but no citations: {missing[:10]}"
    assert not unknown, f"citation keys not in docs/references.bib: {unknown[:10]}"
