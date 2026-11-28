"""The literature atlas: docs/atlas.json's cells are the taxonomy's, and the join with the library
is computed live (tools/verify/atlas.py)."""

from collections import Counter

import pytest

from tools.verify import atlas, taxonomy


def test_literature_shares_gap_and_warning():
    field = {"cells": {
        "a/x": {"papers": 75, "growth": 2.0, "agreement": {"recall": 0.8}, "founding": [
            {"title": "T", "year": 1973, "doi": None, "authors": ["B"], "cited_by_cell": 9,
             "openalex": "W1"}]},
        "a/y": {"papers": 25, "agreement": {"recall": 0.5}, "founding": []}}}
    lit = atlas.literature(field, Counter({"a/x": 1, "a/y": 3}), Counter({"a/x": 2}),
                           Counter(), Counter({"a/y": 4}))
    assert lit["a/x"]["field"] == 75.0 and lit["a/x"]["library"] == 25.0
    assert lit["a/x"]["gap"] == 50.0 and lit["a/y"]["gap"] == -50.0
    assert not lit["a/x"]["warn"] and lit["a/y"]["warn"]
    assert lit["a/x"]["proved"] == 2 and lit["a/y"]["modules"] == 4
    assert "openalex" not in lit["a/x"]["founding"][0]
    assert atlas.largest_gaps(lit, 1) == ["a/x"]


def test_atlas_json_names_taxonomy_cells_and_holds_no_paper_rows():
    field = atlas.load()
    if field is None:
        pytest.skip("docs/atlas.json not generated yet")
    assert set(field["cells"]) <= set(taxonomy.cells())
    for c in field["cells"].values():
        assert set(c) <= {"papers", "by_year", "growth", "cited_in_corpus", "founding", "agreement"}
        assert len(c["founding"]) <= 10
