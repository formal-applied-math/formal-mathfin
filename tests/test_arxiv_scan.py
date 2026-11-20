"""The openness scanner finds authors' own statements that something is open, and not the
topology or the bibliography."""

from __future__ import annotations

from tools.verify import arxiv_scan as s


def test_finds_openness_statements():
    text = ("We prove existence. Uniqueness, however, remains open in general.\n"
            "It is not known whether the boundary is convex.\f"
            "Conjecture 4.2. The value function is concave.\n")
    found = s.hits(text)
    assert [h["page"] for h in found] == [1, 2]
    assert {"remains-open", "not-known"} <= set(found[0]["patterns"])
    assert found[1]["patterns"] == ["numbered"]
    assert "remains open" in found[0]["context"]


def test_unsolved():
    assert s.hits("The construction at stopping times is an unsolved problem.")[0]["patterns"] \
        == ["unsolved"]


def test_ignores_open_sets_and_references():
    body = "Let U be an open set and the interval is open. The map is continuous.\n" * 30
    refs = "References\n[1] A. Author, An open problem in finance, 2020.\n"
    assert s.hits(body + refs) == []


def test_rejoins_hyphenated_lines():
    assert s.hits("The question re-\nmains open for d > 2.")[0]["patterns"] == ["remains-open"]


def test_pdf_paths():
    assert s.pdf_url("2101.00001", 2).endswith("/arxiv/pdf/2101/2101.00001v2.pdf")
    assert s.pdf_url("math/0501001", 1).endswith("/math/pdf/0501/0501001v1.pdf")


def test_index_and_search(tmp_path):
    txt = tmp_path / "txt"
    path = s.local_path(txt, "2101.00001", 2).with_suffix(".txt")
    path.parent.mkdir(parents=True)
    path.write_text("Intro on convex-\nity of boundaries.\fUniqueness remains open\nin general.\f")
    papers = [{"id": "2101.00001", "version": 2, "title": "A paper", "published": "2021-01-01",
               "primary": "q-fin.MF", "categories": ["q-fin.MF"]}]
    assert s.index(papers, txt, tmp_path / "c.db") == {"papers": 1, "pages": 2}
    [hit] = s.search(tmp_path / "c.db", '"remains open"')
    assert (hit["id"], hit["page"]) == ("2101.00001", 2)
    assert s.search(tmp_path / "c.db", "convexity")[0]["page"] == 1  # hyphenation rejoined
