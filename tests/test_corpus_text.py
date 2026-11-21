"""One search index over the arXiv and OpenAlex corpora: each page findable by phrase."""

from __future__ import annotations

import json

from tools.verify import arxiv_scan, corpus_text as ct, openalex_corpus


def test_index_and_search_both_corpora(tmp_path):
    ax, oa = tmp_path / "arxiv", tmp_path / "openalex"
    (ax).mkdir()
    (ax / "papers.jsonl").write_text(json.dumps(
        {"id": "2101.00001", "version": 2, "title": "A paper", "published": "2021-01-01",
         "primary": "q-fin.MF", "categories": ["q-fin.MF"]}) + "\n")
    work = {"id": "https://openalex.org/W1234567", "title": "A thesis", "publication_year": 2019,
            "primary_topic": {"id": "https://openalex.org/T10067", "display_name": "Stoch"}}
    oa.mkdir()
    (oa / "works.jsonl").write_text(json.dumps(work) + "\n")
    for pdf in (arxiv_scan.local_path(ax / "pdf", "2101.00001", 2),
                openalex_corpus.local_path(oa / "pdf", work)):
        pdf.parent.mkdir(parents=True)
        pdf.write_bytes(b"%PDF")
    docs = ct.arxiv_docs(ax) + ct.openalex_docs(oa)
    texts = ["Intro on convex-\nity of boundaries.\fUniqueness remains open\nin general.\f",
             "The conjecture remains open for jumps.\f"]
    for d, t in zip(docs, texts):  # stand in for pdftotext
        d["txt"].parent.mkdir(parents=True)
        d["txt"].write_text(t)
    assert ct.index(docs, tmp_path / "c.db") == {"pages": 3, "arxiv": 1, "openalex": 1}
    hits = ct.search(tmp_path / "c.db", '"remains open"')
    assert {(h["id"], h["source"], h["page"]) for h in hits} == \
        {("2101.00001", "arxiv", 2), ("W1234567", "openalex", 1)}
    assert ct.search(tmp_path / "c.db", "convexity")[0]["page"] == 1  # hyphenation rejoined
