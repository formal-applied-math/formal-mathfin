"""The OpenAlex corpus tool picks direct PDF links, never SSRN, and keeps only real PDFs."""

from __future__ import annotations

from pathlib import Path

from tools.verify import openalex_corpus as oa


def _work(**kw):
    return {"id": "https://openalex.org/W1234567", **kw}


def test_pdf_links_best_first_without_ssrn():
    w = _work(best_oa_location={"pdf_url": "https://hal.science/a.pdf"},
              locations=[{"pdf_url": "https://papers.ssrn.com/x.pdf"},
                         {"pdf_url": "https://hal.science/a.pdf"},
                         {"pdf_url": "https://www.mdpi.com/b.pdf"}, {"pdf_url": None}])
    assert oa.pdf_links(w) == ["https://hal.science/a.pdf", "https://www.mdpi.com/b.pdf"]


def test_paths_and_pdf_check():
    assert oa.wid(_work()) == "W1234567"
    assert oa.local_path(Path("/r"), _work()) == Path("/r/W12/W1234567.pdf")
    assert oa.is_pdf(b"\n%PDF-1.5 ...") and not oa.is_pdf(b"<!DOCTYPE html>")


def test_cached_never_pays_for_a_free_pdf(tmp_path, monkeypatch):
    direct = {"id": "https://openalex.org/W1", "has_content": {"pdf": True},
              "best_oa_location": {"pdf_url": "https://hal.science/a.pdf"}}
    tried = {"id": "https://openalex.org/W2", "has_content": {"pdf": True},
             "best_oa_location": {"pdf_url": "https://hal.science/b.pdf"}}
    only = {"id": "https://openalex.org/W3", "has_content": {"pdf": True}}
    (tmp_path / "fetched.jsonl").write_text('{"id": "W2", "status": "http-403"}\n')
    got: list[str] = []
    monkeypatch.setattr(oa, "_key", lambda: "k")
    monkeypatch.setattr(oa, "_get", lambda url, *a, **k: (got.append(url), (b"%PDF-1.4", ""))[1])
    assert oa.cached([direct, tried, only], tmp_path, budget=1)["ok"] == 2
    assert [u.rsplit("/", 1)[-1] for u in got] == ["W3.pdf", "W2.pdf"]
