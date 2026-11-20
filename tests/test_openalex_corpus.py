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
