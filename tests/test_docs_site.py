"""The docs site generator (tools/verify/docs_site.py) builds from a small index, and its
statement and prose renderers keep names linked and math whole."""

import json

from tools.verify import docs_site
from tools.verify.decl_index import DeclIndex

MODULE = "MathFin.BlackScholes.Call"


def _index(path):
    decls = [
        {"name": "MathFin.bsCall", "kind": "def", "module": MODULE, "line": 10, "doc": "The call.",
         "type": "ℝ → ℝ", "type_hash": "1", "uses": []},
        {"name": "MathFin.bsCall_pos", "kind": "theorem", "module": MODULE, "line": 20,
         "doc": "It is *positive*: $C > 0$.", "type": "∀ (x : ℝ), 0 < MathFin.bsCall x",
         "type_hash": "2", "uses": ["MathFin.bsCall"]},
    ]
    path.write_text(json.dumps({"toolchain": "test", "decls": decls}), encoding="utf-8")
    return path


def test_site_builds(tmp_path):
    out = tmp_path / "site"
    docs_site.build(_index(tmp_path / "idx.json"), out)
    for page in ("index.html", "blueprint.html", "corpus.html", "subjects.html",
                 "references.html", "search.json", "assets/site.css", "assets/site.js",
                 f"m/{MODULE}.html", "s/BlackScholes.html"):
        assert (out / page).is_file(), page
    mod = (out / f"m/{MODULE}.html").read_text(encoding="utf-8")
    assert 'id="MathFin.bsCall_pos"' in mod
    assert 'class="mf" href="../m/MathFin.BlackScholes.Call.html#MathFin.bsCall"' in mod
    assert "used by 1" in mod
    rows = json.loads((out / "search.json").read_text(encoding="utf-8"))
    assert {r["n"] for r in rows} == {"MathFin.bsCall", "MathFin.bsCall_pos"}


def test_statement_links_and_short_names(tmp_path):
    idx = DeclIndex.load(_index(tmp_path / "idx.json"))
    link = docs_site.Linker(idx, "../", dict(idx.decls))
    html = link.statement("∀ [inst : MeasurableSpace Ω] (T : ℝ), MeasureTheory.Integrable "
                          "(MathFin.bsCall T.toNNReal)")
    assert "[MeasurableSpace" in html and "inst :" not in html
    assert '>Integrable</a>' in html and "mathlib4_docs" in html
    assert '>bsCall</a>' in html
    assert "T.toNNReal" in html  # a local variable, not a name to link


def test_prose_keeps_math_whole():
    s = docs_site.first_sentence("The formula $f(B_T) = \\int_0^T f'(B_s)\\,dB_s$ holds. Next.", 30)
    assert s.count("$") % 2 == 0 and s.endswith("…")
    assert docs_site.first_sentence("A $x.y$ dot. B.") == "A $x.y$ dot."
    inline = docs_site._inline("**bold across `code`** and $a*b*c$")
    assert "<strong>bold across <code>code</code></strong>" in inline
    assert "$a*b*c$" in inline
