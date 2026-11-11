"""The docs site generator (tools/verify/docs_site.py) builds from a small index, and its
statement and prose renderers keep names linked and math whole."""

import json

from tools.verify import docs_site
from tools.verify.decl_index import DeclIndex

MODULE = "MathFin.Models.BlackScholes.Call"


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
    for page in ("index.html", "blueprint.html", "joints.html", "corpus.html", "subjects.html",
                 "references.html", "search.json", "assets/site.css", "assets/site.js",
                 f"m/{MODULE}.html", "s/valuation-diffusions.html"):
        assert (out / page).is_file(), page
    joints = (out / "joints.html").read_text(encoding="utf-8")
    assert "Sockets" in joints and "no socket" in joints  # the fixture prices no market
    mod = (out / f"m/{MODULE}.html").read_text(encoding="utf-8")
    assert 'id="MathFin.bsCall_pos"' in mod
    assert 'class="mf" href="../m/MathFin.Models.BlackScholes.Call.html#MathFin.bsCall"' in mod
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


# ---- the Landmarks page: curated headline results, each with its exact statement

def test_landmarks_toml_has_the_required_keys():
    landmarks = docs_site.load_landmarks()         # raises on a malformed entry
    assert landmarks
    for e in landmarks:
        assert all(e[k].strip() for k in docs_site.LANDMARK_KEYS), e["decl"]
    assert {"MathFin.ito_formula_unrestricted", "MathFin.bs_delta_hedge_replication"} \
        <= {e["decl"] for e in landmarks}


def test_malformed_landmark_fails_loudly(tmp_path):
    bad = tmp_path / "landmarks.toml"
    bad.write_text('[[landmark]]\ndecl = "MathFin.x"\ntitle = "X"\nsummary = "s"\n',
                   encoding="utf-8")
    try:
        docs_site.load_landmarks(bad)
    except ValueError as err:
        assert "scope" in str(err)
    else:
        raise AssertionError("a landmark without `scope` was accepted")


def test_landmarks_page_shows_statements_and_placeholders(tmp_path):
    landmarks = docs_site.load_landmarks()
    gone = "MathFin.bs_delta_hedge_replication"          # not in this index: a card, not a crash
    present = [e["decl"] for e in landmarks if e["decl"] != gone]
    decls = [{"name": n, "kind": "theorem", "module": MODULE, "line": i + 1, "doc": None,
              "type": f"STATEMENT_{i} (x : ℝ)", "type_hash": str(i), "uses": []}
             for i, n in enumerate(present)]
    path = tmp_path / "idx.json"
    path.write_text(json.dumps({"toolchain": "test", "decls": decls}), encoding="utf-8")
    site = docs_site.Site.load(path)
    link = docs_site.Linker(site.idx, "", {d.name: d for ds in site.decls.values() for d in ds})
    for e in landmarks:
        html = docs_site.landmark_card(site, link, e, {})
        if e["decl"] == gone:
            assert "Not in this build" in html and "STATEMENT_" not in html
        else:
            assert f"STATEMENT_{present.index(e['decl'])} (x : ℝ)" in html, e["decl"]
            assert "Not proved." in html


def test_landmark_path_is_restricted_to_anchors():
    def mk(n, uses):
        return docs_site.IndexedDecl(
            name=n, kind="theorem", module=MODULE, line=1, private=False, doc=None, type="",
            type_hash=n, type_uses_mathfin=True, uses=tuple(uses), attrs=())
    idx = DeclIndex("test")
    for d in (mk("top", ["helper", "mid"]), mk("helper", ["base"]), mk("mid", ["base"]),
              mk("base", [])):
        idx.decls[d.name] = d
    path = docs_site.landmark_path(idx, "top", {"top": "Top", "mid": "Mid", "base": "Base"})
    assert [a for a, _ in path] == ["mid", "base"]       # `helper` is not an anchor
    assert dict(path)["mid"] == "Base"


# ---- the tree's exceptions (tools/verify/tree_map.toml): a drawing aid, so only its shape is checked

def test_tree_map_places_name_real_cells():
    from tools.verify import program_tree, taxonomy
    exceptions = program_tree.load_map()
    assert exceptions
    for label, cell in exceptions.items():
        assert cell in taxonomy.cells(), (label, cell)
    # a proved node sits in the cell of its module unless the map says otherwise
    node = {"s": "proved", "l": "thm:x", "m": "MathFin.Models.BlackScholes.Call"}
    assert program_tree.place_node(node, {}) == ("valuation/diffusions", "diffusions")
    assert program_tree.place_node(node, {"thm:x": "probability/laws"})[0] == "probability/laws"
    front = {"s": "frontier", "l": "thm:y", "area": "risk/credit", "family": "default"}
    assert program_tree.place_node(front, {}) == ("risk/credit", "default")
    parts = program_tree.crown_order(taxonomy.parts())
    assert [p["key"] for p in parts if p["kind"] == "limb"] == ["choice", "valuation", "risk"]
