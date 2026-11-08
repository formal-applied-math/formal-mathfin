"""docs/taxonomy.toml is the one statement of how the library is organized
(docs/specs/2026-11-08-organization-design.md): every tool that groups the library reads it
through tools/verify/taxonomy.py, and these tests hold it against the tree it describes."""

import json
import re
import tomllib
from pathlib import Path

from tools.verify import taxonomy

ROOT = Path(__file__).resolve().parent.parent


def _modules() -> list[str]:
    return sorted(".".join(p.relative_to(ROOT).with_suffix("").parts)
                  for p in (ROOT / "MathFin").rglob("*.lean"))


def test_every_module_is_in_exactly_one_cell():
    meta = set(taxonomy.meta())
    stray = [m for m in _modules() if m not in meta and taxonomy.cell_of(m) is None]
    assert not stray, f"modules in no cell: {stray[:10]}"
    assert all(taxonomy.cell_of(m) is None for m in meta), "a meta module is also in a cell"


def test_module_prefixes_are_not_dead_and_match_by_component():
    mods = _modules()
    prefixes = [(c["key"], p) for c in taxonomy.cells().values() for p in c.get("modules", [])]
    prefixes += [(f["key"], p) for f in taxonomy.families().values() for p in f["modules"]]
    dead = [(k, p) for k, p in prefixes if not any(m == p or m.startswith(p + ".") for m in mods)]
    assert not dead, f"prefixes matching no module: {dead}"
    # a prefix is a dotted component, never a string prefix
    assert taxonomy.cell_of("MathFin.Choice.Performance.KellyNumeraire") == "choice/dynamic"
    assert taxonomy.cell_of("MathFin.Choice.Performance.KellyX") == "statistics"


def test_cells_and_families_are_well_formed():
    cells = taxonomy.cells()
    for key, c in cells.items():
        assert c["title"].strip() and c["blurb"].strip(), key
        part = taxonomy.part_of(key)
        assert part in cells and cells[part].get("kind") in {"root", "trunk", "limb"}, key
    parts = taxonomy.parts()
    kinds = [p["kind"] for p in parts]
    assert kinds.count("trunk") == 1 and kinds.count("limb") == 3 and "root" in kinds
    for f in taxonomy.families().values():
        assert f["hue"].startswith("--fam-") and f["title"].strip(), f["key"]


def test_frontier_areas_and_families_are_taxonomy_keys():
    frontier = tomllib.loads((ROOT / "docs/blueprint_frontier.toml").read_text("utf-8"))["node"]
    cells, families = taxonomy.cells(), taxonomy.families()
    bad = [n["label"] for n in frontier if n.get("area") not in cells]
    assert not bad, f"frontier nodes with an area that is not a cell key: {bad}"
    bad = [n["label"] for n in frontier if n.get("family", next(iter(families))) not in families]
    assert not bad, f"frontier nodes with an unknown family: {bad}"


def test_joints_name_nodes_and_limbs():
    nodes = json.loads((ROOT / "docs/blueprint_nodes.json").read_text("utf-8"))
    labels = {n["label"] for n in nodes}
    labels |= {n["label"] for n in
               tomllib.loads((ROOT / "docs/blueprint_frontier.toml").read_text("utf-8"))["node"]}
    limbs = {p["key"] for p in taxonomy.parts() if p["kind"] == "limb"}
    for j in taxonomy.joints():
        assert j["node"] in labels, j["node"]
        assert len(j["limbs"]) == 2 and set(j["limbs"]) <= limbs and j["limbs"][0] != j["limbs"][1]


def test_subject_codes_exist():
    known = tomllib.loads((ROOT / "docs/subjects.toml").read_text("utf-8"))
    codes = {f"{s.upper()} {c}" for s in ("jel", "msc") for c in known.get(s, {})}
    items = list(taxonomy.cells().values())
    bad = [(c["key"], s) for c in items for s in c.get("subjects", []) if s not in codes]
    assert not bad, f"subject codes missing from docs/subjects.toml: {bad}"


def test_no_other_module_defines_an_area_or_section_table():
    pattern = re.compile(r"SECTION_AREA|DIR_PLACE|AREA_PLACE|AREA_TXT|SECTIONS\s*[:=]")
    own = {"taxonomy.py"}
    files = [p for g in ("tools/**/*.py", "tools/**/*.js") for p in ROOT.glob(g)]
    offenders = [str(p.relative_to(ROOT)) for p in files
                 if p.name not in own and pattern.search(p.read_text("utf-8"))]
    assert not offenders, f"an area or section table outside the taxonomy: {offenders}"


def test_every_corpus_entry_has_a_place() -> None:
    """The dataset's `cell` and `family` are taxonomy keys: from the snippet's imports, or the
    entry's own `metadata.cell`/`family` where it cites no library module that places it."""
    from tools.verify.corpus import iter_entries
    from tools.verify.hf_dataset import entry_place

    cells, families = taxonomy.cells(), taxonomy.families()
    bad = []
    for _, t in iter_entries():
        cell, family = entry_place(t)
        if cell not in cells or (family is not None and family not in families):
            bad.append((t["id"], cell, family))
    assert bad == []
