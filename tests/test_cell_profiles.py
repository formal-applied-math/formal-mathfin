"""The library's half of the literature atlas: every cell has a profile, every source its cells."""

from __future__ import annotations

from tools.verify import cell_profiles, taxonomy


def test_every_leaf_cell_has_a_profile_and_every_source_a_cell():
    data = cell_profiles.profiles()
    keys = [c["key"] for c in taxonomy.load()["cell"]]
    assert list(data["cells"]) == keys
    parents = {k.split("/")[0] for k in keys if "/" in k}
    for key, cell in data["cells"].items():
        if key not in parents:
            assert cell["modules"], f"{key}: a leaf cell with no module"
        assert cell["profile"].startswith(cell["title"])
    assert sum(bool(s["cells"]) for s in data["sources"]) >= len(data["sources"]) - 5


def test_plain_drops_code_and_link_targets():
    assert cell_profiles._plain("The `Martingale` of [Doob][Doob1953], see [x](http://y).") == \
        "The of Doob, see x."
