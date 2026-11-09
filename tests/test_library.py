"""The host-side library model (`tools/verify/library.py`) and its one Lean-side twin.

Every host tool reads modules, imports and docstrings through `library.py`; the declaration
index (`MathFinTools/Index.lean`) is the one place outside it that must name the aggregators,
because it runs inside Lean. These tests keep the two in step and pin the import parser the
ledger's input hashes depend on.
"""

from __future__ import annotations

import re
from pathlib import Path

from tools.verify import library


def test_index_names_the_same_aggregators() -> None:
    src = Path("MathFinTools/Index.lean").read_text(encoding="utf-8")
    m = re.search(r"def aggregators : List Name := \[([^\]]*)\]", src)
    assert m, "MathFinTools/Index.lean no longer defines `aggregators` as a literal list"
    lean = {n.strip().lstrip("`") for n in m.group(1).split(",")}
    assert lean == set(library.AGGREGATORS), (
        f"Index.lean aggregators {sorted(lean)} != library.AGGREGATORS "
        f"{sorted(library.AGGREGATORS)}")


def test_aggregators_and_init_exist() -> None:
    for name in [*library.AGGREGATORS, library.INIT]:
        assert library.module_path(name).is_file(), name


def test_import_parser() -> None:
    src = "\n".join([
        "module -- shake: keep-downstream",
        "public import MathFin.Foundations.ZCB",
        "import all MathFin.Models.Binomial.Model",
        "public meta import MathFin.Init",
        "import MathFin",
        "import Mathlib.Probability.Moments",
        "-- import MathFin.LineComment",
        "  -- import MathFin.IndentedComment",
        "theorem foo : True := by import_tactic MathFin.NotAnImport",
    ])
    assert library.imports(src) == ["MathFin.Foundations.ZCB", "MathFin.Models.Binomial.Model",
                                    "MathFin.Init", "MathFin", "Mathlib.Probability.Moments"]
    assert library.library_imports(src) == ["MathFin.Foundations.ZCB", "MathFin.Models.Binomial.Model",
                                            "MathFin.Init", "MathFin"]


def test_modules_are_the_library_files() -> None:
    mods = library.modules()
    every = library.modules(aggregators=True)
    assert set(every) - set(mods) == {library.module_path(a) for a in library.AGGREGATORS}
    assert all(p.suffix == ".lean" and not p.name.startswith(".") for p in every)
    assert library.module_name(Path("MathFin/Foundations/ZCB.lean")) == "MathFin.Foundations.ZCB"
