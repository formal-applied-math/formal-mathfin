"""The library as the host sees it: its modules, their imports, their docstrings.

One parser for the facts every host-side tool needs about ``MathFin/`` without a Lean
environment: which files are library modules, which of them are aggregators (they restate the
library rather than add to it), what a file or a benchmark snippet imports, and where a module's
docstring is. The ledger hashes the import closure with it, the architecture tests walk the
import graph with it, the doc standard and the ratchet read the modules it lists, the HF export
and the docs site resolve a snippet's modules through it. The Lean side's own account is the
declaration index (``decl_index.py``); ``MathFinTools/Index.lean`` keeps the same aggregator
list, and ``tests/test_library.py`` checks the two agree.

Pure stdlib; safe on the host.
"""

from __future__ import annotations

import re
from pathlib import Path

LIBRARY_DIR = Path("MathFin")
UMBRELLA = Path("MathFin.lean")

# They import the whole library to restate it (`#guard_msgs` axiom pins, blueprint tags): an
# edge from them shows nothing, their size and imports are their job, and their docstrings are
# their generator's.
AGGREGATORS = frozenset({"MathFin.AxiomAudit", "MathFin.AxiomAuditGen", "MathFin.Blueprint"})
# The conventions module: every module imports it, so an edge to it shows nothing either.
INIT = "MathFin.Init"

# `import M`, `public import M`, `import all M`, `public meta import M`, at the start of a line.
# The ledger hashes the closure this regex walks, so its matches must stay stable.
_IMPORT = re.compile(
    r"^\s*(?:public\s+)?(?:meta\s+)?import(?:\s+all)?\s+([A-Za-z_][\w'.]*)\s*(?:--.*)?$",
    re.MULTILINE)
_MODULE_DOC = re.compile(r"/-!(.*?)-/", re.S)


def module_name(path: Path) -> str:
    return ".".join(Path(path).with_suffix("").parts)


def module_path(name: str, root: Path = Path(".")) -> Path:
    return root / (name.replace(".", "/") + ".lean")


def imports(src: str) -> list[str]:
    """Every module a Lean file or snippet imports, in order."""
    return _IMPORT.findall(src)


def library_imports(src: str) -> list[str]:
    """The library modules a file or snippet imports (the umbrella `MathFin` included)."""
    return [m for m in imports(src) if m == "MathFin" or m.startswith("MathFin.")]


def modules(*, aggregators: bool = False, root: Path = Path(".")) -> list[Path]:
    """The library's module files, sorted; aggregators only on request. Tool temp files
    (`.name.lean`) are not modules."""
    return sorted(p.relative_to(root) if root != Path(".") else p
                  for p in (root / LIBRARY_DIR).rglob("*.lean")
                  if not p.name.startswith(".")
                  and (aggregators or module_name(p.relative_to(root)) not in AGGREGATORS))


def is_aggregator(path: Path | str) -> bool:
    return module_name(Path(path)) in AGGREGATORS


def module_doc_text(src: str) -> str | None:
    """The body of a file's module docstring (its first `/-! … -/`), or `None`."""
    m = _MODULE_DOC.search(src)
    return m.group(1) if m else None


def module_doc_span(src: str) -> tuple[int, int] | None:
    """Where the module docstring's body sits in `src`, for tools that rewrite it."""
    m = _MODULE_DOC.search(src)
    return (m.start(1), m.end(1)) if m else None
