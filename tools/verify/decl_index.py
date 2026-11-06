"""The declaration index: the Lean environment's own account of MathFin.

``lake exe mathfin_index > decl-index.json`` (``MathFinTools/Index.lean``) walks the
environment of the umbrella ``MathFin`` and writes one record per declaration made in
a ``MathFin.*`` module. This module reads that file and answers the questions the
library keeps asking of itself, from one source:

* what exists (``find``), and what uses what (``used_by``, from the recorded ``uses``);
* which theorems state the same thing (``duplicate_statements``, keyed by the hash of the
  statement's ``Expr``, which ignores binder names);
* which private lemmas are general (``mathlib_shaped_private``: the statement mentions no
  MathFin constant, so it is a ``Foundations/`` or upstream lemma kept out of sight).

``tools/verify/mathfin_index.py`` stays: it is the textual approximation the host-side
gates use where no Lean environment exists. ``textual_drift`` compares the two.

Pure stdlib; safe on the host.

Record shape (one per declaration)::

    {"name": "MathFin.foo", "kind": "theorem", "module": "MathFin.Foundations.Foo",
     "line": 42, "private": false, "doc": "…" | null, "type": "∀ …",
     "type_hash": "1234…", "type_uses_mathfin": true,
     "uses": ["MathFin.bar", …], "attrs": ["simp", …]}
"""

from __future__ import annotations

import json
from collections import defaultdict
from dataclasses import dataclass, field
from functools import cached_property
from pathlib import Path

THEOREM_KINDS = frozenset({"theorem"})


@dataclass(frozen=True)
class IndexedDecl:
    name: str
    kind: str
    module: str
    line: int
    private: bool
    doc: str | None
    type: str
    type_hash: str
    type_uses_mathfin: bool
    uses: tuple[str, ...]
    attrs: tuple[str, ...]

    @property
    def path(self) -> str:
        return self.module.replace(".", "/") + ".lean"

    @property
    def short_name(self) -> str:
        """The name a reader writes: private-name mangling removed."""
        return _user_name(self.name)


def _user_name(name: str) -> str:
    # Lean mangles private names as `_private.<Module>.<n>.<Name>`.
    if name.startswith("_private."):
        parts = name.split(".")
        for i, p in enumerate(parts):
            if p.isdigit():
                return ".".join(parts[i + 1:])
    return name


@dataclass
class DeclIndex:
    toolchain: str
    decls: dict[str, IndexedDecl] = field(default_factory=dict)

    # ------------------------------------------------------------- loading

    @classmethod
    def load(cls, path: str | Path) -> DeclIndex:
        data = json.loads(Path(path).read_text(encoding="utf-8"))
        idx = cls(toolchain=data.get("toolchain", ""))
        for r in data["decls"]:
            d = IndexedDecl(
                name=r["name"], kind=r["kind"], module=r["module"], line=r.get("line", 0),
                private=r.get("private", False), doc=r.get("doc"), type=r.get("type", ""),
                type_hash=str(r["type_hash"]), type_uses_mathfin=r.get("type_uses_mathfin", True),
                uses=tuple(r.get("uses", ())), attrs=tuple(r.get("attrs", ())),
            )
            idx.decls[d.name] = d
        return idx

    # ------------------------------------------------------------- graph

    @cached_property
    def used_by(self) -> dict[str, frozenset[str]]:
        rev: dict[str, set[str]] = defaultdict(set)
        for d in self.decls.values():
            for u in d.uses:
                if u != d.name:
                    rev[u].add(d.name)
        return {k: frozenset(v) for k, v in rev.items()}

    def theorems(self) -> list[IndexedDecl]:
        return [d for d in self.decls.values() if d.kind in THEOREM_KINDS]

    # ------------------------------------------------------------- coherence

    def duplicate_statements(self) -> list[list[IndexedDecl]]:
        """Groups of two or more theorems with one statement (up to binder names)."""
        groups: dict[str, list[IndexedDecl]] = defaultdict(list)
        for d in self.theorems():
            groups[d.type_hash].append(d)
        return sorted(
            (sorted(g, key=lambda d: d.name) for g in groups.values() if len(g) > 1),
            key=lambda g: g[0].name,
        )

    def mathlib_shaped_private(self) -> list[IndexedDecl]:
        """Private theorems whose statement mentions no MathFin constant."""
        return sorted(
            (d for d in self.theorems() if d.private and not d.type_uses_mathfin),
            key=lambda d: (d.module, d.line),
        )

    # ------------------------------------------------------------- search

    def find(self, *terms: str, kind: str | None = None, mentions: str | None = None,
             limit: int = 50) -> list[IndexedDecl]:
        """Declarations matching every term in name, docstring or statement
        (case-insensitive), optionally of one kind and mentioning a constant."""
        lowered = [t.lower() for t in terms]
        hits: list[tuple[int, IndexedDecl]] = []
        for d in self.decls.values():
            if kind and d.kind != kind:
                continue
            if mentions and not (any(u.endswith(mentions) for u in d.uses)
                                 or mentions in d.type):
                continue
            name, doc, typ = d.short_name.lower(), (d.doc or "").lower(), d.type.lower()
            if not all(t in name or t in doc or t in typ for t in lowered):
                continue
            # rank: name hits first, then docstring, then statement; public before private
            score = sum(3 if t in name else 2 if t in doc else 1 for t in lowered)
            hits.append((-(score * 2 + (not d.private)), d))
        hits.sort(key=lambda p: (p[0], p[1].name))
        return [d for _, d in hits[:limit]]

    # ------------------------------------------------------------- drift

    def textual_drift(self, textual_names: set[str]) -> tuple[set[str], set[str]]:
        """(public names the environment has and the textual index lacks,
        names the textual index has and the environment lacks).

        Structure fields and instances are left out: the textual index resolves the
        constants a benchmark proof cites by name, and Lean generates those two kinds
        (fields from the structure, instance names from the instance's type), so they are
        cited through the structure or found by instance search, never by a written name.
        """
        structures = {d.name for d in self.decls.values() if d.kind == "structure"}
        env_names = {d.name for d in self.decls.values()
                     if not d.private and "instance" not in d.attrs
                     and d.name.rsplit(".", 1)[0] not in structures}
        all_env = {_user_name(n) for n in self.decls}
        return env_names - textual_names, textual_names - all_env


# ----------------------------------------------------------------- report

def report(idx: DeclIndex, limit: int = 20) -> str:
    """Markdown summary of what the index sees: sizes, duplicate statements,
    Mathlib-shaped private lemmas, and drift against the textual index."""
    from collections import Counter

    from .mathfin_index import declaration_index

    out = ["## Declaration index", "",
           f"{len(idx.decls)} declarations ({idx.toolchain}): " + ", ".join(
               f"{n} {k}" for k, n in Counter(d.kind for d in idx.decls.values()).most_common())]
    dups = idx.duplicate_statements()
    out += ["", f"### Duplicate statements: {len(dups)} group(s)", ""]
    out += [f"- {', '.join(f'`{d.short_name}` ({d.path}:{d.line})' for d in g)}"
            for g in dups[:limit]]
    priv = idx.mathlib_shaped_private()
    out += ["", f"### Private theorems with a Mathlib-only statement: {len(priv)}", ""]
    out += [f"- `{d.short_name}` ({d.path}:{d.line})" for d in priv[:limit]]
    env_only, text_only = idx.textual_drift(set(declaration_index()))
    out += ["", "### Textual index drift (`mathfin_index.py` vs the environment)", "",
            f"{len(env_only)} public declaration(s) the textual index misses; "
            f"{len(text_only)} name(s) it has that the environment lacks."]
    out += [f"- missing: `{n}`" for n in sorted(env_only)[:limit]]
    out += [f"- extra: `{n}`" for n in sorted(text_only)[:limit]]
    return "\n".join(out) + "\n"


def check(idx: DeclIndex) -> list[str]:
    """Problems that fail the build: the textual index has drifted from the environment."""
    from .mathfin_index import declaration_index

    env_only, text_only = idx.textual_drift(set(declaration_index()))
    return ([f"textual index misses `{n}`" for n in sorted(env_only)]
            + [f"textual index has `{n}`, which the environment lacks" for n in sorted(text_only)])


if __name__ == "__main__":
    import sys

    if len(sys.argv) != 3 or sys.argv[1] not in ("report", "check"):
        print("usage: python3 -m tools.verify.decl_index {report,check} decl-index.json")
        raise SystemExit(2)
    idx = DeclIndex.load(sys.argv[2])
    if sys.argv[1] == "report":
        print(report(idx), end="")
        raise SystemExit(0)
    problems = check(idx)
    for m in problems:
        print(m)
    raise SystemExit(1 if problems else 0)
