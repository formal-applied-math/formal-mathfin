"""Which MathFin declarations does a benchmark snippet's proof cite?

The axiom-audit generator and the values tests both need this, and a regex for
``MathFin.…`` is not enough to answer it. A snippet can ``open MathFin`` and
cite ``isStoppingTime_hittingAfter_of_open`` unqualified, use dot notation on a
hypothesis (``h.conditional_expectation_formula`` with
``h : MathFin.BivariateGaussianHyp …``), or cite a theorem that a MathFin file
declares inside ``namespace ProbabilityTheory`` or ``namespace MeasureTheory``.
On 2026-09-25 five theorems cited by ``full`` entries escaped the generated
axiom audit for those reasons.

So this module identifies MathFin constants by where they are declared:

* ``declaration_index`` reads every ``MathFin/**/*.lean`` file, tracks
  ``namespace``/``section``/``end``, and records the fully qualified name of
  each ``theorem``, ``lemma``, ``def``, ``structure`` … it declares;
* ``cited_constants`` resolves each identifier in a snippet's proof bodies
  against that index the way Lean would: as written, under each ``open``ed
  namespace, and, for dot notation ``h.foo`` on a binder ``h : T …``, as
  ``T.foo``. When an identifier is ``c.foo`` for a constant ``c``, the longest
  prefix that names a constant wins, as in Lean.

It is a textual approximation of Lean's name resolution, not a replacement
for it. Dot notation on a term that is not a named binder
(``(f x).foo``) cannot be resolved here; ``unresolved_short_names`` reports
such identifiers so a test can keep them from hiding a citation.

Pure stdlib; safe on the host.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path

MATHFIN_DIR = Path("MathFin")

# The kinds `cited_theorems` keeps. (The generated audit pins every cited
# constant, defs included; the tests reason about theorems.)
THEOREM_KINDS = frozenset({"theorem", "lemma"})


def strip_comments(src: str) -> str:
    """Remove Lean comments (nested ``/- -/`` blocks incl. docstrings, and
    ``--`` line comments), preserving newlines so line numbers stay stable.
    String literals are respected so ``--`` inside a string survives."""
    out = []
    i, n = 0, len(src)
    depth = 0
    in_string = False
    while i < n:
        c = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if depth == 0 and not in_string and c == '"':
            in_string = True
            out.append(c)
            i += 1
            continue
        if in_string:
            if c == "\\":
                out.append(c)
                out.append(nxt)
                i += 2
                continue
            if c == '"':
                in_string = False
            out.append(c)
            i += 1
            continue
        if c == "/" and nxt == "-":
            depth += 1
            i += 2
            continue
        if depth > 0:
            if c == "-" and nxt == "/":
                depth -= 1
                i += 2
                continue
            if c == "\n":
                out.append(c)
            i += 1
            continue
        if c == "-" and nxt == "-":
            while i < n and src[i] != "\n":
                i += 1
            continue
        out.append(c)
        i += 1
    return "".join(out)


def _strip_strings(src: str) -> str:
    return re.sub(r'"(?:\\.|[^"\\])*"', '""', src)


# ---------------------------------------------------------------- the index

@dataclass(frozen=True)
class Decl:
    name: str        # fully qualified
    kind: str        # theorem, lemma, def, structure, …
    path: str        # declaring file
    protected: bool  # `protected`: not reachable by its last component alone


_MODIFIERS = r"(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|public|scoped)\s+)*"
_ATTRS = r"(?:@\[[^\]]*\]\s*)*"
_DECL_RE = re.compile(
    r"^\s*" + _ATTRS + r"(?P<mods>" + _MODIFIERS + r")"
    r"(?P<kind>theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)"
    r"\s+(?P<name>[^\s:({\[⦃]+)")
_NAMESPACE_RE = re.compile(r"^\s*namespace\s+(\S+)")
_SECTION_RE = re.compile(
    r"^\s*" + _ATTRS + r"(?:(?:noncomputable|public)\s+)*section\b\s*(\S*)")
_END_RE = re.compile(r"^\s*end\b\s*(\S*)")
_MUTUAL_RE = re.compile(r"^\s*mutual\b")


def _file_declarations(path: Path) -> list[Decl]:
    """Declarations of one file, with the namespace each is declared in."""
    stack: list[tuple[str, list[str]]] = []  # (kind, name components)
    decls: list[Decl] = []
    for line in strip_comments(path.read_text(encoding="utf-8")).splitlines():
        if m := _NAMESPACE_RE.match(line):
            stack.append(("namespace", m.group(1).split(".")))
            continue
        if m := _SECTION_RE.match(line):
            stack.append(("section", m.group(1).split(".") if m.group(1) else []))
            continue
        if _MUTUAL_RE.match(line):
            stack.append(("mutual", []))
            continue
        if m := _END_RE.match(line):
            target = m.group(1).split(".") if m.group(1) else []
            # `end A.B` closes the scopes whose names compose `A.B`
            closed: list[str] = []
            while stack:
                _kind, comps = stack.pop()
                closed = comps + closed
                if closed == target or not target:
                    break
            continue
        if m := _DECL_RE.match(line):
            mods, kind, name = m.group("mods"), m.group("kind"), m.group("name")
            if "private" in mods.split():
                continue  # unreachable from another module
            if kind == "instance" and name in ("(", "[", "{"):
                continue
            if name.startswith("_root_."):
                full = name[len("_root_."):]
            else:
                prefix = [c for k, comps in stack if k == "namespace" for c in comps]
                full = ".".join(prefix + [name])
            decls.append(Decl(full, kind, str(path), "protected" in mods.split()))
    return decls


@lru_cache(maxsize=1)
def declaration_index() -> dict[str, Decl]:
    """Every public declaration in ``MathFin/``, by fully qualified name."""
    index: dict[str, Decl] = {}
    for path in sorted(MATHFIN_DIR.rglob("*.lean")):
        for decl in _file_declarations(path):
            index.setdefault(decl.name, decl)
    return index


# ---------------------------------------------------------- snippet parsing

# A declaration start, to bound a proof body: everything from a declaration's
# top-level `:=` up to the next declaration is proof position.
DECL_START_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|example)\b")

_OPEN, _CLOSE = "([{", ")]}"


def proof_bodies(code: str) -> list[str]:
    """The proof-position spans of a benchmark snippet: for each declaration, the
    text from its top-level `:=` to the start of the next declaration.

    Bounding by the next declaration is what keeps this proof-position only — the
    scope the generated audit claims. A `:=` nested inside brackets (a named
    argument, a structure instance) is not the proof separator, so the scan tracks
    depth the same way `ledger`/`af_parse` do."""
    starts = [m.start() for m in DECL_START_RE.finditer(code)] + [len(code)]
    out: list[str] = []
    for i in range(len(starts) - 1):
        seg = code[starts[i]:starts[i + 1]]
        depth = 0
        for j, c in enumerate(seg):
            if c in _OPEN:
                depth += 1
            elif c in _CLOSE:
                depth -= 1
            elif c == ":" and depth == 0 and j + 1 < len(seg) and seg[j + 1] == "=":
                out.append(seg[j + 2:])
                break
    return out


# An identifier as it appears in source: dotted, possibly with primes, Unicode
# letters, subscripts and combining marks. A leading `.` (field access on an
# arbitrary term) is captured so the caller can tell it apart.
_IDENT_CHAR = r"[\w'\u0300-\u036f!?]"  # letters, digits, `_`, primes, combining marks
_IDENT_RE = re.compile(
    r"(?<![\w'\u0300-\u036f])(\.?)((?:[^\W\d]|_)" + _IDENT_CHAR + r"*(?:\." + _IDENT_CHAR + r"+)*)")
_OPEN_LINE_RE = re.compile(r"^(\s*)open\s+(.*)$")
_NAMESPACE_LINE_RE = re.compile(r"(?m)^\s*namespace\s+(\S+)")
# `(h₁ h₂ : T …)`, `{h : T}`, `[h : T]`, `⦃h : T⦄`, `have h : T`, `variable (h : T)`
_BINDER_RE = re.compile(
    r"[(\[{⦃]\s*((?:[^\s:()\[\]{}⦃⦄,]+\s+)*[^\s:()\[\]{}⦃⦄,]+)\s*:\s*@?"
    r"((?:[^\W\d]|_)[\w'.]*)")
_HAVE_RE = re.compile(r"\b(?:have|let)\s+([^\s:()\[\]{}⦃⦄,]+)\s*:\s*@?((?:[^\W\d]|_)[\w'.]*)")
_OPEN_KEYWORDS = {"scoped", "hiding", "renaming", "in"}


def _open_commands(code: str):
    """The text of each `open` command. A command continues onto the following
    lines while they are indented past the `open` keyword, as in

        open MathFin.ItoIntegralL2 MathFin.ItoIntegralProcessL2Infinite
          MathFin.ItoLocalMartingaleInfinite
    """
    lines = code.splitlines()
    i = 0
    while i < len(lines):
        m = _OPEN_LINE_RE.match(lines[i])
        i += 1
        if not m:
            continue
        indent, text = len(m.group(1)), [m.group(2)]
        while i < len(lines) and lines[i].strip() and \
                len(lines[i]) - len(lines[i].lstrip()) > indent:
            text.append(lines[i])
            i += 1
        yield " ".join(text)


def _opened_namespaces(code: str) -> list[str]:
    code = strip_comments(code)
    opened: list[str] = []
    for command in _open_commands(code):
        rest = re.sub(r"\([^)]*\)", " ", command)  # `open Foo (bar baz)`
        rest = rest.split(" in ")[0] if " in " in rest else rest
        for tok in rest.split():
            if tok in _OPEN_KEYWORDS or "→" in tok:
                continue
            if re.fullmatch(r"[\w'.]+", tok):
                opened.append(tok)
    for m in _NAMESPACE_LINE_RE.finditer(code):
        comps = m.group(1).split(".")
        opened.extend(".".join(comps[:k]) for k in range(1, len(comps) + 1))
    return opened


def _candidates(ident: str, opened: list[str]):
    """Fully qualified names `ident` could denote, in Lean's lookup order."""
    if ident.startswith("_root_."):
        yield ident[len("_root_."):], False
        return
    yield ident, False
    for ns in opened:
        yield f"{ns}.{ident}", True


def _resolve(ident: str, opened: list[str], index: dict[str, Decl]) -> str | None:
    """The constant a (possibly dotted) identifier names, or ``None``.

    Tries the whole identifier first, then shorter prefixes: in `foo.mp`, `foo`
    is the constant and `mp` is field notation on its type."""
    comps = ident.split(".")
    for k in range(len(comps), 0, -1):
        prefix = ".".join(comps[:k])
        for cand, via_open in _candidates(prefix, opened):
            decl = index.get(cand)
            if decl is None:
                continue
            if decl.protected and via_open and "." not in prefix:
                continue  # a protected name is not reachable by its last component
            return cand
    return None


class _Snippet:
    """Name resolution in one snippet: its `open`ed namespaces, and the binders
    whose type is a MathFin declaration (what dot notation `h.foo` goes through)."""

    def __init__(self, code: str, index: dict[str, Decl]) -> None:
        self.index = index
        self.code = strip_comments(code)
        self.opened = _opened_namespaces(code)
        self.binders: dict[str, str] = {}
        for regex in (_BINDER_RE, _HAVE_RE):
            for m in regex.finditer(self.code):
                head = _resolve(m.group(2), self.opened, index)
                if head is not None:
                    for name in m.group(1).split():
                        self.binders[name] = head

    def resolve(self, ident: str) -> str | None:
        """The MathFin constant an identifier cites, if any. Dot notation on a
        named binder, `h.foo.bar` with `h : T …`, cites `T.foo`; the type `T`
        itself is not a citation."""
        head, _, rest = ident.partition(".")
        if head in self.binders and rest:
            target = _resolve(f"{self.binders[head]}.{rest}", [], self.index)
            return target if target != self.binders[head] else None
        return _resolve(ident, self.opened, self.index)

    def proof_identifiers(self):
        """(is_field_access, identifier) for every identifier in the proof bodies."""
        for body in proof_bodies(self.code):
            for m in _IDENT_RE.finditer(_strip_strings(body)):
                yield bool(m.group(1)), m.group(2).rstrip(".")


# A term written directly after `:=` anywhere in a snippet: the head of a proof
# term, a `have … := foo` step, or a named argument `(h := foo)`.
_ASSIGNED_RE = re.compile(
    r":=\s*\(*\s*@?((?:[^\W\d]|_)" + _IDENT_CHAR + r"*(?:\." + _IDENT_CHAR + r"+)*)")


def cited_constants(code: str, index: dict[str, Decl] | None = None) -> set[str]:
    """Fully qualified MathFin constants that a snippet's proof bodies cite."""
    snippet = _Snippet(code, declaration_index() if index is None else index)
    return {target for is_field, ident in snippet.proof_identifiers()
            if not is_field and (target := snippet.resolve(ident)) is not None}


def cited_theorems(code: str, index: dict[str, Decl] | None = None) -> set[str]:
    """The cited constants that are theorems or lemmas."""
    index = declaration_index() if index is None else index
    return {name for name in cited_constants(code, index)
            if index[name].kind in THEOREM_KINDS}


def assigned_constants(code: str, index: dict[str, Decl] | None = None) -> set[str]:
    """MathFin constants written directly after a `:=` anywhere in a snippet —
    the theorems an entry re-exports or feeds in whole."""
    snippet = _Snippet(code, declaration_index() if index is None else index)
    return {target for m in _ASSIGNED_RE.finditer(snippet.code)
            if (target := snippet.resolve(m.group(1).rstrip("."))) is not None}


def unresolved_short_names(code: str, index: dict[str, Decl] | None = None) -> set[str]:
    """Identifiers in a snippet's proof bodies that were not resolved but share a
    component with the last component of some MathFin theorem.

    These are where a citation could hide from `cited_constants`: field access
    on a term (`(f x).foo`), dot notation on a local without a written type, or
    a name the textual resolver gets wrong. Most are Mathlib names, or fields of
    the snippet's own structures, that happen to share a name with a MathFin
    theorem."""
    index = declaration_index() if index is None else index
    short = {name.rsplit(".", 1)[-1] for name, d in index.items() if d.kind in THEOREM_KINDS}
    snippet = _Snippet(code, index)
    out: set[str] = set()
    for is_field, ident in snippet.proof_identifiers():
        if not is_field and snippet.resolve(ident) is not None:
            continue
        if any(comp in short for comp in ident.split(".")):
            out.add(("." if is_field else "") + ident)
    return out
