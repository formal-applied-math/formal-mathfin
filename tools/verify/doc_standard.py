"""One documentation standard for MathFin module docstrings.

The layout is Mathlib's (docs/specs/2026-11-05-library-practices-design.md §4):

    # Title
    <summary>
    ## Main definitions
    ## Main results
    ## Notation                    (optional)
    ## Implementation notes        (optional)
    <free-form sections: Scope, Provenance, …>
    ## References
    ## Tags

``## References`` cites keys of ``docs/references.bib`` in Mathlib's form,
``* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], §4.2``, with the locator
after the key. ``## Tags`` lists the words a reader searches for, comma-separated, plus
subject codes written as tokens (``JEL G13``, ``MSC 91G20``) from the controlled vocabulary
``docs/subjects.toml``, which a script reads without a Lean environment: the HF dataset
exports them as each entry's subjects.

Two kinds of rule:

* **hard** (``problems``, gated at zero by ``tests/test_values.py``): a title comes first, a
  standard section is spelled the standard way, References and Tags close the docstring in
  that order, every reference bullet cites a key and every key is in the bibliography, every
  subject token is well formed;
* **coverage** (``coverage``, counted by the ratchet): a module that declares theorems without
  Main results, one that declares definitions without Main definitions, one whose References
  miss a work its corpus entries cite (``metadata.citations``: corpus and library share the
  bibliography), one without Tags. A count may fall and may not rise.

    python3 -m tools.verify.doc_standard            # hard problems + coverage counts
"""

from __future__ import annotations

import re
import sys
import tomllib
import unicodedata
from dataclasses import dataclass
from pathlib import Path

from . import library

BIB = Path("docs/references.bib")
SUBJECTS = Path("docs/subjects.toml")

STANDARD = ("Main definitions", "Main results", "Notation", "Implementation notes",
            "References", "Tags")
# Spellings that mean a standard section: the hard rule is to write the standard one.
VARIANTS = {"Result": "Main results", "Results": "Main results",
            "Main result": "Main results", "Main statements": "Main results",
            "Main definitions and results": "Main results", "Reference": "References",
            "Main definition": "Main definitions", "Definitions": "Main definitions",
            "Keywords": "Tags", "Tag": "Tags"}

_HEADING = re.compile(r"^(#{1,6})[ \t]+(.+?)[ \t]*$", re.M)
_CITE = re.compile(r"\]\[([^\]\s]+)\]")
_BIB_KEY = re.compile(r"^@\w+\s*\{\s*([^,\s]+)\s*,", re.M)
_BIB_FIELD = re.compile(r"(\w+)\s*=\s*\{")
_JEL = re.compile(r"^JEL [A-Z][0-9]{1,2}$")
_MSC = re.compile(r"^MSC [0-9]{2}[A-Z-][0-9xX]{2}$")


@dataclass(frozen=True)
class ModuleDoc:
    path: str
    title: str | None
    sections: tuple[tuple[str, str], ...]  # (heading, body) of each `##` section, in order
    text: str = ""  # the whole docstring body, for renderers

    def section(self, name: str) -> str | None:
        return next((body for h, body in self.sections if h == name), None)

    @property
    def headings(self) -> list[str]:
        return [h for h, _ in self.sections]

    @property
    def tags(self) -> list[str]:
        body = self.section("Tags") or ""
        return [t.strip() for t in " ".join(body.split()).split(",") if t.strip()]

    @property
    def subjects(self) -> list[str]:
        """The JEL/MSC subject codes of the Tags section (`JEL G13`, `MSC 91G20`)."""
        return [t for t in self.tags if t.startswith(("JEL ", "MSC "))]

    @property
    def citations(self) -> list[str]:
        return _CITE.findall(self.section("References") or "")


def module_doc(path: Path, src: str | None = None) -> ModuleDoc | None:
    src = path.read_text(encoding="utf-8") if src is None else src
    doc = library.module_doc_text(src)
    if doc is None:
        return None
    heads = list(_HEADING.finditer(doc))
    title = None
    first = next((ln.strip() for ln in doc.splitlines() if ln.strip()), "")
    if first.startswith("# "):
        title = first[2:].strip()
    sections = []
    for i, h in enumerate(heads):
        if len(h.group(1)) != 2:
            continue
        end = next((heads[j].start() for j in range(i + 1, len(heads))
                    if len(heads[j].group(1)) <= 2), len(doc))
        sections.append((h.group(2).strip(), doc[h.end():end].strip()))
    return ModuleDoc(str(path), title, tuple(sections), doc)


_ACCENT = re.compile(r"""\\(["'`^~=.]|[Hcv](?=[{ ]))[{ ]?([A-Za-z])\}?""")
_COMBINING = {'"': "\u0308", "'": "\u0301", "`": "\u0300", "^": "\u0302", "~": "\u0303",
              "=": "\u0304", ".": "\u0307", "H": "\u030b", "c": "\u0327", "v": "\u030c"}


def _latex_text(value: str) -> str:
    """A BibTeX field as plain text: accents composed (`{\\"u}` → `ü`), braces dropped."""
    def compose(m: re.Match) -> str:
        return unicodedata.normalize("NFC", m.group(2) + _COMBINING[m.group(1)])

    value = _ACCENT.sub(compose, value)
    return " ".join(value.replace("{", "").replace("}", "").replace("\\", "").split())


def bib_entries(path: Path = BIB) -> dict[str, dict[str, str]]:
    """Each `@kind{key, field = {value}, …}` of the bibliography: key → fields (lower-case
    names, values with their braces and runs of whitespace removed), plus `kind`."""
    if not path.exists():
        return {}
    src, out = path.read_text(encoding="utf-8"), {}
    for m in _BIB_KEY.finditer(src):
        depth, i = 1, src.index("{", m.start())
        j = i + 1
        while depth and j < len(src):
            depth += {"{": 1, "}": -1}.get(src[j], 0)
            j += 1
        fields = {"kind": src[m.start() + 1:i].strip().lower()}
        for f in _BIB_FIELD.finditer(src, m.end(), j - 1):
            k, depth, v = f.group(1).lower(), 1, f.end()
            while depth and v < j:
                depth += {"{": 1, "}": -1}.get(src[v], 0)
                v += 1
            fields[k] = _latex_text(src[f.end():v - 1])
        out[m.group(1)] = fields
    return out


def bib_keys(path: Path = BIB) -> set[str]:
    return set(bib_entries(path))


def subject_names(path: Path = SUBJECTS) -> dict[str, str]:
    """The controlled vocabulary: `JEL G13` → its official name, likewise `MSC 91G20`."""
    data = tomllib.loads(path.read_text(encoding="utf-8")) if path.exists() else {}
    return {f"{scheme.upper()} {code}": name
            for scheme, codes in data.items() for code, name in codes.items()}


def problems(doc: ModuleDoc, keys: set[str], subjects: dict[str, str]) -> list[str]:
    out = []
    if doc.title is None:
        out.append("the module docstring does not open with a `# Title`")
    for h in doc.headings:
        if h in VARIANTS:
            out.append(f"`## {h}`: write `## {VARIANTS[h]}`")
    hs = doc.headings
    for name in ("References", "Tags"):
        if hs.count(name) > 1:
            out.append(f"`## {name}` appears twice")
    tail = [h for h in hs if h in ("References", "Tags")]
    if tail and hs[-len(tail):] != tail:
        out.append("`## References` and `## Tags` close the docstring (no section after them)")
    if tail == ["Tags", "References"]:
        out.append("`## References` comes before `## Tags`")
    std = [h for h in hs if h in STANDARD]
    if std != sorted(std, key=STANDARD.index):
        out.append("standard sections out of order (" + ", ".join(STANDARD) + ")")
    text = doc.text.lstrip(" \t")  # a title written on the `/-!` line is a heading too
    for m in _HEADING.finditer(text):
        if not text[m.end():].startswith("\n\n"):
            out.append(f"`{m.group(0).strip()}` is not followed by a blank line")
    refs = doc.section("References")
    if refs is not None:
        for bullet in re.split(r"^\*\s", refs, flags=re.M)[1:]:
            if not _CITE.search(bullet):
                out.append(f"reference without a bibliography key: `* {bullet.strip()[:60]}…`")
        for k in doc.citations:
            if k not in keys:
                out.append(f"citation key `{k}` is not in docs/references.bib")
    for t in doc.tags:
        if t.startswith("JEL") and not _JEL.match(t):
            out.append(f"malformed JEL code `{t}` (write `JEL G13`)")
        if t.startswith("MSC") and not _MSC.match(t):
            out.append(f"malformed MSC code `{t}` (write `MSC 91G20`)")
        if (_JEL.match(t) or _MSC.match(t)) and t not in subjects:
            out.append(f"subject code `{t}` is not in docs/subjects.toml (add its row)")
    return out


DEFINITION_KINDS = frozenset({"def", "abbrev", "structure", "inductive", "class"})
THEOREM_KINDS = frozenset({"theorem", "lemma"})


def declared_kinds() -> dict[str, set[str]]:
    """Module path → the kinds of public declaration it makes (the host-side index)."""
    from .mathfin_index import declaration_index

    kinds: dict[str, set[str]] = {}
    for d in declaration_index().values():
        kinds.setdefault(str(d.path), set()).add(d.kind)
    return kinds


def corpus_citations() -> dict[str, set[str]]:
    """Module path → the bibliography keys the corpus entries formalized in it cite. An entry is
    formalized in the module its snippet imports; it cites `metadata.citations`."""
    from .corpus import iter_entries

    cited: dict[str, set[str]] = {}
    for _, entry in iter_entries():
        keys = {c["key"] for c in entry.get("metadata", {}).get("citations", [])}
        for m in library.library_imports(entry["code"]["lean"]):
            if m != "MathFin" and keys:
                cited.setdefault(str(library.module_path(m)), set()).update(keys)
    return cited


def coverage(docs: list[ModuleDoc], kinds: dict[str, set[str]] | None = None,
             cited: dict[str, set[str]] | None = None) -> dict[str, int]:
    """The ratchet's documentation counts. A module that declares a theorem lists its main
    results, one that declares a definition lists its main definitions, and the References of a
    module cite every work its corpus entries formalize (the bibliography is one for corpus and
    library). A helper module no source covers is not asked to cite one."""
    kinds = declared_kinds() if kinds is None else kinds
    cited = corpus_citations() if cited is None else cited
    return {
        "modules_without_main_results": sum(
            bool(kinds.get(d.path, set()) & THEOREM_KINDS) and d.section("Main results") is None
            for d in docs),
        "modules_without_main_definitions": sum(
            bool(kinds.get(d.path, set()) & DEFINITION_KINDS)
            and d.section("Main definitions") is None for d in docs),
        "modules_with_uncited_sources": sum(
            bool(cited.get(d.path, set()) - set(d.citations)) for d in docs),
        "modules_without_tags": sum(d.section("Tags") is None for d in docs),
    }


def all_docs() -> list[ModuleDoc]:
    """Every library module's docstring; a module without one counts as an empty docstring."""
    return [module_doc(p) or ModuleDoc(str(p), None, ()) for p in library.modules()]


def all_problems() -> list[str]:
    keys, subjects = bib_keys(), subject_names()
    return [f"{d.path}: {m}" for d in all_docs() for m in problems(d, keys, subjects)]


def main() -> int:
    probs = all_problems()
    for m in probs:
        print(m)
    for k, v in coverage(all_docs()).items():
        print(f"{k}: {v}")
    return 1 if probs else 0


if __name__ == "__main__":
    sys.exit(main())
