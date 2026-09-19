"""Order the values review's standing first pass: which descriptions claim more
than their statement proves?

Every corpus ``description`` is scored against the theorems in its snippet, and
the MathFin definitions those theorems name, by TypeSafe's Jev — a classifier
that answers a fixed question with calibrated probabilities instead of text.
The output is a reading order, most suspect first. A score is a lead, never a
verdict: nothing here certifies faithfulness, and nothing here gates CI.

Measured on this pipeline (2026-09-18, ``jev-1.13.0``): on 17 descriptions this
repo later corrected, the overclaiming version outscored its fix in 16 (the
exception is an under-claim), and none of the 17 fixes scored above 0.5; on the
corpus as it stood before the 2026-09-18 corrections, 23 entries scored above
0.7 — 16 genuine mismatches, 2 borderline, 5 false alarms (three narrate the
proof, two are faithful on a close read). Blind spot: a conclusion assumed as a
structure field reads as
faithful, because the text matches — ``test_reduced_core_description_discloses_scope``
covers that class. Retirement rule: ``docs/values-review.md`` (the standing
first pass).

Host-side and stdlib-only. It sends each entry's description, its snippet's
statements and the signatures and docstrings of the MathFin definitions they
name — all public — to ``api.typesafe.ai``. Answers are cached by content hash,
so a re-run pays only for entries whose inputs changed::

    TYPESAFE_API_KEY=… python3 -m tools.verify.prose_sweep          # top 15
    python3 -m tools.verify.prose_sweep --since main --top 30       # what changed
    python3 -m tools.verify.prose_sweep --ids mf-vega --show        # with the texts
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import subprocess
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path

from tools.verify.corpus import iter_entries

MODEL = "jev-1.13.0"  # pinned: the measured numbers above belong to this version
ENDPOINT = "https://api.typesafe.ai/v1/systemone"
CACHE_PATH = Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache")) / "formal-mathfin" / "prose-sweep.json"

# --------------------------------------------------------------------------
# statement extraction — every defect here presents as a finding
# --------------------------------------------------------------------------

DOCSTRING_RE = re.compile(r"/--.*?-/", re.S)
DECL_START_RE = re.compile(
    r"(?m)^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma|example)\s"
)
OPEN, CLOSE = "([{⦃⟨", ")]}⦄⟩"


def _ident_char(ch: str) -> bool:
    return ch.isalnum() or ch in "_'."


def proof_separator(chunk: str) -> int:
    """Index of the ``:=`` that ends the statement: the first one outside every
    bracket that no ``let``/``have`` in the statement has claimed. A named argument
    ``(μ := μ)`` is inside parentheses; ``let Δ : ℝ := v`` owns its own ``:=``."""
    depth = pending = 0
    for k, ch in enumerate(chunk):
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth = max(depth - 1, 0)
        elif depth == 0 and (k == 0 or not _ident_char(chunk[k - 1])) and any(
            chunk.startswith(kw, k) and chunk[k + len(kw):k + len(kw) + 1].isspace()
            for kw in ("let", "have")
        ):
            pending += 1
        elif ch == ":" and depth == 0 and chunk.startswith(":=", k):
            if not pending:
                return k
            pending -= 1
    return len(chunk)


def statements(code: str) -> list[str]:
    """Every theorem/lemma/example signature in a snippet, docstrings excluded,
    proofs cut off."""
    body = DOCSTRING_RE.sub("", code)
    starts = [m.start() for m in DECL_START_RE.finditer(body)]
    chunks = [body[s:e] for s, e in zip(starts, starts[1:] + [len(body)])]
    return [c[:proof_separator(c)].strip() for c in chunks]


# --------------------------------------------------------------------------
# the definitions a statement names
# --------------------------------------------------------------------------

DEF_RE = re.compile(
    r"(?:/--(?P<doc>(?:(?!-/).)*)-/\s*)?(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:private|protected|noncomputable)\s+)*"
    r"(?P<kind>def|abbrev|structure|class|inductive)\s+(?P<name>[A-Za-z_][\w'.]*)",
    re.S,
)
MODIFIERS_RE = re.compile(r"\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*")
IDENT_RE = re.compile(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*")
# `namespace X` pushes X; any `section` pushes nothing; `end` pops one of either.
SCOPE_RE = re.compile(
    r"^[ \t]*(?:namespace[ \t]+(?P<ns>[\w.']+)"
    r"|(?:@\[[^\]\n]*\][ \t]*)?(?:(?:public|private|noncomputable)[ \t]+)*section\b"
    r"|(?P<end>end)\b)",
    re.M,
)
OPEN_RE = re.compile(r"^open\b([^\n]*)", re.M)
COMMENT_RE = re.compile(r"/-.*?-/|--[^\n]*", re.S)


def _blank_comments(text: str) -> str:
    """``text`` with every comment replaced by spaces — same length, same line
    breaks — so positions found in it index the original."""
    return COMMENT_RE.sub(lambda m: re.sub(r"[^\n]", " ", m.group()), text)


def _declarations(text: str):
    """``(qualified_name, rendered)`` for each column-0 definition in ``text``,
    qualified by its enclosing ``namespace`` blocks: its signature/fields up to
    the first blank line, then its docstring."""
    scopes = [(m.start(), m.group("ns"), m.group("end") is not None)
              for m in SCOPE_RE.finditer(_blank_comments(text))]
    stack: list[str | None] = []
    seen = 0
    for m in DEF_RE.finditer(text):
        kind = m.start("kind")
        while seen < len(scopes) and scopes[seen][0] < kind:
            _, namespace, is_end = scopes[seen]
            if is_end:
                stack = stack[:-1]
            else:
                stack.append(namespace)  # None for a section
            seen += 1
        if MODIFIERS_RE.fullmatch(text[text.rfind("\n", 0, kind) + 1:kind]) is None:
            continue  # `class` inside a comment is not a declaration
        block = text[kind:kind + 1200]
        blank = re.search(r"\n\s*\n", block)
        block = DOCSTRING_RE.sub("", block[:blank.start()] if blank else block)
        doc = " ".join((m.group("doc") or "").split())
        qualified = ".".join([ns for ns in stack if ns] + [m.group("name")])
        yield qualified, " ".join(block.split())[:600] + (f" — {doc[:300]}" if doc else "")


def definition_index(root: Path = Path("MathFin")) -> dict[str, str]:
    """Qualified name → rendered definition, over the library. The elaborator
    is the ground truth; this is a reading aid."""
    index: dict[str, str] = {}
    for path in sorted(root.rglob("*.lean")):
        for name, rendered in _declarations(path.read_text(encoding="utf-8")):
            if name not in index or ("—" in rendered and "—" not in index[name]):
                index[name] = rendered
    return index


def _resolve(token: str, by_suffix: dict[str, list[str]], opened: list[str]) -> str | None:
    """The qualified name ``token`` refers to — read the way Lean would, through
    the snippet's ``open``s — or None when it names nothing here, or two things
    equally well. A wrong definition misleads more than a missing one."""
    candidates = by_suffix.get(token, [])
    if len(candidates) > 1:
        candidates = [q for q in candidates if q == token or any(q == f"{ns}.{token}" for ns in opened)]
    return candidates[0] if len(candidates) == 1 else None


def named_definitions(stmts: list[str], code: str, index: dict[str, str], limit: int = 6) -> dict[str, str]:
    local = dict(_declarations(code))  # a snippet's own spec structure wins
    opened = [ns for line in OPEN_RE.findall(code)
              for ns in IDENT_RE.findall(re.sub(r"\(.*?\)", "", line)) if ns not in ("scoped", "in")]
    by_suffix: dict[str, list[str]] = {}
    for qualified in index:
        parts = qualified.split(".")
        for i in range(len(parts)):
            by_suffix.setdefault(".".join(parts[i:]), []).append(qualified)
    found: dict[str, str] = {}
    for token in (t for s in stmts for t in IDENT_RE.findall(s)):
        if token in local:
            name, rendered = token, local[token]
        elif (qualified := _resolve(token, by_suffix, opened)) is not None:
            name, rendered = qualified.split(".")[-1], index[qualified]
        else:
            continue
        if name not in found:
            found[name] = rendered
            if len(found) == limit:
                break
    return found


# --------------------------------------------------------------------------
# the questions (as measured; editing them voids the numbers in the docstring)
# --------------------------------------------------------------------------

QUESTIONS = {
    "relation": {
        "type": "choice",
        "instructions": {
            "question": "How do the claims in `description` relate to the theorems in `lean_statements`?",
            "focus": (
                "Judge the positive mathematical claims in `description` against the hypotheses and "
                "conclusions of all theorems in `lean_statements` taken together. `definitions` gives "
                "the meaning of names the theorems use. A sentence in `description` saying some case or "
                "part is NOT delivered is a scope disclosure, not a claim. A sentence explaining HOW the "
                "result is proved (the method, the proof route, an analogy with another result) is not "
                "a claim about the result either. Nor is a further conclusion that `description` "
                "attributes to composing this result with another result it names (another entry or "
                "lemma, e.g. 'with mf-vega, this is ∂²V/∂σ²'): that is a citation."
            ),
        },
        "criteria": {
            "faithful": {
                "what": "Every positive claim in `description` is established by `lean_statements`: the "
                        "same objects, the same generality, the same strength of conclusion.",
                "examples": ["The description says the scalar case is delivered and the vector case is "
                             "not, and the statement is about real-valued random variables."],
            },
            "overclaims": {
                "what": "`description` asserts more than `lean_statements` proves: a more general class "
                        "of objects, a stronger or additional conclusion, a property the conclusion does "
                        "not contain, or a specific named object where the statement only asserts that "
                        "one exists.",
                "examples": [
                    "The description says the sums converge in L² but the statement only proves that "
                    "their expectations converge.",
                    "The description states the result for n assets but the statement treats two.",
                    "The description says a solution exists and is unique but the statement proves "
                    "only uniqueness.",
                ],
            },
            "misstates": {
                "what": "`description` describes a different result than `lean_statements`: a different "
                        "formula, a reversed inequality, or different hypotheses.",
                "not_for": "A description whose only problem is claiming more generality or a stronger "
                           "conclusion than the statement proves; that is overclaims.",
            },
        },
    },
    "more_general": {
        "type": "noul",
        "instructions": "Does `description` claim the result for a more general class of objects than "
                        "`lean_statements` covers?",
        "criteria": {
            "true": "`description` states a general case (any dimension, any finite family, "
                    "time-dependent coefficients, a process-level statement) while `lean_statements` "
                    "treats only a special case (scalar, two components, constant coefficients, "
                    "increments only).",
            "false": "`description` claims no more generality than `lean_statements`, or it says "
                     "explicitly that the general case is not delivered.",
        },
    },
    "stronger_conclusion": {
        "type": "noul",
        "instructions": "Does `description` assert a conclusion that `lean_statements` does not prove?",
        "criteria": {
            "true": "For example a stronger mode of convergence (almost sure or Lᵖ where the statement "
                    "proves convergence in mean or in measure), existence where only uniqueness is "
                    "proved, a continuity or regularity property absent from the conclusion, or a "
                    "second equality the statement does not contain.",
            "false": "Every conclusion in `description` appears in the conclusion of `lean_statements`, "
                     "or `description` explicitly says it is not delivered.",
        },
    },
    "names_existential": {
        "type": "noul",
        "instructions": "Does `description` present a specific formula or named object where "
                        "`lean_statements` only asserts that some object exists?",
        "criteria": {
            "true": "For example `description` writes an integral of a specific integrand while "
                    "`lean_statements` concludes `∃ g, …` without identifying `g`.",
            "false": "Every object `description` names is identified in `lean_statements`, or "
                     "`lean_statements` asserts no existence at all.",
        },
    },
    "wrong_formula": {
        "type": "noul",
        "instructions": "Does `description` state a formula, inequality, or hypothesis that differs "
                        "from the one in `lean_statements`?",
        "criteria": {
            "true": "For example a negative part where the statement has a positive part, a reversed "
                    "inequality, a different constant, or a hypothesis different from the one the "
                    "statement assumes.",
            "false": "The formulas and hypotheses that `description` mentions match those in "
                     "`lean_statements`.",
        },
    },
    "textbook_without_scope": {
        "type": "noul",
        "instructions": "Is `description` phrased as the full textbook theorem, without saying which "
                        "special case or form of it `lean_statements` delivers?",
    },
}
NOULS = ("more_general", "stronger_conclusion", "names_existential", "wrong_formula", "textbook_without_scope")


# --------------------------------------------------------------------------
# the call, cached by content
# --------------------------------------------------------------------------

def _ask(state: dict, model: str, cache: dict, api_key: str) -> dict:
    body = {"state": state, "model": model, "questions": QUESTIONS}
    key = hashlib.sha256(json.dumps(body, sort_keys=True, ensure_ascii=False).encode()).hexdigest()
    if key in cache:
        return cache[key]
    request = urllib.request.Request(
        ENDPOINT, data=json.dumps(body, ensure_ascii=False).encode(), method="POST",
        headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"},
    )
    for attempt in range(6):
        try:
            with urllib.request.urlopen(request, timeout=120) as response:
                cache[key] = json.loads(response.read())
                return cache[key]
        except urllib.error.HTTPError as error:
            if error.code not in (429, 500, 502, 503, 504) or attempt == 5:
                raise RuntimeError(f"TypeSafe HTTP {error.code}: {error.read()[:300]!r}") from error
            time.sleep(float(error.headers.get("retry-after") or 2 ** attempt))
    raise AssertionError("unreachable")


def _score(answers: dict) -> dict:
    relation = answers["relation"]
    return {
        "suspect": round(1 - relation["probabilities"]["faithful"], 3),
        "relation": relation["choice"],
        "confidence": relation["confidence"],
        **{q: answers[q]["noul"] for q in NOULS},
    }


def _changed_since(rev: str) -> set[str]:
    """Ids whose description or snippet differs from ``rev`` (new entries included)."""
    before: dict[str, tuple] = {}
    for path in sorted(Path("benchmarks").glob("*.json")):
        shown = subprocess.run(["git", "show", f"{rev}:{path}"], capture_output=True, text=True)
        if shown.returncode:
            continue
        data = json.loads(shown.stdout)
        for entry in data.get("theorems", data) if isinstance(data, dict) else data:
            before[entry["id"]] = (entry.get("description"), entry["code"]["lean"])
    return {e["id"] for _, e in iter_entries() if before.get(e["id"]) != (e.get("description"), e["code"]["lean"])}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--top", type=int, default=15, help="entries to list (default 15)")
    parser.add_argument("--since", metavar="REV", help="only entries whose description or snippet changed since REV")
    parser.add_argument("--ids", nargs="+", metavar="ID", help="only these entries")
    parser.add_argument("--show", action="store_true", help="print each listed entry's description and statements")
    parser.add_argument("--json", type=Path, metavar="OUT", help="write every scored row here")
    parser.add_argument("--model", default=MODEL)
    args = parser.parse_args(argv)

    api_key = os.environ.get("TYPESAFE_API_KEY")
    if not api_key:
        print("prose_sweep: set TYPESAFE_API_KEY (https://console.typesafe.ai/keys)", file=sys.stderr)
        return 2

    wanted = set(args.ids) if args.ids else None
    if args.since:
        changed = _changed_since(args.since)
        wanted = changed if wanted is None else wanted & changed
    entries = [e for _, e in iter_entries() if wanted is None or e["id"] in wanted]
    if not entries:
        print("prose_sweep: nothing to score")
        return 0

    index = definition_index()
    try:
        cache = json.loads(CACHE_PATH.read_text())
    except (OSError, ValueError):
        cache = {}

    def run(entry: dict) -> dict:
        stmts = statements(entry["code"]["lean"])
        state = {"lean_statements": stmts,
                 "definitions": named_definitions(stmts, entry["code"]["lean"], index),
                 "description": entry.get("description", "")}
        answers = _ask(state, args.model, cache, api_key)["answers"]
        return {"id": entry["id"], "status": entry["metadata"]["formalization_status"],
                **_score(answers), "state": state}

    with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:
        rows = sorted(pool.map(run, entries), key=lambda r: -r["suspect"])
    CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    CACHE_PATH.write_text(json.dumps(cache, ensure_ascii=False))
    if args.json:
        args.json.write_text(json.dumps(rows, indent=1, ensure_ascii=False))

    print(f"{len(rows)} scored · {sum(r['suspect'] > 0.7 for r in rows)} above 0.7 · model {args.model}\n")
    print(f"{'suspect':>7}  {'relation':<10}  {'status':<15}  id")
    for row in rows[:args.top]:
        print(f"{row['suspect']:>7.2f}  {row['relation']:<10}  {row['status']:<15}  {row['id']}")
        if args.show:
            print(f"\n    description: {row['state']['description']}")
            for stmt in row["state"]["lean_statements"]:
                print("    statement:   " + stmt.replace("\n", "\n                 "))
            print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
