"""A generated artifact must not assert a component the data does not record.

`formalization.yaml` is the public AI-disclosure file, and it used to hardcode
"statement specified by Magistral" + `magistral-medium` in the generator source
(`tools/formalization_yaml.py`), with a test asserting those strings. Magistral left
the pipeline on 2026-07-29; the sentence stayed true only because no entry had merged
since. The class of bug is general — a generated file naming a live component it did
not read from the corpus — so this checks the property rather than the one instance.
"""
from __future__ import annotations

import glob
import json
import os
import re

from tools import formalization_yaml as F

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# Vendor / model vocabulary. The generated DISCLOSURE may name one of these only if the
# corpus's own provenance records it. Extend when a new engine enters the pipeline.
COMPONENT_WORDS = (
    "magistral", "leanstral", "mistral", "claude", "gpt", "gemini", "llama",
    "deepseek", "qwen", "kimi", "grok",
)

# The narrower set the GENERATOR SOURCE may not hardcode: engines that can occupy the
# DRAFTER slot, which is the part that changes. Leanstral (and Mistral, its vendor) are
# excluded because the prover is fixed by `provenance.source == leanstral-autoform` —
# naming it is a consequence of the data, not an assumption about the pipeline. Claude
# is excluded here only because it appears in an unrelated method (the interactive
# human-authoring disclosure); if it ever leaks into the MACHINE method,
# `test_the_disclosure_names_only_components_the_corpus_records` catches it.
DRAFTER_WORDS = tuple(w for w in COMPONENT_WORDS
                      if w not in ("leanstral", "mistral", "claude"))


def _corpus_provenance_blob() -> str:
    """Everything the corpus records about how its entries were produced."""
    out = []
    for path in glob.glob(os.path.join(ROOT, "benchmarks", "*.json")):
        data = json.load(open(path, encoding="utf-8"))
        for t in (data.get("theorems", data) if isinstance(data, dict) else data):
            md = t.get("metadata") or {}
            out.append(json.dumps(md.get("provenance") or {}))
            out.append(str(md.get("formalization_scope") or ""))
    return " ".join(out).lower()


def _machine_method(doc: dict) -> dict:
    for m in doc["automation"]["methods"]:
        if any("leanstral" in str(x).lower() for x in m.get("models", [])):
            return m
    raise AssertionError("machine autoformalization method not found")


def test_the_disclosure_names_only_components_the_corpus_records():
    # the machine-autoformalization disclosure tracks the pipeline, so every engine it
    # names must be one the corpus actually attributes an entry to
    method = _machine_method(F.build_doc(ROOT))
    text = " ".join([json.dumps(method.get("models", [])),
                     str(method.get("prompting_notes", "")),
                     str(method.get("tool_setup", ""))]).lower()
    corpus = _corpus_provenance_blob()
    unbacked = [w for w in COMPONENT_WORDS if w in text and w not in corpus]
    assert not unbacked, (
        "formalization.yaml's automation disclosure names "
        f"{unbacked} but no benchmark entry's provenance records it — the generator is "
        "asserting a pipeline the corpus does not attest. Regenerate from provenance "
        "rather than hardcoding (tools/formalization_yaml.py).")


def test_the_generator_does_not_hardcode_a_drafter_into_the_prose():
    # the failure mode was a DRAFTER name baked into an f-string, invisible until the
    # corpus moved on: "statement specified by Magistral" survived the model leaving the
    # pipeline. See DRAFTER_WORDS for why the prover is exempt.
    src = open(os.path.join(ROOT, "tools", "formalization_yaml.py"), encoding="utf-8").read()
    code = "\n".join(l for l in src.splitlines() if not l.strip().startswith("#"))
    hits = set()
    for w in DRAFTER_WORDS:
        for m in re.finditer(rf'["\'][^"\']*{w}[^"\']*["\']', code, re.I):
            hits.add(m.group(0))
    assert not hits, (
        "these string literals name a pipeline component inside the generator, so the "
        f"disclosure cannot follow the corpus when the pipeline changes: {sorted(hits)}")


def test_the_corpus_still_backs_what_the_disclosure_says_today():
    # a live sanity check on the derivation: the entries ARE magistral-drafted today,
    # so the disclosure naming Magistral is correct — and this test is what will fail
    # (pointing at the generator) once that stops being true
    method = _machine_method(F.build_doc(ROOT))
    corpus = _corpus_provenance_blob()
    for model in method.get("models", []):
        base = str(model).lower()
        assert any(w in corpus for w in COMPONENT_WORDS if w in base) or "leanstral" in base, (
            f"disclosure lists model {model!r} with no corpus provenance behind it")


def _drafter_counts() -> tuple[int, dict]:
    """(autoformalized entries, {drafter -> how many entries name it}). An entry whose
    `statement_source` is absent or the drafter-agnostic `autoform` counts as
    unattributed, which is the honest state after the pipeline stopped naming drafters."""
    total, per = 0, {}
    for path in glob.glob(os.path.join(ROOT, "benchmarks", "*.json")):
        data = json.load(open(path, encoding="utf-8"))
        for t in (data.get("theorems", data) if isinstance(data, dict) else data):
            prov = (t.get("metadata") or {}).get("provenance") or {}
            if prov.get("source") != "leanstral-autoform":
                continue
            total += 1
            src = str(prov.get("statement_source") or "autoform").replace("-autoform", "")
            if src != "autoform":
                per[src] = per.get(src, 0) + 1
    return total, per


def test_the_disclosure_does_not_generalize_one_drafter_to_every_entry():
    """The subtler sibling of the hardcoding bug: naming a drafter the corpus DOES
    record, but attaching it to the total count, so entries it never touched are
    attributed to it.

    Concretely — #66/#85 were drafted by Magistral (2026-07-18, while it was live);
    #161/#162 landed 2026-07-31, after it was removed from the pipeline on 2026-07-27,
    and their queue entries carried the name only because provenance used to be stamped
    at enqueue. A sentence reading "4 proofs (statement specified by Magistral)" credits
    a model with work it did not do.

    So: whenever a named drafter accounts for fewer than all autoformalized entries, the
    disclosure has to say how many are actually its."""
    total, per = _drafter_counts()
    note = str(_machine_method(F.build_doc(ROOT)).get("prompting_notes", "")).lower()
    for drafter, count in per.items():
        if drafter not in note:
            continue
        if count != total:
            assert re.search(rf"{re.escape(drafter)}[^,.]*\({count}\)", note), (
                f"the disclosure names {drafter!r} beside a total of {total} "
                f"autoformalized entries, but only {count} record it as their drafter. "
                f"Attribute the count explicitly. Note reads: {note!r}")
