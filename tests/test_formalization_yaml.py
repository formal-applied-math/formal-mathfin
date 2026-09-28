"""Freshness + independence gate for the generated formalization.yaml
(mathlib-initiative v0.4 self-report).

1. ``test_formalization_yaml_is_fresh`` — the committed file is byte-identical
   to the generator's output (a generated artifact is never hand-edited;
   regeneration is a no-op). Mirrors ``test_axiom_audit_gen_is_fresh``.
2. ``test_generator_is_foundry_independent`` — the generator reads only
   main-repo sources; it imports nothing from the foundry and builds a complete
   document with no foundry present. The main repo self-reports on its own.
3. ``test_report_matches_corpus`` — the mechanical numbers (theorem count,
   axioms, sorry=0) track the live corpus.
"""

import json
import os

from tools import formalization_yaml as F

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def test_formalization_yaml_is_fresh():
    generated = F.emit_yaml(F.build_doc(ROOT))
    path = os.path.join(ROOT, "formalization.yaml")
    assert os.path.isfile(path), "formalization.yaml missing — run --write"
    current = open(path, encoding="utf-8").read()
    assert current == generated, (
        "formalization.yaml is stale — run "
        "`python3 -m tools.formalization_yaml --write`")


def test_generator_is_foundry_independent():
    # the generator's own source imports nothing from the foundry
    src = open(os.path.join(ROOT, "tools", "formalization_yaml.py"), encoding="utf-8").read()
    assert "import foundry" not in src and "mathfin_foundry" not in src
    # and it builds a full document from main-repo data alone
    doc = F.build_doc(ROOT)
    assert doc["version"] == "v0.4"
    assert set(doc) >= {"project", "sources", "status", "automation",
                        "fidelity", "review", "alignment"}


def test_report_matches_corpus():
    doc = F.build_doc(ROOT)
    assert doc["status"]["axioms"] == ["propext", "Classical.choice", "Quot.sound"]
    assert doc["status"]["sorry_count"] == 0
    # theorem count = number of alignment rows' statements, and appears in scope
    total = sum(int(s["lean"].split()[0]) for s in doc["alignment"]["statements"])
    assert str(total) in doc["status"]["scope"]
    # automation honestly names the scout
    methods = doc["automation"]["methods"]
    assert any("labs-leanstral-1-5" in m.get("models", []) for m in methods)


def test_alignment_source_overrides_are_unique_and_legacy_fallback_is_preserved(tmp_path):
    (tmp_path / "benchmarks").mkdir()

    def write(name, sources):
        entries = [{"id": f"{name}-{i}", "domain": "mathematical_finance",
                    "metadata": {"formalization_status": "full", **source}}
                   for i, source in enumerate(sources)]
        (tmp_path / "benchmarks" / f"{name}.json").write_text(
            json.dumps({"theorems": entries}), encoding="utf-8")

    write("explicit", [{"alignment_source": "Source B"},
                       {"alignment_source": "Source A"},
                       {"alignment_source": "Source B"}])
    write("legacy", [{}, {"alignment_source": "  "}])
    rows = {row["module"]: row for row in
            F.build_doc(str(tmp_path))["alignment"]["statements"]}
    assert rows["benchmarks/explicit.json"]["source"] == "Source A; Source B"
    assert rows["benchmarks/legacy.json"]["source"] == (
        "mathematical_finance (Saporito, Stochastic Processes)")


def _machine_note(doc):
    for m in doc["automation"]["methods"]:
        if "labs-leanstral-1-5" in m.get("models", []):
            return m["prompting_notes"]
    raise AssertionError("machine method not found")


def _afp_note(doc):
    for m in doc["automation"]["methods"]:
        if "AFP" in m.get("prompting_notes", ""):
            return m["prompting_notes"]
    raise AssertionError("AFP re-formalization method not found")


def test_afp_count_matches_corpus_provenance():
    # the AFP-ported count is MECHANICAL: it reports the number of live corpus
    # entries carrying provenance.source == "afp-actuarial-mathematics", so the
    # "translated, not independently derived" disclosure can never drift.
    import glob
    import json
    n = 0
    for f in glob.glob(os.path.join(ROOT, "benchmarks", "*.json")):
        data = json.load(open(f, encoding="utf-8"))
        for t in (data.get("theorems", data) if isinstance(data, dict) else data):
            prov = (t.get("metadata") or {}).get("provenance") or {}
            if prov.get("source") == "afp-actuarial-mathematics":
                n += 1
    assert _afp_note(F.build_doc(ROOT)).startswith(f"{n} proof(s) authored in our own design")


def test_autoform_provenance_count_is_mechanical(tmp_path):
    # a benchmark entry the pipeline scouted (provenance marker) is COUNTED, not
    # hand-set — so the automation disclosure can never drift from the truth.
    import json
    (tmp_path / "benchmarks").mkdir()
    (tmp_path / "benchmarks" / "x.json").write_text(json.dumps({"theorems": [
        {"id": "human-1", "domain": "mathematical_finance",
         "metadata": {"formalization_status": "full"}},
        {"id": "auto-1", "domain": "mathematical_finance",
         "metadata": {"formalization_status": "full",
                      "provenance": {"source": "leanstral-autoform", "issue": 109}}},
        {"id": "auto-2", "domain": "mathematical_finance",
         "metadata": {"formalization_status": "full",
                      "provenance": {"source": "leanstral-autoform", "issue": 88}}},
    ]}), encoding="utf-8")
    (tmp_path / "tools").mkdir()
    (tmp_path / "tools" / "formalization_meta.toml").write_text("", encoding="utf-8")
    note = _machine_note(F.build_doc(str(tmp_path)))
    assert note.startswith("2 autoformalized proof")
    assert "#88" in note and "#109" in note  # sorted, de-duped issues


def test_autoform_disclosure_is_two_stage():
    # the automation disclosure names BOTH pipeline stages honestly: whoever
    # specified the statement (statement_source), and Leanstral formalizing +
    # proving — not only the prover — plus the autop scout mechanism.
    doc = F.build_doc(ROOT)
    method = next(m for m in doc["automation"]["methods"]
                  if "labs-leanstral-1-5" in m.get("models", []))
    note = method["prompting_notes"]
    assert "Leanstral" in note
    assert "specified by" in note and "formalization + proof by" in note
    assert "autop" in method["tool_setup"]


def test_autoform_disclosure_is_derived_not_pinned_to_a_pipeline(tmp_path):
    # the drafter named in the disclosure comes from the CORPUS, so it cannot
    # outlive the pipeline it describes. Magistral drafted every autoform entry
    # merged before it left on 2026-07-29; an entry drafted after must not inherit
    # that claim just because the generator hardcoded it.
    (tmp_path / "benchmarks").mkdir()
    (tmp_path / "tools").mkdir()
    (tmp_path / "tools" / "formalization_meta.toml").write_text("", encoding="utf-8")

    def write(prov):
        (tmp_path / "benchmarks" / "b.json").write_text(json.dumps({"theorems": [
            {"id": "x", "name": "x", "domain": "mathematical_finance",
             "code": {"lean": "x"},
             "metadata": {"formalization_status": "full", "provenance": prov}}]}),
            encoding="utf-8")

    write({"source": "leanstral-autoform", "issue": 1,
           "statement_source": "magistral-autoform", "statement_model": "magistral-medium"})
    doc = F.build_doc(str(tmp_path))
    note = _machine_note(doc)
    method = next(m for m in doc["automation"]["methods"]
                  if "labs-leanstral-1-5" in m.get("models", []))
    assert "Magistral" in note and "magistral-medium" in method["models"]

    # same corpus shape, drafter unattributed (the post-cutover convention)
    write({"source": "leanstral-autoform", "issue": 1,
           "statement_source": "autoform", "statement_model": "autoform"})
    doc2 = F.build_doc(str(tmp_path))
    method2 = next(m for m in doc2["automation"]["methods"]
                   if "labs-leanstral-1-5" in m.get("models", []))
    assert "Magistral" not in _machine_note(doc2)
    assert "magistral-medium" not in method2["models"]
    assert "Magistral" not in method2["tool_setup"]


def test_autoform_count_matches_corpus_provenance():
    # the note reports the MECHANICAL count of leanstral-autoform provenance
    # entries in the live corpus, so it stays honest as autoform PRs merge (0 on
    # a clean main, 1 once #88's PR lands, …) — never a hand-set snapshot.
    import glob
    import json
    n = 0
    for f in glob.glob(os.path.join(ROOT, "benchmarks", "*.json")):
        data = json.load(open(f, encoding="utf-8"))
        for t in (data.get("theorems", data) if isinstance(data, dict) else data):
            prov = (t.get("metadata") or {}).get("provenance") or {}
            if prov.get("source") == "leanstral-autoform":
                n += 1
    assert _machine_note(F.build_doc(ROOT)).startswith(f"{n} autoformalized proof")


def _foundry_method(doc):
    for m in doc["automation"]["methods"]:
        if "formal-foundry" in str(m.get("framework", "")):
            return m
    raise AssertionError("foundry method not found")


def _corpus(tmp_path, *provs):
    (tmp_path / "benchmarks").mkdir(exist_ok=True)
    (tmp_path / "tools").mkdir(exist_ok=True)
    (tmp_path / "tools" / "formalization_meta.toml").write_text("", encoding="utf-8")
    (tmp_path / "benchmarks" / "b.json").write_text(json.dumps({"theorems": [
        {"id": f"x{i}", "name": f"x{i}", "domain": "mathematical_finance",
         "code": {"lean": "x"},
         "metadata": {"formalization_status": "full", "provenance": prov}}
        for i, prov in enumerate(provs)]}), encoding="utf-8")
    return F.build_doc(str(tmp_path))


def test_the_disclosure_names_the_prover_the_entries_record(tmp_path):
    # the foundry proves with the model `[prover] engine` selects (Claude by default from
    # 2026-09-28, when Mistral retired the Leanstral endpoint). An entry Claude proved must
    # not be disclosed as "proof by Leanstral", nor as costing nothing.
    m = _foundry_method(_corpus(tmp_path, {"source": "leanstral-autoform", "issue": 129,
                                           "model": "claude-sonnet-5"}))
    assert "formalization + proof by Claude (claude-sonnet-5)" in m["prompting_notes"]
    assert "Leanstral" not in m["prompting_notes"] + m["tool_setup"]
    assert "Claude (claude-sonnet-5) formalizes + proves it" in m["tool_setup"]
    assert m["cost"]["spend_usd"] == "subscription-based"
    assert "claude-sonnet-5" in m["models"]


def test_a_mixed_corpus_credits_each_prover_with_its_own_entries(tmp_path):
    m = _foundry_method(_corpus(
        tmp_path,
        {"source": "leanstral-autoform", "issue": 66},                 # historical: Leanstral
        {"source": "leanstral-autoform", "issue": 129, "model": "claude-sonnet-5"}))
    note = m["prompting_notes"]
    assert "proof by Claude (claude-sonnet-5) (1) and Leanstral (1)" in note
    assert "Claude (claude-sonnet-5) and Leanstral formalize + prove it" in m["tool_setup"]
    assert "On a prover pass" in m["tool_setup"]
