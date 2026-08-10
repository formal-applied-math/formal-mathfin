# 02 — Foundry domain packs: make domain content data

**Repo:** `mathfin-foundry` · **Trigger:** now · **Est. scope:** two to three
sessions (see the re-audit below — the first estimate of one session was based on
a reference count that was low by ~4×)
**Design source:** `formal-mathfin/docs/program-architecture.md` §1 (L3) and §3.

## Goal

Extract every domain-specific string **and every namespace-keyed template** in
`probe/` into a versioned **domain pack** directory, so retargeting the foundry at
`formal-econometrics` becomes writing a second pack rather than editing code.

This runbook covers `probe/` only. The scripts, workflows, GHCR image, and issue
contract that decide *which repo the pipeline actually points at* are
[runbook 06](06-foundry-target-plane.md). A domain-free `probe/` is necessary and
not sufficient; do not claim the foundry is retargeted at the end of this one.

## Where the coupling lives (re-audited 2026-08-09)

The 2026-08-06 audit reported "~30 references across `probe/`, lexical not
structural". Re-measured, both halves of that are wrong:

| Where | Hits |
|---|---|
| `probe/*.py` (non-test) | **119** — `autoformalize.py` 39, `af_prompts.py` 12, `decompose.py` 11, `assemble.py` 10, `af_gates.py` 10, `house_context.py` 6, `vibe_prove.py` 4, `pipeline_lib.py`/`embed.py` 3 each, `refinery_notes.py`/`probe_lib.py`/`build_manifest.py` 2 each, `verify_pool.py`/`strengthen.py`/`scout_index.py`/`issues.py` 1 each |
| `probe/test_*.py` | ~250 — fixtures, legitimately domain-flavoured; they become the `mathfin` pack's test data |
| `scripts/*.sh` + `.github/workflows/*.yml` | ~40 — runbook 06's territory |

Most of the 119 is prompt prose and the `MathFin.zcb` exemplar, as the first audit
said. But five sites are **generated code keyed on the namespace**, and no amount
of prompt extraction reaches them:

- `af_gates.py:92,214` — the depth and vacuity gates emit Lean meta code:
  `env.find? `MathFin.{name}`.
- `autoformalize.py:1401-1425` — emits the module skeleton: `namespace MathFin`,
  the house preamble `open scoped NNReal ENNReal` (chosen because 155 of 262
  MathFin modules open exactly those), `end MathFin`, and the benchmark re-export.
- `autoformalize.py:121` — splice extraction is a regex anchored on
  `open scoped NNReal ENNReal … end MathFin`.
- `autoformalize.py:275,294,982` — `_POINTER_RE`, `_LOCATION_RE` and
  `_MATHFIN_IMPORT_RE` parse `MathFin/…/X.lean` paths and `public import MathFin.…`.
- `autoformalize.py:1181,1211` — an issue `area:`-label → `MathFin/<Section>/` map.

Still true from the first audit, and worth keeping: **there is no hardcoded repo
checkout path** in `probe/` — `main_repo` is already a parameter.

## Target layout

The pack carries five kinds of content, not five files of strings.

```
domains/mathfin/
  target.toml      repo slug, default branch, library namespace ("MathFin"), Lake
                   root, benchmarks dir, section list (Foundations/, ...), the
                   target's docs/patterns.md path, lean-lsp container name,
                   verify image, issue-label vocabulary
  house.md         the house doctrine prose currently embedded in probe/house_context.py
  exemplars.json   worked example constants for prompts (replaces hardcoded MathFin.zcb)
                   [{"name": "MathFin.zcb", "applied": "MathFin.zcb r t T",
                     "lesson": "consume, don't re-derive"} , ...]
  pillars.yaml     pillar/bridge vocabulary (for the judge + depth-gate prose)
  pointers.yaml    module map for the depth gate's "consumes a real def" check
  areas.yaml       issue area-label -> section map (out of autoformalize.py:1181)
  templates/       module skeleton, benchmark re-export, depth + vacuity gate
                   snippets, the splice anchor, and the pointer/location/import
                   regex sources
```

A loader (`probe/domain_pack.py`, dataclass + one `load(name)` function) is the
single access path. **Pass the pack object down as a parameter; no module-level
global.** `pipeline.toml` gains `[domain] name = "mathfin"` and nothing else.

## The one acceptance criterion that matters

**Byte-identical rendering — of prompts AND of emitted Lean.** Before touching
anything, write a golden test that captures the exact output of every
prompt-producing function *and* of the module skeleton, the re-export snippet, the
two gate snippets, and a splice round-trip, under the current code. Then assert the
pack-loading refactor reproduces them **byte-for-byte** with the `mathfin` pack.

The first version of this runbook scoped the golden test to prompts. That is the
visible surface but the wrong half of the risk: the foundry's close-rate is tuned
on the prompts, and the *kernel gates* are what the emitted Lean has to survive. A
silently reworded prompt is an invisible regression; a silently reshaped module
skeleton is an invisible regression the gates will blame on the prover.

If a byte-diff is genuinely unavoidable (e.g. a trailing-whitespace artifact of
extraction), it must be listed explicitly in the commit message, not absorbed.

## Steps

1. Golden test first (`probe/test_domain_pack_golden.py`), passing against current
   code, covering prompts + emitted Lean + gate snippets + splice round-trip.
2. Create `domains/mathfin/` by **moving** the strings and templates out of the
   Python files.
3. `probe/domain_pack.py` loader; thread it through every audited file. The five
   namespace-keyed sites become template renders and pack-derived regexes (built
   from the namespace + Lake root), not string constants.
4. Full existing test suite green (`python3 -m pytest probe/ -q`) plus the golden
   test against the pack.
5. Grep-gate: `grep -rn "MathFin\|mathfin" probe/*.py` must return ONLY the
   loader's default pack name and test fixtures. Add that as a test
   (`test_no_domain_leakage`), mirroring formal-mathfin's forbidden-text pattern.
6. Update `docs/overview.md` (foundry) with the pack contract and a short
   "adding a domain" recipe.
7. The econometrics pack belongs to **runbook 06**, once that library's namespace,
   sections and house preamble exist. Writing it here, ahead of them, is the
   seams-guessed-wrong failure mode. (Runbook 03 running concurrently is what
   makes 06 cheap: by the time this lands, the second namespace is real.)

## Constraints

- No behavior change of any kind: this session must not touch the pipeline's
  gates, budgets, or cadence. `pipeline.toml` gains only the `[domain]` key.
- No live pipeline run needed; this is testable entirely host-side. (No Lean
  slot required — it can run alongside runbook 03's Lean work.)
- Tests are the proof: existing suite + golden + leakage gate.

## Acceptance criteria

- [ ] `domains/mathfin/` exists with all seven entries; prose and templates moved,
      not copied (the Python files no longer contain them).
- [ ] Golden test proves byte-identical prompts **and** emitted Lean pre/post.
- [ ] `test_no_domain_leakage` green; full `probe/` suite green.
- [ ] `docs/overview.md` documents the pack contract.

## Kill criteria

- If some reference turns out to be structural in the strong sense (logic
  branching on MathFin-specific *shape*, not a template that can be parameterized)
  — STOP on that file, leave it wired to the pack for the string part, and report
  the structural remainder with a proposed design instead of forcing it. That
  finding changes runbook 06's cost estimate and must surface, not be buried.
