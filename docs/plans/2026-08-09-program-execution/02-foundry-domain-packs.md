# 02 — Foundry domain packs: make domain content data

**Repo:** `mathfin-foundry` · **Trigger:** now · **Est. scope:** one session
**Design source:** `formal-mathfin/docs/program-architecture.md` §1 (L3) and §3.

## Goal

Extract every domain-specific string in `probe/` into a versioned **domain pack**
directory, so retargeting the foundry at `formal-econometrics` becomes writing a
second pack — a config change, not a code change. The coupling audit (2026-08-06)
found the dependence is **lexical, not structural**: ~30 references across
`probe/`, concentrated in prompt prose, the `MathFin.zcb` pedagogical exemplar,
and `MathFin/<Section>/` path prefixes. No hardcoded repo path exists.

## Target layout

```
domains/mathfin/
  house.md         the house doctrine prose currently embedded in probe/house_context.py
  exemplars.json   worked example constants for prompts (replaces hardcoded MathFin.zcb)
                   [{"name": "MathFin.zcb", "applied": "MathFin.zcb r t T",
                     "lesson": "consume, don't re-derive"} , ...]
  pillars.yaml     pillar/bridge vocabulary (for the judge + depth-gate prose)
  pointers.yaml    module map for the depth gate's "consumes a real def" check
  target.toml      repo slug, default branch, library namespace prefix ("MathFin"),
                   Lake root, benchmarks dir, section list (Foundations/, ...)
```

A loader (`probe/domain_pack.py`, dataclass + one `load(name)` function) is the
single access path. `pipeline.toml` gains `[domain] name = "mathfin"`.

## Where the coupling lives (audited 2026-08-06)

- `probe/house_context.py` (335 lines) — the embedded house-doctrine prose, the
  `MathFin.zcb` hallucination warning, a hardcoded example path
  (`MathFin/FixedIncome/VasicekBondPrice.lean`), a MathFin-aware noise filter.
- `probe/af_prompts.py` (332 lines) — 12 references: specifier/formalizer/judge
  role prompts naming MathFin, `MathFin.zcb` as the worked example in ~4 prompts.
- `probe/assemble.py` (10), `probe/build_manifest.py` (2), `probe/issues.py` (1),
  `probe/scout_index.py` (1), `probe/probe_lib.py` (2), `probe/af_gates.py`,
  `probe/embed.py`, `probe/decompose.py`, `probe/strengthen.py`,
  `probe/refinery_notes.py` — grep each for `MathFin|mathfin|formal-mathfin`
  and route every hit through the pack.

## The one acceptance criterion that matters

**Byte-identical prompt rendering.** Before touching anything, write a golden
test: capture the exact rendered output of every prompt-producing function under
the current code (a small fixture set exercising each prompt path), then assert
the pack-loading refactor reproduces them **byte-for-byte** with the `mathfin`
pack. The foundry's close-rate is tuned on these prompts; a silently reworded
prompt is an invisible regression to the thing this repo exists to optimize.
If a byte-diff is genuinely unavoidable (e.g. a trailing-whitespace artifact of
extraction), it must be listed explicitly in the commit message, not absorbed.

## Steps

1. Golden test first (`probe/test_domain_pack_golden.py`), passing against
   current code.
2. Create `domains/mathfin/` by **moving** the strings out of the Python files.
3. `probe/domain_pack.py` loader; thread it through every audited file.
   Signature discipline: pass the pack object down; no module-level global.
4. Full existing test suite green (`python3 -m pytest probe/ -q`) plus the golden
   test against the pack.
5. Grep-gate: `grep -rn "MathFin\|mathfin" probe/*.py` must return ONLY the
   loader's default pack name and test fixtures. Add that as a test
   (`test_no_domain_leakage`), mirroring formal-mathfin's forbidden-text pattern.
6. Update `docs/overview.md` (foundry) with the pack contract and a short
   "adding a domain" recipe.
7. Do NOT write the econometrics pack yet — that belongs to runbook 03/04's
   owner, once the library's namespace and pillars actually exist. An empty
   speculative pack is the seams-guessed-wrong failure mode again.

## Constraints

- No behavior change of any kind: this session must not touch the pipeline's
  gates, budgets, or cadence. `pipeline.toml` gains only the `[domain]` key.
- No live pipeline run needed; this is testable entirely host-side. (No Lean
  slot required — safe to run alongside nothing.)
- Tests are the proof: existing suite + golden + leakage gate.

## Acceptance criteria

- [ ] `domains/mathfin/` exists with all five files; prose moved, not copied
      (the Python files no longer contain it).
- [ ] Golden test proves byte-identical prompts pre/post.
- [ ] `test_no_domain_leakage` green; full `probe/` suite green.
- [ ] `docs/overview.md` documents the pack contract.

## Kill criteria

- If some reference turns out to be structural after all (logic branching on
  MathFin-specific shape, not just strings) — STOP on that file, leave it wired
  to the pack for the string part, and report the structural remainder with a
  proposed design instead of forcing it. That finding changes runbook 03's cost
  estimate and must surface, not be buried.
