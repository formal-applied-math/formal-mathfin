# 01 — Architecture metrics: measure leaf fraction and spine density

**Repo:** `formal-mathfin` · **Trigger:** now · **Est. scope:** one session
**Design source:** `docs/program-architecture.md` §2 ("The two ratios") — read it first.

## Goal

Build the measurement instrument for the corpus's architectural health and take
the first reading. **Measure only — set no thresholds, add no CI gate yet.**
Numbers first, thresholds later; picking a threshold before knowing today's value
produces a gate that never fires or always does.

Two numbers, defined precisely:

- **Leaf fraction**: among all MathFin declarations cited in proof position by the
  benchmark corpus, the share whose proof-term in-degree from *other MathFin
  declarations* is 0 AND that are not blueprint-spine nodes. (In-degree counts
  uses in proof terms/values, not just import edges.) A rising leaf fraction is
  the operational definition of drifting from a theory toward a catalogue.
- **Spine density**: blueprint-spine entries per 100 corpus entries, and bridges
  per pillar (bridge = a `docs/bridges.md`-class result; count from the blueprint
  node list's `uses` edges crossing pillar boundaries — a coarse first cut is fine
  if labelled as coarse).

## What already exists (do not rebuild)

- `tools/verify/axiom_audit_gen.py :: collect_proof_position_names()` — extracts
  every proof-position MathFin constant cited by the corpus (~305 names). This is
  your node set.
- `docs/blueprint_nodes.json` — the 29 curated spine nodes (`name`, `uses`,
  `module` fields). This is the spine set.
- `lake-manifest.json` already carries `importGraph` — module-level edges are
  available as a fallback, but module in-degree is NOT the metric (a module with
  one consumed lemma and nine orphans would look healthy). Use it only for a
  sanity cross-check.

## Approach

1. **Edge extraction (the only new Lean code).** A meta script — mirror the shape
   of `axiom_audit_gen`'s generated file: a single `.lean` that imports `MathFin`,
   walks `ConstantInfo` values for every constant in the `MathFin` namespace, and
   for each collects the set of *other* `MathFin.*` constants referenced in its
   value (proof term). Emit JSON to stdout (one object per constant:
   `{"name": ..., "uses": [...]}`). Suggested home: `scripts/ArchitectureSnapshot.lean`
   + a thin runner. Run it via the daemon (`lean-check` on the file will elaborate
   it; if the `#eval`/`run_cmd` output capture is awkward through the daemon, fall
   back to `lake env lean` inside the verify container — daemon DOWN first).
2. **Report computation (Python, stdlib-only, host-side).** New module
   `tools/verify/architecture_report.py` in the pattern of `coverage_report.py`:
   reads the JSON edges + `collect_proof_position_names()` + `blueprint_nodes.json`
   + the benchmark tier data, computes both ratios, and prints a table:
   overall leaf fraction; leaf fraction by section (`Foundations/`, `BlackScholes/`,
   …); spine density; the top-20 highest-in-degree declarations (the de-facto
   spine — compare against the curated one and report the diff, which is itself a
   finding); the full leaf list.
3. **First reading.** Run it. Write the numbers and the date into a new
   `docs/architecture-report.md` (generated header + a short hand-written reading
   of what the numbers say — is the de-facto spine the curated spine?).
4. **Repeatability.** The report must be re-runnable in one command; document it
   in `docs/architecture-report.md` and add a line to `docs/README.md`'s index.

## Constraints

- Memory doctrine: the Lean pass takes the slot; daemon down before any
  container-side `lake env lean`.
- No `MathFin/` source edits. This runbook is read-only on the library.
- stdlib-only Python (match the existing `tools/verify` contract).
- Do NOT wire anything into CI or `tests/` yet. The derivative-gate comes after
  two or three readings exist, in a later session.

## Acceptance criteria

- [ ] `python3 -m tools.verify.architecture_report` runs from a clean checkout
      (given the JSON edge file) and prints both ratios.
- [ ] `docs/architecture-report.md` exists with the first dated reading and the
      regeneration command.
- [ ] The de-facto-vs-curated spine diff is reported (even if empty).
- [ ] Ledger still fresh; no benchmark or `MathFin/` changes.

## Kill criteria

- If `ConstantInfo`-value traversal cannot be made to terminate reasonably on the
  full library through the daemon or container (e.g. environment memory), REPORT
  the obstruction and ship the module-level `importGraph` approximation instead —
  clearly labelled as an approximation, with the limitation section explaining
  what it cannot see.
