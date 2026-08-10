# 05 — ForMathlib/ and the aging report

**Repo:** whichever domain library births the first field-neutral block ·
**Trigger:** that block exists or is about to · **Design source:**
`docs/program-architecture.md` §1 (L0).

The Brouwer/Kakutani tower was this runbook's expected first case. It is not:
`harfe/fixed-point-theorems-lean4` proves both sorry-free at our exact pin
(`applied-areas.md` §2a, corrected 2026-08-09), so building it would be reproving.
The likelier first case is now something much smaller — e.g. the missing
`∫ f ∂(μ[|s]) = (μ s)⁻¹ • ∫ x in s, f x ∂μ` that runbook 03 will need on contact.
**Before staging anything under `ForMathlib/`, search the Lean ecosystem, not just
Mathlib.** That check is cheap and it is the difference between a departure lounge
and a duplication.

## Do not run early

If no field-neutral Lean block exists yet, there is nothing to age — stop.
Creating an empty `ForMathlib/` "for structure" is exactly the junk-drawer
failure mode this design exists to prevent.

## Goal

Stand up the departure-lounge mechanics the moment the first field-neutral code
lands: `<Lib>/ForMathlib/` with mandatory upstream metadata, a CI-visible aging
report, and the cross-library consumption rules wired into both CLAUDE.md files.

## The contract (from program-architecture.md, made mechanical)

Every declaration under `ForMathlib/` carries, in its module docstring header, a
machine-parseable block:

```
-- upstream-target: Mathlib.Topology.FixedPoints.Brouwer   (destination module)
-- upstream-status: staged | pr-open <url> | merged <rev>
-- staged-since: 2026-XX-XX
```

Rules:
- No `ForMathlib/` file without the block — enforced by a test in the pattern of
  the forbidden-text gates (`test_formathlib_contract`).
- An aging report (`python3 -m tools.verify.formathlib_report`, or the apparatus
  equivalent post-runbook-04) lists every staged entry with its age;
  entries older than a soft threshold (start with 120 days, tune later) are
  flagged loudly in CI output — visible, not failing, to start.
- `merged` entries get deleted at the next pin bump that contains them; the
  report lists "deletable at current pin" as its top section. The
  pin-bump drift sweep (`docs/upstream-consumption-review-2026-07-27.md`
  method) picks these up.

## Cross-library consumption (wire into both CLAUDE.md files)

In order of preference, per program-architecture.md:
1. **Upstream lands** → both libraries consume from Mathlib at the next bump.
   Upstreaming IS the sharing mechanism; the aging report is the pressure.
2. **Single small lemma needed now** → COPY it into the second library, with a
   `-- copied-from: <repo> <module> (delete when upstream lands)` marker; the
   aging report greps for these markers in both repos too.
3. **Large block needed now** (the fixed-point tower case) → the consuming
   library takes a Lake git-dependency on the producing one, **pinned to a tag**.
   Named cost: pin lockstep — the consumer cannot bump Mathlib until the
   producer does. The aging report states, for each such dep, what upstream
   event dissolves it.

## Steps

1. Land (or receive) the first field-neutral block under `<Lib>/ForMathlib/`
   with the contract block on every file.
2. `test_formathlib_contract` + the aging report tool.
3. CLAUDE.md sections in both libraries: the contract, the three consumption
   modes, the deletion-at-pin-bump rule.
4. Update `docs/upstreaming.md` (mathfin) to reference the mechanics: the
   playbook now has a queue with timestamps, not just a log.
5. File the upstream issue/PR plan against Mathlib early — statement-level, before
   polishing everything. Upstream review cycles are long and start best from a
   skeleton the maintainers have seen coming; `docs/upstreaming.md` has the working
   method from BrownianMotion PR #446.

## Acceptance criteria

- [ ] Every `ForMathlib/` file carries the contract block; test enforces it.
- [ ] Aging report runs and shows the first entry with age 0.
- [ ] Both CLAUDE.md files carry the consumption rules.
- [ ] The upstream target module path is real (checked against the current Mathlib
      layout), and an issue/PR skeleton exists or is drafted.
- [ ] The block was searched for across the Lean ecosystem — not only Mathlib —
      before being staged, and the search is recorded.
