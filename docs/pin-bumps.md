# Bumping the pins

The library builds against exact versions of Lean, Mathlib, BrownianMotion and the other Lake
packages. [`lean-toolchain`](../lean-toolchain), [`lakefile.lean`](../lakefile.lean) and
[`lake-manifest.json`](../lake-manifest.json) are the pin files. This page says when the pins move
and what has to be true before a bump merges.

## Cadence

A bump moves Lean, Mathlib and BrownianMotion together, as the recent ones did, to revisions that
build together. MathFin builds on BrownianMotion, so it cannot move to a Lean or Mathlib version
that BrownianMotion does not build on.

The six bumps recorded in the history of `lean-toolchain` came 12 to 56 days apart:

| Date | Lean |
|---|---|
| 2026-05-27 | v4.30.0-rc2 |
| 2026-06-11 | v4.30.0 |
| 2026-06-23 | v4.31.0 |
| 2026-07-27 | v4.32.0 |
| 2026-09-09 | v4.33.0-rc1 |
| 2026-11-04 | v4.35.0 |

Bump when BrownianMotion's `master` has moved to a newer Lean release, preferring a stable release
to a release candidate, and when a full re-verification (below) can be run. Do not bump for its
own sake: a bump restales the whole corpus.

## What has to be true before it merges

The order is the one described in the header of
[`.github/workflows/pin-bump.yml`](../.github/workflows/pin-bump.yml):

1. **The library builds at the new pins.** The `pin-bump build` workflow runs on any pull request
   that changes a pin file, and does nothing else. A green run means there is something worth
   verifying, not that the corpus is verified. Locally, `lake build && lake lint` must exit
   cleanly.
2. **The axiom audit is regenerated.** Run `python3 -m tools.verify.axiom_audit_gen --write` and
   commit the result, so that `MathFin/AxiomAuditGen.lean` is byte-fresh
   (`tests/test_values.py` checks it) and every cited theorem still depends only on `propext`,
   `Classical.choice` and `Quot.sound`.
3. **The whole corpus is re-verified.** A pin bump changes the pin part of every entry's input
   hash, so every row of `verification_ledger.json` goes stale. The `ledger sweep` workflow does
   this on a runner for pull requests that change a pin file, in up to twelve parallel shards, where
   one machine would take many hours. It
   commits the refreshed ledger to the branch. Do not use `ledger rebase-pins` instead: it is not a
   shortcut after a substantive bump. `python3 -m tools.verify.ledger status` must exit 0.
4. **The repository checks pass.** `python3 -m pytest tests/ -q`, then the `build` workflow, which
   runs these gates before the Lean build.

## Re-test the automation at each bump

[`CLAUDE.md`](../CLAUDE.md) records two tool verdicts that depend on the Lean version. Re-test them
when the pins move, and update the note if the answer changed:

- **`grind`**: it does not close nonlinear real inequalities on the corpus sample, and the note says
  to re-test this at each toolchain bump. The trials and the boundary are in
  [`patterns.md`](patterns.md).
- **`hammer`** (LeanHammer): the 2026-06-06 pilot verdict has expired, because the pilot ran one
  Lean version off its target. The `hammer-retest` workflow takes the LeanHammer revision as an
  input and must target the Lean version of the new pins. The procedure is in
  [`hammer-pilot-2026-06-06.md`](hammer-pilot-2026-06-06.md).

## The values review

A bump does not itself require a values review. The review cadence is enforced separately:
`tests/test_values.py::test_values_review_is_current` fails once the corpus has grown more than
12 entries past the last recorded review ([`values-review.md`](values-review.md)). If a bump pull
request fails that test, the cause is corpus growth, not the bump.
