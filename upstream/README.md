# upstream/

Draft files for upstream submission. Not part of this project's
verification surface — these proofs may or may not be in their final form,
and they target *other* repositories' module trees.

Each builds clean against the same Lean/Mathlib/BrownianMotion pins used
in the main project (see `lake-manifest.json` at the repo root). Nothing
under `MathFin/` imports any of these files; they live here so the
proposed code is reviewable before a PR is open.

## brownian-motion/

Drafts targeting [`RemyDegenne/brownian-motion`](https://github.com/RemyDegenne/brownian-motion).

- `Martingale.lean` — two `IsFilteredPreBrownian` martingale identities:
  - `IsFilteredPreBrownian.squareSubTime_isMartingale` (`t ↦ X_t² − t`)
  - `IsFilteredPreBrownian.waldExponential_isMartingale` (`t ↦ exp(α X_t − α² t / 2)` for any `α : ℝ`)
- `ISSUE_BODY.md` — draft GitHub issue / PR body for the same.
  (`StochasticInterval.lean` was **merged upstream** as PR #446 and removed from this
  directory on 2026-07-27; it now lives in BrownianMotion at
  `BrownianMotion/StochasticIntegral/StochasticInterval.lean`, under the upstream
  names `stochIcc`/`stochIco`/`stochIoc`/`stochIoo`/`stochGraph`. Consume it from
  there — do not re-add a local copy.)

## mathlib/

Drafts targeting [`leanprover-community/mathlib4`](https://github.com/leanprover-community/mathlib4),
landing in `Mathlib/Probability/Distributions/Gaussian/Real.lean`.

- `RealTail.lean` — Gaussian tail + completing-the-square lemmas
  (`gaussianReal_zero_one_Iic_neg`, `gaussianReal_zero_one_Ioi_toReal`,
  `exp_mul_gaussianPDFReal_zero_one`, etc.).
- `PR_BODY.md` — draft PR body for the same.

## zulip/

Discussion drafts for the Lean Zulip community (Mathlib, BrownianMotion,
maintainer channels). One file per intended interlocutor — these are
seed messages, not yet posted.
