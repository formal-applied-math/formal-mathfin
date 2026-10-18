/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib

/-!
# Discrete Funding Valuation Adjustment (FVA) and telescoping discount factors

Funding Valuation Adjustment nets a funding COST against a funding BENEFIT (Hull & White, "The
FVA Debate", 2012; Hull, *Options, Futures and Other Derivatives*, XVA chapter). This file's
`discreteFVA` is the additive value adjustment (negative = net cost to the bank); in Hull's own
magnitude convention `FVA = FCA − FBA` (both ≥ 0), `discreteFVA` equals `-(FCA - FBA)`. Over a
discrete tenor with time step `Δt`, funding spreads `FS_B`
(borrowing, applied to the bank's positive exposure it must fund — a cost) and `FS_L` (lending,
applied to negative exposure — the bank effectively holds the counterparty's money and earns a
funding *benefit* from it), and expected discounted positive/negative exposure `EDPE(tᵢ)`,
`EDNE(tᵢ)` (both nonnegative magnitudes):

  `FVA = -∑ᵢ EDPE(tᵢ) · FS_B · Δt + ∑ᵢ EDNE(tᵢ) · FS_L · Δt`.

The funding-benefit leg is ADDED back, not subtracted: with equal spreads `FS_B = FS_L = s`, this
collapses to `FVA = -s · ∑ᵢ (EDPE(tᵢ) - EDNE(tᵢ)) · Δt`, the textbook `-s_F · ∫ EE(t) dt` form over
*net* expected exposure. (An earlier version of this file subtracted both legs, which silently
dropped the funding-benefit netting and made `FVA ≤ 0` hold unconditionally — false under the
correct convention, since a large funding benefit can push net FVA non-negative.)

The clean "telescoping" discount-factor form writes the funding-spread discount factor
`DF(t) = exp(-FS(0,t)·t)`, an alternative to the product-rule approximation `FS·Δt` above. Both
forms are recorded; `fundingDiscountFactor_telescoping_sum` is the headline identity that the
*unweighted* sum of discount-factor drops collapses to the two endpoints `DF(t₀) - DF(tₙ)` — this
is a pure telescoping fact about `DF` and carries no exposure profile (the exposure-weighted sum
`∑ᵢ EDPE(tᵢ)·[DF(tᵢ₋₁) - DF(tᵢ)]` does not telescope unless `EDPE` is constant).

Scope note: `EDPE`/`EDNE` are taken as free parameters (any `Fin n → ℝ` profiles) rather than
imported from `GaussianExposureProfile.lean`. This is a deliberate loose coupling, matching
`DVA.lean`: a caller can supply `expectedPositiveExposure`/`expectedNegativeExposure` from that
file, a collateralized
profile from `CollateralizedExposure.lean`, or any other exposure model, without this file
depending on their distributional assumptions.

## Main definitions and results

* `discreteFVA`: the `FS·Δt` sum form, indexed over uniform buckets.
* `discreteFVA_eq_net_total`: `FVA = (FS_L · ∑EDNE - FS_B · ∑EDPE) · Δt` in closed form
  (linearity of the two sums).
* `discreteFVA_le_fundingBenefit`, `discreteFVA_ge_neg_fundingCost`: with nonnegative spreads,
  exposures and `Δt`, FVA is sandwiched between the negative of its funding-cost leg and its
  funding-benefit leg — the correct replacement for an unconditional sign claim, since funding
  benefit can outweigh funding cost (and vice versa) depending on the exposure profile.
* `fundingDiscountFactor`: `DF(t) = exp(-FS·t)` (constant-spread case).
* `fundingDiscountFactor_telescoping_sum`: `∑ᵢ [DF(tᵢ₋₁) - DF(tᵢ)] = DF(t₀) - DF(tₙ)`, the
  telescoping collapse over a finite bucket sequence.
-/

@[expose] public section

namespace MathFin

variable {n : ℕ} (FSB FSL dt : ℝ) (EDPE EDNE : Fin n → ℝ)

/-- **Discrete FVA**, the `FS·Δt` sum form over `n` uniform buckets of width `Δt`, netting the
funding-cost leg against the funding-benefit leg:
`FVA = -∑ᵢ EDPE(tᵢ)·FS_B·Δt + ∑ᵢ EDNE(tᵢ)·FS_L·Δt`. -/
noncomputable def discreteFVA (FSB FSL dt : ℝ) (EDPE EDNE : Fin n → ℝ) : ℝ :=
  -(∑ i : Fin n, EDPE i * FSB * dt) + ∑ i : Fin n, EDNE i * FSL * dt

/-- **Closed form**: `FVA = (FS_L · ∑EDNE - FS_B · ∑EDPE) · Δt`, by factoring the shared `Δt` and
spread out of each sum. -/
theorem discreteFVA_eq_net_total :
    discreteFVA FSB FSL dt EDPE EDNE =
      (FSL * (∑ i : Fin n, EDNE i) - FSB * (∑ i : Fin n, EDPE i)) * dt := by
  unfold discreteFVA
  have h1 : ∑ i : Fin n, EDPE i * FSB * dt = (∑ i : Fin n, EDPE i) * (FSB * dt) := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ ↦ by ring
  have h2 : ∑ i : Fin n, EDNE i * FSL * dt = (∑ i : Fin n, EDNE i) * (FSL * dt) := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [h1, h2]
  ring

/-- **FVA is bounded above by its funding-benefit leg**: with nonnegative borrowing spread,
positive exposure and `Δt`, the funding-cost leg can only pull FVA down, never past the
funding-benefit leg. (The funding-cost and funding-benefit legs can each dominate depending on
the exposure profile, so FVA has no fixed sign in general — this replaces an earlier,
incorrect unconditional `FVA ≤ 0` claim that silently assumed no funding benefit.) -/
theorem discreteFVA_le_fundingBenefit (hFSB : 0 ≤ FSB) (hEDPE : ∀ i, 0 ≤ EDPE i) (hdt : 0 ≤ dt) :
    discreteFVA FSB FSL dt EDPE EDNE ≤ FSL * (∑ i : Fin n, EDNE i) * dt := by
  rw [discreteFVA_eq_net_total]
  have h1 : 0 ≤ FSB * ∑ i : Fin n, EDPE i :=
    mul_nonneg hFSB (Finset.sum_nonneg fun i _ ↦ hEDPE i)
  nlinarith [mul_nonneg h1 hdt]

/-- **FVA is bounded below by the negative of its funding-cost leg**: with nonnegative lending
spread, negative exposure and `Δt`, the funding-benefit leg can only lift FVA up, never below
the negative of the funding-cost leg. -/
theorem discreteFVA_ge_neg_fundingCost (hFSL : 0 ≤ FSL) (hEDNE : ∀ i, 0 ≤ EDNE i) (hdt : 0 ≤ dt) :
    -(FSB * (∑ i : Fin n, EDPE i)) * dt ≤ discreteFVA FSB FSL dt EDPE EDNE := by
  rw [discreteFVA_eq_net_total]
  have h2 : 0 ≤ FSL * ∑ i : Fin n, EDNE i :=
    mul_nonneg hFSL (Finset.sum_nonneg fun i _ ↦ hEDNE i)
  nlinarith [mul_nonneg h2 hdt]

/-- The (constant-spread) **funding discount factor**: `DF(t) = exp(-FS·t)`. -/
noncomputable def fundingDiscountFactor (FS t : ℝ) : ℝ := Real.exp (-(FS * t))

/-- `DF(0) = 1`. -/
@[simp] lemma fundingDiscountFactor_zero (FS : ℝ) : fundingDiscountFactor FS 0 = 1 := by
  unfold fundingDiscountFactor
  simp

/-- **Telescoping discount factors**: over a finite tenor `t : ℕ → ℝ` and `n` buckets, the sum of
per-bucket discount-factor drops collapses to the two endpoints,
`∑ᵢ [DF(tᵢ) - DF(tᵢ₊₁)] = DF(t₀) - DF(tₙ)` — the clean telescoping identity underlying the
discount-factor form (the exposure-weighted analogue of the `FS·Δt` sum does not telescope; see
the module docstring). A direct instance of Mathlib's generic reversed-telescoping-sum lemma
`Finset.sum_range_sub'`. -/
theorem fundingDiscountFactor_telescoping_sum (t : ℕ → ℝ) (FS : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n,
        (fundingDiscountFactor FS (t i) - fundingDiscountFactor FS (t (i + 1))) =
      fundingDiscountFactor FS (t 0) - fundingDiscountFactor FS (t n) :=
  Finset.sum_range_sub' (fun i ↦ fundingDiscountFactor FS (t i)) n

end MathFin
