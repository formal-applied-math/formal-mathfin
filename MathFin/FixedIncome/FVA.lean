/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib

/-!
# Discrete Funding Valuation Adjustment (FVA) and telescoping discount factors

Funding Valuation Adjustment prices the cost of funding uncollateralized exposure at a spread over
the risk-free rate. Over a discrete tenor with time step `Δt`, funding spreads `FS_B` (borrowing,
applied to the bank's positive exposure it must fund) and `FS_L` (lending, applied to negative
exposure), and expected discounted positive/negative exposure `EDPE(tᵢ)`, `EDNE(tᵢ)`:

  `FVA = -∑ᵢ EDPE(tᵢ) · FS_B · Δt - ∑ᵢ EDNE(tᵢ) · FS_L · Δt`.

The clean "telescoping" discount-factor form writes the funding-spread discount factor
`DF(t) = exp(-FS(0,t)·t)`, so that over a single step the funding cost accrued is exactly the
drop in the discount factor, `DF(tᵢ₋₁) - DF(tᵢ)`, rather than the product-rule approximation
`FS·Δt`. Both forms are recorded; `fva_telescoping_sum_eq_endpoints` is the headline identity that
a telescoping sum of discount-factor drops collapses to the two endpoints, independent of the
exposure profile in between.

Scope note: `EDPE`/`EDNE` are taken as free parameters (any `Fin n → ℝ` profiles) rather than
imported from `GaussianExposureProfile.lean`. This is a deliberate loose coupling, matching
`DVA.lean`: a caller can supply `expectedPositiveExposure`/`expectedNegativeExposure` from that
file, a collateralized
profile from `CollateralizedExposure.lean`, or any other exposure model, without this file
depending on their distributional assumptions.

## Main definitions and results

* `discreteFVA`: the `FS·Δt` sum form, indexed over uniform buckets.
* `discreteFVA_eq_neg_total`: `FVA = -(FS_B · PV(EDPE) + FS_L · PV(EDNE)) · Δt` in closed form
  (linearity of the two sums).
* `fundingDiscountFactor`: `DF(t) = exp(-FS·t)` (constant-spread case).
* `fundingDiscountFactor_telescoping_sum`: `∑ᵢ [DF(tᵢ₋₁) - DF(tᵢ)] = DF(t₀) - DF(tₙ)`, the
  telescoping collapse over a finite bucket sequence.
-/

@[expose] public section

namespace MathFin

variable {n : ℕ} (FSB FSL dt : ℝ) (EDPE EDNE : Fin n → ℝ)

/-- **Discrete FVA**, the `FS·Δt` sum form over `n` uniform buckets of width `Δt`:
`FVA = -∑ᵢ EDPE(tᵢ)·FS_B·Δt - ∑ᵢ EDNE(tᵢ)·FS_L·Δt`. -/
noncomputable def discreteFVA (FSB FSL dt : ℝ) (EDPE EDNE : Fin n → ℝ) : ℝ :=
  -(∑ i : Fin n, EDPE i * FSB * dt) - ∑ i : Fin n, EDNE i * FSL * dt

/-- **Closed form**: `FVA = -(FS_B · ∑EDPE + FS_L · ∑EDNE) · Δt`, by factoring the shared `Δt` and
spread out of each sum. -/
theorem discreteFVA_eq_neg_total :
    discreteFVA FSB FSL dt EDPE EDNE =
      -(FSB * (∑ i : Fin n, EDPE i) + FSL * (∑ i : Fin n, EDNE i)) * dt := by
  unfold discreteFVA
  have h1 : ∑ i : Fin n, EDPE i * FSB * dt = (∑ i : Fin n, EDPE i) * (FSB * dt) := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ ↦ by ring
  have h2 : ∑ i : Fin n, EDNE i * FSL * dt = (∑ i : Fin n, EDNE i) * (FSL * dt) := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [h1, h2]
  ring

/-- **FVA is the negative of the funding cost**: if both spreads and both exposure profiles are
nonnegative, `FVA ≤ 0` (funding uncollateralized exposure is a cost, not a benefit). -/
theorem discreteFVA_nonpos (hFSB : 0 ≤ FSB) (hFSL : 0 ≤ FSL) (hdt : 0 ≤ dt)
    (hEDPE : ∀ i, 0 ≤ EDPE i) (hEDNE : ∀ i, 0 ≤ EDNE i) :
    discreteFVA FSB FSL dt EDPE EDNE ≤ 0 := by
  rw [discreteFVA_eq_neg_total]
  have h1 : 0 ≤ FSB * ∑ i : Fin n, EDPE i :=
    mul_nonneg hFSB (Finset.sum_nonneg fun i _ ↦ hEDPE i)
  have h2 : 0 ≤ FSL * ∑ i : Fin n, EDNE i :=
    mul_nonneg hFSL (Finset.sum_nonneg fun i _ ↦ hEDNE i)
  have h3 : 0 ≤ (FSB * ∑ i : Fin n, EDPE i + FSL * ∑ i : Fin n, EDNE i) * dt :=
    mul_nonneg (by linarith) hdt
  linarith

/-- The (constant-spread) **funding discount factor**: `DF(t) = exp(-FS·t)`. -/
noncomputable def fundingDiscountFactor (FS t : ℝ) : ℝ := Real.exp (-(FS * t))

/-- `DF(0) = 1`. -/
@[simp] lemma fundingDiscountFactor_zero (FS : ℝ) : fundingDiscountFactor FS 0 = 1 := by
  unfold fundingDiscountFactor
  simp

/-- **Telescoping discount factors**: over a finite tenor `t : ℕ → ℝ` and `n` buckets, the sum of
per-bucket discount-factor drops collapses to the two endpoints,
`∑ᵢ [DF(tᵢ) - DF(tᵢ₊₁)] = DF(t₀) - DF(tₙ)`, regardless of the exposure profile — this is the
clean telescoping form that replaces the `FS·Δt` product-rule approximation. A direct instance of
Mathlib's generic reversed-telescoping-sum lemma `Finset.sum_range_sub'`. -/
theorem fundingDiscountFactor_telescoping_sum (t : ℕ → ℝ) (FS : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n,
        (fundingDiscountFactor FS (t i) - fundingDiscountFactor FS (t (i + 1))) =
      fundingDiscountFactor FS (t 0) - fundingDiscountFactor FS (t n) :=
  Finset.sum_range_sub' (fun i ↦ fundingDiscountFactor FS (t i)) n

end MathFin
