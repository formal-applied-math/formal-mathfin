/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.Foundations.NormalQuantile
public import MathFin.RiskMeasures.Gaussian
public import MathFin.RiskMeasures.GaussianValueAtRisk

/-!
# Exposure-profile closed forms for a Gaussian mark-to-market

For a mark-to-market value `V ~ N(μ, σ²)` at a future date, counterparty-exposure metrics admit
closed forms in `Φ` and the standard normal density `φ`:

  `EPE = E[max(V,0)] = μΦ(μ/σ) + σφ(μ/σ)`,
  `ENE = E[max(-V,0)] = μ - EPE`,
  `PFE_α = μ + σΦ⁻¹(α)`.

As in `RiskMeasures/Gaussian.lean`, we take the closed form as the *definition* of the exposure
metric (the library has no `Φ⁻¹`-integral machinery for the truncated-normal expectation itself);
`PFE_α` is literally the Gaussian VaR of `RiskMeasures/GaussianValueAtRisk.lean` restated in
exposure language. What we prove are the genuinely new algebraic relations among these closed
forms, plus the path-level aggregates (average and effective EPE) over a discrete exposure
profile, mirroring the positive-part pattern of `Performance/DownsideMetrics.lean`.

## Main definitions and results

* `expectedPositiveExposure` (EPE), `expectedNegativeExposure` (ENE), `potentialFutureExposure`
  (PFE_α): the Gaussian closed forms.
* `expectedNegativeExposure_eq` / `gaussianExposure_epe_sub_ene`: `ENE = μ - EPE` and its
  rearrangement `EPE - ENE = 2·EPE - μ`.
* `potentialFutureExposure_eq_gaussianVaR`: `PFE_α` is exactly `gaussianVaR μ σ (Φ⁻¹ α)`.
* `averageExposure`: the trapezoid-weighted time-average of a discrete EPE profile.
* `effectiveExposure`: the running maximum of a discrete EPE profile (monotone, by construction).
-/

@[expose] public section

namespace MathFin

open Set ProbabilityTheory

variable {μ σ α : ℝ}

/-- **Expected positive exposure** of a Gaussian mark-to-market `V ~ N(μ,σ²)`:
`EPE = μΦ(μ/σ) + σφ(μ/σ)`. -/
noncomputable def expectedPositiveExposure (μ σ : ℝ) : ℝ :=
  μ * Phi (μ / σ) + σ * gaussianPDFReal 0 1 (μ / σ)

/-- **Expected negative exposure** `ENE = E[max(-V,0)] = μ - EPE` (since `max(V,0) - max(-V,0) =
V`, so `E[max(-V,0)] = E[V] - E[max(V,0)] = μ - EPE`). -/
noncomputable def expectedNegativeExposure (μ σ : ℝ) : ℝ :=
  μ - expectedPositiveExposure μ σ

/-- **Potential future exposure** at level `α`: `PFE_α = μ + σΦ⁻¹(α)`, the Gaussian value-at-risk
of the mark-to-market value restated in exposure language. -/
noncomputable def potentialFutureExposure (μ σ α : ℝ) : ℝ :=
  gaussianVaR μ σ (PhiInv α)

/-- `ENE` unfolds immediately from its definition `ENE = μ - EPE` — stated as a standalone lemma
for readability at call sites. -/
@[simp] lemma expectedNegativeExposure_eq (μ σ : ℝ) :
    expectedNegativeExposure μ σ = μ - expectedPositiveExposure μ σ := rfl

/-- `EPE + ENE = EPE - (EPE - μ) = μ`'s rearrangement: `EPE - ENE = 2·EPE - μ`. -/
lemma gaussianExposure_epe_sub_ene (μ σ : ℝ) :
    expectedPositiveExposure μ σ - expectedNegativeExposure μ σ =
      2 * expectedPositiveExposure μ σ - μ := by
  unfold expectedNegativeExposure
  ring

/-- `EPE + ENE = μ`: the two exposures sum to the expected mark-to-market value, directly from the
definition `ENE = μ - EPE`. -/
lemma gaussianExposure_epe_add_ene (μ σ : ℝ) :
    expectedPositiveExposure μ σ + expectedNegativeExposure μ σ = μ := by
  unfold expectedNegativeExposure
  ring

/-- `PFE_α` is literally the Gaussian VaR at quantile `Φ⁻¹(α)`. -/
lemma potentialFutureExposure_eq_gaussianVaR (μ σ α : ℝ) :
    potentialFutureExposure μ σ α = gaussianVaR μ σ (PhiInv α) := rfl

/-- `PFE` is affine in `(μ, σ)` with slope `Φ⁻¹(α)` — same algebraic shape as `gaussianVaR`. -/
lemma potentialFutureExposure_eq (μ σ α : ℝ) :
    potentialFutureExposure μ σ α = μ + σ * PhiInv α := rfl

/-- At the `50%` level, `PFE` reduces to the expected mark-to-market `μ` (since `Φ⁻¹(1/2) = 0` by
`Phi_zero` and `Phi_eq_iff`). -/
lemma potentialFutureExposure_half (μ σ : ℝ) :
    potentialFutureExposure μ σ (1 / 2) = μ := by
  have hhalf : (1:ℝ)/2 ∈ Ioo (0:ℝ) 1 := by constructor <;> norm_num
  have hz : PhiInv (1/2 : ℝ) = 0 := ((Phi_eq_iff hhalf).mp Phi_zero).symm
  rw [potentialFutureExposure_eq, hz]
  ring

/-- A discrete exposure profile `EPE(tᵢ)` at times `t`, weighted by the trapezoid rule over
consecutive gaps `t_{i+1} - t_i`: the **average EPE** over `[t_0, t_n]`. -/
noncomputable def averageExposure {n : ℕ} (t : Fin (n + 1) → ℝ) (epe : Fin (n + 1) → ℝ) : ℝ :=
  if t (Fin.last n) = t 0 then 0 else
    (∑ i : Fin n, (epe i.castSucc + epe i.succ) / 2 * (t i.succ - t i.castSucc)) /
      (t (Fin.last n) - t 0)

/-- **Effective EPE**: the running maximum of a discrete EPE profile, `EEPE(tₖ) = max_{i ≤ k}
EPE(tᵢ)`, mirroring `maximumDrawdown`'s running-extremum pattern. -/
noncomputable def effectiveExposure {n : ℕ} (epe : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun k ↦ (Finset.univ.filter (· ≤ k)).sup' ⟨0, by simp⟩ epe

/-- **Effective EPE is monotone** in the profile index: `i ≤ j → EEPE(tᵢ) ≤ EEPE(tⱼ)`, since the
running-maximum window only grows. -/
theorem effectiveExposure_monotone {n : ℕ} (epe : Fin (n + 1) → ℝ) :
    Monotone (effectiveExposure epe) := by
  intro i j hij
  unfold effectiveExposure
  apply Finset.sup'_mono
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  exact hk.trans hij

/-- **Effective EPE dominates the raw exposure**: `EPE(tₖ) ≤ EEPE(tₖ)`, since `k` is itself one of
the indices in the running-max window. -/
theorem le_effectiveExposure {n : ℕ} (epe : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    epe k ≤ effectiveExposure epe k := by
  unfold effectiveExposure
  exact Finset.le_sup' epe (by simp)

end MathFin
