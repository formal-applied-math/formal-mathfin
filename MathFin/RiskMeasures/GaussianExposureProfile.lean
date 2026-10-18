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
  `ENE = E[max(-V,0)] = EPE - μ`,
  `PFE_α = μ + σΦ⁻¹(α)`.

As in `RiskMeasures/Gaussian.lean`, we take the closed form as the *definition* of the exposure
metric rather than wiring it to the truncated-normal expectation `E[max(V,0)]` itself — a
derivation exists in principle: `RiskMeasures/RockafellarUryasev.lean`'s
`integral_shortfall_gaussian` already gives this exact `μΦ(μ/σ) + σφ(μ/σ)` shape at the
degenerate threshold `c = 0`, and `RiskMeasures/GaussianExpectedShortfall.lean`'s
`rockafellarUryasev_of_hasLaw_gaussianReal` is the law-level bridge that would carry it to an
actual random variable; connecting the two is left for a follow-up rather than done here.
`PFE_α` is literally the Gaussian
VaR of `RiskMeasures/GaussianValueAtRisk.lean` restated in exposure language. What we prove are the
algebraic relations among these closed forms (rearrangements of the definitions), plus the
path-level aggregates (average and effective EPE) over a discrete exposure profile, mirroring the
positive-part pattern of `Performance/DownsideMetrics.lean`.

## Main definitions and results

* `expectedPositiveExposure` (EPE), `expectedNegativeExposure` (ENE), `potentialFutureExposure`
  (PFE_α): the Gaussian closed forms.
* `expectedNegativeExposure_eq` / `gaussianExposure_epe_add_ene`: `ENE = EPE - μ` and its
  rearrangement `EPE + ENE = 2·EPE - μ`; `gaussianExposure_epe_sub_ene`: `EPE - ENE = μ`.
* `potentialFutureExposure_eq_gaussianVaR`: `PFE_α` is exactly `gaussianVaR μ σ (Φ⁻¹ α)`.
* `averageExposure`: the trapezoid-weighted time-average of a discrete EPE profile.
* `effectiveExposure`: the running maximum of a discrete EPE profile — Basel's *Effective EE*
  (monotone, by construction); not to be confused with *Effective EPE*, its time-average.
-/

@[expose] public section

namespace MathFin

open ProbabilityTheory

/-- **Expected positive exposure** of a Gaussian mark-to-market `V ~ N(μ,σ²)`:
`EPE = μΦ(μ/σ) + σφ(μ/σ)`. -/
noncomputable def expectedPositiveExposure (μ σ : ℝ) : ℝ :=
  μ * Phi (μ / σ) + σ * gaussianPDFReal 0 1 (μ / σ)

/-- **Expected negative exposure** `ENE = E[max(-V,0)] = EPE - μ` (since `max(V,0) - max(-V,0) =
V`, so `max(-V,0) = max(V,0) - V`, i.e. `E[max(-V,0)] = E[max(V,0)] - E[V] = EPE - μ`). -/
noncomputable def expectedNegativeExposure (μ σ : ℝ) : ℝ :=
  expectedPositiveExposure μ σ - μ

/-- **Potential future exposure** at level `α`: `PFE_α = μ + σΦ⁻¹(α)`, the Gaussian value-at-risk
of the mark-to-market value restated in exposure language. -/
noncomputable def potentialFutureExposure (μ σ α : ℝ) : ℝ :=
  gaussianVaR μ σ (PhiInv α)

/-- `ENE` unfolds immediately from its definition `ENE = EPE - μ` — stated as a standalone lemma
for readability at call sites. -/
@[simp] lemma expectedNegativeExposure_eq (μ σ : ℝ) :
    expectedNegativeExposure μ σ = expectedPositiveExposure μ σ - μ := rfl

/-- `EPE - ENE = EPE - (EPE - μ) = μ`: the two exposures recover the expected mark-to-market value,
directly from the definition `ENE = EPE - μ`. -/
lemma gaussianExposure_epe_sub_ene (μ σ : ℝ) :
    expectedPositiveExposure μ σ - expectedNegativeExposure μ σ = μ := by
  unfold expectedNegativeExposure
  ring

/-- `EPE + ENE = EPE + (EPE - μ) = 2·EPE - μ`'s rearrangement of the definition. -/
lemma gaussianExposure_epe_add_ene (μ σ : ℝ) :
    expectedPositiveExposure μ σ + expectedNegativeExposure μ σ =
      2 * expectedPositiveExposure μ σ - μ := by
  unfold expectedNegativeExposure
  ring

/-- `PFE_α` is literally the Gaussian VaR at quantile `Φ⁻¹(α)`. -/
lemma potentialFutureExposure_eq_gaussianVaR (μ σ α : ℝ) :
    potentialFutureExposure μ σ α = gaussianVaR μ σ (PhiInv α) := rfl

/-- `PFE` is affine in `(μ, σ)` with slope `Φ⁻¹(α)` — same algebraic shape as `gaussianVaR`. -/
lemma potentialFutureExposure_eq (μ σ α : ℝ) :
    potentialFutureExposure μ σ α = μ + σ * PhiInv α := rfl

/-- At the `50%` level, `PFE` reduces to the expected mark-to-market `μ` (since `Φ⁻¹(1/2) = 0` by
`PhiInv_half`). -/
lemma potentialFutureExposure_half (μ σ : ℝ) :
    potentialFutureExposure μ σ (1 / 2) = μ := by
  rw [potentialFutureExposure_eq, PhiInv_half]
  ring

/-- A discrete exposure profile `EPE(tᵢ)` at times `t`, weighted by the trapezoid rule over
consecutive gaps `t_{i+1} - t_i`: the **average EPE** over `[t_0, t_n]`. -/
noncomputable def averageExposure {n : ℕ} (t : Fin (n + 1) → ℝ) (epe : Fin (n + 1) → ℝ) : ℝ :=
  (∑ i : Fin n, (epe i.castSucc + epe i.succ) / 2 * (t i.succ - t i.castSucc)) /
    (t (Fin.last n) - t 0)

/-- **Effective EE** (Basel terminology: *Effective Expected Exposure*, not to be confused with
*Effective EPE*, its time-average over the first year): the running maximum of a discrete EPE
profile, `EE_eff(tₖ) = max_{i ≤ k} EPE(tᵢ)`, mirroring `maximumDrawdown`'s running-extremum
pattern. -/
noncomputable def effectiveExposure {n : ℕ} (epe : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun k ↦ (Finset.univ.filter (· ≤ k)).sup' ⟨0, by simp⟩ epe

/-- **Effective EE is monotone** in the profile index: `i ≤ j → EE_eff(tᵢ) ≤ EE_eff(tⱼ)`, since the
running-maximum window only grows. -/
theorem effectiveExposure_monotone {n : ℕ} (epe : Fin (n + 1) → ℝ) :
    Monotone (effectiveExposure epe) := by
  intro i j hij
  unfold effectiveExposure
  apply Finset.sup'_mono
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  exact hk.trans hij

/-- **Effective EE dominates the raw exposure**: `EPE(tₖ) ≤ EE_eff(tₖ)`, since `k` is itself one of
the indices in the running-max window. -/
theorem le_effectiveExposure {n : ℕ} (epe : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    epe k ≤ effectiveExposure epe k := by
  unfold effectiveExposure
  exact Finset.le_sup' epe (by simp)

end MathFin
