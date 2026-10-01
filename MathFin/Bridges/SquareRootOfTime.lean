/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.RiskMeasures.GaussianValueAtRisk
public import MathFin.Foundations.GaussianMoments
public import MathFin.Foundations.ItoLemma2D

/-!
# Bridge: the square-root-of-time rule is a theorem about Brownian increments

`RiskMeasures/Gaussian.lean` records the square-root-of-time scaling of the Gaussian VaR formula
as an algebraic identity (`gaussianVaR_volatility_scaling`). Here it is a statement about the loss
of a geometric Brownian motion `S_t = gbmValue S₀ μ σ t B_t` (`Foundations/ItoLemma2D.lean`) driven
by a pre-Brownian motion `B`. The `h`-period loss `L = −log(S_{t+h}/S_t)` satisfies

  `VaR_α(L) = −(μ − σ²/2)·h + σ √h · Φ⁻¹(α)`   (`σ ≥ 0`).

The volatility term scales with `√h` and the drift term with `h` (McNeil–Frey–Embrechts,
Example 9.4; QRM Exercises 3.16, 9.13). The loss is Gaussian because the Brownian increment is
(`hasLaw_increment`), and its VaR is read off `valueAtRisk_of_hasLaw_gaussianReal`.

A certified unification of two known textbook facts, not new finance. The rule is exact here
because the increments are Gaussian. For heavy-tailed or volatility-clustering returns it is only
an approximation, which is the stylized-facts caveat of MFE §3.1.

## Main results

* `log_gbmValue_div`: the `h`-period log-return of GBM is `(μ − σ²/2)·h + σ·(B_{t+h} − B_t)`.
* `valueAtRisk_gbm_loss`: the square-root-of-time rule for the GBM loss.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- The log-return of GBM over `[t, t + h]` is its drift plus the scaled Brownian increment. -/
lemma log_gbmValue_div {S₀ : ℝ} (hS₀ : 0 < S₀) (μ σ t h x y : ℝ) :
    Real.log (gbmValue S₀ μ σ (t + h) y / gbmValue S₀ μ σ t x) =
      (μ - σ ^ 2 / 2) * h + σ * (y - x) := by
  unfold gbmValue
  rw [mul_div_mul_left _ _ hS₀.ne', ← Real.exp_sub, Real.log_exp]
  ring

/-- **The square-root-of-time rule**: the `h`-period loss `−log(S_{t+h}/S_t)` of a geometric
Brownian motion has `VaR_α = −(μ − σ²/2)·h + σ√h · Φ⁻¹(α)`, the Gaussian closed form with
volatility `σ√h`. -/
theorem valueAtRisk_gbm_loss {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) {S₀ : ℝ}
    (hS₀ : 0 < S₀) (μ : ℝ) {σ : ℝ} (hσ : 0 ≤ σ) (t h : ℝ≥0) {α : ℝ} (hα : α ∈ Ioo 0 1) :
    valueAtRisk (fun ω ↦ -Real.log (gbmValue S₀ μ σ (t + h) (B (t + h) ω) /
        gbmValue S₀ μ σ t (B t ω))) P α =
      gaussianVaR (-((μ - σ ^ 2 / 2) * h)) (σ * √(h : ℝ)) (PhiInv α) := by
  set a := -((μ - σ ^ 2 / 2) * h)
  -- the loss is the affine image `a + (−σ)·Z` of the increment `Z = B_{t+h} − B_t ~ N(0, h)`
  have hloss : (fun ω ↦ -Real.log (gbmValue S₀ μ σ (t + h) (B (t + h) ω) /
      gbmValue S₀ μ σ t (B t ω))) = (fun z ↦ a + (-σ) * z) ∘ fun ω ↦ B (t + h) ω - B t ω := by
    ext ω
    simp only [Function.comp_apply, log_gbmValue_div hS₀, a]
    ring
  have hZ : HasLaw (fun ω ↦ B (t + h) ω - B t ω) (gaussianReal 0 h) P := by
    simpa using hasLaw_increment hB (le_self_add : t ≤ t + h)
  have hmap : HasLaw (fun z ↦ a + (-σ) * z) (gaussianReal a ⟨σ ^ 2 * h, by positivity⟩)
      (gaussianReal 0 h) := by
    refine ⟨by fun_prop, ?_⟩
    rw [show (fun z ↦ a + (-σ) * z) = (· + a) ∘ ((-σ) * ·) by ext; simp [add_comm],
      ← Measure.map_map (measurable_add_const a) (measurable_const_mul _),
      gaussianReal_map_const_mul, gaussianReal_map_add_const, mul_zero, zero_add]
    congr 1
    ext
    simp
    rfl
  rw [hloss, valueAtRisk_of_hasLaw_gaussianReal (hmap.comp hZ) hα]
  congr 1
  change √(σ ^ 2 * (h : ℝ)) = _
  rw [Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq hσ]

end MathFin
