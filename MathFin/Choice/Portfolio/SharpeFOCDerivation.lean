/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Choice.Portfolio.CAPMEquilibrium
public import MathFin.Choice.Portfolio.Markowitz
public import MathFin.Choice.Performance.Ratios
public import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# Markowitz cross-product FOC derived from Sharpe-ratio maximization

The pre-existing `tangentTwo_satisfies_FOC` in `Choice.Portfolio.TangentPortfolio`
verifies that the closed-form weight `tangentWeightTwo` satisfies the
cross-product FOC `r₂ · (Σw)₁ = r₁ · (Σw)₂` by direct algebra (`ring`). It
does **not derive** that FOC from a maximization problem.

This file closes that gap. It

1. defines the two-asset Sharpe-ratio-squared
   `Sh²(w) = E(w)² / V(w)` where `E(w) = w r₁ + (1 − w) r₂`,
   `V(w) = w² σ₁² + (1 − w)² σ₂² + 2 w (1 − w) ρ σ₁ σ₂` (the library's `portfolioVarTwo σ₁ σ₂ ρ w`,
   `Choice/Portfolio/Markowitz.lean`);
2. proves `HasDerivAt` of `Sh²` with the textbook formula
   `Sh²'(w) = (2 E E' V − E² V') / V²`;
3. shows the numerator factors as
   `2 E E' V − E² V' = 2 E · (r₁ · (Σw)₂ − r₂ · (Σw)₁)`;
4. concludes that the critical points of `Sh²` (where `E ≠ 0`, `V ≠ 0`)
   are precisely the points where the cross-product FOC holds.

## Why this is "first principles"

The existing infrastructure stops at "the closed form satisfies the FOC".
This file derives the FOC itself from a maximization problem — closing the
loop between the optimization-theoretic and algebraic perspectives.

## Main definitions

* `expectedReturnTwo`: the two-asset expected return `w r₁ + (1 − w) r₂`.
* `sharpeSqTwo`: the squared Sharpe ratio `E(w)² / V(w)` as a function of `w`.

## Main results

* `sharpeSqTwo_eq_sharpeRatio_sq`: for `V(w) ≥ 0`, `Sh²(w)` is the squared `sharpeRatio` of the
  portfolio return (zero risk-free rate) at volatility `√V(w)`.
* `marginalVariance_covTwo_zero`, `marginalVariance_covTwo_one`: the components `(Σw)₁`, `(Σw)₂` of
  `marginalVariance` (`Choice/Portfolio/CAPMEquilibrium.lean`) at `covTwo` and the
  weights `(w, 1 − w)`.
* `portfolioVarTwo_eq_sum_mul_marginalVar`: `V = w · (Σw)₁ + (1 − w) · (Σw)₂`.
* `hasDerivAt_portfolioVarTwo`: `V'(w) = 2 · ((Σw)₁ − (Σw)₂)`.
* `sharpeSqTwo_deriv_numerator_factored`: the derivative numerator
  factors through `r₁ (Σw)₂ − r₂ (Σw)₁`.
* `sharpeSqTwo_critical_iff_crossProduct_FOC`: critical-point
  characterisation (`E ≠ 0, V ≠ 0` regime).

## References

* [H. Markowitz, *Portfolio selection*][Markowitz1952]
* [Sharpe, *Capital asset prices*][Sharpe1964]

## Tags

Sharpe ratio maximization, tangent portfolio, first-order condition, Markowitz,
maximum Sharpe portfolio, MSC 91G10, JEL G11
-/

@[expose] public section

namespace MathFin

/-- Two-asset expected excess return parameterised by weight `w` on asset 1
(with `1 − w` on asset 2). -/
noncomputable def expectedReturnTwo (w r₁ r₂ : ℝ) : ℝ := w * r₁ + (1 - w) * r₂

/-- Marginal variance of asset 1 at `covTwo` and the weights `(w, 1 − w)`:
`(Σw)₁ = w σ₁² + (1−w) ρ σ₁ σ₂`. -/
lemma marginalVariance_covTwo_zero (σ₁ σ₂ ρ w : ℝ) :
    marginalVariance Finset.univ (covTwo σ₁ σ₂ ρ) ![w, 1 - w] 0 =
      w * σ₁ ^ 2 + (1 - w) * ρ * σ₁ * σ₂ := by
  simp only [marginalVariance, covTwo, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
  ring

/-- Marginal variance of asset 2 at `covTwo` and the weights `(w, 1 − w)`:
`(Σw)₂ = w ρ σ₁ σ₂ + (1−w) σ₂²`. -/
lemma marginalVariance_covTwo_one (σ₁ σ₂ ρ w : ℝ) :
    marginalVariance Finset.univ (covTwo σ₁ σ₂ ρ) ![w, 1 - w] 1 =
      w * ρ * σ₁ * σ₂ + (1 - w) * σ₂ ^ 2 := by
  simp only [marginalVariance, covTwo, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
  ring

/-- Two-asset Sharpe-ratio squared as a function of weight `w`. -/
noncomputable def sharpeSqTwo (w r₁ r₂ σ₁ σ₂ ρ : ℝ) : ℝ :=
  (expectedReturnTwo w r₁ r₂)^2 / (portfolioVarTwo σ₁ σ₂ ρ w)

/-- **The two-asset Sharpe ratio squared is the squared Sharpe ratio** of the portfolio return
with zero risk-free rate (`returns` are excess returns): `Sh²(w) = sharpeRatio E(w) 0 σ(w) ^ 2`,
with `σ(w) = √V(w)` the portfolio volatility. `V(w)` is the variance of `w R₁ + (1 − w) R₂`
(`portfolioVarTwo_eq_variance`, `Choice/Portfolio/MarkowitzLagrangian.lean`). -/
theorem sharpeSqTwo_eq_sharpeRatio_sq (w r₁ r₂ σ₁ σ₂ ρ : ℝ)
    (hV : 0 ≤ portfolioVarTwo σ₁ σ₂ ρ w) :
    sharpeSqTwo w r₁ r₂ σ₁ σ₂ ρ
      = sharpeRatio (expectedReturnTwo w r₁ r₂) 0 (√(portfolioVarTwo σ₁ σ₂ ρ w)) ^ 2 := by
  rw [sharpeSqTwo, sharpeRatio, sub_zero, div_pow, Real.sq_sqrt hV]

/-- **`V` is the weight-weighted sum of the marginal variances**:
`V(w) = w · (Σw)₁ + (1 − w) · (Σw)₂` (for `N` assets, compare
`portfolioVarN_eq_sum_mul_marginalVariance`, `Choice/Portfolio/CAPMEquilibrium.lean`). -/
lemma portfolioVarTwo_eq_sum_mul_marginalVar (σ₁ σ₂ ρ w : ℝ) :
    portfolioVarTwo σ₁ σ₂ ρ w =
      w * marginalVariance Finset.univ (covTwo σ₁ σ₂ ρ) ![w, 1 - w] 0
        + (1 - w) * marginalVariance Finset.univ (covTwo σ₁ σ₂ ρ) ![w, 1 - w] 1 := by
  rw [marginalVariance_covTwo_zero, marginalVariance_covTwo_one]
  unfold portfolioVarTwo
  ring

/-- **Derivative of `E(w) = w r₁ + (1 − w) r₂`** is `r₁ − r₂`. -/
lemma hasDerivAt_expectedReturnTwo (w r₁ r₂ : ℝ) :
    HasDerivAt (fun w' ↦ expectedReturnTwo w' r₁ r₂) (r₁ - r₂) w := by
  unfold expectedReturnTwo
  have h1 : HasDerivAt (fun w' : ℝ ↦ w' * r₁) r₁ w := by
    simpa using (hasDerivAt_id w).mul_const r₁
  have h_sub : HasDerivAt (fun w' : ℝ ↦ (1 : ℝ) - w') (-1) w := by
    simpa using (hasDerivAt_id w).const_sub 1
  have h2 : HasDerivAt (fun w' : ℝ ↦ (1 - w') * r₂) (-r₂) w := by
    have := h_sub.mul_const r₂
    simpa using this
  have h := h1.add h2
  convert h using 1

/-- **Derivative of `V(w) = w² σ₁² + (1−w)² σ₂² + 2 w (1−w) ρ σ₁ σ₂`** is
`V'(w) = 2 · ((Σw)₁ − (Σw)₂)`. Proof: polynomial rewrite of `V` in the form
`A w² + B w + C`, then `(A w² + B w + C)' = 2 A w + B`. -/
lemma hasDerivAt_portfolioVarTwo (σ₁ σ₂ ρ w : ℝ) :
    HasDerivAt (portfolioVarTwo σ₁ σ₂ ρ)
               (2 * (marginalVariance Finset.univ (covTwo σ₁ σ₂ ρ) ![w, 1 - w] 0
                 - marginalVariance Finset.univ (covTwo σ₁ σ₂ ρ) ![w, 1 - w] 1)) w := by
  -- Rewrite V as A w² + B w + C
  have h_v_poly : portfolioVarTwo σ₁ σ₂ ρ =
      (fun w' ↦ (σ₁^2 + σ₂^2 - 2*ρ*σ₁*σ₂) * w'^2 +
                 (-2*σ₂^2 + 2*ρ*σ₁*σ₂) * w' + σ₂^2) := by
    funext w'
    unfold portfolioVarTwo
    ring
  rw [h_v_poly]
  have h_sq : HasDerivAt (fun w' : ℝ ↦ w'^2) (2*w) w := by
    have := hasDerivAt_pow 2 w
    convert this using 1; push_cast; ring
  have h_term1 := h_sq.const_mul (σ₁^2 + σ₂^2 - 2*ρ*σ₁*σ₂)
  have h_term2 := (hasDerivAt_id w).const_mul (-2*σ₂^2 + 2*ρ*σ₁*σ₂)
  have h_term3 : HasDerivAt (fun _ : ℝ ↦ (σ₂^2 : ℝ)) 0 w := hasDerivAt_const w _
  have h := (h_term1.add h_term2).add h_term3
  convert h using 1 <;>
    first | rfl | (rw [marginalVariance_covTwo_zero, marginalVariance_covTwo_one]; ring)

/-- **Derivative of `E²(w)`** is `2 E (r₁ − r₂)`. -/
lemma hasDerivAt_expectedReturnTwo_sq (w r₁ r₂ : ℝ) :
    HasDerivAt (fun w' ↦ (expectedReturnTwo w' r₁ r₂)^2)
               (2 * expectedReturnTwo w r₁ r₂ * (r₁ - r₂)) w := by
  have h := (hasDerivAt_expectedReturnTwo w r₁ r₂).pow 2
  convert h using 1; push_cast; ring

/-- **Derivative of `Sh²(w) = E²/V`**: textbook formula `Sh²'(w) = (2EE'V − E²V')/V²`. -/
theorem hasDerivAt_sharpeSqTwo (w r₁ r₂ σ₁ σ₂ ρ : ℝ)
    (hV : portfolioVarTwo σ₁ σ₂ ρ w ≠ 0) :
    HasDerivAt (fun w' ↦ sharpeSqTwo w' r₁ r₂ σ₁ σ₂ ρ)
               ((2 * expectedReturnTwo w r₁ r₂ * (r₁ - r₂) *
                   portfolioVarTwo σ₁ σ₂ ρ w -
                 (expectedReturnTwo w r₁ r₂)^2 *
                   (2 * (marginalVariance Finset.univ (covTwo σ₁ σ₂ ρ) ![w, 1 - w] 0
                     - marginalVariance Finset.univ (covTwo σ₁ σ₂ ρ) ![w, 1 - w] 1))) /
                (portfolioVarTwo σ₁ σ₂ ρ w)^2) w := by
  unfold sharpeSqTwo
  exact (hasDerivAt_expectedReturnTwo_sq w r₁ r₂).div
        (hasDerivAt_portfolioVarTwo σ₁ σ₂ ρ w) hV

/-- **Algebraic factorization of the Sh² derivative numerator**:

  `2 E E' V − E² V' = 2 E · (r₁ (Σw)₂ − r₂ (Σw)₁)`.

This factorization is the algebraic content of the cross-product FOC: setting
the numerator to zero (with `E ≠ 0`) reduces to `r₁ (Σw)₂ = r₂ (Σw)₁`.

The identity is proved by `ring` after unfolding all definitions; the
non-trivial cancellation is that `(r₁ − r₂) V − E ((Σw)₁ − (Σw)₂)` simplifies
exactly to `r₁ (Σw)₂ − r₂ (Σw)₁`. -/
theorem sharpeSqTwo_deriv_numerator_factored (w r₁ r₂ σ₁ σ₂ ρ : ℝ) :
    2 * expectedReturnTwo w r₁ r₂ * (r₁ - r₂) * portfolioVarTwo σ₁ σ₂ ρ w -
        (expectedReturnTwo w r₁ r₂)^2 *
          (2 * (marginalVariance Finset.univ (covTwo σ₁ σ₂ ρ) ![w, 1 - w] 0
            - marginalVariance Finset.univ (covTwo σ₁ σ₂ ρ) ![w, 1 - w] 1)) =
      2 * expectedReturnTwo w r₁ r₂ *
        (r₁ * marginalVariance Finset.univ (covTwo σ₁ σ₂ ρ) ![w, 1 - w] 1
          - r₂ * marginalVariance Finset.univ (covTwo σ₁ σ₂ ρ) ![w, 1 - w] 0) := by
  rw [marginalVariance_covTwo_zero, marginalVariance_covTwo_one]
  unfold expectedReturnTwo portfolioVarTwo
  ring

/-- **Critical-point characterisation**: in the `E ≠ 0`, `V ≠ 0` regime, the
Sharpe-ratio squared has a critical point at `w` (i.e., `HasDerivAt Sh² 0 w`)
*if and only if* the cross-product FOC `r₂ (Σw)₁ = r₁ (Σw)₂` holds.

This is the first-principles derivation: the FOC arises as the
critical-point condition of a real maximization problem, not as a stated
algebraic identity. -/
theorem sharpeSqTwo_critical_iff_crossProduct_FOC
    (w r₁ r₂ σ₁ σ₂ ρ : ℝ) (hV : portfolioVarTwo σ₁ σ₂ ρ w ≠ 0)
    (hE : expectedReturnTwo w r₁ r₂ ≠ 0) :
    HasDerivAt (fun w' ↦ sharpeSqTwo w' r₁ r₂ σ₁ σ₂ ρ) 0 w ↔
      r₂ * marginalVariance Finset.univ (covTwo σ₁ σ₂ ρ) ![w, 1 - w] 0 =
        r₁ * marginalVariance Finset.univ (covTwo σ₁ σ₂ ρ) ![w, 1 - w] 1 := by
  -- the derivative, with its numerator factored (`sharpeSqTwo_deriv_numerator_factored`)
  have h := (hasDerivAt_sharpeSqTwo w r₁ r₂ σ₁ σ₂ ρ hV).congr_deriv
    (g' := 2 * expectedReturnTwo w r₁ r₂ *
      (r₁ * marginalVariance Finset.univ (covTwo σ₁ σ₂ ρ) ![w, 1 - w] 1 -
        r₂ * marginalVariance Finset.univ (covTwo σ₁ σ₂ ρ) ![w, 1 - w] 0) /
      (portfolioVarTwo σ₁ σ₂ ρ w) ^ 2)
    (by rw [sharpeSqTwo_deriv_numerator_factored])
  refine ⟨fun h0 ↦ ?_, fun h0 ↦ ?_⟩
  · have h2 := (div_eq_zero_iff.1 (h.unique h0)).resolve_right (pow_ne_zero _ hV)
    have h3 := (mul_eq_zero.1 h2).resolve_left (mul_ne_zero two_ne_zero hE)
    linarith
  · have h2 : r₁ * marginalVariance Finset.univ (covTwo σ₁ σ₂ ρ) ![w, 1 - w] 1 -
        r₂ * marginalVariance Finset.univ (covTwo σ₁ σ₂ ρ) ![w, 1 - w] 0 = 0 := by linarith
    rwa [h2, mul_zero, zero_div] at h

end MathFin
