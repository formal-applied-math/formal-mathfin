/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.StrictBoundarySpeed

/-!
# Strict stock-boundary curvature, with no extra speed assumption

The classical pricing contract now implies both weak log curvature and
strictly negative speed. These give strictly positive stock curvature in
calendar time and in time remaining. Actual stopping-value identification is
still a separate obligation; strict logarithmic curvature is not asserted.

## Result

Public entry points include `dividend_stock_curvature`, `zeroDividend_stock_curvature`,
`remainingTimeBoundary`, `deriv2_comp_neg`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

theorem dividend_stock_curvature {k h : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution k h p b)
    {E σ expiry T : ℝ} (hE : 0 < E) (hσ : 0 < σ) (hT : T < expiry) :
    0 < deriv (deriv (stockBoundary E σ expiry b)) T :=
  Comparison.stock_curvature_of_strict_speed hp (fun _ ht => hp.boundary_deriv_neg ht) hE hσ hT

theorem zeroDividend_stock_curvature {k : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : NormalizedPutSolution k p b)
    {E σ expiry T : ℝ} (hE : 0 < E) (hσ : 0 < σ) (hT : T < expiry) :
    0 < deriv (deriv (stockBoundary E σ expiry b)) T :=
  dividend_stock_curvature (dividendPutSolution_zero_iff.mpr hp) hE hσ hT

/-- Stock-price boundary in time remaining: `E*Real.exp (b (σ^2/2*τ))`. -/
noncomputable def remainingTimeBoundary (E σ : ℝ) (b : ℝ → ℝ) (τ : ℝ) : ℝ :=
  E*Real.exp (b (σ^2/2*τ))

theorem deriv2_comp_neg (f : ℝ → ℝ) (x : ℝ) :
    deriv (deriv (fun y => f (-y))) x = deriv (deriv f) (-x) := by
  rw [show deriv (fun y => f (-y)) = fun y => -deriv f (-y) from
    funext (fun y => deriv_comp_neg f y)]
  simp only [deriv.fun_neg,deriv_comp_neg,neg_neg]

theorem dividend_remainingTime_curvature {k h : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution k h p b) {E σ τ : ℝ}
    (hE : 0 < E) (hσ : 0 < σ) (hτ : 0 < τ) :
    0 < deriv (deriv (remainingTimeBoundary E σ b)) τ := by
  have hfun : remainingTimeBoundary E σ b = fun s => stockBoundary E σ 0 b (-s) := by
    funext s
    simp [remainingTimeBoundary,stockBoundary,normalizedTime]
  rw [hfun,deriv2_comp_neg]
  exact dividend_stock_curvature hp hE hσ (neg_neg_of_pos hτ)

theorem zeroDividend_remainingTime_curvature {k : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : NormalizedPutSolution k p b) {E σ τ : ℝ}
    (hE : 0 < E) (hσ : 0 < σ) (hτ : 0 < τ) :
    0 < deriv (deriv (remainingTimeBoundary E σ b)) τ :=
  dividend_remainingTime_curvature (dividendPutSolution_zero_iff.mpr hp) hE hσ hτ

/-- The strict stock-curvature milestone on Liu's restricted parameter range.
This specializes the new proof, not Liu's published argument. -/
theorem liuRange_remainingTime_curvature {k h : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution k h p b) (_hLiu : h + 1 ≤ k) {E σ τ : ℝ}
    (hE : 0 < E) (hσ : 0 < σ) (hτ : 0 < τ) :
    0 < deriv (deriv (remainingTimeBoundary E σ b)) τ :=
  dividend_remainingTime_curvature hp hE hσ hτ

/-- The proposed derivative conclusions together, for the classical pricing
contract. No additional monotonicity, curvature, or strictness input occurs. -/
theorem dividend_boundary_conclusions {k h : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution k h p b) {E σ : ℝ} (hE : 0 < E) (hσ : 0 < σ) :
    (∀ t, 0 < t → deriv b t < 0) ∧
    (∀ t, 0 < t → 0 ≤ deriv (deriv b) t) ∧
    (∀ τ, 0 < τ → 0 < deriv (deriv (remainingTimeBoundary E σ b)) τ) :=
  ⟨fun _ ht => hp.boundary_deriv_neg ht, Comparison.dividend_log_curvature hp,
    fun _ hτ => dividend_remainingTime_curvature hp hE hσ hτ⟩

end MathFin.BlackScholes.AmericanPut.Boundary
