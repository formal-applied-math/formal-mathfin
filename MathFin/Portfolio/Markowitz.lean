/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# Markowitz two-asset portfolio theory

Closed-form results for the two-asset minimum-variance problem. Returns are
modelled by their first two moments only (`σ_1`, `σ_2`, `ρ`) — the classical
mean-variance setting where the covariance matrix is the primitive. That the formula
below is the variance of the random portfolio return `w R₁ + (1 − w) R₂` is proved in
`Portfolio/MarkowitzLagrangian.lean` (`portfolioVarTwo_eq_variance`), together with the
first-order condition the minimum-variance weight satisfies there
(`marginalVariance_minVarWeightTwo`).

For a two-asset portfolio with weight `w` on asset 1 and `1 - w` on asset 2:

  `Var(w) = w² σ_1² + (1 - w)² σ_2² + 2 w (1 - w) ρ σ_1 σ_2`.

The "completing-the-square" identity

  `Var(w) = D · (w − w*)² + V_min`

with `D = σ_1² − 2 ρ σ_1 σ_2 + σ_2²`,
`w* = (σ_2² − ρ σ_1 σ_2) / D`,
`V_min = σ_1² σ_2² (1 − ρ²) / D`,

makes both the location of the minimum (at `w*`) and its value (`V_min`)
immediate, and avoids any explicit calculus.

Results:

* `covTwo`, `portfolioVarTwo_eq_dotProduct`: the two-asset covariance matrix, and
  `Var(w)` as its quadratic form at the weights `(w, 1 − w)`.
* `portfolioVarTwo_eq_quad`: the factorization above.
* `portfolioVarTwo_at_minVarWeight`: `Var(w*) = V_min`.
* `portfolioVarTwo_ge_min`: `Var(w) ≥ V_min` for every `w`, given `D > 0`.
* `minPortfolioVarTwo_perfect_anticorr`: at `ρ = -1` the closed form `V_min`
  is zero; it is the minimum variance when `D > 0` (perfect hedge).
-/

@[expose] public section

namespace MathFin

open Matrix

/-- Portfolio variance for a two-asset mix with weight `w` on asset 1 and
`1 - w` on asset 2. -/
noncomputable def portfolioVarTwo (σ₁ σ₂ ρ : ℝ) (w : ℝ) : ℝ :=
  w ^ 2 * σ₁ ^ 2 + (1 - w) ^ 2 * σ₂ ^ 2 + 2 * w * (1 - w) * ρ * σ₁ * σ₂

/-- The two-asset covariance matrix `!![σ₁², ρσ₁σ₂; ρσ₁σ₂, σ₂²]` for volatilities
`σ₁, σ₂` and correlation `ρ`. -/
noncomputable def covTwo (σ₁ σ₂ ρ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![σ₁ ^ 2, ρ * σ₁ * σ₂; ρ * σ₁ * σ₂, σ₂ ^ 2]

/-- `portfolioVarTwo` is the quadratic form of `covTwo` at the weights `(w, 1 − w)`. -/
lemma portfolioVarTwo_eq_dotProduct (σ₁ σ₂ ρ w : ℝ) :
    portfolioVarTwo σ₁ σ₂ ρ w = ![w, 1 - w] ⬝ᵥ (covTwo σ₁ σ₂ ρ *ᵥ ![w, 1 - w]) := by
  simp [portfolioVarTwo, covTwo, mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- Denominator of the min-variance weight: `D = σ_1² − 2 ρ σ_1 σ_2 + σ_2²`. -/
noncomputable def minVarDenom (σ₁ σ₂ ρ : ℝ) : ℝ :=
  σ₁ ^ 2 - 2 * ρ * σ₁ * σ₂ + σ₂ ^ 2

/-- Closed-form minimum-variance weight:
`w* = (σ_2² − ρ σ_1 σ_2) / D`. -/
noncomputable def minVarWeightTwo (σ₁ σ₂ ρ : ℝ) : ℝ :=
  (σ₂ ^ 2 - ρ * σ₁ * σ₂) / minVarDenom σ₁ σ₂ ρ

/-- Minimum portfolio variance: `V_min = σ_1² σ_2² (1 − ρ²) / D`. -/
noncomputable def minPortfolioVarTwo (σ₁ σ₂ ρ : ℝ) : ℝ :=
  σ₁ ^ 2 * σ₂ ^ 2 * (1 - ρ ^ 2) / minVarDenom σ₁ σ₂ ρ

/-- Two-asset portfolio variance has the closed-form factorization
`Var(w) = D · (w − w*)² + V_min`. -/
lemma portfolioVarTwo_eq_quad {σ₁ σ₂ ρ : ℝ}
    (hD : minVarDenom σ₁ σ₂ ρ ≠ 0) (w : ℝ) :
    portfolioVarTwo σ₁ σ₂ ρ w =
      minVarDenom σ₁ σ₂ ρ * (w - minVarWeightTwo σ₁ σ₂ ρ) ^ 2
      + minPortfolioVarTwo σ₁ σ₂ ρ := by
  unfold portfolioVarTwo minVarWeightTwo minPortfolioVarTwo
  field_simp
  unfold minVarDenom
  ring

/-- Two-asset portfolio variance attains the explicit minimum `V_min` at `w = w*`. -/
lemma portfolioVarTwo_at_minVarWeight {σ₁ σ₂ ρ : ℝ}
    (hD : minVarDenom σ₁ σ₂ ρ ≠ 0) :
    portfolioVarTwo σ₁ σ₂ ρ (minVarWeightTwo σ₁ σ₂ ρ) =
      minPortfolioVarTwo σ₁ σ₂ ρ := by
  rw [portfolioVarTwo_eq_quad hD]
  simp [sub_self]

/-- For any weight, the portfolio variance is at least `V_min`, provided the
denominator `D` is positive (the standard non-degeneracy condition). -/
lemma portfolioVarTwo_ge_min {σ₁ σ₂ ρ : ℝ}
    (hD : 0 < minVarDenom σ₁ σ₂ ρ) (w : ℝ) :
    minPortfolioVarTwo σ₁ σ₂ ρ ≤ portfolioVarTwo σ₁ σ₂ ρ w := by
  rw [portfolioVarTwo_eq_quad hD.ne' w]
  have h_sq : 0 ≤ (w - minVarWeightTwo σ₁ σ₂ ρ) ^ 2 := sq_nonneg _
  have h_term : 0 ≤ minVarDenom σ₁ σ₂ ρ * (w - minVarWeightTwo σ₁ σ₂ ρ) ^ 2 :=
    mul_nonneg hD.le h_sq
  linarith

/-- **Perfect-hedge corollary**: at `ρ = -1` the closed form `V_min` is zero, for any
`σ₁, σ₂`. It is the minimum portfolio variance when `D = (σ₁ + σ₂)² > 0`
(`portfolioVarTwo_ge_min`, `portfolioVarTwo_at_minVarWeight`). -/
lemma minPortfolioVarTwo_perfect_anticorr (σ₁ σ₂ : ℝ) :
    minPortfolioVarTwo σ₁ σ₂ (-1) = 0 := by
  unfold minPortfolioVarTwo
  have h : (1 : ℝ) - (-1) ^ 2 = 0 := by ring
  rw [h]
  ring

end MathFin
