/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.Portfolio.MarkowitzNAsset

/-!
# Component, marginal, and incremental Value-at-Risk (Euler decomposition)

For a Gaussian portfolio loss with positions `x : ι → ℝ` and covariance kernel `σ`, the parametric
VaR is `VaR = α · √(x'Σx)` for a quantile multiplier `α` (e.g. `α = Φ⁻¹(level)`, as in
`RiskMeasures/Gaussian.lean`). Since `x ↦ √(x'Σx)` is positively homogeneous of degree 1, Euler's
theorem gives `∑ᵢ xᵢ · ∂VaR/∂xᵢ = VaR`. We do not need the general calculus machinery for this: the
portfolio variance `x'Σx = ∑ᵢ xᵢ (Σx)ᵢ` already splits termwise, so the sum identity is pure
algebra once the marginal/component VaR are *defined* via the textbook closed form
`∂VaR/∂xᵢ = α(Σx)ᵢ/√(x'Σx)`.

## Main definitions and results

* `weightedSigmaX`: the matrix-vector product `(Σx)ᵢ = ∑ⱼ σᵢⱼ xⱼ`.
* `portfolioVaRN`: the parametric VaR `α · √(x'Σx)`.
* `marginalVaR`: defined as `α(Σx)ᵢ/√(x'Σx)` (`= ∂VaR/∂xᵢ` for symmetric `σ`).
* `componentVaR`: `CVaRᵢ = xᵢ · marginalVaRᵢ`.
* `sum_componentVaR_eq_portfolioVaRN`: **Euler decomposition** `∑ᵢ CVaRᵢ = VaR` (needs
  `0 < x'Σx`, i.e. the portfolio variance is strictly positive).
* `minVarianceHedgeRatio`: the **min-variance hedge ratio** `a* = -W·Cov(Rp,Ri)/σᵢ²` for hedging a
  position against a single asset — a companion risk-reduction formula from the same source
  material, included here alongside the Euler decomposition rather than in its own file.
-/

@[expose] public section

namespace MathFin

variable {ι : Type*} (s : Finset ι) (x : ι → ℝ) (σ : ι → ι → ℝ) (α : ℝ)

/-- The matrix-vector product `(Σx)ᵢ = ∑ⱼ σᵢⱼ xⱼ`. -/
def weightedSigmaX (i : ι) : ℝ := ∑ j ∈ s, σ i j * x j

/-- Parametric portfolio VaR `α · √(x'Σx)`, with `x'Σx` the N-asset portfolio variance of
`Portfolio/MarkowitzNAsset.lean`. -/
noncomputable def portfolioVaRN : ℝ := α * Real.sqrt (portfolioVarN s x σ)

/-- **Marginal VaR**: *defined* as the textbook closed form `α·(Σx)ᵢ/√(x'Σx)`; this equals
`∂VaR/∂xᵢ` when `σ` is symmetric (the general derivative is `α·((Σx)ᵢ + (Σᵀx)ᵢ)/(2√(x'Σx))`). -/
noncomputable def marginalVaR (i : ι) : ℝ :=
  α * weightedSigmaX s x σ i / Real.sqrt (portfolioVarN s x σ)

/-- **Component VaR**: `CVaRᵢ = xᵢ · marginalVaRᵢ` (`= xᵢ · ∂VaR/∂xᵢ` for symmetric `σ`). -/
noncomputable def componentVaR (i : ι) : ℝ := x i * marginalVaR s x σ α i

/-- The portfolio variance is the quadratic form `x'Σx = ∑ᵢ xᵢ(Σx)ᵢ`. -/
lemma portfolioVarN_eq_sum_mul_weightedSigmaX :
    portfolioVarN s x σ = ∑ i ∈ s, x i * weightedSigmaX s x σ i := by
  unfold portfolioVarN weightedSigmaX
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- **Euler decomposition for VaR**: the component VaRs sum to the portfolio VaR,
`∑ᵢ CVaRᵢ = VaR`, whenever the portfolio variance is (strictly) positive. This is Euler's
homogeneous-function theorem for the degree-1-homogeneous map `x ↦ α√(x'Σx)`, made concrete:
`x'Σx` splits termwise as `∑ xᵢ(Σx)ᵢ`, so dividing each term by the common factor `√(x'Σx)` and
multiplying back by it recovers exactly `x'Σx = √(x'Σx) · √(x'Σx)`. -/
theorem sum_componentVaR_eq_portfolioVaRN (hvar : 0 < portfolioVarN s x σ) :
    ∑ i ∈ s, componentVaR s x σ α i = portfolioVaRN s x σ α := by
  have hsqrt : Real.sqrt (portfolioVarN s x σ) ≠ 0 := (Real.sqrt_pos.mpr hvar).ne'
  unfold componentVaR marginalVaR portfolioVaRN
  have hsum : ∑ i ∈ s, x i * (α * weightedSigmaX s x σ i / Real.sqrt (portfolioVarN s x σ)) =
      α * (∑ i ∈ s, x i * weightedSigmaX s x σ i) / Real.sqrt (portfolioVarN s x σ) := by
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  have hsq : Real.sqrt (portfolioVarN s x σ) * Real.sqrt (portfolioVarN s x σ) =
      portfolioVarN s x σ := Real.mul_self_sqrt hvar.le
  rw [hsum, ← portfolioVarN_eq_sum_mul_weightedSigmaX, div_eq_iff hsqrt, mul_assoc, hsq]

/-- The textbook min-variance hedge ratio for hedging a position of size `W` in portfolio `p` with
asset `i`: `a* = -W·Cov(Rp,Rᵢ)/σᵢ²` units of `i` minimise `Var(W·Rp + a·Rᵢ)` (minimality itself is
not proven here). -/
noncomputable def minVarianceHedgeRatio (W covRpRi varRi : ℝ) : ℝ :=
  -W * covRpRi / varRi

end MathFin
