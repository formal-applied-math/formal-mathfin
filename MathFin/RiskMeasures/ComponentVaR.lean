/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.Portfolio.MarkowitzNAsset
public import MathFin.Portfolio.CovariancePSD
public import MathFin.Portfolio.RiskParityFOC

/-!
# Component and marginal Value-at-Risk (the Euler allocation)

For a Gaussian portfolio loss with positions `x : ι → ℝ` and covariance kernel `σ`, the parametric
VaR is `VaR = α · √(x'Σx)` for a quantile multiplier `α` (e.g. `α = Φ⁻¹(level)`, as in
`RiskMeasures/Gaussian.lean`). Since `x ↦ √(x'Σx)` is positively homogeneous of degree 1, Euler's
theorem predicts `∑ᵢ xᵢ · ∂VaR/∂xᵢ = VaR`. Here the marginal VaR is *defined* by the textbook
closed form `α(Σx)ᵢ/√(x'Σx)`, which is `∂VaR/∂xᵢ` for symmetric `σ`; that derivative identity is
not proved in this file. With this definition the component VaR `xᵢ · marginalVaRᵢ` is
`α/√(x'Σx)` times the risk contribution `xᵢ(Σx)ᵢ` of `Portfolio/RiskParityFOC.lean`, and the
Euler identity reduces to `sum_riskContribution_eq_variance`.

## Main definitions and results

* `portfolioVaRN`: the parametric VaR `α · √(x'Σx)`.
* `marginalVaR`: defined as `α(Σx)ᵢ/√(x'Σx)`, with `(Σx)ᵢ = marginalVariance s σ x i`.
* `componentVaR`: `CVaRᵢ = xᵢ · marginalVaRᵢ`.
* `sum_componentVaR_eq_portfolioVaRN`: the Euler allocation `∑ᵢ CVaRᵢ = VaR` (needs `0 < x'Σx`,
  i.e. the portfolio variance is strictly positive).
-/

@[expose] public section

namespace MathFin

variable {ι : Type*} (s : Finset ι) (x : ι → ℝ) (σ : ι → ι → ℝ) (α : ℝ)

/-- Parametric portfolio VaR `α · √(x'Σx)`, with `x'Σx` the N-asset portfolio variance of
`Portfolio/MarkowitzNAsset.lean`. -/
noncomputable def portfolioVaRN : ℝ := α * Real.sqrt (portfolioVarN s x σ)

/-- **Marginal VaR**: *defined* as the textbook closed form `α·(Σx)ᵢ/√(x'Σx)`, with
`(Σx)ᵢ = marginalVariance s σ x i`. For symmetric `σ` this is `∂VaR/∂xᵢ`; that identity is not
proved here. -/
noncomputable def marginalVaR (i : ι) : ℝ :=
  α * marginalVariance s σ x i / Real.sqrt (portfolioVarN s x σ)

/-- **Component VaR**: `CVaRᵢ = xᵢ · marginalVaRᵢ`, i.e. `α/√(x'Σx)` times the risk contribution
`riskContribution s σ x i = xᵢ(Σx)ᵢ`. -/
noncomputable def componentVaR (i : ι) : ℝ := x i * marginalVaR s x σ α i

/-- **Euler allocation of VaR**: the component VaRs sum to the portfolio VaR, `∑ᵢ CVaRᵢ = VaR`,
whenever the portfolio variance is (strictly) positive. This is the identity Euler's theorem
predicts for the degree-1-homogeneous map `x ↦ α√(x'Σx)`; since `marginalVaR` is defined by its
closed form, the proof is the algebra `∑ᵢ xᵢ(Σx)ᵢ = x'Σx` (`sum_riskContribution_eq_variance`,
`portfolioVariance_eq_portfolioVarN`). -/
theorem sum_componentVaR_eq_portfolioVaRN (hvar : 0 < portfolioVarN s x σ) :
    ∑ i ∈ s, componentVaR s x σ α i = portfolioVaRN s x σ α := by
  have hsqrt : Real.sqrt (portfolioVarN s x σ) ≠ 0 := (Real.sqrt_pos.mpr hvar).ne'
  unfold componentVaR marginalVaR portfolioVaRN
  have hsum :
      ∑ i ∈ s, x i * (α * marginalVariance s σ x i / Real.sqrt (portfolioVarN s x σ)) =
        α * (∑ i ∈ s, riskContribution s σ x i) / Real.sqrt (portfolioVarN s x σ) := by
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    unfold riskContribution
    ring
  have hsq : Real.sqrt (portfolioVarN s x σ) * Real.sqrt (portfolioVarN s x σ) =
      portfolioVarN s x σ := Real.mul_self_sqrt hvar.le
  rw [hsum, sum_riskContribution_eq_variance, portfolioVariance_eq_portfolioVarN,
    div_eq_iff hsqrt, mul_assoc, hsq]

end MathFin
