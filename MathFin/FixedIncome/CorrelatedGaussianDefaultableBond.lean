/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib

/-!
# Defaultable zero-coupon bond under correlated Gaussian short rate and hazard rate

A reduced-form defaultable zero-coupon bond under a Gaussian short rate `r` and a Gaussian
hazard rate `λ`,

  `dr_t = θ dt + σ_r dW_r`,  `dλ_t = μ dt + σ_λ dW_λ`,  `Corr(dW_r, dW_λ) = ρ`,

prices as `E[exp(-∫₀ᵀ (r_t + λ_t) dt)]`. Writing `y = ∫₀ᵀ (r_t + λ_t) dt`, `y` is Gaussian (an
affine functional of jointly Gaussian processes), so the price is the Gaussian
moment-generating function of `y` at `-1`:

  `E[exp(-y)] = exp(-E[y] + ½ Var[y])`.

**This file does not re-derive that the time integral `∫₀ᵀ r_t dt` is Gaussian** — that is a
stochastic-calculus fact about the SDEs above, outside the scope of the existing
`StandardGaussianMGF`/`GaussianMoments` substrate this file builds on. Instead `y`'s Gaussian
law is the hypothesis (`y ~ gaussianReal m v`), and the mean/variance formulas

  `E[y] = (r₀ + λ₀) T + ∫₀ᵀ (T - t)(θ + μ) dt = (r₀ + λ₀) T + (θ + μ) T² / 2`,
  `Var[y] = (σ_r² + 2ρ σ_r σ_λ + σ_λ²) T³ / 3`

are packaged as the closed forms the model predicts, with the price identity proved for exactly
those values. The underlying MGF step is already in Mathlib
(`ProbabilityTheory.mgf_id_gaussianReal`); the content here is unfolding `mgf` to the economic
expectation and specialising the mean/variance to this correlated two-factor model.

**Known limitation, disclosed, not silently assumed**: because `r` and `λ` are modeled as
(correlated) Gaussian processes, `λ_t` — the instantaneous hazard/default-intensity rate — can
take **negative** values with positive probability. A negative hazard rate has no probabilistic
meaning (intensities must be nonnegative), so this is a known flaw of the simple Gaussian
hazard-rate model, not addressed by the source lecture notes and not fixed here (a
nonnegative-intensity model, e.g. CIR-type, would avoid it at the cost of losing this
closed-form Gaussian MGF route).

## Main results

* `integral_exp_neg_gaussianReal`: `E[exp(-y)] = exp(-m + v/2)` for `y ∼ gaussianReal m v`, via
  `mgf_id_gaussianReal` at `t = -1`.
* `defaultableZeroCouponBond_price`: the bond-price identity instantiated at this model's
  `E[y]`, `Var[y]` formulas.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace CorrelatedGaussianDefaultableBond

/-- **Gaussian "exponential MGF" at `t = -1`.** For `y ∼ gaussianReal m v`,
`E[exp(-y)] = exp(-m + v/2)`. Direct corollary of Mathlib's `mgf_id_gaussianReal`
(`mgf id (gaussianReal m v) = fun t ↦ exp(m*t + v*t²/2)`) unfolded at `t = -1` and read as an
honest expectation (`mgf X μ t := μ[fun ω ↦ exp (t * X ω)]`). -/
theorem integral_exp_neg_gaussianReal (m : ℝ) (v : ℝ≥0) :
    ∫ y, rexp (-y) ∂(gaussianReal m v) = rexp (-m + (v : ℝ) / 2) := by
  have h := congrFun (mgf_id_gaussianReal (μ := m) (v := v)) (-1)
  simp only [mgf, id_eq] at h
  simpa [neg_one_mul, mul_comm, mul_neg_one] using h

/-- **Defaultable zero-coupon bond price under correlated Gaussian `r`, `λ`.** With
`T ≥ 0` and correlation `ρ ∈ [-1, 1]` (so the model's
`Var[y] = (σ_r² + 2ρσ_rσ_λ + σ_λ²)T³/3` is a genuine, nonnegative variance for any real vols
`σ_r, σ_λ`, from `(σ_r ∓ σ_λ)² ≥ 0`), and `y`'s law taken
to be `gaussianReal (E[y]) (Var[y])` with the model's mean/variance formulas — the hypothesis
disclosed in the module docstring, standing in for the un-formalized claim that `∫₀ᵀ(r_t+λ_t)dt`
is Gaussian with this mean and variance —

  `E[exp(-∫₀ᵀ(r_t+λ_t)dt)] = exp(-E[y] + ½Var[y])`,

with `E[y] = (r₀+λ₀)T + (θ+μ)T²/2` and `Var[y] = (σ_r²+2ρσ_rσ_λ+σ_λ²)T³/3`. See the module
docstring for the disclosed limitation that Gaussian `λ` can go negative.

`hT`, `hρ`, `hρ'` are not needed by the MGF step itself (`integral_exp_neg_gaussianReal` holds for
*any* `m : ℝ` and `v : ℝ≥0`); they are exactly what is needed to certify that this model's
`Var[y]` formula is a legitimate nonnegative variance, i.e. a genuine `ℝ≥0`, in the first place. -/
theorem defaultableZeroCouponBond_price (T r0 lam0 θ μ sigr sigl ρ : ℝ)
    (hT : 0 ≤ T) (hρ : -1 ≤ ρ) (hρ' : ρ ≤ 1) :
    ∫ y, rexp (-y) ∂(gaussianReal
        ((r0 + lam0) * T + (θ + μ) * T ^ 2 / 2)
        ⟨(sigr ^ 2 + 2 * ρ * sigr * sigl + sigl ^ 2) * T ^ 3 / 3, by
          have hdisc : 0 ≤ sigr ^ 2 + 2 * ρ * sigr * sigl + sigl ^ 2 := by
            nlinarith [sq_nonneg (sigr - sigl), sq_nonneg (sigr + sigl)]
          positivity⟩)
      = rexp (-((r0 + lam0) * T + (θ + μ) * T ^ 2 / 2)
          + (sigr ^ 2 + 2 * ρ * sigr * sigl + sigl ^ 2) * T ^ 3 / 3 / 2) :=
  integral_exp_neg_gaussianReal _ _

end CorrelatedGaussianDefaultableBond

end MathFin
