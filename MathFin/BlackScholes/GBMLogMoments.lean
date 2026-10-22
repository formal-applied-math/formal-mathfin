/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.BlackScholes.Call
public import MathFin.Foundations.ItoLemma

/-!
# The law of the Black–Scholes log-return

Under the Black–Scholes lognormal hypothesis `BSCallHyp` (`S_T = S₀·e^{(r − σ²/2)T + σ√T·Z}`
with `Z ~ N(0, 1)`), the log-return `log(S_T/S₀)` is the affine function
`(r − σ²/2)T + σ√T·Z` of the standard normal (`bsLogReturn_eq`), so it is Gaussian:

  `log(S_T/S₀) ~ N((r − σ²/2)T, σ²T)`,

by Mathlib's affine maps of `gaussianReal` (`gaussianReal_const_mul`,
`gaussianReal_const_add`). Its mean `(r − σ²/2)T` and variance `σ²T` are read off the law.

The mean is the drift that Itô's formula gives `log S` for GBM with drift `r`: the
`dt`-coefficient `itoDrift_log_gbm`, `r − σ²/2` (`Foundations/ItoLemma.lean`), times `T`
(`bsLogReturn_mean_eq_itoDrift`). That identity compares two computations of the same
number: the Itô drift is computed algebraically from `f = log`, and the mean from the Gaussian
law. This file does not prove Itô's formula for `log S`.

## Main results

* `bsLogReturn`: definition `(r − σ²/2)·T + σ·√T·Z`.
* `bsLogReturn_eq`: `log(bsTerminal S₀ r σ T Z / S₀) = bsLogReturn r σ T Z`.
* `bsLogReturn_hasLaw`: `bsLogReturn r σ T Z ~ N((r − σ²/2)T, σ²T)` under `BSCallHyp`.
* `bsLogReturn_mean`: `E_Q[bsLogReturn] = (r − σ²/2)·T`.
* `bsLogReturn_variance`: `Var_Q[bsLogReturn] = σ²T`.
* `bsLogReturn_mean_eq_itoDrift`: the mean is `T` times the Itô drift of `log S`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-- **BS log-return** as a function of the standard-normal sample: by
the lognormal hypothesis `S_T = bsTerminal S_0 r σ T Z = S_0 ·
exp((r − σ²/2)·T + σ·√T·Z)`, so

  `log(S_T / S_0) = (r − σ²/2)·T + σ·√T·Z`. -/
noncomputable def bsLogReturn (r σ T Z : ℝ) : ℝ :=
  (r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z

/-- **Algebraic identity**: `log(bsTerminal S_0 r σ T Z / S_0) =
bsLogReturn r σ T Z`. The lognormal hypothesis collapses to a linear
function of `Z` under `log`. -/
theorem bsLogReturn_eq (S_0 r σ T Z : ℝ) (hS_0 : 0 < S_0) :
    Real.log (bsTerminal S_0 r σ T Z / S_0) = bsLogReturn r σ T Z := by
  unfold bsTerminal bsLogReturn
  rw [mul_div_cancel_left₀ _ hS_0.ne', Real.log_exp]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q]
  {S_0 K r σ T : ℝ} {Z : Ω → ℝ}

/-- **The Black–Scholes log-return is Gaussian**: under `BSCallHyp`,
`bsLogReturn r σ T Z ~ N((r − σ²/2)T, σ²T)` — the affine image `(r − σ²/2)T + σ√T·Z` of the
standard normal `Z`. -/
theorem bsLogReturn_hasLaw (h : BSCallHyp Q S_0 K r σ T Z) :
    HasLaw (fun ω ↦ bsLogReturn r σ T (Z ω))
      (gaussianReal ((r - σ ^ 2 / 2) * T) (σ ^ 2 * T).toNNReal) Q := by
  have hL := gaussianReal_const_add (gaussianReal_const_mul h.Z_law (σ * Real.sqrt T))
    ((r - σ ^ 2 / 2) * T)
  have hv : (.mk ((σ * Real.sqrt T) ^ 2) (sq_nonneg _) : ℝ≥0) * 1 = (σ ^ 2 * T).toNNReal := by
    refine NNReal.coe_injective ?_
    rw [NNReal.coe_mul, NNReal.coe_one, mul_one, NNReal.coe_mk,
      Real.coe_toNNReal _ (mul_nonneg (sq_nonneg σ) h.T_pos.le), mul_pow,
      Real.sq_sqrt h.T_pos.le]
  rw [mul_zero, zero_add, hv] at hL
  exact hL

/-- **Mean of the BS log-return under `Q`**: `E_Q[bsLogReturn r σ T Z] = (r − σ²/2)·T`, the
mean of the law `bsLogReturn_hasLaw`. -/
theorem bsLogReturn_mean (h : BSCallHyp Q S_0 K r σ T Z) :
    ∫ ω, bsLogReturn r σ T (Z ω) ∂Q = (r - σ ^ 2 / 2) * T := by
  rw [(bsLogReturn_hasLaw h).integral_eq, integral_id_gaussianReal]

/-- **Variance of the BS log-return under `Q`**: `Var_Q[bsLogReturn r σ T Z] = σ²T`, the
variance of the law `bsLogReturn_hasLaw`. -/
theorem bsLogReturn_variance (h : BSCallHyp Q S_0 K r σ T Z) :
    Var[fun ω ↦ bsLogReturn r σ T (Z ω); Q] = σ ^ 2 * T := by
  rw [(bsLogReturn_hasLaw h).variance_eq, variance_id_gaussianReal,
    Real.coe_toNNReal _ (mul_nonneg (sq_nonneg σ) h.T_pos.le)]

/-- **The mean log-return is `T` times the Itô drift of `log S`**: for any `S ≠ 0`,
`E_Q[log(S_T/S₀)] = itoDrift (1/S) (−1/S²) (rS) (σS) · T`, where the right side is the
`dt`-coefficient of `log` along GBM with drift `r` and volatility `σ` (`itoDrift_log_gbm`,
`r − σ²/2`), integrated over `[0, T]`. -/
theorem bsLogReturn_mean_eq_itoDrift (h : BSCallHyp Q S_0 K r σ T Z) {S : ℝ} (hS : S ≠ 0) :
    ∫ ω, bsLogReturn r σ T (Z ω) ∂Q = itoDrift (1 / S) (-1 / S ^ 2) (r * S) (σ * S) * T := by
  rw [bsLogReturn_mean h, itoDrift_log_gbm r σ S hS]

end MathFin
