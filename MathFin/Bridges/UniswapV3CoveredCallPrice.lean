/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.DeFi.UniswapMechanics
public import MathFin.BlackScholes.Forward

/-!
# A Black–Scholes price bound for a Uniswap v3 position

`DeFi/UniswapMechanics.lean` shows that a Uniswap v3 position with liquidity `L` on the
square-root price range `[a, b]` is worth at most the covered call
`x_max · (P − max (P − ab) 0)` at every price `P = s²` (`v3PositionValue_le_coveredCall`): long
its full X holding `x_max = realReserveX L a b`, short a call struck at the geometric-mean price
`ab = √(p_a p_b)`. Taking discounted expectations under the Black–Scholes law of the price turns
this pointwise bound into a price bound: by `discounted_terminal_eq_S0` and `bs_call_formula`,
the discounted expected value of the position at `T` is at most `x_max · (S₀ − C)`, with `C` the
Black–Scholes call price struck at `ab`.

## Results

* `measurable_v3PositionValue`: the position value is a measurable function of `s`.
* `integral_discounted_v3PositionValue_le`: under `BSCallHyp Q S₀ (ab) r σ T Z`,
  `E_Q[e^{−rT} V(√S_T)] ≤ x_max · (S₀ − (S₀ Φ(d₁) − ab · e^{−rT} Φ(d₂)))`.

## Scope

An upper bound only; the gap is the expectation of the in-range smoothing term
(`coveredCall_sub_v3PositionValue`), which is not computed. The position is held to `T` with no
fees and no rebalancing; token Y is the numéraire, growing at the rate `r`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory DeFi

/-- The value of a v3 position is a measurable function of the square-root price. -/
theorem measurable_v3PositionValue (L a b : ℝ) : Measurable (v3PositionValue L a b) := by
  unfold v3PositionValue realReserveX realReserveY
  exact Measurable.ite measurableSet_Iic (by fun_prop)
    (Measurable.ite measurableSet_Iic (by fun_prop) (by fun_prop))

/-- **The Black–Scholes value of a v3 position is at most that of the covered call.** If the price
of X in Y is `S_T = bsTerminal S₀ r σ T Z` under `Q` (`BSCallHyp`, strike slot `ab`), the
discounted expected value at `T` of a position with liquidity `L ≥ 0` on the square-root range
`[a, b]` is at most `x_max · (S₀ − C)`, where `x_max = realReserveX L a b` is the position's full X
holding and `C = S₀ Φ(d₁) − ab · e^{−rT} Φ(d₂)` is the Black–Scholes call struck at the
geometric-mean price `ab = √(p_a p_b)`. -/
theorem integral_discounted_v3PositionValue_le {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q] {S_0 r σ T L a b : ℝ} {Z : Ω → ℝ} (hL : 0 ≤ L)
    (ha : 0 < a) (hab : a ≤ b) (h : BSCallHyp Q S_0 (a * b) r σ T Z) :
    ∫ ω, Real.exp (-r * T) * v3PositionValue L a b (Real.sqrt (bsTerminal S_0 r σ T (Z ω))) ∂Q
      ≤ realReserveX L a b * (S_0 - (S_0 * Phi (bsd1 S_0 (a * b) r σ T)
          - a * b * Real.exp (-r * T) * Phi (bsd2 S_0 (a * b) r σ T))) := by
  have hX : 0 ≤ realReserveX L a b :=
    mul_nonneg hL (sub_nonneg.mpr (one_div_le_one_div_of_le ha hab))
  have hP0 (ω : Ω) : 0 ≤ bsTerminal S_0 r σ T (Z ω) :=
    (mul_pos h.S_0_pos (Real.exp_pos _)).le
  have hcov (ω : Ω) : v3PositionValue L a b (Real.sqrt (bsTerminal S_0 r σ T (Z ω)))
      ≤ realReserveX L a b * (bsTerminal S_0 r σ T (Z ω)
        - max (bsTerminal S_0 r σ T (Z ω) - a * b) 0) := by
    simpa only [Real.sq_sqrt (hP0 ω)] using
      v3PositionValue_le_coveredCall hL ha hab (Real.sqrt_nonneg (bsTerminal S_0 r σ T (Z ω)))
  have hPint := integrable_bsTerminal h.Z_law S_0 r σ T
  have h1 : Integrable (fun ω ↦ Real.exp (-(r * T)) * bsTerminal S_0 r σ T (Z ω)) Q :=
    hPint.const_mul _
  have h2 : Integrable
      (fun ω ↦ Real.exp (-r * T) * max (bsTerminal S_0 r σ T (Z ω) - a * b) 0) Q :=
    (hPint.sub (integrable_const _)).pos_part.const_mul _
  have hVm : AEStronglyMeasurable
      (fun ω ↦ v3PositionValue L a b (Real.sqrt (bsTerminal S_0 r σ T (Z ω)))) Q :=
    ((measurable_v3PositionValue L a b).comp_aemeasurable
      (Real.continuous_sqrt.measurable.comp_aemeasurable
        ((by unfold bsTerminal; fun_prop : Measurable (bsTerminal S_0 r σ T)).comp_aemeasurable
          h.Z_law.aemeasurable))).aestronglyMeasurable
  have hV : Integrable
      (fun ω ↦ v3PositionValue L a b (Real.sqrt (bsTerminal S_0 r σ T (Z ω)))) Q := by
    refine Integrable.mono' (integrable_const (realReserveX L a b * (a * b))) hVm
      (Filter.Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (v3PositionValue_nonneg hL ha hab)]
    refine (hcov ω).trans (mul_le_mul_of_nonneg_left ?_ hX)
    linarith [le_max_left (bsTerminal S_0 r σ T (Z ω) - a * b) 0]
  have hpt (ω : Ω) :
      Real.exp (-r * T) * v3PositionValue L a b (Real.sqrt (bsTerminal S_0 r σ T (Z ω)))
        ≤ realReserveX L a b * (Real.exp (-(r * T)) * bsTerminal S_0 r σ T (Z ω)
          - Real.exp (-r * T) * max (bsTerminal S_0 r σ T (Z ω) - a * b) 0) := by
    refine (mul_le_mul_of_nonneg_left (hcov ω) (Real.exp_pos _).le).trans_eq ?_
    rw [neg_mul]
    ring
  calc ∫ ω, Real.exp (-r * T) * v3PositionValue L a b (Real.sqrt (bsTerminal S_0 r σ T (Z ω))) ∂Q
      ≤ ∫ ω, realReserveX L a b * (Real.exp (-(r * T)) * bsTerminal S_0 r σ T (Z ω)
          - Real.exp (-r * T) * max (bsTerminal S_0 r σ T (Z ω) - a * b) 0) ∂Q :=
        integral_mono (hV.const_mul _) ((h1.sub h2).const_mul _) hpt
    _ = realReserveX L a b * (S_0 - (S_0 * Phi (bsd1 S_0 (a * b) r σ T)
          - a * b * Real.exp (-r * T) * Phi (bsd2 S_0 (a * b) r σ T))) := by
        rw [integral_const_mul, integral_sub h1 h2, discounted_terminal_eq_S0 h, bs_call_formula h]

end MathFin
