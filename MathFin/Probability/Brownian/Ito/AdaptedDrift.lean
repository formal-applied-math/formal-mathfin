/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Brownian.Ito.DriftPath

/-! # The drift of an Itô process with adapted coefficients

The drift part of the adapted-coefficient Itô formula (`ItoFormulaAdapted`). For a bounded adapted
drift rate `b` with continuous paths, the pathwise integral `A_t = ∫₀ᵗ b_s ds` is taken as it
stands, with no modification:

* it is Lipschitz in time with the bound of `b` as constant, on every path
  (`abs_driftPath_sub_le`), which is the hypothesis the quadratic variation
  `AdaptedQuadraticVariation.tendsto_qv_adapted` asks of a drift;
* it is adapted, as a limit of Riemann sums of `𝓕_t`-measurable values, and so predictable, being
  continuous (`driftPath_isStronglyPredictable`);
* for each `ω` and each bounded `g : ℝ≥0 → ℝ` continuous on `[0, T]`, its Riemann–Stieltjes
  sums converge: `∑ₖ g(tₖ)·(A_{tₖ₊₁} − A_{tₖ}) → ∫₀ᵀ g_s b_s ds`
  (`tendsto_sum_mul_driftPath_sub`), the drift half of the formula's first-order term.

## Main definitions

* `driftPath`: the drift path `A_t(ω) = ∫₀ᵗ b_s(ω) ds` (`DriftPath`, the path-level half of this
  development).

The pathwise limit process `driftContinuousMod` of the `L²` drift operator is this path for the
rate `(s, ω) ↦ ⇑g (s, ω)`: `driftContinuousMod_ae_eq_driftPath` gives, for each `t ≤ T`, almost
surely `driftContinuousMod T hBmeas g t ω = driftPath (fun s ω ↦ ⇑g (s, ω)) t ω`.

## Main results

The rate `b` is bounded and continuous in time throughout, and adapted to the Brownian
filtration for the measurability results.

* `driftPath_sub`: the increment of the drift path over `(s, t]` is the integral of the rate
  over `(s, t]`.
* `abs_driftPath_sub_le`: the drift path is Lipschitz in time, with the bound of the rate as
  constant.
* `continuous_driftPath`: the drift path is continuous.
* `stronglyMeasurable_driftPath`, `driftPath_isStronglyPredictable`: `A_t` is measurable for the
  Brownian filtration at time `t`, and the drift path is predictable.
* `tendsto_sum_mul_driftPath_sub`: for each `ω` and each bounded `g` continuous on `[0, T]`, the
  sums `∑ₖ g(tₖ)·(A_{tₖ₊₁} − A_{tₖ})` along the uniform partitions converge (to `∫₀ᵀ g_s b_s ds`).

## Tags

Itô process, drift, Riemann–Stieltjes sum, predictable process, Itô formula, MSC 60H05, MSC 60G07
-/

@[expose] public section

namespace MathFin
namespace AdaptedDrift

open MeasureTheory ProbabilityTheory Filter Topology
open ItoIntegralL2 ItoIntegralBrownian ItoIntegralRiemannBridge QuadraticVariationL2
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ} (hBmeas : ∀ t, Measurable (B t))
  {b : ℝ≥0 → Ω → ℝ}
  (hb_adap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (b t))
  (hb_cont : ∀ ω, Continuous fun s ↦ b s ω) {Cb : ℝ} (hb_bdd : ∀ s ω, |b s ω| ≤ Cb)

include hb_adap hb_cont hb_bdd in
/-- **The drift path is adapted**: `A_t` is the limit of Riemann sums of values `b(tₖ)` with
`tₖ ≤ t`, each `𝓕_t`-measurable. -/
theorem stronglyMeasurable_driftPath (t : ℝ≥0) :
    StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (driftPath b t) := by
  have hmeas (n : ℕ) : StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)]
      fun ω ↦ ∑ k ∈ Finset.range n,
        b (unifPart t n k) ω * ((unifPart t n (k + 1) : ℝ) - unifPart t n k) :=
    Finset.stronglyMeasurable_fun_sum _ fun k hk ↦ ((hb_adap _).mono ((natFiltration hBmeas).mono
      (unifPart_le_T (Finset.mem_range.mp hk).le))).mul_const _
  let : MeasurableSpace Ω := natFiltration hBmeas t
  exact stronglyMeasurable_of_tendsto atTop hmeas (tendsto_pi_nhds.2 fun ω ↦
    tendsto_riemannSum_setIntegral (hb_cont ω) (fun s ↦ hb_bdd s ω) t)

include hb_adap hb_cont hb_bdd in
/-- **The drift path is predictable**: adapted, with continuous paths. -/
theorem driftPath_isStronglyPredictable :
    IsStronglyPredictable (natFiltration hBmeas) (driftPath b) :=
  StronglyAdapted.isStronglyPredictable_of_leftContinuous
    (stronglyMeasurable_driftPath hBmeas hb_adap hb_cont hb_bdd)
    fun ω _ ↦ (continuous_driftPath hb_cont hb_bdd ω).continuousWithinAt

end AdaptedDrift

end MathFin
