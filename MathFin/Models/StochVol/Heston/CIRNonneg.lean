/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.ItoFormulaTime
public import MathFin.Models.StochVol.Heston.CIRNegativePart
public import MathFin.Models.StochVol.Heston.CIRRegularized

/-!
# Nonnegativity of CIR-type solutions

For `dV = κ(θ - V) dt + σ(V) dB` with `κ, θ ≥ 0`, `V₀ ≥ 0` and a diffusion coefficient vanishing on
`(-∞, 0]`, the solution stays nonnegative.  The proof applies Dynkin's formula
(`ito_formula_L2_integral`) to the bounded `C²` test function `h = N / (1 + N)`,
`N(x) = ((-x)⁺)³` (`cirNegativePart`): `h' σ ≡ 0`, `h'' σ² ≡ 0`, `h' · κ(θ - x) ≤ 0`, so
`E h(V_t) ≤ h(V₀) = 0`, whence `h(V_t) = 0` and `V_t ≥ 0` a.s.; continuity of paths upgrades this
to all times simultaneously.  It covers the regularized diffusions `ξ g_ε` and `ξ √(x⁺)`.

## Main definitions

* `negTest'`
* `negTest''`
* `cirSqrtDiffusion`

## Main results

* `l2ItoProcess_nonneg_of_cir_type`
* `cir_regularized_nonneg`
* `cir_sqrt_nonneg`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section
namespace MathFin.Heston
open MathFin.FilteredIto
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open MathFin MathFin.ItoIntegralL2 MathFin.ItoIntegralCLM MathFin.ItoIntegralProcessGeneral
open MathFin.ItoIntegralProcessContinuousModification MathFin.ItoFormulaAdapted
open MathFin.AdaptedDrift MathFin.ItoIntegralAgainstMartingale

/-! ## The bounded test function -/

/-- `h = N / (1 + N)`, `N = cirNegativePart`. -/
def negTest (x : ℝ) : ℝ := cirNegativePart x / (1 + cirNegativePart x)

/-- `h' = N' / (1 + N)²`. -/
def negTest' (x : ℝ) : ℝ := cirNegativePartDeriv x / (1 + cirNegativePart x) ^ 2

/-- `h'' = (N'' (1 + N) - 2 N'²) / (1 + N)³`. -/
def negTest'' (x : ℝ) : ℝ :=
  (cirNegativePartDeriv2 x * (1 + cirNegativePart x) - 2 * cirNegativePartDeriv x ^ 2)
    / (1 + cirNegativePart x) ^ 3

theorem one_add_cirNegativePart_pos (x : ℝ) : 0 < 1 + cirNegativePart x := by
  have := cirNegativePart_nonneg x
  linarith

theorem hasDerivAt_one_add_cirNegativePart (x : ℝ) :
    HasDerivAt (fun y => 1 + cirNegativePart y) (cirNegativePartDeriv x) x := by
  have h := (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_cirNegativePart x)
  rw [zero_add] at h
  exact h

theorem hasDerivAt_negTest (x : ℝ) : HasDerivAt negTest (negTest' x) x := by
  have hpos := one_add_cirNegativePart_pos x
  refine ((hasDerivAt_cirNegativePart x).div (hasDerivAt_one_add_cirNegativePart x)
    hpos.ne').congr_deriv ?_
  unfold negTest'
  rw [div_eq_div_iff (pow_ne_zero 2 hpos.ne') (pow_ne_zero 2 hpos.ne')]
  ring

theorem hasDerivAt_negTest' (x : ℝ) : HasDerivAt negTest' (negTest'' x) x := by
  have hpos := one_add_cirNegativePart_pos x
  have hd : HasDerivAt (fun y => (1 + cirNegativePart y) ^ 2)
      (2 * (1 + cirNegativePart x) * cirNegativePartDeriv x) x := by
    refine ((hasDerivAt_one_add_cirNegativePart x).pow 2).congr_deriv ?_
    norm_num
  refine ((hasDerivAt_cirNegativePartDeriv x).div hd (pow_ne_zero 2 hpos.ne')).congr_deriv ?_
  unfold negTest''
  rw [div_eq_div_iff (pow_ne_zero 2 (pow_ne_zero 2 hpos.ne')) (pow_ne_zero 3 hpos.ne')]
  ring

theorem continuous_negTest'' : Continuous negTest'' := by
  have hNc : Continuous cirNegativePart := contDiff_cirNegativePart.continuous
  have hN'c : Continuous cirNegativePartDeriv :=
    continuous_iff_continuousAt.2 fun x => (hasDerivAt_cirNegativePartDeriv x).continuousAt
  unfold negTest''
  exact ((continuous_cirNegativePartDeriv2.mul (continuous_const.add hNc)).sub
    (continuous_const.mul (hN'c.pow 2))).div ((continuous_const.add hNc).pow 3)
    (fun x => pow_ne_zero 3 (one_add_cirNegativePart_pos x).ne')

/-- `u ≤ 1 + u³` for `u ≥ 0`. -/
theorem le_one_add_cube {u : ℝ} (hu : 0 ≤ u) : u ≤ 1 + u ^ 3 := by
  nlinarith [mul_nonneg hu (sq_nonneg (u - 1)), sq_nonneg (u - 1 / 2)]

theorem abs_negTest'_le (x : ℝ) : |negTest' x| ≤ 3 := by
  have hu : 0 ≤ max (-x) 0 := le_max_right _ _
  set u := max (-x) 0 with hu_def
  have hD : 0 < 1 + u ^ 3 := by positivity
  have h1 : u ≤ 1 + u ^ 3 := le_one_add_cube hu
  have h2 : u ^ 2 ≤ (1 + u ^ 3) ^ 2 := pow_le_pow_left₀ hu h1 2
  unfold negTest' cirNegativePartDeriv cirNegativePart
  rw [← hu_def, abs_div, abs_of_pos (pow_pos hD 2), div_le_iff₀ (pow_pos hD 2), abs_le]
  constructor <;> nlinarith [sq_nonneg u]

theorem abs_negTest''_le (x : ℝ) : |negTest'' x| ≤ 24 := by
  have hu : 0 ≤ max (-x) 0 := le_max_right _ _
  set u := max (-x) 0 with hu_def
  have hD : 0 < 1 + u ^ 3 := by positivity
  have h1 : u ≤ 1 + u ^ 3 := le_one_add_cube hu
  have h3 : u ^ 3 ≤ 1 + u ^ 3 := by linarith
  have hA : u * (1 + u ^ 3) ≤ (1 + u ^ 3) ^ 2 := by
    rw [sq]; exact mul_le_mul_of_nonneg_right h1 hD.le
  have hB : u ^ 4 ≤ (1 + u ^ 3) ^ 2 := by
    rw [show u ^ 4 = u * u ^ 3 by ring, sq]
    exact mul_le_mul h1 h3 (pow_nonneg hu 3) hD.le
  have hC : (1 + u ^ 3) ^ 2 ≤ (1 + u ^ 3) ^ 3 := by
    rw [show (1 + u ^ 3) ^ 3 = (1 + u ^ 3) ^ 2 * (1 + u ^ 3) by ring]
    have : (1 : ℝ) ≤ 1 + u ^ 3 := by have := pow_nonneg hu 3; linarith
    nlinarith [sq_nonneg (1 + u ^ 3)]
  unfold negTest'' cirNegativePartDeriv2 cirNegativePartDeriv cirNegativePart
  rw [← hu_def, abs_div, abs_of_pos (pow_pos hD 3), div_le_iff₀ (pow_pos hD 3), abs_le]
  constructor
  · nlinarith [mul_nonneg hu hD.le, pow_nonneg hu 4]
  · nlinarith [mul_nonneg hu hD.le, pow_nonneg hu 4]

theorem negTest_nonneg (x : ℝ) : 0 ≤ negTest x :=
  div_nonneg (cirNegativePart_nonneg x) (one_add_cirNegativePart_pos x).le

theorem negTest_eq_zero_iff (x : ℝ) : negTest x = 0 ↔ 0 ≤ x := by
  unfold negTest
  rw [div_eq_zero_iff, or_iff_left (one_add_cirNegativePart_pos x).ne', cirNegativePart_zero_iff]

theorem negTest''_eq_zero_of_nonneg {x : ℝ} (hx : 0 ≤ x) : negTest'' x = 0 := by
  unfold negTest'' cirNegativePartDeriv2 cirNegativePartDeriv
  rw [max_eq_right (neg_nonpos.mpr hx)]
  simp

theorem negTest'_mul_drift_nonpos {κ θ : ℝ} (hκ : 0 ≤ κ) (hθ : 0 ≤ θ) (x : ℝ) :
    negTest' x * (κ * (θ - x)) ≤ 0 := by
  unfold negTest'
  rw [div_mul_eq_mul_div]
  exact div_nonpos_of_nonpos_of_nonneg (cirNegativePart_drift_nonpos κ θ x hκ hθ) (sq_nonneg _)

theorem negTest''_mul_sq_eq_zero {σ : ℝ → ℝ} (hσ : ∀ x ≤ 0, σ x = 0) (x : ℝ) :
    negTest'' x * σ x ^ 2 = 0 := by
  rcases le_or_gt x 0 with hx | hx
  · rw [hσ x hx]; ring
  · rw [negTest''_eq_zero_of_nonneg hx.le, zero_mul]

/-! ## Nonnegativity -/

/-- The square-root diffusion coefficient `ξ √(x⁺)`, defined on all of `ℝ`. -/
def cirSqrtDiffusion (p : Parameters) (x : ℝ) : ℝ := p.xi * Real.sqrt (max x 0)

theorem cirSqrtDiffusion_of_nonpos (p : Parameters) {x : ℝ} (hx : x ≤ 0) :
    cirSqrtDiffusion p x = 0 := by
  simp [cirSqrtDiffusion, max_eq_right hx]

theorem cirRegularizedDiffusion_of_nonpos (p : Parameters) (ε : ℝ) {x : ℝ} (hx : x ≤ 0) :
    cirRegularizedDiffusion p ε x = 0 := by
  simp [cirRegularizedDiffusion, cirApproxDiff_of_nonpos hx]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

section Nonneg
variable (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)

include hB hBcont in
/-- **Nonnegativity of CIR-type solutions.** -/
theorem l2ItoProcess_nonneg_of_cir_type {v₀ κ θ : ℝ} (hv₀ : 0 ≤ v₀) (hκ : 0 ≤ κ) (hθ : 0 ≤ θ)
    {σ : ℝ → ℝ} (hσ : ∀ x ≤ 0, σ x = 0) (G H : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hG : ⇑G =ᵐ[trimMeasure (μ := μ) T hBmeas]
      fun z => κ * (θ - l2ItoProcess T hBmeas v₀ G H z.1 z.2))
    (hH : ⇑H =ᵐ[trimMeasure (μ := μ) T hBmeas]
      fun z => σ (l2ItoProcess T hBmeas v₀ G H z.1 z.2)) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, 0 ≤ l2ItoProcess T hBmeas v₀ G H t ω := by
  set X := l2ItoProcess T hBmeas v₀ G H with hXdef
  have hv : negTest v₀ = 0 := (negTest_eq_zero_iff v₀).2 hv₀
  have hfix : ∀ t ≤ T, ∀ᵐ ω ∂μ, 0 ≤ X t ω := by
    intro t htT
    have hI := ito_formula_L2_integral hB T hBmeas hBcont v₀ G H hasDerivAt_negTest
      hasDerivAt_negTest' continuous_negTest'' abs_negTest'_le abs_negTest''_le htT
    rw [← hXdef] at hI
    have hslice : ∀ᵐ ω ∂μ, ∫ s in Set.Ioc 0 t, (negTest' (X s ω) * G (s, ω)
        + 1 / 2 * (negTest'' (X s ω) * H (s, ω) ^ 2)) ∂timeMeasure ≤ 0 := by
      filter_upwards [ae_ae_of_ae_trim T hBmeas hG, ae_ae_of_ae_trim T hBmeas hH]
        with ω hGω hHω
      have hle : ∀ᵐ s ∂(timeMeasureHorizon T), negTest' (X s ω) * G (s, ω)
          + 1 / 2 * (negTest'' (X s ω) * H (s, ω) ^ 2) ≤ 0 := by
        filter_upwards [hGω, hHω] with s hGs hHs
        rw [hGs, hHs, negTest''_mul_sq_eq_zero hσ, mul_zero, add_zero]
        exact negTest'_mul_drift_nonpos hκ hθ _
      have hle' : ∀ᵐ s ∂timeMeasure.restrict (Set.Ioc 0 t), negTest' (X s ω) * G (s, ω)
          + 1 / 2 * (negTest'' (X s ω) * H (s, ω) ^ 2) ≤ 0 := by
        rw [← timeMeasure_T_restrict_Ioc T htT]
        exact ae_restrict_of_ae hle
      exact integral_nonpos_of_ae hle'
    have hint : ∫ ω, (negTest (X t ω) - negTest v₀) ∂μ ≤ 0 := by
      rw [hI]; exact integral_nonpos_of_ae hslice
    simp only [hv, sub_zero] at hint
    have hintg : Integrable (fun ω => negTest (X t ω)) μ := by
      have := integrable_comp_at hB T hBmeas hBcont v₀ G H hasDerivAt_negTest abs_negTest'_le htT
      simpa only [hv, sub_zero] using this
    have hzero : ∫ ω, negTest (X t ω) ∂μ = 0 :=
      le_antisymm hint (integral_nonneg fun ω => negTest_nonneg _)
    have hae := (integral_eq_zero_iff_of_nonneg (fun ω => negTest_nonneg (X t ω)) hintg).1 hzero
    filter_upwards [hae] with ω hω
    exact (negTest_eq_zero_iff _).1 hω
  have hcont := ae_continuousOn_l2ItoProcess hB T hBmeas hBcont v₀ G H
  rw [← hXdef] at hcont
  have hall := ae_forall_eq_of_continuousOn T hcont (Y := fun t ω => max (X t ω) 0)
    (by
      filter_upwards [hcont] with ω hω
      exact (continuous_id.max continuous_const).comp_continuousOn hω)
    (fun t ht => by
      filter_upwards [hfix t ht] with ω hω
      exact (max_eq_left hω).symm)
  filter_upwards [hall] with ω hω t ht
  rw [hω t ht]
  exact le_max_right _ _

include hB hBcont in
/-- The regularized CIR solutions are nonnegative. -/
theorem cir_regularized_nonneg (p : Parameters) (hκ : 0 ≤ p.kappa) (hθ : 0 ≤ p.theta)
    {ε v₀ : ℝ} (hv₀ : 0 ≤ v₀) (G H : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hG : ⇑G =ᵐ[trimMeasure (μ := μ) T hBmeas]
      fun z => cirDrift p (l2ItoProcess T hBmeas v₀ G H z.1 z.2))
    (hH : ⇑H =ᵐ[trimMeasure (μ := μ) T hBmeas]
      fun z => cirRegularizedDiffusion p ε (l2ItoProcess T hBmeas v₀ G H z.1 z.2)) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, 0 ≤ l2ItoProcess T hBmeas v₀ G H t ω :=
  l2ItoProcess_nonneg_of_cir_type hB T hBmeas hBcont hv₀ hκ hθ
    (fun x hx => cirRegularizedDiffusion_of_nonpos p ε hx) G H (by simpa only [cirDrift] using
          hG) hH

include hB hBcont in
/-- Solutions with the square-root diffusion `ξ √(x⁺)` are nonnegative. -/
theorem cir_sqrt_nonneg (p : Parameters) (hκ : 0 ≤ p.kappa) (hθ : 0 ≤ p.theta)
    {v₀ : ℝ} (hv₀ : 0 ≤ v₀) (G H : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hG : ⇑G =ᵐ[trimMeasure (μ := μ) T hBmeas]
      fun z => cirDrift p (l2ItoProcess T hBmeas v₀ G H z.1 z.2))
    (hH : ⇑H =ᵐ[trimMeasure (μ := μ) T hBmeas]
      fun z => cirSqrtDiffusion p (l2ItoProcess T hBmeas v₀ G H z.1 z.2)) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, 0 ≤ l2ItoProcess T hBmeas v₀ G H t ω :=
  l2ItoProcess_nonneg_of_cir_type hB T hBmeas hBcont hv₀ hκ hθ
    (fun x hx => cirSqrtDiffusion_of_nonpos p hx) G H (by simpa only [cirDrift] using hG) hH

end Nonneg

end MathFin.Heston
