/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Models.StochVol.Heston.CommonCIR
public import MathFin.Probability.Brownian.Ito.Filtered.CommonPredictableProcess
public import MathFin.Probability.Brownian.Ito.Filtered.CommonMixedQv

/-!
# Common Heston State

Construction of the actual finite-horizon Heston log-price and variance on
a supplied two-Brownian common filtration, for every |rho| <= 1.

This is a solution-construction theorem. It does not assume or prove the affine
transform identity, price martingality, or the final vanilla-pricing formula.

## Main results

* `exists_heston_state`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

noncomputable section
namespace MathFin.Heston.CommonState
open MathFin.FilteredIto
open MeasureTheory ProbabilityTheory Filter Topology
open MathFin.FilteredIto.CommonNoise MathFin.FilteredIto.CommonLift
open scoped NNReal ENNReal
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B Z : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ}

theorem exists_heston_state (h : IndependentPair ℱ B Z μ) (T : ℝ≥0)
    (hcB : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
    (hcZ : ∀ ω, Continuous fun t : ℝ≥0 => Z t ω)
    (p : MathFin.Heston.Parameters) (hk : 0 ≤ p.kappa) (hθ : 0 ≤ p.theta)
    (hξ : 0 < p.xi) (hρ : |p.rho| ≤ 1) (x₀ v₀ : ℝ) (hv₀ : 0 ≤ v₀) :
    ∃ (X V : ℝ≥0 → Ω → ℝ)
      (Gx Hv Hx : Lp ℝ 2 (CommonPredictable.trimMeasureT (μ := μ) T ℱ)),
      IsStronglyPredictable ℱ X ∧ IsStronglyPredictable ℱ V ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) (Set.Icc 0 T)) ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => V t ω) (Set.Icc 0 T)) ∧
      (∀ᵐ ω ∂μ, ∀ t ≤ T, 0 ≤ V t ω) ∧
      (⇑Gx =ᵐ[CommonPredictable.trimMeasureT (μ := μ) T ℱ]
        fun z => (p.r-p.q) - (1/2 : ℝ) * V z.1 z.2) ∧
      (⇑Hv =ᵐ[CommonPredictable.trimMeasureT (μ := μ) T ℱ]
        fun z => p.xi * Real.sqrt (V z.1 z.2)) ∧
      (⇑Hx =ᵐ[CommonPredictable.trimMeasureT (μ := μ) T ℱ]
        fun z => Real.sqrt (V z.1 z.2)) ∧
      (∀ᵐ ω ∂μ, ∀ t ≤ T, V t ω = v₀ +
        (∫ s in Set.Ioc 0 t, p.kappa * (p.theta - V s ω) ∂MathFin.ItoIntegralL2.timeMeasure) +
          CommonContinuous.itoContinuousMod T h.left.measurable Hv t ω) ∧
      (∀ᵐ ω ∂μ, ∀ t ≤ T, X t ω = x₀ +
        (∫ s in Set.Ioc 0 t, (p.r-p.q) - (1/2 : ℝ) * V s ω ∂MathFin.ItoIntegralL2.timeMeasure) +
          CommonContinuous.itoContinuousMod T (h.correlated_brownian hρ).measurable Hx t ω) := by
  obtain ⟨V, _G, H, _hrep, hpV, hcV, hmV, hnn, _hG, hH, heqV⟩ :=
    MathFin.Heston.exists_cir_strong_solution h.left_law T h.left.measurable hcB p hk hθ hv₀
  have hle := natural_le h.left
  have hpV' := predictable_mono hle hpV
  have hβ : MemLp (fun z : ℝ≥0 × Ω => (p.r-p.q) - (1/2 : ℝ) * V z.1 z.2) 2
      (MathFin.ItoIntegralCLM.trimMeasure (μ := μ) T h.left.measurable) :=
    (memLp_const (p.r-p.q)).sub (hmV.const_mul (1/2 : ℝ))
  let β := hβ.toLp (fun z : ℝ≥0 × Ω => (p.r-p.q) - (1/2 : ℝ) * V z.1 z.2)
  let Hv := lpLift hle T H
  let Hx := p.xi⁻¹ • Hv
  let Gx := lpLift hle T β
  let W := correlatedNoise p.rho B Z
  have hW : BrownianOn ℱ W μ := h.correlated_brownian hρ
  have hcW : ∀ ω, Continuous fun t : ℝ≥0 => W t ω := by
    intro ω
    exact ((hcB ω).const_mul p.rho).add ((hcZ ω).const_mul (orthogonalWeight p.rho))
  let D := MathFin.ItoIntegralProcessContinuousModification.driftContinuousMod T h.left.measurable β
  let M := CommonContinuous.itoContinuousMod T hW.measurable Hx
  let X := fun t ω => x₀ + D t ω + M t ω
  have hpD : IsStronglyPredictable ℱ D := predictable_mono hle
    (MathFin.ItoIntegralProcessContinuousModification.driftContinuousMod_isStronglyPredictable T
          h.left.measurable β)
  have hpM : IsStronglyPredictable ℱ M :=
    CommonContinuous.itoContinuousMod_isStronglyPredictable hW T hW.measurable hcW Hx
  have hpX : IsStronglyPredictable ℱ X :=
    (IsStronglyPredictable.const.add hpD).add hpM
  have hcX : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) (Set.Icc 0 T) := by
    filter_upwards [MathFin.FilteredIto.driftContinuousMod_continuousOn T h.left.measurable β,
      CommonContinuous.itoContinuousMod_continuousOn hW T hW.measurable hcW Hx] with ω hd hm
    exact (continuousOn_const.add hd).add hm
  have hβm : StronglyMeasurable[(MathFin.ItoIntegralL2.natFiltration h.left.measurable).predictable]
      (fun z : ℝ≥0 × Ω => (p.r-p.q) - (1/2 : ℝ) * V z.1 z.2) :=
    (show Continuous (fun v : ℝ => (p.r-p.q) - (1/2 : ℝ) * v) by
          fun_prop).comp_stronglyMeasurable hpV
  have hGx : ⇑Gx =ᵐ[CommonPredictable.trimMeasureT (μ := μ) T ℱ]
      fun z => (p.r-p.q) - (1/2 : ℝ) * V z.1 z.2 :=
    (coeFn_lpLift hle T β).trans (ae_lift hle T (Lp.stronglyMeasurable β) hβm hβ.coeFn_toLp)
  have hHm : StronglyMeasurable[(MathFin.ItoIntegralL2.natFiltration h.left.measurable).predictable]
      (fun z : ℝ≥0 × Ω => MathFin.Heston.cirDiffusion p (V z.1 z.2)) :=
    (MathFin.Heston.continuous_cirDiffusion p).comp_stronglyMeasurable hpV
  have hHv : ⇑Hv =ᵐ[CommonPredictable.trimMeasureT (μ := μ) T ℱ]
      fun z => p.xi * Real.sqrt (V z.1 z.2) :=
    (coeFn_lpLift hle T H).trans (ae_lift hle T (Lp.stronglyMeasurable H) hHm hH)
  have hHx : ⇑Hx =ᵐ[CommonPredictable.trimMeasureT (μ := μ) T ℱ]
      fun z => Real.sqrt (V z.1 z.2) := by
    filter_upwards [Lp.coeFn_smul p.xi⁻¹ Hv, hHv] with z hs hv
    rw [show Hx z = (p.xi⁻¹ • (Hv : ℝ≥0 × Ω → ℝ)) z from hs,
      Pi.smul_apply, smul_eq_mul, hv, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hξ), one_mul]
  have heqV' : ∀ᵐ ω ∂μ, ∀ t ≤ T, V t ω = v₀ +
      (∫ s in Set.Ioc 0 t, p.kappa * (p.theta - V s ω) ∂MathFin.ItoIntegralL2.timeMeasure) +
        CommonContinuous.itoContinuousMod T h.left.measurable Hv t ω := by
    filter_upwards [heqV, CommonCIR.continuous_integral_natural_lift h.left T hcB H] with ω he
          hl t ht
    rw [hl t ht]
    exact he t ht
  have heqX : ∀ᵐ ω ∂μ, ∀ t ≤ T, X t ω = x₀ +
      (∫ s in Set.Ioc 0 t, (p.r-p.q) - (1/2 : ℝ) * V s ω ∂MathFin.ItoIntegralL2.timeMeasure) +
        CommonContinuous.itoContinuousMod T hW.measurable Hx t ω := by
    filter_upwards [MathFin.FilteredIto.driftContinuousMod_eq_setIntegral_all T h.left.measurable β,
      MathFin.FilteredIto.ae_ae_of_ae_trim T h.left.measurable hβ.coeFn_toLp] with ω hd hco t ht
    have hi : (∫ s in Set.Ioc 0 t, β (s,ω) ∂MathFin.ItoIntegralL2.timeMeasure) =
        ∫ s in Set.Ioc 0 t, (p.r-p.q) - (1/2 : ℝ) * V s ω ∂MathFin.ItoIntegralL2.timeMeasure := by
      apply integral_congr_ae
      rw [← MathFin.FilteredIto.timeMeasure_T_restrict_Ioc T ht]
      exact ae_restrict_of_ae hco
    change x₀ + D t ω + M t ω = _
    rw [show D t ω = _ from hd t ht, hi]
  exact ⟨X, V, Gx, Hv, Hx, hpX, hpV', hcX, hcV, hnn, hGx, hHv, hHx, heqV', heqX⟩

end MathFin.Heston.CommonState
