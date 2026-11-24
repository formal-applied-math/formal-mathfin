/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CommonLift
public import MathFin.Probability.Brownian.Ito.Filtered.CommonContinuous
public import MathFin.Models.StochVol.Heston.CIRStrong

/-!
# Common CIR

Transfer of the constructed finite-horizon CIR solution to a supplied common
Brownian filtration. Integral compatibility is proved by completion in CommonLift;
the continuous representatives agree simultaneously at every time.

## Main results

* `continuous_integral_natural_lift`
* `exists_cir_on_common_filtration`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

noncomputable section
namespace MathFin.Heston.CommonCIR
open MathFin.FilteredIto
open MeasureTheory ProbabilityTheory Filter Topology
open MathFin.FilteredIto.CommonNoise MathFin.FilteredIto.CommonLift
open scoped NNReal ENNReal
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ}

theorem continuous_integral_natural_lift (hB : BrownianOn ℱ B μ) (T : ℝ≥0)
    (hc : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
    (H : Lp ℝ 2 (MathFin.ItoIntegralCLM.trimMeasure (μ := μ) T hB.measurable)) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T,
      CommonContinuous.itoContinuousMod T hB.measurable (lpLift (natural_le hB) T H) t ω =
        MathFin.ItoIntegralProcessContinuousModification.itoContinuousMod T hB.measurable H t ω
              := by
  apply MathFin.FilteredIto.ae_forall_eq_of_continuousOn T
    (CommonContinuous.itoContinuousMod_continuousOn hB T hB.measurable hc _)
    (MathFin.ItoIntegralProcessContinuousModification.itoContinuousMod_continuousOn
      hB.law T hB.measurable hc H)
  intro t ht
  have he := process_commutes (natural_le hB) (brownianOn_natural hB.law hB.measurable) hB T t H
  have hn := process_natural_eq hB.law hB.measurable T t H
  have hp := CommonContinuous.itoContinuousMod_modification hB T hB.measurable hc
    (lpLift (natural_le hB) T H) ht
  rw [he, hn] at hp
  exact hp.trans (MathFin.ItoIntegralProcessContinuousModification.itoContinuousMod_modification
    hB.law T hB.measurable hc H ht).symm

/-- An actual nonnegative, predictable, continuous finite-horizon CIR solution
on the common filtration, satisfying its genuine common-filtration integral
equation. Pathwise uniqueness for arbitrary enlarged-filtration competitors is
not asserted by this existence-and-transfer theorem. -/
theorem exists_cir_on_common_filtration (hB : BrownianOn ℱ B μ) (T : ℝ≥0)
    (hc : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
    (p : MathFin.Heston.Parameters) (hk : 0 ≤ p.kappa) (hθ : 0 ≤ p.theta)
    {v₀ : ℝ} (hv₀ : 0 ≤ v₀) :
    ∃ (V : ℝ≥0 → Ω → ℝ)
      (G H : Lp ℝ 2 (CommonPredictable.trimMeasure_T (μ := μ) T ℱ)),
      IsStronglyPredictable ℱ V ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => V t ω) (Set.Icc 0 T)) ∧
      MemLp (Function.uncurry V) 2 (CommonPredictable.trimMeasure_T (μ := μ) T ℱ) ∧
      (∀ᵐ ω ∂μ, ∀ t ≤ T, 0 ≤ V t ω) ∧
      (⇑G =ᵐ[CommonPredictable.trimMeasure_T (μ := μ) T ℱ]
        fun z => MathFin.Heston.cirDrift p (V z.1 z.2)) ∧
      (⇑H =ᵐ[CommonPredictable.trimMeasure_T (μ := μ) T ℱ]
        fun z => MathFin.Heston.cirDiffusion p (V z.1 z.2)) ∧
      (∀ᵐ ω ∂μ, ∀ t ≤ T, V t ω = v₀ +
        (∫ s in Set.Ioc 0 t, MathFin.Heston.cirDrift p (V s ω) ∂MathFin.ItoIntegralL2.timeMeasure) +
          CommonContinuous.itoContinuousMod T hB.measurable H t ω) := by
  obtain ⟨V, G, H, _hrep, hp, hcV, hm, hnn, hG, hH, heq⟩ :=
    MathFin.Heston.exists_cir_strong_solution hB.law T hB.measurable hc p hk hθ hv₀
  have hle := natural_le hB
  have hp' := predictable_mono hle hp
  have hm' : MemLp (Function.uncurry V) 2 (CommonPredictable.trimMeasure_T (μ := μ) T ℱ) := by
    apply memLp_iff.mpr
    change eLpNorm (Function.uncurry V) 2
      (((CommonPredictable.timeMeasure_T T).prod μ).trim ℱ.predictable_le_prod) < ⊤
    rw [eLpNorm_trim ℱ.predictable_le_prod hp',
      ← eLpNorm_trim (MathFin.ItoIntegralL2.natFiltration hB.measurable).predictable_le_prod hp]
    exact hm.eLpNorm_lt_top
  have hGm : StronglyMeasurable[(MathFin.ItoIntegralL2.natFiltration hB.measurable).predictable]
      (fun z : ℝ≥0 × Ω => MathFin.Heston.cirDrift p (V z.1 z.2)) :=
    (show Continuous (MathFin.Heston.cirDrift p) by
      unfold MathFin.Heston.cirDrift
      fun_prop).comp_stronglyMeasurable hp
  have hHm : StronglyMeasurable[(MathFin.ItoIntegralL2.natFiltration hB.measurable).predictable]
      (fun z : ℝ≥0 × Ω => MathFin.Heston.cirDiffusion p (V z.1 z.2)) :=
    (MathFin.Heston.continuous_cirDiffusion p).comp_stronglyMeasurable hp
  refine ⟨V, lpLift hle T G, lpLift hle T H, hp', hcV, hm', hnn,
    (coeFn_lpLift hle T G).trans (ae_lift hle T (Lp.stronglyMeasurable G) hGm hG),
    (coeFn_lpLift hle T H).trans (ae_lift hle T (Lp.stronglyMeasurable H) hHm hH), ?_⟩
  filter_upwards [heq, continuous_integral_natural_lift hB T hc H] with ω he hl t ht
  rw [hl t ht]
  exact he t ht

end MathFin.Heston.CommonCIR
