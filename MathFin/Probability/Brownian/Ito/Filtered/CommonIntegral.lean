/-
Copyright (c) 2026 Raphael Coelho, Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CommonL2
public import MathFin.Probability.Brownian.Ito.Filtered.CommonPredictable

/-!
# Common Integral

Construction of the continuous predictable L2 integral on a supplied
filtration, by isometric completion of actual Brownian increment sums.
No integral or martingale conclusion is assumed.

Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Common-filtration extension for Heston, 2026-10-18.

## Main definitions

* `itoAssemblyT`
* `itoIntegralCLMT`

## Main results

* `assembly_isometry_T`
* `itoIntegralCLM_T_simpleAssembly`
* `itoIntegralCLM_T_norm`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto.CommonIntegral
open MeasureTheory ProbabilityTheory Filter
open MathFin.FilteredIto.CommonNoise MathFin.FilteredIto.CommonPredictable
open scoped NNReal ENNReal InnerProductSpace
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ}

private lemma eLpNorm_uncurry_trim_T_eq_trim (T : ℝ≥0) (_hBmeas : ∀ t, Measurable (B t))
    (V : TBoundedSP T ℱ) :
    eLpNorm (Function.uncurry ⇑V.val) 2 (trimMeasureT (μ := μ) T ℱ)
      = eLpNorm (Function.uncurry ⇑V.val) 2
          ((CommonL2.timeMeasure.prod μ).trim
            ℱ.predictable_le_prod) := by
  let 𝓕 := ℱ

  have hS_pred : MeasurableSet[𝓕.predictable] (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)) :=
    MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓕) 0 T MeasurableSet.univ

  have hnull : ((CommonL2.timeMeasure.prod μ).trim 𝓕.predictable_le_prod)
      ({(0 : ℝ≥0)} ×ˢ (Set.univ : Set Ω)) = 0 := by
    have hbot_meas : MeasurableSet[𝓕.predictable] ({(0 : ℝ≥0)} ×ˢ (Set.univ : Set Ω)) :=
      MeasureTheory.measurableSet_predictable_singleton_bot_prod
        (𝓕 := 𝓕) (s := (Set.univ : Set Ω)) MeasurableSet.univ
    rw [MeasureTheory.trim_measurableSet_eq 𝓕.predictable_le_prod hbot_meas,
        Measure.prod_prod, CommonL2.timeMeasure_singleton, zero_mul]

  have hae : {z : ℝ≥0 × Ω | z.1 ≠ 0} ∈ MeasureTheory.ae
      ((CommonL2.timeMeasure.prod μ).trim 𝓕.predictable_le_prod) := by
    rw [show {z : ℝ≥0 × Ω | z.1 ≠ 0} = ({(0 : ℝ≥0)} ×ˢ (Set.univ : Set Ω))ᶜ by
          ext ⟨t, ω⟩; simp]
    exact compl_mem_ae_iff.mpr hnull
  have h_ae_eq : (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ⇑V.val)
      =ᵐ[((CommonL2.timeMeasure.prod μ).trim 𝓕.predictable_le_prod)]
        Function.uncurry ⇑V.val := by
    filter_upwards [hae] with z hz

    by_cases htT : z.1 ≤ T
    · rw [Set.indicator_of_mem]
      refine ⟨⟨?_, htT⟩, Set.mem_univ _⟩
      exact pos_iff_ne_zero.mpr hz
    · push Not at htT
      rw [Set.indicator_of_notMem]
      · exact (uncurry_eq_zero_of_lt V htT z.2).symm
      · intro ⟨⟨_, hle⟩, _⟩
        exact absurd hle (not_le.mpr htT)

  calc eLpNorm (Function.uncurry ⇑V.val) 2 (trimMeasureT (μ := μ) T ℱ)
      = eLpNorm (Function.uncurry ⇑V.val) 2
          (((CommonL2.timeMeasure.prod μ).trim 𝓕.predictable_le_prod).restrict
            (Set.Ioc 0 T ×ˢ Set.univ)) := by rw [trimMeasure_T_eq_restrict]; rfl
    _ = eLpNorm ((Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ⇑V.val)) 2
          ((CommonL2.timeMeasure.prod μ).trim 𝓕.predictable_le_prod) :=
        (MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hS_pred.nullMeasurableSet).symm
    _ = eLpNorm (Function.uncurry ⇑V.val) 2
          ((CommonL2.timeMeasure.prod μ).trim 𝓕.predictable_le_prod) :=
        MeasureTheory.eLpNorm_congr_ae h_ae_eq

private lemma simpleProcessL2_T_norm_eq (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : TBoundedSP T ℱ) :
    ‖simpleProcessL2T (μ := μ) T ℱ V.val‖
      = ‖CommonL2.simpleProcessL2 (μ := μ) hBmeas V.val‖ := by
  have h := eLpNorm_uncurry_trim_T_eq_trim (μ := μ) T hBmeas V
  unfold simpleProcessL2T CommonL2.simpleProcessL2
  rw [Lp.norm_toLp, Lp.norm_toLp, h]

/-- Linear map taking a horizon-bounded simple integrand to its terminal integral. -/
def itoAssemblyT (hB : IsFilteredPreBrownian B ℱ μ) (T : ℝ≥0) :
    TBoundedSP T ℱ →ₗ[ℝ] Lp ℝ 2 μ :=
  (CommonL2.itoAssembly hB hB.measurable_eval).comp (TBoundedSP T ℱ).subtype

theorem assembly_isometry_T (hB : IsFilteredPreBrownian B ℱ μ) (T : ℝ≥0) (V : TBoundedSP T ℱ) :
    ‖itoAssemblyT hB T V‖ = ‖simpleAssemblyT (μ := μ) T ℱ V‖ := by
  show ‖CommonL2.itoAssembly hB hB.measurable_eval V.val‖ =
    ‖simpleProcessL2T (μ := μ) T ℱ V.val‖
  rw [simpleProcessL2_T_norm_eq T hB.measurable_eval V]
  exact CommonL2.assembly_isometry hB hB.measurable_eval V.val

/-- The actual terminal Itô integral, defined by continuous extension of the
increment-sum map on the dense simple predictable processes. -/
def itoIntegralCLMT (hB : IsFilteredPreBrownian B ℱ μ) (T : ℝ≥0) :
    Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ) →L[ℝ] Lp ℝ 2 μ :=
  (itoAssemblyT hB T).extendOfNorm (simpleAssemblyT (μ := μ) T ℱ)

theorem itoIntegralCLM_T_simpleAssembly (hB : IsFilteredPreBrownian B ℱ μ) (T : ℝ≥0)
    (V : TBoundedSP T ℱ) :
    itoIntegralCLMT hB T (simpleAssemblyT (μ := μ) T ℱ V) =
      CommonL2.itoSimpleLp hB hB.measurable_eval V.val := by
  rw [itoIntegralCLMT, LinearMap.extendOfNorm_eq (simpleAssembly_T_denseRange T ℱ)
    ⟨1, fun W => by rw [one_mul]; exact (assembly_isometry_T hB T W).le⟩]
  rfl

theorem itoIntegralCLM_T_norm (hB : IsFilteredPreBrownian B ℱ μ) (T : ℝ≥0)
    (f : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    ‖itoIntegralCLMT hB T f‖ = ‖f‖ := by
  rw [itoIntegralCLMT]
  exact LinearMap.norm_extendOfNorm_eq_of_isometry
    (simpleAssembly_T_denseRange T ℱ) (assembly_isometry_T hB T) f

end MathFin.FilteredIto.CommonIntegral
