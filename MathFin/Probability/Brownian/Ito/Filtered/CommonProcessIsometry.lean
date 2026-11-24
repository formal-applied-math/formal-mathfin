/-
Copyright (c) 2026 Raphael Coelho, Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CommonProcessGeneral

/-!
# Common Process Isometry

Time-indexed Ito isometry on a supplied filtration (derived from MathFin
by derive-common-isometry.py).

Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Common-filtration extension for Heston, 2026-10-19.

## Main results

* `itoProcessCLM_norm_sq`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto
namespace CommonProcessGeneral

open MeasureTheory ProbabilityTheory CommonL2 CommonPredictable CommonIntegral CommonProcess
open MathFin.FilteredIto.CommonNoise
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ} (hB : BrownianOn ℱ B μ)

include hB

omit [IsProbabilityMeasure μ] in

private lemma integral_rectTerm_mul_band (t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ ℱ) (p q : ℝ≥0 × ℝ≥0) :
    ∫ z in (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)),
        rectTerm hBmeas V p z * rectTerm hBmeas V q z ∂(timeMeasure.prod μ)
      = (∫ ω, V.value p ω * V.value q ω ∂μ)
          * max 0 ((min (min (p.2 : ℝ) q.2) (t : ℝ)) - (max (p.1 : ℝ) q.1)) := by
  haveI : IsProbabilityMeasure μ := hB.law.isGaussianProcess.isProbabilityMeasure
  have hfun : (fun z : ℝ≥0 × Ω ↦ rectTerm hBmeas V p z * rectTerm hBmeas V q z)
      = fun z ↦ ((Set.Ioc p.1 p.2).indicator (fun _ ↦ (1 : ℝ)) z.1
                    * (Set.Ioc q.1 q.2).indicator (fun _ ↦ (1 : ℝ)) z.1)
                  * (V.value p z.2 * V.value q z.2) := by
    funext z; simp only [rectTerm, elemIntegrand]; ring
  rw [setIntegral_congr_fun (measurableSet_Ioc.prod MeasurableSet.univ)
        (fun z _ ↦ congrFun hfun z),
      ← Measure.restrict_prod_eq_prod_univ,
      integral_prod_mul
        (fun i : ℝ≥0 ↦ (Set.Ioc p.1 p.2).indicator (fun _ ↦ (1 : ℝ)) i
          * (Set.Ioc q.1 q.2).indicator (fun _ ↦ (1 : ℝ)) i)
        (fun ω ↦ V.value p ω * V.value q ω), mul_comm]
  congr 1
  have hpt : ∀ i : ℝ≥0, (Set.Ioc p.1 p.2).indicator (fun _ ↦ (1 : ℝ)) i
        * (Set.Ioc q.1 q.2).indicator (fun _ ↦ (1 : ℝ)) i
        = (Set.Ioc p.1 p.2 ∩ Set.Ioc q.1 q.2).indicator (1 : ℝ≥0 → ℝ) i := by
    intro i; rw [Set.inter_indicator_one]; rfl
  simp_rw [hpt]
  rw [integral_indicator_one (measurableSet_Ioc.inter measurableSet_Ioc), Measure.real_def,
      Measure.restrict_apply (measurableSet_Ioc.inter measurableSet_Ioc),
      Set.Ioc_inter_Ioc, Set.Ioc_inter_Ioc, timeMeasure_Ioc, ENNReal.toReal_ofReal']
  push_cast
  rw [max_eq_left (le_max_of_le_left (by positivity))]
  exact max_comm _ _

omit hB in

private lemma band_overlap_real (P1 P2 Q1 Q2 T : ℝ) :
    max 0 (min (min P2 T) (min Q2 T) - max (min P1 T) (min Q1 T))
      = max 0 (min (min P2 Q2) T - max P1 Q1) := by

  have hR : min (min P2 T) (min Q2 T) = min (min P2 Q2) T := by
    rw [min_min_min_comm, min_self]
  rw [hR]
  rcases le_total (max P1 Q1) T with hLT | hLT
  ·
    rw [min_eq_left ((le_max_left P1 Q1).trans hLT),
        min_eq_left ((le_max_right P1 Q1).trans hLT)]
  ·
    have hRle : min (min P2 Q2) T ≤ T := min_le_right _ _
    have hL : max (min P1 T) (min Q1 T) = T := by
      apply le_antisymm (max_le (min_le_right _ _) (min_le_right _ _))
      rcases le_total P1 Q1 with h | h
      · rw [max_eq_right h] at hLT; exact le_max_of_le_right (le_min hLT le_rfl)
      · rw [max_eq_left h] at hLT; exact le_max_of_le_left (le_min hLT le_rfl)
    rw [hL, max_eq_left (by linarith : min (min P2 Q2) T - T ≤ 0),
        max_eq_left (by linarith : min (min P2 Q2) T - max P1 Q1 ≤ 0)]

omit hB in

private lemma trimMeasure_T_restrict_band {t T : ℝ≥0} (htT : t ≤ T)
    (_hBmeas : ∀ u, Measurable (B u)) :
    (trimMeasureT (μ := μ) T ℱ).restrict (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω))
      = trimMeasureT (μ := μ) t ℱ := by
  rw [trimMeasure_T_eq_restrict T ℱ,
      Measure.restrict_restrict_of_subset
        (Set.prod_mono (Set.Ioc_subset_Ioc le_rfl htT) subset_rfl),
      trimMeasure_T_eq_restrict t ℱ]

omit hB in

private lemma integral_trimMeasure_T {t : ℝ≥0} (_hBmeas : ∀ u, Measurable (B u))
    {f : ℝ≥0 × Ω → ℝ}
    (hf : StronglyMeasurable[ℱ.predictable] f) :
    ∫ z, f z ∂(trimMeasureT (μ := μ) t ℱ)
      = ∫ z in (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)), f z ∂(timeMeasure.prod μ) := by
  rw [show trimMeasureT (μ := μ) t ℱ
        = ((timeMeasureT t).prod μ).trim ℱ.predictable_le_prod from rfl,
      integral_trim ℱ.predictable_le_prod hf,
      show ((timeMeasureT t).prod μ : Measure (ℝ≥0 × Ω))
          = (timeMeasure.prod μ).restrict (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)) from by
        rw [timeMeasureT, Measure.restrict_prod_eq_prod_univ]; rfl]

omit [IsProbabilityMeasure μ] in

private lemma band_integral_uncurry_sq {t T : ℝ≥0} (htT : t ≤ T)
    (hBmeas : ∀ u, Measurable (B u)) (V : SimpleProcess ℝ ℱ) :
    ∫ z in (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)),
        (Function.uncurry ⇑V z) ^ 2 ∂(trimMeasureT (μ := μ) T ℱ)
      = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support,
          (∫ ω, V.value p ω * V.value q ω ∂μ)
            * max 0 ((min (min (p.2 : ℝ) q.2) (t : ℝ)) - max (p.1 : ℝ) q.1) := by
  haveI : IsProbabilityMeasure μ := hB.law.isGaussianProcess.isProbabilityMeasure

  rw [trimMeasure_T_restrict_band htT hBmeas]
  simp only [pow_two]
  have hsm : StronglyMeasurable[ℱ.predictable]
      (fun z ↦ Function.uncurry ⇑V z * Function.uncurry ⇑V z) :=
    V.isStronglyPredictable.mul V.isStronglyPredictable
  rw [integral_trimMeasure_T hBmeas hsm]

  have hint : ∀ p ∈ V.value.support, ∀ q ∈ V.value.support,
      Integrable (fun z ↦ rectTerm hBmeas V p z * rectTerm hBmeas V q z) (timeMeasure.prod μ) :=
    fun p _ q _ ↦ (memLp_rectTerm hBmeas V p).integrable_mul (memLp_rectTerm hBmeas V q)
  have hsq : (fun z ↦ Function.uncurry ⇑V z * Function.uncurry ⇑V z)
      =ᵐ[(timeMeasure.prod μ).restrict (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω))]
        fun z ↦ ∑ p ∈ V.value.support, ∑ q ∈ V.value.support,
          rectTerm hBmeas V p z * rectTerm hBmeas V q z := by
    filter_upwards [ae_restrict_of_ae (uncurry_ae_eq_sum_rectTerm hBmeas V)] with z hz
    rw [hz, Finset.sum_mul_sum]
  rw [integral_congr_ae hsq,
      integral_finsetSum _ (fun p hp ↦
        (integrable_finsetSum _ fun q hq ↦ hint p hp q hq).integrableOn)]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [integral_finsetSum _ fun q hq ↦ (hint p hp q hq).integrableOn]
  exact Finset.sum_congr rfl fun q _ ↦ integral_rectTerm_mul_band hB t hBmeas V p q

omit [IsProbabilityMeasure μ] in

private lemma itoSimpleProcessLp_band_isometry {t T : ℝ≥0} (htT : t ≤ T)
    (hBmeas : ∀ u, Measurable (B u)) (V : SimpleProcess ℝ ℱ) :
    ‖itoSimpleProcessLp (μ := μ) hB hBmeas V t‖ ^ 2
      = ∫ z in (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)),
          (Function.uncurry ⇑V z) ^ 2 ∂(trimMeasureT (μ := μ) T ℱ) := by
  rw [band_integral_uncurry_sq hB htT hBmeas V]
  have hLHS : ‖itoSimpleProcessLp (μ := μ) hB hBmeas V t‖ ^ 2
      = ∫ ω, (itoSimpleProcess hBmeas V t ω) ^ 2 ∂μ := by
    rw [MathFin.lp_two_norm_sq (itoSimpleProcessLp hB hBmeas V t)]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_itoSimpleProcess hB hBmeas V t).coeFn_toLp] with ω hω
    rw [show (itoSimpleProcessLp hB hBmeas V t : Ω → ℝ) ω = itoSimpleProcess hBmeas V t ω from hω]
  rw [hLHS, itoSimpleProcess_isometry_time hB hBmeas V t]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  congr 1
  push_cast
  exact band_overlap_real _ _ _ _ _

omit hB in

private lemma measurableSet_band (t : ℝ≥0) (_hBmeas : ∀ u, Measurable (B u)) :
    MeasurableSet[ℱ.predictable] (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)) :=
  MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := ℱ) 0 t
    MeasurableSet.univ

omit hB in

private noncomputable def truncCLM (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u)) :
    Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ) →L[ℝ]
      Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ) :=
  LinearMap.mkContinuous
    { toFun := fun φ ↦ ((Lp.memLp φ).indicator (measurableSet_band t hBmeas).nullMeasurableSet).toLp
        ((Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)).indicator (φ : ℝ≥0 × Ω → ℝ))
      map_add' := fun φ ψ ↦ by
        refine Lp.ext ?_
        filter_upwards [((Lp.memLp (φ + ψ)).indicator (measurableSet_band t
              hBmeas).nullMeasurableSet).coeFn_toLp,
          Lp.coeFn_add (((Lp.memLp φ).indicator (measurableSet_band t
                hBmeas).nullMeasurableSet).toLp _)
            (((Lp.memLp ψ).indicator (measurableSet_band t hBmeas).nullMeasurableSet).toLp _),
          ((Lp.memLp φ).indicator (measurableSet_band t hBmeas).nullMeasurableSet).coeFn_toLp,
          ((Lp.memLp ψ).indicator (measurableSet_band t hBmeas).nullMeasurableSet).coeFn_toLp,
          Lp.coeFn_add φ ψ] with z e_sum e_radd e_φ e_ψ h_φψ
        rw [e_sum, e_radd, Pi.add_apply, e_φ, e_ψ]
        simp only [Set.indicator_apply, h_φψ, Pi.add_apply]
        split_ifs <;> ring
      map_smul' := fun c φ ↦ by
        refine Lp.ext ?_
        filter_upwards [((Lp.memLp (c • φ)).indicator (measurableSet_band t
              hBmeas).nullMeasurableSet).coeFn_toLp,
          Lp.coeFn_smul c (((Lp.memLp φ).indicator (measurableSet_band t
                hBmeas).nullMeasurableSet).toLp _),
          ((Lp.memLp φ).indicator (measurableSet_band t hBmeas).nullMeasurableSet).coeFn_toLp,
          Lp.coeFn_smul c φ] with z e_sm e_rsmul e_φ h_φ
        rw [e_sm, RingHom.id_apply, e_rsmul, Pi.smul_apply, e_φ]
        simp only [Set.indicator_apply, h_φ, Pi.smul_apply, smul_eq_mul]
        split_ifs <;> ring }
    1 (fun φ ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [one_mul, Lp.norm_toLp, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top φ)
        (eLpNorm_indicator_le _ (measurableSet_band t hBmeas).nullMeasurableSet))

omit [IsProbabilityMeasure μ] hB in

private lemma truncCLM_norm_sq (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    ‖truncCLM (μ := μ) T t hBmeas φ‖ ^ 2
      = ∫ z in (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)), (φ z) ^ 2
          ∂(trimMeasureT (μ := μ) T ℱ) := by
  rw [MathFin.lp_two_norm_sq, ← integral_indicator (measurableSet_band t hBmeas)]
  refine integral_congr_ae ?_
  filter_upwards [((Lp.memLp φ).indicator (measurableSet_band t
        hBmeas).nullMeasurableSet).coeFn_toLp] with z hz
  rw [show (truncCLM (μ := μ) T t hBmeas φ : ℝ≥0 × Ω → ℝ) z
        = (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)).indicator (φ : ℝ≥0 × Ω → ℝ) z from hz]
  by_cases hzm : z ∈ (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω))
  · rw [Set.indicator_of_mem hzm, Set.indicator_of_mem hzm]
  · rw [Set.indicator_of_notMem hzm, Set.indicator_of_notMem hzm]; norm_num

theorem itoProcessCLM_norm_sq {t T : ℝ≥0} (htT : t ≤ T) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    ‖itoProcessCLM hB T t hBmeas φ‖ ^ 2
      = ∫ z in (Set.Ioc 0 t ×ˢ (Set.univ : Set Ω)), (φ z) ^ 2
          ∂(trimMeasureT (μ := μ) T ℱ) := by
  rw [← truncCLM_norm_sq T t hBmeas φ]
  refine congrFun (DenseRange.equalizer (simpleAssembly_T_denseRange (μ := μ) T ℱ)
    ((continuous_pow 2).comp (itoProcessCLM hB T t hBmeas).continuous.norm)
    ((continuous_pow 2).comp (truncCLM (μ := μ) T t hBmeas).continuous.norm)
    (funext fun V ↦ ?_)) φ
  simp only [Function.comp_apply]
  rw [itoProcessCLM_simpleAssembly_T, truncCLM_norm_sq,
      itoSimpleProcessLp_band_isometry hB htT hBmeas V.val]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae (memLp_uncurry_trim_T T ℱ V.val).coeFn_toLp] with z hz
  rw [show (simpleAssemblyT (μ := μ) T ℱ V : ℝ≥0 × Ω → ℝ) z
        = Function.uncurry ⇑V.val z from hz]

end CommonProcessGeneral
end MathFin.FilteredIto
