/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CommonIntegral
public import MathFin.Probability.Brownian.Ito.Filtered.CommonProcessGeneral
public import MathFin.Probability.Brownian.Ito.ItoIntegralProcessGeneral
public import Mathlib.MeasureTheory.Function.LpSeminorm.Trim

/-!
# Common Lift

Enlargement of the filtration for predictable L2 kernels. This file builds
the norm-preserving inclusion needed to transport the existing natural-filtration
CIR integrands into the joint Brownian filtration.

## Main definitions

* `lpLiftLI`
* `simpleLift`
* `boundedSimpleLift`

## Main results

* `process_commutes`
* `integral_natural_eq`
* `process_natural_eq`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto.CommonLift
open MeasureTheory ProbabilityTheory
open MathFin.FilteredIto.CommonNoise MathFin.FilteredIto.CommonPredictable
      MathFin.FilteredIto.CommonIntegral
open scoped NNReal ENNReal
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {ℱ₁ ℱ₂ : Filtration ℝ≥0 mΩ}

theorem predictable_le (hle : ∀ t, ℱ₁ t ≤ ℱ₂ t) : ℱ₁.predictable ≤ ℱ₂.predictable := by
  apply MeasurableSpace.generateFrom_mono
  rintro s (⟨A, hA, rfl⟩ | ⟨t, A, hA, rfl⟩)
  · exact Or.inl ⟨A, hle 0 A hA, rfl⟩
  · exact Or.inr ⟨t, A, hle t A hA, rfl⟩

theorem natural_le {B : ℝ≥0 → Ω → ℝ} (hB : BrownianOn ℱ₂ B μ) :
    ∀ t, MathFin.ItoIntegralL2.natFiltration hB.measurable t ≤ ℱ₂ t := by
  intro t
  apply iSup₂_le
  intro s hst
  exact (measurable_iff_comap_le.mp (hB.adapted s).measurable).trans (ℱ₂.mono hst)

theorem predictable_mono (hle : ∀ t, ℱ₁ t ≤ ℱ₂ t) {X : ℝ≥0 → Ω → ℝ}
    (hX : IsStronglyPredictable ℱ₁ X) : IsStronglyPredictable ℱ₂ X :=
  (show StronglyMeasurable[ℱ₁.predictable] (Function.uncurry X) from hX).mono
    (predictable_le hle)

theorem memLp_lift (hle : ∀ t, ℱ₁ t ≤ ℱ₂ t) (T : ℝ≥0)
    (f : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ₁)) :
    MemLp (f : ℝ≥0 × Ω → ℝ) 2 (trimMeasure_T (μ := μ) T ℱ₂) := by
  have hf := (Lp.stronglyMeasurable f).mono (predictable_le hle)
  refine memLp_iff.mpr ?_
  change eLpNorm (f : ℝ≥0 × Ω → ℝ) 2 (((timeMeasure_T T).prod μ).trim ℱ₂.predictable_le_prod) < ⊤
  rw [eLpNorm_trim ℱ₂.predictable_le_prod hf,
    ← eLpNorm_trim ℱ₁.predictable_le_prod (Lp.stronglyMeasurable f)]
  exact memLp_iff.mp (Lp.memLp f)

def lpLift (hle : ∀ t, ℱ₁ t ≤ ℱ₂ t) (T : ℝ≥0)
    (f : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ₁)) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ₂) := (memLp_lift hle T f).toLp f

theorem coeFn_lpLift (hle : ∀ t, ℱ₁ t ≤ ℱ₂ t) (T : ℝ≥0)
    (f : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ₁)) :
    (lpLift hle T f : ℝ≥0 × Ω → ℝ) =ᵐ[trimMeasure_T (μ := μ) T ℱ₂] f :=
  (memLp_lift hle T f).coeFn_toLp

theorem ae_lift (hle : ∀ t, ℱ₁ t ≤ ℱ₂ t) (T : ℝ≥0) {f g : ℝ≥0 × Ω → ℝ}
    (hf : StronglyMeasurable[ℱ₁.predictable] f) (hg : StronglyMeasurable[ℱ₁.predictable] g)
    (he : f =ᵐ[trimMeasure_T (μ := μ) T ℱ₁] g) :
    f =ᵐ[trimMeasure_T (μ := μ) T ℱ₂] g := by
  have he' : f =ᵐ[(timeMeasure_T T).prod μ] g := ae_eq_of_ae_eq_trim he
  exact (hf.mono (predictable_le hle)).ae_eq_trim_of_stronglyMeasurable
    ℱ₂.predictable_le_prod (hg.mono (predictable_le hle)) he'

theorem lpLift_add (hle : ∀ t, ℱ₁ t ≤ ℱ₂ t) (T : ℝ≥0)
    (f g : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ₁)) :
    lpLift hle T (f+g) = lpLift hle T f + lpLift hle T g := by
  apply Lp.ext
  filter_upwards [coeFn_lpLift hle T (f+g), coeFn_lpLift hle T f,
    coeFn_lpLift hle T g, Lp.coeFn_add (lpLift hle T f) (lpLift hle T g),
    ae_lift hle T (Lp.stronglyMeasurable (f+g))
      ((Lp.stronglyMeasurable f).add (Lp.stronglyMeasurable g)) (Lp.coeFn_add f g)]
    with z hfg hf hg ha he
  rw [hfg, ha, Pi.add_apply, hf, hg]
  exact he

theorem lpLift_smul (hle : ∀ t, ℱ₁ t ≤ ℱ₂ t) (T : ℝ≥0) (a : ℝ)
    (f : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ₁)) :
    lpLift hle T (a • f) = a • lpLift hle T f := by
  apply Lp.ext
  filter_upwards [coeFn_lpLift hle T (a • f), coeFn_lpLift hle T f,
    Lp.coeFn_smul a (lpLift hle T f),
    ae_lift hle T (Lp.stronglyMeasurable (a • f))
      ((Lp.stronglyMeasurable f).const_smul a) (Lp.coeFn_smul a f)] with z hsa hf hs he
  rw [hsa, hs, Pi.smul_apply, hf]
  exact he

theorem norm_lpLift (hle : ∀ t, ℱ₁ t ≤ ℱ₂ t) (T : ℝ≥0)
    (f : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ₁)) : ‖lpLift hle T f‖ = ‖f‖ := by
  rw [lpLift, Lp.norm_toLp, Lp.norm_def]
  congr 1
  change eLpNorm (f : ℝ≥0 × Ω → ℝ) 2 (((timeMeasure_T T).prod μ).trim ℱ₂.predictable_le_prod) = _
  rw [eLpNorm_trim ℱ₂.predictable_le_prod ((Lp.stronglyMeasurable f).mono (predictable_le hle)),
    ← eLpNorm_trim ℱ₁.predictable_le_prod (Lp.stronglyMeasurable f)]
  rfl

def lpLiftLI (hle : ∀ t, ℱ₁ t ≤ ℱ₂ t) (T : ℝ≥0) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ₁) →ₗᵢ[ℝ] Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ₂) where
  toFun := lpLift hle T
  map_add' := lpLift_add hle T
  map_smul' := lpLift_smul hle T
  norm_map' := norm_lpLift hle T

def simpleLift (hle : ∀ t, ℱ₁ t ≤ ℱ₂ t) (V : SimpleProcess ℝ ℱ₁) : SimpleProcess ℝ ℱ₂ where
  valueBot := V.valueBot
  value := V.value
  le_of_mem_support_value := V.le_of_mem_support_value
  measurable_valueBot := V.measurable_valueBot.mono (hle 0) le_rfl
  measurable_value' p _ := (V.measurable_value p).mono (hle p.1) le_rfl
  bounded_valueBot := V.bounded_valueBot
  bounded_value := V.bounded_value

theorem simpleLift_coe (hle : ∀ t, ℱ₁ t ≤ ℱ₂ t) (V : SimpleProcess ℝ ℱ₁) :
    (simpleLift hle V : ℝ≥0 → Ω → ℝ) = V := rfl

variable [IsProbabilityMeasure μ]

def boundedSimpleLift (hle : ∀ t, ℱ₁ t ≤ ℱ₂ t) {T : ℝ≥0}
    (V : TBoundedSP T ℱ₁) : TBoundedSP T ℱ₂ :=
  ⟨simpleLift hle V.val, V.property⟩

theorem lpLift_simpleAssembly (hle : ∀ t, ℱ₁ t ≤ ℱ₂ t) (T : ℝ≥0)
    (V : TBoundedSP T ℱ₁) :
    lpLift hle T (simpleAssembly_T (μ := μ) T ℱ₁ V) =
      simpleAssembly_T (μ := μ) T ℱ₂ (boundedSimpleLift hle V) := by
  have he := ae_lift hle T (Lp.stronglyMeasurable (simpleAssembly_T (μ := μ) T ℱ₁ V))
    V.val.isStronglyPredictable (memLp_uncurry_trim_T (μ := μ) T ℱ₁ V.val).coeFn_toLp
  apply Lp.ext
  filter_upwards [coeFn_lpLift hle T (simpleAssembly_T (μ := μ) T ℱ₁ V), he,
    (memLp_uncurry_trim_T (μ := μ) T ℱ₂ (boundedSimpleLift hle V).val).coeFn_toLp]
    with z hl he hr
  exact hl.trans (he.trans hr.symm)

theorem integral_commutes (hle : ∀ t, ℱ₁ t ≤ ℱ₂ t) {B : ℝ≥0 → Ω → ℝ}
    (hB₁ : BrownianOn ℱ₁ B μ) (hB₂ : BrownianOn ℱ₂ B μ) (T : ℝ≥0)
    (f : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ₁)) :
    itoIntegralCLM_T hB₂ T (lpLift hle T f) = itoIntegralCLM_T hB₁ T f := by
  have he : (fun g => itoIntegralCLM_T hB₂ T (lpLift hle T g)) =
      (fun g => itoIntegralCLM_T hB₁ T g) := by
    apply (simpleAssembly_T_denseRange (μ := μ) T ℱ₁).equalizer
      ((itoIntegralCLM_T hB₂ T).continuous.comp (lpLiftLI hle T).continuous)
      (itoIntegralCLM_T hB₁ T).continuous
    funext V
    change itoIntegralCLM_T hB₂ T (lpLift hle T (simpleAssembly_T T ℱ₁ V)) =
      itoIntegralCLM_T hB₁ T (simpleAssembly_T T ℱ₁ V)
    rw [lpLift_simpleAssembly, itoIntegralCLM_T_simpleAssembly, itoIntegralCLM_T_simpleAssembly]
    rfl
  exact congrFun he f

theorem process_commutes (hle : ∀ t, ℱ₁ t ≤ ℱ₂ t) {B : ℝ≥0 → Ω → ℝ}
    (hB₁ : BrownianOn ℱ₁ B μ) (hB₂ : BrownianOn ℱ₂ B μ) (T t : ℝ≥0)
    (f : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ₁)) :
    CommonProcessGeneral.itoProcessCLM hB₂ T t hB₂.measurable (lpLift hle T f) =
      CommonProcessGeneral.itoProcessCLM hB₁ T t hB₁.measurable f := by
  have he : (fun g => CommonProcessGeneral.itoProcessCLM hB₂ T t hB₂.measurable (lpLift hle T g)) =
      (fun g => CommonProcessGeneral.itoProcessCLM hB₁ T t hB₁.measurable g) := by
    apply (simpleAssembly_T_denseRange (μ := μ) T ℱ₁).equalizer
      ((CommonProcessGeneral.itoProcessCLM hB₂ T t hB₂.measurable).continuous.comp (lpLiftLI hle
            T).continuous)
      (CommonProcessGeneral.itoProcessCLM hB₁ T t hB₁.measurable).continuous
    funext V
    change CommonProcessGeneral.itoProcessCLM hB₂ T t hB₂.measurable
      (lpLift hle T (simpleAssembly_T T ℱ₁ V)) =
        CommonProcessGeneral.itoProcessCLM hB₁ T t hB₁.measurable (simpleAssembly_T T ℱ₁ V)
    rw [lpLift_simpleAssembly, CommonProcessGeneral.itoProcessCLM_simpleAssembly_T,
      CommonProcessGeneral.itoProcessCLM_simpleAssembly_T]
    rfl
  exact congrFun he f

/-- Compatibility with the old natural-filtration integral. -/
theorem integral_natural_eq {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hm : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (f : Lp ℝ 2 (MathFin.ItoIntegralCLM.trimMeasure (μ := μ) T hm)) :
    itoIntegralCLM_T (brownianOn_natural hB hm) T f =
      MathFin.ItoIntegralCLM.itoIntegralCLM hB T hm f := by
  have he := (MathFin.ItoIntegralCLM.simpleAssemblyHorizon_denseRange (μ := μ) T hm).equalizer
    (itoIntegralCLM_T (brownianOn_natural hB hm) T).continuous
    (MathFin.ItoIntegralCLM.itoIntegralCLM hB T hm).continuous
  apply congrFun (he ?_) f
  funext V
  let W : TBoundedSP T (MathFin.ItoIntegralL2.natFiltration hm) := ⟨V.1, V.2⟩
  exact (itoIntegralCLM_T_simpleAssembly (brownianOn_natural hB hm) T W).trans
    (MathFin.ItoIntegralCLM.itoIntegralCLM_simpleAssemblyHorizon hB T hm V).symm


theorem process_natural_eq {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hm : ∀ t, Measurable (B t)) (T t : ℝ≥0)
    (f : Lp ℝ 2 (MathFin.ItoIntegralCLM.trimMeasure (μ := μ) T hm)) :
    CommonProcessGeneral.itoProcessCLM (brownianOn_natural hB hm) T t hm f =
      MathFin.ItoIntegralProcessGeneral.itoProcessCLM hB T t hm f := by
  have he := (MathFin.ItoIntegralCLM.simpleAssemblyHorizon_denseRange (μ := μ) T hm).equalizer
    (CommonProcessGeneral.itoProcessCLM (brownianOn_natural hB hm) T t hm).continuous
    (MathFin.ItoIntegralProcessGeneral.itoProcessCLM hB T t hm).continuous
  apply congrFun (he ?_) f
  funext V
  let W : TBoundedSP T (MathFin.ItoIntegralL2.natFiltration hm) := ⟨V.1, V.2⟩
  exact (CommonProcessGeneral.itoProcessCLM_simpleAssembly_T (brownianOn_natural hB hm) T t hm
        W).trans
    (MathFin.ItoIntegralProcessGeneral.itoProcessCLM_simpleAssemblyHorizon hB T t hm V).symm

end MathFin.FilteredIto.CommonLift
