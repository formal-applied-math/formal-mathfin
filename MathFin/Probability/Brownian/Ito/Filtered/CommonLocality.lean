/-
Copyright (c) 2026 Raphael Coelho, Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CommonProcessIsometry

/-!
# Common Locality

Locality of the common-filtration Ito integral: `F_a`-linearity
(`∫ Z·φ dB = Z·∫ φ dB` for `φ` supported after `a`) and time locality
(`∫ 𝟙_(u,T]·φ dB = ∫ φ dB − (φ●B)_u`). Derived from MathFin by
derive-common-locality.py.

Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Common-filtration extension for Heston, 2026-10-19.

## Main definitions

* `smulAdapted`
* `restrictAfterCLM`
* `afterStepSP`

## Main results

* `itoProcessCLM_eq_zero_of_vanishes_before`
* `itoIntegralCLM_T_eq_itoProcessCLM_of_vanishes_after`
* `itoIntegralCLM_T_restrictAfterCLM`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto
namespace CommonLocality

open MeasureTheory ProbabilityTheory Filter CommonL2 CommonPredictable CommonIntegral
open MathFin.FilteredIto.CommonNoise
open scoped NNReal ENNReal Topology

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ} (hB : IsFilteredPreBrownian B ℱ μ)

/-- Horizon-bounded simple process supported on a single deterministic band. -/
noncomputable def stepSP {T : ℝ≥0} (_hBmeas : ∀ t, Measurable (B t)) {a b : ℝ≥0}
    (hab : a ≤ b) (hbT : b ≤ T) {φ : Ω → ℝ}
    (hφ : Measurable[ℱ a] φ) {M : ℝ} (hφM : ∀ ω, |φ ω| ≤ M) :
    TBoundedSP T ℱ :=
  ⟨{ valueBot := 0
     value := Finsupp.single (a, b) φ
     le_of_mem_support_value := fun p hp ↦ by
       obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
       exact hab
     measurable_valueBot := measurable_const
     measurable_value' := fun p hp ↦ by
       obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
       rw [Finsupp.single_eq_same]; exact hφ
     bounded_valueBot := ⟨0, by simp⟩
     bounded_value := ⟨M, fun p hp ω ↦ by
       obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
       rw [Finsupp.single_eq_same, Real.norm_eq_abs]; exact hφM ω⟩ },
   fun p hp ↦ by
     obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
     exact hbT⟩

lemma itoSimple_stepSP {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t)) {a b : ℝ≥0}
    (hab : a ≤ b) (hbT : b ≤ T) {φ : Ω → ℝ}
    (hφ : Measurable[ℱ a] φ) {M : ℝ} (hφM : ∀ ω, |φ ω| ≤ M) (ω : Ω) :
    itoSimple hBmeas (stepSP hBmeas hab hbT hφ hφM).val ω = φ ω * (B b ω - B a ω) := by
  rw [itoSimple_apply]
  show (Finsupp.single (a, b) φ).sum (fun p v ↦ v ω * (B p.2 ω - B p.1 ω))
      = φ ω * (B b ω - B a ω)
  rw [Finsupp.sum_single_index (by simp)]

lemma itoSimple_sum (hBmeas : ∀ t, Measurable (B t)) {ι' : Type*} (s : Finset ι')
    (V : ι' → SimpleProcess ℝ ℱ) :
    itoSimple hBmeas (∑ i ∈ s, V i) = ∑ i ∈ s, itoSimple hBmeas (V i) := by
  classical
  induction s using Finset.induction with
  | empty => funext ω; simp [itoSimple]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, itoSimple_add, ih]

section MulBdd

variable {α : Type*} {mα : MeasurableSpace α} {ν : Measure α}

theorem memLp_mul_of_bdd {g : α → ℝ} (hg : Measurable g) {C : ℝ} (hgC : ∀ x, |g x| ≤ C)
    (f : Lp ℝ 2 ν) : MemLp (fun x ↦ g x * f x) 2 ν := by
  refine MemLp.mono ((Lp.memLp f).const_mul C)
    (hg.stronglyMeasurable.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right ((hgC x).trans (le_abs_self C)) (abs_nonneg _)

/-- Continuous linear operator multiplying an L² function by a bounded factor. -/
noncomputable def mulBddCLM (ν : Measure α) {g : α → ℝ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, |g x| ≤ C) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (memLp_mul_of_bdd hg hgC f).toLp _
      map_add' := fun f₁ f₂ ↦ by
        refine Lp.ext ?_
        filter_upwards [(memLp_mul_of_bdd hg hgC (f₁ + f₂)).coeFn_toLp,
          Lp.coeFn_add ((memLp_mul_of_bdd hg hgC f₁).toLp (fun x ↦ g x * f₁ x))
            ((memLp_mul_of_bdd hg hgC f₂).toLp (fun x ↦ g x * f₂ x)),
          (memLp_mul_of_bdd hg hgC f₁).coeFn_toLp, (memLp_mul_of_bdd hg hgC f₂).coeFn_toLp,
          Lp.coeFn_add f₁ f₂] with x e0 e1 e2 e3 e4
        simp only [e0, e1, e2, e3, e4, Pi.add_apply]
        ring
      map_smul' := fun c f ↦ by
        refine Lp.ext ?_
        filter_upwards [(memLp_mul_of_bdd hg hgC (c • f)).coeFn_toLp,
          Lp.coeFn_smul c ((memLp_mul_of_bdd hg hgC f).toLp (fun x ↦ g x * f x)),
          (memLp_mul_of_bdd hg hgC f).coeFn_toLp, Lp.coeFn_smul c f] with x e0 e1 e2 e3
        simp only [e0, e1, e2, e3, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        ring }
    |C| (fun f ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [(memLp_mul_of_bdd hg hgC f).coeFn_toLp] with x hx
      rw [hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right ((hgC x).trans (le_abs_self C)) (abs_nonneg _))

theorem coeFn_mulBddCLM (ν : Measure α) {g : α → ℝ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, |g x| ≤ C) (f : Lp ℝ 2 ν) :
    ⇑(mulBddCLM ν hg hgC f) =ᵐ[ν] fun x ↦ g x * f x :=
  (memLp_mul_of_bdd hg hgC f).coeFn_toLp

end MulBdd

/-- Random multiplier switched on strictly after its observation time. -/
noncomputable def afterFactor (a : ℝ≥0) (Z : Ω → ℝ) : ℝ≥0 × Ω → ℝ :=
  fun p ↦ if a < p.1 then Z p.2 else 0

omit mΩ in

lemma abs_afterFactor_le {a : ℝ≥0} {Z : Ω → ℝ} {C : ℝ} (hZb : ∀ ω, |Z ω| ≤ C)
    (p : ℝ≥0 × Ω) : |afterFactor a Z p| ≤ max C 0 := by
  simp only [afterFactor]
  split_ifs with h
  · exact (hZb p.2).trans (le_max_left _ _)
  · simp

lemma measurable_afterFactor {a : ℝ≥0} (_hBmeas : ∀ t, Measurable (B t)) {Z : Ω → ℝ}
    (hZm : Measurable[ℱ a] Z) :
    Measurable[(ℱ).predictable] (afterFactor a Z) := by
  set 𝓕 := ℱ
  intro S hS
  have hIoi : MeasurableSet[𝓕.predictable] (Set.Ioi a ×ˢ (Z ⁻¹' S)) :=
    MeasureTheory.measurableSet_predictable_Ioi_prod (𝓕 := 𝓕) (hZm hS)
  have hoff : MeasurableSet[𝓕.predictable] ((Set.Ioi a ×ˢ (Set.univ : Set Ω))ᶜ) :=
    (MeasureTheory.measurableSet_predictable_Ioi_prod (𝓕 := 𝓕) (i := a)
      MeasurableSet.univ).compl
  by_cases h0 : (0 : ℝ) ∈ S
  · have hset : afterFactor a Z ⁻¹' S
        = Set.Ioi a ×ˢ (Z ⁻¹' S) ∪ (Set.Ioi a ×ˢ (Set.univ : Set Ω))ᶜ := by
      ext p
      simp only [afterFactor, Set.mem_preimage, Set.mem_union, Set.mem_prod, Set.mem_Ioi,
        Set.mem_compl_iff, Set.mem_univ, and_true]
      by_cases h : a < p.1 <;> simp [h, h0]
    rw [hset]
    exact hIoi.union hoff
  · have hset : afterFactor a Z ⁻¹' S = Set.Ioi a ×ˢ (Z ⁻¹' S) := by
      ext p
      simp only [afterFactor, Set.mem_preimage, Set.mem_prod, Set.mem_Ioi]
      by_cases h : a < p.1 <;> simp [h, h0]
    rw [hset]
    exact hIoi

/-- Multiply a predictable kernel by a bounded coefficient after its observation time. -/
noncomputable def smulAdaptedCLM (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ℱ a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) :
    Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ) →L[ℝ]
      Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ) :=
  mulBddCLM (trimMeasureT (μ := μ) T ℱ) (measurable_afterFactor hBmeas hZm)
    (abs_afterFactor_le hZb)

omit [IsProbabilityMeasure μ] in

theorem coeFn_smulAdaptedCLM (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ℱ a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    ⇑(smulAdaptedCLM T a hBmeas Z hZm C hZb φ)
      =ᵐ[trimMeasureT (μ := μ) T ℱ] fun p ↦ afterFactor a Z p * φ p :=
  coeFn_mulBddCLM _ _ _ φ

/-- Predictable kernel multiplied after time a by a bounded adapted coefficient. -/
noncomputable def smulAdapted (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ℱ a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C)
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ) :=
  smulAdaptedCLM T a hBmeas Z hZm C hZb φ

omit [IsProbabilityMeasure μ] in

theorem coeFn_smulAdapted_afterFactor (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ℱ a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    ⇑(smulAdapted T a hBmeas Z hZm C hZb φ)
      =ᵐ[trimMeasureT (μ := μ) T ℱ] fun p ↦ afterFactor a Z p * φ p :=
  coeFn_smulAdaptedCLM T a hBmeas Z hZm C hZb φ

omit [IsProbabilityMeasure μ] in

theorem coeFn_smulAdapted (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ℱ a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ))
    (hφ : ∀ᵐ p ∂(trimMeasureT (μ := μ) T ℱ), p.1 ≤ a → φ p = 0) :
    ⇑(smulAdapted T a hBmeas Z hZm C hZb φ)
      =ᵐ[trimMeasureT (μ := μ) T ℱ] fun p ↦ Z p.2 * φ p := by
  filter_upwards [coeFn_smulAdapted_afterFactor T a hBmeas Z hZm C hZb φ, hφ] with p e1 e2
  rw [e1]
  simp only [afterFactor]
  split_ifs with h
  · rfl
  · rw [e2 (not_lt.mp h), mul_zero, mul_zero]

/-- Continuous linear restriction of a predictable kernel to times strictly after a. -/
noncomputable def restrictAfterCLM (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ) →L[ℝ]
      Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ) :=
  smulAdaptedCLM T a hBmeas (fun _ ↦ (1 : ℝ)) measurable_const 1 (fun _ ↦ abs_one.le)

omit [IsProbabilityMeasure μ] in

theorem restrictAfterCLM_eq (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ))
    (hφ : ∀ᵐ p ∂(trimMeasureT (μ := μ) T ℱ), p.1 ≤ a → φ p = 0) :
    restrictAfterCLM T a hBmeas φ = φ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_smulAdaptedCLM T a hBmeas (fun _ ↦ (1 : ℝ)) measurable_const 1
    (fun _ ↦ abs_one.le) φ, hφ] with p e1 e2
  rw [show (restrictAfterCLM T a hBmeas φ : ℝ≥0 × Ω → ℝ) p
      = afterFactor a (fun _ ↦ (1 : ℝ)) p * (φ : ℝ≥0 × Ω → ℝ) p from e1]
  simp only [afterFactor]
  split_ifs with h
  · rw [one_mul]
  · rw [zero_mul, e2 (not_lt.mp h)]

omit [IsProbabilityMeasure μ] in

theorem coeFn_restrictAfterCLM (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    ⇑(restrictAfterCLM T a hBmeas φ) =ᵐ[trimMeasureT (μ := μ) T ℱ]
      fun p ↦ if a < p.1 then φ p else 0 := by
  filter_upwards [coeFn_smulAdaptedCLM T a hBmeas (fun _ ↦ (1 : ℝ)) measurable_const 1
    (fun _ ↦ abs_one.le) φ] with p hp
  rw [show ⇑(restrictAfterCLM T a hBmeas φ) p
      = afterFactor a (fun _ ↦ (1 : ℝ)) p * (φ : ℝ≥0 × Ω → ℝ) p from hp]
  simp only [afterFactor]
  split_ifs <;> simp

lemma ae_fst_ne_zero (T : ℝ≥0) (_hBmeas : ∀ t, Measurable (B t)) :
    ∀ᵐ p ∂(trimMeasureT (μ := μ) T ℱ), p.1 ≠ 0 := by
  set 𝓕 := ℱ
  have hbot : MeasurableSet[𝓕.predictable] (({(⊥ : ℝ≥0)} : Set ℝ≥0) ×ˢ (Set.univ : Set Ω)) :=
    MeasureTheory.measurableSet_predictable_singleton_bot_prod (𝓕 := 𝓕) MeasurableSet.univ
  have htime : timeMeasureT T ({(⊥ : ℝ≥0)} : Set ℝ≥0) = 0 :=
    nonpos_iff_eq_zero.mp
      ((Measure.restrict_apply_le _ _).trans
        (CommonL2.timeMeasure_singleton (⊥ : ℝ≥0)).le)
  have hnull : (trimMeasureT (μ := μ) T ℱ)
      (({(⊥ : ℝ≥0)} : Set ℝ≥0) ×ˢ (Set.univ : Set Ω)) = 0 := by
    unfold trimMeasureT
    rw [MeasureTheory.trim_measurableSet_eq _ hbot, Measure.prod_prod, htime, zero_mul]
  have hset : {p : ℝ≥0 × Ω | ¬ p.1 ≠ 0}
      = ({(⊥ : ℝ≥0)} : Set ℝ≥0) ×ˢ (Set.univ : Set Ω) := by
    ext p
    simp
  rw [ae_iff, hset]
  exact hnull

private lemma coe_simpleProcess_sum {ι' : Type*} (_hBmeas : ∀ t, Measurable (B t))
    (s : Finset ι') (W : ι' → SimpleProcess ℝ (ℱ))
    (t : ℝ≥0) (ω : Ω) : ⇑(∑ i ∈ s, W i) t ω = ∑ i ∈ s, ⇑(W i) t ω := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, SimpleProcess.coe_add]
      simp [ih]

lemma coe_stepSP {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t)) {a' b : ℝ≥0}
    (hab : a' ≤ b) (hbT : b ≤ T) {ψ : Ω → ℝ}
    (hψm : Measurable[ℱ a'] ψ) {M : ℝ} (hψM : ∀ ω, |ψ ω| ≤ M)
    (t : ℝ≥0) (ω : Ω) :
    ⇑(stepSP hBmeas hab hbT hψm hψM : TBoundedSP T ℱ).val t ω
      = (Set.Ioc a' b).indicator (fun _ ↦ ψ ω) t := by
  rw [SimpleProcess.apply_eq]
  have hbot : ({(⊥ : ℝ≥0)} : Set ℝ≥0).indicator
      (fun _ ↦ (stepSP hBmeas hab hbT hψm hψM :
        TBoundedSP T ℱ).val.valueBot ω) t = 0 := by
    simp [stepSP]
  rw [hbot, zero_add]
  show (Finsupp.single (a', b) ψ).sum
      (fun p v ↦ (Set.Ioc p.1 p.2).indicator (fun _ ↦ v ω) t) = _
  rw [Finsupp.sum_single_index (by simp)]

/-- Simple process after truncating its bands and multiplying by an adapted coefficient. -/
noncomputable def afterStepSP (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ℱ a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (V : TBoundedSP T ℱ) : TBoundedSP T ℱ :=
  ∑ p ∈ V.val.value.support.attach,
    if h : a ⊔ p.val.1 ≤ p.val.2 then
      stepSP hBmeas h (V.property p.val p.property)
        (φ := fun ω ↦ Z ω * V.val.value p.val ω)
        ((hZm.mono ((ℱ).mono le_sup_left) le_rfl).mul
          ((V.val.measurable_value p.val).mono
            ((ℱ).mono le_sup_right) le_rfl))
        (M := C * V.val.valueBound)
        (fun ω ↦ by
          rw [abs_mul]
          exact mul_le_mul (hZb ω)
            (by rw [← Real.norm_eq_abs]; exact V.val.value_le_valueBound p.val ω)
            (abs_nonneg _) ((abs_nonneg (Z ω)).trans (hZb ω)))
    else 0

private lemma coe_afterStepSP (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ℱ a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (V : TBoundedSP T ℱ) {t : ℝ≥0} (ht : t ≠ 0) (ω : Ω) :
    ⇑(afterStepSP T a hBmeas Z hZm C hZb V).val t ω
      = afterFactor a Z (t, ω) * ⇑V.val t ω := by
  have htbot : t ∉ ({(⊥ : ℝ≥0)} : Set ℝ≥0) := by
    simp only [Set.mem_singleton_iff, NNReal.bot_eq_zero]
    exact ht
  have hV : ⇑V.val t ω
      = ∑ p ∈ V.val.value.support,
          (Set.Ioc p.1 p.2).indicator (fun _ ↦ V.val.value p ω) t := by
    rw [SimpleProcess.apply_eq, Set.indicator_of_notMem htbot, zero_add, Finsupp.sum]
  rw [afterStepSP, AddSubmonoidClass.coe_finsetSum, coe_simpleProcess_sum hBmeas, hV,
        Finset.mul_sum,
    ← Finset.sum_attach V.val.value.support
      (fun q ↦ afterFactor a Z (t, ω) * (Set.Ioc q.1 q.2).indicator
        (fun _ ↦ V.val.value q ω) t)]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  by_cases hle : a ⊔ p.val.1 ≤ p.val.2
  · rw [dite_eq_left hle, coe_stepSP hBmeas]
    simp only [afterFactor]
    by_cases hat : a < t
    · have hmem : t ∈ Set.Ioc (a ⊔ p.val.1) p.val.2 ↔ t ∈ Set.Ioc p.val.1 p.val.2 := by
        simp only [Set.mem_Ioc, sup_lt_iff]
        exact ⟨fun h ↦ ⟨h.1.2, h.2⟩, fun h ↦ ⟨⟨hat, h.1⟩, h.2⟩⟩
      by_cases hin : t ∈ Set.Ioc p.val.1 p.val.2
      · rw [Set.indicator_of_mem (hmem.mpr hin), Set.indicator_of_mem hin, ite_eq_left hat]
      · rw [Set.indicator_of_notMem (fun hc ↦ hin (hmem.mp hc)), Set.indicator_of_notMem hin,
          mul_zero]
    · rw [if_neg hat, zero_mul]
      exact Set.indicator_of_notMem (fun (hc : t ∈ Set.Ioc (a ⊔ p.val.1) p.val.2) ↦ hat
            (lt_of_le_of_lt le_sup_left hc.1)) _
  · rw [dite_eq_right hle]
    have hzero : ⇑((0 : TBoundedSP T ℱ).val) t ω = 0 := by simp
    rw [hzero, eq_comm]
    simp only [afterFactor]
    by_cases hat : a < t
    · rw [Set.indicator_of_notMem (fun (hc : t ∈ Set.Ioc p.val.1 p.val.2) ↦ hle (sup_le
          (hat.le.trans hc.2) (hc.1.le.trans hc.2))),
        mul_zero]
    · rw [if_neg hat, zero_mul]

private lemma simpleAssembly_T_afterStepSP (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ℱ a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (V : TBoundedSP T ℱ) :
    simpleAssemblyT (μ := μ) T ℱ (afterStepSP T a hBmeas Z hZm C hZb V)
      = smulAdaptedCLM T a hBmeas Z hZm C hZb (simpleAssemblyT (μ := μ) T ℱ V) := by
  refine Lp.ext ?_
  filter_upwards [(memLp_uncurry_trim_T (μ := μ) T ℱ
      (afterStepSP T a hBmeas Z hZm C hZb V).val).coeFn_toLp,
    coeFn_smulAdaptedCLM T a hBmeas Z hZm C hZb (simpleAssemblyT (μ := μ) T ℱ V),
    (memLp_uncurry_trim_T (μ := μ) T ℱ V.val).coeFn_toLp,
    ae_fst_ne_zero (μ := μ) T hBmeas] with p e1 e2 e3 hp
  rw [show (simpleAssemblyT (μ := μ) T ℱ (afterStepSP T a hBmeas Z hZm C hZb V) :
        ℝ≥0 × Ω → ℝ) p
      = Function.uncurry ⇑(afterStepSP T a hBmeas Z hZm C hZb V).val p from e1, e2,
    show (simpleAssemblyT (μ := μ) T ℱ V : ℝ≥0 × Ω → ℝ) p
      = Function.uncurry ⇑V.val p from e3]
  obtain ⟨t, ω⟩ := p
  exact coe_afterStepSP T a hBmeas Z hZm C hZb V hp ω

private lemma itoSimple_afterStepSP_eq (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ℱ a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (V : TBoundedSP T ℱ) (ω : Ω) :
    CommonL2.itoSimple hBmeas (afterStepSP T a hBmeas Z hZm C hZb V).val ω
      = ∑ p ∈ V.val.value.support.attach,
          if _h : a ⊔ p.val.1 ≤ p.val.2 then
            Z ω * V.val.value p.val ω * (B p.val.2 ω - B (a ⊔ p.val.1) ω) else 0 := by
  rw [afterStepSP, AddSubmonoidClass.coe_finsetSum, itoSimple_sum,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  by_cases hle : a ⊔ p.val.1 ≤ p.val.2
  · rw [dite_eq_left hle, dite_eq_left hle, itoSimple_stepSP]
  · rw [dite_eq_right hle, dite_eq_right hle]
    simp [CommonL2.itoSimple]

private lemma itoSimple_afterStepSP_smul (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ℱ a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (V : TBoundedSP T ℱ) (ω : Ω) :
    CommonL2.itoSimple hBmeas (afterStepSP T a hBmeas Z hZm C hZb V).val ω
      = Z ω * CommonL2.itoSimple hBmeas
          (afterStepSP T a hBmeas (fun _ ↦ (1 : ℝ)) measurable_const 1
            (fun _ ↦ abs_one.le) V).val ω := by
  rw [itoSimple_afterStepSP_eq, itoSimple_afterStepSP_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  by_cases hle : a ⊔ p.val.1 ≤ p.val.2
  · rw [dite_eq_left hle, dite_eq_left hle]; ring
  · rw [dite_eq_right hle, dite_eq_right hle, mul_zero]

theorem itoIntegralCLM_T_smulAdapted (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ℱ a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C)
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ))
    (hφ : ∀ᵐ p ∂(trimMeasureT (μ := μ) T ℱ), p.1 ≤ a → φ p = 0) :
    ⇑(itoIntegralCLMT hB T (smulAdapted T a hBmeas Z hZm C hZb φ))
      =ᵐ[μ] fun ω ↦ Z ω * itoIntegralCLMT hB T φ ω := by

  have hZmΩ : Measurable Z := hZm.mono ((ℱ).le a) le_rfl

  have hEq : (itoIntegralCLMT hB T).comp (smulAdaptedCLM T a hBmeas Z hZm C hZb)
      = (mulBddCLM μ hZmΩ hZb).comp
          ((itoIntegralCLMT hB T).comp (restrictAfterCLM T a hBmeas)) := by
    refine ContinuousLinearMap.ext fun ψ ↦ ?_
    refine congrFun (DenseRange.equalizer (simpleAssembly_T_denseRange (μ := μ) T ℱ)
      (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
      (funext fun V ↦ ?_)) ψ
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]

    set U := afterStepSP T a hBmeas (fun _ ↦ (1 : ℝ)) measurable_const 1 (fun _ ↦ abs_one.le) V
    rw [← simpleAssembly_T_afterStepSP T a hBmeas Z hZm C hZb V,
      show restrictAfterCLM T a hBmeas (simpleAssemblyT (μ := μ) T ℱ V)
          = simpleAssemblyT (μ := μ) T ℱ U from
        (simpleAssembly_T_afterStepSP T a hBmeas (fun _ ↦ (1 : ℝ)) measurable_const 1
          (fun _ ↦ abs_one.le) V).symm,
      itoIntegralCLM_T_simpleAssembly, itoIntegralCLM_T_simpleAssembly]
    refine Lp.ext ?_
    filter_upwards [(CommonL2.memLp_itoSimple hB hBmeas
        (afterStepSP T a hBmeas Z hZm C hZb V).val).coeFn_toLp,
      coeFn_mulBddCLM μ hZmΩ hZb (CommonL2.itoSimpleLp hB hBmeas U.val),
      (CommonL2.memLp_itoSimple hB hBmeas U.val).coeFn_toLp] with ω f1 f2 f3
    rw [show (CommonL2.itoSimpleLp hB hBmeas
          (afterStepSP T a hBmeas Z hZm C hZb V).val : Ω → ℝ) ω
        = CommonL2.itoSimple hBmeas (afterStepSP T a hBmeas Z hZm C hZb V).val ω from f1,
      f2, show (CommonL2.itoSimpleLp hB hBmeas U.val : Ω → ℝ) ω
        = CommonL2.itoSimple hBmeas U.val ω from f3]
    exact itoSimple_afterStepSP_smul T a hBmeas Z hZm C hZb V ω
  have h1 := DFunLike.congr_fun hEq φ
  simp only [ContinuousLinearMap.comp_apply, restrictAfterCLM_eq T a hBmeas φ hφ] at h1
  rw [show smulAdapted T a hBmeas Z hZm C hZb φ
      = smulAdaptedCLM T a hBmeas Z hZm C hZb φ from rfl, h1]
  exact coeFn_mulBddCLM μ hZmΩ hZb _

theorem itoIntegralCLM_T_smulAdapted_of_memLp (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ℱ a] Z)
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ))
    (hφ : ∀ᵐ p ∂(trimMeasureT (μ := μ) T ℱ), p.1 ≤ a → φ p = 0)
    (hZφ : MemLp (fun p : ℝ≥0 × Ω ↦ Z p.2 * φ p) 2 (trimMeasureT (μ := μ) T ℱ)) :
    ⇑(itoIntegralCLMT hB T (hZφ.toLp _))
      =ᵐ[μ] fun ω ↦ Z ω * itoIntegralCLMT hB T φ ω := by
  set ψ := hZφ.toLp (fun p : ℝ≥0 × Ω ↦ Z p.2 * φ p)
  have hψ : ∀ᵐ p ∂(trimMeasureT (μ := μ) T ℱ), p.1 ≤ a → ψ p = 0 := by
    filter_upwards [hZφ.coeFn_toLp, hφ] with p e1 e2 h
    rw [show (ψ : ℝ≥0 × Ω → ℝ) p = Z p.2 * (φ : ℝ≥0 × Ω → ℝ) p from e1, e2 h, mul_zero]
  have key : ∀ M : ℕ, ∀ᵐ ω ∂μ, |Z ω| ≤ (M : ℝ) →
      (itoIntegralCLMT hB T ψ) ω = Z ω * (itoIntegralCLMT hB T φ) ω := by
    intro M
    have hAm : MeasurableSet[ℱ a] {ω | |Z ω| ≤ (M : ℝ)} := by
      rw [show {ω | |Z ω| ≤ (M : ℝ)} = Z ⁻¹' (Set.Icc (-(M : ℝ)) (M : ℝ)) from by
        ext ω; simp [abs_le]]
      exact hZm measurableSet_Icc
    have hg1m : Measurable[ℱ a]
        (Set.indicator {ω | |Z ω| ≤ (M : ℝ)} (fun _ ↦ (1 : ℝ))) := measurable_const.indicator hAm
    have hg1b (ω : Ω) : |Set.indicator {ω | |Z ω| ≤ (M : ℝ)} (fun _ ↦ (1 : ℝ)) ω| ≤ 1 := by
      by_cases hm : ω ∈ {ω | |Z ω| ≤ (M : ℝ)}
      · simp [Set.indicator_of_mem hm]
      · simp [Set.indicator_of_notMem hm]
    have hgZm : Measurable[ℱ a]
        (Set.indicator {ω | |Z ω| ≤ (M : ℝ)} Z) := hZm.indicator hAm
    have hgZb (ω : Ω) : |Set.indicator {ω | |Z ω| ≤ (M : ℝ)} Z ω| ≤ (M : ℝ) := by
      by_cases hm : ω ∈ {ω | |Z ω| ≤ (M : ℝ)}
      · rw [Set.indicator_of_mem hm]; exact hm
      · simp [Set.indicator_of_notMem hm]
    have E1 := itoIntegralCLM_T_smulAdapted hB T a hBmeas _ hg1m 1 hg1b ψ hψ
    have E2 := itoIntegralCLM_T_smulAdapted hB T a hBmeas _ hgZm (M : ℝ) hgZb φ hφ
    have hsame : smulAdapted T a hBmeas _ hg1m 1 hg1b ψ
        = smulAdapted T a hBmeas _ hgZm (M : ℝ) hgZb φ := by
      refine Lp.ext ?_
      filter_upwards [coeFn_smulAdapted_afterFactor T a hBmeas _ hg1m 1 hg1b ψ,
        coeFn_smulAdapted_afterFactor T a hBmeas _ hgZm (M : ℝ) hgZb φ,
        hZφ.coeFn_toLp] with p f1 f2 f3
      rw [f1, f2, show (ψ : ℝ≥0 × Ω → ℝ) p = Z p.2 * (φ : ℝ≥0 × Ω → ℝ) p from f3]
      simp only [afterFactor]
      split_ifs with h
      · by_cases hm : p.2 ∈ {ω | |Z ω| ≤ (M : ℝ)}
        · simp [Set.indicator_of_mem hm]
        · simp [Set.indicator_of_notMem hm]
      · rw [zero_mul, zero_mul]
    rw [hsame] at E1
    filter_upwards [E1, E2] with ω h1 h2 hω
    have hmem : ω ∈ {ω | |Z ω| ≤ (M : ℝ)} := hω
    have h3 := h1.symm.trans h2
    rwa [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, one_mul] at h3
  filter_upwards [ae_all_iff.mpr key] with ω hω
  obtain ⟨M, hM⟩ := exists_nat_ge |Z ω|
  exact hω M hM

theorem itoIntegralCLM_T_smul_of_memLp (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ℱ a] Z)
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ))
    (hφ : ∀ᵐ p ∂(trimMeasureT (μ := μ) T ℱ), p.1 ≤ a → φ p = 0)
    (hZI : MemLp (fun ω ↦ Z ω * itoIntegralCLMT hB T φ ω) 2 μ) :
    ∃ ψ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ),
      (⇑ψ =ᵐ[trimMeasureT (μ := μ) T ℱ] fun p ↦ Z p.2 * φ p) ∧
      ⇑(itoIntegralCLMT hB T ψ)
        =ᵐ[μ] fun ω ↦ Z ω * itoIntegralCLMT hB T φ ω := by

  have hAm (M : ℕ) : MeasurableSet[ℱ a]
      {ω | |Z ω| ≤ (M : ℝ)} := by
    rw [show {ω | |Z ω| ≤ (M : ℝ)} = Z ⁻¹' (Set.Icc (-(M : ℝ)) (M : ℝ)) from by
      ext ω; simp [abs_le]]
    exact hZm measurableSet_Icc
  have hZMm (M : ℕ) : Measurable[ℱ a]
      (Set.indicator {ω | |Z ω| ≤ (M : ℝ)} Z) := hZm.indicator (hAm M)
  have hZMb (M : ℕ) (ω : Ω) : |Set.indicator {ω | |Z ω| ≤ (M : ℝ)} Z ω| ≤ (M : ℝ) := by
    by_cases hm : ω ∈ {ω | |Z ω| ≤ (M : ℝ)}
    · rw [Set.indicator_of_mem hm]; exact hm
    · simp [Set.indicator_of_notMem hm]

  have hbound (M : ℕ) :
      ‖smulAdapted T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ‖ ≤ ‖hZI.toLp _‖ := by
    rw [← itoIntegralCLM_T_norm hB T (smulAdapted T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ)]
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [itoIntegralCLM_T_smulAdapted hB T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ hφ,
      hZI.coeFn_toLp] with ω h1 h2
    rw [h1, h2, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    by_cases hm : ω ∈ {ω | |Z ω| ≤ (M : ℝ)}
    · rw [Set.indicator_of_mem hm]
    · rw [Set.indicator_of_notMem hm, abs_zero]; exact abs_nonneg _

  have hZφ : MemLp (fun p : ℝ≥0 × Ω ↦ Z p.2 * φ p) 2 (trimMeasureT (μ := μ) T ℱ) := by
    have hmeas : AEStronglyMeasurable[(ℱ).predictable]
        (fun p : ℝ≥0 × Ω ↦ Z p.2 * φ p) (trimMeasureT (μ := μ) T ℱ) := by
      refine AEStronglyMeasurable.congr
        ((measurable_afterFactor hBmeas hZm).stronglyMeasurable.aestronglyMeasurable.mul
          (Lp.aestronglyMeasurable φ)) ?_
      filter_upwards [hφ] with p hp
      simp only [Pi.mul_apply, afterFactor]
      split_ifs with hc
      · rfl
      · rw [hp (not_lt.mp hc), mul_zero, mul_zero]
    have hlim : ∀ᵐ p ∂(trimMeasureT (μ := μ) T ℱ),
        Tendsto (fun M : ℕ ↦
            (smulAdapted T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ : ℝ≥0 × Ω → ℝ) p)
          atTop (𝓝 (Z p.2 * φ p)) := by
      filter_upwards [ae_all_iff.mpr (fun M : ℕ ↦
        coeFn_smulAdapted_afterFactor T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ), hφ] with p hall hp
      rcases le_or_gt p.1 a with hle | hlt
      · have hz (M : ℕ) :
            (smulAdapted T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ : ℝ≥0 × Ω → ℝ) p = 0 := by
          rw [hall M]
          simp only [afterFactor, ite_eq_right (not_lt.mpr hle), zero_mul]
        simp only [hz, hp hle, mul_zero]
        exact tendsto_const_nhds
      · refine Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [eventually_ge_atTop ⌈|Z p.2|⌉₊] with M hM
        have hmem : p.2 ∈ {ω | |Z ω| ≤ (M : ℝ)} :=
          (Nat.le_ceil |Z p.2|).trans (Nat.cast_le.mpr hM)
        rw [hall M]
        simp only [afterFactor, ite_eq_left hlt, Set.indicator_of_mem hmem]
    have hle : atTop.liminf (fun M : ℕ ↦ eLpNorm
        (⇑(smulAdapted T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ)) 2
          (trimMeasureT (μ := μ) T ℱ))
        ≤ ENNReal.ofReal ‖hZI.toLp (fun ω ↦ Z ω * itoIntegralCLMT hB T φ ω)‖ := by
      refine liminf_le_of_frequently_le' (Filter.Frequently.of_forall fun M ↦ ?_)
      rw [show eLpNorm (⇑(smulAdapted T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ)) 2
            (trimMeasureT (μ := μ) T ℱ)
          = ENNReal.ofReal ‖smulAdapted T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ‖ from by
        rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]]
      exact ENNReal.ofReal_le_ofReal (hbound M)
    apply memLp_iff.mpr
    exact lt_of_le_of_lt ((MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun M : ℕ ↦ Lp.aestronglyMeasurable
        (smulAdapted T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ)) _ hmeas hlim).trans hle)
      ENNReal.ofReal_lt_top
  exact ⟨hZφ.toLp _, hZφ.coeFn_toLp,
    itoIntegralCLM_T_smulAdapted_of_memLp hB T a hBmeas Z hZm φ hφ hZφ⟩

section TimeLocality

open CommonProcessGeneral

omit [IsProbabilityMeasure μ] in

private lemma measurableSet_timeBand (u : ℝ≥0) (_hBmeas : ∀ t, Measurable (B t)) :
    MeasurableSet[(ℱ).predictable]
      (Set.Ioc 0 u ×ˢ (Set.univ : Set Ω)) :=
  MeasureTheory.measurableSet_predictable_Ioc_prod
    (𝓕 := ℱ) 0 u MeasurableSet.univ

theorem itoProcessCLM_eq_zero_of_vanishes_before (T u : ℝ≥0) (huT : u ≤ T)
    (hBmeas : ∀ t, Measurable (B t)) (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ))
    (hφ : ∀ᵐ p ∂(trimMeasureT (μ := μ) T ℱ), p.1 ≤ u → φ p = 0) :
    itoProcessCLM hB T u hBmeas φ = 0 := by
  have hzero : ∫ z in (Set.Ioc 0 u ×ˢ (Set.univ : Set Ω)), (φ z) ^ 2
      ∂(trimMeasureT (μ := μ) T ℱ) = 0 := by
    have hae : ∀ᵐ z ∂((trimMeasureT (μ := μ) T ℱ).restrict
        (Set.Ioc 0 u ×ˢ (Set.univ : Set Ω))), (φ z) ^ 2 = 0 := by
      rw [ae_restrict_iff' (measurableSet_timeBand u hBmeas)]
      filter_upwards [hφ] with z hz hzmem
      rw [hz hzmem.1.2]
      ring
    rw [integral_congr_ae hae, integral_zero]
  refine norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp ?_)
  rw [itoProcessCLM_norm_sq hB huT hBmeas φ, hzero]

theorem itoIntegralCLM_T_eq_itoProcessCLM_of_vanishes_after (T u : ℝ≥0) (huT : u ≤ T)
    (hBmeas : ∀ t, Measurable (B t)) (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ))
    (hφ : ∀ᵐ p ∂(trimMeasureT (μ := μ) T ℱ), u < p.1 → φ p = 0) :
    itoIntegralCLMT hB T φ = itoProcessCLM hB T u hBmeas φ := by
  have : Fact ((ℱ u : MeasurableSpace Ω) ≤ mΩ) :=
    ⟨(ℱ).le u⟩
  set X := itoIntegralCLMT hB T φ with hX

  have hband : ∫ z in (Set.Ioc 0 u ×ˢ (Set.univ : Set Ω)), (φ z) ^ 2
      ∂(trimMeasureT (μ := μ) T ℱ)
      = ∫ z, (φ z) ^ 2 ∂(trimMeasureT (μ := μ) T ℱ) := by
    refine setIntegral_eq_integral_of_ae_compl_eq_zero ?_
    filter_upwards [hφ, ae_fst_mem_Ioc_trimMeasure_T (μ := μ) T ℱ] with z hz hzT hznot
    rw [hz (by by_contra hc; exact hznot ⟨⟨hzT.1, not_lt.mp hc⟩, Set.mem_univ _⟩)]
    ring
  have hnorm : ‖(condExpL2 ℝ ℝ ((ℱ).le u) X : Lp ℝ 2 μ)‖ = ‖X‖ := by
    have hsq : ‖itoProcessCLM hB T u hBmeas φ‖ ^ 2 = ‖X‖ ^ 2 := by
      rw [itoProcessCLM_norm_sq hB huT hBmeas φ, hband, hX, itoIntegralCLM_T_norm hB T φ,
        CommonL2.lp_two_norm_sq φ]
    rw [← itoProcessCLM_eq_condExpL2 hB T u hBmeas φ]
    have hs := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hs
  rw [itoProcessCLM_eq_condExpL2 hB T u hBmeas φ]
  have hcoe : ((condExpL2 ℝ ℝ ((ℱ).le u) X : Lp ℝ 2 μ))
      = (lpMeas ℝ ℝ (ℱ u) 2 μ).starProjection X := rfl
  rw [hcoe] at hnorm ⊢
  exact (Submodule.starProjection_eq_self_iff.mpr
    ((Submodule.mem_iff_norm_starProjection _ X).mpr hnorm)).symm

theorem itoIntegralCLM_T_restrictAfterCLM (T u : ℝ≥0) (huT : u ≤ T)
    (hBmeas : ∀ t, Measurable (B t)) (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    itoIntegralCLMT hB T (restrictAfterCLM T u hBmeas φ)
      = itoIntegralCLMT hB T φ - itoProcessCLM hB T u hBmeas φ := by
  set R := restrictAfterCLM T u hBmeas φ
  have hafter : ∀ᵐ p ∂(trimMeasureT (μ := μ) T ℱ), p.1 ≤ u → R p = 0 := by
    filter_upwards [coeFn_restrictAfterCLM T u hBmeas φ] with p hp hpu
    rw [hp, ite_eq_right (not_lt.mpr hpu)]
  have hbefore : ∀ᵐ p ∂(trimMeasureT (μ := μ) T ℱ), u < p.1 → (φ - R) p = 0 := by
    filter_upwards [coeFn_restrictAfterCLM T u hBmeas φ, Lp.coeFn_sub φ R] with p hp hsub hpu
    rw [hsub, Pi.sub_apply, hp, ite_eq_left hpu, sub_self]
  have hkey : itoIntegralCLMT hB T (φ - R) = itoProcessCLM hB T u hBmeas φ := by
    rw [itoIntegralCLM_T_eq_itoProcessCLM_of_vanishes_after hB T u huT hBmeas (φ - R) hbefore,
      map_sub, itoProcessCLM_eq_zero_of_vanishes_before hB T u huT hBmeas R hafter, sub_zero]
  rw [← hkey, map_sub]
  abel

end TimeLocality

end CommonLocality
end MathFin.FilteredIto
