/-
Copyright (c) 2026 Raphael Coelho, Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.ItoIntegralCLM

/-!
# Common Predictable

Predictable L2 density for an arbitrary common filtration. These are
measure-theoretic results: no Brownian or stochastic-calculus hypothesis occurs.
Derived from the pinned local ItoIntegralCLM by derive-common-predictable.py.

Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Adapted to an arbitrary filtration for this Heston project, 2026-10-18.

## Main definitions

* `TBoundedSP`
* `simpleAssembly_T`
* `iocSP_T`

## Main results

* `uncurry_iocSP_T_eq`
* `setIntegral_eq_setIntegral_inter_supp`
* `simpleAssembly_T_denseRange`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto.CommonPredictable
open MeasureTheory ProbabilityTheory Filter
open MathFin
open scoped NNReal ENNReal InnerProductSpace
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def timeMeasure_T (T : ℝ≥0) : Measure ℝ≥0 :=
  ItoIntegralL2.timeMeasure.restrict (Set.Ioc 0 T)

instance (T : ℝ≥0) : IsFiniteMeasure (timeMeasure_T T) := by
  refine ⟨?_⟩
  rw [timeMeasure_T, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    ItoIntegralL2.timeMeasure_Ioc]
  exact ENNReal.ofReal_lt_top

def trimMeasure_T (T : ℝ≥0) (ℱ : Filtration ℝ≥0 mΩ) :=
  ((timeMeasure_T T).prod μ).trim ℱ.predictable_le_prod

instance (T : ℝ≥0) (ℱ : Filtration ℝ≥0 mΩ) :
    IsFiniteMeasure (trimMeasure_T (μ := μ) T ℱ) := by
  unfold trimMeasure_T
  infer_instance

lemma memLp_uncurry_trim_T (T : ℝ≥0) (ℱ : Filtration ℝ≥0 mΩ)
    (V : SimpleProcess ℝ ℱ) :
    MemLp (Function.uncurry ⇑V) 2 (trimMeasure_T (μ := μ) T ℱ) := by
  obtain ⟨C, hC⟩ := V.coe_bounded
  exact MemLp.of_bound V.isStronglyPredictable.aestronglyMeasurable C
    (Eventually.of_forall fun z => hC z.1 z.2)

lemma uncurry_coe_add (ℱ : Filtration ℝ≥0 mΩ) (V W : SimpleProcess ℝ ℱ) :
    Function.uncurry ⇑(V + W) = Function.uncurry ⇑V + Function.uncurry ⇑W := by
  rw [SimpleProcess.coe_add]; rfl

lemma uncurry_coe_smul (ℱ : Filtration ℝ≥0 mΩ) (c : ℝ) (V : SimpleProcess ℝ ℱ) :
    Function.uncurry ⇑(c • V) = c • Function.uncurry ⇑V := by
  rw [SimpleProcess.coe_smul]; rfl

def predictableRect (ℱ : Filtration ℝ≥0 mΩ) :
    Set (Set (ℝ≥0 × Ω)) :=
  ℱ.predictableRectangles

lemma isPiSystem_predictableRect (ℱ : Filtration ℝ≥0 mΩ) :
    IsPiSystem (predictableRect (mΩ := mΩ) ℱ) :=
  (MeasureTheory.Filtration.isSetSemiring_predictableRectangles _).isPiSystem

theorem generateFrom_predictableRect (ℱ : Filtration ℝ≥0 mΩ) :
    MeasurableSpace.generateFrom (predictableRect (mΩ := mΩ) ℱ) =
      ℱ.predictable := by
  let 𝓕 := ℱ
  apply le_antisymm
  ·
    apply MeasurableSpace.generateFrom_le
    rintro S (⟨F₀, hF₀, rfl⟩ | ⟨a, b, _hab, F, hF, rfl⟩)
    ·
      exact MeasureTheory.measurableSet_predictable_singleton_bot_prod (𝓕 := 𝓕) hF₀
    · exact MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓕) a b hF
  ·
    apply MeasureTheory.measurableSpace_le_predictable_of_measurableSet

    · intro A hA
      exact MeasurableSpace.measurableSet_generateFrom
        (MeasureTheory.Filtration.singletonBot_prod_mem_predictableRectangles _ hA)

    · intro i A hA
      obtain ⟨seq, _hmono, htends⟩ :=
        Filter.exists_seq_monotone_tendsto_atTop_atTop ℝ≥0
      have h_Ioi : (Set.Ioi i : Set ℝ≥0) = ⋃ n : ℕ, Set.Ioc i (seq n) := by
        ext s
        simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ioc]
        refine ⟨fun his ↦ ?_, fun ⟨_, h, _⟩ ↦ h⟩
        rw [Filter.tendsto_atTop_atTop] at htends
        obtain ⟨n, hn⟩ := htends s
        exact ⟨n, his, hn n le_rfl⟩
      rw [h_Ioi, Set.iUnion_prod_const]
      exact MeasurableSet.iUnion fun n ↦ MeasurableSpace.measurableSet_generateFrom
        (MeasureTheory.Filtration.Ioc_prod_mem_predictableRectangles _ i (seq n) hA)

lemma trimMeasure_T_eq_restrict (T : ℝ≥0) (ℱ : Filtration ℝ≥0 mΩ) :
    trimMeasure_T (μ := μ) T ℱ =
      ((ItoIntegralL2.timeMeasure.prod μ).trim
        ℱ.predictable_le_prod).restrict
        (Set.Ioc 0 T ×ˢ Set.univ) := by
  let 𝓕 := ℱ
  show ((timeMeasure_T T).prod μ).trim 𝓕.predictable_le_prod = _
  unfold timeMeasure_T
  rw [Measure.restrict_prod_eq_prod_univ,
      ← MeasureTheory.restrict_trim 𝓕.predictable_le_prod _
        (MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓕) 0 T MeasurableSet.univ)]

lemma ae_fst_mem_Ioc_trimMeasure_T (T : ℝ≥0) (ℱ : Filtration ℝ≥0 mΩ) :
    ∀ᵐ z ∂(trimMeasure_T (μ := μ) T ℱ), z.1 ∈ Set.Ioc 0 T := by
  rw [trimMeasure_T_eq_restrict]
  exact (ae_restrict_mem (MeasureTheory.measurableSet_predictable_Ioc_prod
    (𝓕 := ℱ) 0 T MeasurableSet.univ)).mono
    fun _ hz ↦ hz.1

noncomputable def simpleProcessL2_T (T : ℝ≥0) (ℱ : Filtration ℝ≥0 mΩ)
    (V : SimpleProcess ℝ ℱ) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ) :=
  (memLp_uncurry_trim_T T ℱ V).toLp (Function.uncurry ⇑V)

def TBoundedSP (T : ℝ≥0) (ℱ : Filtration ℝ≥0 mΩ) :
    Submodule ℝ (SimpleProcess ℝ ℱ) where
  carrier := { V | ∀ p ∈ V.value.support, p.2 ≤ T }
  add_mem' {V W} hV hW p hp := by
    rcases Finset.mem_union.mp (Finsupp.support_add hp) with h | h
    · exact hV p h
    · exact hW p h
  zero_mem' p hp := absurd hp (by simp)
  smul_mem' c V hV p hp := hV p (Finsupp.support_smul hp)

lemma uncurry_eq_zero_of_lt {T : ℝ≥0} {ℱ : Filtration ℝ≥0 mΩ}
    (V : TBoundedSP T ℱ) {t : ℝ≥0} (ht : T < t) (ω : Ω) :
    Function.uncurry ⇑V.val (t, ω) = 0 := by
  show ⇑V.val t ω = 0
  rw [SimpleProcess.apply_eq]
  have ht0 : t ≠ ⊥ := by
    intro h
    rw [h, NNReal.bot_eq_zero] at ht
    exact absurd ht (by simp)
  have hbot : ({(⊥ : ℝ≥0)} : Set ℝ≥0).indicator
      (fun _ ↦ V.val.valueBot ω) t = 0 :=
    Set.indicator_of_notMem (by simpa using ht0) _
  rw [hbot, zero_add, Finsupp.sum]
  refine Finset.sum_eq_zero fun p hp ↦ ?_
  refine Set.indicator_of_notMem ?_ _
  simp only [Set.mem_Ioc, not_and, not_le]
  intro _
  exact lt_of_le_of_lt (V.property p hp) ht

noncomputable def simpleAssembly_T (T : ℝ≥0) (ℱ : Filtration ℝ≥0 mΩ) :
    TBoundedSP T ℱ →ₗ[ℝ] Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ) where
  toFun V := simpleProcessL2_T T ℱ V.val
  map_add' V W := by
    show simpleProcessL2_T T ℱ ((V + W).val) = _
    rw [Submodule.coe_add, simpleProcessL2_T, simpleProcessL2_T, simpleProcessL2_T,
        ← MemLp.toLp_add (memLp_uncurry_trim_T T ℱ V.val)
          (memLp_uncurry_trim_T T ℱ W.val)]
    congr 1
    exact uncurry_coe_add ℱ V.val W.val
  map_smul' c V := by
    show simpleProcessL2_T T ℱ ((c • V).val) = _
    rw [Submodule.coe_smul, simpleProcessL2_T, simpleProcessL2_T, RingHom.id_apply,
        ← MemLp.toLp_const_smul c (memLp_uncurry_trim_T T ℱ V.val)]
    congr 1
    exact uncurry_coe_smul ℱ c V.val

lemma setIntegral_eq_zero_of_orthogonal_pred (T : ℝ≥0)
    (ℱ : Filtration ℝ≥0 mΩ)
    {g : ℝ≥0 × Ω → ℝ}
    (hg_int : Integrable g (trimMeasure_T (μ := μ) T ℱ))
    (h_orth : ∀ R ∈ predictableRect (mΩ := mΩ) ℱ,
      ∫ z in R, g z ∂(trimMeasure_T (μ := μ) T ℱ) = 0)
    (s : Set (ℝ≥0 × Ω))
    (hs : MeasurableSet[ℱ.predictable] s) :
    ∫ z in s, g z ∂(trimMeasure_T (μ := μ) T ℱ) = 0 := by
  let 𝓕 := ℱ

  have h_total : ∫ z, g z ∂(trimMeasure_T (μ := μ) T ℱ) = 0 := by
    by_cases hT : 0 < T
    ·
      have hR : Set.Ioc 0 T ×ˢ (Set.univ : Set Ω) ∈ predictableRect (mΩ := mΩ) ℱ :=
        Or.inr ⟨0, T, hT, Set.univ, MeasurableSet.univ, rfl⟩
      have hS_pred : MeasurableSet[𝓕.predictable] (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)) :=
        MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓕) 0 T MeasurableSet.univ

      have hSc_null :
          (trimMeasure_T (μ := μ) T ℱ) (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω))ᶜ = 0 := by
        rw [trimMeasure_T_eq_restrict,
            Measure.restrict_apply (MeasurableSet.compl hS_pred),
            Set.compl_inter_self]
        exact measure_empty
      have h_int_Sc : ∫ z in (Set.Ioc 0 T ×ˢ Set.univ)ᶜ, g z
          ∂(trimMeasure_T (μ := μ) T ℱ) = 0 :=
        setIntegral_measure_zero g hSc_null
      have h_int_S := h_orth _ hR
      have h_split := integral_add_compl
        (μ := trimMeasure_T (μ := μ) T ℱ) (f := g) hS_pred hg_int
      linarith
    ·
      push Not at hT
      have hT0 : T = 0 := le_antisymm hT bot_le
      have h_zero : trimMeasure_T (μ := μ) T ℱ = 0 := by
        subst hT0
        unfold trimMeasure_T timeMeasure_T
        rw [Set.Ioc_self, Measure.restrict_empty, Measure.zero_prod,
            MeasureTheory.zero_trim]

      let gf : ℝ≥0 × Ω → ℝ := (g : ℝ≥0 × Ω → ℝ)
      show ∫ z, gf z ∂(trimMeasure_T (μ := μ) T ℱ) = 0
      rw [h_zero]
      exact integral_zero_measure gf

  refine MeasurableSpace.induction_on_inter
    (C := fun s _ ↦ ∫ z in s, g z ∂(trimMeasure_T (μ := μ) T ℱ) = 0)
    (h_eq := (generateFrom_predictableRect ℱ).symm)
    (h_inter := isPiSystem_predictableRect ℱ)
    (empty := setIntegral_empty)
    (basic := fun R hR ↦ h_orth R hR)
    (compl := ?_) (iUnion := ?_) s hs
  ·
    intro S hS hPS
    have h_split := integral_add_compl
      (μ := trimMeasure_T (μ := μ) T ℱ) (f := g) hS hg_int
    linarith
  ·
    intro f hf hfm hf_zero
    rw [integral_iUnion hfm hf hg_int.integrableOn]
    simp [hf_zero]

noncomputable def iocSP_T {T : ℝ≥0} (ℱ : Filtration ℝ≥0 mΩ)
    {a b : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T) {F : Set Ω}
    (hF : MeasurableSet[ℱ a] F) :
    TBoundedSP T ℱ :=
  ⟨(ElementaryPredictableSet.IocProd a b hF).indicator (1 : ℝ), fun p hp ↦ by

    have h_I_eq : (ElementaryPredictableSet.IocProd a b hF).I = {(a, b)} := by
      show (if a ≤ b then ({(a, b)} : Finset _) else ∅) = _
      rw [ite_eq_left hab]
    have h_in_I : p ∈ (ElementaryPredictableSet.IocProd a b hF).I := by
      by_contra hp_not
      apply Finsupp.mem_support_iff.mp hp
      show ((ElementaryPredictableSet.IocProd a b hF).indicator 1).value p = 0
      simp [ElementaryPredictableSet.indicator, Finsupp.onFinset_apply, hp_not]
    rw [h_I_eq, Finset.mem_singleton] at h_in_I
    rcases h_in_I with rfl
    exact hbT⟩

lemma uncurry_iocSP_T_eq {T : ℝ≥0} (ℱ : Filtration ℝ≥0 mΩ)
    {a b : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T) {F : Set Ω}
    (hF : MeasurableSet[ℱ a] F) :
    Function.uncurry ⇑(iocSP_T ℱ hab hbT hF : TBoundedSP T ℱ).val
      = (Set.Ioc a b ×ˢ F).indicator (fun _ ↦ (1 : ℝ)) := by
  funext ⟨t, ω⟩
  change ⇑((ElementaryPredictableSet.IocProd a b hF).indicator (1 : ℝ)) t ω
      = (Set.Ioc a b ×ˢ F).indicator (fun _ ↦ (1 : ℝ)) (t, ω)
  rw [ElementaryPredictableSet.coe_indicator,
      ElementaryPredictableSet.coe_IocProd a b hF]
  rfl

private lemma inner_simpleAssembly_T_iocSP_T {T : ℝ≥0} (ℱ : Filtration ℝ≥0 mΩ)
    {a b : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T) {F : Set Ω}
    (hF : MeasurableSet[ℱ a] F)
    (g : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    ⟪simpleAssembly_T (μ := μ) T ℱ (iocSP_T ℱ hab hbT hF), g⟫_ℝ
      = ∫ z in Set.Ioc a b ×ˢ F, g z ∂(trimMeasure_T (μ := μ) T ℱ) := by
  let 𝓕 := ℱ

  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  rw [L2.inner_def]

  have h_coe := MemLp.coeFn_toLp
    (memLp_uncurry_trim_T (μ := μ) T ℱ
      (iocSP_T ℱ hab hbT hF : TBoundedSP T ℱ).val)
  have h_uncurry_eq := uncurry_iocSP_T_eq ℱ hab hbT hF
  have h_ae_eq : ∀ᵐ z ∂(trimMeasure_T (μ := μ) T ℱ),
      (⟪(simpleAssembly_T (μ := μ) T ℱ (iocSP_T ℱ hab hbT hF) : ℝ≥0 × Ω → ℝ) z,
        (g : ℝ≥0 × Ω → ℝ) z⟫_ℝ : ℝ)
        = (Set.Ioc a b ×ˢ F).indicator (fun z ↦ (g : ℝ≥0 × Ω → ℝ) z) z := by
    filter_upwards [h_coe] with z hz

    have hSA_eq :
        (simpleAssembly_T (μ := μ) T ℱ (iocSP_T ℱ hab hbT hF) : ℝ≥0 × Ω → ℝ) z
          = (Set.Ioc a b ×ˢ F).indicator (fun _ ↦ (1 : ℝ)) z := by
      calc (simpleAssembly_T (μ := μ) T ℱ (iocSP_T ℱ hab hbT hF) : ℝ≥0 × Ω → ℝ) z
          = Function.uncurry ⇑(iocSP_T ℱ hab hbT hF : TBoundedSP T ℱ).val z := hz
        _ = (Set.Ioc a b ×ˢ F).indicator (fun _ ↦ (1 : ℝ)) z := by rw [h_uncurry_eq]
    rw [hSA_eq]

    show (g : ℝ≥0 × Ω → ℝ) z * (Set.Ioc a b ×ˢ F).indicator (fun _ ↦ (1 : ℝ)) z
        = (Set.Ioc a b ×ˢ F).indicator (fun z ↦ (g : ℝ≥0 × Ω → ℝ) z) z
    by_cases hz_in : z ∈ Set.Ioc a b ×ˢ F
    · rw [Set.indicator_of_mem hz_in, Set.indicator_of_mem hz_in, mul_one]
    · rw [Set.indicator_of_notMem hz_in, Set.indicator_of_notMem hz_in, mul_zero]
  rw [integral_congr_ae h_ae_eq]

  exact integral_indicator
    (MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓕) a b hF)

lemma setIntegral_eq_setIntegral_inter_supp {T : ℝ≥0}
    (ℱ : Filtration ℝ≥0 mΩ)
    (g : ℝ≥0 × Ω → ℝ) (R : Set (ℝ≥0 × Ω))
    (hR : MeasurableSet[ℱ.predictable] R) :
    ∫ z in R, g z ∂(trimMeasure_T (μ := μ) T ℱ) =
      ∫ z in R ∩ (Set.Ioc 0 T ×ˢ Set.univ), g z ∂(trimMeasure_T (μ := μ) T ℱ) := by
  let 𝓕 := ℱ

  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  have hS_pred : MeasurableSet (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)) :=
    MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓕) 0 T MeasurableSet.univ

  have h1 : (trimMeasure_T (μ := μ) T ℱ).restrict R
      = (trimMeasure_T (μ := μ) T ℱ).restrict (R ∩ Set.Ioc 0 T ×ˢ Set.univ) := by
    rw [trimMeasure_T_eq_restrict,
        Measure.restrict_restrict hR,
        Measure.restrict_restrict (hR.inter hS_pred),
        Set.inter_assoc, Set.inter_self]
  show ∫ z, g z ∂((trimMeasure_T (μ := μ) T ℱ).restrict R)
      = ∫ z, g z ∂((trimMeasure_T (μ := μ) T ℱ).restrict (R ∩ Set.Ioc 0 T ×ˢ Set.univ))
  rw [h1]

theorem simpleAssembly_T_denseRange (T : ℝ≥0) (ℱ : Filtration ℝ≥0 mΩ) :
    DenseRange (simpleAssembly_T (μ := μ) T ℱ) := by
  let 𝓕 := ℱ
  suffices h_orth_bot :
      (LinearMap.range (simpleAssembly_T (μ := μ) T ℱ))ᗮ = ⊥ by
    rw [denseRange_iff_closure_range,
        ← LinearMap.coe_range (simpleAssembly_T (μ := μ) T ℱ),
        ← Submodule.topologicalClosure_coe,
        Submodule.topologicalClosure_eq_top_iff.mpr h_orth_bot, Submodule.top_coe]
  rw [Submodule.eq_bot_iff]
  intro g h_mem
  rw [Submodule.mem_orthogonal] at h_mem

  have h_orth : ∀ R ∈ predictableRect (mΩ := mΩ) ℱ,
      ∫ z in R, g z ∂(trimMeasure_T (μ := μ) T ℱ) = 0 := by
    intro R hR
    rcases hR with ⟨F₀, hF₀, rfl⟩ | ⟨a, b, _hab, F, hF, rfl⟩
    ·

      have h_R_pred : MeasurableSet[𝓕.predictable] ({(⊥ : ℝ≥0)} ×ˢ F₀) :=
        MeasureTheory.measurableSet_predictable_singleton_bot_prod (𝓕 := 𝓕) hF₀
      rw [setIntegral_eq_setIntegral_inter_supp ℱ g _ h_R_pred]
      have h_empty : ({(⊥ : ℝ≥0)} ×ˢ F₀) ∩ Set.Ioc 0 T ×ˢ (Set.univ : Set Ω) = ∅ := by
        rw [Set.prod_inter_prod,
            show ({(⊥ : ℝ≥0)} ∩ Set.Ioc 0 T : Set ℝ≥0) = ∅ by
              ext x; simp,
            Set.empty_prod]
      rw [h_empty, setIntegral_empty]
    ·
      have h_R_pred : MeasurableSet[𝓕.predictable] (Set.Ioc a b ×ˢ F) :=
        MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓕) a b hF
      rw [setIntegral_eq_setIntegral_inter_supp ℱ g _ h_R_pred]
      have h_inter : (Set.Ioc a b ×ˢ F) ∩ (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω))
          = Set.Ioc (max a 0) (min b T) ×ˢ F := by
        ext ⟨t, ω⟩
        simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true]
        constructor
        · rintro ⟨⟨⟨h1, h2⟩, hω⟩, ⟨h3, h4⟩⟩
          exact ⟨⟨max_lt h1 h3, le_min h2 h4⟩, hω⟩
        · rintro ⟨⟨h1, h2⟩, hω⟩
          refine ⟨⟨⟨(le_max_left _ _).trans_lt h1, h2.trans (min_le_left _ _)⟩, hω⟩, ?_⟩
          exact ⟨(le_max_right _ _).trans_lt h1, h2.trans (min_le_right _ _)⟩
      rw [h_inter]
      have hmax : max a 0 = a := max_eq_left bot_le
      rw [hmax]

      by_cases hab' : a ≤ min b T
      ·
        have hbT' : min b T ≤ T := min_le_right _ _
        have h_set := inner_simpleAssembly_T_iocSP_T (μ := μ) ℱ hab' hbT' hF g
        have h_inner := h_mem _ ⟨iocSP_T ℱ hab' hbT' hF, rfl⟩
        rw [← h_set]
        exact h_inner
      ·
        push Not at hab'
        rw [Set.Ioc_eq_empty (not_lt.mpr hab'.le), Set.empty_prod, setIntegral_empty]

  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  refine (Lp.eq_zero_iff_ae_eq_zero (f := g)).mpr ?_
  exact Lp.ae_eq_zero_of_forall_setIntegral_eq_zero g
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    (fun _ _ _ ↦ ((Lp.memLp g).integrable one_le_two).integrableOn)
    (fun s hs _ ↦ setIntegral_eq_zero_of_orthogonal_pred T ℱ
      ((Lp.memLp g).integrable one_le_two) h_orth s hs)

end MathFin.FilteredIto.CommonPredictable
