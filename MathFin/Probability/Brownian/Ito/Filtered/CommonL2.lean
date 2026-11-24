/-
Copyright (c) 2026 Raphael Coelho, Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CommonPairing

/-!
# Common L2

Actual simple Itô sums, L2 membership and their overlap isometry for random
coefficients measurable on a common filtration. Generated from the pinned
ItoIntegralL2 source; all stochastic inputs are proved in CommonPairing.

Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Generalized to an arbitrary common filtration for Heston, 2026-10-18.

## Main definitions

* `simpleProcessL2`
* `itoAssembly`
* `simpleAssembly`

## Main results

* `uncurry_coe_add`
* `uncurry_coe_smul`
* `assembly_isometry`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto.CommonL2
open MeasureTheory ProbabilityTheory
open MathFin.FilteredIto.CommonNoise
open scoped NNReal ENNReal InnerProductSpace
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ}

theorem adaptedAt_of_measurable (_hBm : ∀ t, Measurable (B t)) {s : ℝ≥0}
    {f : Ω → ℝ} (hf : Measurable[ℱ s] f) : CommonPairing.AdaptedAt ℱ s f := hf

noncomputable def itoSimple (_hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ) : Ω → ℝ :=
  fun ω ↦ V.value.sum fun p v ↦ v ω * (B p.2 ω - B p.1 ω)

lemma itoSimple_apply (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ) (ω : Ω) :
    itoSimple hBmeas V ω
      = V.value.sum fun p v ↦ v ω * (B p.2 ω - B p.1 ω) :=
  rfl

variable [IsProbabilityMeasure μ]

theorem memLp_itoSimple (hB : BrownianOn ℱ B μ) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ) :
    MemLp (itoSimple hBmeas V) 2 μ := by
  rw [show itoSimple hBmeas V
        = fun ω ↦ ∑ p ∈ V.value.support, V.value p ω * (B p.2 ω - B p.1 ω)
      from funext fun ω ↦ by rw [itoSimple_apply]; rfl]
  refine memLp_finsetSum V.value.support (fun p hp ↦ ?_)
  refine MathFin.ItoIsometryAdapted.memLp_adapted_mul_increment hB.isFilteredPreBrownian
        (V.le_of_mem_support_value p hp)
    (adaptedAt_of_measurable hBmeas (V.measurable_value p)) ?_
  exact MemLp.of_bound
    ((V.measurable_value p).mono (ℱ.le p.1) le_rfl).aestronglyMeasurable
    V.valueBound (ae_of_all _ (V.value_le_valueBound p))

noncomputable def itoSimpleLp (hB : BrownianOn ℱ B μ) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ) : Lp ℝ 2 μ :=
  (memLp_itoSimple hB hBmeas V).toLp _

theorem itoSimple_sq_integral (hB : BrownianOn ℱ B μ) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ) :
    ∫ ω, (itoSimple hBmeas V ω) ^ 2 ∂μ
      = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support,
          (∫ ω, V.value p ω * V.value q ω ∂μ)
            * max 0 ((min (p.2 : ℝ) q.2) - (max (p.1 : ℝ) q.1)) := by
  set a : (ℝ≥0 × ℝ≥0) → Ω → ℝ := fun p ω ↦ V.value p ω * (B p.2 ω - B p.1 ω)
  have ha_L2 : ∀ p ∈ V.value.support, MemLp (a p) 2 μ := fun p hp ↦
    MathFin.ItoIsometryAdapted.memLp_adapted_mul_increment hB.isFilteredPreBrownian
          (V.le_of_mem_support_value p hp)
      (adaptedAt_of_measurable hBmeas (V.measurable_value p))
      (MemLp.of_bound
        ((V.measurable_value p).mono (ℱ.le p.1) le_rfl).aestronglyMeasurable
        V.valueBound (ae_of_all _ (V.value_le_valueBound p)))
  have hint : ∀ p ∈ V.value.support, ∀ q ∈ V.value.support,
      Integrable (fun ω ↦ a p ω * a q ω) μ :=
    fun p hp q hq ↦ (ha_L2 p hp).integrable_mul (ha_L2 q hq)
  calc ∫ ω, (itoSimple hBmeas V ω) ^ 2 ∂μ
      = ∫ ω, ∑ p ∈ V.value.support, ∑ q ∈ V.value.support, a p ω * a q ω ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
        show itoSimple hBmeas V ω ^ 2
          = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support, a p ω * a q ω
        rw [show itoSimple hBmeas V ω = ∑ p ∈ V.value.support, a p ω from by
              rw [itoSimple_apply]; rfl, sq, Finset.sum_mul_sum]
    _ = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support, ∫ ω, a p ω * a q ω ∂μ := by
        rw [integral_finsetSum _ (fun p hp ↦ integrable_finsetSum _ fun q hq ↦ hint p hp q hq)]
        exact Finset.sum_congr rfl fun p hp ↦
          integral_finsetSum _ (fun q hq ↦ hint p hp q hq)
    _ = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support,
          (∫ ω, V.value p ω * V.value q ω ∂μ)
            * max 0 ((min (p.2 : ℝ) q.2) - (max (p.1 : ℝ) q.1)) := by
        refine Finset.sum_congr rfl fun p hp ↦ Finset.sum_congr rfl fun q hq ↦ ?_
        exact MathFin.ItoIsometryAdapted.rect_increment_pairing hB.isFilteredPreBrownian
          (adaptedAt_of_measurable hBmeas (V.measurable_value p))
          (adaptedAt_of_measurable hBmeas (V.measurable_value q))
          (fun ω ↦ by rw [← Real.norm_eq_abs]; exact V.value_le_valueBound p ω)
          (fun ω ↦ by rw [← Real.norm_eq_abs]; exact V.value_le_valueBound q ω)
          (V.le_of_mem_support_value p hp) (V.le_of_mem_support_value q hq)

lemma lp_two_norm_sq {α : Type*} {mα : MeasurableSpace α} {ν : Measure α}
    (g : Lp ℝ 2 ν) : ‖g‖ ^ 2 = ∫ a, (g a) ^ 2 ∂ν := by
  have h : ⟪g, g⟫_ℝ = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
  rw [L2.inner_def] at h
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards with a
  show (g a) * (g a) = (g a) ^ 2
  ring

theorem itoSimpleLp_norm_sq (hB : BrownianOn ℱ B μ) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ) :
    ‖(itoSimpleLp hB hBmeas V : Lp ℝ 2 μ)‖ ^ 2
      = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support,
          (∫ ω, V.value p ω * V.value q ω ∂μ)
            * max 0 ((min (p.2 : ℝ) q.2) - (max (p.1 : ℝ) q.1)) := by
  rw [lp_two_norm_sq, ← itoSimple_sq_integral hB hBmeas V]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_itoSimple hB hBmeas V).coeFn_toLp] with ω hω
  rw [show (itoSimpleLp hB hBmeas V : Ω → ℝ) ω = itoSimple hBmeas V ω from hω]

lemma measurableEmbedding_nnrealCoe : MeasurableEmbedding ((↑) : ℝ≥0 → ℝ) :=
  NNReal.isClosedEmbedding_coe.measurableEmbedding

noncomputable def timeMeasure : Measure ℝ≥0 := Measure.comap ((↑) : ℝ≥0 → ℝ) volume

lemma timeMeasure_Ioc (a b : ℝ≥0) :
    timeMeasure (Set.Ioc a b) = ENNReal.ofReal ((b : ℝ) - a) := by
  have himg : ((↑) : ℝ≥0 → ℝ) '' Set.Ioc a b = Set.Ioc (a : ℝ) b := by
    ext x
    simp only [Set.mem_image, Set.mem_Ioc]
    constructor
    · rintro ⟨y, ⟨hay, hyb⟩, rfl⟩
      exact ⟨by exact_mod_cast hay, by exact_mod_cast hyb⟩
    · rintro ⟨hax, hxb⟩
      have hx0 : 0 ≤ x := le_of_lt (lt_of_le_of_lt a.coe_nonneg hax)
      exact ⟨⟨x, hx0⟩, ⟨by exact_mod_cast hax, by exact_mod_cast hxb⟩, rfl⟩
  rw [timeMeasure, measurableEmbedding_nnrealCoe.comap_apply, himg, Real.volume_Ioc]

lemma timeMeasure_Ioc_inter (a b c d : ℝ≥0) :
    timeMeasure (Set.Ioc a b ∩ Set.Ioc c d)
      = ENNReal.ofReal (min (b : ℝ) d - max (a : ℝ) c) := by
  rw [Set.Ioc_inter_Ioc, timeMeasure_Ioc, NNReal.coe_min, NNReal.coe_max]

instance : IsFiniteMeasureOnCompacts timeMeasure :=
  IsFiniteMeasureOnCompacts.comap' volume NNReal.continuous_coe measurableEmbedding_nnrealCoe

instance : SigmaFinite timeMeasure := inferInstance

lemma timeMeasure_singleton (a : ℝ≥0) : timeMeasure {a} = 0 := by
  rw [timeMeasure, measurableEmbedding_nnrealCoe.comap_apply, Set.image_singleton,
    Real.volume_singleton]

noncomputable def elemIntegrand (a b : ℝ≥0) (Z : Ω → ℝ) : ℝ≥0 × Ω → ℝ :=
  fun z ↦ (Set.Ioc a b).indicator (fun _ ↦ (1 : ℝ)) z.1 * Z z.2

noncomputable def rectTerm (_hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ) (p : ℝ≥0 × ℝ≥0) :
    ℝ≥0 × Ω → ℝ :=
  elemIntegrand p.1 p.2 (V.value p)

lemma rectTerm_eq_indicator (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ) (p : ℝ≥0 × ℝ≥0) :
    rectTerm hBmeas V p
      = (Set.Ioc p.1 p.2 ×ˢ (Set.univ : Set Ω)).indicator (fun z ↦ V.value p z.2) := by
  funext z
  rw [rectTerm, elemIntegrand, Set.indicator_apply, Set.indicator_apply]
  simp only [Set.mem_prod, Set.mem_univ, and_true]
  split_ifs <;> simp

lemma memLp_rectTerm (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ) (p : ℝ≥0 × ℝ≥0) :
    MemLp (rectTerm hBmeas V p) 2 (timeMeasure.prod μ) := by
  have : IsFiniteMeasure (timeMeasure.restrict (Set.Ioc p.1 p.2)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, timeMeasure_Ioc];
        exact ENNReal.ofReal_lt_top⟩
  rw [rectTerm_eq_indicator,
      memLp_indicator_iff_restrict (measurableSet_Ioc.prod MeasurableSet.univ).nullMeasurableSet,
      ← Measure.prod_restrict, Measure.restrict_univ]
  have hmeas : Measurable (fun z : ℝ≥0 × Ω ↦ V.value p z.2) :=
    ((V.measurable_value p).mono (ℱ.le p.1) le_rfl).comp measurable_snd
  exact MemLp.of_bound hmeas.aestronglyMeasurable V.valueBound
    (ae_of_all _ fun z ↦ by rw [Real.norm_eq_abs]; exact V.value_le_valueBound p z.2)

lemma uncurry_ae_eq_sum_rectTerm_of_ae_fst_ne_zero {m : MeasurableSpace (ℝ≥0 × Ω)}
    {ν : @Measure (ℝ≥0 × Ω) m} (hν : ∀ᵐ z ∂ν, z.1 ≠ 0) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ) :
    Function.uncurry ⇑V =ᵐ[ν] fun z ↦ ∑ p ∈ V.value.support, rectTerm hBmeas V p z := by
  filter_upwards [hν] with z hz
  show ⇑V z.1 z.2 = _
  rw [SimpleProcess.apply_eq, Set.indicator_of_notMem (by simpa using hz), zero_add, Finsupp.sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [rectTerm, elemIntegrand, Set.indicator_apply, Set.indicator_apply]
  split_ifs <;> simp

lemma ae_fst_ne_zero_prod (μ : Measure Ω) [SFinite μ] :
    ∀ᵐ z : ℝ≥0 × Ω ∂(timeMeasure.prod μ), z.1 ≠ 0 := by
  rw [Filter.eventually_iff, mem_ae_iff,
      show {z : ℝ≥0 × Ω | z.1 ≠ 0}ᶜ = {(0 : ℝ≥0)} ×ˢ (Set.univ : Set Ω) from by ext z; simp,
      Measure.prod_prod, timeMeasure_singleton, zero_mul]

lemma uncurry_ae_eq_sum_rectTerm (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ) :
    Function.uncurry ⇑V
      =ᵐ[timeMeasure.prod μ] fun z ↦ ∑ p ∈ V.value.support, rectTerm hBmeas V p z :=
  uncurry_ae_eq_sum_rectTerm_of_ae_fst_ne_zero (ae_fst_ne_zero_prod μ) hBmeas V

lemma memLp_uncurry_prod (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ) :
    MemLp (Function.uncurry ⇑V) 2 (timeMeasure.prod μ) :=
  (memLp_congr_ae (uncurry_ae_eq_sum_rectTerm hBmeas V)).mpr
    (memLp_finsetSum _ fun p _ ↦ memLp_rectTerm hBmeas V p)

lemma memLp_uncurry_trim (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ) :
    MemLp (Function.uncurry ⇑V) 2
      ((timeMeasure.prod μ).trim ℱ.predictable_le_prod) := by
  apply memLp_iff.mpr
  rw [eLpNorm_trim _ V.isStronglyPredictable]
  exact (memLp_uncurry_prod hBmeas V).eLpNorm_lt_top

noncomputable def simpleProcessL2 (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ) :
    Lp ℝ 2 ((timeMeasure.prod μ).trim ℱ.predictable_le_prod) :=
  (memLp_uncurry_trim hBmeas V).toLp (Function.uncurry ⇑V)

lemma integral_rectTerm_mul (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ) (p q : ℝ≥0 × ℝ≥0) :
    ∫ z, rectTerm hBmeas V p z * rectTerm hBmeas V q z ∂(timeMeasure.prod μ)
      = (∫ ω, V.value p ω * V.value q ω ∂μ)
          * max 0 ((min (p.2 : ℝ) q.2) - (max (p.1 : ℝ) q.1)) := by
  have hfun : (fun z : ℝ≥0 × Ω ↦ rectTerm hBmeas V p z * rectTerm hBmeas V q z)
      = fun z ↦ ((Set.Ioc p.1 p.2).indicator (fun _ ↦ (1 : ℝ)) z.1
                    * (Set.Ioc q.1 q.2).indicator (fun _ ↦ (1 : ℝ)) z.1)
                  * (V.value p z.2 * V.value q z.2) := by
    funext z; simp only [rectTerm, elemIntegrand]; ring
  rw [hfun, integral_prod_mul
        (fun i ↦ (Set.Ioc p.1 p.2).indicator (fun _ ↦ (1 : ℝ)) i
          * (Set.Ioc q.1 q.2).indicator (fun _ ↦ (1 : ℝ)) i)
        (fun ω ↦ V.value p ω * V.value q ω), mul_comm]
  congr 1
  have hpt : ∀ i : ℝ≥0, (Set.Ioc p.1 p.2).indicator (fun _ ↦ (1 : ℝ)) i
        * (Set.Ioc q.1 q.2).indicator (fun _ ↦ (1 : ℝ)) i
        = (Set.Ioc p.1 p.2 ∩ Set.Ioc q.1 q.2).indicator (1 : ℝ≥0 → ℝ) i := by
    intro i; rw [Set.inter_indicator_one]; rfl
  simp_rw [hpt]
  rw [integral_indicator_one (measurableSet_Ioc.inter measurableSet_Ioc),
      Measure.real_def, timeMeasure_Ioc_inter, ENNReal.toReal_ofReal', max_comm]

theorem simpleProcessL2_norm_sq (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ) :
    ‖simpleProcessL2 (μ := μ) hBmeas V‖ ^ 2
      = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support,
          (∫ ω, V.value p ω * V.value q ω ∂μ)
            * max 0 ((min (p.2 : ℝ) q.2) - (max (p.1 : ℝ) q.1)) := by

  have hStepA : ‖simpleProcessL2 (μ := μ) hBmeas V‖ ^ 2
      = ∫ z, (Function.uncurry ⇑V z) ^ 2 ∂(timeMeasure.prod μ) := by
    rw [lp_two_norm_sq (simpleProcessL2 (μ := μ) hBmeas V)]
    have hco : (fun z ↦ (simpleProcessL2 (μ := μ) hBmeas V z) ^ 2)
        =ᵐ[(timeMeasure.prod μ).trim ℱ.predictable_le_prod]
          fun z ↦ (Function.uncurry ⇑V z) ^ 2 := by
      filter_upwards [(memLp_uncurry_trim hBmeas V).coeFn_toLp] with z hz
      rw [show (simpleProcessL2 (μ := μ) hBmeas V) z = Function.uncurry ⇑V z from hz]
    rw [integral_congr_ae hco]
    simp only [pow_two]
    have hsm2 : StronglyMeasurable[ℱ.predictable]
        (fun z ↦ Function.uncurry ⇑V z * Function.uncurry ⇑V z) :=
      V.isStronglyPredictable.mul V.isStronglyPredictable
    exact (integral_trim ℱ.predictable_le_prod hsm2).symm
  rw [hStepA]

  have hint : ∀ p ∈ V.value.support, ∀ q ∈ V.value.support,
      Integrable (fun z ↦ rectTerm hBmeas V p z * rectTerm hBmeas V q z) (timeMeasure.prod μ) :=
    fun p _ q _ ↦ (memLp_rectTerm hBmeas V p).integrable_mul (memLp_rectTerm hBmeas V q)
  have hsq : ∀ᵐ z ∂(timeMeasure.prod μ), (Function.uncurry ⇑V z) ^ 2
      = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support,
          rectTerm hBmeas V p z * rectTerm hBmeas V q z := by
    filter_upwards [uncurry_ae_eq_sum_rectTerm hBmeas V] with z hz
    rw [hz, sq, Finset.sum_mul_sum]
  rw [integral_congr_ae hsq,
      integral_finsetSum _ (fun p hp ↦ integrable_finsetSum _ fun q hq ↦ hint p hp q hq)]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [integral_finsetSum _ fun q hq ↦ hint p hp q hq]
  exact Finset.sum_congr rfl fun q _ ↦ integral_rectTerm_mul hBmeas V p q

lemma itoSimple_add (hBmeas : ∀ t, Measurable (B t))
    (V W : SimpleProcess ℝ ℱ) :
    itoSimple hBmeas (V + W) = itoSimple hBmeas V + itoSimple hBmeas W := by
  funext ω
  simp only [itoSimple, Pi.add_apply, show (V + W).value = V.value + W.value from rfl]
  exact Finsupp.sum_add_index' (fun p ↦ by simp) (fun p v w ↦ by simp [add_mul])

lemma itoSimple_smul (hBmeas : ∀ t, Measurable (B t)) (c : ℝ)
    (V : SimpleProcess ℝ ℱ) :
    itoSimple hBmeas (c • V) = c • itoSimple hBmeas V := by
  funext ω
  simp only [itoSimple, Pi.smul_apply, smul_eq_mul,
    show (c • V).value = c • V.value from rfl]
  rw [Finsupp.sum_smul_index' (fun p ↦ by simp), Finsupp.mul_sum]
  exact Finsupp.sum_congr fun p _ ↦ by simp [mul_assoc]

noncomputable def itoAssembly (hB : BrownianOn ℱ B μ) (hBmeas : ∀ t, Measurable (B t)) :
    SimpleProcess ℝ ℱ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun V := itoSimpleLp hB hBmeas V
  map_add' V W := by
    rw [itoSimpleLp, itoSimpleLp, itoSimpleLp,
        ← MemLp.toLp_add (memLp_itoSimple hB hBmeas V) (memLp_itoSimple hB hBmeas W)]
    congr 1
    exact itoSimple_add hBmeas V W
  map_smul' c V := by
    rw [itoSimpleLp, itoSimpleLp, RingHom.id_apply,
        ← MemLp.toLp_const_smul c (memLp_itoSimple hB hBmeas V)]
    congr 1
    exact itoSimple_smul hBmeas c V

lemma uncurry_coe_add (_hBmeas : ∀ t, Measurable (B t))
    (V W : SimpleProcess ℝ ℱ) :
    Function.uncurry ⇑(V + W) = Function.uncurry ⇑V + Function.uncurry ⇑W := by
  rw [SimpleProcess.coe_add]; rfl

lemma uncurry_coe_smul (_hBmeas : ∀ t, Measurable (B t)) (c : ℝ)
    (V : SimpleProcess ℝ ℱ) :
    Function.uncurry ⇑(c • V) = c • Function.uncurry ⇑V := by
  rw [SimpleProcess.coe_smul]; rfl

noncomputable def simpleAssembly (hBmeas : ∀ t, Measurable (B t)) :
    SimpleProcess ℝ ℱ
      →ₗ[ℝ] Lp ℝ 2 ((timeMeasure.prod μ).trim ℱ.predictable_le_prod) where
  toFun V := simpleProcessL2 (μ := μ) hBmeas V
  map_add' V W := by
    rw [simpleProcessL2, simpleProcessL2, simpleProcessL2,
        ← MemLp.toLp_add (memLp_uncurry_trim hBmeas V) (memLp_uncurry_trim hBmeas W)]
    congr 1
    exact uncurry_coe_add hBmeas V W
  map_smul' c V := by
    rw [simpleProcessL2, simpleProcessL2, RingHom.id_apply,
        ← MemLp.toLp_const_smul c (memLp_uncurry_trim hBmeas V)]
    congr 1
    exact uncurry_coe_smul hBmeas c V

theorem assembly_isometry (hB : BrownianOn ℱ B μ) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ ℱ) :
    ‖itoAssembly (μ := μ) hB hBmeas V‖ = ‖simpleAssembly (μ := μ) hBmeas V‖ := by
  have hsq : ‖itoAssembly (μ := μ) hB hBmeas V‖ ^ 2 = ‖simpleAssembly (μ := μ) hBmeas V‖ ^ 2 := by
    show ‖(itoSimpleLp hB hBmeas V : Lp ℝ 2 μ)‖ ^ 2 = ‖simpleProcessL2 (μ := μ) hBmeas V‖ ^ 2
    rw [itoSimpleLp_norm_sq hB hBmeas V, simpleProcessL2_norm_sq hBmeas V]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

end MathFin.FilteredIto.CommonL2
