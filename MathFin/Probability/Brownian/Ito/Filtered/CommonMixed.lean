/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CorrelatedIntegral

/-!
# Common Mixed

Orthogonality of the two completed common-filtration integrals. The
coefficients may depend jointly on both pasts. Independence of the raw Brownian
paths alone is not substituted for independence of random adapted integrals.

## Main results

* `IndependentPair.integral_itoSimple_mul`
* `IndependentPair.inner_itoSimpleLp`
* `IndependentPair.inner_itoIntegral`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto.CommonNoise
open MeasureTheory ProbabilityTheory
open MathFin.FilteredIto.CommonPredictable MathFin.FilteredIto.CommonIntegral
open scoped NNReal ENNReal InnerProductSpace
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {B Z : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ}

theorem IndependentPair.swap (h : IndependentPair ℱ B Z μ) : IndependentPair ℱ Z B μ := by
  refine ⟨h.right_law, h.left_law, h.right_adapted, h.left_adapted,
    h.paths_independent.symm, ?_⟩
  intro s f hf
  exact (h.joint_future_independent s hf).comp measurable_id measurable_swap

private theorem mixed_bounded_integrable (h : IndependentPair ℱ B Z μ)
    {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C)
    (a b c d : ℝ≥0) :
    Integrable (fun ω => f ω * ((B b ω - B a ω) * (Z d ω - Z c ω))) μ := by
  have hp : Integrable (fun ω => (B b ω - B a ω) * (Z d ω - Z c ω)) μ :=
    h.left_law.isGaussianProcess.hasGaussianLaw_sub.memLp_two.integrable_mul
      h.right_law.isGaussianProcess.hasGaussianLaw_sub.memLp_two
  exact hp.bdd_mul hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)

private theorem mixed_rectangle_oriented (h : IndependentPair ℱ B Z μ)
    {f g : Ω → ℝ} {s t s' t' : ℝ≥0}
    (hf : Measurable[ℱ s] f) (hg : Measurable[ℱ s'] g)
    {Cf Cg : ℝ} (hfb : ∀ ω, |f ω| ≤ Cf) (hgb : ∀ ω, |g ω| ≤ Cg)
    (hst' : s' ≤ t') (hss' : s ≤ s') :
    (∫ ω, (f ω * (B t ω - B s ω)) * (g ω * (Z t' ω - Z s' ω)) ∂μ) = 0 := by
  have hfm := hf.mono (ℱ.le s) le_rfl
  have hgm := hg.mono (ℱ.le s') le_rfl
  have hfg : Measurable[ℱ s'] (fun ω => f ω * g ω) :=
    (hf.mono (ℱ.mono hss') le_rfl).mul hg
  have hfgb : ∀ ω, |f ω * g ω| ≤ Cf * Cg := fun ω => by
    rw [abs_mul]
    exact mul_le_mul (hfb ω) (hgb ω) (abs_nonneg _) ((abs_nonneg _).trans (hfb ω))
  by_cases htle : t ≤ s'
  · have hχ := ((hf.mono (ℱ.mono hss') le_rfl).mul
      (((h.left_adapted t).measurable.mono (ℱ.mono htle) le_rfl).sub
        ((h.left_adapted s).measurable.mono (ℱ.mono hss') le_rfl))).mul hg
    have he := MathFin.ItoIsometryAdapted.integral_adapted_mul_increment
          h.right.isFilteredPreBrownian hst' hχ
    calc
      (∫ ω, (f ω * (B t ω - B s ω)) * (g ω * (Z t' ω - Z s' ω)) ∂μ) =
          ∫ ω, (f ω * (B t ω - B s ω) * g ω) * (Z t' ω - Z s' ω) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        ring
      _ = 0 := he
  · have hst : s' ≤ t := (not_le.mp htle).le
    have hχ := hfg.mul (((h.left_adapted s').measurable).sub
      ((h.left_adapted s).measurable.mono (ℱ.mono hss') le_rfl))
    have hfirst : (∫ ω, f ω * g ω * ((B s' ω - B s ω) * (Z t' ω - Z s' ω)) ∂μ) = 0 := by
      have he := MathFin.ItoIsometryAdapted.integral_adapted_mul_increment
            h.right.isFilteredPreBrownian hst' hχ
      calc
        _ = ∫ ω, (f ω * g ω * (B s' ω - B s ω)) * (Z t' ω - Z s' ω) ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with ω
          ring
        _ = 0 := he
    have hindep : IndepFun (fun ω => f ω * g ω)
        (fun ω => (B t ω - B s' ω) * (Z t' ω - Z s' ω)) μ := by
      have hi := (h.joint_future_independent s' hfg).comp measurable_id
        (show Measurable (fun p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) =>
          p.1 (t-s') * p.2 (t'-s')) by fun_prop)
      simpa only [Function.comp_def, id_eq, add_tsub_cancel_of_le hst,
        add_tsub_cancel_of_le hst'] using hi
    have hsecond : (∫ ω, f ω * g ω * ((B t ω - B s' ω) * (Z t' ω - Z s' ω)) ∂μ) = 0 := by
      rw [hindep.integral_fun_mul_eq_mul_integral (hfm.mul hgm).aestronglyMeasurable
        (((h.left.measurable t).sub (h.left.measurable s')).mul
          ((h.right.measurable t').sub (h.right.measurable s'))).aestronglyMeasurable]
      rw [h.integral_increment_mul s' t s' t', mul_zero]
    have hsum : (∫ ω, (f ω * (B t ω - B s ω)) * (g ω * (Z t' ω - Z s' ω)) ∂μ) =
        (∫ ω, f ω * g ω * ((B s' ω - B s ω) * (Z t' ω - Z s' ω)) ∂μ) +
        ∫ ω, f ω * g ω * ((B t ω - B s' ω) * (Z t' ω - Z s' ω)) ∂μ := by
      rw [← integral_add (mixed_bounded_integrable h (f := fun ω => f ω * g ω)
        (hfm.mul hgm) hfgb s s' s' t')
        (mixed_bounded_integrable h (f := fun ω => f ω * g ω) (hfm.mul hgm) hfgb s' t s' t')]
      apply integral_congr_ae
      filter_upwards [] with ω
      ring
    rw [hsum, hfirst, hsecond, zero_add]

theorem IndependentPair.mixed_rectangle (h : IndependentPair ℱ B Z μ)
    {f g : Ω → ℝ} {s t s' t' : ℝ≥0}
    (hf : Measurable[ℱ s] f) (hg : Measurable[ℱ s'] g)
    {Cf Cg : ℝ} (hfb : ∀ ω, |f ω| ≤ Cf) (hgb : ∀ ω, |g ω| ≤ Cg)
    (hst : s ≤ t) (hst' : s' ≤ t') :
    (∫ ω, (f ω * (B t ω - B s ω)) * (g ω * (Z t' ω - Z s' ω)) ∂μ) = 0 := by
  rcases le_total s s' with hss | hss
  · exact mixed_rectangle_oriented h hf hg hfb hgb hst' hss
  · rw [show (fun ω => (f ω * (B t ω - B s ω)) * (g ω * (Z t' ω - Z s' ω))) =
      (fun ω => (g ω * (Z t' ω - Z s' ω)) * (f ω * (B t ω - B s ω))) by
        funext ω; ring]
    exact mixed_rectangle_oriented h.swap hg hf hgb hfb hst hss

variable [IsProbabilityMeasure μ]

theorem IndependentPair.integral_itoSimple_mul (h : IndependentPair ℱ B Z μ)
    (V W : SimpleProcess ℝ ℱ) :
    (∫ ω, CommonL2.itoSimple h.left.measurable V ω *
      CommonL2.itoSimple h.right.measurable W ω ∂μ) = 0 := by
  let a := fun p ω => V.value p ω * (B p.2 ω - B p.1 ω)
  let b := fun p ω => W.value p ω * (Z p.2 ω - Z p.1 ω)
  have ha : ∀ p ∈ V.value.support, MemLp (a p) 2 μ := by
    intro p hp
    apply MathFin.ItoIsometryAdapted.memLp_adapted_mul_increment h.left.isFilteredPreBrownian
          (V.le_of_mem_support_value p hp) (V.measurable_value p)
    exact MemLp.of_bound ((V.measurable_value p).mono (ℱ.le p.1) le_rfl).aestronglyMeasurable
      V.valueBound (Filter.Eventually.of_forall (V.value_le_valueBound p))
  have hb : ∀ p ∈ W.value.support, MemLp (b p) 2 μ := by
    intro p hp
    apply MathFin.ItoIsometryAdapted.memLp_adapted_mul_increment h.right.isFilteredPreBrownian
          (W.le_of_mem_support_value p hp) (W.measurable_value p)
    exact MemLp.of_bound ((W.measurable_value p).mono (ℱ.le p.1) le_rfl).aestronglyMeasurable
      W.valueBound (Filter.Eventually.of_forall (W.value_le_valueBound p))
  have hi : ∀ p ∈ V.value.support, ∀ q ∈ W.value.support,
      Integrable (fun ω => a p ω * b q ω) μ :=
    fun p hp q hq => (ha p hp).integrable_mul (hb q hq)
  change (∫ ω, (∑ p ∈ V.value.support, a p ω) * (∑ q ∈ W.value.support, b q ω) ∂μ) = 0
  simp_rw [Finset.sum_mul_sum]
  rw [integral_finsetSum _ (fun p hp => integrable_finsetSum _
    (fun q hq => hi p hp q hq))]
  apply Finset.sum_eq_zero
  intro p hp
  rw [integral_finsetSum _ (fun q hq => hi p hp q hq)]
  apply Finset.sum_eq_zero
  intro q hq
  exact h.mixed_rectangle (V.measurable_value p) (W.measurable_value q)
    (V.value_le_valueBound p) (W.value_le_valueBound q)
    (V.le_of_mem_support_value p hp) (W.le_of_mem_support_value q hq)

theorem IndependentPair.inner_itoSimpleLp (h : IndependentPair ℱ B Z μ)
    (V W : SimpleProcess ℝ ℱ) :
    ⟪CommonL2.itoSimpleLp h.left h.left.measurable V,
      CommonL2.itoSimpleLp h.right h.right.measurable W⟫_ℝ = 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ ω, CommonL2.itoSimple h.left.measurable V ω * CommonL2.itoSimple h.right.measurable W
          ω ∂μ := by
      apply integral_congr_ae
      filter_upwards [(CommonL2.memLp_itoSimple h.left h.left.measurable V).coeFn_toLp,
        (CommonL2.memLp_itoSimple h.right h.right.measurable W).coeFn_toLp] with ω hb hz
      change (CommonL2.itoSimpleLp h.right h.right.measurable W ω) *
        (CommonL2.itoSimpleLp h.left h.left.measurable V ω) = _
      rw [show CommonL2.itoSimpleLp h.left h.left.measurable V ω = _ from hb,
        show CommonL2.itoSimpleLp h.right h.right.measurable W ω = _ from hz]
      ring
    _ = 0 := h.integral_itoSimple_mul V W

/-- The two real integrals are orthogonal for arbitrary random predictable L2
kernels on the COMMON filtration. No independence of these integrals is claimed. -/
theorem IndependentPair.inner_itoIntegral (h : IndependentPair ℱ B Z μ) (T : ℝ≥0)
    (f g : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    ⟪itoIntegralCLMT h.left T f, itoIntegralCLMT h.right T g⟫_ℝ = 0 := by
  have hv (V : TBoundedSP T ℱ) :
      (fun g => ⟪itoIntegralCLMT h.left T (simpleAssemblyT (μ := μ) T ℱ V),
        itoIntegralCLMT h.right T g⟫_ℝ) = (fun _ => (0 : ℝ)) := by
    apply (simpleAssembly_T_denseRange (μ := μ) T ℱ).equalizer
      (continuous_const.inner (itoIntegralCLMT h.right T).continuous) continuous_const
    funext W
    simp only [Function.comp_apply, itoIntegralCLM_T_simpleAssembly]
    exact h.inner_itoSimpleLp V.val W.val
  have he : (fun f => ⟪itoIntegralCLMT h.left T f, itoIntegralCLMT h.right T g⟫_ℝ) =
      (fun _ => (0 : ℝ)) := by
    apply (simpleAssembly_T_denseRange (μ := μ) T ℱ).equalizer
      ((itoIntegralCLMT h.left T).continuous.inner continuous_const) continuous_const
    funext V
    exact congrFun (hv V) g
  exact congrFun he f

end MathFin.FilteredIto.CommonNoise
