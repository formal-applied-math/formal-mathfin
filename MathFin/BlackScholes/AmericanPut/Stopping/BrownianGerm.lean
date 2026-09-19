/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.BrownianModel
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Arbitrarily early downward Brownian excursions

Normalized evaluations at times `(n+1)⁻²` all have the standard Gaussian law.
Their negative limsup event belongs to the Brownian germ sigma algebra. The
zero-one law and bounded convergence show that this event has probability one.
No independence between these overlapping evaluations is claimed or needed.

## Result

Public entry points include `brownianProbeTime`, `brownianProbe`, `brownianNegativeGerm`, `brownianProbeTime_pos`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

/-- The `n`-th probe time `(1/(n+1))^2`. -/
noncomputable def brownianProbeTime (n : ℕ) : ℝ≥0 := (1/((n : ℝ≥0)+1))^2

/-- The Brownian evaluation at `brownianProbeTime n`, normalized by the factor `n+1`. -/
noncomputable def brownianProbe (n : ℕ) (ω : ℝ≥0 → ℝ) : ℝ :=
  ((n : ℝ)+1)*brownian (brownianProbeTime n) ω

/-- The set of paths whose normalized probes `brownianProbe n` fall below `-1` for infinitely
many `n`. -/
def brownianNegativeGerm : Set (ℝ≥0 → ℝ) :=
  {ω | ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ brownianProbe n ω < -1}

theorem brownianProbeTime_pos (n : ℕ) : 0 < brownianProbeTime n := by
  unfold brownianProbeTime
  positivity

theorem brownianProbeTime_tendsto : Tendsto brownianProbeTime atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => (1/((n : ℝ≥0)+1))^2) atTop (𝓝 0)
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0)).pow 2

theorem brownianProbe_hasLaw (n : ℕ) :
    HasLaw (brownianProbe n) (gaussianReal 0 1) gaussianLimit := by
  have hh := gaussianReal_const_mul (hasLaw_brownian_eval (t := brownianProbeTime n)) ((n : ℝ)+1)
  have hv : (NNReal.mk (((n : ℝ)+1)^2) (sq_nonneg _))*brownianProbeTime n = 1 := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mul,NNReal.coe_mk,brownianProbeTime,NNReal.coe_pow,
      NNReal.coe_div,NNReal.coe_one,NNReal.coe_add,NNReal.coe_natCast]
    field_simp
  change HasLaw (fun ω => ((n : ℝ)+1)*brownian (brownianProbeTime n) ω) (gaussianReal 0 1) gaussianLimit
  simpa only [mul_zero,hv] using hh

theorem brownianNegativeGerm_tail (M : ℕ) :
    brownianNegativeGerm = {ω | ∀ N : ℕ, ∃ n : ℕ, max N M ≤ n ∧ brownianProbe n ω < -1} := by
  ext ω
  constructor
  · intro h N
    exact h (max N M)
  · intro h N
    obtain ⟨n,hn,hneg⟩ := h N
    exact ⟨n,(le_max_left _ _).trans hn,hneg⟩

theorem brownianNegativeGerm_measurable_germ :
    MeasurableSet[⨅ s > (0 : ℝ≥0), Filtration.natural brownian
      (fun t => (measurable_brownian t).stronglyMeasurable) s] brownianNegativeGerm := by
  rw [MeasurableSpace.measurableSet_iInf]
  intro s
  rw [MeasurableSpace.measurableSet_iInf]
  intro hs
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    (brownianProbeTime_tendsto.eventually (Iio_mem_nhds hs))
  rw [brownianNegativeGerm_tail M]
  simp only [ofPred_forall,ofPred_exists]
  apply MeasurableSet.iInter
  intro N
  apply MeasurableSet.iUnion
  intro n
  by_cases hn : max N M ≤ n
  · simp only [hn,true_and]
    have hmn : M ≤ n := (le_max_right _ _).trans hn
    have hW := (Filtration.stronglyAdapted_natural
      (fun t => (measurable_brownian t).stronglyMeasurable) (brownianProbeTime n)).mono
        ((Filtration.natural brownian (fun t => (measurable_brownian t).stronglyMeasurable)).mono
          (hM n hmn).le)
    exact measurableSet_lt (hW.measurable.const_mul _) measurable_const
  · simp only [hn,false_and,ofPred_false]
    exact @MeasurableSet.empty _ (Filtration.natural brownian
      (fun t => (measurable_brownian t).stronglyMeasurable) s)

theorem brownianNegativeGerm_measurable : MeasurableSet brownianNegativeGerm := by
  have hle : (⨅ s > (0 : ℝ≥0), Filtration.natural brownian
      (fun t => (measurable_brownian t).stronglyMeasurable) s) ≤
      (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)) :=
    (iInf_le_of_le (1 : ℝ≥0) (iInf_le_of_le (by norm_num : (0 : ℝ≥0) < 1) le_rfl)).trans
      ((Filtration.natural brownian (fun t => (measurable_brownian t).stronglyMeasurable)).le 1)
  exact hle _ brownianNegativeGerm_measurable_germ

/-- The continuous test function `max 0 (min 1 (-x-1))`, valued in `[0,1]` and zero on
`-1 ≤ x`. -/
noncomputable def negativeProbeTest (x : ℝ) : ℝ := max 0 (min 1 (-x-1))

theorem negativeProbeTest_continuous : Continuous negativeProbeTest := by
  unfold negativeProbeTest
  fun_prop

theorem negativeProbeTest_bounds (x : ℝ) : 0 ≤ negativeProbeTest x ∧ negativeProbeTest x ≤ 1 :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

theorem negativeProbeTest_zero {x : ℝ} (hx : -1 ≤ x) : negativeProbeTest x = 0 := by
  unfold negativeProbeTest
  rw [max_eq_left]
  exact (min_le_right _ _).trans (by linarith)

theorem negativeProbeTest_integral_pos : 0 < ∫ x, negativeProbeTest x ∂gaussianReal 0 1 := by
  letI : (gaussianReal 0 1).IsOpenPosMeasure :=
    (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : ℝ≥0) ≠ 0)).isOpenPosMeasure
  have hi : Integrable negativeProbeTest (gaussianReal 0 1) :=
    (integrable_const (1 : ℝ)).mono_nonneg negativeProbeTest_continuous.aestronglyMeasurable
      (Eventually.of_forall (fun x => (negativeProbeTest_bounds x).1))
      (Eventually.of_forall (fun x => (negativeProbeTest_bounds x).2))
  apply integral_pos_of_integrable_nonneg_nonzero negativeProbeTest_continuous hi
    (fun x => (negativeProbeTest_bounds x).1)
  show negativeProbeTest (-2) ≠ 0
  norm_num [negativeProbeTest]

theorem brownianNegativeGerm_prob_one : gaussianLimit brownianNegativeGerm = 1 := by
  rcases isBrownianReal_brownian.indep_zero measurable_brownian continuous_brownian
    brownianNegativeGerm_measurable_germ with hz | ho
  · have hae : ∀ᵐ ω ∂gaussianLimit, ω ∉ brownianNegativeGerm := by
      rw [ae_iff]
      simpa only [not_not,ofPred_mem_eq] using hz
    have hlim : ∀ᵐ ω ∂gaussianLimit,
        Tendsto (fun n => negativeProbeTest (brownianProbe n ω)) atTop (𝓝 0) := by
      filter_upwards [hae] with ω hω
      have hnot : ¬ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ brownianProbe n ω < -1 := hω
      push Not at hnot
      obtain ⟨N,hN⟩ := hnot
      have he : (fun n => negativeProbeTest (brownianProbe n ω)) =ᶠ[atTop] fun _ => 0 := by
        filter_upwards [eventually_ge_atTop N] with n hn
        exact negativeProbeTest_zero (hN n hn)
      exact tendsto_const_nhds.congr' he.symm
    have hi : Tendsto (fun n => ∫ ω, negativeProbeTest (brownianProbe n ω) ∂gaussianLimit)
        atTop (𝓝 (∫ _ : (ℝ≥0 → ℝ), (0 : ℝ) ∂gaussianLimit)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      · intro n
        exact (negativeProbeTest_continuous.measurable.comp
          ((measurable_brownian _).const_mul _)).aestronglyMeasurable
      · exact integrable_const 1
      · intro n
        apply Eventually.of_forall
        intro ω
        rw [Real.norm_eq_abs,abs_of_nonneg (negativeProbeTest_bounds _).1]
        exact (negativeProbeTest_bounds _).2
      · exact hlim
    have he (n : ℕ) : (∫ ω, negativeProbeTest (brownianProbe n ω) ∂gaussianLimit) =
        ∫ x, negativeProbeTest x ∂gaussianReal 0 1 :=
      (brownianProbe_hasLaw n).integral_comp negativeProbeTest_continuous.aestronglyMeasurable
    simp only [he,integral_zero] at hi
    have hzI : (∫ x, negativeProbeTest x ∂gaussianReal 0 1) = 0 :=
      tendsto_nhds_unique tendsto_const_nhds hi
    exact (negativeProbeTest_integral_pos.ne' hzI).elim
  · exact ho

theorem brownianNegativeGerm_ae : ∀ᵐ ω ∂gaussianLimit, ω ∈ brownianNegativeGerm :=
  (mem_ae_iff_prob_eq_one brownianNegativeGerm_measurable).mpr brownianNegativeGerm_prob_one

theorem brownian_downward_excursion_of_germ {ω : ℝ≥0 → ℝ}
    (hω : ω ∈ brownianNegativeGerm) (μ σ : ℝ) (hσ : 0 < σ)
    {δ : ℝ≥0} (hδ : 0 < δ) :
    ∃ t : ℝ≥0, 0 < t ∧ t < δ ∧ μ*(t : ℝ)+σ*brownian t ω < 0 := by
  have hd : Tendsto (fun n : ℕ => μ/((n : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [mul_zero,mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul μ
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    ((brownianProbeTime_tendsto.eventually (Iio_mem_nhds hδ)).and
      (hd.eventually (Iio_mem_nhds hσ)))
  obtain ⟨n,hn,hneg⟩ := hω N
  obtain ⟨ht,hm⟩ := hN n hn
  refine ⟨brownianProbeTime n,brownianProbeTime_pos n,ht,?_⟩
  have hnp : 0 < (n : ℝ)+1 := by positivity
  have he : (μ*(brownianProbeTime n : ℝ)+σ*brownian (brownianProbeTime n) ω)*((n : ℝ)+1) =
      μ/((n : ℝ)+1)+σ*brownianProbe n ω := by
    simp only [brownianProbeTime,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,
      NNReal.coe_add,NNReal.coe_natCast,brownianProbe]
    field_simp
  apply (mul_lt_mul_iff_left₀ hnp).mp
  rw [he,zero_mul]
  nlinarith [mul_lt_mul_of_pos_left hneg hσ]

/-- One probability-one event supplies every fixed drift, positive volatility,
and positive time window. -/
theorem brownian_downward_excursions_ae : ∀ᵐ ω ∂gaussianLimit,
    ∀ μ σ : ℝ, 0 < σ → ∀ δ : ℝ≥0, 0 < δ →
      ∃ t : ℝ≥0, 0 < t ∧ t < δ ∧ μ*(t : ℝ)+σ*brownian t ω < 0 := by
  filter_upwards [brownianNegativeGerm_ae] with ω hω
  exact fun μ σ hσ _ hδ => brownian_downward_excursion_of_germ hω μ σ hσ hδ

end MathFin.BlackScholes.AmericanPut.Stopping
