/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.DriftRiemannConvergence
public import MathFin.Foundations.ItoProcessPredictable

/-! # The drift of an Itô process with adapted coefficients

The drift part of the adapted-coefficient Itô formula (`ItoFormulaAdapted`). For a bounded adapted
drift rate `b` with continuous paths, the pathwise integral `A_t = ∫₀ᵗ b_s ds` is taken as it stands, with no
modification:

* it is Lipschitz in time with the bound of `b` as constant, on every path
  (`abs_driftPath_sub_le`), which is the hypothesis the quadratic variation
  `AdaptedQuadraticVariation.tendsto_qv_adapted` asks of a drift;
* it is adapted, as a limit of Riemann sums of `𝓕_t`-measurable values, and so predictable, being
  continuous (`driftPath_isStronglyPredictable`);
* for each `ω` and each bounded `g : ℝ≥0 → ℝ` continuous on `[0, T]`, its Riemann–Stieltjes
  sums converge: `∑ₖ g(tₖ)·(A_{tₖ₊₁} − A_{tₖ}) → ∫₀ᵀ g_s b_s ds`
  (`tendsto_sum_mul_driftPath_sub`), the drift half of the formula's first-order term.
-/

@[expose] public section

namespace MathFin
namespace AdaptedDrift

open MeasureTheory ProbabilityTheory Filter Topology
open ItoIntegralL2 ItoIntegralBrownian ItoIntegralRiemannBridge QuadraticVariationL2
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ} (hBmeas : ∀ t, Measurable (B t))
  {b : ℝ≥0 → Ω → ℝ}
  (hb_adap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (b t))
  (hb_cont : ∀ ω, Continuous fun s ↦ b s ω) {Cb : ℝ} (hb_bdd : ∀ s ω, |b s ω| ≤ Cb)

/-- The drift path `A_t = ∫₀ᵗ b_s ds`, the pathwise integral of the drift rate. -/
noncomputable def driftPath (b : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in Set.Ioc 0 t, b s ω ∂timeMeasure

omit mΩ in
include hb_cont hb_bdd in
/-- A bounded continuous path is integrable over a bounded interval of time. -/
theorem integrableOn_Ioc (u t : ℝ≥0) (ω : Ω) :
    IntegrableOn (fun s ↦ b s ω) (Set.Ioc u t) timeMeasure :=
  Measure.integrableOn_of_bounded (by rw [timeMeasure_Ioc]; exact ENNReal.ofReal_ne_top)
    (hb_cont ω).aestronglyMeasurable (ae_of_all _ fun s ↦ (Real.norm_eq_abs _).trans_le (hb_bdd s ω))

omit mΩ in
include hb_cont hb_bdd in
/-- The increment of the drift path over `(s, t]` is the integral of the rate over it. -/
theorem driftPath_sub {s t : ℝ≥0} (hst : s ≤ t) (ω : Ω) :
    driftPath b t ω - driftPath b s ω = ∫ x in Set.Ioc s t, b x ω ∂timeMeasure := by
  rw [driftPath, driftPath, ← Set.Ioc_union_Ioc_eq_Ioc zero_le hst,
    setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (integrableOn_Ioc hb_cont hb_bdd 0 s ω) (integrableOn_Ioc hb_cont hb_bdd s t ω),
    add_sub_cancel_left]

omit mΩ in
include hb_cont hb_bdd in
/-- **The drift path is Lipschitz in time**, with the bound of the rate as its constant. -/
theorem abs_driftPath_sub_le ⦃s t : ℝ≥0⦄ (hst : s ≤ t) (ω : Ω) :
    |driftPath b t ω - driftPath b s ω| ≤ Cb * ((t : ℝ) - s) := by
  rw [driftPath_sub hb_cont hb_bdd hst, ← Real.norm_eq_abs]
  refine (norm_setIntegral_le_of_norm_le_const (by rw [timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top)
    fun x _ ↦ (Real.norm_eq_abs _).trans_le (hb_bdd x ω)).trans_eq ?_
  rw [measureReal_def, timeMeasure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.2 (NNReal.coe_le_coe.2 hst))]

omit mΩ in
include hb_cont hb_bdd in
/-- Every drift path is continuous. -/
theorem continuous_driftPath (ω : Ω) : Continuous fun t ↦ driftPath b t ω := by
  have hCb : 0 ≤ Cb := (abs_nonneg _).trans (hb_bdd 0 ω)
  refine (LipschitzWith.of_dist_le_mul (K := Cb.toNNReal) fun s t ↦ ?_).continuous
  rw [Real.dist_eq, NNReal.dist_eq, Real.coe_toNNReal _ hCb]
  rcases le_total t s with h | h
  · exact (abs_driftPath_sub_le hb_cont hb_bdd h ω).trans_eq
      (by rw [abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 h))])
  · rw [abs_sub_comm, abs_sub_comm (s : ℝ)]
    exact (abs_driftPath_sub_le hb_cont hb_bdd h ω).trans_eq
      (by rw [abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 h))])

include hb_adap hb_cont hb_bdd in
/-- **The drift path is adapted**: `A_t` is the limit of Riemann sums of values `b(tₖ)` with
`tₖ ≤ t`, each `𝓕_t`-measurable. -/
theorem stronglyMeasurable_driftPath (t : ℝ≥0) :
    StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (driftPath b t) := by
  have hmeas (n : ℕ) : StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)]
      fun ω ↦ ∑ k ∈ Finset.range n,
        b (unifPart t n k) ω * ((unifPart t n (k + 1) : ℝ) - unifPart t n k) :=
    Finset.stronglyMeasurable_fun_sum _ fun k hk ↦ ((hb_adap _).mono ((natFiltration hBmeas).mono
      (unifPart_le_T (Finset.mem_range.mp hk).le))).mul_const _
  letI : MeasurableSpace Ω := natFiltration hBmeas t
  exact stronglyMeasurable_of_tendsto atTop hmeas (tendsto_pi_nhds.2 fun ω ↦
    tendsto_riemannSum_setIntegral (hb_cont ω) (fun s ↦ hb_bdd s ω) t)

include hb_adap hb_cont hb_bdd in
/-- **The drift path is predictable**: adapted, with continuous paths. -/
theorem driftPath_isStronglyPredictable :
    IsStronglyPredictable (natFiltration hBmeas) (driftPath b) :=
  StronglyAdapted.isStronglyPredictable_of_leftContinuous
    (stronglyMeasurable_driftPath hBmeas hb_adap hb_cont hb_bdd)
    fun ω _ ↦ (continuous_driftPath hb_cont hb_bdd ω).continuousWithinAt

omit mΩ in
include hb_cont hb_bdd in
/-- **Riemann–Stieltjes sums against the drift path converge**, for each `ω` and each bounded
`g : ℝ≥0 → ℝ` continuous on `[0, T]`: `∑ₖ g(tₖ)·(A_{tₖ₊₁} − A_{tₖ}) → ∫₀ᵀ g_s b_s ds`. The
sum is the integral of the left-endpoint step function of `g` against `b ds`, and the step
functions converge on `(0, T]` under the bound of `g` (`tendsto_sum_indicator_unifPart`). -/
theorem tendsto_sum_mul_driftPath_sub (T : ℝ≥0) (ω : Ω) {g : ℝ≥0 → ℝ}
    (hg : ContinuousOn g (Set.Icc 0 T)) {Cg : ℝ} (hg_bdd : ∀ s, |g s| ≤ Cg) :
    Tendsto (fun n ↦ ∑ k ∈ Finset.range n, g (unifPart T n k)
        * (driftPath b (unifPart T n (k + 1)) ω - driftPath b (unifPart T n k) ω)) atTop
      (𝓝 (∫ s in Set.Ioc 0 T, g s * b s ω ∂timeMeasure)) := by
  have hCg : 0 ≤ Cg := (abs_nonneg _).trans (hg_bdd 0)
  have hCb : 0 ≤ Cb := (abs_nonneg _).trans (hb_bdd 0 ω)
  haveI : IsFiniteMeasure (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)) :=
    ⟨by rw [Measure.restrict_apply_univ, timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  set F : ℕ → ℝ≥0 → ℝ := fun n s ↦ ∑ j ∈ Finset.range n,
    (Set.Ioc (unifPart T n j) (unifPart T n (j + 1))).indicator (fun _ ↦ g (unifPart T n j)) s
  have hFm (n : ℕ) : Measurable (F n) :=
    Finset.measurable_fun_sum _ fun j _ ↦ measurable_const.indicator measurableSet_Ioc
  -- each sum is the integral of the step function against `b ds`
  have hsum (n : ℕ) : ∑ k ∈ Finset.range n, g (unifPart T n k)
        * (driftPath b (unifPart T n (k + 1)) ω - driftPath b (unifPart T n k) ω)
      = ∫ s in Set.Ioc 0 T, F n s * b s ω ∂timeMeasure := by
    have hint (j : ℕ) : Integrable (fun s ↦
        (Set.Ioc (unifPart T n j) (unifPart T n (j + 1))).indicator (fun _ ↦ g (unifPart T n j)) s
          * b s ω) (timeMeasure.restrict (Set.Ioc 0 T)) :=
      (integrable_const (Cg * Cb)).mono'
        ((measurable_const.indicator measurableSet_Ioc).aestronglyMeasurable.mul
          (hb_cont ω).aestronglyMeasurable)
        (ae_of_all _ fun s ↦ by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          refine mul_le_mul ?_ (hb_bdd s ω) (abs_nonneg _) hCg
          by_cases h : s ∈ Set.Ioc (unifPart T n j) (unifPart T n (j + 1))
          · simpa only [Set.indicator_of_mem h] using hg_bdd _
          · simpa only [Set.indicator_of_notMem h, abs_zero] using hCg)
    simp only [F, Finset.sum_mul]
    rw [integral_finsetSum _ fun j _ ↦ hint j]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hcell : Set.Ioc 0 T ∩ Set.Ioc (unifPart T n k) (unifPart T n (k + 1))
        = Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) :=
      Set.inter_eq_right.2 (Set.Ioc_subset_Ioc zero_le (unifPart_le_T (Finset.mem_range.mp hk)))
    have hind : (fun s ↦ (Set.Ioc (unifPart T n k) (unifPart T n (k + 1))).indicator
          (fun _ ↦ g (unifPart T n k)) s * b s ω)
        = (Set.Ioc (unifPart T n k) (unifPart T n (k + 1))).indicator
          fun s ↦ g (unifPart T n k) * b s ω := by
      funext s
      by_cases hs : s ∈ Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) <;> simp [hs]
    rw [driftPath_sub hb_cont hb_bdd (unifPart_mono T n (Nat.le_succ k)), ← integral_const_mul,
      hind, setIntegral_indicator measurableSet_Ioc, hcell]
  simp only [hsum]
  refine tendsto_integral_of_dominated_convergence (fun _ ↦ Cg * Cb)
    (fun n ↦ (hFm n).aestronglyMeasurable.mul (hb_cont ω).aestronglyMeasurable)
    (integrable_const _) (fun n ↦ ?_) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (abs_sum_indicator_unifPart_le T n hs hCg hg_bdd) (hb_bdd s ω)
      (abs_nonneg _) hCg
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact (tendsto_sum_indicator_unifPart T hs (hg s ⟨hs.1.le, hs.2⟩)).mul_const _

end AdaptedDrift

end MathFin
