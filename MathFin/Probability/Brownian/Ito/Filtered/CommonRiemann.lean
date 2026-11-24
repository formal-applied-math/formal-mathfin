/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CommonStopping
public import MathFin.Probability.Brownian.Ito.Filtered.CommonQv

/-!
# Riemann–Stieltjes sums of common-filtration stochastic integrals

Along the uniform partition `tₖ = kT/n` of `[0, T]`, for a bounded adapted weight `w`
with a.s. continuous paths and an `L²` kernel `φ`,

  `∑ₖ w(tₖ)·(M_{tₖ₊₁} − M_{tₖ}) → ∫₀ᵀ w φ dB`   in `L²(μ)`,

where `M` is the continuous version of `∫ φ dB`. The left side is exactly the integral of
the frozen kernel `∑ₖ w(tₖ)·𝟙_{(tₖ,tₖ₊₁]}·φ` (locality of the integral), and the frozen
kernels converge to `w φ` in `L²(trim_T)` by dominated convergence.

## Main definitions

* `frozenFactor`
* `frozenKernel`
* `mulKernel`

## Main results

* `itoIntegralCLM_T_frozenKernel`
* `frozenSum_eq_itoIntegral`
* `tendsto_riemannStieltjes`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto
namespace CommonRiemann

open MeasureTheory ProbabilityTheory Filter Topology
open MathFin.FilteredIto.CommonNoise MathFin.FilteredIto.CommonL2
      MathFin.FilteredIto.CommonPredictable MathFin.FilteredIto.CommonIntegral
  MathFin.FilteredIto.CommonProcessGeneral MathFin.FilteredIto.CommonContinuous
        MathFin.FilteredIto.CommonLocality
  MathFin.FilteredIto.CommonStopping
open MathFin (unifPart)
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ}

/-! ### The uniform partition -/

lemma unifPart_eq_gridPt (T : ℝ≥0) (n k : ℕ) : unifPart T n k = gridPt T n k := by
  unfold unifPart gridPt
  rw [div_mul_eq_mul_div, mul_div_assoc]

lemma upart_zero (T : ℝ≥0) (n : ℕ) : unifPart T n 0 = 0 := by
  rw [unifPart_eq_gridPt, gridPt_zero]

lemma upart_self (T : ℝ≥0) {n : ℕ} (hn : 0 < n) : unifPart T n n = T := by
  rw [unifPart_eq_gridPt, gridPt_self T hn]

lemma upart_mono (T : ℝ≥0) (n : ℕ) {j k : ℕ} (h : j ≤ k) : unifPart T n j ≤ unifPart T n k := by
  rw [unifPart_eq_gridPt, unifPart_eq_gridPt]
  exact gridPt_mono T n h

lemma upart_le (T : ℝ≥0) {n k : ℕ} (hk : k ≤ n) : unifPart T n k ≤ T := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [unifPart]
  · rw [unifPart_eq_gridPt]
    exact gridPt_le T hn hk

lemma upart_succ (T : ℝ≥0) (n k : ℕ) : unifPart T n (k + 1) = unifPart T n k + T / n := by
  rw [unifPart_eq_gridPt, unifPart_eq_gridPt, gridPt_succ]

/-! ### Almost-everywhere statements for the predictable measure -/

/-- A predictable-measurable property that holds, for every time `s ∈ (0, T]`, for almost
every `ω`, holds `trim_T`-almost everywhere. -/
lemma ae_trim_of_forall_ae {T : ℝ≥0} {P : ℝ≥0 × Ω → Prop}
    (hP : MeasurableSet[ℱ.predictable] {p | P p})
    (h : ∀ s ∈ Set.Ioc 0 T, ∀ᵐ ω ∂μ, P (s, ω)) :
    ∀ᵐ p ∂(trimMeasureT (μ := μ) T ℱ), P p := by
  have hprod : ∀ᵐ p ∂((timeMeasureT T).prod μ), P p := by
    rw [Measure.ae_prod_iff_ae_ae (ℱ.predictable_le_prod _ hP), timeMeasureT,
      ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun s hs => h s hs
  rw [ae_iff] at hprod ⊢
  rw [trimMeasureT, trim_measurableSet_eq _
    (show MeasurableSet[ℱ.predictable] {a | ¬ P a} from hP.compl)]
  exact hprod

/-- A `trim_T`-almost-everywhere property holds, for almost every time `s ∈ (0,T]`, for
almost every `ω`. -/
lemma ae_ae_of_ae_trim' {T : ℝ≥0} {P : ℝ≥0 × Ω → Prop}
    (h : ∀ᵐ p ∂(trimMeasureT (μ := μ) T ℱ), P p) :
    ∀ᵐ s ∂(timeMeasureT T), ∀ᵐ ω ∂μ, P (s, ω) :=
  Measure.ae_ae_of_ae_prod (ae_of_ae_trim ℱ.predictable_le_prod h)

/-! ### Frozen factors and frozen kernels -/

/-- The frozen step factor `∑ₖ w(tₖ)·𝟙_{(tₖ,tₖ₊₁]}(s)`, written with switched-on factors so
that it is visibly predictable. -/
def frozenFactor (T : ℝ≥0) (n : ℕ) (w : ℝ≥0 → Ω → ℝ) (p : ℝ≥0 × Ω) : ℝ :=
  ∑ k ∈ Finset.range n, (afterFactor (unifPart T n k) (w (unifPart T n k)) p
    - afterFactor (unifPart T n (k + 1)) (w (unifPart T n k)) p)

omit mΩ in
lemma frozenFactor_eq (T : ℝ≥0) (n : ℕ) (w : ℝ≥0 → Ω → ℝ) (p : ℝ≥0 × Ω) :
    frozenFactor T n w p = ∑ k ∈ Finset.range n,
      w (unifPart T n k) p.2 * bandInd (gridPt T n k) (gridPt T n (k + 1)) p.1 := by
  unfold frozenFactor
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [afterFactor, bandInd, ← unifPart_eq_gridPt]
  split_ifs <;> ring

lemma measurable_frozenFactor (T : ℝ≥0) (n : ℕ) (hBmeas : ∀ u, Measurable (B u))
    {w : ℝ≥0 → Ω → ℝ} (hw : ∀ t, Measurable[ℱ t] (w t)) :
    Measurable[ℱ.predictable] (frozenFactor T n w) := by
  unfold frozenFactor
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (measurable_afterFactor hBmeas (hw _)).sub
    (measurable_afterFactor hBmeas ((hw _).mono (ℱ.mono (upart_mono T n (Nat.le_succ k))) le_rfl))

omit mΩ in
lemma abs_frozenFactor_le (T : ℝ≥0) {n : ℕ} (hn : 0 < n) {w : ℝ≥0 → Ω → ℝ} {C : ℝ}
    (hC : ∀ t ω, |w t ω| ≤ C) (p : ℝ≥0 × Ω) : |frozenFactor T n w p| ≤ C := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 p.2)
  rw [frozenFactor_eq]
  have hb : ∀ k, 0 ≤ bandInd (gridPt T n k) (gridPt T n (k + 1)) p.1 :=
    fun k => bandInd_nonneg (gridPt_mono T n (Nat.le_succ k)) p.1
  calc |∑ k ∈ Finset.range n, w (unifPart T n k) p.2 * bandInd (gridPt T n k) (gridPt T n (k +
        1)) p.1|
      ≤ ∑ k ∈ Finset.range n, |w (unifPart T n k) p.2 * bandInd (gridPt T n k) (gridPt T n (k +
            1)) p.1| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, C * bandInd (gridPt T n k) (gridPt T n (k + 1)) p.1 := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul, abs_of_nonneg (hb k)]
        exact mul_le_mul_of_nonneg_right (hC _ _) (hb k)
    _ = C * ((if 0 < p.1 then 1 else 0) - (if T < p.1 then 1 else 0)) := by
        rw [← Finset.mul_sum, sum_bandInd T hn p.1]
    _ ≤ C := by
        have : (if (0 : ℝ≥0) < p.1 then (1 : ℝ) else 0) - (if T < p.1 then 1 else 0) ≤ 1 := by
          split_ifs <;> norm_num
        exact mul_le_of_le_one_right hC0 this

omit mΩ in
/-- **Pointwise convergence of frozen factors** at a time `s ∈ (0, T]` of continuity. -/
lemma tendsto_frozenFactor (T : ℝ≥0) {w : ℝ≥0 → Ω → ℝ} {s : ℝ≥0} (hs : s ∈ Set.Ioc 0 T)
    {ω : Ω} (hc : ContinuousOn (fun t ↦ w t ω) (Set.Icc 0 T)) :
    Tendsto (fun n ↦ frozenFactor T n w (s, ω)) atTop (𝓝 (w s ω)) := by
  have hsI : s ∈ Set.Icc 0 T := ⟨zero_le, hs.2⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousWithinAt_iff.mp (hc s hsI) (ε / 2) (half_pos hε)
  have h0 : Tendsto (fun n : ℕ ↦ T / (n : ℝ≥0)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat T
  have hev := (tendsto_order.1 h0).2 (Real.toNNReal (δ / 2)) (Real.toNNReal_pos.mpr (half_pos hδ))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max N₀ 1, fun n hn => ?_⟩
  have hn1 : 0 < n := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hn)
  have hnT : T / (n : ℝ≥0) < Real.toNNReal (δ / 2) := hN₀ n (le_trans (le_max_left _ _) hn)
  have hsum : ∑ k ∈ Finset.range n, bandInd (gridPt T n k) (gridPt T n (k + 1)) s = 1 := by
    rw [sum_bandInd T hn1 s, ite_eq_left hs.1, ite_eq_right (not_lt.mpr hs.2), sub_zero]
  have hb : ∀ k, 0 ≤ bandInd (gridPt T n k) (gridPt T n (k + 1)) s :=
    fun k => bandInd_nonneg (gridPt_mono T n (Nat.le_succ k)) s
  have hdiff : frozenFactor T n w (s, ω) - w s ω = ∑ k ∈ Finset.range n,
      (w (unifPart T n k) ω - w s ω) * bandInd (gridPt T n k) (gridPt T n (k + 1)) s := by
    rw [frozenFactor_eq]
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_one]
  have hterm : ∀ k ∈ Finset.range n, |(w (unifPart T n k) ω - w s ω)
      * bandInd (gridPt T n k) (gridPt T n (k + 1)) s|
        ≤ ε / 2 * bandInd (gridPt T n k) (gridPt T n (k + 1)) s := by
    intro k hk
    rw [abs_mul, abs_of_nonneg (hb k)]
    by_cases hband : gridPt T n k < s ∧ ¬ gridPt T n (k + 1) < s
    · refine mul_le_mul_of_nonneg_right ?_ (hb k)
      have hk' : unifPart T n k ∈ Set.Icc 0 T :=
        ⟨zero_le, upart_le T (Nat.le_of_lt_succ (Nat.lt_succ_of_lt (Finset.mem_range.mp hk)))⟩
      have hdist : dist (unifPart T n k) s < δ := by
        rw [unifPart_eq_gridPt]
        have h1 : gridPt T n k < s := hband.1
        have h2 : s ≤ gridPt T n k + T / n := by
          rw [← gridPt_succ]; exact not_lt.mp hband.2
        rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (by
          have := NNReal.coe_le_coe.mpr h1.le; linarith)]
        have h2' : (s : ℝ) ≤ gridPt T n k + (T / n : ℝ≥0) := by exact_mod_cast h2
        have h3 : ((T / (n : ℝ≥0) : ℝ≥0) : ℝ) < δ / 2 := Real.lt_toNNReal_iff_coe_lt.mp hnT
        linarith
      have := hδε hk' hdist
      rw [Real.dist_eq] at this
      exact this.le
    · have hz : bandInd (gridPt T n k) (gridPt T n (k + 1)) s = 0 := by
        unfold bandInd
        by_cases h1 : gridPt T n k < s
        · have h2 : gridPt T n (k + 1) < s := by
            by_contra h2; exact hband ⟨h1, h2⟩
          simp [h1, h2]
        · have h2 : ¬ gridPt T n (k + 1) < s :=
            fun h2 => h1 (lt_of_le_of_lt (gridPt_mono T n (Nat.le_succ k)) h2)
          simp [h1, h2]
      simp [hz]
  rw [Real.dist_eq, hdiff]
  calc |∑ k ∈ Finset.range n, (w (unifPart T n k) ω - w s ω)
        * bandInd (gridPt T n k) (gridPt T n (k + 1)) s|
      ≤ ∑ k ∈ Finset.range n, |(w (unifPart T n k) ω - w s ω)
        * bandInd (gridPt T n k) (gridPt T n (k + 1)) s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, ε / 2 * bandInd (gridPt T n k) (gridPt T n (k + 1)) s :=
        Finset.sum_le_sum hterm
    _ = ε / 2 := by rw [← Finset.mul_sum, hsum, mul_one]
    _ < ε := half_lt_self hε

/-- The frozen kernel `∑ₖ w(tₖ)·𝟙_{(tₖ,tₖ₊₁]}·φ`. -/
noncomputable def frozenKernel (T : ℝ≥0) (n : ℕ) (hBmeas : ∀ u, Measurable (B u))
    (w : ℝ≥0 → Ω → ℝ) (hw : ∀ t, Measurable[ℱ t] (w t)) (C : ℝ) (hC : ∀ t ω, |w t ω| ≤ C)
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ) :=
  ∑ k ∈ Finset.range n, smulAdapted T (unifPart T n k) hBmeas (w (unifPart T n k))
    (hw _) C (fun ω ↦ hC _ ω) (band T (unifPart T n k) (unifPart T n (k + 1)) hBmeas φ)

omit [IsProbabilityMeasure μ] in
lemma coeFn_frozenKernel (T : ℝ≥0) (n : ℕ) (hBmeas : ∀ u, Measurable (B u))
    (w : ℝ≥0 → Ω → ℝ) (hw : ∀ t, Measurable[ℱ t] (w t)) (C : ℝ) (hC : ∀ t ω, |w t ω| ≤ C)
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    ⇑(frozenKernel T n hBmeas w hw C hC φ) =ᵐ[trimMeasureT (μ := μ) T ℱ]
      fun p ↦ frozenFactor T n w p * φ p := by
  have hterm : ∀ k ∈ Finset.range n,
      ⇑(smulAdapted T (unifPart T n k) hBmeas (w (unifPart T n k)) (hw _) C (fun ω ↦ hC _ ω)
        (band T (unifPart T n k) (unifPart T n (k + 1)) hBmeas φ))
      =ᵐ[trimMeasureT (μ := μ) T ℱ] fun p ↦
        (afterFactor (unifPart T n k) (w (unifPart T n k)) p
          - afterFactor (unifPart T n (k + 1)) (w (unifPart T n k)) p) * φ p := by
    intro k _
    have hmono := upart_mono T n (Nat.le_succ k)
    filter_upwards [coeFn_smulAdapted_afterFactor T (unifPart T n k) hBmeas
      (w (unifPart T n k)) (hw _) C (fun ω ↦ hC _ ω)
      (band T (unifPart T n k) (unifPart T n (k + 1)) hBmeas φ),
      coeFn_band T (unifPart T n k) (unifPart T n (k + 1)) hBmeas φ] with p h1 h2
    rw [h1, h2]
    simp only [afterFactor]
    by_cases ha : unifPart T n k < p.1
    · by_cases hb : unifPart T n (k + 1) < p.1
      · simp only [ha, hb, ite_true]; ring
      · simp only [ha, hb, ite_true, ite_false]; ring
    · have hb : ¬ unifPart T n (k + 1) < p.1 := fun hb => ha (lt_of_le_of_lt hmono hb)
      simp only [ha, hb, ite_false]; ring
  have hall := (Filter.eventually_all_finset (Finset.range n)).mpr hterm
  filter_upwards [Lp.coeFn_finsetSum (Finset.range n) (fun k ↦ smulAdapted T (unifPart T n k)
      hBmeas (w (unifPart T n k)) (hw _) C (fun ω ↦ hC _ ω)
      (band T (unifPart T n k) (unifPart T n (k + 1)) hBmeas φ)), hall] with p h1 h2
  rw [frozenKernel, h1, Finset.sum_apply, frozenFactor, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k hk => h2 k hk

/-- The limit kernel `w·φ`, for a predictable bounded weight. -/
noncomputable def mulKernel (T : ℝ≥0) {w : ℝ≥0 → Ω → ℝ}
    (hwP : Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω ↦ w p.1 p.2)) {C : ℝ}
    (hC : ∀ t ω, |w t ω| ≤ C) (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ) :=
  mulBddCLM (trimMeasureT (μ := μ) T ℱ) hwP (fun p ↦ hC p.1 p.2) φ

omit [IsProbabilityMeasure μ] in
lemma coeFn_mulKernel (T : ℝ≥0) {w : ℝ≥0 → Ω → ℝ}
    (hwP : Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω ↦ w p.1 p.2)) {C : ℝ}
    (hC : ∀ t ω, |w t ω| ≤ C) (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    ⇑(mulKernel T hwP hC φ) =ᵐ[trimMeasureT (μ := μ) T ℱ] fun p ↦ w p.1 p.2 * φ p :=
  coeFn_mulBddCLM _ _ _ φ

/-- **Frozen kernels converge** to `w·φ` in `L²(trim_T)` when the paths of `w` are a.s.
continuous on `[0, T]`. -/
theorem tendsto_frozenKernel (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    {w : ℝ≥0 → Ω → ℝ} (hw : ∀ t, Measurable[ℱ t] (w t))
    (hwP : Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω ↦ w p.1 p.2)) {C : ℝ}
    (hC : ∀ t ω, |w t ω| ≤ C) (hcont : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ w t ω) (Set.Icc 0 T))
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    Tendsto (fun n : ℕ ↦ frozenKernel T n hBmeas w hw C hC φ) atTop
      (𝓝 (mulKernel T hwP hC φ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set F : ℕ → ℝ≥0 × Ω → ℝ := fun n p ↦
    ((frozenKernel T n hBmeas w hw C hC φ - mulKernel T hwP hC φ : Lp ℝ 2 _) p) ^ 2 with hF
  have hcoe : ∀ᵐ p ∂(trimMeasureT (μ := μ) T ℱ), ∀ n : ℕ,
      F n p = ((frozenFactor T n w p - w p.1 p.2) * φ p) ^ 2 := by
    rw [ae_all_iff]
    intro n
    filter_upwards [Lp.coeFn_sub (frozenKernel T n hBmeas w hw C hC φ) (mulKernel T hwP hC φ),
      coeFn_frozenKernel T n hBmeas w hw C hC φ, coeFn_mulKernel T hwP hC φ] with p h1 h2 h3
    simp only [hF]
    rw [h1, Pi.sub_apply, h2, h3]
    ring
  -- pointwise convergence of the frozen factor, trim-almost everywhere
  have hconv : ∀ᵐ p ∂(trimMeasureT (μ := μ) T ℱ),
      Tendsto (fun n ↦ frozenFactor T n w p - w p.1 p.2) atTop (𝓝 0) := by
    refine ae_trim_of_forall_ae ?_ ?_
    · exact measurableSet_tendsto (𝓝 0) fun n =>
        (measurable_frozenFactor T n hBmeas hw).sub hwP
    · intro s hs
      filter_upwards [hcont] with ω hω
      have := (tendsto_frozenFactor T hs hω).sub_const (w s ω)
      simpa using this
  have hint : Tendsto (fun n ↦ ∫ p, F n p ∂(trimMeasureT (μ := μ) T ℱ)) atTop (𝓝 0) := by
    have key := tendsto_integral_of_dominated_convergence (μ := trimMeasureT (μ := μ) T ℱ)
      (F := F) (f := fun _ => (0 : ℝ)) (fun p ↦ (2 * C) ^ 2 * (φ p) ^ 2)
      (fun n => (Lp.aestronglyMeasurable _).pow 2)
      ((Lp.memLp φ).integrable_sq.const_mul _)
      (fun n => by
        filter_upwards [hcoe] with p hp
        rw [hp n, Real.norm_eq_abs, abs_pow, abs_mul, mul_pow, sq_abs, sq_abs]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        obtain ⟨h2a, h2b⟩ := abs_le.mp (hC p.1 p.2)
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp only [frozenFactor, Finset.range_zero, Finset.sum_empty, zero_sub, neg_sq]
          nlinarith
        · obtain ⟨h1a, h1b⟩ := abs_le.mp (abs_frozenFactor_le T hn hC p)
          nlinarith)
      (by
        filter_upwards [hcoe, hconv] with p hp hc
        have : Tendsto (fun n ↦ ((frozenFactor T n w p - w p.1 p.2) * φ p) ^ 2) atTop
            (𝓝 ((0 * φ p) ^ 2)) := ((hc.mul_const _).pow 2)
        simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
        exact this.congr fun n => (hp n).symm)
    simpa using key
  have hsq : ∀ n : ℕ, ‖frozenKernel T n hBmeas w hw C hC φ - mulKernel T hwP hC φ‖ ^ 2
      = ∫ p, F n p ∂(trimMeasureT (μ := μ) T ℱ) := fun n => MathFin.lp_two_norm_sq _
  have h2 : Tendsto (fun n : ℕ ↦ ‖frozenKernel T n hBmeas w hw C hC φ - mulKernel T hwP hC φ‖ ^ 2)
      atTop (𝓝 0) := by
    simp_rw [hsq]; exact hint
  have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
  simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at h3
  exact h3

variable (hB : BrownianOn ℱ B μ)
include hB

/-- The integral of a frozen kernel is the frozen Riemann–Stieltjes sum. -/
theorem itoIntegralCLM_T_frozenKernel (T : ℝ≥0) (n : ℕ) (hBmeas : ∀ u, Measurable (B u))
    (w : ℝ≥0 → Ω → ℝ) (hw : ∀ t, Measurable[ℱ t] (w t)) (C : ℝ) (hC : ∀ t ω, |w t ω| ≤ C)
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    (itoIntegralCLMT hB T (frozenKernel T n hBmeas w hw C hC φ) : Ω → ℝ)
      =ᵐ[μ] fun ω ↦ ∑ k ∈ Finset.range n, w (unifPart T n k) ω *
        (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas φ ω
          - itoProcessCLM hB T (unifPart T n k) hBmeas φ ω) := by
  rw [← itoProcessCLM_terminal_eq hB T hBmeas, frozenKernel, map_sum]
  have hterm : ∀ k ∈ Finset.range n,
      (itoProcessCLM hB T T hBmeas (smulAdapted T (unifPart T n k) hBmeas (w (unifPart T n k))
        (hw _) C (fun ω ↦ hC _ ω) (band T (unifPart T n k) (unifPart T n (k + 1)) hBmeas φ))
        : Ω → ℝ)
      =ᵐ[μ] fun ω ↦ w (unifPart T n k) ω *
        (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas φ ω
          - itoProcessCLM hB T (unifPart T n k) hBmeas φ ω) := by
    intro k hk
    have hk1 : k + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
    have hbT := upart_le T hk1
    have hab := upart_mono T n (Nat.le_succ k)
    have h := itoProcessCLM_smulAdapted_band hB T _ _ T hab hbT le_rfl hBmeas
      (w (unifPart T n k)) (hw _) C (fun ω ↦ hC _ ω) φ
    rwa [min_eq_left hbT, min_eq_left (hab.trans hbT)] at h
  have hall := (Filter.eventually_all_finset (Finset.range n)).mpr hterm
  filter_upwards [Lp.coeFn_finsetSum (Finset.range n) (fun k ↦ itoProcessCLM hB T T hBmeas
      (smulAdapted T (unifPart T n k) hBmeas (w (unifPart T n k)) (hw _) C (fun ω ↦ hC _ ω)
        (band T (unifPart T n k) (unifPart T n (k + 1)) hBmeas φ))), hall] with ω h1 h2
  rw [h1, Finset.sum_apply]
  exact Finset.sum_congr rfl fun k hk => h2 k hk

/-- The frozen sum written with the continuous version `M` of the integral. -/
theorem frozenSum_eq_itoIntegral (T : ℝ≥0) (n : ℕ) (hBmeas : ∀ u, Measurable (B u))
    (hBcont : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω)
    (w : ℝ≥0 → Ω → ℝ) (hw : ∀ t, Measurable[ℱ t] (w t)) (C : ℝ) (hC : ∀ t ω, |w t ω| ≤ C)
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    (fun ω ↦ ∑ k ∈ Finset.range n, w (unifPart T n k) ω *
        (itoContinuousMod T hBmeas φ (unifPart T n (k + 1)) ω
          - itoContinuousMod T hBmeas φ (unifPart T n k) ω))
      =ᵐ[μ] (itoIntegralCLMT hB T (frozenKernel T n hBmeas w hw C hC φ) : Ω → ℝ) := by
  have hmod : ∀ k ∈ Finset.range (n + 1),
      (fun ω ↦ itoContinuousMod T hBmeas φ (unifPart T n k) ω)
        =ᵐ[μ] itoProcessCLM hB T (unifPart T n k) hBmeas φ :=
    fun k hk ↦ itoContinuousMod_modification hB T hBmeas hBcont φ
      (upart_le T (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
  have hall := (Filter.eventually_all_finset (Finset.range (n + 1))).mpr hmod
  filter_upwards [hall, itoIntegralCLM_T_frozenKernel hB T n hBmeas w hw C hC φ] with ω h1 h2
  rw [h2]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [← h1 (k + 1) (Finset.mem_range.mpr (Nat.succ_lt_succ hk')),
    ← h1 k (Finset.mem_range.mpr (Nat.lt_succ_of_lt hk'))]

/-- **Riemann–Stieltjes convergence.** For a bounded adapted predictable weight `w` with a.s.
continuous paths, `∑ₖ w(tₖ)(M_{tₖ₊₁} − M_{tₖ}) → ∫₀ᵀ w φ dB` in `L²(μ)`. -/
theorem tendsto_riemannStieltjes (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (hBcont : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω)
    {w : ℝ≥0 → Ω → ℝ} (hw : ∀ t, Measurable[ℱ t] (w t))
    (hwP : Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω ↦ w p.1 p.2)) {C : ℝ}
    (hC : ∀ t ω, |w t ω| ≤ C) (hcont : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ w t ω) (Set.Icc 0 T))
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    Tendsto (fun n : ℕ ↦ ∫ ω, (∑ k ∈ Finset.range n, w (unifPart T n k) ω *
        (itoContinuousMod T hBmeas φ (unifPart T n (k + 1)) ω
          - itoContinuousMod T hBmeas φ (unifPart T n k) ω)
        - itoIntegralCLMT hB T (mulKernel T hwP hC φ) ω) ^ 2 ∂μ) atTop (𝓝 0) := by
  have hL : Tendsto (fun n : ℕ ↦ itoIntegralCLMT hB T (frozenKernel T n hBmeas w hw C hC φ))
      atTop (𝓝 (itoIntegralCLMT hB T (mulKernel T hwP hC φ))) :=
    ((itoIntegralCLMT hB T).continuous.tendsto _).comp
      (tendsto_frozenKernel T hBmeas hw hwP hC hcont φ)
  have hn : Tendsto (fun n : ℕ ↦ ‖itoIntegralCLMT hB T (frozenKernel T n hBmeas w hw C hC φ)
      - itoIntegralCLMT hB T (mulKernel T hwP hC φ)‖ ^ 2) atTop (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp hL).pow 2
    simpa using this
  refine hn.congr fun n => ?_
  rw [MathFin.lp_two_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (itoIntegralCLMT hB T (frozenKernel T n hBmeas w hw C hC φ))
      (itoIntegralCLMT hB T (mulKernel T hwP hC φ)),
    frozenSum_eq_itoIntegral hB T n hBmeas hBcont w hw C hC φ] with ω h1 h2
  rw [h1, Pi.sub_apply, ← h2]

end CommonRiemann
end MathFin.FilteredIto
