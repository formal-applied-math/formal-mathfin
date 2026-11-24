/-
Copyright (c) 2026 Raphael Coelho, Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CommonPairing
public import MathFin.Probability.Brownian.WeightedQuadraticVariation

/-!
# Common Qv

Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Common-filtration extension for Heston, 2026-10-18.

## Main results

* `common_adapted_increment_sq_sub`
* `tendsto_weighted_qv_process_of_ae_continuous`
* `tendsto_weighted_qv_process`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto.CommonQv
open MeasureTheory ProbabilityTheory Filter
open MathFin MathFin.QuadraticVariationL2
open MathFin.FilteredIto.CommonNoise
open scoped NNReal ENNReal Topology
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ}

theorem common_adapted_increment_sq_sub (hB : BrownianOn ℱ B μ)
    {a b c : ℝ≥0} (hac : a ≤ c) (hbc : b ≤ c) (r : ℝ) :
    CommonPairing.AdaptedAt ℱ c (fun ω => (B b ω - B a ω)^2 - r) :=
  ((((hB.adapted b).measurable.mono (ℱ.mono hbc) le_rfl).sub
    ((hB.adapted a).measurable.mono (ℱ.mono hac) le_rfl)).pow_const 2).sub_const r

variable (hB : BrownianOn ℱ B μ)
include hB
omit hB in
private theorem unifPart_le {T : ℝ≥0} {n k : ℕ} (hk : k ≤ n) : unifPart T n k ≤ T := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [unifPart]
  · exact mul_le_of_le_one_left zero_le
      ((div_le_one (Nat.cast_pos.2 hn)).2 (Nat.cast_le.2 hk))

private theorem integral_adapted_mul_centered_sq
    (hBmeas : ∀ t, Measurable (B t)) {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁)
    {χ : Ω → ℝ} (hχ : CommonPairing.AdaptedAt ℱ t₀ χ) :
    ∫ ω, χ ω * ((B t₁ ω - B t₀ ω) ^ 2 - ((t₁ : ℝ) - t₀)) ∂μ = 0 := by
  haveI : IsProbabilityMeasure μ := hB.law.isGaussianProcess.isProbabilityMeasure
  have hχm : Measurable χ := hχ.measurable hBmeas
  have hYm : Measurable (fun ω ↦ (B t₁ ω - B t₀ ω) ^ 2 - ((t₁ : ℝ) - t₀)) := by fun_prop
  have hindep : IndepFun χ (fun ω ↦ (B t₁ ω - B t₀ ω) ^ 2 - ((t₁ : ℝ) - t₀)) μ := by
    have h := (hB.independent ht hχ).comp
      measurable_id (by fun_prop : Measurable (fun x : ℝ ↦ x ^ 2 - ((t₁ : ℝ) - t₀)))
    simpa [Function.comp_def] using h
  rw [hindep.integral_fun_mul_eq_mul_integral hχm.aestronglyMeasurable hYm.aestronglyMeasurable,
      integral_increment_centered_mean hB.law ht, mul_zero]

private theorem weighted_fluctuation_integral_le
    (hBmeas : ∀ t, Measurable (B t))
    {w : ℝ≥0 → Ω → ℝ} (hw_adapt : ∀ s, CommonPairing.AdaptedAt ℱ s (w s))
    {C : ℝ} (hC : 0 ≤ C) (hw_bdd : ∀ s ω, |w s ω| ≤ C) (T : ℝ≥0) (n : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range n,
        w (unifPart T n k) ω
          * ((B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
             - ((unifPart T n (k + 1) : ℝ) - unifPart T n k))) ^ 2 ∂μ
      ≤ ∑ k ∈ Finset.range n,
          C ^ 2 * (2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 2) := by
  haveI : IsProbabilityMeasure μ := hB.law.isGaussianProcess.isProbabilityMeasure
  have hmono : Monotone (unifPart T n) := fun i j hij ↦ by simp only [unifPart]; gcongr
  set t : ℕ → ℝ≥0 := unifPart T n
  set Y : ℕ → Ω → ℝ := fun k ω ↦ (B (t (k + 1)) ω - B (t k) ω) ^ 2 - ((t (k + 1) : ℝ) - t k)
    with hY_def
  set a : ℕ → Ω → ℝ := fun k ω ↦ w (t k) ω * Y k ω with ha_def
  have hw_meas : ∀ s, Measurable (w s) := fun s ↦ (hw_adapt s).measurable hBmeas
  have hYL2 : ∀ k, MemLp (Y k) 2 μ := fun k ↦ memLp_increment_sq_centered_two hB.law (t k) (t (k
        + 1)) _
  have ha_aesm : ∀ k, AEStronglyMeasurable (a k) μ := fun k ↦
    (hw_meas (t k)).aestronglyMeasurable.mul (hYL2 k).aestronglyMeasurable
  have haL2 : ∀ k, MemLp (a k) 2 μ := fun k ↦
    MemLp.mono ((hYL2 k).const_mul C) (ha_aesm k) (ae_of_all _ fun ω ↦ by
      simp only [ha_def, Real.norm_eq_abs, abs_mul]
      rw [abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hw_bdd _ _) (abs_nonneg _))
  have hint : ∀ k l, Integrable (fun ω ↦ a k ω * a l ω) μ :=
    fun k l ↦ (haL2 k).integrable_mul (haL2 l)
  have hY_adapt : ∀ k, CommonPairing.AdaptedAt ℱ (t (k + 1)) (Y k) := fun k ↦
    common_adapted_increment_sq_sub hB (hmono (Nat.le_succ k)) le_rfl _
  have ha_adapt : ∀ k, CommonPairing.AdaptedAt ℱ (t (k + 1)) (a k) := fun k ↦
    ((hw_adapt (t k)).mono (hmono (Nat.le_succ k))).mul (hY_adapt k)
  have hcross : ∀ k ∈ Finset.range n, ∀ l ∈ Finset.range n, l ≠ k →
      ∫ ω, a k ω * a l ω ∂μ = 0 := by
    intro k _ l _ hlk
    rcases lt_or_gt_of_ne hlk with hlt | hgt
    · have hχ : CommonPairing.AdaptedAt ℱ (t k) (fun ω ↦ a l ω * w (t k) ω) :=
        ((ha_adapt l).mono (hmono (Nat.succ_le_of_lt hlt))).mul (hw_adapt (t k))
      have h := integral_adapted_mul_centered_sq hB hBmeas (hmono (Nat.le_succ k)) hχ
      rw [show (fun ω ↦ a k ω * a l ω)
            = (fun ω ↦ (a l ω * w (t k) ω)
                * ((B (t (k + 1)) ω - B (t k) ω) ^ 2 - ((t (k + 1) : ℝ) - t k)))
          from funext fun ω ↦ by simp only [ha_def, hY_def]; ring]
      exact h
    · have hχ : CommonPairing.AdaptedAt ℱ (t l) (fun ω ↦ a k ω * w (t l) ω) :=
        ((ha_adapt k).mono (hmono (Nat.succ_le_of_lt hgt))).mul (hw_adapt (t l))
      have h := integral_adapted_mul_centered_sq hB hBmeas (hmono (Nat.le_succ l)) hχ
      rw [show (fun ω ↦ a k ω * a l ω)
            = (fun ω ↦ (a k ω * w (t l) ω)
                * ((B (t (l + 1)) ω - B (t l) ω) ^ 2 - ((t (l + 1) : ℝ) - t l)))
          from funext fun ω ↦ by simp only [ha_def, hY_def]; ring]
      exact h
  have hdiag : ∀ k ∈ Finset.range n,
      ∫ ω, a k ω * a k ω ∂μ ≤ C ^ 2 * (2 * ((t (k + 1) : ℝ) - t k) ^ 2) := by
    intro k _
    have hgsq : ∀ ω, (w (t k) ω) ^ 2 ≤ C ^ 2 := fun ω ↦ by
      nlinarith [hw_bdd (t k) ω, abs_nonneg (w (t k) ω), sq_abs (w (t k) ω)]
    have hle : ∀ ω, a k ω * a k ω ≤ C ^ 2 * (Y k ω * Y k ω) := fun ω ↦ by
      simp only [ha_def]
      nlinarith [hgsq ω, mul_self_nonneg (Y k ω)]
    calc ∫ ω, a k ω * a k ω ∂μ
        ≤ ∫ ω, C ^ 2 * (Y k ω * Y k ω) ∂μ :=
          integral_mono (hint k k) (((hYL2 k).integrable_mul (hYL2 k)).const_mul _) hle
      _ = C ^ 2 * ∫ ω, Y k ω * Y k ω ∂μ := integral_const_mul _ _
      _ = C ^ 2 * (2 * ((t (k + 1) : ℝ) - t k) ^ 2) := by
          rw [show (fun ω ↦ Y k ω * Y k ω)
                = (fun ω ↦ ((B (t (k + 1)) ω - B (t k) ω) ^ 2 - ((t (k + 1) : ℝ) - t k)) ^ 2)
              from funext fun ω ↦ by simp only [hY_def]; ring,
              integral_increment_sq_centered hB.law (hmono (Nat.le_succ k))]
  calc ∫ ω, (∑ k ∈ Finset.range n, a k ω) ^ 2 ∂μ
      = ∫ ω, ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, a k ω * a l ω ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
        show (∑ k ∈ Finset.range n, a k ω) ^ 2
          = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, a k ω * a l ω
        rw [sq, Finset.sum_mul_sum]
    _ = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, ∫ ω, a k ω * a l ω ∂μ := by
        rw [integral_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun l _ ↦ hint k l]
        exact Finset.sum_congr rfl fun k _ ↦ integral_finsetSum _ fun l _ ↦ hint k l
    _ ≤ ∑ k ∈ Finset.range n, C ^ 2 * (2 * ((t (k + 1) : ℝ) - t k) ^ 2) := by
        refine Finset.sum_le_sum fun k hk ↦ ?_
        rw [Finset.sum_eq_single k (fun l hl hlk ↦ hcross k hk l hl hlk) fun h ↦ absurd hk h]
        exact hdiag k hk

private theorem tendsto_weighted_fluctuation
    (hBmeas : ∀ t, Measurable (B t))
    {w : ℝ≥0 → Ω → ℝ} (hw_adapt : ∀ s, CommonPairing.AdaptedAt ℱ s (w s))
    {C : ℝ} (hC : 0 ≤ C) (hw_bdd : ∀ s ω, |w s ω| ≤ C) (T : ℝ≥0) :
    Tendsto (fun n : ℕ ↦
        ∫ ω, (∑ k ∈ Finset.range n,
            w (unifPart T n k) ω
              * ((B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
                 - ((unifPart T n (k + 1) : ℝ) - unifPart T n k))) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  refine squeeze_zero' (g := fun n : ℕ ↦ 2 * C ^ 2 * (T : ℝ) ^ 2 / n)
    (Eventually.of_forall fun n ↦ integral_nonneg fun ω ↦ sq_nonneg _) ?_
    (by simpa using tendsto_const_div_atTop_nhds_zero_nat (2 * C ^ 2 * (T : ℝ) ^ 2))
  filter_upwards [eventually_gt_atTop 0] with n hn
  refine (weighted_fluctuation_integral_le hB hBmeas hw_adapt hC hw_bdd T n).trans (le_of_eq ?_)
  have hΔ : ∀ k ∈ Finset.range n, ((unifPart T n (k + 1) : ℝ) - unifPart T n k) = (T : ℝ) / n :=
    fun k _ ↦ by simp only [unifPart]; push_cast; field_simp; ring
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [show (∑ k ∈ Finset.range n, C ^ 2 * (2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 2))
        = ∑ _k ∈ Finset.range n, C ^ 2 * (2 * ((T : ℝ) / n) ^ 2)
      from Finset.sum_congr rfl fun k hk ↦ by rw [hΔ k hk],
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

theorem tendsto_weighted_qv_process_of_ae_continuous
    (hBmeas : ∀ t, Measurable (B t))
    {w : ℝ≥0 → Ω → ℝ} (hw_adapt : ∀ s, CommonPairing.AdaptedAt ℱ s (w s))
    {C : ℝ} (hC0 : 0 ≤ C) (hw_bdd : ∀ s ω, |w s ω| ≤ C) (T : ℝ≥0)
    (hw_cont : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦ w s ω) (Set.Icc 0 T)) :
    Tendsto (fun n : ℕ ↦
        ∫ ω, (∑ k ∈ Finset.range n,
                w (unifPart T n k) ω
                  * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
              - ∫ s in Set.Ioc 0 T, w s ω ∂ItoIntegralL2.timeMeasure) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  haveI : IsProbabilityMeasure μ := hB.law.isGaussianProcess.isProbabilityMeasure
  have hw_meas : ∀ s, Measurable (w s) := fun s ↦ (hw_adapt s).measurable hBmeas
  set Ssum : ℕ → Ω → ℝ := fun n ω ↦ ∑ k ∈ Finset.range n,
      w (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2 with hSsum
  set Rsum : ℕ → Ω → ℝ := fun n ω ↦ ∑ k ∈ Finset.range n,
      w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) with hRsum
  set Ipath : Ω → ℝ := fun ω ↦ ∫ s in Set.Ioc 0 T, w s ω ∂ItoIntegralL2.timeMeasure with hIpath
  show Tendsto (fun n ↦ ∫ ω, (Ssum n ω - Ipath ω) ^ 2 ∂μ) atTop (𝓝 0)

  have hTermI : Tendsto (fun n ↦ ∫ ω, (Ssum n ω - Rsum n ω) ^ 2 ∂μ) atTop (𝓝 0) := by
    refine (tendsto_congr fun n ↦ ?_).mp
      (tendsto_weighted_fluctuation hB hBmeas hw_adapt hC0 hw_bdd T)
    refine integral_congr_ae (Eventually.of_forall fun ω ↦ ?_)
    show (∑ k ∈ Finset.range n, w (unifPart T n k) ω
          * ((B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
            - ((unifPart T n (k + 1) : ℝ) - unifPart T n k))) ^ 2 = (Ssum n ω - Rsum n ω) ^ 2
    have hbase : (∑ k ∈ Finset.range n, w (unifPart T n k) ω
          * ((B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
            - ((unifPart T n (k + 1) : ℝ) - unifPart T n k))) = Ssum n ω - Rsum n ω := by
      simp only [hSsum, hRsum]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    rw [hbase]

  obtain ⟨v, hv_meas, hv_cont, hv_bdd, hv⟩ :=
    exists_continuous_version_of_ae_continuousOn hw_meas T hw_cont hC0 hw_bdd
  have hvw : ∀ᵐ ω ∂μ, ∀ n, (∑ k ∈ Finset.range n,
        v (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)
      - ∫ s in Set.Ioc 0 T, v s ω ∂ItoIntegralL2.timeMeasure) ^ 2 = (Rsum n ω - Ipath ω) ^ 2 := by
    filter_upwards [hv] with ω hω n
    rw [Finset.sum_congr rfl fun k hk ↦ by
        rw [hω _ (unifPart_le (Finset.mem_range.mp hk).le)],
      setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ hω s hs.2]
  have hTermII : Tendsto (fun n ↦ ∫ ω, (Rsum n ω - Ipath ω) ^ 2 ∂μ) atTop (𝓝 0) :=
    (tendsto_riemann_L2_process hv_meas hv_cont hC0 hv_bdd T).congr fun n ↦
      integral_congr_ae (hvw.mono fun ω h ↦ h n)

  have hInt_I : ∀ n, Integrable (fun ω ↦ (Ssum n ω - Rsum n ω) ^ 2) μ := by
    intro n
    have heq : (fun ω ↦ Ssum n ω - Rsum n ω) = fun ω ↦ ∑ k ∈ Finset.range n,
        w (unifPart T n k) ω * ((B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
          - ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) := by
      funext ω
      rw [hSsum, hRsum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    have hmemS : MemLp (fun ω ↦ Ssum n ω - Rsum n ω) 2 μ := by
      rw [heq]
      refine memLp_finsetSum _ fun k _ ↦ ?_
      have hZ : MemLp (fun ω ↦ (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
          - ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) 2 μ :=
        memLp_increment_sq_centered_two hB.law (unifPart T n k) (unifPart T n (k + 1)) _
      have haesm : AEStronglyMeasurable (fun ω ↦ w (unifPart T n k) ω
          * ((B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
            - ((unifPart T n (k + 1) : ℝ) - unifPart T n k))) μ :=
        (hw_meas _).aestronglyMeasurable.mul hZ.aestronglyMeasurable
      refine MemLp.mono (hZ.const_mul C) haesm (Eventually.of_forall fun ω ↦ ?_)
      simp only [Real.norm_eq_abs, abs_mul]
      rw [abs_of_nonneg hC0]
      exact mul_le_mul_of_nonneg_right (hw_bdd _ _) (abs_nonneg _)
    have hsq : (fun ω ↦ (Ssum n ω - Rsum n ω) ^ 2)
        = fun ω ↦ (Ssum n ω - Rsum n ω) * (Ssum n ω - Rsum n ω) := by funext ω; ring
    rw [hsq]; exact hmemS.integrable_mul hmemS
  have hInt_II : ∀ n, Integrable (fun ω ↦ (Rsum n ω - Ipath ω) ^ 2) μ := fun n ↦
    (integrable_riemann_defect_sq hv_meas hv_cont hC0 hv_bdd T n).congr (hvw.mono fun ω h ↦ h n)

  have hupper : Tendsto (fun n ↦ 2 * ∫ ω, (Ssum n ω - Rsum n ω) ^ 2 ∂μ
      + 2 * ∫ ω, (Rsum n ω - Ipath ω) ^ 2 ∂μ) atTop (𝓝 0) := by
    simpa using (hTermI.const_mul 2).add (hTermII.const_mul 2)
  refine squeeze_zero (fun n ↦ integral_nonneg fun ω ↦ sq_nonneg _) (fun n ↦ ?_) hupper
  have hptwise : ∀ ω, (Ssum n ω - Ipath ω) ^ 2
      ≤ 2 * (Ssum n ω - Rsum n ω) ^ 2 + 2 * (Rsum n ω - Ipath ω) ^ 2 := fun ω ↦ by
    nlinarith [sq_nonneg (Ssum n ω - 2 * Rsum n ω + Ipath ω)]
  calc ∫ ω, (Ssum n ω - Ipath ω) ^ 2 ∂μ
      ≤ ∫ ω, (2 * (Ssum n ω - Rsum n ω) ^ 2 + 2 * (Rsum n ω - Ipath ω) ^ 2) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ sq_nonneg _)
          (((hInt_I n).const_mul 2).add ((hInt_II n).const_mul 2))
          (Eventually.of_forall hptwise)
    _ = 2 * ∫ ω, (Ssum n ω - Rsum n ω) ^ 2 ∂μ + 2 * ∫ ω, (Rsum n ω - Ipath ω) ^ 2 ∂μ := by
        rw [integral_add ((hInt_I n).const_mul 2) ((hInt_II n).const_mul 2),
          integral_const_mul, integral_const_mul]

theorem tendsto_weighted_qv_process
    (hBmeas : ∀ t, Measurable (B t))
    {w : ℝ≥0 → Ω → ℝ} (hw_adapt : ∀ s, CommonPairing.AdaptedAt ℱ s (w s))
    (hw_cont : ∀ ω, Continuous fun s ↦ w s ω)
    {C : ℝ} (hC0 : 0 ≤ C) (hw_bdd : ∀ s ω, |w s ω| ≤ C) (T : ℝ≥0) :
    Tendsto (fun n : ℕ ↦
        ∫ ω, (∑ k ∈ Finset.range n,
                w (unifPart T n k) ω
                  * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
              - ∫ s in Set.Ioc 0 T, w s ω ∂ItoIntegralL2.timeMeasure) ^ 2 ∂μ)
      atTop (𝓝 0) :=
  tendsto_weighted_qv_process_of_ae_continuous hB hBmeas hw_adapt hC0 hw_bdd T
    (Eventually.of_forall fun ω ↦ (hw_cont ω).continuousOn)

end MathFin.FilteredIto.CommonQv
