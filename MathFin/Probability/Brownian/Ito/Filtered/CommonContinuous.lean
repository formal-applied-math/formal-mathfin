/-
Copyright (c) 2026 Raphael Coelho, Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CommonProcessGeneral
public import MathFin.Probability.Brownian.Ito.Filtered.CommonProcessLocalMartingale
public import BrownianMotion.StochasticIntegral.DoobLp

/-!
# Common Continuous

Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Common-filtration extension for Heston, 2026-10-18.

## Main definitions

* `itoContinuousMod`

## Main results

* `consecutive_norm_le`
* `itoContinuousMod_continuousOn`
* `exists_continuous_modification_itoProcess`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open MathFin.FilteredIto.CommonNoise
open scoped NNReal ENNReal
namespace MathFin.FilteredIto
namespace CommonContinuous

open CommonL2 CommonPredictable CommonIntegral CommonProcess CommonProcessGeneral

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ} (hB : IsFilteredPreBrownian
        B ℱ μ)

include hB

theorem itoSimpleProcess_maximal_weak (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (V : SimpleProcess ℝ ℱ) (T : ℝ≥0) (ε : ℝ) :
    ε • μ.real {ω | ε ≤ ⨆ i : Set.Iic T, ‖itoSimpleProcess hBmeas V i ω‖}
      ≤ ∫ ω in {ω | ε ≤ ⨆ i : Set.Iic T, ‖itoSimpleProcess hBmeas V i ω‖},
          ‖itoSimpleProcess hBmeas V T ω‖ ∂μ :=
  maximal_ineq_norm (itoSimpleProcess_isMartingale hB hBmeas V) ε T
    (fun ω _ ↦ (itoSimpleProcess_pathContinuous hBmeas hBcont V ω).continuousWithinAt)

theorem itoSimpleProcess_maximal_prob (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (T : ℝ≥0) (V : TBoundedSP T ℱ) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ε ≤ ⨆ i : Set.Iic T, ‖itoSimpleProcess hBmeas V.val i ω‖}
      ≤ ε⁻¹ * ‖simpleAssemblyT (μ := μ) T ℱ V‖ := by
  set f := itoSimpleProcess hBmeas V.val T
  set S := {ω | ε ≤ ⨆ i : Set.Iic T, ‖itoSimpleProcess hBmeas V.val i ω‖}
  have hf : MemLp f 2 μ := memLp_itoSimpleProcess hB hBmeas V.val T
  have hfi : Integrable f μ := hf.integrable (by norm_num)
  have hweak := itoSimpleProcess_maximal_weak hB hBmeas hBcont V.val T ε

  have hsub : ∫ ω in S, ‖f ω‖ ∂μ ≤ ∫ ω, ‖f ω‖ ∂μ :=
    setIntegral_le_integral hfi.norm (ae_of_all _ fun ω ↦ norm_nonneg _)

  have hL2 : ∫ ω, ‖f ω‖ ∂μ ≤ ‖itoSimpleProcessLp hB hBmeas V.val T‖ := by
    rw [itoSimpleProcessLp, Lp.norm_toLp,
      ← ENNReal.toReal_ofReal (integral_nonneg fun ω ↦ norm_nonneg _),
      ofReal_integral_norm_eq_lintegral_enorm hfi,
      ← eLpNorm_one_eq_lintegral_enorm hfi.aestronglyMeasurable]
    exact ENNReal.toReal_mono hf.eLpNorm_lt_top.ne (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))

  have hterm : ‖itoSimpleProcessLp hB hBmeas V.val T‖ = ‖simpleAssemblyT (μ := μ) T ℱ V‖ := by
    rw [← itoProcessCLM_simpleAssembly_T hB T T hBmeas V, itoProcessCLM_norm_terminal hB T hBmeas]

  rw [smul_eq_mul] at hweak
  have hchain : ε * μ.real S ≤ ‖simpleAssemblyT (μ := μ) T ℱ V‖ :=
    hweak.trans (hsub.trans (hL2.trans_eq hterm))
  calc μ.real S = ε⁻¹ * (ε * μ.real S) := by
        rw [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]
    _ ≤ ε⁻¹ * ‖simpleAssemblyT (μ := μ) T ℱ V‖ :=
        mul_le_mul_of_nonneg_left hchain (inv_nonneg.mpr hε.le)

omit hB in

theorem approxSeq (T : ℝ≥0) (_hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    ∃ V : ℕ → TBoundedSP T ℱ,
      ∀ n, ‖simpleAssemblyT (μ := μ) T ℱ (V n) - φ‖ ≤ (2⁻¹ : ℝ) ^ n := by
  have hd := simpleAssembly_T_denseRange (μ := μ) T ℱ
  have hex : ∀ n : ℕ, ∃ V : TBoundedSP T ℱ,
      ‖simpleAssemblyT (μ := μ) T ℱ V - φ‖ ≤ (2⁻¹ : ℝ) ^ n := by
    intro n
    obtain ⟨V, hV⟩ := hd.exists_dist_lt φ (by positivity : (0 : ℝ) < (2⁻¹ : ℝ) ^ n)
    exact ⟨V, by rw [← dist_eq_norm, dist_comm]; exact hV.le⟩
  choose V hV using hex
  exact ⟨V, hV⟩

omit hB in

lemma itoSimpleProcess_sub (hBmeas : ∀ t, Measurable (B t))
    (V W : SimpleProcess ℝ ℱ) (t : ℝ≥0) :
    itoSimpleProcess hBmeas (V - W) t
      = itoSimpleProcess hBmeas V t - itoSimpleProcess hBmeas W t := by
  rw [sub_eq_add_neg, itoSimpleProcess_add, itoSimpleProcess_neg, ← sub_eq_add_neg]

theorem summable_maximal_tail (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) (V : ℕ → TBoundedSP T ℱ)
    (hV : ∀ n, ‖simpleAssemblyT (μ := μ) T ℱ (V n) - φ‖ ≤ (2⁻¹ : ℝ) ^ n) :
    Summable (fun n ↦ μ.real {ω | (3 / 4 : ℝ) ^ n ≤
      ⨆ i : Set.Iic T, ‖itoSimpleProcess hBmeas (V n - V (n + 1)).val i ω‖}) := by
  refine Summable.of_nonneg_of_le (fun n ↦ measureReal_nonneg) (fun n ↦ ?_)
    ((summable_geometric_of_lt_one (r := 2 / 3) (by norm_num) (by norm_num)).mul_left 2)

  refine (itoSimpleProcess_maximal_prob hB hBmeas hBcont T (V n - V (n + 1))
    (ε := (3 / 4 : ℝ) ^ n) (by positivity)).trans ?_
  have hnorm : ‖simpleAssemblyT (μ := μ) T ℱ (V n - V (n + 1))‖ ≤ 2 * (2⁻¹ : ℝ) ^ n := by
    rw [map_sub]
    calc ‖simpleAssemblyT (μ := μ) T ℱ (V n) - simpleAssemblyT (μ := μ) T ℱ (V (n + 1))‖
        ≤ ‖simpleAssemblyT (μ := μ) T ℱ (V n) - φ‖
            + ‖φ - simpleAssemblyT (μ := μ) T ℱ (V (n + 1))‖ := by
          have h := norm_add_le (simpleAssemblyT (μ := μ) T ℱ (V n) - φ)
            (φ - simpleAssemblyT (μ := μ) T ℱ (V (n + 1)))
          simpa using h
      _ ≤ (2⁻¹ : ℝ) ^ n + (2⁻¹ : ℝ) ^ (n + 1) := by
          gcongr
          · exact hV n
          · rw [norm_sub_rev]; exact hV (n + 1)
      _ ≤ 2 * (2⁻¹ : ℝ) ^ n := by
          rw [pow_succ]; linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) n]
  calc ((3 / 4 : ℝ) ^ n)⁻¹ * ‖simpleAssemblyT (μ := μ) T ℱ (V n - V (n + 1))‖
      ≤ ((3 / 4 : ℝ) ^ n)⁻¹ * (2 * (2⁻¹ : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = 2 * (2 / 3 : ℝ) ^ n := by
        rw [← inv_pow, mul_comm (2 : ℝ) ((2⁻¹ : ℝ) ^ n), ← mul_assoc, ← mul_pow,
          show ((3 / 4 : ℝ)⁻¹ * 2⁻¹) = 2 / 3 from by norm_num, mul_comm]

theorem ae_eventually_sup_lt (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) (V : ℕ → TBoundedSP T ℱ)
    (hV : ∀ n, ‖simpleAssemblyT (μ := μ) T ℱ (V n) - φ‖ ≤ (2⁻¹ : ℝ) ^ n) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      (⨆ i : Set.Iic T, ‖itoSimpleProcess hBmeas (V n - V (n + 1)).val i ω‖) < (3 / 4 : ℝ) ^ n := by
  set A : ℕ → Set Ω := fun n ↦ {ω | (3 / 4 : ℝ) ^ n ≤
    ⨆ i : Set.Iic T, ‖itoSimpleProcess hBmeas (V n - V (n + 1)).val i ω‖} with hA
  have hconv : (∑' n, μ (A n)) ≠ ∞ := by
    have heq : ∀ n, μ (A n) = ENNReal.ofReal (μ.real (A n)) :=
      fun n ↦ (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    simp_rw [heq]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ measureReal_nonneg)
      (summable_maximal_tail hB T hBmeas hBcont φ V hV)]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hconv] with ω hω
  filter_upwards [hω] with n hn
  rwa [hA, Set.mem_ofPred_eq, not_le] at hn

omit hB in

lemma norm_le_iSup_Iic (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (W : SimpleProcess ℝ ℱ) (ω : Ω) {i : ℝ≥0} (hi : i ≤ T) :
    ‖itoSimpleProcess hBmeas W i ω‖
      ≤ ⨆ j : Set.Iic T, ‖itoSimpleProcess hBmeas W (j : ℝ≥0) ω‖ := by
  have hcont : Continuous fun j : Set.Iic T ↦ ‖itoSimpleProcess hBmeas W (j : ℝ≥0) ω‖ :=
    (continuous_norm.comp (itoSimpleProcess_pathContinuous hBmeas hBcont W ω)).comp
      continuous_subtype_val
  have hIic : (Set.Iic T : Set ℝ≥0) = Set.Icc 0 T := by
    ext x; simp only [Set.mem_Iic, Set.mem_Icc, zero_le, true_and]
  have : CompactSpace (Set.Iic T) := isCompact_iff_compactSpace.mp (hIic ▸ isCompact_Icc)
  exact le_ciSup (isCompact_range hcont).bddAbove ⟨i, hi⟩

omit hB in

/-- Continuous modification obtained from the approximating simple integrals. -/
noncomputable def itoContinuousMod (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) (t : ℝ≥0) (ω : Ω) : ℝ :=
  limUnder atTop fun n ↦ itoSimpleProcess hBmeas ((approxSeq T hBmeas φ).choose n).val t ω

theorem itoContinuousMod_tendsto (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, t ≤ T →
      Tendsto (fun n ↦ itoSimpleProcess hBmeas ((approxSeq T hBmeas φ).choose n).val t ω) atTop
        (𝓝 (itoContinuousMod T hBmeas φ t ω)) := by
  set V := (approxSeq T hBmeas φ).choose with hVdef
  have hV := (approxSeq T hBmeas φ).choose_spec
  filter_upwards [ae_eventually_sup_lt hB T hBmeas hBcont φ V hV] with ω hω
  intro t ht
  have hcauchy : CauchySeq (fun n ↦ itoSimpleProcess hBmeas (V n).val t ω) := by
    apply cauchySeq_of_summable_dist
    obtain ⟨N, hN⟩ := eventually_atTop.mp hω
    rw [← summable_nat_add_iff N]
    refine Summable.of_nonneg_of_le (fun n ↦ dist_nonneg) (fun n ↦ ?_)
      (f := fun n ↦ (3 / 4 : ℝ) ^ (n + N)) ?_
    · rw [dist_eq_norm]
      have hcoe : ((V (n + N) - V (n + N + 1)).val : SimpleProcess ℝ ℱ)
          = (V (n + N)).val - (V (n + N + 1)).val := rfl
      have hlin : itoSimpleProcess hBmeas (V (n + N)).val t ω
            - itoSimpleProcess hBmeas (V (n + N + 1)).val t ω
          = itoSimpleProcess hBmeas (V (n + N) - V (n + N + 1)).val t ω := by
        rw [hcoe]
        exact (congrFun (itoSimpleProcess_sub hBmeas (V (n + N)).val (V (n + N + 1)).val t) ω).symm
      rw [hlin]
      exact (norm_le_iSup_Iic T hBmeas hBcont (V (n + N) - V (n + N + 1)).val ω ht).trans
        (hN (n + N) (Nat.le_add_left N n)).le
    · simp_rw [pow_add]
      exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  simpa only [itoContinuousMod, hVdef] using hcauchy.tendsto_limUnder

theorem itoContinuousMod_modification (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) {t : ℝ≥0} (ht : t ≤ T) :
    (fun ω ↦ itoContinuousMod T hBmeas φ t ω) =ᵐ[μ] itoProcessCLM hB T t hBmeas φ := by
  set V := (approxSeq T hBmeas φ).choose with hVdef
  have hV := (approxSeq T hBmeas φ).choose_spec
  set F : ℕ → Ω → ℝ := fun n ω ↦ itoSimpleProcess hBmeas (V n).val t ω
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) μ :=
    fun n ↦ (memLp_itoSimpleProcess hB hBmeas (V n).val t).aestronglyMeasurable

  have hmeasG : TendstoInMeasure μ F atTop (fun ω ↦ itoContinuousMod T hBmeas φ t ω) := by
    refine tendstoInMeasure_of_tendsto_ae hFmeas ?_
    filter_upwards [itoContinuousMod_tendsto hB T hBmeas hBcont φ] with ω hω using hω t ht

  have hsa : Tendsto (fun n ↦ simpleAssemblyT (μ := μ) T ℱ (V n)) atTop (𝓝 φ) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n ↦ norm_nonneg _) hV
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  have hLp : Tendsto (fun n ↦ itoSimpleProcessLp hB hBmeas (V n).val t) atTop
      (𝓝 (itoProcessCLM hB T t hBmeas φ)) := by
    have hrw : (fun n ↦ itoSimpleProcessLp hB hBmeas (V n).val t)
        = fun n ↦ itoProcessCLM hB T t hBmeas (simpleAssemblyT (μ := μ) T ℱ (V n)) :=
      funext fun n ↦ (itoProcessCLM_simpleAssembly_T hB T t hBmeas (V n)).symm
    rw [hrw]
    exact ((itoProcessCLM hB T t hBmeas).continuous.tendsto φ).comp hsa
  have heLp : Tendsto (fun n ↦ eLpNorm (F n - ⇑(itoProcessCLM hB T t hBmeas φ)) 2 μ) atTop (𝓝 0)
        := by
    refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F
      (fun n ↦ memLp_itoSimpleProcess hB hBmeas (V n).val t)
      (⇑(itoProcessCLM hB T t hBmeas φ)) (Lp.memLp _)).mp ?_
    simp only [Lp.toLp_coeFn]
    exact hLp
  have hmeasH : TendstoInMeasure μ F atTop (⇑(itoProcessCLM hB T t hBmeas φ)) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) heLp
  exact tendstoInMeasure_ae_unique hmeasG hmeasH

omit hB in

lemma consecutive_norm_le (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) (V : ℕ → TBoundedSP T ℱ)
    (ω : Ω) {t : ℝ≥0} (ht : t ≤ T) (a : ℕ) :
    ‖itoSimpleProcess hBmeas (V a).val t ω - itoSimpleProcess hBmeas (V (a + 1)).val t ω‖
      ≤ ⨆ j : Set.Iic T, ‖itoSimpleProcess hBmeas (V a - V (a + 1)).val (j : ℝ≥0) ω‖ := by
  have hcoe : ((V a - V (a + 1)).val : SimpleProcess ℝ ℱ)
      = (V a).val - (V (a + 1)).val := rfl
  rw [show itoSimpleProcess hBmeas (V a).val t ω - itoSimpleProcess hBmeas (V (a + 1)).val t ω
        = itoSimpleProcess hBmeas (V a - V (a + 1)).val t ω from by
      rw [hcoe]; exact (congrFun (itoSimpleProcess_sub hBmeas (V a).val (V (a + 1)).val t) ω).symm]
  exact norm_le_iSup_Iic T hBmeas hBcont (V a - V (a + 1)).val ω ht

theorem itoContinuousMod_continuousOn (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ itoContinuousMod T hBmeas φ t ω) (Set.Icc 0 T) := by
  set V := (approxSeq T hBmeas φ).choose with hVdef
  have hV := (approxSeq T hBmeas φ).choose_spec
  filter_upwards [ae_eventually_sup_lt hB T hBmeas hBcont φ V hV,
    itoContinuousMod_tendsto hB T hBmeas hBcont φ] with ω hω htends
  rw [show (Set.Icc 0 T : Set ℝ≥0) = Set.Iic T from by
    ext x; simp only [Set.mem_Icc, Set.mem_Iic, zero_le, true_and]]
  obtain ⟨N, hN⟩ := eventually_atTop.mp hω
  have huniform : TendstoUniformlyOn (fun n t ↦ itoSimpleProcess hBmeas (V n).val t ω)
      (fun t ↦ itoContinuousMod T hBmeas φ t ω) atTop (Set.Iic T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have htend0 : Tendsto (fun n ↦ 4 * (3 / 4 : ℝ) ^ n) atTop (𝓝 0) := by
      rw [show (0 : ℝ) = 4 * 0 from by ring]
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul 4
    filter_upwards [eventually_ge_atTop N, htend0.eventually_lt_const hε] with n hn hnε
    intro t ht
    rw [Set.mem_Iic] at ht
    rw [dist_comm]

    have htendsto : Tendsto (fun k ↦ itoSimpleProcess hBmeas (V (k + n)).val t ω) atTop
        (𝓝 (itoContinuousMod T hBmeas φ t ω)) := (htends t ht).comp (tendsto_add_atTop_nat n)
    have hstep : ∀ k, dist (itoSimpleProcess hBmeas (V (k + n)).val t ω)
        (itoSimpleProcess hBmeas (V (k + 1 + n)).val t ω) ≤ (3 / 4 : ℝ) ^ n * (3 / 4 : ℝ) ^ k := by
      intro k
      rw [show k + 1 + n = (k + n) + 1 from by ring, dist_eq_norm]
      refine (consecutive_norm_le T hBmeas hBcont V ω ht (k + n)).trans ?_
      exact (hN (k + n) (hn.trans (Nat.le_add_left n k))).le.trans
        (le_of_eq (by rw [pow_add]; ring))
    have h0 :=
      dist_le_of_le_geometric_of_tendsto₀ (3 / 4) ((3 / 4 : ℝ) ^ n) (by norm_num) hstep htendsto
    simp only [zero_add] at h0
    refine lt_of_le_of_lt (h0.trans (le_of_eq ?_)) hnε
    rw [show (1 : ℝ) - 3 / 4 = 1 / 4 from by norm_num]; ring
  have hcont : ∀ᶠ n in atTop,
      ContinuousOn (fun t ↦ itoSimpleProcess hBmeas (V n).val t ω) (Set.Iic T) :=
    Eventually.of_forall fun n ↦
      (itoSimpleProcess_pathContinuous hBmeas hBcont (V n).val ω).continuousOn
  exact huniform.continuousOn hcont.frequently

theorem exists_continuous_modification_itoProcess (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    ∃ X : ℝ≥0 → Ω → ℝ,
      (∀ t, t ≤ T → X t =ᵐ[μ] itoProcessCLM hB T t hBmeas φ) ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Set.Icc 0 T)) :=
  ⟨itoContinuousMod T hBmeas φ,
    fun _ ht ↦ itoContinuousMod_modification hB T hBmeas hBcont φ ht,
    itoContinuousMod_continuousOn hB T hBmeas hBcont φ⟩

end CommonContinuous
end MathFin.FilteredIto
