/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CommonItoTime
public import MathFin.Probability.Brownian.Ito.Filtered.MartingaleLimit

/-!
# Optional times and stopped Itô integrals on the common filtration

Hitting times of processes whose paths are only almost surely continuous are, without
completing the filtration, merely *optional* times (`{σ < r} ∈ ℱ r`).  This file shows that the
continuous Itô integral evaluated at a bounded optional time is integrable with mean zero
(approximating from above by dyadic stopping times, with a uniform `L²` bound and Vitali's
theorem), and constructs rational-grid exit times with the pathwise properties needed for
localization.  No completeness of the filtration is assumed.

## Main definitions

* `dyadicUpper`
* `ratTimes`
* `exitTime`

## Main results

* `le_of_le_exitTime`
* `exitTime_eq_of_lt`
* `eventually_exitTime_eq`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto
namespace CommonOptional

open MeasureTheory ProbabilityTheory Filter Topology
open MathFin.FilteredIto.CommonNoise MathFin.FilteredIto.CommonPredictable
      MathFin.FilteredIto.CommonIntegral
  MathFin.FilteredIto.CommonProcessGeneral MathFin.FilteredIto.CommonContinuous
        MathFin.FilteredIto.CommonStopping
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}

/-- Optional times: `{σ < r} ∈ ℱ r` for every `r`. -/
def IsOptional (ℱ : Filtration ℝ≥0 mΩ) (σ : Ω → ℝ≥0) : Prop :=
  ∀ r : ℝ≥0, MeasurableSet[ℱ r] {ω | σ ω < r}

/-! ### Dyadic approximation from above -/

/-- Dyadic approximation from above of a random time, capped at `T`. -/
def dyadicUpper (T : ℝ≥0) (k : ℕ) (σ : Ω → ℝ≥0) (ω : Ω) : ℝ≥0 :=
  min T (((⌊(2 : ℝ≥0) ^ k * σ ω⌋₊ : ℝ≥0) + 1) / 2 ^ k)

omit mΩ in
lemma dyadicUpper_le (T : ℝ≥0) (k : ℕ) (σ : Ω → ℝ≥0) (ω : Ω) : dyadicUpper T k σ ω ≤ T :=
  min_le_left _ _

lemma lt_dyadic (k : ℕ) (x : ℝ≥0) : x < ((⌊(2 : ℝ≥0) ^ k * x⌋₊ : ℝ≥0) + 1) / 2 ^ k := by
  have h2 : (0 : ℝ≥0) < 2 ^ k := pow_pos two_pos k
  rw [lt_div_iff₀ h2, mul_comm]
  exact Nat.lt_floor_add_one _

lemma dyadic_le (k : ℕ) (x : ℝ≥0) :
    ((⌊(2 : ℝ≥0) ^ k * x⌋₊ : ℝ≥0) + 1) / 2 ^ k ≤ x + 1 / 2 ^ k := by
  have h2 : (0 : ℝ≥0) < 2 ^ k := pow_pos two_pos k
  rw [div_le_iff₀ h2, add_mul, one_div, inv_mul_cancel₀ h2.ne', mul_comm x]
  exact add_le_add (Nat.floor_le (by positivity)) le_rfl

lemma isStop_dyadicUpper {σ : Ω → ℝ≥0} (hσ : IsOptional ℱ σ) (T : ℝ≥0) (k : ℕ) :
    IsStop ℱ (dyadicUpper T k σ) := by
  intro r
  by_cases hTr : T ≤ r
  · have : {ω | dyadicUpper T k σ ω ≤ r} = Set.univ :=
      Set.eq_univ_of_forall fun ω => (dyadicUpper_le T k σ ω).trans hTr
    rw [this]; exact MeasurableSet.univ
  · replace hTr : r < T := not_le.mp hTr
    have h2 : (0 : ℝ≥0) < 2 ^ k := pow_pos two_pos k
    set rk : ℝ≥0 := (⌊r * 2 ^ k⌋₊ : ℝ≥0) / 2 ^ k with hrk
    have hrkr : rk ≤ r := by
      rw [hrk, div_le_iff₀ h2]; exact Nat.floor_le (by positivity)
    have hset : {ω | dyadicUpper T k σ ω ≤ r} = {ω | σ ω < rk} := by
      ext ω
      simp only [Set.mem_ofPred_eq, dyadicUpper, min_le_iff, not_le.mpr hTr, false_or]
      rw [div_le_iff₀ h2, hrk, lt_div_iff₀ h2]
      constructor
      · intro h
        have h' : ⌊(2 : ℝ≥0) ^ k * σ ω⌋₊ + 1 ≤ ⌊r * 2 ^ k⌋₊ := by
          rw [Nat.le_floor_iff (by positivity)]; exact_mod_cast h
        have h'' : ⌊(2 : ℝ≥0) ^ k * σ ω⌋₊ < ⌊r * 2 ^ k⌋₊ := Nat.lt_of_lt_of_le (Nat.lt_succ_self
              _) h'
        rw [Nat.floor_lt (by positivity)] at h''
        rw [mul_comm (σ ω)]; exact h''
      · intro h
        have h' : ⌊(2 : ℝ≥0) ^ k * σ ω⌋₊ < ⌊r * 2 ^ k⌋₊ := by
          rw [Nat.floor_lt (by positivity), mul_comm ((2 : ℝ≥0) ^ k)]; exact h
        have h'' : ((⌊(2 : ℝ≥0) ^ k * σ ω⌋₊ + 1 : ℕ) : ℝ≥0) ≤ (⌊r * 2 ^ k⌋₊ : ℝ≥0) := by
          exact_mod_cast Nat.succ_le_of_lt h'
        calc ((⌊(2 : ℝ≥0) ^ k * σ ω⌋₊ : ℝ≥0) + 1) = ((⌊(2 : ℝ≥0) ^ k * σ ω⌋₊ + 1 : ℕ) : ℝ≥0) := by
              push_cast; rfl
          _ ≤ (⌊r * 2 ^ k⌋₊ : ℝ≥0) := h''
          _ ≤ r * 2 ^ k := Nat.floor_le (by positivity)
    rw [hset]
    exact ℱ.mono hrkr _ (hσ rk)

omit mΩ in
lemma tendsto_dyadicUpper {T : ℝ≥0} {σ : Ω → ℝ≥0} (hσT : ∀ ω, σ ω ≤ T) (ω : Ω) :
    Tendsto (fun k ↦ dyadicUpper T k σ ω) atTop (𝓝 (σ ω)) := by
  have h0 : Tendsto (fun k : ℕ ↦ (1 : ℝ≥0) / 2 ^ k) atTop (𝓝 0) :=
    (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1 / 2) (by norm_num)).congr
      fun k => one_div_pow (2 : ℝ≥0) k
  have hup : Tendsto (fun k : ℕ ↦ σ ω + 1 / 2 ^ k) atTop (𝓝 (σ ω)) := by
    simpa using (tendsto_const_nhds (x := σ ω)).add h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun k => ?_)
    (fun k => ?_)
  · exact le_min (hσT ω) (lt_dyadic k (σ ω)).le
  · exact (min_le_right _ _).trans (dyadic_le k (σ ω))

/-! ### The Itô integral at an optional time -/

/-- **Optional stopping for continuous Itô integrals.** At a bounded optional time the
continuous Itô integral is integrable with mean zero. -/
theorem itoContinuousMod_optional (hB : IsFilteredPreBrownian B ℱ μ)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) {T : ℝ≥0}
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) {σ : Ω → ℝ≥0}
    (hσ : IsOptional ℱ σ) (hσT : ∀ ω, σ ω ≤ T) :
    Integrable (fun ω ↦ itoContinuousMod T hB.measurable_eval φ (σ ω) ω) μ ∧
      ∫ ω, itoContinuousMod T hB.measurable_eval φ (σ ω) ω ∂μ = 0 := by
  set F : ℕ → Ω → ℝ := fun k ω ↦ itoContinuousMod T hB.measurable_eval φ (dyadicUpper T k σ ω) ω
    with hF
  set G : Ω → ℝ := fun ω ↦ itoContinuousMod T hB.measurable_eval φ (σ ω) ω with hG
  have hτ : ∀ k, IsStop ℱ (dyadicUpper T k σ) := fun k => isStop_dyadicUpper hσ T k
  have hrep : ∀ k, (itoIntegralCLMT hB T (stopKernel T (hτ k) φ) : Ω → ℝ) =ᵐ[μ] F k := by
    intro k
    filter_upwards [itoIntegralCLM_T_stopKernel hB T hB.measurable_eval hBc (hτ k) φ] with ω hω
    rw [hω, min_eq_right (dyadicUpper_le T k σ ω)]
  have hFmeas : ∀ k, AEStronglyMeasurable (F k) μ := fun k =>
    (Lp.aestronglyMeasurable _).congr (hrep k)
  have hFint : ∀ k, Integrable (F k) μ := fun k =>
    ((Lp.memLp _).integrable one_le_two).congr (hrep k)
  have hFzero : ∀ k, ∫ ω, F k ω ∂μ = 0 := fun k => by
    rw [← integral_congr_ae (hrep k)]
    exact integral_itoIntegralCLM_T hB T hB.measurable_eval _
  have hnorm : ∀ k, ‖stopKernel T (hτ k) φ‖ ≤ ‖φ‖ := fun k => by
    have h := Lp.norm_le_mul_norm_of_ae_le_mul (c := 1) (f := stopKernel T (hτ k) φ) (g := φ)
      (by
        filter_upwards [coeFn_stopKernel T (hτ k) φ] with p hp
        rw [hp, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, one_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (abs_stopFactor_le _ p))
    simpa using h
  have hFbd : ∀ k, eLpNorm (F k) 2 μ ≤ (‖φ‖₊ : ℝ≥0∞) := fun k => by
    rw [← eLpNorm_congr_ae (hrep k), ← Lp.enorm_def, enorm_eq_nnnorm]
    refine ENNReal.coe_le_coe.2 ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, itoIntegralCLM_T_norm]
    exact hnorm k
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun k ↦ F k ω) atTop (𝓝 (G ω)) := by
    filter_upwards [itoContinuousMod_continuousOn hB T hB.measurable_eval hBc φ] with ω hω
    have hcw := hω (σ ω) ⟨(zero_le : (0 : ℝ≥0) ≤ σ ω), hσT ω⟩
    have ht : Tendsto (fun k ↦ dyadicUpper T k σ ω) atTop (𝓝[Set.Icc 0 T] (σ ω)) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_dyadicUpper hσT ω, Eventually.of_forall fun k =>
        ⟨(zero_le : (0 : ℝ≥0) ≤ _), dyadicUpper_le T k σ ω⟩⟩
    exact hcw.tendsto.comp ht
  have hGmeas : AEStronglyMeasurable G μ := aestronglyMeasurable_of_tendsto_ae atTop hFmeas hlim
  have hUI := uniformIntegrable_one_of_eLpNorm_bdd (p := 2) ENNReal.one_lt_two ENNReal.ofNat_ne_top
    hFmeas ‖φ‖₊ hFbd
  have hGint : Integrable G μ := memLp_one_iff_integrable.1 (hUI.memLp_of_ae_tendsto hlim)
  have hL1 := tendsto_Lp_finite_of_tendsto_ae (p := 1) le_rfl ENNReal.one_ne_top hFmeas
    (hUI.memLp_of_ae_tendsto hlim) hUI.unifIntegrable hlim
  have hconv := tendsto_integral_of_L1' G (Eventually.of_forall hFint) hL1
  refine ⟨hGint, ?_⟩
  have h0 : Tendsto (fun k ↦ ∫ ω, F k ω ∂μ) atTop (𝓝 0) := by
    simp only [hFzero]; exact tendsto_const_nhds
  exact tendsto_nhds_unique hconv h0

/-! ### Rational-grid exit times -/

/-- The nonnegative rational times. -/
def ratTimes : Set ℝ≥0 := Set.range fun q : ℚ ↦ Real.toNNReal q

lemma countable_ratTimes : ratTimes.Countable := Set.countable_range _

lemma exists_ratTimes_between {a b : ℝ≥0} (hab : a < b) : ∃ q ∈ ratTimes, a < q ∧ q < b := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (a : ℝ) < b from hab)
  have hq0 : (0 : ℝ) ≤ q := a.2.trans hq1.le
  refine ⟨Real.toNNReal q, ⟨q, rfl⟩, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]; exact hq1
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]; exact hq2

/-- First rational time in `[0, T]` at which `g ≥ n`, or `T` if there is none. -/
def exitTime (T : ℝ≥0) (g : ℝ≥0 → Ω → ℝ) (n : ℝ) (ω : Ω) : ℝ≥0 :=
  sInf (insert T {q | q ∈ ratTimes ∧ q ≤ T ∧ n ≤ g q ω})

omit mΩ in
lemma exitTime_le (T : ℝ≥0) (g : ℝ≥0 → Ω → ℝ) (n : ℝ) (ω : Ω) : exitTime T g n ω ≤ T :=
  csInf_le (OrderBot.bddBelow _) (Set.mem_insert _ _)

omit mΩ in
lemma exitTime_le_of_mem {T : ℝ≥0} {g : ℝ≥0 → Ω → ℝ} {n : ℝ} {ω : Ω} {q : ℝ≥0}
    (hq : q ∈ ratTimes) (hqT : q ≤ T) (hn : n ≤ g q ω) : exitTime T g n ω ≤ q :=
  csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _ ⟨hq, hqT, hn⟩)

omit mΩ in
lemma exitTime_lt_iff {T : ℝ≥0} {g : ℝ≥0 → Ω → ℝ} {n : ℝ} {ω : Ω} {r : ℝ≥0} :
    exitTime T g n ω < r ↔ T < r ∨ ∃ q ∈ ratTimes, q ≤ T ∧ n ≤ g q ω ∧ q < r := by
  unfold exitTime
  rw [csInf_lt_iff (OrderBot.bddBelow _) (Set.insert_nonempty _ _)]
  constructor
  · rintro ⟨b, hb, hbr⟩
    rcases hb with rfl | ⟨hq, hqT, hn⟩
    · exact Or.inl hbr
    · exact Or.inr ⟨b, hq, hqT, hn, hbr⟩
  · rintro (h | ⟨q, hq, hqT, hn, hqr⟩)
    · exact ⟨T, Set.mem_insert _ _, h⟩
    · exact ⟨q, Set.mem_insert_of_mem _ ⟨hq, hqT, hn⟩, hqr⟩

/-- Rational exit times of adapted processes are optional times. -/
lemma isOptional_exitTime {g : ℝ≥0 → Ω → ℝ} (hg : ∀ t, Measurable[ℱ t] (g t)) (T : ℝ≥0)
    (n : ℝ) : IsOptional ℱ (exitTime T g n) := by
  intro r
  have hset : {ω | exitTime T g n ω < r} = {ω | T < r} ∪
      ⋃ q ∈ {q : ℝ≥0 | q ∈ ratTimes ∧ q ≤ T ∧ q < r}, {ω | n ≤ g q ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion, exitTime_lt_iff, exists_prop]
    constructor
    · rintro (h | ⟨q, hq, hqT, hn, hqr⟩)
      · exact Or.inl h
      · exact Or.inr ⟨q, ⟨hq, hqT, hqr⟩, hn⟩
    · rintro (h | ⟨q, ⟨hq, hqT, hqr⟩, hn⟩)
      · exact Or.inl h
      · exact Or.inr ⟨q, hq, hqT, hn, hqr⟩
  rw [hset]
  refine MeasurableSet.union ?_ ?_
  · by_cases h : T < r
    · simp only [h, Set.ofPred_true]; exact @MeasurableSet.univ Ω (ℱ r)
    · simp only [h, Set.ofPred_false]; exact @MeasurableSet.empty Ω (ℱ r)
  · refine MeasurableSet.biUnion (countable_ratTimes.mono fun q hq => hq.1) fun q hq => ?_
    exact ℱ.mono hq.2.2.le _ (hg q measurableSet_Ici)

omit mΩ in
/-- Before a rational exit time, a path that is continuous on `[0, T]` and starts below the
level stays below the level. -/
lemma le_of_le_exitTime {T : ℝ≥0} {g : ℝ≥0 → Ω → ℝ} {n : ℝ} {ω : Ω}
    (hc : ContinuousOn (fun t ↦ g t ω) (Set.Icc 0 T)) (h0 : g 0 ω < n)
    {s : ℝ≥0} (hs : s ≤ exitTime T g n ω) : g s ω ≤ n := by
  by_contra hgt'
  have hgt : n < g s ω := not_le.mp hgt'
  have hsT : s ≤ T := hs.trans (exitTime_le T g n ω)
  have hspos : 0 < s := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with h | h
    · rw [← h] at hgt; linarith
    · exact h
  have hev : ∀ᶠ t in 𝓝[Set.Icc 0 T] s, n < g t ω :=
    (hc s ⟨zero_le, hsT⟩).eventually (lt_mem_nhds hgt)
  have hsub : Set.Ico 0 s ⊆ Set.Icc 0 T := fun t ht => ⟨ht.1, ht.2.le.trans hsT⟩
  have hev' : ∀ᶠ t in 𝓝[<] s, n < g t ω := by
    rw [← nhdsWithin_Ico_eq_nhdsLT hspos]
    exact hev.filter_mono (nhdsWithin_mono _ hsub)
  obtain ⟨l, hl, hIoo⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hspos).1 hev'
  obtain ⟨q, hq, hlq, hqs⟩ := exists_ratTimes_between (show l < s from hl)
  have hgq : n < g q ω := hIoo ⟨hlq, hqs⟩
  have := exitTime_le_of_mem (g := g) (ω := ω) hq (hqs.le.trans hsT) hgq.le
  exact absurd (this.trans_lt hqs) (not_lt.2 hs)

omit mΩ in
lemma exitTime_eq_of_lt {T : ℝ≥0} {g : ℝ≥0 → Ω → ℝ} {n : ℝ} {ω : Ω}
    (h : ∀ t ≤ T, g t ω < n) : exitTime T g n ω = T := by
  apply le_antisymm (exitTime_le T g n ω)
  apply le_csInf (Set.insert_nonempty _ _)
  rintro b (rfl | ⟨_, hqT, hn⟩)
  · exact le_rfl
  · exact absurd hn (not_le.2 (h b hqT))

omit mΩ in
/-- For a path continuous on `[0, T]`, the rational exit times at levels `n → ∞` are
eventually equal to `T`. -/
lemma eventually_exitTime_eq {T : ℝ≥0} {g : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : ContinuousOn (fun t ↦ g t ω) (Set.Icc 0 T)) :
    ∀ᶠ n : ℕ in atTop, exitTime T g n ω = T := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hc).bddAbove
  obtain ⟨N, hN⟩ := exists_nat_gt M
  filter_upwards [eventually_ge_atTop N] with n hn
  apply exitTime_eq_of_lt
  intro t ht
  have hle : g t ω ≤ M := hM ⟨t, ⟨zero_le, ht⟩, rfl⟩
  calc g t ω ≤ M := hle
    _ < N := hN
    _ ≤ n := by exact_mod_cast hn

end CommonOptional
end MathFin.FilteredIto
