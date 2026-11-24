/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CommonCovariation

/-!
# Covariation of continuous `L²` kernels

The covariation theorems of `CommonCovariation` are extended from bounded to merely
continuous (adapted, predictable, `L²`) kernel representatives by truncation
`h ↦ max (-k) (min k h)`: the frozen bilinear sums are uniformly `L¹`-continuous in the kernels,

  `E|Sₙ(x₁,y₁) − Sₙ(x₂,y₂)| ≤ C₀ (‖x₁ − x₂‖‖y₁‖ + ‖x₂‖‖y₁ − y₂‖)`,

because `∑ⱼ E[(ΔMⱼ)²] ≤ ‖x‖²` (time-indexed isometry), and the truncated kernels and
time integrals converge by dominated convergence.

## Main definitions

* `ContProcess`
* `clampAt`
* `truncKernel`

## Main results

* `tendsto_approxError`
* `tendsto_covariation_same_L2`
* `tendsto_covariation_cross_L2`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto
namespace CommonCovariation

open MeasureTheory ProbabilityTheory Filter Topology
open MathFin.FilteredIto.CommonNoise MathFin.FilteredIto.CommonL2
      MathFin.FilteredIto.CommonPredictable MathFin.FilteredIto.CommonIntegral
  MathFin.FilteredIto.CommonProcess MathFin.FilteredIto.CommonProcessGeneral
        MathFin.FilteredIto.CommonContinuous
  MathFin.FilteredIto.CommonLocality MathFin.FilteredIto.CommonStopping
        MathFin.FilteredIto.CommonRiemann
open MathFin (unifPart)
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ}

/-- An adapted, predictable process with a.s. continuous paths on `[0, T]`. -/
structure ContProcess (ℱ : Filtration ℝ≥0 mΩ) (μ : Measure Ω) (T : ℝ≥0)
    (h : ℝ≥0 → Ω → ℝ) : Prop where
  adapted : ∀ t, Measurable[ℱ t] (h t)
  pred : Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω ↦ h p.1 p.2)
  cont : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ h t ω) (Set.Icc 0 T)

omit [IsProbabilityMeasure μ] in
lemma GoodProcess.toCont {T : ℝ≥0} {h : ℝ≥0 → Ω → ℝ} {C : ℝ} (hh : GoodProcess ℱ μ T h C) :
    ContProcess ℱ μ T h := ⟨hh.adapted, hh.pred, hh.cont⟩

/-! ### Truncation -/

/-- Truncation at level `m`. -/
def clampAt (m x : ℝ) : ℝ := max (-m) (min m x)

lemma continuous_clampAt (m : ℝ) : Continuous (clampAt m) :=
  continuous_const.max (continuous_const.min continuous_id)

lemma abs_clampAt_le {m : ℝ} (hm : 0 ≤ m) (x : ℝ) : |clampAt m x| ≤ m := by
  unfold clampAt
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

lemma clampAt_eq {m x : ℝ} (h : |x| ≤ m) : clampAt m x = x := by
  unfold clampAt
  obtain ⟨h1, h2⟩ := abs_le.mp h
  rw [min_eq_right h2, max_eq_right h1]

lemma abs_clampAt_sub_le {m : ℝ} (hm : 0 ≤ m) (x : ℝ) : |clampAt m x - x| ≤ |x| := by
  unfold clampAt
  rcases le_total x 0 with hx | hx
  · rw [min_eq_right (hx.trans hm), abs_of_nonpos hx]
    rcases le_total (-m) x with h | h
    · rw [max_eq_right h, sub_self, abs_zero]; linarith
    · rw [max_eq_left h, abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_nonneg hx]
    rcases le_total m x with h | h
    · rw [min_eq_left h, max_eq_right (by linarith), abs_of_nonpos (by linarith)]; linarith
    · rw [min_eq_right h, max_eq_right (by linarith), sub_self, abs_zero]; exact hx

lemma abs_clampAt_le_abs {m : ℝ} (hm : 0 ≤ m) (x : ℝ) : |clampAt m x| ≤ |x| := by
  unfold clampAt
  rcases le_total x 0 with hx | hx
  · rw [min_eq_right (hx.trans hm), abs_of_nonpos hx]
    rcases le_total (-m) x with h | h
    · rw [max_eq_right h, abs_of_nonpos hx]
    · rw [max_eq_left h, abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg hx]
    rcases le_total m x with h | h
    · rw [min_eq_left h, max_eq_right (by linarith), abs_of_nonneg hm]; exact h
    · rw [min_eq_right h, max_eq_right (by linarith), abs_of_nonneg hx]

omit [IsProbabilityMeasure μ] in
/-- Truncations of continuous processes are good. -/
lemma ContProcess.trunc {T : ℝ≥0} {h : ℝ≥0 → Ω → ℝ} (hh : ContProcess ℱ μ T h) (k : ℕ) :
    GoodProcess ℱ μ T (fun t ω ↦ clampAt k (h t ω)) k where
  adapted t := (continuous_clampAt _).measurable.comp (hh.adapted t)
  pred := (continuous_clampAt _).measurable.comp hh.pred
  bdd t ω := abs_clampAt_le (Nat.cast_nonneg k) _
  cont := by
    filter_upwards [hh.cont] with ω hω
    exact (continuous_clampAt _).comp_continuousOn hω
  nonneg := Nat.cast_nonneg k

/-- The truncated kernel `max (-k) (min k h)`. -/
noncomputable def truncKernel (T : ℝ≥0) {h : ℝ≥0 → Ω → ℝ} (hh : ContProcess ℱ μ T h) (k : ℕ) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ) :=
  (MemLp.of_bound ((continuous_clampAt (k : ℝ)).measurable.comp hh.pred).aestronglyMeasurable
    (k : ℝ) (Eventually.of_forall fun p ↦ by
      rw [Real.norm_eq_abs]; exact abs_clampAt_le (Nat.cast_nonneg k) _)).toLp
    (fun p : ℝ≥0 × Ω ↦ clampAt k (h p.1 p.2))

lemma coeFn_truncKernel (T : ℝ≥0) {h : ℝ≥0 → Ω → ℝ} (hh : ContProcess ℱ μ T h) (k : ℕ) :
    ⇑(truncKernel (μ := μ) T hh k) =ᵐ[trimMeasure_T (μ := μ) T ℱ]
      fun p ↦ clampAt k (h p.1 p.2) :=
  MemLp.coeFn_toLp _

/-- Truncated kernels converge in `L²(trim_T)`. -/
theorem tendsto_truncKernel (T : ℝ≥0) {h : ℝ≥0 → Ω → ℝ} (hh : ContProcess ℱ μ T h)
    {φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)}
    (hφ : ⇑φ =ᵐ[trimMeasure_T (μ := μ) T ℱ] fun p ↦ h p.1 p.2) :
    Tendsto (fun k : ℕ ↦ truncKernel (μ := μ) T hh k) atTop (𝓝 φ) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hcoe : ∀ᵐ p ∂(trimMeasure_T (μ := μ) T ℱ), ∀ k : ℕ,
      ((truncKernel (μ := μ) T hh k - φ : Lp ℝ 2 _) p) ^ 2
        = (clampAt k (h p.1 p.2) - h p.1 p.2) ^ 2 := by
    rw [ae_all_iff]
    intro k
    filter_upwards [Lp.coeFn_sub (truncKernel (μ := μ) T hh k) φ, coeFn_truncKernel T hh k, hφ]
      with p h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have hint : Tendsto (fun k : ℕ ↦ ∫ p, ((truncKernel (μ := μ) T hh k - φ : Lp ℝ 2 _) p) ^ 2
      ∂(trimMeasure_T (μ := μ) T ℱ)) atTop (𝓝 0) := by
    have key := tendsto_integral_of_dominated_convergence (μ := trimMeasure_T (μ := μ) T ℱ)
      (F := fun k p ↦ ((truncKernel (μ := μ) T hh k - φ : Lp ℝ 2 _) p) ^ 2)
      (f := fun _ => (0 : ℝ)) (fun p ↦ (φ p) ^ 2)
      (fun k => (Lp.aestronglyMeasurable _).pow 2) (Lp.memLp φ).integrable_sq
      (fun k => by
        filter_upwards [hcoe, hφ] with p hp hp'
        rw [hp k, Real.norm_eq_abs, abs_pow, hp']
        calc |clampAt k (h p.1 p.2) - h p.1 p.2| ^ 2 ≤ |h p.1 p.2| ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) (abs_clampAt_sub_le (Nat.cast_nonneg k) _) 2
          _ = (h p.1 p.2) ^ 2 := sq_abs _)
      (by
        filter_upwards [hcoe] with p hp
        have hev : ∀ᶠ k : ℕ in atTop, (clampAt k (h p.1 p.2) - h p.1 p.2) ^ 2 = 0 := by
          obtain ⟨K, hK⟩ := exists_nat_ge |h p.1 p.2|
          filter_upwards [eventually_ge_atTop K] with k hk
          rw [clampAt_eq (hK.trans (by exact_mod_cast hk)), sub_self]
          norm_num
        exact tendsto_const_nhds.congr' (hev.mono fun k hk => ((hp k).trans hk).symm))
    simpa using key
  have h2 : Tendsto (fun k : ℕ ↦ ‖truncKernel (μ := μ) T hh k - φ‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [MathFin.lp_two_norm_sq]; exact hint
  have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
  simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at h3
  exact h3

/-! ### Mean-square size of the increments -/

omit [IsProbabilityMeasure μ] in
lemma norm_band_sq_eq (T a b : ℝ≥0) (hWmeas : ∀ u, Measurable (W u))
    (z : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    ∀ᵐ p ∂(trimMeasure_T (μ := μ) T ℱ),
      (band T a b hWmeas z p) ^ 2 = bandInd a b p.1 ^ 2 * (z p) ^ 2 := by
  filter_upwards [coeFn_band T a b hWmeas z] with p hp
  rw [hp, bandInd]
  split_ifs <;> ring

/-- `∑ⱼ E[(ΔMⱼ)²] ≤ ‖z‖²`. -/
lemma sum_integral_incrM_sq_le (hW : BrownianOn ℱ W μ)
    (hWc : ∀ ω, Continuous fun u : ℝ≥0 ↦ W u ω) (T : ℝ≥0) (n : ℕ)
    (z : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    ∑ j ∈ Finset.range n, ∫ ω, (itoContinuousMod T hW.measurable z (unifPart T n (j + 1)) ω
      - itoContinuousMod T hW.measurable z (unifPart T n j) ω) ^ 2 ∂μ ≤ ‖z‖ ^ 2 := by
  have hterm : ∀ j ∈ Finset.range n, ∫ ω, (itoContinuousMod T hW.measurable z
      (unifPart T n (j + 1)) ω - itoContinuousMod T hW.measurable z (unifPart T n j) ω) ^ 2 ∂μ
      = ∫ p, (band T (unifPart T n j) (unifPart T n (j + 1)) hW.measurable z p) ^ 2
          ∂(trimMeasure_T (μ := μ) T ℱ) := by
    intro j hj
    rw [← MathFin.lp_two_norm_sq, ← itoIntegralCLM_T_norm hW T, MathFin.lp_two_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [incrM_ae_eq hW hWc T (Finset.mem_range.mp hj) z] with ω hω
    rw [← hω]
  rw [Finset.sum_congr rfl hterm, ← integral_finsetSum _ fun j _ => (Lp.memLp _).integrable_sq,
    MathFin.lp_two_norm_sq]
  refine integral_mono_ae (integrable_finsetSum _ fun j _ => (Lp.memLp _).integrable_sq)
    (Lp.memLp z).integrable_sq ?_
  have hall := (Filter.eventually_all_finset (Finset.range n)).mpr fun j _ =>
    norm_band_sq_eq T (unifPart T n j) (unifPart T n (j + 1)) hW.measurable z
  filter_upwards [hall] with p hp
  rw [Finset.sum_congr rfl hp, ← Finset.sum_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Finset.range_zero, Finset.sum_empty, zero_mul]; positivity
  · have hsq : ∀ j, bandInd (unifPart T n j) (unifPart T n (j + 1)) p.1 ^ 2
        = bandInd (gridPt T n j) (gridPt T n (j + 1)) p.1 := by
      intro j
      rw [unifPart_eq_gridPt, unifPart_eq_gridPt, bandInd_sq (gridPt_mono T n (Nat.le_succ j))]
    simp_rw [hsq]
    rw [sum_bandInd T hn p.1]
    refine mul_le_of_le_one_left (sq_nonneg _) ?_
    split_ifs <;> norm_num

lemma memLp_incrM (hW : BrownianOn ℱ W μ) (hWc : ∀ ω, Continuous fun u : ℝ≥0 ↦ W u ω)
    (T : ℝ≥0) {n j : ℕ} (hj : j < n) (z : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    MemLp (fun ω ↦ itoContinuousMod T hW.measurable z (unifPart T n (j + 1)) ω
      - itoContinuousMod T hW.measurable z (unifPart T n j) ω) 2 μ :=
  (Lp.memLp _).ae_eq (incrM_ae_eq hW hWc T hj z).symm

/-- Increments of the continuous integral are linear in the kernel, almost surely. -/
lemma incrM_sub_ae (hW : BrownianOn ℱ W μ) (hWc : ∀ ω, Continuous fun u : ℝ≥0 ↦ W u ω)
    (T : ℝ≥0) {n j : ℕ} (hj : j < n) (x y : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    ∀ᵐ ω ∂μ, (itoContinuousMod T hW.measurable x (unifPart T n (j + 1)) ω
        - itoContinuousMod T hW.measurable x (unifPart T n j) ω)
      - (itoContinuousMod T hW.measurable y (unifPart T n (j + 1)) ω
        - itoContinuousMod T hW.measurable y (unifPart T n j) ω)
      = itoContinuousMod T hW.measurable (x - y) (unifPart T n (j + 1)) ω
        - itoContinuousMod T hW.measurable (x - y) (unifPart T n j) ω := by
  have hband : band T (unifPart T n j) (unifPart T n (j + 1)) hW.measurable (x - y)
      = band T (unifPart T n j) (unifPart T n (j + 1)) hW.measurable x
        - band T (unifPart T n j) (unifPart T n (j + 1)) hW.measurable y := by
    simp only [band, map_sub]; abel
  filter_upwards [incrM_ae_eq hW hWc T hj x, incrM_ae_eq hW hWc T hj y,
    incrM_ae_eq hW hWc T hj (x - y),
    Lp.coeFn_sub (itoIntegralCLM_T hW T (band T (unifPart T n j) (unifPart T n (j + 1))
      hW.measurable x)) (itoIntegralCLM_T hW T (band T (unifPart T n j) (unifPart T n (j + 1))
      hW.measurable y))] with ω h1 h2 h3 h4
  rw [h1, h2, h3, hband, map_sub, h4, Pi.sub_apply]

/-- **Uniform bilinear estimate** for frozen covariation sums. -/
lemma integral_abs_frozenBilinear_le {W' : ℝ≥0 → Ω → ℝ} (hW : BrownianOn ℱ W μ)
    (hWc : ∀ ω, Continuous fun u : ℝ≥0 ↦ W u ω) (hW' : BrownianOn ℱ W' μ)
    (hW'c : ∀ ω, Continuous fun u : ℝ≥0 ↦ W' u ω) (T : ℝ≥0) (n : ℕ)
    {w : ℝ≥0 → Ω → ℝ} {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hwb : ∀ t ω, |w t ω| ≤ C₀)
    (x y : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    ∫ ω, |∑ j ∈ Finset.range n, w (unifPart T n j) ω
        * (itoContinuousMod T hW.measurable x (unifPart T n (j + 1)) ω
          - itoContinuousMod T hW.measurable x (unifPart T n j) ω)
        * (itoContinuousMod T hW'.measurable y (unifPart T n (j + 1)) ω
          - itoContinuousMod T hW'.measurable y (unifPart T n j) ω)| ∂μ
      ≤ C₀ * (‖x‖ * ‖y‖) := by
  have hX := fun j (hj : j ∈ Finset.range n) => memLp_incrM hW hWc T (Finset.mem_range.mp hj) x
  have hY := fun j (hj : j ∈ Finset.range n) => memLp_incrM hW' hW'c T (Finset.mem_range.mp hj) y
  have hint : Integrable (fun ω ↦ ∑ j ∈ Finset.range n,
      |(itoContinuousMod T hW.measurable x (unifPart T n (j + 1)) ω
          - itoContinuousMod T hW.measurable x (unifPart T n j) ω)
        * (itoContinuousMod T hW'.measurable y (unifPart T n (j + 1)) ω
          - itoContinuousMod T hW'.measurable y (unifPart T n j) ω)|) μ :=
    integrable_finsetSum _ fun j hj => ((hX j hj).integrable_mul (hY j hj)).abs
  have hint' : Integrable (fun ω ↦ C₀ * ∑ j ∈ Finset.range n,
      |(itoContinuousMod T hW.measurable x (unifPart T n (j + 1)) ω
          - itoContinuousMod T hW.measurable x (unifPart T n j) ω)
        * (itoContinuousMod T hW'.measurable y (unifPart T n (j + 1)) ω
          - itoContinuousMod T hW'.measurable y (unifPart T n j) ω)|) μ := hint.const_mul C₀
  refine (integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg _) hint'
    (Eventually.of_forall fun ω => ?_)).trans ?_
  · beta_reduce
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [mul_assoc, abs_mul]
    exact mul_le_mul_of_nonneg_right (hwb _ _) (abs_nonneg _)
  · rw [integral_const_mul, integral_finsetSum (f := fun j ω ↦
      |(itoContinuousMod T hW.measurable x (unifPart T n (j + 1)) ω
          - itoContinuousMod T hW.measurable x (unifPart T n j) ω)
        * (itoContinuousMod T hW'.measurable y (unifPart T n (j + 1)) ω
          - itoContinuousMod T hW'.measurable y (unifPart T n j) ω)|) _
      fun j hj => ((hX j hj).integrable_mul (hY j hj)).abs]
    refine mul_le_mul_of_nonneg_left ((sum_integral_abs_mul_le (Finset.range n) hX hY).trans ?_)
      hC₀
    have e1 := sum_integral_incrM_sq_le hW hWc T n x
    have e2 := sum_integral_incrM_sq_le hW' hW'c T n y
    calc _ ≤ √(‖x‖ ^ 2) * √(‖y‖ ^ 2) :=
          mul_le_mul (Real.sqrt_le_sqrt e1) (Real.sqrt_le_sqrt e2) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = ‖x‖ * ‖y‖ := by rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-! ### An abstract approximation lemma -/

omit mΩ in
lemma tendsto_of_approx {mΩ' : MeasurableSpace Ω} {ν : Measure Ω}
    {S : ℕ → Ω → ℝ} {L : Ω → ℝ} {S' : ℕ → ℕ → Ω → ℝ} {L' : ℕ → Ω → ℝ} {e : ℕ → ℝ}
    (hS : ∀ n, Integrable (S n) ν) (hS' : ∀ k n, Integrable (S' k n) ν)
    (hL' : ∀ k, Integrable (L' k) ν) (hLL : ∀ k, Integrable (fun ω ↦ L' k ω - L ω) ν)
    (happrox : ∀ k n, ∫ ω, |S n ω - S' k n ω| ∂ν ≤ e k) (he : Tendsto e atTop (𝓝 0))
    (hL : Tendsto (fun k ↦ ∫ ω, |L' k ω - L ω| ∂ν) atTop (𝓝 0))
    (hconv : ∀ k, Tendsto (fun n ↦ ∫ ω, |S' k n ω - L' k ω| ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ ω, |S n ω - L ω| ∂ν) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hsum : Tendsto (fun k ↦ e k + ∫ ω, |L' k ω - L ω| ∂ν) atTop (𝓝 0) := by
    simpa using he.add hL
  obtain ⟨k, hk⟩ := (hsum.eventually (gt_mem_nhds (half_pos hε))).exists
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hconv k) (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hNn := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun ω => abs_nonneg _)] at hNn ⊢
  have i1 : Integrable (fun ω ↦ |S n ω - S' k n ω|) ν := ((hS n).sub (hS' k n)).abs
  have i2 : Integrable (fun ω ↦ |S' k n ω - L' k ω|) ν := ((hS' k n).sub (hL' k)).abs
  have i3 : Integrable (fun ω ↦ |L' k ω - L ω|) ν := (hLL k).abs
  have h12 : Integrable (fun ω ↦ |S n ω - S' k n ω| + |S' k n ω - L' k ω|) ν := i1.add i2
  have h123 : Integrable (fun ω ↦ |S n ω - S' k n ω| + |S' k n ω - L' k ω|
      + |L' k ω - L ω|) ν := h12.add i3
  have hle := integral_mono_of_nonneg (μ := ν) (f := fun ω ↦ |S n ω - L ω|)
    (Eventually.of_forall fun ω => abs_nonneg _) h123 (Eventually.of_forall fun ω => by
      calc |S n ω - L ω| = |(S n ω - S' k n ω) + (S' k n ω - L' k ω) + (L' k ω - L ω)| := by
            congr 1; ring
        _ ≤ |S n ω - S' k n ω| + |S' k n ω - L' k ω| + |L' k ω - L ω| :=
            (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl))
  rw [integral_add h12 i3, integral_add i1 i2] at hle
  linarith [happrox k n]

/-! ### Integrability of frozen bilinear sums -/

lemma integrable_frozenBilinear {W' : ℝ≥0 → Ω → ℝ} (hW : BrownianOn ℱ W μ)
    (hWc : ∀ ω, Continuous fun u : ℝ≥0 ↦ W u ω) (hW' : BrownianOn ℱ W' μ)
    (hW'c : ∀ ω, Continuous fun u : ℝ≥0 ↦ W' u ω) (T : ℝ≥0) (n : ℕ)
    {w : ℝ≥0 → Ω → ℝ} {C₀ : ℝ} (hwm : ∀ t, Measurable (w t)) (hwb : ∀ t ω, |w t ω| ≤ C₀)
    (x y : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    Integrable (fun ω ↦ ∑ j ∈ Finset.range n, w (unifPart T n j) ω
        * (itoContinuousMod T hW.measurable x (unifPart T n (j + 1)) ω
          - itoContinuousMod T hW.measurable x (unifPart T n j) ω)
        * (itoContinuousMod T hW'.measurable y (unifPart T n (j + 1)) ω
          - itoContinuousMod T hW'.measurable y (unifPart T n j) ω)) μ := by
  refine integrable_finsetSum _ fun j hj => ?_
  have hXY := (memLp_incrM hW hWc T (Finset.mem_range.mp hj) x).integrable_mul
    (memLp_incrM hW' hW'c T (Finset.mem_range.mp hj) y)
  have := hXY.bdd_mul (c := C₀) (hwm (unifPart T n j)).aestronglyMeasurable
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hwb (unifPart T n j) ω)
  refine this.congr (Eventually.of_forall fun ω => ?_)
  show w (unifPart T n j) ω * ((itoContinuousMod T hW.measurable x (unifPart T n (j + 1)) ω
      - itoContinuousMod T hW.measurable x (unifPart T n j) ω)
      * (itoContinuousMod T hW'.measurable y (unifPart T n (j + 1)) ω
        - itoContinuousMod T hW'.measurable y (unifPart T n j) ω)) = _
  ring

/-- Approximation of a frozen bilinear sum by changing both kernels. -/
lemma integral_abs_frozenBilinear_sub_le {W' : ℝ≥0 → Ω → ℝ} (hW : BrownianOn ℱ W μ)
    (hWc : ∀ ω, Continuous fun u : ℝ≥0 ↦ W u ω) (hW' : BrownianOn ℱ W' μ)
    (hW'c : ∀ ω, Continuous fun u : ℝ≥0 ↦ W' u ω) (T : ℝ≥0) (n : ℕ)
    {w : ℝ≥0 → Ω → ℝ} {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hwm : ∀ t, Measurable (w t))
    (hwb : ∀ t ω, |w t ω| ≤ C₀) (x₁ y₁ x₂ y₂ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    ∫ ω, |∑ j ∈ Finset.range n, w (unifPart T n j) ω
        * (itoContinuousMod T hW.measurable x₁ (unifPart T n (j + 1)) ω
          - itoContinuousMod T hW.measurable x₁ (unifPart T n j) ω)
        * (itoContinuousMod T hW'.measurable y₁ (unifPart T n (j + 1)) ω
          - itoContinuousMod T hW'.measurable y₁ (unifPart T n j) ω)
      - ∑ j ∈ Finset.range n, w (unifPart T n j) ω
        * (itoContinuousMod T hW.measurable x₂ (unifPart T n (j + 1)) ω
          - itoContinuousMod T hW.measurable x₂ (unifPart T n j) ω)
        * (itoContinuousMod T hW'.measurable y₂ (unifPart T n (j + 1)) ω
          - itoContinuousMod T hW'.measurable y₂ (unifPart T n j) ω)| ∂μ
      ≤ C₀ * (‖x₁ - x₂‖ * ‖y₁‖ + ‖x₂‖ * ‖y₁ - y₂‖) := by
  set A : Ω → ℝ := fun ω ↦ ∑ j ∈ Finset.range n, w (unifPart T n j) ω
        * (itoContinuousMod T hW.measurable (x₁ - x₂) (unifPart T n (j + 1)) ω
          - itoContinuousMod T hW.measurable (x₁ - x₂) (unifPart T n j) ω)
        * (itoContinuousMod T hW'.measurable y₁ (unifPart T n (j + 1)) ω
          - itoContinuousMod T hW'.measurable y₁ (unifPart T n j) ω) with hA
  set B' : Ω → ℝ := fun ω ↦ ∑ j ∈ Finset.range n, w (unifPart T n j) ω
        * (itoContinuousMod T hW.measurable x₂ (unifPart T n (j + 1)) ω
          - itoContinuousMod T hW.measurable x₂ (unifPart T n j) ω)
        * (itoContinuousMod T hW'.measurable (y₁ - y₂) (unifPart T n (j + 1)) ω
          - itoContinuousMod T hW'.measurable (y₁ - y₂) (unifPart T n j) ω) with hB'
  have hAi : Integrable A μ := integrable_frozenBilinear hW hWc hW' hW'c T n hwm hwb _ _
  have hBi : Integrable B' μ := integrable_frozenBilinear hW hWc hW' hW'c T n hwm hwb _ _
  have hX := (Filter.eventually_all_finset (Finset.range n)).mpr fun j hj =>
    incrM_sub_ae hW hWc T (Finset.mem_range.mp hj) x₁ x₂
  have hY := (Filter.eventually_all_finset (Finset.range n)).mpr fun j hj =>
    incrM_sub_ae hW' hW'c T (Finset.mem_range.mp hj) y₁ y₂
  have hsplit : ∀ᵐ ω ∂μ, |∑ j ∈ Finset.range n, w (unifPart T n j) ω
        * (itoContinuousMod T hW.measurable x₁ (unifPart T n (j + 1)) ω
          - itoContinuousMod T hW.measurable x₁ (unifPart T n j) ω)
        * (itoContinuousMod T hW'.measurable y₁ (unifPart T n (j + 1)) ω
          - itoContinuousMod T hW'.measurable y₁ (unifPart T n j) ω)
      - ∑ j ∈ Finset.range n, w (unifPart T n j) ω
        * (itoContinuousMod T hW.measurable x₂ (unifPart T n (j + 1)) ω
          - itoContinuousMod T hW.measurable x₂ (unifPart T n j) ω)
        * (itoContinuousMod T hW'.measurable y₂ (unifPart T n (j + 1)) ω
          - itoContinuousMod T hW'.measurable y₂ (unifPart T n j) ω)| ≤ |A ω| + |B' ω| := by
    filter_upwards [hX, hY] with ω h1 h2
    refine le_of_eq_of_le ?_ (abs_add_le (A ω) (B' ω))
    congr 1
    simp only [hA, hB']
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← h1 j hj, ← h2 j hj]
    ring
  have hAB : Integrable (fun ω ↦ |A ω| + |B' ω|) μ := hAi.abs.add hBi.abs
  refine (integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg _) hAB hsplit).trans ?_
  rw [integral_add hAi.abs hBi.abs, mul_add]
  have e1 := integral_abs_frozenBilinear_le hW hWc hW' hW'c T n hC₀ hwb (x₁ - x₂) y₁
  have e2 := integral_abs_frozenBilinear_le hW hWc hW' hW'c T n hC₀ hwb x₂ (y₁ - y₂)
  exact add_le_add e1 e2

/-! ### Truncated time integrals -/

/-- `E|∫ w·trunc_k(h₁)·trunc_k(h₂) ds − ∫ w h₁ h₂ ds| → 0`, with integrability of the error. -/
lemma tendsto_timeIntegral_trunc (T : ℝ≥0) {w h₁ h₂ : ℝ≥0 → Ω → ℝ} {C₀ : ℝ}
    (hw : GoodProcess ℱ μ T w C₀) (hc₁ : ContProcess ℱ μ T h₁) (hc₂ : ContProcess ℱ μ T h₂)
    {φ₁ φ₂ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)}
    (hφ₁ : ⇑φ₁ =ᵐ[trimMeasure_T (μ := μ) T ℱ] fun p ↦ h₁ p.1 p.2)
    (hφ₂ : ⇑φ₂ =ᵐ[trimMeasure_T (μ := μ) T ℱ] fun p ↦ h₂ p.1 p.2) :
    (∀ k : ℕ, Integrable (fun ω ↦ ∫ s, w s ω * clampAt k (h₁ s ω) * clampAt k (h₂ s ω)
        ∂(timeMeasure_T T) - ∫ s, w s ω * h₁ s ω * h₂ s ω ∂(timeMeasure_T T)) μ) ∧
    Tendsto (fun k : ℕ ↦ ∫ ω, |∫ s, w s ω * clampAt k (h₁ s ω) * clampAt k (h₂ s ω)
        ∂(timeMeasure_T T) - ∫ s, w s ω * h₁ s ω * h₂ s ω ∂(timeMeasure_T T)| ∂μ)
      atTop (𝓝 0) := by
  -- the product function `|h₁ h₂|` is integrable on the product measure
  have hprodP : Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω ↦ h₁ p.1 p.2 * h₂ p.1 p.2) :=
    hc₁.pred.mul hc₂.pred
  have hH : Integrable (fun p : ℝ≥0 × Ω ↦ h₁ p.1 p.2 * h₂ p.1 p.2)
      ((timeMeasure_T T).prod μ) := by
    have h1 : Integrable (fun p ↦ φ₁ p * φ₂ p) (trimMeasure_T (μ := μ) T ℱ) :=
      (Lp.memLp φ₁).integrable_mul (Lp.memLp φ₂)
    have h2 : Integrable (fun p : ℝ≥0 × Ω ↦ h₁ p.1 p.2 * h₂ p.1 p.2)
        (trimMeasure_T (μ := μ) T ℱ) := by
      refine h1.congr ?_
      filter_upwards [hφ₁, hφ₂] with p e1 e2
      rw [e1, e2]
    exact integrable_of_integrable_trim ℱ.predictable_le_prod h2
  set G : ℕ → ℝ≥0 × Ω → ℝ := fun k p ↦ |w p.1 p.2| * |clampAt k (h₁ p.1 p.2)
    * clampAt k (h₂ p.1 p.2) - h₁ p.1 p.2 * h₂ p.1 p.2| with hG
  have hGm : ∀ k, Measurable[ℱ.predictable] (G k) := by
    intro k
    simp only [hG]
    exact (continuous_abs.measurable.comp hw.pred).mul (continuous_abs.measurable.comp
      ((((continuous_clampAt _).measurable.comp hc₁.pred).mul
      ((continuous_clampAt _).measurable.comp hc₂.pred)).sub hprodP))
  have hGb : ∀ k p, ‖G k p‖ ≤ 2 * C₀ * |h₁ p.1 p.2 * h₂ p.1 p.2| := by
    intro k p
    simp only [hG, Real.norm_eq_abs, abs_mul, abs_abs]
    have hk := Nat.cast_nonneg (α := ℝ) k
    have a1 := abs_clampAt_le_abs hk (h₁ p.1 p.2)
    have a2 := abs_clampAt_le_abs hk (h₂ p.1 p.2)
    have e : |clampAt k (h₁ p.1 p.2) * clampAt k (h₂ p.1 p.2) - h₁ p.1 p.2 * h₂ p.1 p.2|
        ≤ 2 * (|h₁ p.1 p.2| * |h₂ p.1 p.2|) := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul]
      linarith [mul_le_mul a1 a2 (abs_nonneg _) (abs_nonneg _)]
    calc |w p.1 p.2| * |clampAt k (h₁ p.1 p.2) * clampAt k (h₂ p.1 p.2) - h₁ p.1 p.2 * h₂ p.1 p.2|
        ≤ C₀ * (2 * (|h₁ p.1 p.2| * |h₂ p.1 p.2|)) :=
          mul_le_mul (hw.bdd _ _) e (abs_nonneg _) hw.nonneg
      _ = 2 * C₀ * (|h₁ p.1 p.2| * |h₂ p.1 p.2|) := by ring
  have hGi : ∀ k, Integrable (G k) ((timeMeasure_T T).prod μ) := fun k =>
    (hH.abs.const_mul (2 * C₀)).mono' ((hGm k).mono ℱ.predictable_le_prod
          le_rfl).aestronglyMeasurable
      (Eventually.of_forall fun p => (hGb k p).trans (by rw [abs_mul]))
  -- dominated convergence on the product measure
  have hGlim : Tendsto (fun k ↦ ∫ p, G k p ∂((timeMeasure_T T).prod μ)) atTop (𝓝 0) := by
    have key := tendsto_integral_of_dominated_convergence (μ := (timeMeasure_T T).prod μ)
      (F := G) (f := fun _ => (0 : ℝ)) (fun p ↦ 2 * C₀ * |h₁ p.1 p.2 * h₂ p.1 p.2|)
      (fun k => ((hGm k).mono ℱ.predictable_le_prod le_rfl).aestronglyMeasurable)
      (hH.abs.const_mul _) (fun k => Eventually.of_forall (hGb k))
      (Eventually.of_forall fun p => by
        obtain ⟨K, hK⟩ := exists_nat_ge (max |h₁ p.1 p.2| |h₂ p.1 p.2|)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop K] with k hk
        have hk' : max |h₁ p.1 p.2| |h₂ p.1 p.2| ≤ k := hK.trans (by exact_mod_cast hk)
        simp only [hG]
        rw [clampAt_eq ((le_max_left _ _).trans hk'), clampAt_eq ((le_max_right _ _).trans hk'),
          sub_self, abs_zero, mul_zero])
    simpa using key
  -- Fubini and the pointwise bound
  have hfub : ∀ k, ∫ p, G k p ∂((timeMeasure_T T).prod μ)
      = ∫ ω, ∫ s, G k (s, ω) ∂(timeMeasure_T T) ∂μ := fun k => integral_prod_symm _ (hGi k)
  have hsec_wh : ∀ᵐ ω ∂μ, Integrable (fun s ↦ w s ω * h₁ s ω * h₂ s ω) (timeMeasure_T T) := by
    have hI : Integrable (fun p : ℝ≥0 × Ω ↦ w p.1 p.2 * h₁ p.1 p.2 * h₂ p.1 p.2)
        ((timeMeasure_T T).prod μ) := by
      refine (hH.bdd_mul (c := C₀) (hw.pred.mono ℱ.predictable_le_prod le_rfl).aestronglyMeasurable
        (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hw.bdd _ _)).congr
        (Eventually.of_forall fun p => ?_)
      show w p.1 p.2 * (h₁ p.1 p.2 * h₂ p.1 p.2) = _
      ring
    exact hI.prod_left_ae
  have hsec_wc : ∀ k : ℕ, ∀ᵐ ω ∂μ, Integrable (fun s ↦ w s ω * clampAt k (h₁ s ω)
      * clampAt k (h₂ s ω)) (timeMeasure_T T) := by
    intro k
    refine Eventually.of_forall fun ω => ?_
    refine Integrable.of_bound (C := C₀ * k * k) ?_ ?_
    · have hm : Measurable (fun s : ℝ≥0 ↦ w s ω * clampAt k (h₁ s ω) * clampAt k (h₂ s ω)) :=
        (((hw.pred.mono ℱ.predictable_le_prod le_rfl).comp measurable_prodMk_right).mul
          (((continuous_clampAt _).measurable.comp
            (hc₁.pred.mono ℱ.predictable_le_prod le_rfl)).comp measurable_prodMk_right)).mul
          (((continuous_clampAt _).measurable.comp
            (hc₂.pred.mono ℱ.predictable_le_prod le_rfl)).comp measurable_prodMk_right)
      exact hm.aestronglyMeasurable
    · refine Eventually.of_forall fun s => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have hk := Nat.cast_nonneg (α := ℝ) k
      exact mul_le_mul (mul_le_mul (hw.bdd s ω) (abs_clampAt_le hk _) (abs_nonneg _) hw.nonneg)
        (abs_clampAt_le hk _) (abs_nonneg _) (mul_nonneg hw.nonneg hk)
  have hpt : ∀ k : ℕ, ∀ᵐ ω ∂μ, |∫ s, w s ω * clampAt k (h₁ s ω) * clampAt k (h₂ s ω)
      ∂(timeMeasure_T T) - ∫ s, w s ω * h₁ s ω * h₂ s ω ∂(timeMeasure_T T)|
        ≤ ∫ s, G k (s, ω) ∂(timeMeasure_T T) := by
    intro k
    filter_upwards [hsec_wh, hsec_wc k] with ω h1 h2
    rw [← integral_sub h2 h1]
    refine (abs_integral_le_integral_abs).trans (le_of_eq (integral_congr_ae
      (Eventually.of_forall fun s => ?_)))
    simp only [hG]
    rw [← abs_mul]
    congr 1
    ring
  have hmeasL : ∀ k : ℕ, AEStronglyMeasurable (fun ω ↦ ∫ s, w s ω * clampAt k (h₁ s ω)
      * clampAt k (h₂ s ω) ∂(timeMeasure_T T) - ∫ s, w s ω * h₁ s ω * h₂ s ω
        ∂(timeMeasure_T T)) μ := by
    intro k
    refine ((stronglyMeasurable_timeIntegral (ℱ := ℱ) T ?_).sub
      (stronglyMeasurable_timeIntegral (ℱ := ℱ) T ?_)).aestronglyMeasurable
    · exact (hw.pred.mul ((continuous_clampAt _).measurable.comp hc₁.pred)).mul
        ((continuous_clampAt _).measurable.comp hc₂.pred)
    · exact (hw.pred.mul hc₁.pred).mul hc₂.pred
  refine ⟨fun k => (hGi k).integral_prod_right.mono' (hmeasL k) ?_, ?_⟩
  · filter_upwards [hpt k] with ω hω
    rwa [Real.norm_eq_abs]
  · refine squeeze_zero (fun k => integral_nonneg fun ω => abs_nonneg _) (fun k => ?_)
      (hGlim.congr fun k => hfub k)
    exact integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg _)
      (hGi k).integral_prod_right (hpt k)

/-! ### Covariation for continuous, possibly unbounded, integrands -/

omit [IsProbabilityMeasure μ] in
lemma tendsto_approxError {E : Type*} [NormedAddCommGroup E] {φ₁ φ₂ : E} {ψ₁ ψ₂ : ℕ → E}
    (C₀ : ℝ) (h₁ : Tendsto ψ₁ atTop (𝓝 φ₁)) (h₂ : Tendsto ψ₂ atTop (𝓝 φ₂)) :
    Tendsto (fun k ↦ C₀ * (‖φ₁ - ψ₁ k‖ * ‖φ₂‖ + ‖ψ₁ k‖ * ‖φ₂ - ψ₂ k‖)) atTop (𝓝 0) := by
  have a1 : Tendsto (fun k ↦ ‖φ₁ - ψ₁ k‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero.mp h₁).congr fun k => norm_sub_rev _ _
  have a2 : Tendsto (fun k ↦ ‖φ₂ - ψ₂ k‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero.mp h₂).congr fun k => norm_sub_rev _ _
  have a3 : Tendsto (fun k ↦ ‖ψ₁ k‖) atTop (𝓝 ‖φ₁‖) := h₁.norm
  have := ((a1.mul_const ‖φ₂‖).add (a3.mul a2)).const_mul C₀
  rw [show C₀ * (0 * ‖φ₂‖ + ‖φ₁‖ * 0) = 0 by ring] at this
  exact this

/-- Same driver, continuous adapted integrands (no boundedness):
`Σ_j w(t_j) ΔM¹_j ΔM²_j → ∫₀ᵀ w h₁ h₂ ds` in `L¹(μ)`. -/
theorem tendsto_covariation_same_L2 (hW : BrownianOn ℱ W μ)
    (hWc : ∀ ω, Continuous fun u : ℝ≥0 ↦ W u ω) (T : ℝ≥0)
    {w h₁ h₂ : ℝ≥0 → Ω → ℝ} {C₀ : ℝ} (hw : GoodProcess ℱ μ T w C₀)
    (hc₁ : ContProcess ℱ μ T h₁) (hc₂ : ContProcess ℱ μ T h₂)
    {φ₁ φ₂ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)}
    (hφ₁ : ⇑φ₁ =ᵐ[trimMeasure_T (μ := μ) T ℱ] fun p ↦ h₁ p.1 p.2)
    (hφ₂ : ⇑φ₂ =ᵐ[trimMeasure_T (μ := μ) T ℱ] fun p ↦ h₂ p.1 p.2) :
    Tendsto (fun n : ℕ ↦ ∫ ω, |∑ j ∈ Finset.range n, w (unifPart T n j) ω
        * (itoContinuousMod T hW.measurable φ₁ (unifPart T n (j + 1)) ω
            - itoContinuousMod T hW.measurable φ₁ (unifPart T n j) ω)
        * (itoContinuousMod T hW.measurable φ₂ (unifPart T n (j + 1)) ω
            - itoContinuousMod T hW.measurable φ₂ (unifPart T n j) ω)
        - ∫ s, w s ω * h₁ s ω * h₂ s ω ∂(timeMeasure_T T)| ∂μ) atTop (𝓝 0) := by
  have hwm : ∀ t, Measurable (w t) := fun t => (hw.adapted t).mono (ℱ.le t) le_rfl
  obtain ⟨hLLi, hLL⟩ := tendsto_timeIntegral_trunc T hw hc₁ hc₂ hφ₁ hφ₂
  refine tendsto_of_approx (ν := μ)
    (S := fun n ω ↦ ∑ j ∈ Finset.range n, w (unifPart T n j) ω
        * (itoContinuousMod T hW.measurable φ₁ (unifPart T n (j + 1)) ω
            - itoContinuousMod T hW.measurable φ₁ (unifPart T n j) ω)
        * (itoContinuousMod T hW.measurable φ₂ (unifPart T n (j + 1)) ω
            - itoContinuousMod T hW.measurable φ₂ (unifPart T n j) ω))
    (S' := fun k n ω ↦ ∑ j ∈ Finset.range n, w (unifPart T n j) ω
        * (itoContinuousMod T hW.measurable (truncKernel (μ := μ) T hc₁ k) (unifPart T n (j + 1)) ω
            - itoContinuousMod T hW.measurable (truncKernel (μ := μ) T hc₁ k) (unifPart T n j) ω)
        * (itoContinuousMod T hW.measurable (truncKernel (μ := μ) T hc₂ k) (unifPart T n (j + 1)) ω
            - itoContinuousMod T hW.measurable (truncKernel (μ := μ) T hc₂ k) (unifPart T n j) ω))
    (L := fun ω ↦ ∫ s, w s ω * h₁ s ω * h₂ s ω ∂(timeMeasure_T T))
    (L' := fun (k : ℕ) ω ↦ ∫ s, w s ω * clampAt k (h₁ s ω) * clampAt k (h₂ s ω)
      ∂(timeMeasure_T T))
    (e := fun k ↦ C₀ * (‖φ₁ - truncKernel (μ := μ) T hc₁ k‖ * ‖φ₂‖
      + ‖truncKernel (μ := μ) T hc₁ k‖ * ‖φ₂ - truncKernel (μ := μ) T hc₂ k‖))
    (fun n => integrable_frozenBilinear hW hWc hW hWc T n hwm hw.bdd φ₁ φ₂)
    (fun k n => integrable_frozenBilinear hW hWc hW hWc T n hwm hw.bdd _ _)
    (fun k => ?_) hLLi
    (fun k n => integral_abs_frozenBilinear_sub_le hW hWc hW hWc T n hw.nonneg hwm hw.bdd _ _ _ _)
    (tendsto_approxError C₀ (tendsto_truncKernel T hc₁ hφ₁) (tendsto_truncKernel T hc₂ hφ₂))
    hLL (fun k => ?_)
  · have hg := (hw.mul (hc₁.trunc k)).mul (hc₂.trunc k)
    exact (memLp_timeIntegral (ℱ := ℱ) T hg.pred hg.bdd).integrable one_le_two
  · exact tendsto_covariation_same hW hWc T hw (hc₁.trunc k) (hc₂.trunc k)
      (coeFn_truncKernel T hc₁ k) (coeFn_truncKernel T hc₂ k)

/-- Independent drivers, continuous adapted integrands (no boundedness):
`Σ_j w(t_j) ΔM^B_j ΔM^Z_j → 0` in `L¹(μ)`. -/
theorem tendsto_covariation_cross_L2 {B Z : ℝ≥0 → Ω → ℝ} (hP : IndependentPair ℱ B Z μ)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) (hZc : ∀ ω, Continuous fun u : ℝ≥0 ↦ Z u ω)
    (T : ℝ≥0) {w h₁ h₂ : ℝ≥0 → Ω → ℝ} {C₀ : ℝ} (hw : GoodProcess ℱ μ T w C₀)
    (hc₁ : ContProcess ℱ μ T h₁) (hc₂ : ContProcess ℱ μ T h₂)
    {φ₁ φ₂ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)}
    (hφ₁ : ⇑φ₁ =ᵐ[trimMeasure_T (μ := μ) T ℱ] fun p ↦ h₁ p.1 p.2)
    (hφ₂ : ⇑φ₂ =ᵐ[trimMeasure_T (μ := μ) T ℱ] fun p ↦ h₂ p.1 p.2) :
    Tendsto (fun n : ℕ ↦ ∫ ω, |∑ j ∈ Finset.range n, w (unifPart T n j) ω
        * (itoContinuousMod T hP.left.measurable φ₁ (unifPart T n (j + 1)) ω
            - itoContinuousMod T hP.left.measurable φ₁ (unifPart T n j) ω)
        * (itoContinuousMod T hP.right.measurable φ₂ (unifPart T n (j + 1)) ω
            - itoContinuousMod T hP.right.measurable φ₂ (unifPart T n j) ω)| ∂μ) atTop (𝓝 0) := by
  have hwm : ∀ t, Measurable (w t) := fun t => (hw.adapted t).mono (ℱ.le t) le_rfl
  have key := tendsto_of_approx (ν := μ)
    (S := fun n ω ↦ ∑ j ∈ Finset.range n, w (unifPart T n j) ω
        * (itoContinuousMod T hP.left.measurable φ₁ (unifPart T n (j + 1)) ω
            - itoContinuousMod T hP.left.measurable φ₁ (unifPart T n j) ω)
        * (itoContinuousMod T hP.right.measurable φ₂ (unifPart T n (j + 1)) ω
            - itoContinuousMod T hP.right.measurable φ₂ (unifPart T n j) ω))
    (S' := fun k n ω ↦ ∑ j ∈ Finset.range n, w (unifPart T n j) ω
        * (itoContinuousMod T hP.left.measurable (truncKernel (μ := μ) T hc₁ k)
              (unifPart T n (j + 1)) ω
            - itoContinuousMod T hP.left.measurable (truncKernel (μ := μ) T hc₁ k)
              (unifPart T n j) ω)
        * (itoContinuousMod T hP.right.measurable (truncKernel (μ := μ) T hc₂ k)
              (unifPart T n (j + 1)) ω
            - itoContinuousMod T hP.right.measurable (truncKernel (μ := μ) T hc₂ k)
              (unifPart T n j) ω))
    (L := fun _ ↦ (0 : ℝ)) (L' := fun _ _ ↦ (0 : ℝ))
    (e := fun k ↦ C₀ * (‖φ₁ - truncKernel (μ := μ) T hc₁ k‖ * ‖φ₂‖
      + ‖truncKernel (μ := μ) T hc₁ k‖ * ‖φ₂ - truncKernel (μ := μ) T hc₂ k‖))
    (fun n => integrable_frozenBilinear hP.left hBc hP.right hZc T n hwm hw.bdd φ₁ φ₂)
    (fun k n => integrable_frozenBilinear hP.left hBc hP.right hZc T n hwm hw.bdd _ _)
    (fun _ => integrable_const _) (fun _ => by simp)
    (fun k n => integral_abs_frozenBilinear_sub_le hP.left hBc hP.right hZc T n hw.nonneg hwm
      hw.bdd _ _ _ _)
    (tendsto_approxError C₀ (tendsto_truncKernel T hc₁ hφ₁) (tendsto_truncKernel T hc₂ hφ₂))
    (by simp only [sub_self, abs_zero, integral_zero]; exact tendsto_const_nhds)
    (fun k => by
      simpa only [sub_zero] using tendsto_covariation_cross hP hBc hZc T hw (hc₁.trunc k)
        (hc₂.trunc k) (coeFn_truncKernel T hc₁ k) (coeFn_truncKernel T hc₂ k))
  simpa only [sub_zero] using key

end CommonCovariation
end MathFin.FilteredIto
