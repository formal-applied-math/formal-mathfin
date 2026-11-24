/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import Mathlib.Order.Interval.Set.Union
public import MathFin.Probability.Brownian.Ito.Filtered.CommonCovariationL2

/-!
# Itô's formula on the common filtration

For an `ι`-indexed continuous Itô process

  `Yⁱ_t = yⁱ + ∫₀ᵗ aⁱ ds + ∫₀ᵗ bⁱ dB + ∫₀ᵗ cⁱ dZ`

driven by an independent pair `(B, Z)` of `ℱ`-Brownian motions, and a `C²` function `f`
with bounded first and second derivatives and uniformly continuous second derivative,

  `f(Y_T) = f(y) + ∫₀ᵀ (∑ᵢ ∂ᵢf(Y) aⁱ + ½ ∑ᵢₖ ∂ᵢₖf(Y)(bⁱbᵏ + cⁱcᵏ)) ds
      + ∑ᵢ ∫₀ᵀ ∂ᵢf(Y) bⁱ dB + ∑ᵢ ∫₀ᵀ ∂ᵢf(Y) cⁱ dZ`   a.s.

The proof is by uniform partitions: telescoping, second-order Taylor expansion with a
uniform remainder, `L¹` convergence of the Riemann–Stieltjes and covariation sums
(`CommonRiemann`, `CommonCovariationL2`), pathwise convergence of the drift sums, and a
common almost surely convergent subsequence.

## Main definitions

* `pd2`
* `ItoTest`
* `ItoProc`

## Main results

* `tendsto_rs_pair`
* `tendsto_cov_pair`
* `ito_formula`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto
namespace CommonIto

open MeasureTheory ProbabilityTheory Filter Topology
open MathFin.FilteredIto.CommonNoise MathFin.FilteredIto.CommonL2
      MathFin.FilteredIto.CommonPredictable MathFin.FilteredIto.CommonIntegral
  MathFin.FilteredIto.CommonProcess MathFin.FilteredIto.CommonProcessGeneral
        MathFin.FilteredIto.CommonContinuous
  MathFin.FilteredIto.CommonLocality MathFin.FilteredIto.CommonStopping
        MathFin.FilteredIto.CommonRiemann MathFin.FilteredIto.CommonCovariation
open MathFin (unifPart)
open scoped NNReal ENNReal

local notation "leb" => MathFin.ItoIntegralL2.timeMeasure

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-! ### From `L¹` convergence to an almost surely convergent subsequence -/

lemma exists_subseq_ae_of_integral_abs {F : ℕ → Ω → ℝ} (hF : ∀ n, Integrable (F n) μ)
    (h : Tendsto (fun n ↦ ∫ ω, |F n ω| ∂μ) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂μ, Tendsto (fun k ↦ F (ns k) ω) atTop (𝓝 0) := by
  have hm : TendstoInMeasure μ F atTop (fun _ ↦ (0 : ℝ)) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero ?_
    have e : ∀ n, eLpNorm (F n - fun _ ↦ (0 : ℝ)) 1 μ = ENNReal.ofReal (∫ ω, |F n ω| ∂μ) := by
      intro n
      have h0 : (F n - fun _ ↦ (0 : ℝ)) = F n := by ext ω; simp
      rw [h0, eLpNorm_one_eq_lintegral_enorm (hF n).aestronglyMeasurable, ←
            ofReal_integral_norm_eq_lintegral_enorm (hF n)]
      simp only [Real.norm_eq_abs]
    simp_rw [e]
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal h
  exact hm.exists_seq_tendsto_ae

lemma exists_subseq_ae_of_integral_abs_fintype {κ : Type*} [Fintype κ] {F : κ → ℕ → Ω → ℝ}
    (hF : ∀ m n, Integrable (F m n) μ)
    (h : ∀ m, Tendsto (fun n ↦ ∫ ω, |F m n ω| ∂μ) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ ω ∂μ, ∀ m, Tendsto (fun k ↦ F m (ns k) ω) atTop (𝓝 0) := by
  have hEi : ∀ n, Integrable (fun ω ↦ ∑ m, |F m n ω|) μ := fun n =>
    integrable_finsetSum _ fun m _ => (hF m n).abs
  have hEl : Tendsto (fun n ↦ ∫ ω, |(∑ m, |F m n ω|)| ∂μ) atTop (𝓝 0) := by
    have e : ∀ n, ∫ ω, |(∑ m, |F m n ω|)| ∂μ = ∑ m, ∫ ω, |F m n ω| ∂μ := by
      intro n
      rw [← integral_finsetSum _ fun m _ => (hF m n).abs]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      exact abs_of_nonneg (Finset.sum_nonneg fun m _ => abs_nonneg _)
    simp_rw [e]
    simpa using tendsto_finsetSum (Finset.univ : Finset κ) fun m _ => h m
  obtain ⟨ns, hns, hae⟩ := exists_subseq_ae_of_integral_abs hEi hEl
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hae] with ω hω m
  refine squeeze_zero_norm (fun k => ?_) hω
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun m ↦ |F m (ns k) ω|) (fun m _ => abs_nonneg _)
    (Finset.mem_univ m)

/-! ### Grid increments of continuous paths -/

lemma eventually_small_incr {T : ℝ≥0} {g : ℝ≥0 → ℝ} (hg : ContinuousOn g (Set.Icc 0 T))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ j < n, |g (unifPart T n (j + 1)) - g (unifPart T n j)| < ε := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hg
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδε⟩ := huc ε hε
  have hT : Tendsto (fun n : ℕ ↦ (T : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (T : ℝ)
  filter_upwards [hT.eventually (gt_mem_nhds hδ)] with n hn j hj
  have h1 : unifPart T n (j + 1) ∈ Set.Icc 0 T := ⟨zero_le, upart_le T (by omega)⟩
  have h2 : unifPart T n j ∈ Set.Icc 0 T := ⟨zero_le, upart_le T hj.le⟩
  have hd : dist (unifPart T n (j + 1)) (unifPart T n j) < δ := by
    rw [upart_succ, NNReal.dist_eq]
    simp only [NNReal.coe_add, add_sub_cancel_left, NNReal.coe_div, NNReal.coe_natCast]
    rwa [abs_of_nonneg (by positivity)]
  have := hδε _ h1 _ h2 hd
  rwa [Real.dist_eq] at this

/-! ### Drift integrals over the grid -/

lemma integrableOn_of_continuousOn {T : ℝ≥0} {g : ℝ≥0 → ℝ} (hg : ContinuousOn g (Set.Icc 0 T)) :
    IntegrableOn g (Set.Ioc 0 T) leb := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hm : AEStronglyMeasurable g (timeMeasureT T) :=
    (hg.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have : Integrable g (timeMeasureT T) :=
    Integrable.of_bound hm C (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs =>
      hC s (Set.Ioc_subset_Icc_self hs))
  exact this

lemma setIntegral_Ioc_sub {T x y : ℝ≥0} {a : ℝ≥0 → ℝ} (ha : IntegrableOn a (Set.Ioc 0 T) leb)
    (hxy : x ≤ y) (hyT : y ≤ T) :
    ∫ s in Set.Ioc 0 y, a s ∂leb - ∫ s in Set.Ioc 0 x, a s ∂leb
      = ∫ s in Set.Ioc x y, a s ∂leb := by
  rw [← Set.Ioc_union_Ioc_eq_Ioc (zero_le : (0 : ℝ≥0) ≤ x) hxy, setIntegral_union
    (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
    (ha.mono_set (Set.Ioc_subset_Ioc le_rfl (hxy.trans hyT)))
    (ha.mono_set (Set.Ioc_subset_Ioc (zero_le : (0 : ℝ≥0) ≤ x) hyT))]
  ring

lemma sum_grid_sub {T : ℝ≥0} {n : ℕ} (hn : 0 < n) (G : ℝ≥0 → ℝ) :
    ∑ j ∈ Finset.range n, (G (unifPart T n (j + 1)) - G (unifPart T n j)) = G T - G 0 := by
  rw [Finset.sum_range_sub (fun j ↦ G (unifPart T n j)), upart_self T hn, upart_zero]

lemma sum_abs_incr_le {T : ℝ≥0} {a : ℝ≥0 → ℝ} (ha : IntegrableOn a (Set.Ioc 0 T) leb) (n : ℕ) :
    ∑ j ∈ Finset.range n, |∫ s in Set.Ioc 0 (unifPart T n (j + 1)), a s ∂leb
      - ∫ s in Set.Ioc 0 (unifPart T n j), a s ∂leb| ≤ ∫ s in Set.Ioc 0 T, |a s| ∂leb := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Finset.range_zero, Finset.sum_empty]
    exact setIntegral_nonneg measurableSet_Ioc fun s _ => abs_nonneg _
  have key : ∀ j ∈ Finset.range n, |∫ s in Set.Ioc 0 (unifPart T n (j + 1)), a s ∂leb
      - ∫ s in Set.Ioc 0 (unifPart T n j), a s ∂leb|
        ≤ ∫ s in Set.Ioc 0 (unifPart T n (j + 1)), |a s| ∂leb
          - ∫ s in Set.Ioc 0 (unifPart T n j), |a s| ∂leb := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [setIntegral_Ioc_sub ha (upart_mono T n (Nat.le_succ j)) (upart_le T hj'),
      setIntegral_Ioc_sub (Integrable.abs ha) (upart_mono T n (Nat.le_succ j)) (upart_le T hj')]
    exact abs_integral_le_integral_abs
  refine (Finset.sum_le_sum key).trans (le_of_eq ?_)
  rw [sum_grid_sub hn (fun t ↦ ∫ s in Set.Ioc 0 t, |a s| ∂leb)]
  simp

/-- Pathwise Riemann sums of a continuous integrand against a drift integral. -/
lemma tendsto_drift_riemann {T : ℝ≥0} {g a : ℝ≥0 → ℝ} (hg : ContinuousOn g (Set.Icc 0 T))
    (ha : IntegrableOn a (Set.Ioc 0 T) leb) :
    Tendsto (fun n : ℕ ↦ ∑ j ∈ Finset.range n, g (unifPart T n j) *
      (∫ s in Set.Ioc 0 (unifPart T n (j + 1)), a s ∂leb
        - ∫ s in Set.Ioc 0 (unifPart T n j), a s ∂leb))
      atTop (𝓝 (∫ s in Set.Ioc 0 T, g s * a s ∂leb)) := by
  obtain ⟨Cg, hCg⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hga : IntegrableOn (fun s ↦ g s * a s) (Set.Ioc 0 T) leb := by
    refine Integrable.bdd_mul (c := Cg) ha
      ((hg.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc) ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun s hs =>
      hCg s (Set.Ioc_subset_Icc_self hs)
  set K := ∫ s in Set.Ioc 0 T, |a s| ∂leb with hK
  have hK0 : 0 ≤ K := setIntegral_nonneg measurableSet_Ioc fun s _ => abs_nonneg _
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hg
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε' : 0 < ε / (K + 1) := by positivity
  obtain ⟨δ, hδ, hδε⟩ := huc (ε / (K + 1)) hε'
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((tendsto_const_div_atTop_nhds_zero_nat (T : ℝ)).eventually (gt_mem_nhds hδ))
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 0 < n := lt_of_lt_of_le zero_lt_one (le_of_max_le_right hn)
  have hTn : (T : ℝ) / n < δ := hN n (le_of_max_le_left hn)
  have hcell : ∀ j ∈ Finset.range n,
      |g (unifPart T n j) * (∫ s in Set.Ioc 0 (unifPart T n (j + 1)), a s ∂leb
          - ∫ s in Set.Ioc 0 (unifPart T n j), a s ∂leb)
        - (∫ s in Set.Ioc 0 (unifPart T n (j + 1)), g s * a s ∂leb
          - ∫ s in Set.Ioc 0 (unifPart T n j), g s * a s ∂leb)|
      ≤ ε / (K + 1) * (∫ s in Set.Ioc 0 (unifPart T n (j + 1)), |a s| ∂leb
          - ∫ s in Set.Ioc 0 (unifPart T n j), |a s| ∂leb) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hle : unifPart T n j ≤ unifPart T n (j + 1) := upart_mono T n (Nat.le_succ j)
    have hT1 : unifPart T n (j + 1) ≤ T := upart_le T hj'
    rw [setIntegral_Ioc_sub ha hle hT1, setIntegral_Ioc_sub hga hle hT1,
      setIntegral_Ioc_sub (Integrable.abs ha) hle hT1]
    have hsub : Set.Ioc (unifPart T n j) (unifPart T n (j + 1)) ⊆ Set.Ioc 0 T :=
      Set.Ioc_subset_Ioc zero_le hT1
    have ha' : IntegrableOn a (Set.Ioc (unifPart T n j) (unifPart T n (j + 1))) leb :=
      ha.mono_set hsub
    have hga' : IntegrableOn (fun s ↦ g s * a s)
        (Set.Ioc (unifPart T n j) (unifPart T n (j + 1))) leb := hga.mono_set hsub
    have e1 : g (unifPart T n j) * ∫ s in Set.Ioc (unifPart T n j) (unifPart T n (j + 1)), a s ∂leb
        - ∫ s in Set.Ioc (unifPart T n j) (unifPart T n (j + 1)), g s * a s ∂leb
        = ∫ s in Set.Ioc (unifPart T n j) (unifPart T n (j + 1)),
            (g (unifPart T n j) - g s) * a s ∂leb := by
      rw [← integral_const_mul, ← integral_sub (ha'.const_mul _) hga']
      refine integral_congr_ae (Eventually.of_forall fun s => ?_)
      show g (unifPart T n j) * a s - g s * a s = (g (unifPart T n j) - g s) * a s
      ring
    have e2 : ε / (K + 1) * ∫ s in Set.Ioc (unifPart T n j) (unifPart T n (j + 1)), |a s| ∂leb
        = ∫ s in Set.Ioc (unifPart T n j) (unifPart T n (j + 1)), ε / (K + 1) * |a s| ∂leb :=
      (integral_const_mul _ _).symm
    rw [e1, e2]
    have hint1 : IntegrableOn (fun s ↦ |(g (unifPart T n j) - g s) * a s|)
        (Set.Ioc (unifPart T n j) (unifPart T n (j + 1))) leb := by
      have : IntegrableOn (fun s ↦ g (unifPart T n j) * a s - g s * a s)
          (Set.Ioc (unifPart T n j) (unifPart T n (j + 1))) leb := (ha'.const_mul _).sub hga'
      refine (Integrable.abs this).congr (Eventually.of_forall fun s => ?_)
      show |g (unifPart T n j) * a s - g s * a s| = |(g (unifPart T n j) - g s) * a s|
      rw [sub_mul]
    refine (abs_integral_le_integral_abs).trans (setIntegral_mono_on hint1
      ((Integrable.abs ha').const_mul _) measurableSet_Ioc fun s hs => ?_)
    have hsI : s ∈ Set.Icc 0 T := Set.Ioc_subset_Icc_self (hsub hs)
    have htI : unifPart T n j ∈ Set.Icc 0 T := ⟨zero_le, hle.trans hT1⟩
    have hd : dist (unifPart T n j) s < δ := by
      rw [NNReal.dist_eq, abs_sub_comm,
        abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hs.1.le))]
      have h2 : (s : ℝ) ≤ unifPart T n (j + 1) := NNReal.coe_le_coe.mpr hs.2
      rw [upart_succ, NNReal.coe_add, NNReal.coe_div, NNReal.coe_natCast] at h2
      linarith
    have hgs := (hδε _ htI _ hsI hd).le
    rw [Real.dist_eq] at hgs
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hgs (abs_nonneg _)
  have hL : ∫ s in Set.Ioc 0 T, g s * a s ∂leb = ∑ j ∈ Finset.range n,
      (∫ s in Set.Ioc 0 (unifPart T n (j + 1)), g s * a s ∂leb
        - ∫ s in Set.Ioc 0 (unifPart T n j), g s * a s ∂leb) := by
    rw [sum_grid_sub hn1 (fun t ↦ ∫ s in Set.Ioc 0 t, g s * a s ∂leb)]
    simp
  have hKs : K = ∑ j ∈ Finset.range n,
      (∫ s in Set.Ioc 0 (unifPart T n (j + 1)), |a s| ∂leb
        - ∫ s in Set.Ioc 0 (unifPart T n j), |a s| ∂leb) := by
    rw [sum_grid_sub hn1 (fun t ↦ ∫ s in Set.Ioc 0 t, |a s| ∂leb)]
    simp [hK]
  rw [Real.dist_eq, hL, ← Finset.sum_sub_distrib]
  calc _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum hcell
    _ = ε / (K + 1) * K := by rw [← Finset.mul_sum, ← hKs]
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith

/-- Pathwise: `∑ⱼ g(tⱼ) Δuⱼ ΔAⱼ → 0` for a bounded `g`, a continuous `u` and a drift `A`. -/
lemma tendsto_drift_cross {T : ℝ≥0} {g u a : ℝ≥0 → ℝ} {C : ℝ} (hgb : ∀ t, |g t| ≤ C)
    (hu : ContinuousOn u (Set.Icc 0 T)) (ha : IntegrableOn a (Set.Ioc 0 T) leb) :
    Tendsto (fun n : ℕ ↦ ∑ j ∈ Finset.range n, g (unifPart T n j)
      * (u (unifPart T n (j + 1)) - u (unifPart T n j))
      * (∫ s in Set.Ioc 0 (unifPart T n (j + 1)), a s ∂leb
        - ∫ s in Set.Ioc 0 (unifPart T n j), a s ∂leb)) atTop (𝓝 0) := by
  set K := ∫ s in Set.Ioc 0 T, |a s| ∂leb
  have hK0 : 0 ≤ K := setIntegral_nonneg measurableSet_Ioc fun s _ => abs_nonneg _
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hgb 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hη : 0 < ε / (C * K + 1) := by positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (eventually_small_incr hu hη)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero]
  have hsum := sum_abs_incr_le ha n
  calc _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, C * (ε / (C * K + 1))
          * |∫ s in Set.Ioc 0 (unifPart T n (j + 1)), a s ∂leb
            - ∫ s in Set.Ioc 0 (unifPart T n j), a s ∂leb| := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right (mul_le_mul (hgb _)
          (hN n hn j (Finset.mem_range.mp hj)).le (abs_nonneg _) hC0) (abs_nonneg _)
    _ = C * (ε / (C * K + 1)) * ∑ j ∈ Finset.range n,
          |∫ s in Set.Ioc 0 (unifPart T n (j + 1)), a s ∂leb
            - ∫ s in Set.Ioc 0 (unifPart T n j), a s ∂leb| := by rw [Finset.mul_sum]
    _ ≤ C * (ε / (C * K + 1)) * K := by gcongr
    _ = ε * (C * K / (C * K + 1)) := by ring
    _ < ε := by
      refine mul_lt_of_lt_one_right hε ?_
      rw [div_lt_one (by positivity)]
      linarith

/-! ### Second-order Taylor expansion -/

lemma taylor_two_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (y h : E) {ε : ℝ}
    (hε : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ f) (y + s • h) - fderiv ℝ (fderiv ℝ f) y‖ ≤ ε) :
    |f (y + h) - f y - fderiv ℝ f y h - (1 / 2) * fderiv ℝ (fderiv ℝ f) y h h|
      ≤ ε * ‖h‖ ^ 2 := by
  have hε0 : 0 ≤ ε := (norm_nonneg (fderiv ℝ (fderiv ℝ f) (y + (0 : ℝ) • h)
    - fderiv ℝ (fderiv ℝ f) y)).trans (hε 0 ⟨le_rfl, zero_le_one⟩)
  have hd1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right one_add_one_eq_two.le
  have hd2 : Differentiable ℝ (fderiv ℝ f) := hf1.differentiable one_ne_zero
  set D2 := fderiv ℝ (fderiv ℝ f) y with hD2
  set ψ : ℝ → ℝ := fun s ↦ f (y + s • h) - f y - s * fderiv ℝ f y h - s * s / 2 * D2 h h
    with hψdef
  set ψ' : ℝ → ℝ := fun s ↦ fderiv ℝ f (y + s • h) h - fderiv ℝ f y h - s * D2 h h
    with hψ'def
  set ψ'' : ℝ → ℝ := fun s ↦ fderiv ℝ (fderiv ℝ f) (y + s • h) h h - D2 h h with hψ''def
  have hpath : ∀ s : ℝ, HasDerivAt (fun s : ℝ ↦ y + s • h) h s := by
    intro s
    have := ((hasDerivAt_id' s).smul_const h).const_add y
    simpa using this
  have hψ : ∀ s, HasDerivAt ψ (ψ' s) s := by
    intro s
    have h1 : HasDerivAt (fun s ↦ f (y + s • h)) (fderiv ℝ f (y + s • h) h) s :=
      (hd1 (y + s • h)).hasFDerivAt.comp_hasDerivAt s (hpath s)
    have h2 : HasDerivAt (fun s : ℝ ↦ s * fderiv ℝ f y h) (fderiv ℝ f y h) s := by
      simpa using (hasDerivAt_id' s).mul_const (fderiv ℝ f y h)
    have h3 : HasDerivAt (fun s : ℝ ↦ s * s / 2 * D2 h h) (s * D2 h h) s := by
      have hss : HasDerivAt (fun s : ℝ ↦ s * s) (1 * s + s * 1) s :=
        (hasDerivAt_id' s).mul (hasDerivAt_id' s)
      exact ((hss.div_const 2).mul_const (D2 h h)).congr_deriv (by ring)
    exact ((h1.sub_const (f y)).sub h2).sub h3
  have hψ' : ∀ s, HasDerivAt ψ' (ψ'' s) s := by
    intro s
    have h1 : HasDerivAt (fun s ↦ fderiv ℝ f (y + s • h))
        (fderiv ℝ (fderiv ℝ f) (y + s • h) h) s :=
      (hd2 (y + s • h)).hasFDerivAt.comp_hasDerivAt s (hpath s)
    have h1' : HasDerivAt (fun s ↦ fderiv ℝ f (y + s • h) h)
        (fderiv ℝ (fderiv ℝ f) (y + s • h) h h) s := by
      have := h1.clm_apply (hasDerivAt_const s h)
      simpa using this
    have h2 : HasDerivAt (fun s : ℝ ↦ s * D2 h h) (D2 h h) s := by
      simpa using (hasDerivAt_id' s).mul_const (D2 h h)
    exact (h1'.sub_const _).sub h2
  have hb2 : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖ψ'' s‖ ≤ ε * ‖h‖ ^ 2 := by
    intro s hs
    have e : ψ'' s = (fderiv ℝ (fderiv ℝ f) (y + s • h) - D2) h h := by
      simp only [hψ''def, _root_.sub_apply]
    calc ‖ψ'' s‖ = ‖(fderiv ℝ (fderiv ℝ f) (y + s • h) - D2) h h‖ := by rw [e]
      _ ≤ ‖fderiv ℝ (fderiv ℝ f) (y + s • h) - D2‖ * ‖h‖ * ‖h‖ :=
          ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ ε * ‖h‖ * ‖h‖ := by gcongr; exact hε s hs
      _ = ε * ‖h‖ ^ 2 := by ring
  have hb1 : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖ψ' s‖ ≤ ε * ‖h‖ ^ 2 := by
    intro s hs
    have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := ψ') (f' := ψ'')
      (fun x _ => (hψ' x).hasDerivWithinAt) (fun x hx => hb2 x (Set.Ico_subset_Icc_self hx)) s hs
    have h0 : ψ' 0 = 0 := by simp [hψ'def]
    rw [h0, sub_zero] at key
    calc ‖ψ' s‖ ≤ ε * ‖h‖ ^ 2 * (s - 0) := key
      _ ≤ ε * ‖h‖ ^ 2 * 1 := by
          gcongr
          linarith [hs.2]
      _ = ε * ‖h‖ ^ 2 := mul_one _
  have key := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := ψ) (f' := ψ')
    (fun x _ => (hψ x).hasDerivWithinAt) (fun x hx => hb1 x (Set.Ico_subset_Icc_self hx))
  have h0 : ψ 0 = 0 := by simp [hψdef]
  have h1 : ψ 1 = f (y + h) - f y - fderiv ℝ f y h - (1 / 2) * D2 h h := by
    simp only [hψdef, one_smul, one_mul]
  rw [h0, sub_zero, h1, Real.norm_eq_abs] at key
  exact key

lemma taylor_two_uniform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : ContDiff ℝ 2 f)
    (huc : ∀ ε > 0, ∃ δ > 0, ∀ y z : E, ‖y - z‖ < δ →
      ‖fderiv ℝ (fderiv ℝ f) y - fderiv ℝ (fderiv ℝ f) z‖ < ε) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y h : E, ‖h‖ < δ →
      |f (y + h) - f y - fderiv ℝ f y h - (1 / 2) * fderiv ℝ (fderiv ℝ f) y h h|
        ≤ ε * ‖h‖ ^ 2 := by
  obtain ⟨δ, hδ, hδε⟩ := huc ε hε
  refine ⟨δ, hδ, fun y h hh => taylor_two_bound hf y h fun s hs => ?_⟩
  have hd : ‖(y + s • h) - y‖ < δ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc s * ‖h‖ ≤ 1 * ‖h‖ := by gcongr; exact hs.2
      _ < δ := by rwa [one_mul]
  exact (hδε _ _ hd).le

/-! ### Coordinates -/

lemma clm_apply_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : (ι → ℝ) →L[ℝ] F) (h : ι → ℝ) :
    L h = ∑ i, h i • L (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single h]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_smul]
  congr 1
  ext k
  by_cases hk : k = i
  · subst hk; simp
  · simp [hk]

lemma fderiv_apply_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → ℝ)
    (y h : ι → ℝ) : fderiv ℝ f y h = ∑ i, h i * fderiv ℝ f y (Pi.single i 1) := by
  rw [clm_apply_eq_sum (fderiv ℝ f y) h]
  simp only [smul_eq_mul]

lemma fderiv2_apply_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → ℝ)
    (y h : ι → ℝ) : fderiv ℝ (fderiv ℝ f) y h h
      = ∑ i, ∑ k, h i * h k * fderiv ℝ (fderiv ℝ f) y (Pi.single i 1) (Pi.single k 1) := by
  rw [clm_apply_eq_sum (fderiv ℝ (fderiv ℝ f) y) h, _root_.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [_root_.smul_apply,
    clm_apply_eq_sum (fderiv ℝ (fderiv ℝ f) y (Pi.single i 1)) h, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [smul_eq_mul]
  ring

lemma norm_sq_le_sum_sq {ι : Type*} [Fintype ι] (h : ι → ℝ) : ‖h‖ ^ 2 ≤ ∑ i, h i ^ 2 := by
  have hs : ‖h‖ ≤ Real.sqrt (∑ i, h i ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun k ↦ h k ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ i))
  calc ‖h‖ ^ 2 ≤ Real.sqrt (∑ i, h i ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hs 2
    _ = ∑ i, h i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-! ### Test functions and grid increments -/

/-- Increment of a path over the `j`-th cell of the uniform grid of `[0, T]` with `n` cells. -/
def gridIncr (T : ℝ≥0) (n j : ℕ) (g : ℝ≥0 → ℝ) : ℝ := g (unifPart T n (j + 1)) - g (unifPart T n j)

/-- The partial derivative `∂ᵢ f(y)`. -/
def pd {ι : Type*} [DecidableEq ι] (f : (ι → ℝ) → ℝ) (i : ι) (y : ι → ℝ) : ℝ :=
  fderiv ℝ f y (Pi.single i 1)

/-- The second partial derivative `∂ᵢ∂ₖ f(y)`. -/
def pd2 {ι : Type*} [DecidableEq ι] (f : (ι → ℝ) → ℝ) (i k : ι) (y : ι → ℝ) : ℝ :=
  fderiv ℝ (fderiv ℝ f) y (Pi.single i 1) (Pi.single k 1)

/-- Test functions for Itô's formula: `C²`, bounded first and second derivatives, uniformly
continuous second derivative. -/
structure ItoTest {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (C₁ C₂ : ℝ) : Prop where
  contDiff : ContDiff ℝ 2 f
  bdd1 : ∀ y, ‖fderiv ℝ f y‖ ≤ C₁
  bdd2 : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ C₂
  unif : ∀ ε > 0, ∃ δ > 0, ∀ y z : ι → ℝ, ‖y - z‖ < δ →
    ‖fderiv ℝ (fderiv ℝ f) y - fderiv ℝ (fderiv ℝ f) z‖ < ε

section TestFunctions

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℝ} {C₁ C₂ : ℝ}

lemma norm_single_le_one (i : ι) : ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun k => ?_
  by_cases hk : k = i
  · subst hk; simp
  · simp [hk]

lemma ItoTest.continuous_pd (hf : ItoTest f C₁ C₂) (i : ι) : Continuous (pd f i) :=
  (hf.contDiff.continuous_fderiv (by norm_num)).clm_apply continuous_const

lemma ItoTest.continuous_pd2 (hf : ItoTest f C₁ C₂) (i k : ι) : Continuous (pd2 f i k) :=
  (((hf.contDiff.fderiv_right one_add_one_eq_two.le).continuous_fderiv one_ne_zero).clm_apply
    continuous_const).clm_apply continuous_const

omit [DecidableEq ι] in
lemma ItoTest.nonneg₁ (hf : ItoTest f C₁ C₂) : 0 ≤ C₁ :=
  (norm_nonneg (fderiv ℝ f 0)).trans (hf.bdd1 0)

omit [DecidableEq ι] in
lemma ItoTest.nonneg₂ (hf : ItoTest f C₁ C₂) : 0 ≤ C₂ :=
  (norm_nonneg (fderiv ℝ (fderiv ℝ f) 0)).trans (hf.bdd2 0)

lemma ItoTest.abs_pd_le (hf : ItoTest f C₁ C₂) (i : ι) (y : ι → ℝ) : |pd f i y| ≤ C₁ := by
  rw [← Real.norm_eq_abs, pd]
  calc ‖fderiv ℝ f y (Pi.single i 1)‖ ≤ ‖fderiv ℝ f y‖ * ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖ :=
        (fderiv ℝ f y).le_opNorm _
    _ ≤ C₁ * 1 := mul_le_mul (hf.bdd1 y) (norm_single_le_one i) (norm_nonneg _) hf.nonneg₁
    _ = C₁ := mul_one _

lemma ItoTest.abs_pd2_le (hf : ItoTest f C₁ C₂) (i k : ι) (y : ι → ℝ) : |pd2 f i k y| ≤ C₂ := by
  rw [← Real.norm_eq_abs, pd2]
  calc ‖fderiv ℝ (fderiv ℝ f) y (Pi.single i 1) (Pi.single k 1)‖
        ≤ ‖fderiv ℝ (fderiv ℝ f) y‖ * ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖
          * ‖(Pi.single k (1 : ℝ) : ι → ℝ)‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
    _ ≤ C₂ * 1 * 1 := mul_le_mul (mul_le_mul (hf.bdd2 y) (norm_single_le_one i) (norm_nonneg _)
          hf.nonneg₂) (norm_single_le_one k) (norm_nonneg _) (by have := hf.nonneg₂; positivity)
    _ = C₂ := by ring

end TestFunctions

/-- Reorganisation of the telescoped Taylor sums. -/
lemma sum_reorg {ι : Type*} [Fintype ι] (n : ℕ) (P1 P2 : ι → ℕ → ℝ)
    (Z1 Z2 Z3 : ι → ι → ℕ → ℝ) (R : ℕ → ℝ) :
    ∑ j ∈ Finset.range n, (∑ i, P1 i j + ∑ i, P2 i j
        + (1 / 2) * ∑ i, ∑ k, (Z1 i k j + Z2 i k j + Z3 i k j) + R j)
      = ∑ i, ∑ j ∈ Finset.range n, P1 i j + ∑ i, ∑ j ∈ Finset.range n, P2 i j
        + (1 / 2) * ∑ i, ∑ k, (∑ j ∈ Finset.range n, Z1 i k j
          + ∑ j ∈ Finset.range n, Z2 i k j + ∑ j ∈ Finset.range n, Z3 i k j)
        + ∑ j ∈ Finset.range n, R j := by
  have h1 : ∑ j ∈ Finset.range n, ∑ i, P1 i j = ∑ i, ∑ j ∈ Finset.range n, P1 i j :=
    Finset.sum_comm
  have h2 : ∑ j ∈ Finset.range n, ∑ i, P2 i j = ∑ i, ∑ j ∈ Finset.range n, P2 i j :=
    Finset.sum_comm
  have h3 : ∑ j ∈ Finset.range n, ∑ i, ∑ k, (Z1 i k j + Z2 i k j + Z3 i k j)
      = ∑ i, ∑ k, (∑ j ∈ Finset.range n, Z1 i k j + ∑ j ∈ Finset.range n, Z2 i k j
          + ∑ j ∈ Finset.range n, Z3 i k j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    h1, h2, h3]

/-! ### Deterministic assembly -/

/-- **Pathwise assembly of Itô's formula.** For a fixed path, given the limits of the
Riemann–Stieltjes sums and of the martingale covariation sums along a subsequence of uniform
partitions, the Taylor expansion of `f(Y_T) − f(y)` yields Itô's formula. -/
theorem ito_assembly {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
    {f : (ι → ℝ) → ℝ} {C₁ C₂ : ℝ} (hf : ItoTest f C₁ C₂)
    {y : ι → ℝ} {Y : ℝ≥0 → ι → ℝ} {MB MZ a : ι → ℝ≥0 → ℝ}
    (hYeq : ∀ i, ∀ t ≤ T, Y t i = y i + ∫ s in Set.Ioc 0 t, a i s ∂leb + MB i t + MZ i t)
    (ha : ∀ i, ContinuousOn (a i) (Set.Icc 0 T))
    (hMB : ∀ i, ContinuousOn (MB i) (Set.Icc 0 T)) (hMZ : ∀ i, ContinuousOn (MZ i) (Set.Icc 0 T))
    (hYc : ∀ i, ContinuousOn (fun t ↦ Y t i) (Set.Icc 0 T))
    (hMB0 : ∀ i, MB i 0 = 0) (hMZ0 : ∀ i, MZ i 0 = 0)
    {ns : ℕ → ℕ} (hns : StrictMono ns) {IR : ι → ℝ} {LQ : ι → ι → ℝ} {LQ1 : ι → ℝ}
    (hRS : ∀ i, Tendsto (fun m ↦ ∑ j ∈ Finset.range (ns m), pd f i (Y (unifPart T (ns m) j)) *
        (gridIncr T (ns m) j (MB i) + gridIncr T (ns m) j (MZ i))) atTop (𝓝 (IR i)))
    (hQ : ∀ i k, Tendsto (fun m ↦ ∑ j ∈ Finset.range (ns m),
        pd2 f i k (Y (unifPart T (ns m) j))
          * (gridIncr T (ns m) j (MB i) + gridIncr T (ns m) j (MZ i))
          * (gridIncr T (ns m) j (MB k) + gridIncr T (ns m) j (MZ k))) atTop (𝓝 (LQ i k)))
    (hQ1 : ∀ i, Tendsto (fun m ↦ ∑ j ∈ Finset.range (ns m),
        (gridIncr T (ns m) j (MB i) + gridIncr T (ns m) j (MZ i))
          * (gridIncr T (ns m) j (MB i) + gridIncr T (ns m) j (MZ i))) atTop (𝓝 (LQ1 i))) :
    f (Y T) = f y + ∑ i, ∫ s in Set.Ioc 0 T, pd f i (Y s) * a i s ∂leb
      + ∑ i, IR i + (1 / 2) * ∑ i, ∑ k, LQ i k := by
  have haI : ∀ i, IntegrableOn (a i) (Set.Ioc 0 T) leb := fun i =>
    integrableOn_of_continuousOn (ha i)
  have hYcv : ContinuousOn Y (Set.Icc 0 T) := continuousOn_pi.mpr hYc
  -- increments of the coordinates
  have hdec : ∀ n j, j < n → ∀ i, gridIncr T n j (fun t ↦ Y t i)
      = gridIncr T n j (fun t ↦ ∫ s in Set.Ioc 0 t, a i s ∂leb)
        + (gridIncr T n j (MB i) + gridIncr T n j (MZ i)) := by
    intro n j hj i
    simp only [gridIncr]
    rw [hYeq i _ (upart_le T (Nat.succ_le_of_lt hj)), hYeq i _ (upart_le T hj.le)]
    ring
  have hY0 : Y 0 = y := by
    funext i
    rw [hYeq i 0 zero_le, hMB0, hMZ0]
    simp
  -- the per-cell Taylor identity
  have hstep : ∀ n j, j < n → f (Y (unifPart T n (j + 1))) - f (Y (unifPart T n j)) =
      ∑ i, pd f i (Y (unifPart T n j)) * gridIncr T n j (fun t ↦ ∫ s in Set.Ioc 0 t, a i s ∂leb)
      + ∑ i, pd f i (Y (unifPart T n j)) * (gridIncr T n j (MB i) + gridIncr T n j (MZ i))
      + (1 / 2) * ∑ i, ∑ k, (pd2 f i k (Y (unifPart T n j))
            * (gridIncr T n j (MB i) + gridIncr T n j (MZ i))
            * (gridIncr T n j (MB k) + gridIncr T n j (MZ k))
          + pd2 f i k (Y (unifPart T n j)) * gridIncr T n j (fun t ↦ Y t k)
            * gridIncr T n j (fun t ↦ ∫ s in Set.Ioc 0 t, a i s ∂leb)
          + pd2 f i k (Y (unifPart T n j)) * gridIncr T n j (fun t ↦ MB i t + MZ i t)
            * gridIncr T n j (fun t ↦ ∫ s in Set.Ioc 0 t, a k s ∂leb))
      + (f (Y (unifPart T n (j + 1))) - f (Y (unifPart T n j))
          - fderiv ℝ f (Y (unifPart T n j)) (Y (unifPart T n (j + 1)) - Y (unifPart T n j))
          - (1 / 2) * fderiv ℝ (fderiv ℝ f) (Y (unifPart T n j))
              (Y (unifPart T n (j + 1)) - Y (unifPart T n j))
              (Y (unifPart T n (j + 1)) - Y (unifPart T n j))) := by
    intro n j hj
    have hd : ∀ i, (Y (unifPart T n (j + 1)) - Y (unifPart T n j)) i
        = gridIncr T n j (fun t ↦ Y t i) := fun i => rfl
    have e1 : fderiv ℝ f (Y (unifPart T n j)) (Y (unifPart T n (j + 1)) - Y (unifPart T n j))
        = ∑ i, pd f i (Y (unifPart T n j))
            * gridIncr T n j (fun t ↦ ∫ s in Set.Ioc 0 t, a i s ∂leb)
          + ∑ i, pd f i (Y (unifPart T n j)) * (gridIncr T n j (MB i) + gridIncr T n j (MZ i)) := by
      rw [fderiv_apply_eq_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hd i, hdec n j hj i]
      simp only [pd]
      ring
    have e2 : fderiv ℝ (fderiv ℝ f) (Y (unifPart T n j))
          (Y (unifPart T n (j + 1)) - Y (unifPart T n j))
          (Y (unifPart T n (j + 1)) - Y (unifPart T n j))
        = ∑ i, ∑ k, (pd2 f i k (Y (unifPart T n j))
              * (gridIncr T n j (MB i) + gridIncr T n j (MZ i))
              * (gridIncr T n j (MB k) + gridIncr T n j (MZ k))
            + pd2 f i k (Y (unifPart T n j)) * gridIncr T n j (fun t ↦ Y t k)
              * gridIncr T n j (fun t ↦ ∫ s in Set.Ioc 0 t, a i s ∂leb)
            + pd2 f i k (Y (unifPart T n j)) * gridIncr T n j (fun t ↦ MB i t + MZ i t)
              * gridIncr T n j (fun t ↦ ∫ s in Set.Ioc 0 t, a k s ∂leb)) := by
      rw [fderiv2_apply_eq_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      simp only [hd]
      have hi := hdec n j hj i
      have hk := hdec n j hj k
      have hm : gridIncr T n j (fun t ↦ MB i t + MZ i t)
          = gridIncr T n j (MB i) + gridIncr T n j (MZ i) := by
        simp only [gridIncr]; ring
      simp only [pd2]
      linear_combination (gridIncr T n j (fun t ↦ Y t k)
          * fderiv ℝ (fderiv ℝ f) (Y (unifPart T n j)) (Pi.single i 1) (Pi.single k 1)) * hi
        + (fderiv ℝ (fderiv ℝ f) (Y (unifPart T n j)) (Pi.single i 1) (Pi.single k 1)
          * (gridIncr T n j (MB i) + gridIncr T n j (MZ i))) * hk
        - (fderiv ℝ (fderiv ℝ f) (Y (unifPart T n j)) (Pi.single i 1) (Pi.single k 1)
          * gridIncr T n j (fun t ↦ ∫ s in Set.Ioc 0 t, a k s ∂leb)) * hm
    rw [e1, e2]
    ring
  -- the telescoped identity
  have hid : ∀ n, 0 < n → f (Y T) - f y =
      ∑ i, ∑ j ∈ Finset.range n, pd f i (Y (unifPart T n j))
          * gridIncr T n j (fun t ↦ ∫ s in Set.Ioc 0 t, a i s ∂leb)
      + ∑ i, ∑ j ∈ Finset.range n, pd f i (Y (unifPart T n j))
          * (gridIncr T n j (MB i) + gridIncr T n j (MZ i))
      + (1 / 2) * ∑ i, ∑ k, (∑ j ∈ Finset.range n, pd2 f i k (Y (unifPart T n j))
            * (gridIncr T n j (MB i) + gridIncr T n j (MZ i))
            * (gridIncr T n j (MB k) + gridIncr T n j (MZ k))
          + ∑ j ∈ Finset.range n, pd2 f i k (Y (unifPart T n j)) * gridIncr T n j (fun t ↦ Y t k)
            * gridIncr T n j (fun t ↦ ∫ s in Set.Ioc 0 t, a i s ∂leb)
          + ∑ j ∈ Finset.range n, pd2 f i k (Y (unifPart T n j))
            * gridIncr T n j (fun t ↦ MB i t + MZ i t)
            * gridIncr T n j (fun t ↦ ∫ s in Set.Ioc 0 t, a k s ∂leb))
      + ∑ j ∈ Finset.range n, (f (Y (unifPart T n (j + 1))) - f (Y (unifPart T n j))
          - fderiv ℝ f (Y (unifPart T n j)) (Y (unifPart T n (j + 1)) - Y (unifPart T n j))
          - (1 / 2) * fderiv ℝ (fderiv ℝ f) (Y (unifPart T n j))
              (Y (unifPart T n (j + 1)) - Y (unifPart T n j))
              (Y (unifPart T n (j + 1)) - Y (unifPart T n j))) := by
    intro n hn
    have htel : f (Y T) - f y
        = ∑ j ∈ Finset.range n, (f (Y (unifPart T n (j + 1))) - f (Y (unifPart T n j))) := by
      rw [Finset.sum_range_sub (fun j ↦ f (Y (unifPart T n j))), upart_self T hn, upart_zero, hY0]
    rw [htel, Finset.sum_congr rfl fun j hj => hstep n j (Finset.mem_range.mp hj)]
    exact sum_reorg n _ _ _ _ _ _
  -- pathwise drift limits
  have hDA : ∀ i, Tendsto (fun m ↦ ∑ j ∈ Finset.range (ns m), pd f i (Y (unifPart T (ns m) j))
      * gridIncr T (ns m) j (fun t ↦ ∫ s in Set.Ioc 0 t, a i s ∂leb)) atTop
      (𝓝 (∫ s in Set.Ioc 0 T, pd f i (Y s) * a i s ∂leb)) := fun i =>
    (tendsto_drift_riemann (g := fun s ↦ pd f i (Y s))
      ((hf.continuous_pd i).comp_continuousOn hYcv) (haI i)).comp hns.tendsto_atTop
  have hE1 : ∀ i k, Tendsto (fun m ↦ ∑ j ∈ Finset.range (ns m),
      pd2 f i k (Y (unifPart T (ns m) j)) * gridIncr T (ns m) j (fun t ↦ Y t k)
        * gridIncr T (ns m) j (fun t ↦ ∫ s in Set.Ioc 0 t, a i s ∂leb)) atTop (𝓝 0) :=
    fun i k => (tendsto_drift_cross (g := fun s ↦ pd2 f i k (Y s))
      (fun t => hf.abs_pd2_le i k (Y t)) (hYc k) (haI i)).comp hns.tendsto_atTop
  have hE2 : ∀ i k, Tendsto (fun m ↦ ∑ j ∈ Finset.range (ns m),
      pd2 f i k (Y (unifPart T (ns m) j)) * gridIncr T (ns m) j (fun t ↦ MB i t + MZ i t)
        * gridIncr T (ns m) j (fun t ↦ ∫ s in Set.Ioc 0 t, a k s ∂leb)) atTop (𝓝 0) :=
    fun i k => (tendsto_drift_cross (g := fun s ↦ pd2 f i k (Y s))
      (fun t => hf.abs_pd2_le i k (Y t)) ((hMB i).add (hMZ i)) (haI k)).comp hns.tendsto_atTop
  -- the squared increments converge along the subsequence
  have hSQ : Tendsto (fun m ↦ ∑ j ∈ Finset.range (ns m),
      ∑ i, gridIncr T (ns m) j (fun t ↦ Y t i) ^ 2) atTop (𝓝 (∑ i, LQ1 i)) := by
    have hi1 : ∀ i, Tendsto (fun m ↦ ∑ j ∈ Finset.range (ns m),
        gridIncr T (ns m) j (fun t ↦ Y t i) ^ 2) atTop (𝓝 (LQ1 i)) := by
      intro i
      have h1 := (tendsto_drift_cross (g := fun _ ↦ (1 : ℝ)) (C := 1) (fun _ => by simp)
        (hYc i) (haI i)).comp hns.tendsto_atTop
      have h2 := (tendsto_drift_cross (g := fun _ ↦ (1 : ℝ)) (C := 1) (fun _ => by simp)
        ((hMB i).add (hMZ i)) (haI i)).comp hns.tendsto_atTop
      have := ((hQ1 i).add h1).add h2
      rw [add_zero, add_zero] at this
      refine this.congr fun m => ?_
      simp only [Function.comp_apply, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hi := hdec (ns m) j (Finset.mem_range.mp hj) i
      simp only [gridIncr, Pi.add_apply] at hi ⊢
      linear_combination (-(Y (unifPart T (ns m) (j + 1)) i - Y (unifPart T (ns m) j) i
        + ((MB i (unifPart T (ns m) (j + 1)) - MB i (unifPart T (ns m) j))
          + (MZ i (unifPart T (ns m) (j + 1)) - MZ i (unifPart T (ns m) j))))) * hi
    refine (tendsto_finsetSum Finset.univ fun i _ => hi1 i).congr fun m => ?_
    exact Finset.sum_comm
  -- the Taylor remainders vanish along the subsequence
  have hrem : Tendsto (fun m ↦ ∑ j ∈ Finset.range (ns m),
      (f (Y (unifPart T (ns m) (j + 1))) - f (Y (unifPart T (ns m) j))
        - fderiv ℝ f (Y (unifPart T (ns m) j))
            (Y (unifPart T (ns m) (j + 1)) - Y (unifPart T (ns m) j))
        - (1 / 2) * fderiv ℝ (fderiv ℝ f) (Y (unifPart T (ns m) j))
            (Y (unifPart T (ns m) (j + 1)) - Y (unifPart T (ns m) j))
            (Y (unifPart T (ns m) (j + 1)) - Y (unifPart T (ns m) j)))) atTop (𝓝 0) := by
    set K := |∑ i, LQ1 i| + 1 with hKdef
    have hK : 0 < K := by positivity
    obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp
      (hSQ.eventually (gt_mem_nhds (lt_add_one (∑ i, LQ1 i))))
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hδR⟩ := taylor_two_uniform hf.contDiff hf.unif
      (ε := ε / (2 * K)) (by positivity)
    have hsmall : ∀ᶠ n in atTop, ∀ i, ∀ j < n, |gridIncr T n j (fun t ↦ Y t i)| < δ :=
      Filter.eventually_all.mpr fun i => eventually_small_incr (hYc i) hδ
    obtain ⟨M₁, hM₁⟩ := Filter.eventually_atTop.mp (hns.tendsto_atTop.eventually hsmall)
    refine ⟨max M₀ M₁, fun m hm => ?_⟩
    have hsm := hM₁ m (le_of_max_le_right hm)
    have hsq := hM₀ m (le_of_max_le_left hm)
    rw [Real.dist_eq, sub_zero]
    have hSQK : ∑ j ∈ Finset.range (ns m), ∑ i, gridIncr T (ns m) j (fun t ↦ Y t i) ^ 2 ≤ K := by
      have := le_abs_self (∑ i, LQ1 i)
      exact hsq.le.trans (by linarith)
    calc _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range (ns m),
            ε / (2 * K) * ∑ i, gridIncr T (ns m) j (fun t ↦ Y t i) ^ 2 := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hnorm : ‖Y (unifPart T (ns m) (j + 1)) - Y (unifPart T (ns m) j)‖ < δ :=
            (pi_norm_lt_iff hδ).mpr fun i => by
              rw [Real.norm_eq_abs]; exact hsm i j (Finset.mem_range.mp hj)
          have key := hδR (Y (unifPart T (ns m) j))
            (Y (unifPart T (ns m) (j + 1)) - Y (unifPart T (ns m) j)) hnorm
          have e : Y (unifPart T (ns m) j) + (Y (unifPart T (ns m) (j + 1)) - Y (unifPart T (ns
                m) j))
              = Y (unifPart T (ns m) (j + 1)) := by abel
          rw [e] at key
          exact key.trans (mul_le_mul_of_nonneg_left (norm_sq_le_sum_sq _) (by positivity))
      _ = ε / (2 * K) * ∑ j ∈ Finset.range (ns m),
            ∑ i, gridIncr T (ns m) j (fun t ↦ Y t i) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ε / (2 * K) * K := by gcongr
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
  -- combine
  have hL := (((tendsto_finsetSum Finset.univ fun i _ => hDA i).add
      (tendsto_finsetSum Finset.univ fun i _ => hRS i)).add
      ((tendsto_finsetSum Finset.univ fun i _ => tendsto_finsetSum Finset.univ fun k _ =>
        ((hQ i k).add (hE1 i k)).add (hE2 i k)).const_mul (1 / 2))).add hrem
  simp only [add_zero] at hL
  have hconst : Tendsto (fun m ↦ ∑ i, ∑ j ∈ Finset.range (ns m), pd f i (Y (unifPart T (ns m) j))
          * gridIncr T (ns m) j (fun t ↦ ∫ s in Set.Ioc 0 t, a i s ∂leb)
      + ∑ i, ∑ j ∈ Finset.range (ns m), pd f i (Y (unifPart T (ns m) j))
          * (gridIncr T (ns m) j (MB i) + gridIncr T (ns m) j (MZ i))
      + (1 / 2) * ∑ i, ∑ k, (∑ j ∈ Finset.range (ns m), pd2 f i k (Y (unifPart T (ns m) j))
            * (gridIncr T (ns m) j (MB i) + gridIncr T (ns m) j (MZ i))
            * (gridIncr T (ns m) j (MB k) + gridIncr T (ns m) j (MZ k))
          + ∑ j ∈ Finset.range (ns m), pd2 f i k (Y (unifPart T (ns m) j))
            * gridIncr T (ns m) j (fun t ↦ Y t k)
            * gridIncr T (ns m) j (fun t ↦ ∫ s in Set.Ioc 0 t, a i s ∂leb)
          + ∑ j ∈ Finset.range (ns m), pd2 f i k (Y (unifPart T (ns m) j))
            * gridIncr T (ns m) j (fun t ↦ MB i t + MZ i t)
            * gridIncr T (ns m) j (fun t ↦ ∫ s in Set.Ioc 0 t, a k s ∂leb))
      + ∑ j ∈ Finset.range (ns m), (f (Y (unifPart T (ns m) (j + 1))) - f (Y (unifPart T (ns m) j))
          - fderiv ℝ f (Y (unifPart T (ns m) j))
              (Y (unifPart T (ns m) (j + 1)) - Y (unifPart T (ns m) j))
          - (1 / 2) * fderiv ℝ (fderiv ℝ f) (Y (unifPart T (ns m) j))
              (Y (unifPart T (ns m) (j + 1)) - Y (unifPart T (ns m) j))
              (Y (unifPart T (ns m) (j + 1)) - Y (unifPart T (ns m) j))))
      atTop (𝓝 (f (Y T) - f y)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    exact hid (ns m) (lt_of_lt_of_le hm (hns.id_le m))
  have huniq := tendsto_nhds_unique hconst hL
  linarith

/-! ### Itô processes on the common filtration -/

section Probabilistic

variable [IsProbabilityMeasure μ] {ℱ : Filtration ℝ≥0 mΩ} {B Z W : ℝ≥0 → Ω → ℝ}

lemma itoContinuousMod_zero_ae (hW : BrownianOn ℱ W μ) (T : ℝ≥0)
    (hWc : ∀ ω, Continuous fun u : ℝ≥0 ↦ W u ω) (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    ∀ᵐ ω ∂μ, itoContinuousMod T hW.measurable φ 0 ω = 0 := by
  have h1 := itoContinuousMod_modification hW T hW.measurable hWc φ (zero_le : (0 : ℝ≥0) ≤ T)
  rw [CommonStopping.itoProcessCLM_zero_time hW T hW.measurable φ] at h1
  filter_upwards [h1, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)] with ω e1 e2
  rw [e1, e2, Pi.zero_apply]

omit [IsProbabilityMeasure μ] in
lemma goodProcess_comp {ι : Type*} [Fintype ι] {T : ℝ≥0} {Y : ι → ℝ≥0 → Ω → ℝ}
    (hY : ∀ i, ContProcess ℱ μ T (Y i)) {g : (ι → ℝ) → ℝ} (hg : Continuous g) {C : ℝ}
    (hgb : ∀ y, |g y| ≤ C) : GoodProcess ℱ μ T (fun t ω ↦ g (fun i ↦ Y i t ω)) C where
  adapted t := by
    have hm : ∀ i, Measurable[ℱ t] (Y i t) := fun i => (hY i).adapted t
    letI : MeasurableSpace Ω := ℱ t
    exact hg.measurable.comp (measurable_pi_lambda hm)
  pred := by
    have hm : ∀ i, Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω ↦ Y i p.1 p.2) :=
      fun i => (hY i).pred
    letI : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    exact hg.measurable.comp (measurable_pi_lambda hm)
  bdd _ _ := hgb _
  cont := by
    have h := ae_all_iff.mpr fun i => (hY i).cont
    filter_upwards [h] with ω hω
    exact hg.comp_continuousOn (continuousOn_pi.mpr hω)
  nonneg := (abs_nonneg _).trans (hgb 0)

omit [IsProbabilityMeasure μ] in
lemma goodProcess_one (T : ℝ≥0) : GoodProcess ℱ μ T (fun _ _ ↦ (1 : ℝ)) 1 where
  adapted _ := measurable_const
  pred := measurable_const
  bdd _ _ := by simp
  cont := Eventually.of_forall fun _ => continuousOn_const
  nonneg := zero_le_one

omit [IsProbabilityMeasure μ] in
lemma goodProcess_pd {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
    {Y : ι → ℝ≥0 → Ω → ℝ} (hY : ∀ i, ContProcess ℱ μ T (Y i)) {f : (ι → ℝ) → ℝ} {C₁ C₂ : ℝ}
    (hf : ItoTest f C₁ C₂) (i : ι) :
    GoodProcess ℱ μ T (fun t ω ↦ pd f i (fun l ↦ Y l t ω)) C₁ :=
  goodProcess_comp hY (hf.continuous_pd i) (hf.abs_pd_le i)

omit [IsProbabilityMeasure μ] in
lemma goodProcess_pd2 {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}
    {Y : ι → ℝ≥0 → Ω → ℝ} (hY : ∀ i, ContProcess ℱ μ T (Y i)) {f : (ι → ℝ) → ℝ} {C₁ C₂ : ℝ}
    (hf : ItoTest f C₁ C₂) (i k : ι) :
    GoodProcess ℱ μ T (fun t ω ↦ pd2 f i k (fun l ↦ Y l t ω)) C₂ :=
  goodProcess_comp hY (hf.continuous_pd2 i k) (hf.abs_pd2_le i k)

/-- An `ι`-indexed continuous Itô process driven by the independent pair `(B, Z)`:
`Yⁱ_t = yⁱ + ∫₀ᵗ aⁱ ds + ∫₀ᵗ bⁱ dB + ∫₀ᵗ cⁱ dZ` for all `t ≤ T`, almost surely. -/
structure ItoProc {ι : Type*} (hP : IndependentPair ℱ B Z μ) (T : ℝ≥0)
    (Y : ι → ℝ≥0 → Ω → ℝ) (y : ι → ℝ) (a b c : ι → ℝ≥0 → Ω → ℝ)
    (φB φZ : ι → Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) : Prop where
  proc : ∀ i, ContProcess ℱ μ T (Y i)
  drift : ∀ᵐ ω ∂μ, ∀ i, ContinuousOn (fun t ↦ a i t ω) (Set.Icc 0 T)
  diffB : ∀ i, ContProcess ℱ μ T (b i)
  diffZ : ∀ i, ContProcess ℱ μ T (c i)
  kerB : ∀ i, ⇑(φB i) =ᵐ[trimMeasureT (μ := μ) T ℱ] fun p ↦ b i p.1 p.2
  kerZ : ∀ i, ⇑(φZ i) =ᵐ[trimMeasureT (μ := μ) T ℱ] fun p ↦ c i p.1 p.2
  eq : ∀ᵐ ω ∂μ, ∀ i, ∀ t ≤ T, Y i t ω = y i + ∫ s in Set.Ioc 0 t, a i s ω ∂leb
    + itoContinuousMod T hP.left.measurable (φB i) t ω
    + itoContinuousMod T hP.right.measurable (φZ i) t ω

/-- Time integrals of `w h₁ h₂` are integrable. -/
lemma integrable_timeIntegral_mul (T : ℝ≥0) {w h₁ h₂ : ℝ≥0 → Ω → ℝ} {C₀ : ℝ}
    (hw : GoodProcess ℱ μ T w C₀) {φ₁ φ₂ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)}
    (hφ₁ : ⇑φ₁ =ᵐ[trimMeasureT (μ := μ) T ℱ] fun p ↦ h₁ p.1 p.2)
    (hφ₂ : ⇑φ₂ =ᵐ[trimMeasureT (μ := μ) T ℱ] fun p ↦ h₂ p.1 p.2) :
    Integrable (fun ω ↦ ∫ s, w s ω * h₁ s ω * h₂ s ω ∂(timeMeasureT T)) μ := by
  have hH : Integrable (fun p : ℝ≥0 × Ω ↦ h₁ p.1 p.2 * h₂ p.1 p.2)
      ((timeMeasureT T).prod μ) := by
    have h1 : Integrable (fun p ↦ φ₁ p * φ₂ p) (trimMeasureT (μ := μ) T ℱ) :=
      (Lp.memLp φ₁).integrable_mul (Lp.memLp φ₂)
    have h2 : Integrable (fun p : ℝ≥0 × Ω ↦ h₁ p.1 p.2 * h₂ p.1 p.2)
        (trimMeasureT (μ := μ) T ℱ) := by
      refine h1.congr ?_
      filter_upwards [hφ₁, hφ₂] with p e1 e2
      rw [e1, e2]
    exact integrable_of_integrable_trim ℱ.predictable_le_prod h2
  have hI : Integrable (fun p : ℝ≥0 × Ω ↦ w p.1 p.2 * h₁ p.1 p.2 * h₂ p.1 p.2)
      ((timeMeasureT T).prod μ) := by
    refine (hH.bdd_mul (c := C₀) (hw.pred.mono ℱ.predictable_le_prod le_rfl).aestronglyMeasurable
      (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hw.bdd _ _)).congr
      (Eventually.of_forall fun p => ?_)
    show w p.1 p.2 * (h₁ p.1 p.2 * h₂ p.1 p.2) = _
    ring
  exact hI.integral_prod_right

omit [IsProbabilityMeasure μ] in
lemma integral_abs_le_four {f g₁ l₁ g₂ l₂ g₃ g₄ : Ω → ℝ} (h₁ : Integrable g₁ μ)
    (k₁ : Integrable l₁ μ) (h₂ : Integrable g₂ μ) (k₂ : Integrable l₂ μ)
    (h₃ : Integrable g₃ μ) (h₄ : Integrable g₄ μ)
    (hle : ∀ᵐ ω ∂μ, |f ω| ≤ |g₁ ω - l₁ ω| + |g₂ ω - l₂ ω| + |g₃ ω| + |g₄ ω|) :
    ∫ ω, |f ω| ∂μ ≤ ∫ ω, |g₁ ω - l₁ ω| ∂μ + ∫ ω, |g₂ ω - l₂ ω| ∂μ
      + ∫ ω, |g₃ ω| ∂μ + ∫ ω, |g₄ ω| ∂μ := by
  have a₁ : Integrable (fun ω ↦ |g₁ ω - l₁ ω|) μ := (h₁.sub k₁).abs
  have a₂ : Integrable (fun ω ↦ |g₂ ω - l₂ ω|) μ := (h₂.sub k₂).abs
  have a₃ : Integrable (fun ω ↦ |g₃ ω|) μ := h₃.abs
  have a₄ : Integrable (fun ω ↦ |g₄ ω|) μ := h₄.abs
  have i12 : Integrable (fun ω ↦ |g₁ ω - l₁ ω| + |g₂ ω - l₂ ω|) μ := a₁.add a₂
  have i123 : Integrable (fun ω ↦ |g₁ ω - l₁ ω| + |g₂ ω - l₂ ω| + |g₃ ω|) μ := i12.add a₃
  have i1234 : Integrable (fun ω ↦ |g₁ ω - l₁ ω| + |g₂ ω - l₂ ω| + |g₃ ω| + |g₄ ω|) μ :=
    i123.add a₄
  calc ∫ ω, |f ω| ∂μ ≤ ∫ ω, (|g₁ ω - l₁ ω| + |g₂ ω - l₂ ω| + |g₃ ω| + |g₄ ω|) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg _) i1234 hle
    _ = _ := by rw [integral_add i123 a₄, integral_add i12 a₃, integral_add a₁ a₂]

/-- Riemann–Stieltjes sums are square integrable. -/
lemma memLp_rs (hW : BrownianOn ℱ W μ) (hWc : ∀ ω, Continuous fun u : ℝ≥0 ↦ W u ω) (T : ℝ≥0)
    (n : ℕ) {w : ℝ≥0 → Ω → ℝ} {C : ℝ} (hw : GoodProcess ℱ μ T w C)
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    MemLp (fun ω ↦ ∑ j ∈ Finset.range n, w (unifPart T n j) ω
      * (itoContinuousMod T hW.measurable φ (unifPart T n (j + 1)) ω
        - itoContinuousMod T hW.measurable φ (unifPart T n j) ω)) 2 μ := by
  refine memLp_finsetSum _ fun j hj => ?_
  have hX := memLp_incrM hW hWc T (Finset.mem_range.mp hj) φ
  refine MemLp.mono (hX.const_mul C)
    (((hw.adapted _).mono (ℱ.le _) le_rfl).aestronglyMeasurable.mul hX.aestronglyMeasurable) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right ((hw.bdd _ _).trans (le_abs_self C)) (abs_nonneg _)

/-- Riemann–Stieltjes sums against `M^B + M^Z` converge in `L¹`. -/
theorem tendsto_rs_pair (hP : IndependentPair ℱ B Z μ)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) (hZc : ∀ ω, Continuous fun u : ℝ≥0 ↦ Z u ω)
    (T : ℝ≥0) {w : ℝ≥0 → Ω → ℝ} {C : ℝ} (hw : GoodProcess ℱ μ T w C)
    (φ ψ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    (∀ n, Integrable (fun ω ↦ ∑ j ∈ Finset.range n, w (unifPart T n j) ω
        * (gridIncr T n j (fun t ↦ itoContinuousMod T hP.left.measurable φ t ω)
          + gridIncr T n j (fun t ↦ itoContinuousMod T hP.right.measurable ψ t ω))
        - (itoIntegralCLMT hP.left T (mulKernel T hw.pred hw.bdd φ) ω
          + itoIntegralCLMT hP.right T (mulKernel T hw.pred hw.bdd ψ) ω)) μ) ∧
    Tendsto (fun n ↦ ∫ ω, |∑ j ∈ Finset.range n, w (unifPart T n j) ω
        * (gridIncr T n j (fun t ↦ itoContinuousMod T hP.left.measurable φ t ω)
          + gridIncr T n j (fun t ↦ itoContinuousMod T hP.right.measurable ψ t ω))
        - (itoIntegralCLMT hP.left T (mulKernel T hw.pred hw.bdd φ) ω
          + itoIntegralCLMT hP.right T (mulKernel T hw.pred hw.bdd ψ) ω)| ∂μ)
      atTop (𝓝 0) := by
  have mB : ∀ n, MemLp (fun ω ↦ ∑ j ∈ Finset.range n, w (unifPart T n j) ω
      * (itoContinuousMod T hP.left.measurable φ (unifPart T n (j + 1)) ω
        - itoContinuousMod T hP.left.measurable φ (unifPart T n j) ω)
      - itoIntegralCLMT hP.left T (mulKernel T hw.pred hw.bdd φ) ω) 2 μ := fun n =>
    (memLp_rs hP.left hBc T n hw φ).sub (Lp.memLp _)
  have mZ : ∀ n, MemLp (fun ω ↦ ∑ j ∈ Finset.range n, w (unifPart T n j) ω
      * (itoContinuousMod T hP.right.measurable ψ (unifPart T n (j + 1)) ω
        - itoContinuousMod T hP.right.measurable ψ (unifPart T n j) ω)
      - itoIntegralCLMT hP.right T (mulKernel T hw.pred hw.bdd ψ) ω) 2 μ := fun n =>
    (memLp_rs hP.right hZc T n hw ψ).sub (Lp.memLp _)
  have tB : Tendsto (fun n ↦ ∫ ω, |∑ j ∈ Finset.range n, w (unifPart T n j) ω
      * (itoContinuousMod T hP.left.measurable φ (unifPart T n (j + 1)) ω
        - itoContinuousMod T hP.left.measurable φ (unifPart T n j) ω)
      - itoIntegralCLMT hP.left T (mulKernel T hw.pred hw.bdd φ) ω| ∂μ) atTop (𝓝 0) := by
    have h2 := tendsto_riemannStieltjes hP.left T hP.left.measurable hBc hw.adapted hw.pred
      hw.bdd hw.cont φ
    refine squeeze_zero (fun n => integral_nonneg fun ω => abs_nonneg _)
      (fun n => MathFin.integral_abs_le_sqrt_integral_sq (mB n)) ?_
    simpa using h2.sqrt
  have tZ : Tendsto (fun n ↦ ∫ ω, |∑ j ∈ Finset.range n, w (unifPart T n j) ω
      * (itoContinuousMod T hP.right.measurable ψ (unifPart T n (j + 1)) ω
        - itoContinuousMod T hP.right.measurable ψ (unifPart T n j) ω)
      - itoIntegralCLMT hP.right T (mulKernel T hw.pred hw.bdd ψ) ω| ∂μ) atTop (𝓝 0) := by
    have h2 := tendsto_riemannStieltjes hP.right T hP.right.measurable hZc hw.adapted hw.pred
      hw.bdd hw.cont ψ
    refine squeeze_zero (fun n => integral_nonneg fun ω => abs_nonneg _)
      (fun n => MathFin.integral_abs_le_sqrt_integral_sq (mZ n)) ?_
    simpa using h2.sqrt
  have hsplit : ∀ n ω, ∑ j ∈ Finset.range n, w (unifPart T n j) ω
        * (gridIncr T n j (fun t ↦ itoContinuousMod T hP.left.measurable φ t ω)
          + gridIncr T n j (fun t ↦ itoContinuousMod T hP.right.measurable ψ t ω))
        - (itoIntegralCLMT hP.left T (mulKernel T hw.pred hw.bdd φ) ω
          + itoIntegralCLMT hP.right T (mulKernel T hw.pred hw.bdd ψ) ω)
      = (∑ j ∈ Finset.range n, w (unifPart T n j) ω
          * (itoContinuousMod T hP.left.measurable φ (unifPart T n (j + 1)) ω
            - itoContinuousMod T hP.left.measurable φ (unifPart T n j) ω)
          - itoIntegralCLMT hP.left T (mulKernel T hw.pred hw.bdd φ) ω)
        + (∑ j ∈ Finset.range n, w (unifPart T n j) ω
          * (itoContinuousMod T hP.right.measurable ψ (unifPart T n (j + 1)) ω
            - itoContinuousMod T hP.right.measurable ψ (unifPart T n j) ω)
          - itoIntegralCLMT hP.right T (mulKernel T hw.pred hw.bdd ψ) ω) := by
    intro n ω
    simp only [gridIncr, mul_add, Finset.sum_add_distrib]
    ring
  refine ⟨fun n => ?_, ?_⟩
  · refine (((mB n).integrable one_le_two).add ((mZ n).integrable one_le_two)).congr
      (Eventually.of_forall fun ω => ?_)
    exact (hsplit n ω).symm
  · refine squeeze_zero (fun n => integral_nonneg fun ω => abs_nonneg _) (fun n => ?_)
      (by simpa using tB.add tZ)
    have i1 := ((mB n).integrable one_le_two).abs
    have i2 := ((mZ n).integrable one_le_two).abs
    refine (integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg _) (i1.add i2)
      (Eventually.of_forall fun ω => ?_)).trans (le_of_eq (integral_add i1 i2))
    exact (le_of_eq (congrArg abs (hsplit n ω))).trans (abs_add_le _ _)

/-- Martingale covariation sums for the pair `(M^B + M^Z)` converge in `L¹`. -/
theorem tendsto_cov_pair (hP : IndependentPair ℱ B Z μ)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) (hZc : ∀ ω, Continuous fun u : ℝ≥0 ↦ Z u ω)
    (T : ℝ≥0) {w : ℝ≥0 → Ω → ℝ} {C₀ : ℝ} (hw : GoodProcess ℱ μ T w C₀)
    {b₁ c₁ b₂ c₂ : ℝ≥0 → Ω → ℝ}
    (hb₁ : ContProcess ℱ μ T b₁) (hc₁ : ContProcess ℱ μ T c₁)
    (hb₂ : ContProcess ℱ μ T b₂) (hc₂ : ContProcess ℱ μ T c₂)
    {φ₁ ψ₁ φ₂ ψ₂ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)}
    (hφ₁ : ⇑φ₁ =ᵐ[trimMeasureT (μ := μ) T ℱ] fun p ↦ b₁ p.1 p.2)
    (hψ₁ : ⇑ψ₁ =ᵐ[trimMeasureT (μ := μ) T ℱ] fun p ↦ c₁ p.1 p.2)
    (hφ₂ : ⇑φ₂ =ᵐ[trimMeasureT (μ := μ) T ℱ] fun p ↦ b₂ p.1 p.2)
    (hψ₂ : ⇑ψ₂ =ᵐ[trimMeasureT (μ := μ) T ℱ] fun p ↦ c₂ p.1 p.2) :
    (∀ n, Integrable (fun ω ↦ ∑ j ∈ Finset.range n, w (unifPart T n j) ω
        * (gridIncr T n j (fun t ↦ itoContinuousMod T hP.left.measurable φ₁ t ω)
          + gridIncr T n j (fun t ↦ itoContinuousMod T hP.right.measurable ψ₁ t ω))
        * (gridIncr T n j (fun t ↦ itoContinuousMod T hP.left.measurable φ₂ t ω)
          + gridIncr T n j (fun t ↦ itoContinuousMod T hP.right.measurable ψ₂ t ω))
        - ∫ s, w s ω * (b₁ s ω * b₂ s ω + c₁ s ω * c₂ s ω) ∂(timeMeasureT T)) μ) ∧
    Tendsto (fun n ↦ ∫ ω, |∑ j ∈ Finset.range n, w (unifPart T n j) ω
        * (gridIncr T n j (fun t ↦ itoContinuousMod T hP.left.measurable φ₁ t ω)
          + gridIncr T n j (fun t ↦ itoContinuousMod T hP.right.measurable ψ₁ t ω))
        * (gridIncr T n j (fun t ↦ itoContinuousMod T hP.left.measurable φ₂ t ω)
          + gridIncr T n j (fun t ↦ itoContinuousMod T hP.right.measurable ψ₂ t ω))
        - ∫ s, w s ω * (b₁ s ω * b₂ s ω + c₁ s ω * c₂ s ω) ∂(timeMeasureT T)| ∂μ)
      atTop (𝓝 0) := by
  have hwm : ∀ t, Measurable (w t) := fun t => (hw.adapted t).mono (ℱ.le t) le_rfl
  have iBB := fun n => integrable_frozenBilinear hP.left hBc hP.left hBc T n hwm hw.bdd φ₁ φ₂
  have iZZ := fun n => integrable_frozenBilinear hP.right hZc hP.right hZc T n hwm hw.bdd ψ₁ ψ₂
  have iBZ := fun n => integrable_frozenBilinear hP.left hBc hP.right hZc T n hwm hw.bdd φ₁ ψ₂
  have iZB := fun n => integrable_frozenBilinear hP.left hBc hP.right hZc T n hwm hw.bdd φ₂ ψ₁
  have iLBB := integrable_timeIntegral_mul T hw hφ₁ hφ₂
  have iLZZ := integrable_timeIntegral_mul T hw hψ₁ hψ₂
  have tBB := tendsto_covariation_same_L2 hP.left hBc T hw hb₁ hb₂ hφ₁ hφ₂
  have tZZ := tendsto_covariation_same_L2 hP.right hZc T hw hc₁ hc₂ hψ₁ hψ₂
  have tBZ := tendsto_covariation_cross_L2 hP hBc hZc T hw hb₁ hc₂ hφ₁ hψ₂
  have tZB := tendsto_covariation_cross_L2 hP hBc hZc T hw hb₂ hc₁ hφ₂ hψ₁
  have hLsplit : ∀ᵐ ω ∂μ, ∫ s, w s ω * (b₁ s ω * b₂ s ω + c₁ s ω * c₂ s ω) ∂(timeMeasureT T)
      = ∫ s, w s ω * b₁ s ω * b₂ s ω ∂(timeMeasureT T)
        + ∫ s, w s ω * c₁ s ω * c₂ s ω ∂(timeMeasureT T) := by
    filter_upwards [hw.cont, hb₁.cont, hb₂.cont, hc₁.cont, hc₂.cont] with ω h0 h1 h2 h3 h4
    have i1 : Integrable (fun s ↦ w s ω * b₁ s ω * b₂ s ω) (timeMeasureT T) :=
      integrableOn_of_continuousOn ((h0.mul h1).mul h2)
    have i2 : Integrable (fun s ↦ w s ω * c₁ s ω * c₂ s ω) (timeMeasureT T) :=
      integrableOn_of_continuousOn ((h0.mul h3).mul h4)
    rw [← integral_add i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    show w s ω * (b₁ s ω * b₂ s ω + c₁ s ω * c₂ s ω)
      = w s ω * b₁ s ω * b₂ s ω + w s ω * c₁ s ω * c₂ s ω
    ring
  have hQsplit : ∀ n ω, ∑ j ∈ Finset.range n, w (unifPart T n j) ω
        * (gridIncr T n j (fun t ↦ itoContinuousMod T hP.left.measurable φ₁ t ω)
          + gridIncr T n j (fun t ↦ itoContinuousMod T hP.right.measurable ψ₁ t ω))
        * (gridIncr T n j (fun t ↦ itoContinuousMod T hP.left.measurable φ₂ t ω)
          + gridIncr T n j (fun t ↦ itoContinuousMod T hP.right.measurable ψ₂ t ω))
      = ∑ j ∈ Finset.range n, w (unifPart T n j) ω
          * (itoContinuousMod T hP.left.measurable φ₁ (unifPart T n (j + 1)) ω
            - itoContinuousMod T hP.left.measurable φ₁ (unifPart T n j) ω)
          * (itoContinuousMod T hP.left.measurable φ₂ (unifPart T n (j + 1)) ω
            - itoContinuousMod T hP.left.measurable φ₂ (unifPart T n j) ω)
        + ∑ j ∈ Finset.range n, w (unifPart T n j) ω
          * (itoContinuousMod T hP.right.measurable ψ₁ (unifPart T n (j + 1)) ω
            - itoContinuousMod T hP.right.measurable ψ₁ (unifPart T n j) ω)
          * (itoContinuousMod T hP.right.measurable ψ₂ (unifPart T n (j + 1)) ω
            - itoContinuousMod T hP.right.measurable ψ₂ (unifPart T n j) ω)
        + ∑ j ∈ Finset.range n, w (unifPart T n j) ω
          * (itoContinuousMod T hP.left.measurable φ₁ (unifPart T n (j + 1)) ω
            - itoContinuousMod T hP.left.measurable φ₁ (unifPart T n j) ω)
          * (itoContinuousMod T hP.right.measurable ψ₂ (unifPart T n (j + 1)) ω
            - itoContinuousMod T hP.right.measurable ψ₂ (unifPart T n j) ω)
        + ∑ j ∈ Finset.range n, w (unifPart T n j) ω
          * (itoContinuousMod T hP.left.measurable φ₂ (unifPart T n (j + 1)) ω
            - itoContinuousMod T hP.left.measurable φ₂ (unifPart T n j) ω)
          * (itoContinuousMod T hP.right.measurable ψ₁ (unifPart T n (j + 1)) ω
            - itoContinuousMod T hP.right.measurable ψ₁ (unifPart T n j) ω) := by
    intro n ω
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [gridIncr]
    ring
  have hQi : ∀ n, Integrable (fun ω ↦ ∑ j ∈ Finset.range n, w (unifPart T n j) ω
        * (gridIncr T n j (fun t ↦ itoContinuousMod T hP.left.measurable φ₁ t ω)
          + gridIncr T n j (fun t ↦ itoContinuousMod T hP.right.measurable ψ₁ t ω))
        * (gridIncr T n j (fun t ↦ itoContinuousMod T hP.left.measurable φ₂ t ω)
          + gridIncr T n j (fun t ↦ itoContinuousMod T hP.right.measurable ψ₂ t ω))) μ := by
    intro n
    refine ((((iBB n).add (iZZ n)).add (iBZ n)).add (iZB n)).congr
      (Eventually.of_forall fun ω => ?_)
    exact (hQsplit n ω).symm
  have hLi : Integrable (fun ω ↦ ∫ s, w s ω * (b₁ s ω * b₂ s ω + c₁ s ω * c₂ s ω)
      ∂(timeMeasureT T)) μ := by
    refine (iLBB.add iLZZ).congr ?_
    filter_upwards [hLsplit] with ω hω
    exact hω.symm
  refine ⟨fun n => (hQi n).sub hLi, ?_⟩
  have hsum := ((tBB.add tZZ).add tBZ).add tZB
  simp only [add_zero] at hsum
  refine squeeze_zero (fun n => integral_nonneg fun ω => abs_nonneg _) (fun n => ?_) hsum
  refine integral_abs_le_four (iBB n) iLBB (iZZ n) iLZZ (iBZ n) (iZB n) ?_
  filter_upwards [hLsplit] with ω hω
  rw [hω, hQsplit n ω]
  exact (le_of_eq (congrArg abs (by ring))).trans ((abs_add_le _ _).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl))

end Probabilistic

section Main

variable [IsProbabilityMeasure μ] {ℱ : Filtration ℝ≥0 mΩ} {B Z : ℝ≥0 → Ω → ℝ}

/-- **Itô's formula on the common filtration** (terminal time `T`). For an `ι`-indexed continuous
Itô process `Y` driven by the independent pair `(B, Z)` and a test function `f`,
almost surely

  `f(Y_T) = f(y) + ∫₀ᵀ (∑ᵢ ∂ᵢf(Y) aⁱ + ½ ∑ᵢₖ ∂ᵢₖf(Y)(bⁱbᵏ + cⁱcᵏ)) ds
      + ∑ᵢ ∫₀ᵀ ∂ᵢf(Y) bⁱ dB + ∑ᵢ ∫₀ᵀ ∂ᵢf(Y) cⁱ dZ`. -/
theorem ito_formula {ι : Type*} [Fintype ι] [DecidableEq ι] (hP : IndependentPair ℱ B Z μ)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) (hZc : ∀ ω, Continuous fun u : ℝ≥0 ↦ Z u ω)
    {T : ℝ≥0} {Y : ι → ℝ≥0 → Ω → ℝ} {y : ι → ℝ} {a b c : ι → ℝ≥0 → Ω → ℝ}
    {φB φZ : ι → Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)} (hY : ItoProc hP T Y y a b c φB φZ)
    {f : (ι → ℝ) → ℝ} {C₁ C₂ : ℝ} (hf : ItoTest f C₁ C₂) :
    ∀ᵐ ω ∂μ, f (fun i ↦ Y i T ω) = f y
      + ∫ s in Set.Ioc 0 T, (∑ i, pd f i (fun l ↦ Y l s ω) * a i s ω
          + (1 / 2) * ∑ i, ∑ k, pd2 f i k (fun l ↦ Y l s ω)
              * (b i s ω * b k s ω + c i s ω * c k s ω)) ∂leb
      + ∑ i, itoIntegralCLMT hP.left T (mulKernel T (goodProcess_pd hY.proc hf i).pred
          (goodProcess_pd hY.proc hf i).bdd (φB i)) ω
      + ∑ i, itoIntegralCLMT hP.right T (mulKernel T (goodProcess_pd hY.proc hf i).pred
          (goodProcess_pd hY.proc hf i).bdd (φZ i)) ω := by
  obtain ⟨ns, hns, hae⟩ := exists_subseq_ae_of_integral_abs_fintype (μ := μ)
    (κ := ι ⊕ (ι × ι) ⊕ ι)
    (F := Sum.elim (fun i n ω ↦ ∑ j ∈ Finset.range n, pd f i (fun l ↦ Y l (unifPart T n j) ω)
        * (gridIncr T n j (fun t ↦ itoContinuousMod T hP.left.measurable (φB i) t ω)
          + gridIncr T n j (fun t ↦ itoContinuousMod T hP.right.measurable (φZ i) t ω))
        - (itoIntegralCLMT hP.left T (mulKernel T (goodProcess_pd hY.proc hf i).pred
          (goodProcess_pd hY.proc hf i).bdd (φB i)) ω
          + itoIntegralCLMT hP.right T (mulKernel T (goodProcess_pd hY.proc hf i).pred
          (goodProcess_pd hY.proc hf i).bdd (φZ i)) ω))
      (Sum.elim (fun ik n ω ↦ ∑ j ∈ Finset.range n, pd2 f ik.1 ik.2 (fun l ↦ Y l (unifPart T n j) ω)
        * (gridIncr T n j (fun t ↦ itoContinuousMod T hP.left.measurable (φB ik.1) t ω)
          + gridIncr T n j (fun t ↦ itoContinuousMod T hP.right.measurable (φZ ik.1) t ω))
        * (gridIncr T n j (fun t ↦ itoContinuousMod T hP.left.measurable (φB ik.2) t ω)
          + gridIncr T n j (fun t ↦ itoContinuousMod T hP.right.measurable (φZ ik.2) t ω))
        - ∫ s, pd2 f ik.1 ik.2 (fun l ↦ Y l s ω) * (b ik.1 s ω * b ik.2 s ω + c ik.1 s ω * c
              ik.2 s ω) ∂(timeMeasureT T))
      (fun i n ω ↦ ∑ j ∈ Finset.range n, 1
        * (gridIncr T n j (fun t ↦ itoContinuousMod T hP.left.measurable (φB i) t ω)
          + gridIncr T n j (fun t ↦ itoContinuousMod T hP.right.measurable (φZ i) t ω))
        * (gridIncr T n j (fun t ↦ itoContinuousMod T hP.left.measurable (φB i) t ω)
          + gridIncr T n j (fun t ↦ itoContinuousMod T hP.right.measurable (φZ i) t ω))
        - ∫ s, 1 * (b i s ω * b i s ω + c i s ω * c i s ω) ∂(timeMeasureT T))))
    (by
      rintro (i | ik | i) n
      · exact (tendsto_rs_pair hP hBc hZc T (goodProcess_pd hY.proc hf i) (φB i) (φZ i)).1 n
      · exact (tendsto_cov_pair hP hBc hZc T (goodProcess_pd2 hY.proc hf ik.1 ik.2)
          (hY.diffB ik.1) (hY.diffZ ik.1) (hY.diffB ik.2) (hY.diffZ ik.2)
        (hY.kerB ik.1) (hY.kerZ ik.1) (hY.kerB ik.2) (hY.kerZ ik.2)).1 n
      · exact (tendsto_cov_pair hP hBc hZc T (goodProcess_one T)
          (hY.diffB i) (hY.diffZ i) (hY.diffB i) (hY.diffZ i)
        (hY.kerB i) (hY.kerZ i) (hY.kerB i) (hY.kerZ i)).1 n)
    (by
      rintro (i | ik | i)
      · exact (tendsto_rs_pair hP hBc hZc T (goodProcess_pd hY.proc hf i) (φB i) (φZ i)).2
      · exact (tendsto_cov_pair hP hBc hZc T (goodProcess_pd2 hY.proc hf ik.1 ik.2)
          (hY.diffB ik.1) (hY.diffZ ik.1) (hY.diffB ik.2) (hY.diffZ ik.2)
        (hY.kerB ik.1) (hY.kerZ ik.1) (hY.kerB ik.2) (hY.kerZ ik.2)).2
      · exact (tendsto_cov_pair hP hBc hZc T (goodProcess_one T)
          (hY.diffB i) (hY.diffZ i) (hY.diffB i) (hY.diffZ i)
        (hY.kerB i) (hY.kerZ i) (hY.kerB i) (hY.kerZ i)).2)
  have hcB : ∀ᵐ ω ∂μ, ∀ i, ContinuousOn
      (fun t ↦ itoContinuousMod T hP.left.measurable (φB i) t ω) (Set.Icc 0 T) :=
    ae_all_iff.mpr fun i => itoContinuousMod_continuousOn hP.left T hP.left.measurable hBc (φB i)
  have hcZ : ∀ᵐ ω ∂μ, ∀ i, ContinuousOn
      (fun t ↦ itoContinuousMod T hP.right.measurable (φZ i) t ω) (Set.Icc 0 T) :=
    ae_all_iff.mpr fun i => itoContinuousMod_continuousOn hP.right T hP.right.measurable hZc (φZ i)
  have h0B : ∀ᵐ ω ∂μ, ∀ i, itoContinuousMod T hP.left.measurable (φB i) 0 ω = 0 :=
    ae_all_iff.mpr fun i => itoContinuousMod_zero_ae hP.left T hBc (φB i)
  have h0Z : ∀ᵐ ω ∂μ, ∀ i, itoContinuousMod T hP.right.measurable (φZ i) 0 ω = 0 :=
    ae_all_iff.mpr fun i => itoContinuousMod_zero_ae hP.right T hZc (φZ i)
  have hYc : ∀ᵐ ω ∂μ, ∀ i, ContinuousOn (fun t ↦ Y i t ω) (Set.Icc 0 T) :=
    ae_all_iff.mpr fun i => (hY.proc i).cont
  have hbc : ∀ᵐ ω ∂μ, ∀ i, ContinuousOn (fun t ↦ b i t ω) (Set.Icc 0 T) :=
    ae_all_iff.mpr fun i => (hY.diffB i).cont
  have hcc : ∀ᵐ ω ∂μ, ∀ i, ContinuousOn (fun t ↦ c i t ω) (Set.Icc 0 T) :=
    ae_all_iff.mpr fun i => (hY.diffZ i).cont
  filter_upwards [hY.eq, hY.drift, hcB, hcZ, h0B, h0Z, hYc, hbc, hcc, hae]
    with ω hωeq hωa hωB hωZ hω0B hω0Z hωY hωb hωc hωF
  have hRS : ∀ i, Tendsto (fun m ↦ ∑ j ∈ Finset.range (ns m), pd f i (fun l ↦ Y l (unifPart T
        (ns m) j) ω)
        * (gridIncr T (ns m) j (fun t ↦ itoContinuousMod T hP.left.measurable (φB i) t ω)
          + gridIncr T (ns m) j (fun t ↦ itoContinuousMod T hP.right.measurable (φZ i) t ω))) atTop
      (𝓝 (itoIntegralCLMT hP.left T (mulKernel T (goodProcess_pd hY.proc hf i).pred
          (goodProcess_pd hY.proc hf i).bdd (φB i)) ω
        + itoIntegralCLMT hP.right T (mulKernel T (goodProcess_pd hY.proc hf i).pred
          (goodProcess_pd hY.proc hf i).bdd (φZ i)) ω)) := fun i =>
    tendsto_sub_nhds_zero_iff.mp (hωF (Sum.inl i))
  have hQ : ∀ i k, Tendsto (fun m ↦ ∑ j ∈ Finset.range (ns m), pd2 f i k (fun l ↦ Y l (unifPart
        T (ns m) j) ω)
        * (gridIncr T (ns m) j (fun t ↦ itoContinuousMod T hP.left.measurable (φB i) t ω)
          + gridIncr T (ns m) j (fun t ↦ itoContinuousMod T hP.right.measurable (φZ i) t ω))
        * (gridIncr T (ns m) j (fun t ↦ itoContinuousMod T hP.left.measurable (φB k) t ω)
          + gridIncr T (ns m) j (fun t ↦ itoContinuousMod T hP.right.measurable (φZ k) t ω))) atTop
      (𝓝 (∫ s, pd2 f i k (fun l ↦ Y l s ω) * (b i s ω * b k s ω + c i s ω * c k s ω)
            ∂(timeMeasureT T))) := fun i k =>
    tendsto_sub_nhds_zero_iff.mp (hωF (Sum.inr (Sum.inl (i, k))))
  have hQ1 : ∀ i, Tendsto (fun m ↦ ∑ j ∈ Finset.range (ns m),
        (gridIncr T (ns m) j (fun t ↦ itoContinuousMod T hP.left.measurable (φB i) t ω)
          + gridIncr T (ns m) j (fun t ↦ itoContinuousMod T hP.right.measurable (φZ i) t ω))
        * (gridIncr T (ns m) j (fun t ↦ itoContinuousMod T hP.left.measurable (φB i) t ω)
          + gridIncr T (ns m) j (fun t ↦ itoContinuousMod T hP.right.measurable (φZ i) t ω))) atTop
      (𝓝 (∫ s, 1 * (b i s ω * b i s ω + c i s ω * c i s ω) ∂(timeMeasureT T))) := by
    intro i
    have h3 : Tendsto (fun m ↦ ∑ j ∈ Finset.range (ns m), 1
        * (gridIncr T (ns m) j (fun t ↦ itoContinuousMod T hP.left.measurable (φB i) t ω)
          + gridIncr T (ns m) j (fun t ↦ itoContinuousMod T hP.right.measurable (φZ i) t ω))
        * (gridIncr T (ns m) j (fun t ↦ itoContinuousMod T hP.left.measurable (φB i) t ω)
          + gridIncr T (ns m) j (fun t ↦ itoContinuousMod T hP.right.measurable (φZ i) t ω))
        - ∫ s, 1 * (b i s ω * b i s ω + c i s ω * c i s ω) ∂(timeMeasureT T)) atTop (𝓝 0) :=
              hωF (Sum.inr (Sum.inr i))
    refine (tendsto_sub_nhds_zero_iff.mp h3).congr fun m => Finset.sum_congr rfl fun j _ => ?_
    ring
  have key := ito_assembly (T := T) hf (y := y) (Y := fun t l ↦ Y l t ω)
    (MB := fun i t ↦ itoContinuousMod T hP.left.measurable (φB i) t ω)
    (MZ := fun i t ↦ itoContinuousMod T hP.right.measurable (φZ i) t ω)
    (a := fun i s ↦ a i s ω) hωeq hωa hωB hωZ hωY hω0B hω0Z hns hRS hQ hQ1
  have hYv : ContinuousOn (fun t l ↦ Y l t ω) (Set.Icc 0 T) := continuousOn_pi.mpr hωY
  have hPi : ∀ i, IntegrableOn (fun s ↦ pd f i (fun l ↦ Y l s ω) * a i s ω) (Set.Ioc 0 T) leb :=
    fun i => integrableOn_of_continuousOn (((hf.continuous_pd i).comp_continuousOn hYv).mul (hωa i))
  have hQi : ∀ i k, IntegrableOn (fun s ↦ pd2 f i k (fun l ↦ Y l s ω)
      * (b i s ω * b k s ω + c i s ω * c k s ω)) (Set.Ioc 0 T) leb := fun i k =>
    integrableOn_of_continuousOn (((hf.continuous_pd2 i k).comp_continuousOn hYv).mul
      (((hωb i).mul (hωb k)).add ((hωc i).mul (hωc k))))
  have hint : ∫ s in Set.Ioc 0 T, (∑ i, pd f i (fun l ↦ Y l s ω) * a i s ω
        + (1 / 2) * ∑ i, ∑ k, pd2 f i k (fun l ↦ Y l s ω)
            * (b i s ω * b k s ω + c i s ω * c k s ω)) ∂leb
      = ∑ i, ∫ s in Set.Ioc 0 T, pd f i (fun l ↦ Y l s ω) * a i s ω ∂leb
        + (1 / 2) * ∑ i, ∑ k, ∫ s in Set.Ioc 0 T, pd2 f i k (fun l ↦ Y l s ω)
            * (b i s ω * b k s ω + c i s ω * c k s ω) ∂leb := by
    rw [integral_add (integrable_finsetSum _ fun i _ => hPi i)
      ((integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hQi i k).const_mul _),
      integral_finsetSum _ fun i _ => hPi i, integral_const_mul,
      integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hQi i k]
    congr 2
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun k _ => hQi i k
  rw [hint]
  simp only [timeMeasureT, Finset.sum_add_distrib] at key
  linear_combination key

end Main

end CommonIto
end MathFin.FilteredIto
