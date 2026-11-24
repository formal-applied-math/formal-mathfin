/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CommonRiemann
public import MathFin.Probability.Brownian.Ito.Filtered.CommonMixedQv
public import MathFin.Probability.Analysis.FiniteMeasureCauchySchwarz

/-!
# Quadratic covariation of common-filtration stochastic integrals

For integrals `M = ∫ φ dW`, `N = ∫ ψ dW'` of kernels with bounded, adapted, predictable,
a.s. continuous representatives `h`, `k`, and a weight `w` of the same kind,

* same driver `W = W'`:  `∑ⱼ w(tⱼ)ΔMⱼΔNⱼ → ∫₀ᵀ w h k ds`   in `L¹(μ)`;
* independent drivers `(W, W') = (B, Z)`: `∑ⱼ w(tⱼ)ΔMⱼΔNⱼ → 0`   in `L¹(μ)`.

Proof: freeze the integrands, `ΔMⱼ = h(tⱼ)ΔWⱼ + Dⱼ`, where the freezing defects satisfy
`∑ⱼ E[Dⱼ²] = ∫ ∑ⱼ 𝟙_{(tⱼ,tⱼ₊₁]}(h − h(tⱼ))² → 0` (isometry and dominated convergence); the
frozen sum is a weighted Brownian (co)variation sum, and the defect terms are controlled by
the Cauchy–Schwarz inequality.

## Main definitions

* `GoodProcess`
* `oneKernel`
* `defectKernel`

## Main results

* `GoodProcess.mul`
* `tendsto_covariation_same`
* `tendsto_covariation_cross`

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

/-- A bounded, adapted, predictable process with a.s. continuous paths on `[0, T]`. -/
structure GoodProcess (ℱ : Filtration ℝ≥0 mΩ) (μ : Measure Ω) (T : ℝ≥0)
    (h : ℝ≥0 → Ω → ℝ) (C : ℝ) : Prop where
  adapted : ∀ t, Measurable[ℱ t] (h t)
  pred : Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω ↦ h p.1 p.2)
  bdd : ∀ t ω, |h t ω| ≤ C
  cont : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ h t ω) (Set.Icc 0 T)
  nonneg : 0 ≤ C

/-- A property that holds for almost every time and, at each such time, almost surely,
holds `trim_T`-almost everywhere (for predictable properties). -/
lemma ae_trim_of_ae_ae {T : ℝ≥0} {P : ℝ≥0 × Ω → Prop}
    (hP : MeasurableSet[ℱ.predictable] {p | P p})
    (h : ∀ᵐ s ∂(timeMeasure_T T), ∀ᵐ ω ∂μ, P (s, ω)) :
    ∀ᵐ p ∂(trimMeasure_T (μ := μ) T ℱ), P p := by
  have hprod : ∀ᵐ p ∂((timeMeasure_T T).prod μ), P p := by
    rw [Measure.ae_prod_iff_ae_ae (ℱ.predictable_le_prod _ hP)]
    exact h
  rw [ae_iff] at hprod ⊢
  rw [trimMeasure_T, trim_measurableSet_eq _
    (show MeasurableSet[ℱ.predictable] {a | ¬ P a} from hP.compl)]
  exact hprod

omit mΩ in
lemma bandInd_sq {a b : ℝ≥0} (hab : a ≤ b) (s : ℝ≥0) : bandInd a b s ^ 2 = bandInd a b s := by
  unfold bandInd
  by_cases ha : a < s
  · by_cases hb : b < s
    · simp [ha, hb]
    · simp [ha, hb]
  · have hb : ¬ b < s := fun hb => ha (lt_of_le_of_lt hab hb)
    simp [ha, hb]

/-! ### The constant kernel and the Brownian increments -/

/-- The constant kernel `1`. -/
noncomputable def oneKernel (T : ℝ≥0) : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ) :=
  (memLp_const (1 : ℝ)).toLp (fun _ ↦ (1 : ℝ))

lemma coeFn_oneKernel (T : ℝ≥0) :
    ⇑(oneKernel (μ := μ) (ℱ := ℱ) T) =ᵐ[trimMeasure_T (μ := μ) T ℱ] fun _ ↦ (1 : ℝ) :=
  (memLp_const (1 : ℝ)).coeFn_toLp

omit [IsProbabilityMeasure μ] in
lemma coe_stepSP' {T : ℝ≥0} (hWmeas : ∀ t, Measurable (W t)) {a b : ℝ≥0}
    (hab : a ≤ b) (hbT : b ≤ T) {φ : Ω → ℝ} (hφ : Measurable[ℱ a] φ) {M : ℝ}
    (hφM : ∀ ω, |φ ω| ≤ M) (t : ℝ≥0) (ω : Ω) :
    ⇑(stepSP hWmeas hab hbT hφ hφM : TBoundedSP T ℱ).val t ω
      = (Set.Ioc a b).indicator (fun _ ↦ φ ω) t := by
  rw [SimpleProcess.apply_eq]
  have hbot : ({(⊥ : ℝ≥0)} : Set ℝ≥0).indicator
      (fun _ ↦ (stepSP hWmeas hab hbT hφ hφM : TBoundedSP T ℱ).val.valueBot ω) t = 0 := by
    simp [stepSP]
  rw [hbot, zero_add]
  show (Finsupp.single (a, b) φ).sum
      (fun p v ↦ (Set.Ioc p.1 p.2).indicator (fun _ ↦ v ω) t) = _
  rw [Finsupp.sum_single_index (by simp)]

lemma oneKernel_eq (hWmeas : ∀ t, Measurable (W t)) (T : ℝ≥0) :
    oneKernel (μ := μ) (ℱ := ℱ) T = simpleAssembly_T (μ := μ) T ℱ
      (stepSP hWmeas (zero_le : (0 : ℝ≥0) ≤ T) le_rfl (φ := fun _ ↦ (1 : ℝ))
        measurable_const (M := 1) (fun _ ↦ by simp)) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_oneKernel (μ := μ) (ℱ := ℱ) T,
    (memLp_uncurry_trim_T (μ := μ) T ℱ (stepSP hWmeas (zero_le : (0 : ℝ≥0) ≤ T) le_rfl
      (φ := fun _ ↦ (1 : ℝ)) measurable_const (M := 1) (fun _ ↦ by simp)).val).coeFn_toLp,
    ae_fst_mem_Ioc_trimMeasure_T (μ := μ) T ℱ] with p h1 h2 h3
  rw [h1]
  show (1 : ℝ) = ⇑((memLp_uncurry_trim_T (μ := μ) T ℱ (stepSP hWmeas
    (zero_le : (0 : ℝ≥0) ≤ T) le_rfl (φ := fun _ ↦ (1 : ℝ)) measurable_const (M := 1)
      (fun _ ↦ by simp)).val).toLp _) p
  rw [h2]
  show (1 : ℝ) = ⇑(stepSP hWmeas (zero_le : (0 : ℝ≥0) ≤ T) le_rfl (φ := fun _ ↦ (1 : ℝ))
      measurable_const (M := 1) (fun _ ↦ by simp) : TBoundedSP T ℱ).val p.1 p.2
  rw [coe_stepSP', Set.indicator_of_mem h3]

/-- `∫₀ᵗ 1 dW = W_t − W_0`. -/
theorem itoProcessCLM_oneKernel (hW : BrownianOn ℱ W μ) (T t : ℝ≥0) (htT : t ≤ T) :
    (itoProcessCLM hW T t hW.measurable (oneKernel (μ := μ) (ℱ := ℱ) T) : Ω → ℝ) =ᵐ[μ]
      fun ω ↦ W t ω - W 0 ω := by
  rw [oneKernel_eq hW.measurable T, itoProcessCLM_simpleAssembly_T]
  filter_upwards [(memLp_itoSimpleProcess hW hW.measurable (stepSP hW.measurable
    (zero_le : (0 : ℝ≥0) ≤ T) le_rfl (φ := fun _ ↦ (1 : ℝ)) measurable_const (M := 1)
      (fun _ ↦ by simp) : TBoundedSP T ℱ).val t).coeFn_toLp] with ω hω
  rw [itoSimpleProcessLp, hω, itoSimpleProcess_apply]
  show (Finsupp.single ((0 : ℝ≥0), T) (fun _ : Ω ↦ (1 : ℝ))).sum
      (fun p v ↦ v ω * (W (min p.2 t) ω - W (min p.1 t) ω)) = _
  rw [Finsupp.sum_single_index (by simp), min_eq_right htT,
    min_eq_left (zero_le : (0 : ℝ≥0) ≤ t), one_mul]

/-! ### Freezing defects -/

/-- The freezing defect kernel `𝟙_{(tⱼ,tⱼ₊₁]}·(φ − h(tⱼ))`. -/
noncomputable def defectKernel (T : ℝ≥0) (n j : ℕ) (hWmeas : ∀ u, Measurable (W u))
    (h : ℝ≥0 → Ω → ℝ) (hha : ∀ t, Measurable[ℱ t] (h t)) (C : ℝ) (hhb : ∀ t ω, |h t ω| ≤ C)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ) :=
  band T (unifPart T n j) (unifPart T n (j + 1)) hWmeas φ
    - smulAdapted T (unifPart T n j) hWmeas (h (unifPart T n j)) (hha _) C (fun ω ↦ hhb _ ω)
      (band T (unifPart T n j) (unifPart T n (j + 1)) hWmeas (oneKernel (μ := μ) (ℱ := ℱ) T))

lemma coeFn_defectKernel (T : ℝ≥0) (n j : ℕ) (hWmeas : ∀ u, Measurable (W u))
    (h : ℝ≥0 → Ω → ℝ) (hha : ∀ t, Measurable[ℱ t] (h t)) (C : ℝ) (hhb : ∀ t ω, |h t ω| ≤ C)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    ⇑(defectKernel T n j hWmeas h hha C hhb φ) =ᵐ[trimMeasure_T (μ := μ) T ℱ]
      fun p ↦ bandInd (gridPt T n j) (gridPt T n (j + 1)) p.1 * (φ p - h (unifPart T n j) p.2) := by
  have hmono := upart_mono T n (Nat.le_succ j)
  have e1 := Lp.coeFn_sub (band T (unifPart T n j) (unifPart T n (j + 1)) hWmeas φ)
      (smulAdapted T (unifPart T n j) hWmeas (h (unifPart T n j)) (hha _) C (fun ω ↦ hhb _ ω)
        (band T (unifPart T n j) (unifPart T n (j + 1)) hWmeas (oneKernel (μ := μ) (ℱ := ℱ) T)))
  have e2 := coeFn_band T (unifPart T n j) (unifPart T n (j + 1)) hWmeas φ
  have e3 := coeFn_smulAdapted_afterFactor T (unifPart T n j) hWmeas (h (unifPart T n j)) (hha _) C
      (fun ω ↦ hhb _ ω) (band T (unifPart T n j) (unifPart T n (j + 1)) hWmeas (oneKernel (μ :=
            μ) (ℱ := ℱ) T))
  have e4 := coeFn_band T (unifPart T n j) (unifPart T n (j + 1)) hWmeas
    (oneKernel (μ := μ) (ℱ := ℱ) T)
  have e5 := coeFn_oneKernel (μ := μ) (ℱ := ℱ) T
  filter_upwards [e1, e2, e3, e4, e5] with p h1 h2 h3 h4 h5
  show ⇑(band T (unifPart T n j) (unifPart T n (j + 1)) hWmeas φ
    - smulAdapted T (unifPart T n j) hWmeas (h (unifPart T n j)) (hha _) C (fun ω ↦ hhb _ ω)
      (band T (unifPart T n j) (unifPart T n (j + 1)) hWmeas (oneKernel (μ := μ) (ℱ := ℱ) T))) p = _
  rw [h1, Pi.sub_apply, h2, h3, h4, h5]
  simp only [afterFactor, bandInd, ← unifPart_eq_gridPt]
  by_cases ha : unifPart T n j < p.1
  · by_cases hb : unifPart T n (j + 1) < p.1
    · simp only [ha, hb, ite_true]; ring
    · simp only [ha, hb, ite_true, ite_false]; ring
  · have hb : ¬ unifPart T n (j + 1) < p.1 := fun hb => ha (lt_of_le_of_lt hmono hb)
    simp only [ha, hb, ite_false]; ring

/-- The integral of the defect kernel is the freezing defect `ΔMⱼ − h(tⱼ)ΔWⱼ`. -/
theorem itoIntegralCLM_T_defectKernel (hW : BrownianOn ℱ W μ)
    (hWc : ∀ ω, Continuous fun u : ℝ≥0 ↦ W u ω) (T : ℝ≥0) {n j : ℕ} (hj : j < n)
    (h : ℝ≥0 → Ω → ℝ) (hha : ∀ t, Measurable[ℱ t] (h t)) (C : ℝ) (hhb : ∀ t ω, |h t ω| ≤ C)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    (itoIntegralCLM_T hW T (defectKernel T n j hW.measurable h hha C hhb φ) : Ω → ℝ)
      =ᵐ[μ] fun ω ↦ (itoContinuousMod T hW.measurable φ (unifPart T n (j + 1)) ω
          - itoContinuousMod T hW.measurable φ (unifPart T n j) ω)
        - h (unifPart T n j) ω * (W (unifPart T n (j + 1)) ω - W (unifPart T n j) ω) := by
  have hbT := upart_le T (Nat.succ_le_of_lt hj)
  have hab := upart_mono T n (Nat.le_succ j)
  have haT := hab.trans hbT
  have hband := itoIntegralCLM_T_band hW T _ _ haT hbT hW.measurable φ
  have hsm := itoProcessCLM_smulAdapted_band hW T _ _ T hab hbT le_rfl hW.measurable
    (h (unifPart T n j)) (hha _) C (fun ω ↦ hhb _ ω) (oneKernel (μ := μ) (ℱ := ℱ) T)
  rw [min_eq_left hbT, min_eq_left haT, itoProcessCLM_terminal_eq] at hsm
  filter_upwards [Lp.coeFn_sub (itoIntegralCLM_T hW T
      (band T (unifPart T n j) (unifPart T n (j + 1)) hW.measurable φ))
      (itoIntegralCLM_T hW T (smulAdapted T (unifPart T n j) hW.measurable (h (unifPart T n j))
        (hha _) C (fun ω ↦ hhb _ ω)
        (band T (unifPart T n j) (unifPart T n (j + 1)) hW.measurable (oneKernel (μ := μ) (ℱ :=
              ℱ) T)))),
    hsm, Lp.coeFn_sub (itoProcessCLM hW T (unifPart T n (j + 1)) hW.measurable φ)
      (itoProcessCLM hW T (unifPart T n j) hW.measurable φ),
    itoContinuousMod_modification hW T hW.measurable hWc φ hbT,
    itoContinuousMod_modification hW T hW.measurable hWc φ haT,
    itoProcessCLM_oneKernel hW T _ hbT, itoProcessCLM_oneKernel hW T _ haT]
    with ω h1 h2 h3 h4 h5 h6 h7
  rw [defectKernel, map_sub, h1, Pi.sub_apply, h2, hband, h3, Pi.sub_apply, ← h4, ← h5, h6, h7]
  ring

/-- `‖𝟙_{(tⱼ,tⱼ₊₁]}(φ − h(tⱼ))‖² = ∫ 𝟙_{(tⱼ,tⱼ₊₁]}(h − h(tⱼ))²`. -/
lemma norm_defectKernel_sq (T : ℝ≥0) (n j : ℕ) (hWmeas : ∀ u, Measurable (W u))
    {h : ℝ≥0 → Ω → ℝ} (hha : ∀ t, Measurable[ℱ t] (h t)) {C : ℝ} (hhb : ∀ t ω, |h t ω| ≤ C)
    {φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)}
    (hφ : ⇑φ =ᵐ[trimMeasure_T (μ := μ) T ℱ] fun p ↦ h p.1 p.2) :
    ‖defectKernel T n j hWmeas h hha C hhb φ‖ ^ 2
      = ∫ p, bandInd (gridPt T n j) (gridPt T n (j + 1)) p.1
          * (h p.1 p.2 - h (unifPart T n j) p.2) ^ 2 ∂(trimMeasure_T (μ := μ) T ℱ) := by
  rw [MathFin.lp_two_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_defectKernel T n j hWmeas h hha C hhb φ, hφ] with p h1 h2
  rw [h1, h2, mul_pow, bandInd_sq (gridPt_mono T n (Nat.le_succ j))]

/-- **The freezing defects vanish in mean square:** `∑ⱼ ‖𝟙_{(tⱼ,tⱼ₊₁]}(φ − h(tⱼ))‖² → 0`. -/
theorem tendsto_sum_norm_defectKernel_sq (T : ℝ≥0) (hWmeas : ∀ u, Measurable (W u))
    {h : ℝ≥0 → Ω → ℝ} {C : ℝ} (hh : GoodProcess ℱ μ T h C)
    {φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)}
    (hφ : ⇑φ =ᵐ[trimMeasure_T (μ := μ) T ℱ] fun p ↦ h p.1 p.2) :
    Tendsto (fun n : ℕ ↦ ∑ j ∈ Finset.range n,
      ‖defectKernel T n j hWmeas h hh.adapted C hh.bdd φ‖ ^ 2) atTop (𝓝 0) := by
  set F : ℕ → ℝ≥0 × Ω → ℝ := fun n p ↦ ∑ j ∈ Finset.range n,
    (defectKernel T n j hWmeas h hh.adapted C hh.bdd φ p) ^ 2 with hF
  have hsum : ∀ n, ∑ j ∈ Finset.range n, ‖defectKernel T n j hWmeas h hh.adapted C hh.bdd φ‖ ^ 2
      = ∫ p, F n p ∂(trimMeasure_T (μ := μ) T ℱ) := by
    intro n
    simp only [hF]
    rw [integral_finsetSum _ fun j _ => (Lp.memLp _).integrable_sq]
    exact Finset.sum_congr rfl fun j _ => MathFin.lp_two_norm_sq _
  have hcoe : ∀ᵐ p ∂(trimMeasure_T (μ := μ) T ℱ), ∀ n : ℕ,
      F n p = ∑ j ∈ Finset.range n, bandInd (gridPt T n j) (gridPt T n (j + 1)) p.1
        * (h p.1 p.2 - h (unifPart T n j) p.2) ^ 2 := by
    rw [ae_all_iff]
    intro n
    have hall : ∀ᵐ p ∂(trimMeasure_T (μ := μ) T ℱ), ∀ j ∈ Finset.range n,
        defectKernel T n j hWmeas h hh.adapted C hh.bdd φ p
          = bandInd (gridPt T n j) (gridPt T n (j + 1)) p.1 * (φ p - h (unifPart T n j) p.2) :=
      (Filter.eventually_all_finset _).mpr fun j _ => coeFn_defectKernel T n j hWmeas h _ C _ φ
    filter_upwards [hall, hφ] with p h1 h2
    simp only [hF]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [h1 j hj, h2, mul_pow, bandInd_sq (gridPt_mono T n (Nat.le_succ j))]
  have hint : Tendsto (fun n ↦ ∫ p, F n p ∂(trimMeasure_T (μ := μ) T ℱ)) atTop (𝓝 0) := by
    have key := tendsto_integral_of_dominated_convergence (μ := trimMeasure_T (μ := μ) T ℱ)
      (F := F) (f := fun _ => (0 : ℝ)) (fun _ ↦ (2 * C) ^ 2)
      (fun n => by
        simp only [hF]
        exact (Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
          (Lp.aestronglyMeasurable (defectKernel T n j hWmeas h hh.adapted C hh.bdd φ)).pow 2))
      (integrable_const ((2 * C) ^ 2))
      (fun n => by
        filter_upwards [hcoe] with p hp
        rw [hp n, Real.norm_eq_abs]
        have hb : ∀ j, 0 ≤ bandInd (gridPt T n j) (gridPt T n (j + 1)) p.1 :=
          fun j => bandInd_nonneg (gridPt_mono T n (Nat.le_succ j)) p.1
        have hterm : ∀ j ∈ Finset.range n, bandInd (gridPt T n j) (gridPt T n (j + 1)) p.1
            * (h p.1 p.2 - h (unifPart T n j) p.2) ^ 2
              ≤ (2 * C) ^ 2 * bandInd (gridPt T n j) (gridPt T n (j + 1)) p.1 := by
          intro j _
          rw [mul_comm]
          refine mul_le_mul_of_nonneg_right ?_ (hb j)
          obtain ⟨h1a, h1b⟩ := abs_le.mp (hh.bdd p.1 p.2)
          obtain ⟨h2a, h2b⟩ := abs_le.mp (hh.bdd (unifPart T n j) p.2)
          nlinarith
        have hnn : 0 ≤ ∑ j ∈ Finset.range n, bandInd (gridPt T n j) (gridPt T n (j + 1)) p.1
            * (h p.1 p.2 - h (unifPart T n j) p.2) ^ 2 :=
          Finset.sum_nonneg fun j _ => mul_nonneg (hb j) (sq_nonneg _)
        rw [abs_of_nonneg hnn]
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp only [Finset.range_zero, Finset.sum_empty]; positivity
        · calc ∑ j ∈ Finset.range n, bandInd (gridPt T n j) (gridPt T n (j + 1)) p.1
                * (h p.1 p.2 - h (unifPart T n j) p.2) ^ 2
              ≤ ∑ j ∈ Finset.range n, (2 * C) ^ 2
                  * bandInd (gridPt T n j) (gridPt T n (j + 1)) p.1 := Finset.sum_le_sum hterm
            _ = (2 * C) ^ 2 * ((if 0 < p.1 then 1 else 0) - (if T < p.1 then 1 else 0)) := by
                rw [← Finset.mul_sum, sum_bandInd T hn p.1]
            _ ≤ (2 * C) ^ 2 := by
                have : (if (0 : ℝ≥0) < p.1 then (1 : ℝ) else 0)
                    - (if T < p.1 then 1 else 0) ≤ 1 := by split_ifs <;> norm_num
                exact mul_le_of_le_one_right (sq_nonneg _) this)
      (by
        refine ae_trim_of_ae_ae ?_ ?_
        · refine measurableSet_tendsto (𝓝 0) fun n => ?_
          simp only [hF]
          exact Finset.measurable_fun_sum _ fun j _ =>
            (Lp.stronglyMeasurable (defectKernel T n j hWmeas h hh.adapted C hh.bdd
                  φ)).measurable.pow_const 2
        · have h1 := ae_ae_of_ae_trim' hcoe
          have h2 : ∀ᵐ s ∂(timeMeasure_T T), s ∈ Set.Ioc 0 T := by
            rw [timeMeasure_T]; exact ae_restrict_mem measurableSet_Ioc
          filter_upwards [h1, h2] with s hs1 hs2
          filter_upwards [hs1, hh.cont] with ω hω1 hω2
          have hu : ContinuousOn (fun r ↦ (h s ω - h r ω) ^ 2) (Set.Icc 0 T) :=
            (continuousOn_const.sub hω2).pow 2
          have := tendsto_frozenFactor T (w := fun r _ ↦ (h s ω - h r ω) ^ 2) hs2 (ω := ω) hu
          simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
          refine this.congr fun n => ?_
          rw [hω1 n, frozenFactor_eq]
          exact Finset.sum_congr rfl fun j _ => mul_comm _ _)
    simpa using key
  simp_rw [hsum]
  exact hint

/-! ### An abstract freezing estimate -/

omit mΩ in
lemma abs_bilinear_sub_le (s : Finset ℕ) (w h₁ h₂ a₁ a₂ X Y : ℕ → ℝ) (L : ℝ) {C₀ C₁ C₂ : ℝ}
    (hC₀ : 0 ≤ C₀) (hw : ∀ j ∈ s, |w j| ≤ C₀) (hh₁ : ∀ j ∈ s, |h₁ j| ≤ C₁)
    (hh₂ : ∀ j ∈ s, |h₂ j| ≤ C₂) :
    |∑ j ∈ s, w j * X j * Y j - L|
      ≤ |∑ j ∈ s, w j * h₁ j * h₂ j * (a₁ j * a₂ j) - L|
        + C₀ * C₂ * ∑ j ∈ s, |(X j - h₁ j * a₁ j) * a₂ j|
        + C₀ * C₁ * ∑ j ∈ s, |a₁ j * (Y j - h₂ j * a₂ j)|
        + C₀ * ∑ j ∈ s, |(X j - h₁ j * a₁ j) * (Y j - h₂ j * a₂ j)| := by
  have hsplit : ∑ j ∈ s, w j * X j * Y j - L
      = (∑ j ∈ s, w j * h₁ j * h₂ j * (a₁ j * a₂ j) - L)
        + (∑ j ∈ s, w j * h₂ j * ((X j - h₁ j * a₁ j) * a₂ j)
          + ∑ j ∈ s, w j * h₁ j * (a₁ j * (Y j - h₂ j * a₂ j))
          + ∑ j ∈ s, w j * ((X j - h₁ j * a₁ j) * (Y j - h₂ j * a₂ j))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have : ∑ j ∈ s, w j * X j * Y j = ∑ j ∈ s, w j * h₁ j * h₂ j * (a₁ j * a₂ j)
        + ∑ j ∈ s, (w j * h₂ j * ((X j - h₁ j * a₁ j) * a₂ j)
          + w j * h₁ j * (a₁ j * (Y j - h₂ j * a₂ j))
          + w j * ((X j - h₁ j * a₁ j) * (Y j - h₂ j * a₂ j))) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]; ring
  have e1 : |∑ j ∈ s, w j * h₂ j * ((X j - h₁ j * a₁ j) * a₂ j)|
      ≤ C₀ * C₂ * ∑ j ∈ s, |(X j - h₁ j * a₁ j) * a₂ j| := by
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hw j hj) (hh₂ j hj) (abs_nonneg _) hC₀)
      (abs_nonneg _)
  have e2 : |∑ j ∈ s, w j * h₁ j * (a₁ j * (Y j - h₂ j * a₂ j))|
      ≤ C₀ * C₁ * ∑ j ∈ s, |a₁ j * (Y j - h₂ j * a₂ j)| := by
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hw j hj) (hh₁ j hj) (abs_nonneg _) hC₀)
      (abs_nonneg _)
  have e3 : |∑ j ∈ s, w j * ((X j - h₁ j * a₁ j) * (Y j - h₂ j * a₂ j))|
      ≤ C₀ * ∑ j ∈ s, |(X j - h₁ j * a₁ j) * (Y j - h₂ j * a₂ j)| := by
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hw j hj) (abs_nonneg _)
  rw [hsplit]
  calc _ ≤ |∑ j ∈ s, w j * h₁ j * h₂ j * (a₁ j * a₂ j) - L|
        + (|∑ j ∈ s, w j * h₂ j * ((X j - h₁ j * a₁ j) * a₂ j)|
          + |∑ j ∈ s, w j * h₁ j * (a₁ j * (Y j - h₂ j * a₂ j))|
          + |∑ j ∈ s, w j * ((X j - h₁ j * a₁ j) * (Y j - h₂ j * a₂ j))|) := by
        refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by linarith

omit [IsProbabilityMeasure μ] in
lemma sum_integral_abs_mul_le (s : Finset ℕ) {X Y : ℕ → Ω → ℝ}
    (hX : ∀ j ∈ s, MemLp (X j) 2 μ) (hY : ∀ j ∈ s, MemLp (Y j) 2 μ) :
    ∑ j ∈ s, ∫ ω, |X j ω * Y j ω| ∂μ
      ≤ √(∑ j ∈ s, ∫ ω, X j ω ^ 2 ∂μ) * √(∑ j ∈ s, ∫ ω, Y j ω ^ 2 ∂μ) := by
  calc ∑ j ∈ s, ∫ ω, |X j ω * Y j ω| ∂μ
      ≤ ∑ j ∈ s, √(∫ ω, X j ω ^ 2 ∂μ) * √(∫ ω, Y j ω ^ 2 ∂μ) :=
        Finset.sum_le_sum fun j hj => MathFin.integral_abs_mul_le_sqrt_mul_sqrt (hX j hj) (hY j hj)
    _ ≤ _ := Real.sum_sqrt_mul_sqrt_le _ (fun j => integral_nonneg fun ω => sq_nonneg _)
          (fun j => integral_nonneg fun ω => sq_nonneg _)

/-- **Abstract freezing estimate.** If the freezing defects `Xⱼ − h₁ⱼ a₁ⱼ`, `Yⱼ − h₂ⱼ a₂ⱼ`
vanish in summed mean square, the driving increments have bounded summed mean square, and
the frozen sum converges in `L²`, then the bilinear sum converges in `L¹`. -/
theorem tendsto_bilinear_of_freezing {w h₁ h₂ X Y a₁ a₂ : ℕ → ℕ → Ω → ℝ} {L : Ω → ℝ}
    {C₀ C₁ C₂ K : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hw : ∀ n, ∀ j ∈ Finset.range n, ∀ ω, |w n j ω| ≤ C₀)
    (hh₁ : ∀ n, ∀ j ∈ Finset.range n, ∀ ω, |h₁ n j ω| ≤ C₁)
    (hh₂ : ∀ n, ∀ j ∈ Finset.range n, ∀ ω, |h₂ n j ω| ≤ C₂)
    (hD₁m : ∀ n, ∀ j ∈ Finset.range n, MemLp (fun ω ↦ X n j ω - h₁ n j ω * a₁ n j ω) 2 μ)
    (hD₂m : ∀ n, ∀ j ∈ Finset.range n, MemLp (fun ω ↦ Y n j ω - h₂ n j ω * a₂ n j ω) 2 μ)
    (ha₁m : ∀ n, ∀ j ∈ Finset.range n, MemLp (a₁ n j) 2 μ)
    (ha₂m : ∀ n, ∀ j ∈ Finset.range n, MemLp (a₂ n j) 2 μ)
    (hQm : ∀ n, MemLp (fun ω ↦ ∑ j ∈ Finset.range n,
      w n j ω * h₁ n j ω * h₂ n j ω * (a₁ n j ω * a₂ n j ω) - L ω) 2 μ)
    (hQ : Tendsto (fun n ↦ ∫ ω, (∑ j ∈ Finset.range n,
      w n j ω * h₁ n j ω * h₂ n j ω * (a₁ n j ω * a₂ n j ω) - L ω) ^ 2 ∂μ) atTop (𝓝 0))
    (hD₁ : Tendsto (fun n ↦ ∑ j ∈ Finset.range n,
      ∫ ω, (X n j ω - h₁ n j ω * a₁ n j ω) ^ 2 ∂μ) atTop (𝓝 0))
    (hD₂ : Tendsto (fun n ↦ ∑ j ∈ Finset.range n,
      ∫ ω, (Y n j ω - h₂ n j ω * a₂ n j ω) ^ 2 ∂μ) atTop (𝓝 0))
    (ha₁ : ∀ n, ∑ j ∈ Finset.range n, ∫ ω, a₁ n j ω ^ 2 ∂μ ≤ K)
    (ha₂ : ∀ n, ∑ j ∈ Finset.range n, ∫ ω, a₂ n j ω ^ 2 ∂μ ≤ K) :
    Tendsto (fun n ↦ ∫ ω, |∑ j ∈ Finset.range n, w n j ω * X n j ω * Y n j ω - L ω| ∂μ)
      atTop (𝓝 0) := by
  have hbound : ∀ n, ∫ ω, |∑ j ∈ Finset.range n, w n j ω * X n j ω * Y n j ω - L ω| ∂μ
      ≤ √(∫ ω, (∑ j ∈ Finset.range n,
            w n j ω * h₁ n j ω * h₂ n j ω * (a₁ n j ω * a₂ n j ω) - L ω) ^ 2 ∂μ)
        + C₀ * C₂ * (√(∑ j ∈ Finset.range n, ∫ ω, (X n j ω - h₁ n j ω * a₁ n j ω) ^ 2 ∂μ) * √K)
        + C₀ * C₁ * (√K * √(∑ j ∈ Finset.range n, ∫ ω, (Y n j ω - h₂ n j ω * a₂ n j ω) ^ 2 ∂μ))
        + C₀ * (√(∑ j ∈ Finset.range n, ∫ ω, (X n j ω - h₁ n j ω * a₁ n j ω) ^ 2 ∂μ)
            * √(∑ j ∈ Finset.range n, ∫ ω, (Y n j ω - h₂ n j ω * a₂ n j ω) ^ 2 ∂μ)) := by
    intro n
    have i1 : Integrable (fun ω ↦ |∑ j ∈ Finset.range n,
        w n j ω * h₁ n j ω * h₂ n j ω * (a₁ n j ω * a₂ n j ω) - L ω|) μ :=
      ((hQm n).integrable one_le_two).abs
    have i2 : Integrable (fun ω ↦ ∑ j ∈ Finset.range n,
        |(X n j ω - h₁ n j ω * a₁ n j ω) * a₂ n j ω|) μ :=
      integrable_finsetSum _ fun j hj => ((hD₁m n j hj).integrable_mul (ha₂m n j hj)).abs
    have i3 : Integrable (fun ω ↦ ∑ j ∈ Finset.range n,
        |a₁ n j ω * (Y n j ω - h₂ n j ω * a₂ n j ω)|) μ :=
      integrable_finsetSum _ fun j hj => ((ha₁m n j hj).integrable_mul (hD₂m n j hj)).abs
    have i4 : Integrable (fun ω ↦ ∑ j ∈ Finset.range n,
        |(X n j ω - h₁ n j ω * a₁ n j ω) * (Y n j ω - h₂ n j ω * a₂ n j ω)|) μ :=
      integrable_finsetSum _ fun j hj => ((hD₁m n j hj).integrable_mul (hD₂m n j hj)).abs
    have i2' : Integrable (fun ω ↦ C₀ * C₂ * ∑ j ∈ Finset.range n,
        |(X n j ω - h₁ n j ω * a₁ n j ω) * a₂ n j ω|) μ := i2.const_mul _
    have i3' : Integrable (fun ω ↦ C₀ * C₁ * ∑ j ∈ Finset.range n,
        |a₁ n j ω * (Y n j ω - h₂ n j ω * a₂ n j ω)|) μ := i3.const_mul _
    have i4' : Integrable (fun ω ↦ C₀ * ∑ j ∈ Finset.range n,
        |(X n j ω - h₁ n j ω * a₁ n j ω) * (Y n j ω - h₂ n j ω * a₂ n j ω)|) μ := i4.const_mul _
    have j12 : Integrable (fun ω ↦ |∑ j ∈ Finset.range n,
        w n j ω * h₁ n j ω * h₂ n j ω * (a₁ n j ω * a₂ n j ω) - L ω|
        + C₀ * C₂ * ∑ j ∈ Finset.range n, |(X n j ω - h₁ n j ω * a₁ n j ω) * a₂ n j ω|) μ :=
      i1.add i2'
    have j123 : Integrable (fun ω ↦ |∑ j ∈ Finset.range n,
        w n j ω * h₁ n j ω * h₂ n j ω * (a₁ n j ω * a₂ n j ω) - L ω|
        + C₀ * C₂ * ∑ j ∈ Finset.range n, |(X n j ω - h₁ n j ω * a₁ n j ω) * a₂ n j ω|
        + C₀ * C₁ * ∑ j ∈ Finset.range n, |a₁ n j ω * (Y n j ω - h₂ n j ω * a₂ n j ω)|) μ :=
      j12.add i3'
    have hG : Integrable (fun ω ↦ |∑ j ∈ Finset.range n,
        w n j ω * h₁ n j ω * h₂ n j ω * (a₁ n j ω * a₂ n j ω) - L ω|
        + C₀ * C₂ * ∑ j ∈ Finset.range n, |(X n j ω - h₁ n j ω * a₁ n j ω) * a₂ n j ω|
        + C₀ * C₁ * ∑ j ∈ Finset.range n, |a₁ n j ω * (Y n j ω - h₂ n j ω * a₂ n j ω)|
        + C₀ * ∑ j ∈ Finset.range n,
          |(X n j ω - h₁ n j ω * a₁ n j ω) * (Y n j ω - h₂ n j ω * a₂ n j ω)|) μ :=
      j123.add i4'
    have hmono := integral_mono_of_nonneg (μ := μ)
      (f := fun ω ↦ |∑ j ∈ Finset.range n, w n j ω * X n j ω * Y n j ω - L ω|)
      (Eventually.of_forall fun ω => abs_nonneg _) hG
      (Eventually.of_forall fun ω => abs_bilinear_sub_le (Finset.range n) (fun j ↦ w n j ω)
        (fun j ↦ h₁ n j ω) (fun j ↦ h₂ n j ω) (fun j ↦ a₁ n j ω) (fun j ↦ a₂ n j ω)
        (fun j ↦ X n j ω) (fun j ↦ Y n j ω) (L ω) hC₀ (fun j hj => hw n j hj ω)
        (fun j hj => hh₁ n j hj ω) (fun j hj => hh₂ n j hj ω))
    rw [integral_add j123 i4', integral_add j12 i3', integral_add i1 i2',
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_finsetSum (f := fun j ω ↦ |(X n j ω - h₁ n j ω * a₁ n j ω) * a₂ n j ω|) _
        fun j hj => ((hD₁m n j hj).integrable_mul (ha₂m n j hj)).abs,
      integral_finsetSum (f := fun j ω ↦ |a₁ n j ω * (Y n j ω - h₂ n j ω * a₂ n j ω)|) _
        fun j hj => ((ha₁m n j hj).integrable_mul (hD₂m n j hj)).abs,
      integral_finsetSum (f := fun j ω ↦
          |(X n j ω - h₁ n j ω * a₁ n j ω) * (Y n j ω - h₂ n j ω * a₂ n j ω)|) _
        fun j hj => ((hD₁m n j hj).integrable_mul (hD₂m n j hj)).abs]
      at hmono
    have c1 := MathFin.integral_abs_le_sqrt_integral_sq (hQm n)
    have c2 := sum_integral_abs_mul_le (μ := μ) (Finset.range n) (hD₁m n) (ha₂m n)
    have c3 := sum_integral_abs_mul_le (μ := μ) (Finset.range n) (ha₁m n) (hD₂m n)
    have c4 := sum_integral_abs_mul_le (μ := μ) (Finset.range n) (hD₁m n) (hD₂m n)
    have s1 : √(∑ j ∈ Finset.range n, ∫ ω, a₂ n j ω ^ 2 ∂μ) ≤ √K := Real.sqrt_le_sqrt (ha₂ n)
    have s2 : √(∑ j ∈ Finset.range n, ∫ ω, a₁ n j ω ^ 2 ∂μ) ≤ √K := Real.sqrt_le_sqrt (ha₁ n)
    refine hmono.trans (add_le_add (add_le_add (add_le_add c1 ?_) ?_) ?_)
    · exact mul_le_mul_of_nonneg_left (c2.trans (mul_le_mul_of_nonneg_left s1
        (Real.sqrt_nonneg _))) (mul_nonneg hC₀ hC₂)
    · exact mul_le_mul_of_nonneg_left (c3.trans (mul_le_mul_of_nonneg_right s2
        (Real.sqrt_nonneg _))) (mul_nonneg hC₀ hC₁)
    · exact mul_le_mul_of_nonneg_left c4 hC₀
  have hq0 := (Real.continuous_sqrt.tendsto 0).comp hQ
  have hd₁0 := (Real.continuous_sqrt.tendsto 0).comp hD₁
  have hd₂0 := (Real.continuous_sqrt.tendsto 0).comp hD₂
  simp only [Function.comp_def, Real.sqrt_zero] at hq0 hd₁0 hd₂0
  have hlim := ((hq0.add ((hd₁0.mul_const √K).const_mul (C₀ * C₂))).add
    ((hd₂0.const_mul √K).const_mul (C₀ * C₁))).add ((hd₁0.mul hd₂0).const_mul C₀)
  simp only [zero_mul, mul_zero, add_zero] at hlim
  exact squeeze_zero (fun n => integral_nonneg fun ω => abs_nonneg _) hbound hlim

/-! ### Increments, defects and time integrals -/

/-- Brownian increments over a band are integrals of the constant kernel. -/
lemma incrW_ae_eq (hW : BrownianOn ℱ W μ) (T : ℝ≥0) {n j : ℕ} (hj : j < n) :
    (fun ω ↦ W (unifPart T n (j + 1)) ω - W (unifPart T n j) ω) =ᵐ[μ]
      ⇑(itoIntegralCLM_T hW T (band T (unifPart T n j) (unifPart T n (j + 1)) hW.measurable
        (oneKernel (μ := μ) (ℱ := ℱ) T))) := by
  have hbT := upart_le T (Nat.succ_le_of_lt hj)
  have haT := (upart_mono T n (Nat.le_succ j)).trans hbT
  rw [itoIntegralCLM_T_band hW T _ _ haT hbT hW.measurable]
  filter_upwards [Lp.coeFn_sub (itoProcessCLM hW T (unifPart T n (j + 1)) hW.measurable
      (oneKernel (μ := μ) (ℱ := ℱ) T))
      (itoProcessCLM hW T (unifPart T n j) hW.measurable (oneKernel (μ := μ) (ℱ := ℱ) T)),
    itoProcessCLM_oneKernel hW T _ hbT, itoProcessCLM_oneKernel hW T _ haT] with ω h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]
  ring

lemma memLp_incrW (hW : BrownianOn ℱ W μ) (T : ℝ≥0) {n j : ℕ} (hj : j < n) :
    MemLp (fun ω ↦ W (unifPart T n (j + 1)) ω - W (unifPart T n j) ω) 2 μ :=
  (Lp.memLp _).ae_eq (incrW_ae_eq hW T hj).symm

omit [IsProbabilityMeasure μ] in
lemma sum_integral_incrW_sq_le (hW : BrownianOn ℱ W μ) (T : ℝ≥0) (n : ℕ) :
    ∑ j ∈ Finset.range n, ∫ ω, (W (unifPart T n (j + 1)) ω - W (unifPart T n j) ω) ^ 2 ∂μ
      ≤ T := by
  rw [Finset.sum_congr rfl fun j _ => hW.integral_increment_sq (upart_mono T n (Nat.le_succ j)),
    Finset.sum_range_sub (fun j ↦ ((unifPart T n j : ℝ≥0) : ℝ)) n, upart_zero, NNReal.coe_zero,
    sub_zero]
  exact_mod_cast upart_le T le_rfl

/-- The increment of the continuous integral over a band. -/
lemma incrM_ae_eq (hW : BrownianOn ℱ W μ) (hWc : ∀ ω, Continuous fun u : ℝ≥0 ↦ W u ω)
    (T : ℝ≥0) {n j : ℕ} (hj : j < n) (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    (fun ω ↦ itoContinuousMod T hW.measurable φ (unifPart T n (j + 1)) ω
        - itoContinuousMod T hW.measurable φ (unifPart T n j) ω) =ᵐ[μ]
      ⇑(itoIntegralCLM_T hW T (band T (unifPart T n j) (unifPart T n (j + 1)) hW.measurable φ))
            := by
  have hbT := upart_le T (Nat.succ_le_of_lt hj)
  have haT := (upart_mono T n (Nat.le_succ j)).trans hbT
  rw [itoIntegralCLM_T_band hW T _ _ haT hbT hW.measurable]
  filter_upwards [Lp.coeFn_sub (itoProcessCLM hW T (unifPart T n (j + 1)) hW.measurable φ)
      (itoProcessCLM hW T (unifPart T n j) hW.measurable φ),
    itoContinuousMod_modification hW T hW.measurable hWc φ hbT,
    itoContinuousMod_modification hW T hW.measurable hWc φ haT] with ω h1 h2 h3
  rw [h1, Pi.sub_apply, ← h2, ← h3]

lemma memLp_defect (hW : BrownianOn ℱ W μ) (hWc : ∀ ω, Continuous fun u : ℝ≥0 ↦ W u ω)
    (T : ℝ≥0) {n j : ℕ} (hj : j < n) {h : ℝ≥0 → Ω → ℝ} {C : ℝ} (hh : GoodProcess ℱ μ T h C)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    MemLp (fun ω ↦ (itoContinuousMod T hW.measurable φ (unifPart T n (j + 1)) ω
        - itoContinuousMod T hW.measurable φ (unifPart T n j) ω)
      - h (unifPart T n j) ω * (W (unifPart T n (j + 1)) ω - W (unifPart T n j) ω)) 2 μ :=
  (Lp.memLp _).ae_eq (itoIntegralCLM_T_defectKernel hW hWc T hj h hh.adapted C hh.bdd φ)

lemma integral_defect_sq (hW : BrownianOn ℱ W μ) (hWc : ∀ ω, Continuous fun u : ℝ≥0 ↦ W u ω)
    (T : ℝ≥0) {n j : ℕ} (hj : j < n) {h : ℝ≥0 → Ω → ℝ} {C : ℝ} (hh : GoodProcess ℱ μ T h C)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    ∫ ω, ((itoContinuousMod T hW.measurable φ (unifPart T n (j + 1)) ω
        - itoContinuousMod T hW.measurable φ (unifPart T n j) ω)
      - h (unifPart T n j) ω * (W (unifPart T n (j + 1)) ω - W (unifPart T n j) ω)) ^ 2 ∂μ
      = ‖defectKernel T n j hW.measurable h hh.adapted C hh.bdd φ‖ ^ 2 := by
  rw [← itoIntegralCLM_T_norm hW T, MathFin.lp_two_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [itoIntegralCLM_T_defectKernel hW hWc T hj h hh.adapted C hh.bdd φ] with ω hω
  rw [hω]

lemma tendsto_sum_integral_defect_sq (hW : BrownianOn ℱ W μ)
    (hWc : ∀ ω, Continuous fun u : ℝ≥0 ↦ W u ω) (T : ℝ≥0) {h : ℝ≥0 → Ω → ℝ} {C : ℝ}
    (hh : GoodProcess ℱ μ T h C) {φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)}
    (hφ : ⇑φ =ᵐ[trimMeasure_T (μ := μ) T ℱ] fun p ↦ h p.1 p.2) :
    Tendsto (fun n : ℕ ↦ ∑ j ∈ Finset.range n,
      ∫ ω, ((itoContinuousMod T hW.measurable φ (unifPart T n (j + 1)) ω
          - itoContinuousMod T hW.measurable φ (unifPart T n j) ω)
        - h (unifPart T n j) ω * (W (unifPart T n (j + 1)) ω - W (unifPart T n j) ω)) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  refine (tendsto_sum_norm_defectKernel_sq T hW.measurable hh hφ).congr fun n => ?_
  exact Finset.sum_congr rfl fun j hj =>
    (integral_defect_sq hW hWc T (Finset.mem_range.mp hj) hh φ).symm

omit [IsProbabilityMeasure μ] in
lemma stronglyMeasurable_timeIntegral (T : ℝ≥0) {g : ℝ≥0 → Ω → ℝ}
    (hg : Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω ↦ g p.1 p.2)) :
    StronglyMeasurable (fun ω ↦ ∫ s, g s ω ∂(timeMeasure_T T)) :=
  StronglyMeasurable.integral_prod_left' (μ := timeMeasure_T T)
    (f := fun p : ℝ≥0 × Ω ↦ g p.1 p.2) (hg.mono ℱ.predictable_le_prod le_rfl).stronglyMeasurable

lemma memLp_timeIntegral (T : ℝ≥0) {g : ℝ≥0 → Ω → ℝ} {C : ℝ}
    (hg : Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω ↦ g p.1 p.2)) (hgb : ∀ t ω, |g t ω| ≤ C) :
    MemLp (fun ω ↦ ∫ s, g s ω ∂(timeMeasure_T T)) 2 μ := by
  refine MemLp.of_bound (stronglyMeasurable_timeIntegral T hg).aestronglyMeasurable
    (C * (timeMeasure_T T Set.univ).toReal) (Eventually.of_forall fun ω => ?_)
  exact norm_integral_le_of_norm_le_const (Eventually.of_forall fun s => hgb s ω)

omit [IsProbabilityMeasure μ] in
/-- Products of good processes are good. -/
lemma GoodProcess.mul {T : ℝ≥0} {h₁ h₂ : ℝ≥0 → Ω → ℝ} {C₁ C₂ : ℝ}
    (hg₁ : GoodProcess ℱ μ T h₁ C₁) (hg₂ : GoodProcess ℱ μ T h₂ C₂) :
    GoodProcess ℱ μ T (fun t ω ↦ h₁ t ω * h₂ t ω) (C₁ * C₂) where
  adapted t := (hg₁.adapted t).mul (hg₂.adapted t)
  pred := hg₁.pred.mul hg₂.pred
  bdd t ω := by
    rw [abs_mul]
    exact mul_le_mul (hg₁.bdd t ω) (hg₂.bdd t ω) (abs_nonneg _) hg₁.nonneg
  cont := by
    filter_upwards [hg₁.cont, hg₂.cont] with ω h1 h2
    exact h1.mul h2
  nonneg := mul_nonneg hg₁.nonneg hg₂.nonneg

/-! ### Covariation of bounded continuous kernels -/

/-- **Quadratic covariation, same driver.** -/
theorem tendsto_covariation_same (hW : BrownianOn ℱ W μ)
    (hWc : ∀ ω, Continuous fun u : ℝ≥0 ↦ W u ω) (T : ℝ≥0)
    {w h₁ h₂ : ℝ≥0 → Ω → ℝ} {C₀ C₁ C₂ : ℝ} (hw : GoodProcess ℱ μ T w C₀)
    (hg₁ : GoodProcess ℱ μ T h₁ C₁) (hg₂ : GoodProcess ℱ μ T h₂ C₂)
    {φ₁ φ₂ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)}
    (hφ₁ : ⇑φ₁ =ᵐ[trimMeasure_T (μ := μ) T ℱ] fun p ↦ h₁ p.1 p.2)
    (hφ₂ : ⇑φ₂ =ᵐ[trimMeasure_T (μ := μ) T ℱ] fun p ↦ h₂ p.1 p.2) :
    Tendsto (fun n : ℕ ↦ ∫ ω, |∑ j ∈ Finset.range n, w (unifPart T n j) ω
        * (itoContinuousMod T hW.measurable φ₁ (unifPart T n (j + 1)) ω
            - itoContinuousMod T hW.measurable φ₁ (unifPart T n j) ω)
        * (itoContinuousMod T hW.measurable φ₂ (unifPart T n (j + 1)) ω
            - itoContinuousMod T hW.measurable φ₂ (unifPart T n j) ω)
        - ∫ s, w s ω * h₁ s ω * h₂ s ω ∂(timeMeasure_T T)| ∂μ) atTop (𝓝 0) := by
  have hg := (hw.mul hg₁).mul hg₂
  have hQraw := MathFin.FilteredIto.CommonQv.tendsto_weighted_qv_process_of_ae_continuous hW
        hW.measurable
    (w := fun t ω ↦ w t ω * h₁ t ω * h₂ t ω) (fun s => hg.adapted s) hg.nonneg hg.bdd T hg.cont
  refine tendsto_bilinear_of_freezing (μ := μ)
    (w := fun n j ω ↦ w (unifPart T n j) ω) (h₁ := fun n j ω ↦ h₁ (unifPart T n j) ω)
    (h₂ := fun n j ω ↦ h₂ (unifPart T n j) ω)
    (X := fun n j ω ↦ itoContinuousMod T hW.measurable φ₁ (unifPart T n (j + 1)) ω
      - itoContinuousMod T hW.measurable φ₁ (unifPart T n j) ω)
    (Y := fun n j ω ↦ itoContinuousMod T hW.measurable φ₂ (unifPart T n (j + 1)) ω
      - itoContinuousMod T hW.measurable φ₂ (unifPart T n j) ω)
    (a₁ := fun n j ω ↦ W (unifPart T n (j + 1)) ω - W (unifPart T n j) ω)
    (a₂ := fun n j ω ↦ W (unifPart T n (j + 1)) ω - W (unifPart T n j) ω)
    (L := fun ω ↦ ∫ s, w s ω * h₁ s ω * h₂ s ω ∂(timeMeasure_T T)) (K := T)
    hw.nonneg hg₁.nonneg hg₂.nonneg (fun n j _ ω => hw.bdd _ ω) (fun n j _ ω => hg₁.bdd _ ω)
    (fun n j _ ω => hg₂.bdd _ ω)
    (fun n j hj => memLp_defect hW hWc T (Finset.mem_range.mp hj) hg₁ φ₁)
    (fun n j hj => memLp_defect hW hWc T (Finset.mem_range.mp hj) hg₂ φ₂)
    (fun n j hj => memLp_incrW hW T (Finset.mem_range.mp hj))
    (fun n j hj => memLp_incrW hW T (Finset.mem_range.mp hj)) (fun n => ?_) ?_
    (tendsto_sum_integral_defect_sq hW hWc T hg₁ hφ₁)
    (tendsto_sum_integral_defect_sq hW hWc T hg₂ hφ₂)
    (sum_integral_incrW_sq_le hW T) (sum_integral_incrW_sq_le hW T)
  · refine ((hW.memLp_weightedSquareSum (w := fun t ω ↦ w t ω * h₁ t ω * h₂ t ω)
      (fun t => hg.adapted t) hg.nonneg hg.bdd T n).sub
        (memLp_timeIntegral T hg.pred hg.bdd)).ae_eq (Eventually.of_forall fun ω => ?_)
    show weightedSquareSum W (fun t ω ↦ w t ω * h₁ t ω * h₂ t ω) T n ω
        - ∫ s, w s ω * h₁ s ω * h₂ s ω ∂(timeMeasure_T T)
      = ∑ j ∈ Finset.range n, w (unifPart T n j) ω * h₁ (unifPart T n j) ω
          * h₂ (unifPart T n j) ω * ((W (unifPart T n (j + 1)) ω - W (unifPart T n j) ω)
            * (W (unifPart T n (j + 1)) ω - W (unifPart T n j) ω))
        - ∫ s, w s ω * h₁ s ω * h₂ s ω ∂(timeMeasure_T T)
    rw [weightedSquareSum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  · refine hQraw.congr fun n => integral_congr_ae (Eventually.of_forall fun ω => ?_)
    show (∑ k ∈ Finset.range n, (w (unifPart T n k) ω * h₁ (unifPart T n k) ω
          * h₂ (unifPart T n k) ω) * (W (unifPart T n (k + 1)) ω - W (unifPart T n k) ω) ^ 2
        - ∫ s in Set.Ioc 0 T, w s ω * h₁ s ω * h₂ s ω ∂MathFin.ItoIntegralL2.timeMeasure) ^ 2
      = (∑ j ∈ Finset.range n, w (unifPart T n j) ω * h₁ (unifPart T n j) ω
          * h₂ (unifPart T n j) ω * ((W (unifPart T n (j + 1)) ω - W (unifPart T n j) ω)
            * (W (unifPart T n (j + 1)) ω - W (unifPart T n j) ω))
        - ∫ s, w s ω * h₁ s ω * h₂ s ω ∂(timeMeasure_T T)) ^ 2
    congr 2
    exact Finset.sum_congr rfl fun j _ => by ring

/-- **Quadratic covariation, independent drivers.** For an independent pair `(B, Z)`,
`∑ⱼ w(tⱼ)·ΔMⱼ·ΔNⱼ → 0` in `L¹`, where `M = ∫ φ₁ dB`, `N = ∫ φ₂ dZ`. -/
theorem tendsto_covariation_cross {B Z : ℝ≥0 → Ω → ℝ} (hP : IndependentPair ℱ B Z μ)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) (hZc : ∀ ω, Continuous fun u : ℝ≥0 ↦ Z u ω)
    (T : ℝ≥0) {w h₁ h₂ : ℝ≥0 → Ω → ℝ} {C₀ C₁ C₂ : ℝ} (hw : GoodProcess ℱ μ T w C₀)
    (hg₁ : GoodProcess ℱ μ T h₁ C₁) (hg₂ : GoodProcess ℱ μ T h₂ C₂)
    {φ₁ φ₂ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)}
    (hφ₁ : ⇑φ₁ =ᵐ[trimMeasure_T (μ := μ) T ℱ] fun p ↦ h₁ p.1 p.2)
    (hφ₂ : ⇑φ₂ =ᵐ[trimMeasure_T (μ := μ) T ℱ] fun p ↦ h₂ p.1 p.2) :
    Tendsto (fun n : ℕ ↦ ∫ ω, |∑ j ∈ Finset.range n, w (unifPart T n j) ω
        * (itoContinuousMod T hP.left.measurable φ₁ (unifPart T n (j + 1)) ω
            - itoContinuousMod T hP.left.measurable φ₁ (unifPart T n j) ω)
        * (itoContinuousMod T hP.right.measurable φ₂ (unifPart T n (j + 1)) ω
            - itoContinuousMod T hP.right.measurable φ₂ (unifPart T n j) ω)| ∂μ) atTop (𝓝 0) := by
  have hg := (hw.mul hg₁).mul hg₂
  have hQraw := hP.weighted_crossVariation_L2 (w := fun t ω ↦ w t ω * h₁ t ω * h₂ t ω)
    (fun t => hg.adapted t) hg.nonneg hg.bdd T hg.cont
  have key := tendsto_bilinear_of_freezing (μ := μ)
    (w := fun n j ω ↦ w (unifPart T n j) ω) (h₁ := fun n j ω ↦ h₁ (unifPart T n j) ω)
    (h₂ := fun n j ω ↦ h₂ (unifPart T n j) ω)
    (X := fun n j ω ↦ itoContinuousMod T hP.left.measurable φ₁ (unifPart T n (j + 1)) ω
      - itoContinuousMod T hP.left.measurable φ₁ (unifPart T n j) ω)
    (Y := fun n j ω ↦ itoContinuousMod T hP.right.measurable φ₂ (unifPart T n (j + 1)) ω
      - itoContinuousMod T hP.right.measurable φ₂ (unifPart T n j) ω)
    (a₁ := fun n j ω ↦ B (unifPart T n (j + 1)) ω - B (unifPart T n j) ω)
    (a₂ := fun n j ω ↦ Z (unifPart T n (j + 1)) ω - Z (unifPart T n j) ω)
    (L := fun _ ↦ 0) (K := T)
    hw.nonneg hg₁.nonneg hg₂.nonneg (fun n j _ ω => hw.bdd _ ω) (fun n j _ ω => hg₁.bdd _ ω)
    (fun n j _ ω => hg₂.bdd _ ω)
    (fun n j hj => memLp_defect hP.left hBc T (Finset.mem_range.mp hj) hg₁ φ₁)
    (fun n j hj => memLp_defect hP.right hZc T (Finset.mem_range.mp hj) hg₂ φ₂)
    (fun n j hj => memLp_incrW hP.left T (Finset.mem_range.mp hj))
    (fun n j hj => memLp_incrW hP.right T (Finset.mem_range.mp hj)) (fun n => ?_) ?_
    (tendsto_sum_integral_defect_sq hP.left hBc T hg₁ hφ₁)
    (tendsto_sum_integral_defect_sq hP.right hZc T hg₂ hφ₂)
    (sum_integral_incrW_sq_le hP.left T) (sum_integral_incrW_sq_le hP.right T)
  · simpa only [sub_zero] using key
  · refine (hP.memLp_weightedCrossSum (w := fun t ω ↦ w t ω * h₁ t ω * h₂ t ω)
      (fun t => hg.adapted t) hg.nonneg hg.bdd T n).ae_eq (Eventually.of_forall fun ω => ?_)
    show weightedCrossSum B Z (fun t ω ↦ w t ω * h₁ t ω * h₂ t ω) T n ω
      = ∑ j ∈ Finset.range n, w (unifPart T n j) ω * h₁ (unifPart T n j) ω
          * h₂ (unifPart T n j) ω * ((B (unifPart T n (j + 1)) ω - B (unifPart T n j) ω)
            * (Z (unifPart T n (j + 1)) ω - Z (unifPart T n j) ω)) - 0
    rw [weightedCrossSum, sub_zero]
    exact Finset.sum_congr rfl fun j _ => by ring
  · refine hQraw.congr fun n => integral_congr_ae (Eventually.of_forall fun ω => ?_)
    show weightedCrossSum B Z (fun t ω ↦ w t ω * h₁ t ω * h₂ t ω) T n ω ^ 2
      = (∑ j ∈ Finset.range n, w (unifPart T n j) ω * h₁ (unifPart T n j) ω
          * h₂ (unifPart T n j) ω * ((B (unifPart T n (j + 1)) ω - B (unifPart T n j) ω)
            * (Z (unifPart T n (j + 1)) ω - Z (unifPart T n j) ω)) - 0) ^ 2
    rw [weightedCrossSum, sub_zero]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring

end CommonCovariation
end MathFin.FilteredIto
