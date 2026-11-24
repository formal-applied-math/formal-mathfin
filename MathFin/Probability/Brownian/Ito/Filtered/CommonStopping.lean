/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CommonLocality
public import MathFin.Probability.Brownian.Ito.Filtered.CommonContinuous

/-!
# Stopped stochastic integrals on the common filtration

For a random time `τ` with `{τ ≤ r} ∈ ℱ r` for every `r`, the stochastic interval
`{(s, ω) | s ≤ τ ω}` is predictable, and the integral of the truncated kernel is the
stopped integral:

  `∫₀ᵗ 𝟙_{s ≤ τ} φ dB = (∫ φ dB)_{t ∧ τ}`   almost surely, for every `t ≤ T`.

The proof first treats the dyadic-type step kernels `∑ₖ 𝟙_{aₖ < τ} 𝟙_{(aₖ, aₖ₊₁]} φ`
(grid `aₖ = kT/N`), whose integral telescopes pathwise to the continuous integral at
the finite-valued time `σ_N ∧ t`, and then passes to the limit `N → ∞` using the
isometry (dominated convergence of the kernels) and path continuity of the integral.

## Main definitions

* `stepKernel`
* `bandInd`
* `stepFactor`

## Main results

* `ae_forall_eq_of_continuousOn'`
* `itoContinuousMod_stopKernel`
* `itoIntegralCLM_T_stopKernel`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto
namespace CommonStopping

open MeasureTheory ProbabilityTheory Filter Topology
open MathFin.FilteredIto.CommonNoise MathFin.FilteredIto.CommonL2
      MathFin.FilteredIto.CommonPredictable MathFin.FilteredIto.CommonIntegral
  MathFin.FilteredIto.CommonProcessGeneral MathFin.FilteredIto.CommonContinuous
        MathFin.FilteredIto.CommonLocality
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ}

/-! ### The stochastic interval of a stopping time -/

/-- The stopping-time property of an `ℝ≥0`-valued random time for the filtration `ℱ`. -/
def IsStop (ℱ : Filtration ℝ≥0 mΩ) (τ : Ω → ℝ≥0) : Prop :=
  ∀ r : ℝ≥0, MeasurableSet[ℱ r] {ω | τ ω ≤ r}

lemma measurableSet_lt_of_isStop {τ : Ω → ℝ≥0} (hτ : IsStop ℱ τ) (r : ℝ≥0) :
    MeasurableSet[ℱ r] {ω | r < τ ω} := by
  have h := (hτ r).compl
  convert h using 1
  ext ω
  simp [not_le]

/-- The closed stochastic interval `{(s, ω) | s ≤ τ ω}`. -/
def stochInterval (τ : Ω → ℝ≥0) : Set (ℝ≥0 × Ω) := {p | p.1 ≤ τ p.2}

omit mΩ in
/-- Rational description of the stochastic interval: `s ≤ τ` iff for every rational cut
`r`, either `s ≤ r` or `r < τ`. -/
theorem stochInterval_eq_iInter (τ : Ω → ℝ≥0) :
    stochInterval τ = ⋂ q : ℚ, ((Set.Iic (q : ℝ).toNNReal ×ˢ (Set.univ : Set Ω)) ∪
      (Set.Ioi (q : ℝ).toNNReal ×ˢ {ω | (q : ℝ).toNNReal < τ ω})) := by
  ext ⟨s, ω⟩
  simp only [stochInterval, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union, Set.mem_prod,
    Set.mem_Iic, Set.mem_univ, and_true, Set.mem_Ioi]
  constructor
  · intro h q
    by_cases hs : s ≤ (q : ℝ).toNNReal
    · exact Or.inl hs
    · push Not at hs
      exact Or.inr ⟨hs, lt_of_lt_of_le hs h⟩
  · intro h
    by_contra hlt
    push Not at hlt
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (by exact_mod_cast hlt : ((τ ω : ℝ)) < (s : ℝ))
    have hq0 : (0 : ℝ) ≤ q := le_trans (NNReal.coe_nonneg _) hq1.le
    have hcoe : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0
    rcases h q with h1 | ⟨_, h2⟩
    · have : (s : ℝ) ≤ q := by rw [← hcoe]; exact_mod_cast h1
      linarith
    · have : (q : ℝ) < τ ω := by rw [← hcoe]; exact_mod_cast h2
      linarith

/-- **The stochastic interval of a stopping time is predictable.** -/
theorem measurableSet_stochInterval {τ : Ω → ℝ≥0} (hτ : IsStop ℱ τ) :
    MeasurableSet[ℱ.predictable] (stochInterval τ) := by
  rw [stochInterval_eq_iInter]
  refine MeasurableSet.iInter fun q => ?_
  refine MeasurableSet.union ?_ ?_
  · have hsplit : Set.Iic ((q : ℝ).toNNReal) ×ˢ (Set.univ : Set Ω) =
        (({⊥} : Set ℝ≥0) ×ˢ (Set.univ : Set Ω)) ∪
          (Set.Ioc ⊥ ((q : ℝ).toNNReal) ×ˢ (Set.univ : Set Ω)) := by
      ext ⟨s, ω⟩
      simp only [Set.mem_prod, Set.mem_Iic, Set.mem_univ, and_true, Set.mem_union,
        Set.mem_singleton_iff, Set.mem_Ioc, NNReal.bot_eq_zero]
      constructor
      · intro h
        rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with h0 | h0
        · exact Or.inl h0.symm
        · exact Or.inr ⟨h0, h⟩
      · rintro (h | ⟨_, h⟩)
        · rw [h]; exact zero_le
        · exact h
    rw [hsplit]
    exact (measurableSet_predictable_singleton_bot_prod MeasurableSet.univ).union
      (measurableSet_predictable_Ioc_prod _ _ MeasurableSet.univ)
  · exact measurableSet_predictable_Ioi_prod (measurableSet_lt_of_isStop hτ _)

/-- The indicator `𝟙_{s ≤ τ ω}` of the stochastic interval. -/
def stopFactor (τ : Ω → ℝ≥0) : ℝ≥0 × Ω → ℝ :=
  (stochInterval τ).indicator (fun _ ↦ (1 : ℝ))

omit mΩ in
lemma stopFactor_apply (τ : Ω → ℝ≥0) (p : ℝ≥0 × Ω) :
    stopFactor τ p = if p.1 ≤ τ p.2 then 1 else 0 := by
  unfold stopFactor
  by_cases hp : p.1 ≤ τ p.2
  · rw [Set.indicator_of_mem (show p ∈ stochInterval τ from hp), ite_eq_left hp]
  · rw [Set.indicator_of_notMem (show p ∉ stochInterval τ from hp), ite_eq_right hp]

lemma measurable_stopFactor {τ : Ω → ℝ≥0} (hτ : IsStop ℱ τ) :
    Measurable[ℱ.predictable] (stopFactor τ) :=
  measurable_const.indicator (measurableSet_stochInterval hτ)

omit mΩ in
lemma abs_stopFactor_le (τ : Ω → ℝ≥0) (p : ℝ≥0 × Ω) : |stopFactor τ p| ≤ 1 := by
  rw [stopFactor_apply]
  split_ifs <;> simp

/-- The kernel truncated at `τ`: `(s, ω) ↦ 𝟙_{s ≤ τ ω} φ(s, ω)`, as a contraction of
`L²(trim_T)`. -/
noncomputable def stopKernel (T : ℝ≥0) {τ : Ω → ℝ≥0} (hτ : IsStop ℱ τ) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ) →L[ℝ] Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ) :=
  mulBddCLM (trimMeasure_T (μ := μ) T ℱ) (measurable_stopFactor hτ) (abs_stopFactor_le τ)

omit [IsProbabilityMeasure μ] in
lemma coeFn_stopKernel (T : ℝ≥0) {τ : Ω → ℝ≥0} (hτ : IsStop ℱ τ)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    ⇑(stopKernel T hτ φ) =ᵐ[trimMeasure_T (μ := μ) T ℱ] fun p ↦ stopFactor τ p * φ p :=
  coeFn_mulBddCLM _ _ _ φ

/-! ### Bands `𝟙_{(a,b]}·φ` and their integrals -/

/-- Restriction of a kernel to the time band `(a, b]`. -/
noncomputable def band (T a b : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ) :=
  restrictAfterCLM T a hBmeas φ - restrictAfterCLM T b hBmeas φ

omit [IsProbabilityMeasure μ] in
lemma coeFn_band (T a b : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    ⇑(band T a b hBmeas φ) =ᵐ[trimMeasure_T (μ := μ) T ℱ]
      fun p ↦ (if a < p.1 then φ p else 0) - (if b < p.1 then φ p else 0) := by
  filter_upwards [Lp.coeFn_sub (restrictAfterCLM T a hBmeas φ) (restrictAfterCLM T b hBmeas φ),
    coeFn_restrictAfterCLM T a hBmeas φ, coeFn_restrictAfterCLM T b hBmeas φ] with p h1 h2 h3
  show ⇑(restrictAfterCLM T a hBmeas φ - restrictAfterCLM T b hBmeas φ) p = _
  rw [h1, Pi.sub_apply, h2, h3]

omit [IsProbabilityMeasure μ] in
lemma band_vanishes (T a b c : ℝ≥0) (hca : c ≤ a) (hab : a ≤ b)
    (hBmeas : ∀ u, Measurable (B u)) (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    ∀ᵐ p ∂(trimMeasure_T (μ := μ) T ℱ), p.1 ≤ c → band T a b hBmeas φ p = 0 := by
  filter_upwards [coeFn_band T a b hBmeas φ] with p hp hpc
  rw [hp, ite_eq_right (not_lt.mpr (hpc.trans hca)), ite_eq_right (not_lt.mpr ((hpc.trans
        hca).trans hab)),
    sub_zero]

omit [IsProbabilityMeasure μ] in
lemma restrictAfter_band (T a b t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    restrictAfterCLM T t hBmeas (band T a b hBmeas φ) = band T (max a t) (max b t) hBmeas φ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_restrictAfterCLM T t hBmeas (band T a b hBmeas φ),
    coeFn_band T a b hBmeas φ, coeFn_band T (max a t) (max b t) hBmeas φ] with p h1 h2 h3
  rw [h1, h3]
  by_cases ht : t < p.1
  · rw [ite_eq_left ht, h2]
    simp only [max_lt_iff, ht, and_true]
  · rw [ite_eq_right ht]
    simp only [max_lt_iff, ht, and_false, ite_false, sub_self]

omit [IsProbabilityMeasure μ] in
lemma restrictAfter_smulAdapted (T a t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (Z : Ω → ℝ) (hZm : Measurable[ℱ a] Z) (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C)
    (ψ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    restrictAfterCLM T t hBmeas (smulAdapted T a hBmeas Z hZm C hZb ψ)
      = smulAdapted T a hBmeas Z hZm C hZb (restrictAfterCLM T t hBmeas ψ) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_restrictAfterCLM T t hBmeas (smulAdapted T a hBmeas Z hZm C hZb ψ),
    coeFn_smulAdapted_afterFactor T a hBmeas Z hZm C hZb ψ,
    coeFn_smulAdapted_afterFactor T a hBmeas Z hZm C hZb (restrictAfterCLM T t hBmeas ψ),
    coeFn_restrictAfterCLM T t hBmeas ψ] with p h1 h2 h3 h4
  rw [h1, h3, h4]
  split_ifs with ht
  · rw [h2]
  · simp

/-- An equality of differences in `L²` holds pointwise almost everywhere. -/
lemma ae_sub_eq_sub {α : Type*} {m : MeasurableSpace α} {ν : Measure α}
    {f g h k : Lp ℝ 2 ν} (e : f - g = h - k) :
    ∀ᵐ x ∂ν, f x - g x = h x - k x := by
  filter_upwards [Lp.coeFn_sub f g, Lp.coeFn_sub h k] with x h1 h2
  rw [← Pi.sub_apply, ← h1, e, h2, Pi.sub_apply]

variable (hB : BrownianOn ℱ B μ)
include hB

/-- `(φ●B)_t = ∫₀ᵀ φ dB − ∫₀ᵀ 𝟙_{(t,T]} φ dB`. -/
lemma itoProcessCLM_eq_sub_restrictAfter (T t : ℝ≥0) (htT : t ≤ T)
    (hBmeas : ∀ u, Measurable (B u)) (ψ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    itoProcessCLM hB T t hBmeas ψ
      = itoIntegralCLM_T hB T ψ - itoIntegralCLM_T hB T (restrictAfterCLM T t hBmeas ψ) := by
  rw [itoIntegralCLM_T_restrictAfterCLM hB T t htT hBmeas ψ, sub_sub_cancel]

/-- `∫₀ᵀ 𝟙_{(a,b]} φ dB = (φ●B)_b − (φ●B)_a`. -/
lemma itoIntegralCLM_T_band (T a b : ℝ≥0) (haT : a ≤ T) (hbT : b ≤ T)
    (hBmeas : ∀ u, Measurable (B u)) (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    itoIntegralCLM_T hB T (band T a b hBmeas φ)
      = itoProcessCLM hB T b hBmeas φ - itoProcessCLM hB T a hBmeas φ := by
  rw [band, map_sub, itoIntegralCLM_T_restrictAfterCLM hB T a haT hBmeas φ,
    itoIntegralCLM_T_restrictAfterCLM hB T b hbT hBmeas φ]
  abel

/-- **Per-band stopped identity.** For `a ≤ b ≤ T`, `t ≤ T` and a bounded
`ℱ a`-measurable factor `Z`,
`(Z·𝟙_{(a,b]}·φ ● B)_t = Z·((φ●B)_{b∧t} − (φ●B)_{a∧t})`. -/
theorem itoProcessCLM_smulAdapted_band (T a b t : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (htT : t ≤ T) (hBmeas : ∀ u, Measurable (B u))
    (Z : Ω → ℝ) (hZm : Measurable[ℱ a] Z) (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    (itoProcessCLM hB T t hBmeas (smulAdapted T a hBmeas Z hZm C hZb (band T a b hBmeas φ))
        : Ω → ℝ)
      =ᵐ[μ] fun ω ↦ Z ω * (itoProcessCLM hB T (min b t) hBmeas φ ω
        - itoProcessCLM hB T (min a t) hBmeas φ ω) := by
  have haT : a ≤ T := hab.trans hbT
  have hmaT : max a t ≤ T := max_le haT htT
  have hmbT : max b t ≤ T := max_le hbT htT
  have e1 := itoIntegralCLM_T_smulAdapted hB T a hBmeas Z hZm C hZb (band T a b hBmeas φ)
    (band_vanishes T a b a le_rfl hab hBmeas φ)
  have e2 := itoIntegralCLM_T_smulAdapted hB T a hBmeas Z hZm C hZb
    (band T (max a t) (max b t) hBmeas φ)
    (band_vanishes T (max a t) (max b t) a (le_max_left a t) (max_le_max hab le_rfl) hBmeas φ)
  rw [itoIntegralCLM_T_band hB T a b haT hbT hBmeas φ] at e1
  rw [itoIntegralCLM_T_band hB T (max a t) (max b t) hmaT hmbT hBmeas φ] at e2
  have key : (itoProcessCLM hB T b hBmeas φ - itoProcessCLM hB T a hBmeas φ)
      - (itoProcessCLM hB T (max b t) hBmeas φ - itoProcessCLM hB T (max a t) hBmeas φ)
      = itoProcessCLM hB T (min b t) hBmeas φ - itoProcessCLM hB T (min a t) hBmeas φ := by
    rcases le_total b t with hbt | hbt
    · rw [max_eq_right hbt, max_eq_right (hab.trans hbt), min_eq_left hbt,
        min_eq_left (hab.trans hbt)]
      abel
    · rw [max_eq_left hbt, min_eq_right hbt]
      rcases le_total a t with hat | hat
      · rw [max_eq_right hat, min_eq_left hat]; abel
      · rw [max_eq_left hat, min_eq_right hat]; abel
  rw [itoProcessCLM_eq_sub_restrictAfter hB T t htT hBmeas, restrictAfter_smulAdapted,
    restrictAfter_band]
  filter_upwards [Lp.coeFn_sub
      (itoIntegralCLM_T hB T (smulAdapted T a hBmeas Z hZm C hZb (band T a b hBmeas φ)))
      (itoIntegralCLM_T hB T
        (smulAdapted T a hBmeas Z hZm C hZb (band T (max a t) (max b t) hBmeas φ))),
    e1, e2, ae_sub_eq_sub key] with ω h0 h1 h2 h3
  rw [h0, Pi.sub_apply, h1, h2, ← mul_sub, h3]

/-- `(ψ●B)_0 = 0`. -/
lemma itoProcessCLM_zero_time (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (ψ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) : itoProcessCLM hB T 0 hBmeas ψ = 0 :=
  itoProcessCLM_eq_zero_of_vanishes_before hB T 0 zero_le hBmeas ψ (by
    filter_upwards [ae_fst_mem_Ioc_trimMeasure_T (μ := μ) T ℱ] with p hp h0
    exact absurd (lt_of_lt_of_le hp.1 h0) (lt_irrefl _))

omit hB

/-! ### The grid `aₖ = k·T/N` and its telescoping identity -/

/-- Grid points `aₖ = k·(T/N)`. -/
def gridPt (T : ℝ≥0) (N k : ℕ) : ℝ≥0 := (k : ℝ≥0) * (T / N)

lemma gridPt_zero (T : ℝ≥0) (N : ℕ) : gridPt T N 0 = 0 := by simp [gridPt]

lemma gridPt_self (T : ℝ≥0) {N : ℕ} (hN : 0 < N) : gridPt T N N = T := by
  have hN' : (N : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [gridPt, mul_div_assoc', mul_div_cancel_left₀ T hN']

lemma gridPt_succ (T : ℝ≥0) (N k : ℕ) : gridPt T N (k + 1) = gridPt T N k + T / N := by
  simp only [gridPt, Nat.cast_add, Nat.cast_one, add_mul, one_mul]

lemma gridPt_mono (T : ℝ≥0) (N : ℕ) {j k : ℕ} (h : j ≤ k) : gridPt T N j ≤ gridPt T N k := by
  unfold gridPt
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h) zero_le

lemma gridPt_le (T : ℝ≥0) {N k : ℕ} (hN : 0 < N) (hk : k ≤ N) : gridPt T N k ≤ T :=
  (gridPt_mono T N hk).trans (gridPt_self T hN).le

lemma gridPt_lt_iff (T : ℝ≥0) (hT : 0 < T) {N : ℕ} (hN : 0 < N) (k : ℕ) (x : ℝ≥0) :
    gridPt T N k < x ↔ k < ⌈x / (T / N)⌉₊ := by
  have hh : 0 < T / N := div_pos hT (Nat.cast_pos.mpr hN)
  rw [Nat.lt_ceil, lt_div_iff₀ hh, gridPt]

/-- Pathwise telescoping: `∑ₖ 𝟙_{aₖ < x}(g(k+1) − g(k)) = g(m) − g(0)` with
`m = min N ⌈x/(T/N)⌉`. -/
lemma sum_gridIndicator_telescope (T : ℝ≥0) (hT : 0 < T) {N : ℕ} (hN : 0 < N) (x : ℝ≥0)
    (g : ℕ → ℝ) :
    ∑ k ∈ Finset.range N, (if gridPt T N k < x then (1 : ℝ) else 0) * (g (k + 1) - g k)
      = g (min N ⌈x / (T / N)⌉₊) - g 0 := by
  set m := min N ⌈x / (T / N)⌉₊ with hm_def
  have hm : m ≤ N := min_le_left _ _
  have hiff : ∀ k, k < N → (gridPt T N k < x ↔ k < m) := by
    intro k hk
    rw [gridPt_lt_iff T hT hN k x, hm_def, lt_min_iff]
    exact ⟨fun h => ⟨hk, h⟩, fun h => h.2⟩
  rw [← Finset.sum_range_add_sum_Ico _ hm, ← Finset.sum_range_sub g m]
  have h1 : ∑ k ∈ Finset.range m, (if gridPt T N k < x then (1 : ℝ) else 0) * (g (k + 1) - g k)
      = ∑ k ∈ Finset.range m, (g (k + 1) - g k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkm := Finset.mem_range.mp hk
    rw [ite_eq_left ((hiff k (lt_of_lt_of_le hkm hm)).mpr hkm), one_mul]
  have h2 : ∑ k ∈ Finset.Ico m N, (if gridPt T N k < x then (1 : ℝ) else 0) * (g (k + 1) - g k)
      = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' := Finset.mem_Ico.mp hk
    rw [ite_eq_right (fun h => absurd ((hiff k hk'.2).mp h) (not_lt.mpr hk'.1)), zero_mul]
  rw [h1, h2, add_zero]

/-- The finite-valued grid approximation `σ_N = a_m ≥ τ` of `τ` (capped at `T`). -/
def gridStop (T : ℝ≥0) (N : ℕ) (τ : Ω → ℝ≥0) (ω : Ω) : ℝ≥0 :=
  gridPt T N (min N ⌈τ ω / (T / N)⌉₊)

omit mΩ in
lemma gridStop_le (T : ℝ≥0) (hT : 0 < T) {N : ℕ} (hN : 0 < N) (τ : Ω → ℝ≥0) (ω : Ω) :
    gridStop T N τ ω ≤ τ ω + T / N := by
  have hh : 0 < T / N := div_pos hT (Nat.cast_pos.mpr hN)
  calc gridStop T N τ ω ≤ gridPt T N ⌈τ ω / (T / N)⌉₊ := gridPt_mono T N (min_le_right _ _)
    _ = (⌈τ ω / (T / N)⌉₊ : ℝ≥0) * (T / N) := rfl
    _ ≤ (τ ω / (T / N) + 1) * (T / N) :=
        mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one zero_le).le zero_le
    _ = τ ω + T / N := by rw [add_mul, div_mul_cancel₀ _ hh.ne', one_mul]

omit mΩ in
lemma min_le_gridStop (T : ℝ≥0) (hT : 0 < T) {N : ℕ} (hN : 0 < N) (τ : Ω → ℝ≥0) (ω : Ω) :
    min (τ ω) T ≤ gridStop T N τ ω := by
  have hh : 0 < T / N := div_pos hT (Nat.cast_pos.mpr hN)
  unfold gridStop
  rcases le_total N ⌈τ ω / (T / N)⌉₊ with h | h
  · rw [min_eq_left h, gridPt_self T hN]
    exact min_le_right _ _
  · rw [min_eq_right h]
    calc min (τ ω) T ≤ τ ω := min_le_left _ _
      _ = τ ω / (T / N) * (T / N) := (div_mul_cancel₀ _ hh.ne').symm
      _ ≤ (⌈τ ω / (T / N)⌉₊ : ℝ≥0) * (T / N) :=
          mul_le_mul_of_nonneg_right (Nat.le_ceil _) zero_le
      _ = gridPt T N ⌈τ ω / (T / N)⌉₊ := rfl

omit mΩ in
/-- `σ_N ∧ t → τ ∧ t`. -/
lemma tendsto_min_gridStop (T : ℝ≥0) (hT : 0 < T) (τ : Ω → ℝ≥0) (ω : Ω) {t : ℝ≥0}
    (htT : t ≤ T) :
    Tendsto (fun n : ℕ ↦ min (gridStop T (n + 1) τ ω) t) atTop (𝓝 (min (τ ω) t)) := by
  have hlow : ∀ n : ℕ, min (τ ω) t ≤ min (gridStop T (n + 1) τ ω) t := fun n => by
    have := min_le_gridStop T hT (Nat.succ_pos n) τ ω
    calc min (τ ω) t = min (min (τ ω) T) t := by rw [min_assoc, min_eq_right htT]
      _ ≤ min (gridStop T (n + 1) τ ω) t := min_le_min_right t this
  have hup : ∀ n : ℕ, min (gridStop T (n + 1) τ ω) t
      ≤ min (τ ω) t + T / ((n + 1 : ℕ) : ℝ≥0) := fun n => by
    calc min (gridStop T (n + 1) τ ω) t
        ≤ min (τ ω + T / ((n + 1 : ℕ) : ℝ≥0)) (t + T / ((n + 1 : ℕ) : ℝ≥0)) :=
          min_le_min (gridStop_le T hT (Nat.succ_pos n) τ ω) le_self_add
      _ = min (τ ω) t + T / ((n + 1 : ℕ) : ℝ≥0) := min_add_add_right _ _ _
  have h0 : Tendsto (fun n : ℕ ↦ T / ((n + 1 : ℕ) : ℝ≥0)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat T).comp (tendsto_add_atTop_nat 1)
  have hlim : Tendsto (fun n : ℕ ↦ min (τ ω) t + T / ((n + 1 : ℕ) : ℝ≥0)) atTop
      (𝓝 (min (τ ω) t)) := by
    simpa using (tendsto_const_nhds (x := min (τ ω) t)).add h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim hlow hup

/-! ### Step kernels -/

/-- The `ℱ aₖ`-measurable switch `𝟙_{aₖ < τ}`. -/
def gridFactor (T : ℝ≥0) (N k : ℕ) (τ : Ω → ℝ≥0) : Ω → ℝ :=
  fun ω ↦ if gridPt T N k < τ ω then 1 else 0

lemma measurable_gridFactor {τ : Ω → ℝ≥0} (hτ : IsStop ℱ τ) (T : ℝ≥0) (N k : ℕ) :
    Measurable[ℱ (gridPt T N k)] (gridFactor T N k τ) :=
  Measurable.ite (measurableSet_lt_of_isStop hτ (gridPt T N k)) measurable_const measurable_const

omit mΩ in
lemma abs_gridFactor_le (T : ℝ≥0) (N k : ℕ) (τ : Ω → ℝ≥0) (ω : Ω) :
    |gridFactor T N k τ ω| ≤ 1 := by
  unfold gridFactor
  split_ifs <;> simp

/-- The step kernel `∑ₖ 𝟙_{aₖ < τ}·𝟙_{(aₖ, aₖ₊₁]}·φ`. -/
noncomputable def stepKernel (T : ℝ≥0) (N : ℕ) (hBmeas : ∀ u, Measurable (B u))
    {τ : Ω → ℝ≥0} (hτ : IsStop ℱ τ) (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ) :=
  ∑ k ∈ Finset.range N, smulAdapted T (gridPt T N k) hBmeas (gridFactor T N k τ)
    (measurable_gridFactor hτ T N k) 1 (abs_gridFactor_le T N k τ)
    (band T (gridPt T N k) (gridPt T N (k + 1)) hBmeas φ)

/-- Indicator of the band `(a, b]`, written `[a < s] − [b < s]`. -/
def bandInd (a b s : ℝ≥0) : ℝ := (if a < s then 1 else 0) - (if b < s then 1 else 0)

/-- The step factor `∑ₖ 𝟙_{aₖ < τ ω}·𝟙_{(aₖ, aₖ₊₁]}(s)`. -/
def stepFactor (T : ℝ≥0) (N : ℕ) (τ : Ω → ℝ≥0) (p : ℝ≥0 × Ω) : ℝ :=
  ∑ k ∈ Finset.range N,
    (if gridPt T N k < τ p.2 then 1 else 0) * bandInd (gridPt T N k) (gridPt T N (k + 1)) p.1

omit [IsProbabilityMeasure μ] in
lemma coeFn_stepKernel (T : ℝ≥0) (N : ℕ) (hBmeas : ∀ u, Measurable (B u))
    {τ : Ω → ℝ≥0} (hτ : IsStop ℱ τ) (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    ⇑(stepKernel T N hBmeas hτ φ) =ᵐ[trimMeasure_T (μ := μ) T ℱ]
      fun p ↦ stepFactor T N τ p * φ p := by
  have hterm : ∀ k ∈ Finset.range N,
      ⇑(smulAdapted T (gridPt T N k) hBmeas (gridFactor T N k τ)
        (measurable_gridFactor hτ T N k) 1 (abs_gridFactor_le T N k τ)
        (band T (gridPt T N k) (gridPt T N (k + 1)) hBmeas φ))
      =ᵐ[trimMeasure_T (μ := μ) T ℱ] fun p ↦ (if gridPt T N k < τ p.2 then (1 : ℝ) else 0)
        * bandInd (gridPt T N k) (gridPt T N (k + 1)) p.1 * φ p := by
    intro k _
    have hmono := gridPt_mono T N (Nat.le_succ k)
    filter_upwards [coeFn_smulAdapted_afterFactor T (gridPt T N k) hBmeas (gridFactor T N k τ)
      (measurable_gridFactor hτ T N k) 1 (abs_gridFactor_le T N k τ)
      (band T (gridPt T N k) (gridPt T N (k + 1)) hBmeas φ),
      coeFn_band T (gridPt T N k) (gridPt T N (k + 1)) hBmeas φ] with p h1 h2
    rw [h1, h2]
    simp only [afterFactor, gridFactor, bandInd]
    by_cases ha : gridPt T N k < p.1
    · by_cases hb : gridPt T N (k + 1) < p.1
      · simp only [ha, hb, ite_true]; ring
      · simp only [ha, hb, ite_true, ite_false]; ring
    · have hb : ¬ gridPt T N (k + 1) < p.1 := fun hb => ha (lt_of_le_of_lt hmono hb)
      simp only [ha, hb, ite_false]; ring
  have hall := (Filter.eventually_all_finset (Finset.range N)).mpr hterm
  filter_upwards [Lp.coeFn_finsetSum (Finset.range N) (fun k ↦ smulAdapted T (gridPt T N k)
      hBmeas (gridFactor T N k τ) (measurable_gridFactor hτ T N k) 1 (abs_gridFactor_le T N k τ)
      (band T (gridPt T N k) (gridPt T N (k + 1)) hBmeas φ)), hall] with p h1 h2
  rw [stepKernel, h1, Finset.sum_apply, stepFactor, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k hk => h2 k hk

omit mΩ in
lemma bandInd_nonneg {a b : ℝ≥0} (hab : a ≤ b) (s : ℝ≥0) : 0 ≤ bandInd a b s := by
  unfold bandInd
  by_cases ha : a < s
  · by_cases hb : b < s
    · simp [ha, hb]
    · simp [ha, hb]
  · have hb : ¬ b < s := fun hb => ha (lt_of_le_of_lt hab hb)
    simp [ha, hb]

omit mΩ in
/-- `∑ₖ [aₖ < s] − [aₖ₊₁ < s] = [0 < s] − [T < s]`. -/
lemma sum_bandInd (T : ℝ≥0) {N : ℕ} (hN : 0 < N) (s : ℝ≥0) :
    ∑ k ∈ Finset.range N, bandInd (gridPt T N k) (gridPt T N (k + 1)) s
      = (if 0 < s then 1 else 0) - (if T < s then 1 else 0) := by
  have h := Finset.sum_range_sub (fun k ↦ -(if gridPt T N k < s then (1 : ℝ) else 0)) N
  simp only [gridPt_zero, gridPt_self T hN] at h
  rw [show (if (0 : ℝ≥0) < s then (1 : ℝ) else 0) - (if T < s then 1 else 0)
      = -(if T < s then (1 : ℝ) else 0) - -(if (0 : ℝ≥0) < s then 1 else 0) by ring, ← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold bandInd
  ring

omit mΩ in
lemma stepFactor_nonneg_le_one (T : ℝ≥0) {N : ℕ} (hN : 0 < N) (τ : Ω → ℝ≥0)
    (p : ℝ≥0 × Ω) : 0 ≤ stepFactor T N τ p ∧ stepFactor T N τ p ≤ 1 := by
  have hb : ∀ k, 0 ≤ bandInd (gridPt T N k) (gridPt T N (k + 1)) p.1 :=
    fun k => bandInd_nonneg (gridPt_mono T N (Nat.le_succ k)) p.1
  constructor
  · refine Finset.sum_nonneg fun k _ => mul_nonneg ?_ (hb k)
    split_ifs <;> norm_num
  · calc stepFactor T N τ p
        ≤ ∑ k ∈ Finset.range N, bandInd (gridPt T N k) (gridPt T N (k + 1)) p.1 := by
          refine Finset.sum_le_sum fun k _ => ?_
          calc (if gridPt T N k < τ p.2 then (1 : ℝ) else 0)
                * bandInd (gridPt T N k) (gridPt T N (k + 1)) p.1
              ≤ 1 * bandInd (gridPt T N k) (gridPt T N (k + 1)) p.1 :=
                mul_le_mul_of_nonneg_right (by split_ifs <;> norm_num) (hb k)
            _ = _ := one_mul _
      _ = (if 0 < p.1 then 1 else 0) - (if T < p.1 then 1 else 0) := sum_bandInd T hN p.1
      _ ≤ 1 := by split_ifs <;> norm_num

omit mΩ in
/-- On `[[0, τ]] ∩ (0, T]` the step factor is `1`. -/
lemma stepFactor_eq_one (T : ℝ≥0) {N : ℕ} (hN : 0 < N) (τ : Ω → ℝ≥0)
    {p : ℝ≥0 × Ω} (hp : p.1 ∈ Set.Ioc 0 T) (hpτ : p.1 ≤ τ p.2) : stepFactor T N τ p = 1 := by
  have hterm : ∀ k ∈ Finset.range N, (if gridPt T N k < τ p.2 then (1 : ℝ) else 0)
      * bandInd (gridPt T N k) (gridPt T N (k + 1)) p.1
        = bandInd (gridPt T N k) (gridPt T N (k + 1)) p.1 := by
    intro k _
    by_cases ha : gridPt T N k < p.1
    · rw [ite_eq_left (lt_of_lt_of_le ha hpτ), one_mul]
    · have hb : ¬ gridPt T N (k + 1) < p.1 :=
        fun hb => ha (lt_of_le_of_lt (gridPt_mono T N (Nat.le_succ k)) hb)
      simp [bandInd, ha, hb]
  rw [stepFactor, Finset.sum_congr rfl hterm, sum_bandInd T hN p.1, ite_eq_left hp.1,
    ite_eq_right (not_lt.mpr hp.2), sub_zero]

omit mΩ in
/-- Beyond `τ + T/N` the step factor is `0`. -/
lemma stepFactor_eq_zero (T : ℝ≥0) {N : ℕ} (τ : Ω → ℝ≥0) {p : ℝ≥0 × Ω}
    (hpτ : τ p.2 + T / N < p.1) : stepFactor T N τ p = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hz : gridPt T N k < τ p.2
  · have hb : gridPt T N (k + 1) < p.1 := by
      rw [gridPt_succ]
      exact lt_of_le_of_lt (add_le_add hz.le le_rfl) hpτ
    have ha : gridPt T N k < p.1 := lt_of_le_of_lt (gridPt_mono T N (Nat.le_succ k)) hb
    simp [bandInd, ha, hb]
  · simp [hz]

omit mΩ in
lemma stopFactor_eq_zero {τ : Ω → ℝ≥0} {p : ℝ≥0 × Ω} (h : τ p.2 < p.1) : stopFactor τ p = 0 := by
  rw [stopFactor_apply, ite_eq_right (not_le.mpr h)]

/-- **Kernel convergence.** The step kernels converge to the stopped kernel in `L²(trim_T)`. -/
theorem tendsto_stepKernel (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    {τ : Ω → ℝ≥0} (hτ : IsStop ℱ τ) (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    Tendsto (fun n : ℕ ↦ stepKernel T (n + 1) hBmeas hτ φ) atTop (𝓝 (stopKernel T hτ φ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set F : ℕ → ℝ≥0 × Ω → ℝ := fun n p ↦
    ((stepKernel T (n + 1) hBmeas hτ φ - stopKernel T hτ φ : Lp ℝ 2 _) p) ^ 2 with hF
  have hcoe : ∀ᵐ p ∂(trimMeasure_T (μ := μ) T ℱ), ∀ n : ℕ,
      F n p = ((stepFactor T (n + 1) τ p - stopFactor τ p) * φ p) ^ 2 := by
    rw [ae_all_iff]
    intro n
    filter_upwards [Lp.coeFn_sub (stepKernel T (n + 1) hBmeas hτ φ) (stopKernel T hτ φ),
      coeFn_stepKernel T (n + 1) hBmeas hτ φ, coeFn_stopKernel T hτ φ] with p h1 h2 h3
    simp only [hF]
    rw [h1, Pi.sub_apply, h2, h3]
    ring
  have hint : Tendsto (fun n ↦ ∫ p, F n p ∂(trimMeasure_T (μ := μ) T ℱ)) atTop (𝓝 0) := by
    have key := tendsto_integral_of_dominated_convergence (μ := trimMeasure_T (μ := μ) T ℱ)
      (F := F) (f := fun _ => (0 : ℝ)) (fun p ↦ 4 * (φ p) ^ 2)
      (fun n => (Lp.aestronglyMeasurable _).pow 2)
      ((Lp.memLp φ).integrable_sq.const_mul 4)
      (fun n => by
        filter_upwards [hcoe] with p hp
        rw [hp n, Real.norm_eq_abs, abs_pow, abs_mul, mul_pow]
        have h1 := stepFactor_nonneg_le_one T (Nat.succ_pos n) τ p
        have h2 := abs_stopFactor_le τ p
        have h2' := abs_le.mp h2
        have hsq : (stepFactor T (n + 1) τ p - stopFactor τ p) ^ 2 ≤ 4 := by nlinarith
        calc |stepFactor T (n + 1) τ p - stopFactor τ p| ^ 2 * |φ p| ^ 2
            = (stepFactor T (n + 1) τ p - stopFactor τ p) ^ 2 * (φ p) ^ 2 := by
              rw [sq_abs, sq_abs]
          _ ≤ 4 * (φ p) ^ 2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg _))
      (by
        filter_upwards [hcoe, ae_fst_mem_Ioc_trimMeasure_T (μ := μ) T ℱ] with p hp hmem
        have hev : ∀ᶠ n : ℕ in atTop, stepFactor T (n + 1) τ p = stopFactor τ p := by
          by_cases hpτ : p.1 ≤ τ p.2
          · refine Eventually.of_forall fun n => ?_
            rw [stepFactor_eq_one T (Nat.succ_pos n) τ hmem hpτ, stopFactor_apply, ite_eq_left hpτ]
          · push Not at hpτ
            have h0 : Tendsto (fun n : ℕ ↦ T / ((n + 1 : ℕ) : ℝ≥0)) atTop (𝓝 0) :=
              (tendsto_const_div_atTop_nhds_zero_nat T).comp (tendsto_add_atTop_nat 1)
            filter_upwards [(tendsto_order.1 h0).2 (p.1 - τ p.2) (tsub_pos_of_lt hpτ)] with n hn
            rw [stepFactor_eq_zero T τ (lt_tsub_iff_left.mp hn), stopFactor_eq_zero hpτ]
        have : ∀ᶠ n : ℕ in atTop, F n p = 0 := by
          filter_upwards [hev] with n hn
          rw [hp n, hn, sub_self, zero_mul]
          norm_num
        exact tendsto_const_nhds.congr' (this.mono fun n hn => hn.symm))
    simpa using key
  have hsq : ∀ n : ℕ, ‖stepKernel T (n + 1) hBmeas hτ φ - stopKernel T hτ φ‖ ^ 2
      = ∫ p, F n p ∂(trimMeasure_T (μ := μ) T ℱ) := fun n => MathFin.lp_two_norm_sq _
  have h2 : Tendsto (fun n : ℕ ↦ ‖stepKernel T (n + 1) hBmeas hτ φ - stopKernel T hτ φ‖ ^ 2)
      atTop (𝓝 0) := by
    simp_rw [hsq]; exact hint
  have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
  simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at h3
  exact h3

include hB

/-- The integral of a step kernel, as a finite sum of band increments. -/
theorem itoProcessCLM_stepKernel (T t : ℝ≥0) (htT : t ≤ T) {N : ℕ} (hN : 0 < N)
    (hBmeas : ∀ u, Measurable (B u)) {τ : Ω → ℝ≥0} (hτ : IsStop ℱ τ)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    (itoProcessCLM hB T t hBmeas (stepKernel T N hBmeas hτ φ) : Ω → ℝ)
      =ᵐ[μ] fun ω ↦ ∑ k ∈ Finset.range N, gridFactor T N k τ ω *
        (itoProcessCLM hB T (min (gridPt T N (k + 1)) t) hBmeas φ ω
          - itoProcessCLM hB T (min (gridPt T N k) t) hBmeas φ ω) := by
  rw [stepKernel, map_sum]
  have hterm : ∀ k ∈ Finset.range N,
      (itoProcessCLM hB T t hBmeas (smulAdapted T (gridPt T N k) hBmeas (gridFactor T N k τ)
        (measurable_gridFactor hτ T N k) 1 (abs_gridFactor_le T N k τ)
        (band T (gridPt T N k) (gridPt T N (k + 1)) hBmeas φ)) : Ω → ℝ)
      =ᵐ[μ] fun ω ↦ gridFactor T N k τ ω *
        (itoProcessCLM hB T (min (gridPt T N (k + 1)) t) hBmeas φ ω
          - itoProcessCLM hB T (min (gridPt T N k) t) hBmeas φ ω) := fun k hk =>
    itoProcessCLM_smulAdapted_band hB T _ _ t (gridPt_mono T N (Nat.le_succ k))
      (gridPt_le T hN (Nat.succ_le_of_lt (Finset.mem_range.mp hk))) htT hBmeas _ _ 1 _ φ
  have hall := (Filter.eventually_all_finset (Finset.range N)).mpr hterm
  filter_upwards [Lp.coeFn_finsetSum (Finset.range N) (fun k ↦ itoProcessCLM hB T t hBmeas
      (smulAdapted T (gridPt T N k) hBmeas (gridFactor T N k τ)
        (measurable_gridFactor hτ T N k) 1 (abs_gridFactor_le T N k τ)
        (band T (gridPt T N k) (gridPt T N (k + 1)) hBmeas φ))), hall] with ω h1 h2
  rw [h1, Finset.sum_apply]
  exact Finset.sum_congr rfl fun k hk => h2 k hk

/-- **Finite-valued stopped identity.** For the grid time `σ_N ≥ τ`, the integral of the
step kernel is the continuous integral at `σ_N ∧ t`. -/
theorem stepKernel_integral_eq (T t : ℝ≥0) (htT : t ≤ T) (hT : 0 < T) {N : ℕ} (hN : 0 < N)
    (hBmeas : ∀ u, Measurable (B u)) (hBcont : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω)
    {τ : Ω → ℝ≥0} (hτ : IsStop ℱ τ) (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    (itoProcessCLM hB T t hBmeas (stepKernel T N hBmeas hτ φ) : Ω → ℝ)
      =ᵐ[μ] fun ω ↦ itoContinuousMod T hBmeas φ (min (gridStop T N τ ω) t) ω := by
  have hmod : ∀ k ∈ Finset.range (N + 1),
      (fun ω ↦ itoContinuousMod T hBmeas φ (min (gridPt T N k) t) ω)
        =ᵐ[μ] itoProcessCLM hB T (min (gridPt T N k) t) hBmeas φ :=
    fun k _ ↦ itoContinuousMod_modification hB T hBmeas hBcont φ ((min_le_right _ _).trans htT)
  have hall := (Filter.eventually_all_finset (Finset.range (N + 1))).mpr hmod
  have hM0 := itoContinuousMod_modification hB T hBmeas hBcont φ (zero_le : (0 : ℝ≥0) ≤ T)
  rw [itoProcessCLM_zero_time hB T hBmeas φ] at hM0
  filter_upwards [itoProcessCLM_stepKernel hB T t htT hN hBmeas hτ φ, hall, hM0,
    Lp.coeFn_zero ℝ 2 μ] with ω h1 h2 h3 h4
  rw [h1]
  have hg : ∀ k ∈ Finset.range N, gridFactor T N k τ ω *
      (itoProcessCLM hB T (min (gridPt T N (k + 1)) t) hBmeas φ ω
        - itoProcessCLM hB T (min (gridPt T N k) t) hBmeas φ ω)
      = (if gridPt T N k < τ ω then (1 : ℝ) else 0) *
        ((fun j ↦ itoContinuousMod T hBmeas φ (min (gridPt T N j) t) ω) (k + 1)
          - (fun j ↦ itoContinuousMod T hBmeas φ (min (gridPt T N j) t) ω) k) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [← h2 (k + 1) (Finset.mem_range.mpr (Nat.succ_lt_succ hk')),
      ← h2 k (Finset.mem_range.mpr (Nat.lt_succ_of_lt hk'))]
    rfl
  have hz : itoContinuousMod T hBmeas φ 0 ω = 0 := by
    have := h3.trans h4
    simpa using this
  rw [Finset.sum_congr rfl hg, sum_gridIndicator_telescope T hT hN (τ ω)
    (fun j ↦ itoContinuousMod T hBmeas φ (min (gridPt T N j) t) ω)]
  simp only [gridPt_zero, min_eq_left (zero_le : (0 : ℝ≥0) ≤ t)]
  rw [hz, sub_zero]
  rfl

/-- **Stopped stochastic integral.** For a stopping time `τ` and `t ≤ T`,
`∫₀ᵗ 𝟙_{s ≤ τ} φ dB = (∫ φ dB)_{t ∧ τ}` almost surely, where the right side is the
continuous version of the integral evaluated at the random time `t ∧ τ`. -/
theorem itoProcessCLM_stopKernel (T t : ℝ≥0) (htT : t ≤ T) (hBmeas : ∀ u, Measurable (B u))
    (hBcont : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) {τ : Ω → ℝ≥0} (hτ : IsStop ℱ τ)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    (itoProcessCLM hB T t hBmeas (stopKernel T hτ φ) : Ω → ℝ)
      =ᵐ[μ] fun ω ↦ itoContinuousMod T hBmeas φ (min t (τ ω)) ω := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht0 | ht0
  · subst ht0
    have h1 := itoContinuousMod_modification hB T hBmeas hBcont φ (zero_le : (0 : ℝ≥0) ≤ T)
    rw [itoProcessCLM_zero_time hB T hBmeas φ] at h1
    rw [itoProcessCLM_zero_time hB T hBmeas]
    filter_upwards [h1] with ω hω
    rw [min_eq_left (zero_le : (0 : ℝ≥0) ≤ τ ω), hω]
  have hT : 0 < T := lt_of_lt_of_le ht0 htT
  have hF : Tendsto (fun n : ℕ ↦ itoProcessCLM hB T t hBmeas (stepKernel T (n + 1) hBmeas hτ φ))
      atTop (𝓝 (itoProcessCLM hB T t hBmeas (stopKernel T hτ φ))) :=
    ((itoProcessCLM hB T t hBmeas).continuous.tendsto _).comp (tendsto_stepKernel T hBmeas hτ φ)
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hF).exists_seq_tendsto_ae
  have hstep : ∀ᵐ ω ∂μ, ∀ n : ℕ,
      (itoProcessCLM hB T t hBmeas (stepKernel T (n + 1) hBmeas hτ φ) : Ω → ℝ) ω
        = itoContinuousMod T hBmeas φ (min (gridStop T (n + 1) τ ω) t) ω :=
    ae_all_iff.mpr fun n ↦ stepKernel_integral_eq hB T t htT hT (Nat.succ_pos n) hBmeas hBcont hτ φ
  filter_upwards [hae, hstep, itoContinuousMod_continuousOn hB T hBmeas hBcont φ]
    with ω h1 h2 h3
  have hx0 : min (τ ω) t ∈ Set.Icc 0 T := ⟨zero_le, (min_le_right _ _).trans htT⟩
  have hmem : ∀ n : ℕ, min (gridStop T (n + 1) τ ω) t ∈ Set.Icc 0 T :=
    fun n => ⟨zero_le, (min_le_right _ _).trans htT⟩
  have hlim : Tendsto (fun n : ℕ ↦ itoContinuousMod T hBmeas φ (min (gridStop T (n + 1) τ ω) t) ω)
      atTop (𝓝 (itoContinuousMod T hBmeas φ (min (τ ω) t) ω)) :=
    ((h3 _ hx0).tendsto).comp (tendsto_nhdsWithin_iff.mpr
      ⟨tendsto_min_gridStop T hT τ ω htT, Eventually.of_forall hmem⟩)
  have heq : (fun i ↦ (itoProcessCLM hB T t hBmeas (stepKernel T (ns i + 1) hBmeas hτ φ)
      : Ω → ℝ) ω) = fun i ↦ itoContinuousMod T hBmeas φ (min (gridStop T (ns i + 1) τ ω) t) ω :=
    funext fun i => h2 (ns i)
  have h1' := h1
  simp only [heq] at h1'
  rw [min_comm t (τ ω)]
  exact tendsto_nhds_unique h1' (hlim.comp hns.tendsto_atTop)

omit hB [IsProbabilityMeasure μ] in
/-- Processes with a.s. continuous paths on `[0,T]` that agree a.s. at each time of `[0,T]`
agree a.s. at all times of `[0,T]` simultaneously. -/
theorem ae_forall_eq_of_continuousOn' {T : ℝ≥0} {X Y : ℝ≥0 → Ω → ℝ}
    (hX : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) (Set.Icc 0 T))
    (hY : ∀ᵐ ω ∂μ, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T))
    (h : ∀ t ≤ T, X t =ᵐ[μ] Y t) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, X t ω = Y t ω := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Set.Icc (0 : ℝ≥0) T)
  have hD : ∀ᵐ ω ∂μ, ∀ d ∈ D, X d.1 ω = Y d.1 ω := by
    rw [ae_ball_iff hDc]
    intro d _
    exact h d.1 d.2.2
  filter_upwards [hX, hY, hD] with ω hXω hYω hDω
  intro t ht
  have hcX : Continuous fun s : Set.Icc (0 : ℝ≥0) T => X s.1 ω :=
    hXω.comp_continuous continuous_subtype_val (fun s => s.2)
  have hcY : Continuous fun s : Set.Icc (0 : ℝ≥0) T => Y s.1 ω :=
    hYω.comp_continuous continuous_subtype_val (fun s => s.2)
  have heq := Continuous.ext_on hDd hcX hcY (fun d hd => hDω d hd)
  exact congrFun heq ⟨t, zero_le, ht⟩

/-- **Stopped stochastic integral, pathwise form.** Almost surely, for every `t ∈ [0, T]`,
the continuous integral of the truncated kernel equals the continuous integral stopped at
`τ`: `(𝟙_{[[0,τ]]}φ ● B)_t = (φ●B)_{t ∧ τ}`. -/
theorem itoContinuousMod_stopKernel (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (hBcont : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) {τ : Ω → ℝ≥0} (hτ : IsStop ℱ τ)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, itoContinuousMod T hBmeas (stopKernel T hτ φ) t ω
      = itoContinuousMod T hBmeas φ (min t (τ ω)) ω := by
  refine ae_forall_eq_of_continuousOn'
    (X := fun t ω ↦ itoContinuousMod T hBmeas (stopKernel T hτ φ) t ω)
    (Y := fun t ω ↦ itoContinuousMod T hBmeas φ (min t (τ ω)) ω)
    (itoContinuousMod_continuousOn hB T hBmeas hBcont _) ?_ ?_
  · filter_upwards [itoContinuousMod_continuousOn hB T hBmeas hBcont φ] with ω hω
    refine hω.comp (continuous_id.min continuous_const).continuousOn ?_
    intro s hs
    exact ⟨zero_le, (min_le_left _ _).trans hs.2⟩
  · intro t ht
    filter_upwards [itoContinuousMod_modification hB T hBmeas hBcont (stopKernel T hτ φ) ht,
      itoProcessCLM_stopKernel hB T t ht hBmeas hBcont hτ φ] with ω h1 h2
    exact h1.trans h2

/-- Terminal form: `∫₀ᵀ 𝟙_{s ≤ τ} φ dB = (φ●B)_{T ∧ τ}` almost surely. -/
theorem itoIntegralCLM_T_stopKernel (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (hBcont : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) {τ : Ω → ℝ≥0} (hτ : IsStop ℱ τ)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    (itoIntegralCLM_T hB T (stopKernel T hτ φ) : Ω → ℝ)
      =ᵐ[μ] fun ω ↦ itoContinuousMod T hBmeas φ (min T (τ ω)) ω := by
  rw [← itoProcessCLM_terminal_eq hB T hBmeas]
  exact itoProcessCLM_stopKernel hB T T le_rfl hBmeas hBcont hτ φ

end CommonStopping
end MathFin.FilteredIto
