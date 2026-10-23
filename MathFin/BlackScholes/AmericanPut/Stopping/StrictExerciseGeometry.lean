/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.PricePositivity

/-! # Full exercise/continuation separation for the financial stopping value

Price positivity excludes all out-of-the-money exercise at positive maturity.
The previously constructed in-the-money threshold therefore describes the
entire nonnegative-spot contact set. Its strict positivity is not assumed or
proved here; the later `PositiveExerciseBoundary` module derives it from the
actual interior PDE and a stationary upper barrier.

## Result

Public entry points include `threshold_lt_strike_of_price_pos`, `value_contact_iff_le_threshold`,
`value_strict_continuation_iff`, `canonicalStockBoundary`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped NNReal Topology

section General

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → ℝ}
  {K r q σ : ℝ} {T : ℝ≥0}

theorem threshold_lt_strike_of_price_pos (hW : Measurable W.uncurry)
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0) (hK : 0 ≤ K) (hr : 0 ≤ r)
    (hpos : 0 < americanPutValue P 𝓕 W K r q σ K T) :
    exerciseThreshold P 𝓕 W K r q σ T < K := by
  have hm := threshold_mem_exerciseSet (P := P) (𝓕 := 𝓕) (q := q) (σ := σ) (T := T)
    hW hzero hK hr
  apply lt_of_le_of_ne hm.2.1
  intro he
  have hh := hm.2.2
  rw [he,sub_self] at hh
  linarith

theorem value_contact_iff_le_threshold (hW : Measurable W.uncurry)
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0) (hK : 0 < K) (hr : 0 ≤ r)
    (hpos : ∀ S, 0 < S → 0 < americanPutValue P 𝓕 W K r q σ S T)
    {S : ℝ} (hS : 0 ≤ S) :
    americanPutValue P 𝓕 W K r q σ S T = max (K-S) 0 ↔
      S ≤ exerciseThreshold P 𝓕 W K r q σ T := by
  have hset := exerciseSet_eq_interval (P := P) (𝓕 := 𝓕) (q := q) (σ := σ) (T := T)
    hW hzero hK.le hr
  constructor
  · intro he
    have hSK : S ≤ K := by
      by_contra hn
      have hlt : K < S := lt_of_not_ge hn
      have hp := hpos S (hK.trans hlt)
      rw [he,max_eq_right (sub_nonpos.mpr hlt.le)] at hp
      exact (lt_irrefl 0) hp
    have hm : S ∈ exerciseSet P 𝓕 W K r q σ T :=
      ⟨hS,hSK,by simpa only [max_eq_left (sub_nonneg.mpr hSK)] using he⟩
    rw [hset] at hm
    exact hm.2
  · intro hSB
    have hm : S ∈ exerciseSet P 𝓕 W K r q σ T := by rw [hset]; exact ⟨hS,hSB⟩
    simpa only [max_eq_left (sub_nonneg.mpr hm.2.1)] using hm.2.2

theorem value_strict_continuation_iff (hW : Measurable W.uncurry)
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0) (hK : 0 < K) (hr : 0 ≤ r)
    (hpos : ∀ S, 0 < S → 0 < americanPutValue P 𝓕 W K r q σ S T)
    {S : ℝ} (hS : 0 ≤ S) :
    max (K-S) 0 < americanPutValue P 𝓕 W K r q σ S T ↔
      exerciseThreshold P 𝓕 W K r q σ T < S := by
  have he := value_contact_iff_le_threshold hW hzero hK hr hpos hS
  have hlo := payoff_le_value (P := P) (𝓕 := 𝓕) (q := q) (σ := σ) (T := T)
    hW hzero hK.le hr hS
  constructor
  · intro hp
    exact lt_of_not_ge (fun hSB => hp.ne' (he.mpr hSB))
  · intro hSB
    exact lt_of_le_of_ne hlo (fun hh => (not_le.mpr hSB) (he.mp hh.symm))

end General

/-- The exercise threshold `brownianUsualExerciseBoundary` in the canonical normalization
`K = 1`, `σ = Real.sqrt 2`, at the maturity `t.toNNReal`. -/
noncomputable def canonicalStockBoundary (k h t : ℝ) : ℝ :=
  brownianUsualExerciseBoundary 1 k h (Real.sqrt 2) t.toNNReal

theorem canonicalStockBoundary_lt_one {k h : ℝ} (hk : 0 ≤ k) {t : ℝ} (ht : 0 < t) :
    canonicalStockBoundary k h t < 1 := by
  let μ := completedMeasure gaussianLimit
  have hz : ∀ᵐ ω ∂μ, brownian 0 ω = 0 := isBrownianReal_brownian.eval_zero_ae_eq_zero
  have hp := brownianUsualAmericanPut_pos (K := 1) (q := h) (σ := Real.sqrt 2) (S := 1)
    (by norm_num) hk (Real.sqrt_pos.mpr (by norm_num)) (by norm_num) (Real.toNNReal_pos.mpr ht)
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  exact threshold_lt_strike_of_price_pos (P := μ) (𝓕 := brownianUsualFiltration)
    brownian_completed_measurable hz (by norm_num) hk hp

theorem canonicalPrice_contact_iff {k h : ℝ} (hk : 0 ≤ k) (x : ℝ) {t : ℝ} (ht : 0 < t) :
    canonicalPrice k h x t = putPayoff x ↔ Real.exp x ≤ canonicalStockBoundary k h t := by
  let μ := completedMeasure gaussianLimit
  have hz : ∀ᵐ ω ∂μ, brownian 0 ω = 0 := isBrownianReal_brownian.eval_zero_ae_eq_zero
  have hp (S : ℝ) (hS : 0 < S) := brownianUsualAmericanPut_pos (K := 1) (q := h)
    (σ := Real.sqrt 2) (by norm_num) hk (Real.sqrt_pos.mpr (by norm_num)) hS
    (Real.toNNReal_pos.mpr ht)
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  exact value_contact_iff_le_threshold (P := μ) (𝓕 := brownianUsualFiltration)
    brownian_completed_measurable hz (by norm_num) hk hp (Real.exp_pos x).le

theorem canonicalPrice_strict_continuation_iff {k h : ℝ} (hk : 0 ≤ k) (x : ℝ)
    {t : ℝ} (ht : 0 < t) :
    putPayoff x < canonicalPrice k h x t ↔ canonicalStockBoundary k h t < Real.exp x := by
  have he := canonicalPrice_contact_iff (h := h) hk x ht
  have hlo := (canonicalPrice_bounds (h := h) hk x t).1
  constructor
  · intro hp
    exact lt_of_not_ge (fun hSB => hp.ne' (he.mpr hSB))
  · intro hSB
    exact lt_of_le_of_ne hlo (fun hh => (not_le.mpr hSB) (he.mp hh.symm))

theorem canonicalStockBoundary_nonneg {k h : ℝ} (hk : 0 ≤ k) (t : ℝ) :
    0 ≤ canonicalStockBoundary k h t := by
  let μ := completedMeasure gaussianLimit
  have hz : ∀ᵐ ω ∂μ, brownian 0 ω = 0 := isBrownianReal_brownian.eval_zero_ae_eq_zero
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  exact (threshold_bounds (P := μ) (𝓕 := brownianUsualFiltration)
    brownian_completed_measurable hz (by norm_num) hk).1

theorem canonicalStockBoundary_initial {k h : ℝ} (hk : 0 ≤ k) :
    canonicalStockBoundary k h 0 = 1 := by
  let μ := completedMeasure gaussianLimit
  have hz : ∀ᵐ ω ∂μ, brownian 0 ω = 0 := isBrownianReal_brownian.eval_zero_ae_eq_zero
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  have hh := threshold_at_expiry (P := μ) (𝓕 := brownianUsualFiltration) (K := 1)
    (q := h) (σ := Real.sqrt 2) brownian_completed_measurable hz (by norm_num) hk
  simpa only [canonicalStockBoundary,brownianUsualExerciseBoundary,Real.toNNReal_zero] using hh

/-- An open continuation domain defined from the actual price, before any PDE
or positive/smooth logarithmic boundary has been established. -/
def canonicalContinuationRegion (k h : ℝ) : Set (ℝ × ℝ) :=
  {z | 0 < z.2 ∧ putPayoff z.1 < canonicalPrice k h z.1 z.2}

theorem canonicalContinuationRegion_isOpen {k h : ℝ} (hk : 0 ≤ k) :
    IsOpen (canonicalContinuationRegion k h) := by
  exact (isOpen_lt continuous_const continuous_snd).inter
    (isOpen_lt (show Continuous (fun z : ℝ × ℝ => putPayoff z.1) by
      unfold putPayoff; fun_prop) (canonicalPrice_continuous hk))

theorem canonicalContinuationRegion_eq {k h : ℝ} (hk : 0 ≤ k) :
    canonicalContinuationRegion k h =
      {z | 0 < z.2 ∧ canonicalStockBoundary k h z.2 < Real.exp z.1} := by
  ext z
  exact and_congr_right (fun ht => canonicalPrice_strict_continuation_iff hk z.1 ht)

end MathFin.BlackScholes.AmericanPut.Stopping
