/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.BrownianGerm
public import MathFin.BlackScholes.AmericanPut.Stopping.ActualBoundaryContinuity
public import MathFin.BlackScholes.AmericanPut.Stopping.ActualOptimality

/-! # Optimal contact times tend to zero at the actual exercise boundary

An early downward Brownian excursion reaches exercise for every sufficiently
nearby initial log price. The boundary moves in the favorable direction as
remaining maturity decreases. This gives almost-sure convergence of the actual
first-contact times, not an assumption of probabilistic boundary regularity.

## Result

Public entry points include `brownianUsualActualContactTime_le_of_downcrossing`, `brownianUsualActualContactTime_tendsto_of_germ`, `brownianUsualActualContactTime_tendsto_boundary`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

theorem brownianUsualActualContactTime_le_of_downcrossing {k h : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (x : ℝ) {T s : ℝ≥0} (hs : s < T)
    (ω : ℝ≥0 → ℝ)
    (hcross : x+(k-h-1)*(s : ℝ)+Real.sqrt 2*brownian s ω ≤
      canonicalLogBoundary k h (T : ℝ)) :
    brownianUsualActualContactTime (h := h) hk.le x T ω ≤ s := by
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  by_contra! hτ
  have hcont := canonicalContactRule_continuation_before (h := h) hk.le
    brownianUsual_adapted continuous_brownian x T ω
    (show s < (canonicalContactRule (h := h) hk.le brownianUsual_adapted continuous_brownian x T).time ω from hτ)
  rw [canonicalContinuationRegion_eq_logBoundary hk hh hhk] at hcont
  have hsR : (s : ℝ) < (T : ℝ) := by exact_mod_cast hs
  have hmono := canonicalLogBoundary_antitoneOn hk hh hhk
    (show (T : ℝ)-(s : ℝ) ∈ Ici 0 from sub_nonneg.mpr hsR.le)
    (show (T : ℝ) ∈ Ici 0 from T.coe_nonneg)
    (sub_le_self _ s.coe_nonneg)
  have hpath : canonicalLogPath brownian k h x T s ω =
      x+(k-h-1)*(s : ℝ)+Real.sqrt 2*brownian s ω := by
    simp only [canonicalLogPath,min_eq_left hs.le,min_eq_left hsR.le]
  have hlt := hcont.2
  dsimp only [mem_ofPred_eq] at hlt
  rw [hpath] at hlt
  linarith

theorem brownianUsualActualContactTime_tendsto_of_germ {k h : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) {T : ℝ≥0} (hT : 0 < T)
    {ω : ℝ≥0 → ℝ} (hω : ω ∈ brownianNegativeGerm) :
    Tendsto (fun x => brownianUsualActualContactTime (h := h) hk.le x T ω)
      (𝓝 (canonicalLogBoundary k h (T : ℝ))) (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact (not_lt_of_ge (bot_le : (0 : ℝ≥0) ≤ a) ha).elim
  · intro δ hδ
    obtain ⟨s,_hs0,hs,hneg⟩ := brownian_downward_excursion_of_germ hω (k-h-1) (Real.sqrt 2)
      (Real.sqrt_pos.mpr (by norm_num)) (lt_min hδ hT)
    have hsδ : s < δ := hs.trans_le (min_le_left _ _)
    have hsT : s < T := hs.trans_le (min_le_right _ _)
    have hnear : canonicalLogBoundary k h (T : ℝ) <
        canonicalLogBoundary k h (T : ℝ)-((k-h-1)*(s : ℝ)+Real.sqrt 2*brownian s ω) := by
      linarith
    filter_upwards [Iio_mem_nhds hnear] with x hx
    change x < canonicalLogBoundary k h (T : ℝ)-((k-h-1)*(s : ℝ)+Real.sqrt 2*brownian s ω) at hx
    exact (brownianUsualActualContactTime_le_of_downcrossing hk hh hhk x hsT ω (by linarith)).trans_lt hsδ

/-- This is convergence of the actual optimal rules, whose optimality was
proved separately, on the completed usual Brownian probability space. -/
theorem brownianUsualActualContactTime_tendsto_boundary {k h : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) {T : ℝ≥0} (hT : 0 < T) :
    ∀ᵐ ω ∂completedMeasure gaussianLimit,
      Tendsto (fun x => brownianUsualActualContactTime (h := h) hk.le x T ω)
        (𝓝 (canonicalLogBoundary k h (T : ℝ))) (𝓝 0) := by
  have hg : ∀ᵐ ω ∂completedMeasure gaussianLimit, ω ∈ brownianNegativeGerm := brownianNegativeGerm_ae
  filter_upwards [hg] with ω hω
  exact brownianUsualActualContactTime_tendsto_of_germ hk hh hhk hT hω

end MathFin.BlackScholes.AmericanPut.Stopping
