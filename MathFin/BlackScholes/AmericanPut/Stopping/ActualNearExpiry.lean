/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ActualConvexLowerComparison
public import MathFin.BlackScholes.AmericanPut.Boundary.ExpiryBarrier

/-! # The actual boundary lies below every fixed line near expiry

The shrinking square-root barrier is compared directly with the stopping
price using its positive spatial curvature. No classical boundary regularity,
European asymptotic, or boundary convexity is assumed.

## Result

Public entry points include `expiryBarrier_le_canonicalPrice`,
`canonicalPrice_exists_expiryBarrier_window`, `canonicalLogBoundary_exists_sqrt_upper_bound`,
`canonicalLogBoundary_below_linear_eventually`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter Boundary
open scoped Topology

theorem expiryBarrier_le_canonicalPrice {k h T : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (hT1 : T ≤ 1)
    (hsmall : (|k - h-1| + k) * Real.sqrt T ≤ 1 / 4) :
    ∀ z ∈ twoSidedStrip (fun t => -Real.sqrt t) Real.sqrt T,
      expiryBarrier z.1 z.2 ≤ canonicalPrice k h z.1 z.2 := by
  have hL : Continuous (fun t : ℝ => -Real.sqrt t) := Real.continuous_sqrt.neg
  have hR : Continuous Real.sqrt := Real.continuous_sqrt
  apply convex_subsolution_le_canonicalPrice_on_strip hk hh hhk hL hR
    (twoSidedStrip_isCompact hL hR (fun t _ => by linarith [Real.sqrt_nonneg t]))
    (expiryBarrier_continuousOn T) (fun _ _ ht _ _ _ => expiryBarrier_contDiffAt ht)
  · intro x t ht _ _ _
    rw [expiryBarrier_deriv2_x x ht]
    positivity
  · intro x t ht htT hl hr
    have he := expiryBarrier_subsolution hk.le ht (htT.trans hT1)
      ((mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htT)
        (add_nonneg (abs_nonneg _) hk.le)).trans hsmall) hl.le hr.le
    unfold pricingOperator dividendSpatialOperator at *
    dsimp only
    linarith
  · intro x _ _
    simpa only [expiryBarrier_zero] using
      (putPayoff_nonneg x).trans (canonicalPrice_bounds (h := h) hk.le x 0).1
  · intro t ht htT
    exact (expiryBarrier_left_le_payoff ht (htT.trans hT1)).trans
        (canonicalPrice_bounds hk.le _ t).1
  · intro t ht _
    simpa using (putPayoff_nonneg (Real.sqrt t)).trans
      (canonicalPrice_bounds (h := h) hk.le (Real.sqrt t) t).1

theorem canonicalPrice_exists_expiryBarrier_window {k h : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) :
    ∃ T : ℝ, 0 < T ∧ ∀ z ∈ twoSidedStrip (fun t => -Real.sqrt t) Real.sqrt T,
      expiryBarrier z.1 z.2 ≤ canonicalPrice k h z.1 z.2 := by
  have hc : Continuous (fun t : ℝ => (|k-h-1|+k)*Real.sqrt t) := by fun_prop
  have he : ∀ᶠ t in 𝓝[>] (0 : ℝ), (|k-h-1|+k)*Real.sqrt t < 1/4 :=
    nhdsWithin_le_nhds (hc.continuousAt.eventually (Iio_mem_nhds (by norm_num)))
  obtain ⟨a,ha,hall⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp he
  let T := min a 1/2
  have hT : 0 < T := by dsimp [T]; positivity
  have hTa : T < a := by dsimp [T]; linarith [min_le_left a 1]
  have hT1 : T ≤ 1 := by dsimp [T]; linarith [min_le_right a 1]
  exact ⟨T,hT,expiryBarrier_le_canonicalPrice hk hh hhk hT1 (hall ⟨hT,hTa⟩).le⟩

theorem canonicalLogBoundary_exists_sqrt_upper_bound {k h : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) :
    ∃ T : ℝ, 0 < T ∧ ∀ t, 0 < t → t ≤ T → canonicalLogBoundary k h t < -Real.sqrt t/64 := by
  obtain ⟨T,hT,hbound⟩ := canonicalPrice_exists_expiryBarrier_window hk hh hhk
  refine ⟨T,hT,?_⟩
  intro t ht htT
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  let x := -Real.sqrt t/64
  have hx : x ≤ 0 := by dsimp [x]; linarith
  have hl : -Real.sqrt t ≤ x := by dsimp [x]; linarith
  have hr : x ≤ Real.sqrt t := hx.trans hs.le
  have hp : Real.sqrt t/16 ≤ canonicalPrice k h x t :=
    (expiryBarrier_ge_sqrt ht hx).trans (hbound (x,t) ⟨ht.le,htT,hl,hr⟩)
  have hpay : 1-Real.exp x ≤ Real.sqrt t/64 := by
    have he := Real.add_one_le_exp x
    dsimp [x] at *
    linarith
  by_contra! hn
  rw [canonicalPrice_exercise_value hk hh hhk ht hn] at hp
  linarith

theorem canonicalLogBoundary_below_linear_eventually {k h : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (M : ℝ) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), canonicalLogBoundary k h t < -M*t := by
  obtain ⟨T,hT,hbound⟩ := canonicalLogBoundary_exists_sqrt_upper_bound hk hh hhk
  have hc : Continuous (fun t : ℝ => 64*M*Real.sqrt t) := by fun_prop
  have he : ∀ᶠ t in 𝓝[>] (0 : ℝ), 64*M*Real.sqrt t < 1 :=
    nhdsWithin_le_nhds (hc.continuousAt.eventually (Iio_mem_nhds (by norm_num)))
  filter_upwards [he,nhdsWithin_le_nhds (Iio_mem_nhds hT),self_mem_nhdsWithin] with t hsm htT ht
  have ht0 : 0 < t := ht
  have hs := Real.sqrt_pos.mpr ht0
  have hm := mul_lt_mul_of_pos_right hsm hs
  have hs2 := Real.sq_sqrt ht0.le
  have hMt : M*t < Real.sqrt t/64 := by
    nlinarith [congrArg (fun y : ℝ => M*y) hs2]
  exact (hbound t ht0 htT.le).trans (by linarith)

theorem canonicalLogBoundary_ratio_tendsto_atBot {k h : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) :
    Tendsto (fun t => canonicalLogBoundary k h t/t) (𝓝[>] 0) atBot := by
  apply tendsto_atBot.mpr
  intro a
  filter_upwards [canonicalLogBoundary_below_linear_eventually hk hh hhk (|a|+1),
    self_mem_nhdsWithin] with t hb ht
  have hr := (div_lt_iff₀ (show 0 < t from ht)).mpr hb
  have ha : -(|a|+1) ≤ a := by linarith [neg_abs_le a]
  exact hr.le.trans ha

end MathFin.BlackScholes.AmericanPut.Stopping
