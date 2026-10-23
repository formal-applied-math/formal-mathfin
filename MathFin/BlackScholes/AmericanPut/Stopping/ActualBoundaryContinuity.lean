/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ContinuationSlice
public import MathFin.BlackScholes.AmericanPut.Stopping.BoundarySemicontinuity

/-! # Continuity of the actual exercise boundary

The slice-forcing argument excludes downward jumps. Together with the already
proved upper semicontinuity and monotonicity, it gives full continuity, including
expiry. No smooth-fit or free-boundary differentiability assumption is used.

## Result

Public entry points include `canonicalStockBoundary_exists_later_gt`,
`canonicalStockBoundary_continuousAt`, `canonicalStockBoundary_continuousOn`,
`canonicalLogBoundary_continuousAt`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter Boundary
open scoped Topology ContDiff

theorem canonicalStockBoundary_exists_later_gt {k h a u : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (ha : 0 ≤ a)
    (hu : u < canonicalStockBoundary k h a) :
    ∃ t : ℝ, a < t ∧ u < canonicalStockBoundary k h t := by
  by_contra! hdown
  have hu0 : 0 < u :=
    (canonicalStockBoundary_pos hk hh hhk (show 0 ≤ a+1 by linarith)).trans_le
      (hdown (a+1) (by linarith))
  let l := Real.log u
  let r := canonicalLogBoundary k h a
  have hlr : l < r := Real.log_lt_log hu0 hu
  have hB1 : canonicalStockBoundary k h a ≤ 1 := by
    have he := canonicalStockBoundary_antitone (h := h) hk.le ha
    simpa only [canonicalStockBoundary_initial hk.le] using he
  have hr0 : r ≤ 0 := Real.log_nonpos (canonicalStockBoundary_pos hk hh hhk ha).le hB1
  let c := (l+r)/2
  let ρ := (r-l)/4
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hL : l < c-ρ := by dsimp [c,ρ]; linarith
  have hR : c+ρ < r := by dsimp [c,ρ]; linarith
  have hR0 : c+ρ < 0 := hR.trans_le hr0
  have hinit (x : ℝ) (hx : x ≤ c+ρ) : canonicalPrice k h x a = 1-Real.exp x := by
    have hx0 : x < 0 := hx.trans_lt hR0
    have hp : canonicalPrice k h x a = putPayoff x := by
      rcases ha.eq_or_lt with he | ht
      · rw [← he,canonicalPrice_initial hk.le]
      · exact (canonicalPrice_contact_iff_logBoundary hk hh hhk ht).mpr (hx.trans hR.le)
    simpa only [putPayoff,max_eq_left (sub_nonneg.mpr (Real.exp_le_one_iff.mpr hx0.le))] using hp
  apply canonicalPrice_no_instantaneous_interval hk hh hhk hρ hR0
    (hinit (c-ρ) (by linarith)) (hinit (c+ρ) le_rfl)
  intro t ht x hx
  have ht0 : 0 < t := ha.trans_lt ht
  have hux : u < Real.exp x := by
    calc
      u = Real.exp l := (Real.exp_log hu0).symm
      _ < Real.exp x := Real.exp_lt_exp.mpr (hL.trans hx.1)
  exact ⟨ht0,(canonicalPrice_strict_continuation_iff hk.le x ht0).mpr
    ((hdown t ht).trans_lt hux)⟩

/-- Continuity at every nonnegative maturity, with the price's total-time
extension giving a two-sided statement even at expiry. -/
theorem canonicalStockBoundary_continuousAt {k h a : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (ha : 0 ≤ a) :
    ContinuousAt (canonicalStockBoundary k h) a := by
  apply tendsto_order.mpr
  constructor
  · intro u hu
    obtain ⟨t,ht,hut⟩ := canonicalStockBoundary_exists_later_gt hk hh hhk ha hu
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact hut.trans_le (canonicalStockBoundary_antitone hk.le hs.le)
  · intro u hu
    exact canonicalStockBoundary_upperSemicontinuous hk.le a u hu

theorem canonicalStockBoundary_continuousOn {k h : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) :
    ContinuousOn (canonicalStockBoundary k h) (Ici 0) :=
  fun _ ha => (canonicalStockBoundary_continuousAt hk hh hhk ha).continuousWithinAt

theorem canonicalLogBoundary_continuousAt {k h a : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (ha : 0 ≤ a) :
    ContinuousAt (canonicalLogBoundary k h) a :=
  (canonicalStockBoundary_continuousAt hk hh hhk ha).log
    (ne_of_gt (canonicalStockBoundary_pos hk hh hhk ha))

theorem canonicalLogBoundary_continuousOn {k h : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) :
    ContinuousOn (canonicalLogBoundary k h) (Ici 0) :=
  fun _ ha => (canonicalLogBoundary_continuousAt hk hh hhk ha).continuousWithinAt

theorem canonicalLogBoundary_antitoneOn {k h : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) :
    AntitoneOn (canonicalLogBoundary k h) (Ici 0) := by
  intro s hs t ht hst
  exact Real.log_le_log (canonicalStockBoundary_pos hk hh hhk ht)
    (canonicalStockBoundary_antitone hk.le hst)

theorem zeroDividend_canonicalLogBoundary_continuousOn {k : ℝ} (hk : 0 < k) :
    ContinuousOn (canonicalLogBoundary k 0) (Ici 0) :=
  canonicalLogBoundary_continuousOn hk le_rfl hk.le

end MathFin.BlackScholes.AmericanPut.Stopping
