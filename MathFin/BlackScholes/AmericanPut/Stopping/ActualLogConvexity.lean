/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ActualComparisonIntervals
public import MathFin.BlackScholes.AmericanPut.Stopping.ActualNearExpiry
public import MathFin.BlackScholes.AmericanPut.Boundary.LineIntervalConvexity

/-! # Convexity of the actual logarithmic exercise boundary

This is a convex-function statement for the constructed usual-filtration
stopping value, without a boundary-smoothness or classical-solution premise.
It does not assert existence of classical boundary second derivatives or
strict logarithmic curvature.

## Result

Public entry points include `canonicalLogBoundary_convexOn`,
`zeroDividend_canonicalLogBoundary_convexOn`, and `liuRange_canonicalLogBoundary_convexOn`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter Boundary
open scoped Topology

theorem canonicalLogBoundary_convexOn {k h : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) : ConvexOn ℝ (Ioi 0) (canonicalLogBoundary k h) := by
  apply convexOn_of_negative_line_intervals
    (fun _ ht => canonicalLogBoundary_neg hk hh hhk ht)
    ((canonicalLogBoundary_antitoneOn hk hh hhk).mono (Ioi_subset_Ici_self))
  · intro c T _ hT
    have hnear := canonicalLogBoundary_below_linear_eventually hk hh hhk c
    have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
    have hless : ∀ᶠ t : ℝ in 𝓝[>] 0, t < T := nhdsWithin_le_nhds (Iio_mem_nhds hT)
    exact (hpos.and (hless.and hnear)).exists
  · intro c d hc hd
    exact canonicalLogBoundary_below_line_time_interval hk hh hhk hc hd

theorem zeroDividend_canonicalLogBoundary_convexOn {k : ℝ} (hk : 0 < k) :
    ConvexOn ℝ (Ioi 0) (canonicalLogBoundary k 0) :=
  canonicalLogBoundary_convexOn hk le_rfl hk.le

theorem liuRange_canonicalLogBoundary_convexOn {k h : ℝ}
    (hh : 0 ≤ h) (hliu : h + 1 ≤ k) : ConvexOn ℝ (Ioi 0) (canonicalLogBoundary k h) :=
  canonicalLogBoundary_convexOn (by linarith) hh (by linarith)

end MathFin.BlackScholes.AmericanPut.Stopping
