/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ActualLogConvexity
public import MathFin.BlackScholes.AmericanPut.Stopping.ActualNoFlatTail
public import MathFin.BlackScholes.AmericanPut.Boundary.ConvexStrictMonotonicity
public import Mathlib.Analysis.Convex.Continuous

/-! # Strict decrease and stock convexity of the actual exercise boundary

These are function-level results for the constructed stopping value, without
a classical-solution or boundary-smoothness premise. In particular, strict
convexity does not assert existence or positivity of classical second derivatives.

## Result

Public entry points include `canonicalLogBoundary_strictAntiOn`,
`canonicalStockBoundary_strictAntiOn`, `canonicalStockBoundary_strictConvexOn`,
`canonicalLogBoundary_locallyLipschitzOn`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Boundary

theorem canonicalLogBoundary_strictAntiOn {k h : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) : StrictAntiOn (canonicalLogBoundary k h) (Ioi 0) := by
  exact strictAntiOn_of_convex_antitone_no_flat_tail (canonicalLogBoundary_convexOn hk hh hhk)
    ((canonicalLogBoundary_antitoneOn hk hh hhk).mono Ioi_subset_Ici_self)
    (fun _ hA => canonicalLogBoundary_no_flat_tail hk hh hhk hA)

theorem canonicalStockBoundary_strictAntiOn {k h : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) : StrictAntiOn (canonicalStockBoundary k h) (Ioi 0) := by
  intro s hs t ht hst
  rw [← exp_canonicalLogBoundary hk hh hhk hs.le,← exp_canonicalLogBoundary hk hh hhk ht.le]
  exact Real.exp_lt_exp.mpr (canonicalLogBoundary_strictAntiOn hk hh hhk hs ht hst)

theorem canonicalStockBoundary_strictConvexOn {k h : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) : StrictConvexOn ℝ (Ioi 0) (canonicalStockBoundary k h) := by
  apply (strictConvexOn_exp_of_convex_injective (canonicalLogBoundary_convexOn hk hh hhk)
    (canonicalLogBoundary_strictAntiOn hk hh hhk).injOn).congr
  intro t ht
  exact exp_canonicalLogBoundary hk hh hhk ht.le

theorem canonicalLogBoundary_locallyLipschitzOn {k h : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) : LocallyLipschitzOn (Ioi 0) (canonicalLogBoundary k h) :=
  (canonicalLogBoundary_convexOn hk hh hhk).locallyLipschitzOn isOpen_Ioi

theorem canonicalStockBoundary_locallyLipschitzOn {k h : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) : LocallyLipschitzOn (Ioi 0) (canonicalStockBoundary k h) :=
  (canonicalStockBoundary_strictConvexOn hk hh hhk).convexOn.locallyLipschitzOn isOpen_Ioi

theorem zeroDividend_canonicalLogBoundary_strictAntiOn {k : ℝ} (hk : 0 < k) :
    StrictAntiOn (canonicalLogBoundary k 0) (Ioi 0) :=
  canonicalLogBoundary_strictAntiOn hk le_rfl hk.le

theorem liuRange_canonicalLogBoundary_strictAntiOn {k h : ℝ}
    (hh : 0 ≤ h) (hliu : h + 1 ≤ k) : StrictAntiOn (canonicalLogBoundary k h) (Ioi 0) :=
  canonicalLogBoundary_strictAntiOn (by linarith) hh (by linarith)

theorem zeroDividend_canonicalStockBoundary_strictConvexOn {k : ℝ} (hk : 0 < k) :
    StrictConvexOn ℝ (Ioi 0) (canonicalStockBoundary k 0) :=
  canonicalStockBoundary_strictConvexOn hk le_rfl hk.le

theorem liuRange_canonicalStockBoundary_strictConvexOn {k h : ℝ}
    (hh : 0 ≤ h) (hliu : h + 1 ≤ k) :
    StrictConvexOn ℝ (Ioi 0) (canonicalStockBoundary k h) :=
  canonicalStockBoundary_strictConvexOn (by linarith) hh (by linarith)

end MathFin.BlackScholes.AmericanPut.Stopping
