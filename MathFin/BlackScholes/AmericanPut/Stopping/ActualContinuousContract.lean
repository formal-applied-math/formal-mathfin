/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ActualGradientTrace
public import MathFin.BlackScholes.AmericanPut.Boundary.ContinuousBoundaryProblem

/-! # The actual price satisfies the continuous-boundary pricing contract

Every field is proved for the usual-filtration stopping value. Unlike the
classical assembly, this theorem has no remaining boundary-smoothness premise.

## Result

Public entry points include `canonicalPrice_continuousBoundaryPutSolution`,
`zeroDividend_canonicalPrice_continuousBoundaryPutSolution`,
`liuRange_canonicalPrice_continuousBoundaryPutSolution`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter Boundary
open scoped Topology ContDiff

theorem canonicalPrice_continuousBoundaryPutSolution {k h : ℝ}
    (hk : 0 < k) (hh : 0 ≤ h) (hhk : h ≤ k) :
    ContinuousBoundaryPutSolution k h (canonicalPrice k h) (canonicalLogBoundary k h) := by
  have hregion : canonicalContinuationRegion k h = continuationRegion (canonicalLogBoundary k h) :=
    canonicalContinuationRegion_eq_logBoundary hk hh hhk
  refine {
    rate_pos := hk
    dividend_nonneg := hh
    dividend_le_rate := hhk
    boundary_initial := canonicalLogBoundary_initial hk
    boundary_continuous := canonicalLogBoundary_continuousOn hk hh hhk
    toPutEnvelope := canonicalPrice_putEnvelope hk.le
    price_smooth := ?_
    exercise := ?_
    continuation := ?_
    equation := ?_
    smooth_fit := fun _ ht => canonicalPrice_smooth_fit hk hh hhk ht
    gradient_trace := fun _ ht => canonicalPrice_gradient_trace hk hh hhk ht
    decay := fun t _ => canonicalPrice_decay hk.le t }
  · rw [← hregion]
    exact canonicalPrice_contDiffOn hk.le
  · intro x t ht hx
    rw [(canonicalPrice_contact_iff_logBoundary hk hh hhk ht).mpr hx]
    exact putPayoff_of_nonpos (hx.trans (canonicalLogBoundary_neg hk hh hhk ht).le)
  · intro x t ht hx
    have hz : (x,t) ∈ canonicalContinuationRegion k h := by
      rw [hregion]
      exact ⟨ht,hx⟩
    exact hz.2
  · intro x t ht hx
    have hz : (x,t) ∈ canonicalContinuationRegion k h := by
      rw [hregion]
      exact ⟨ht,hx⟩
    exact canonicalPrice_continuation_pde hk.le hz

theorem zeroDividend_canonicalPrice_continuousBoundaryPutSolution {k : ℝ} (hk : 0 < k) :
    ContinuousBoundaryPutSolution k 0 (canonicalPrice k 0) (canonicalLogBoundary k 0) :=
  canonicalPrice_continuousBoundaryPutSolution hk le_rfl hk.le

theorem liuRange_canonicalPrice_continuousBoundaryPutSolution {k h : ℝ}
    (hh : 0 ≤ h) (hliu : h + 1 ≤ k) :
    ContinuousBoundaryPutSolution k h (canonicalPrice k h) (canonicalLogBoundary k h) :=
  canonicalPrice_continuousBoundaryPutSolution (by linarith) hh (by linarith)

end MathFin.BlackScholes.AmericanPut.Stopping
