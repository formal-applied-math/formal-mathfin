/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ActualContinuousContract
public import MathFin.BlackScholes.AmericanPut.Boundary.ComparisonUnimodality
public import MathFin.BlackScholes.AmericanPut.Boundary.Tangency
public import MathFin.BlackScholes.AmericanPut.Boundary.ContinuousContact

/-! # The proposed comparison invariant for the actual stopping price

The single-positive-interval principle and terminal contact obstruction now
hold for the constructed price and boundary, without a classical-solution
premise or any time differentiability of the boundary.

## Result

Public entry points include `canonicalStraightDifference_superlevel_interval`,
`canonicalStraightDifference_positive_interval`, `canonicalLogBoundary_no_return_contact`,
`zeroDividend_canonicalStraightDifference_positive_interval`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter Boundary Boundary.Comparison
open scoped Topology

theorem canonicalStraightDifference_superlevel_interval {k h c d t ε : ℝ}
    (hk : 0 < k) (hh : 0 ≤ h) (hhk : h ≤ k) (hc : 0 < c) (hd : d ≤ 0)
    (ht : 0 < t) (hε : 0 ≤ ε) :
    OrdConnected {x | canonicalLogBoundary k h t < x ∧
      ε < straightDifference (canonicalPrice k h) k h c d x t} :=
  straightDifference_superlevel_interval (canonicalPrice_continuousBoundaryPutSolution hk hh hhk)
    hc hd ht hε

theorem canonicalStraightDifference_positive_interval {k h c d t : ℝ}
    (hk : 0 < k) (hh : 0 ≤ h) (hhk : h ≤ k) (hc : 0 < c) (hd : d ≤ 0) (ht : 0 < t) :
    OrdConnected {x | canonicalLogBoundary k h t < x ∧
      0 < straightDifference (canonicalPrice k h) k h c d x t} :=
  canonicalStraightDifference_superlevel_interval hk hh hhk hc hd ht le_rfl

/-- A line cannot reach contact after lying strictly above the actual
boundary and then lie above it again at a later maturity. No boundary
derivatives, isolated-contact hypothesis, or local curvature are assumed. -/
theorem canonicalLogBoundary_no_return_contact {k h c d a T U : ℝ}
    (hk : 0 < k) (hh : 0 ≤ h) (hhk : h ≤ k) (hc : 0 < c) (hd : d ≤ 0)
    (ha : 0 < a) (haT : a < T) (hTU : T < U)
    (hcontact : canonicalLogBoundary k h T = d - c*T)
    (hpast : ∀ t ∈ Ico a T, canonicalLogBoundary k h t < d - c*t)
    (hfuture : canonicalLogBoundary k h U < d - c*U) : False := by
  let hp := canonicalPrice_continuousBoundaryPutSolution hk hh hhk
  have hU : 0 < U := (ha.trans haT).trans hTU
  have hpos : 0 < straightDifference (canonicalPrice k h) k h c d (d-c*U) U := by
    simpa only [lineDifference,movingLineTransform,zero_add] using
      lineDifference_on_line_pos hp hU hfuture
  obtain ⟨x,hx,hpx⟩ := straightDifference_positive_at_earlier_time hp hc hd
    (ha.trans haT).le hTU.le hfuture.le hpos
  exact no_contact_of_past_line_below_and_terminal_positive hp ha haT hcontact hpast hx hpx
    (fun _ ht => canonicalStraightDifference_positive_interval hk hh hhk hc hd ht)

theorem zeroDividend_canonicalStraightDifference_positive_interval {k c d t : ℝ}
    (hk : 0 < k) (hc : 0 < c) (hd : d ≤ 0) (ht : 0 < t) :
    OrdConnected {x | canonicalLogBoundary k 0 t < x ∧
      0 < straightDifference (canonicalPrice k 0) k 0 c d x t} :=
  canonicalStraightDifference_positive_interval hk le_rfl hk.le hc hd ht

theorem liuRange_canonicalStraightDifference_positive_interval {k h c d t : ℝ}
    (hh : 0 ≤ h) (hliu : h + 1 ≤ k) (hc : 0 < c) (hd : d ≤ 0) (ht : 0 < t) :
    OrdConnected {x | canonicalLogBoundary k h t < x ∧
      0 < straightDifference (canonicalPrice k h) k h c d x t} :=
  canonicalStraightDifference_positive_interval (by linarith) hh (by linarith) hc hd ht

/-- The actual boundary's strict sublevel set below each admissible line is
an interval in time. This is a derivative-free consequence of the spatial
comparison invariant and the terminal Hopf argument. -/
theorem canonicalLogBoundary_below_line_time_interval {k h c d : ℝ}
    (hk : 0 < k) (hh : 0 ≤ h) (hhk : h ≤ k) (hc : 0 < c) (hd : d ≤ 0) :
    OrdConnected {t | 0 < t ∧ canonicalLogBoundary k h t < d-c*t} := by
  rw [ordConnected_iff]
  intro a ha U hU _ m hm
  refine ⟨ha.1.trans_le hm.1,?_⟩
  by_contra! hn
  let f : ℝ → ℝ := fun t => canonicalLogBoundary k h t-(d-c*t)
  have hf : ContinuousOn f (Icc a m) :=
    ((canonicalLogBoundary_continuousOn hk hh hhk).mono
      (fun t ht => ha.1.le.trans ht.1)).sub (by fun_prop)
  obtain ⟨T,haT,hTm,hzero,hpast⟩ := exists_first_nonnegative_contact hm.1 hf
    (show f a < 0 from sub_neg.mpr ha.2) (show 0 ≤ f m from sub_nonneg.mpr hn)
  have hmU : m < U := lt_of_le_of_ne hm.2 (by
    intro he
    rw [he] at hn
    exact not_le_of_gt hU.2 hn)
  apply canonicalLogBoundary_no_return_contact hk hh hhk hc hd ha.1 haT (hTm.trans_lt hmU)
    (sub_eq_zero.mp hzero) ?_ hU.2
  intro t ht
  exact sub_neg.mp (hpast t ht)

theorem zeroDividend_canonicalLogBoundary_below_line_time_interval {k c d : ℝ}
    (hk : 0 < k) (hc : 0 < c) (hd : d ≤ 0) :
    OrdConnected {t | 0 < t ∧ canonicalLogBoundary k 0 t < d-c*t} :=
  canonicalLogBoundary_below_line_time_interval hk le_rfl hk.le hc hd

theorem liuRange_canonicalLogBoundary_below_line_time_interval {k h c d : ℝ}
    (hh : 0 ≤ h) (hliu : h + 1 ≤ k) (hc : 0 < c) (hd : d ≤ 0) :
    OrdConnected {t | 0 < t ∧ canonicalLogBoundary k h t < d-c*t} :=
  canonicalLogBoundary_below_line_time_interval (by linarith) hh (by linarith) hc hd

end MathFin.BlackScholes.AmericanPut.Stopping
