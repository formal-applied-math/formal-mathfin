/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.TimeMonotonicity

/-!
# Boundary monotonicity and speed at a hypothetical concave point

Price time-monotonicity forces the exercise boundary to be nonincreasing.
This yields a nonpositive derivative. If its second derivative were negative
at an interior time, its first derivative could not be zero there, because
that would be a local maximum of a nonpositive derivative.

This last observation is sufficient for the log-curvature contradiction. It
does not assert a strictly negative boundary speed at every positive time.

## Result

Public entry points include `boundary_antitoneOn`, `boundary_deriv_nonpos`,
`boundary_deriv_neg_of_curvature_neg`, `price_mono_time`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set Filter
open scoped Topology

namespace DividendPutSolution

variable {k h : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}

theorem boundary_antitoneOn (hp : DividendPutSolution k h p b) : AntitoneOn b (Ici 0) := by
  intro s hs t ht hst
  change 0 ≤ s at hs
  change 0 ≤ t at ht
  rcases eq_or_lt_of_le hs with he | hspos
  · rw [← he,hp.boundary_initial]
    rcases eq_or_lt_of_le ht with ht0 | htpos
    · simp [← ht0,hp.boundary_initial]
    · exact hp.boundary_nonpos htpos
  · have htpos : 0 < t := hspos.trans_le hst
    by_contra hn
    have hboundary : b s < b t := lt_of_not_ge hn
    have hcontinue := hp.continuation (b t) s hspos hboundary
    have hprice := hp.price_mono_time (b t) hspos.le hst
    rw [hp.exercise (b t) t htpos le_rfl] at hprice
    have hpayoff : 1-Real.exp (b t) ≤ putPayoff (b t) := le_max_left _ _
    linarith

theorem boundary_deriv_nonpos (hp : DividendPutSolution k h p b) {t : ℝ} (ht : 0 < t) :
    deriv b t ≤ 0 := by
  have hh := hp.boundary_antitoneOn.derivWithin_nonpos (x := t)
  rwa [derivWithin_of_mem_nhds (Ici_mem_nhds ht)] at hh

/-- At any hypothetical negative-curvature point the speed is strictly
negative. Thus the curvature contradiction does not need strict speed as an
independent global assumption. -/
theorem boundary_deriv_neg_of_curvature_neg (hp : DividendPutSolution k h p b)
    {t : ℝ} (ht : 0 < t) (hcurv : deriv (deriv b) t < 0) : deriv b t < 0 := by
  apply lt_of_le_of_ne (hp.boundary_deriv_nonpos ht)
  intro he
  have hm : IsLocalMax (deriv b) t := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    rw [he]
    exact hp.boundary_deriv_nonpos hs
  have hz := hm.deriv_eq_zero
  linarith

end DividendPutSolution

end MathFin.BlackScholes.AmericanPut.Boundary
