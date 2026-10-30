/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.Tangency
public import MathFin.BlackScholes.AmericanPut.Boundary.TangentIntercept
public import MathFin.BlackScholes.AmericanPut.Boundary.NearExpiry
public import MathFin.BlackScholes.AmericanPut.Boundary.BoundaryMonotonicity

/-!
# Conditional assembly of the straight-line comparison proof

These modular implications retain explicit interval and speed arguments.
`ComparisonConclusion` supplies the interval invariant for weak log curvature;
`StrictBoundarySpeed` and `StockConclusion` then discharge the strict-speed
argument for strict stock curvature. The actual stopping-value identification
is separate from these classical-contract results.

## Result

Public entry points include `dividend_curvature_of_comparison_inputs`, `stock_curvature_of_comparison_inputs`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary.Comparison

open Set Filter
open scoped Topology

/-- The proposed log-curvature conclusion, conditional only on the
interval invariant. In particular this invariant is not claimed as a
consequence of an unformalized zero-number theorem. -/
theorem dividend_curvature_of_comparison_inputs {k h : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} (hp : DividendPutSolution k h p b)
    (hinterval : ∀ c d : ℝ, 0 < c → d < 0 → ∀ t, 0 < t →
      OrdConnected {x | b t < x ∧ 0 < straightDifference p k h c d x t}) :
    ∀ t, 0 < t → 0 ≤ deriv (deriv b) t := by
  apply curvature_nonneg_of_negative_intercepts hp.boundary_smooth hp.boundary_ratio_tendsto_atBot
  intro t ht hd
  by_contra hn
  have hspeed := hp.boundary_deriv_neg_of_curvature_neg ht (lt_of_not_ge hn)
  exact hn (curvature_nonneg_of_tangent_intervals hp ht hspeed hd.le
    (hinterval (-deriv b t) (b t - t * deriv b t) (neg_pos.mpr hspeed) hd))

/-- The requested STRICT stock-boundary curvature consequence of the same
conditional proof. `stockBoundary` uses the existing calendar-time convention;
time reversal does not change the second-derivative sign. This is still not
an identification with a continuous-time optimal-stopping value. -/
theorem stock_curvature_of_comparison_inputs {k h : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} (hp : DividendPutSolution k h p b)
    (hspeed : ∀ t, 0 < t → deriv b t < 0)
    (hinterval : ∀ c d : ℝ, 0 < c → d < 0 → ∀ t, 0 < t →
      OrdConnected {x | b t < x ∧ 0 < straightDifference p k h c d x t})
    {E σ expiry T : ℝ} (hE : 0 < E) (hσ : 0 < σ) (hT : T < expiry) :
    0 < deriv (deriv (stockBoundary E σ expiry b)) T := by
  have ht := normalizedTime_pos hσ hT
  have hs : ContDiffAt ℝ 2 b (normalizedTime σ expiry T) :=
    (hp.boundary_smooth.contDiffAt (Ioi_mem_nhds ht)).of_le (WithTop.coe_le_coe.mpr le_top)
  apply deriv2_stockBoundary_pos_of_nonneg hE hσ hT
    (fun t ht =>
        ((hp.boundary_smooth.contDiffAt (Ioi_mem_nhds ht)).differentiableAt (by simp)).hasDerivAt)
    (((hs.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt)
    (dividend_curvature_of_comparison_inputs hp hinterval _ ht)
  exact (hspeed _ ht).ne

end MathFin.BlackScholes.AmericanPut.Boundary.Comparison
