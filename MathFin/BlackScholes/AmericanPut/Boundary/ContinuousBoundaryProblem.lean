/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.Problem

/-! # The classical put contract with a continuous exercise boundary

`ContinuousBoundaryPutSolution k h p b` is the classical normalized put solution in the
regime `0 ≤ h ≤ k`, `0 < k`, asking of the boundary only that it be continuous. It is a
solution predicate, not an existence or stochastic verification theorem, and no
monotonicity, convexity or curvature is among its assumptions. Interior derivatives are
ordinary derivatives; at the moving boundary, smooth fit is a right derivative and a right
trace, so no second derivative of the payoff-extended price across the boundary is
required, and no smoothness at expiry is imposed. `DividendPutSolution` adds smoothness of
the boundary; the straight comparison, maximum principle and terminal Hopf arguments use
the present data directly.

The facts here follow from the contract alone: the boundary lies below the strike, the
contact set before expiry is the half-line below the boundary (so the boundary of a given
price is unique), and the price is smooth near each continuation point.

## Result

Public entry points include `ContinuousBoundaryPutSolution`, `boundary_nonpos`,
`contact_iff`, `contact_in_stock_units`, `boundary_unique`, `price_contDiffAt`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set Filter
open scoped Topology ContDiff

/-- Classical normalized put solution in the regime `0 ≤ h ≤ k`, `0 < k`, with a continuous
boundary `b`. Pairs are `(log spot, time remaining)`; boundary derivatives are one-sided. -/
structure ContinuousBoundaryPutSolution (k h : ℝ) (p : ℝ → ℝ → ℝ) (b : ℝ → ℝ) : Prop where
  rate_pos : 0 < k
  dividend_nonneg : 0 ≤ h
  dividend_le_rate : h ≤ k
  boundary_initial : b 0 = 0
  boundary_continuous : ContinuousOn b (Ici 0)
  price_continuous : ContinuousOn (fun z : ℝ × ℝ => p z.1 z.2) {z | 0 ≤ z.2}
  price_smooth : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => p z.1 z.2) (continuationRegion b)
  initial : ∀ x, p x 0 = putPayoff x
  dominates : ∀ x t, 0 ≤ t → putPayoff x ≤ p x t
  bounded : ∀ x t, 0 ≤ t → p x t ≤ 1
  exercise : ∀ x t, 0 < t → x ≤ b t → p x t = 1 - Real.exp x
  continuation : ∀ x t, 0 < t → b t < x → putPayoff x < p x t
  equation : ∀ x t, 0 < t → b t < x →
    deriv (p x) t = dividendSpatialOperator k h (fun y => p y t) x
  smooth_fit : ∀ t, 0 < t → HasDerivWithinAt (fun x => p x t)
    (-Real.exp (b t)) (Ici (b t)) (b t)
  gradient_trace : ∀ t, 0 < t → Tendsto (fun x => deriv (fun y => p y t) x)
    (𝓝[>] (b t)) (𝓝 (-Real.exp (b t)))
  decay : ∀ t, 0 ≤ t → Tendsto (fun x => p x t) atTop (𝓝 0)

namespace ContinuousBoundaryPutSolution

variable {k h : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}

/-- The contact condition and nonnegative value force the threshold below strike. -/
theorem boundary_nonpos (hp : ContinuousBoundaryPutSolution k h p b) {t : ℝ} (ht : 0 < t) :
    b t ≤ 0 := by
  have hv := (putPayoff_nonneg (b t)).trans (hp.dominates (b t) t ht.le)
  rw [hp.exercise (b t) t ht le_rfl] at hv
  exact Real.exp_le_one_iff.mp (by linarith)

/-- Before expiry the contact set is exactly the lower half-line. -/
theorem contact_iff (hp : ContinuousBoundaryPutSolution k h p b) {x t : ℝ} (ht : 0 < t) :
    p x t = putPayoff x ↔ x ≤ b t := by
  refine ⟨fun he => le_of_not_gt fun hx => (hp.continuation x t ht hx).ne' he, fun hx => ?_⟩
  rw [hp.exercise x t ht hx, putPayoff_of_nonpos (hx.trans (hp.boundary_nonpos ht))]

/-- In particular, the boundary is recoverable from the value function. -/
theorem contactSet (hp : ContinuousBoundaryPutSolution k h p b) {t : ℝ} (ht : 0 < t) :
    {x | p x t = putPayoff x} = Iic (b t) :=
  Set.ext fun _ => hp.contact_iff ht

theorem boundary_eq_sSup_contact (hp : ContinuousBoundaryPutSolution k h p b)
    {t : ℝ} (ht : 0 < t) : b t = sSup {x | p x t = putPayoff x} := by
  rw [hp.contactSet ht, csSup_Iic]

/-- Uniqueness of the threshold for a FIXED price, not PDE uniqueness. -/
theorem boundary_unique (hp : ContinuousBoundaryPutSolution k h p b) {r : ℝ → ℝ}
    (hr : ContinuousBoundaryPutSolution k h p r) {t : ℝ} (ht : 0 ≤ t) : b t = r t := by
  rcases ht.eq_or_lt with ht | ht
  · subst t
    rw [hp.boundary_initial, hr.boundary_initial]
  · rw [hp.boundary_eq_sSup_contact ht, hr.boundary_eq_sSup_contact ht]

/-- At expiry the contact set is all of log-price space, unlike positive times. -/
theorem contactSet_expiry (hp : ContinuousBoundaryPutSolution k h p b) :
    {x | p x 0 = putPayoff x} = univ := by
  ext x
  simp [hp.initial]

/-- The reconstructed boundary is positive and does not exceed strike. -/
theorem stockBoundary_bounds (hp : ContinuousBoundaryPutSolution k h p b)
    {E σ expiry T : ℝ} (hE : 0 < E) (hσ : 0 < σ) (hT : T < expiry) :
    0 < stockBoundary E σ expiry b T ∧ stockBoundary E σ expiry b T ≤ E := by
  constructor
  · exact mul_pos hE (Real.exp_pos _)
  · have hs := hp.boundary_nonpos (normalizedTime_pos hσ hT)
    simpa [stockBoundary] using
      mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr hs) hE.le

/-- Price/payoff coincidence expressed in the original positive stock variable. -/
theorem contact_in_stock_units (hp : ContinuousBoundaryPutSolution k h p b)
    {K S t : ℝ} (hK : 0 < K) (hS : 0 < S) (ht : 0 < t) :
    K * p (Real.log (S / K)) t = max (K - S) 0 ↔ S ≤ K * Real.exp (b t) := by
  rw [← putPayoff_in_stock_units hK hS, mul_right_inj' hK.ne', hp.contact_iff ht,
    ← Real.exp_le_exp, Real.exp_log (div_pos hS hK), div_le_iff₀ hK, mul_comm K]

/-- Interior smoothness at a space-time point follows from the moving-domain
contract and continuity of the boundary; no smoothness across it is assumed. -/
theorem price_contDiffAt (hp : ContinuousBoundaryPutSolution k h p b)
    {x t : ℝ} (ht : 0 < t) (hx : b t < x) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => p z.1 z.2) (x, t) := by
  have hb : ContinuousAt b t := hp.boundary_continuous.continuousAt (Ici_mem_nhds ht)
  have hbt : ContinuousAt (fun z : ℝ × ℝ => b z.2) (x, t) := hb.comp continuousAt_snd
  have ht' : ∀ᶠ z : ℝ × ℝ in 𝓝 (x, t), 0 < z.2 :=
    continuousAt_const.eventually_lt continuousAt_snd ht
  have hx' : ∀ᶠ z : ℝ × ℝ in 𝓝 (x, t), b z.2 < z.1 :=
    hbt.eventually_lt continuousAt_fst hx
  exact hp.price_smooth.contDiffAt (ht'.and hx')

end ContinuousBoundaryPutSolution

end MathFin.BlackScholes.AmericanPut.Boundary
