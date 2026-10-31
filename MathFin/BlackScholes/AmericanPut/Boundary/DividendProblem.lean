/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.ContinuousBoundaryProblem

/-!
# The classical put contract and its zero-dividend case

`DividendPutSolution k h p b` is `ContinuousBoundaryPutSolution k h p b` together with
smoothness of the boundary at positive times: the classical solution contract for the
proposed theorem. No boundary monotonicity, curvature, zero-count invariant, or comparison
principle is assumed. Existence remains an obligation; stochastic identification from this
contract is proved in `Stopping/ClassicalSupermartingale` and `Stopping/UsualBrownianValue`.

The CCJZ zero-dividend contract `NormalizedPutSolution k p b` is by definition the case
`h = 0`, so every result proved for `DividendPutSolution` applies to it as stated.

## Result

Public entry points include `DividendPutSolution`, `NormalizedPutSolution`,
`normalized_dividend_regime`, `liu_condition_normalization`, `DividendCurvatureClaim`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set
open scoped ContDiff

theorem normalized_dividend_regime {r q σ : ℝ}
    (hr : 0 < r) (hq : 0 ≤ q) (hqr : q ≤ r) (hσ : 0 < σ) :
    0 < normalizedRate r σ ∧ 0 ≤ normalizedRate q σ ∧
      normalizedRate q σ ≤ normalizedRate r σ := by
  refine ⟨normalizedRate_pos hr hσ, ?_, ?_⟩
  · unfold normalizedRate
    positivity
  · unfold normalizedRate
    gcongr

/-- Liu's physical restriction is exactly `h+1 ≤ k` after normalization. -/
theorem liu_condition_normalization {r q σ : ℝ} (hσ : 0 < σ) :
    normalizedRate q σ + 1 ≤ normalizedRate r σ ↔ q + σ ^ 2 / 2 ≤ r := by
  have hs : 0 < σ ^ 2 := sq_pos_of_pos hσ
  unfold normalizedRate
  rw [← div_self hs.ne', ← add_div, div_le_div_iff_of_pos_right hs]
  constructor <;> intro h <;> nlinarith

/-- Classical normalized put solution in the regime `0 ≤ h ≤ k`, `0 < k`: the
continuous-boundary contract with a boundary smooth at positive times.
Pairs are `(log spot, time remaining)`. Boundary derivatives are one-sided. -/
structure DividendPutSolution (k h : ℝ) (p : ℝ → ℝ → ℝ) (b : ℝ → ℝ) : Prop
    extends ContinuousBoundaryPutSolution k h p b where
  boundary_smooth : ContDiffOn ℝ ∞ b (Ioi 0)

instance {k h : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} :
    Coe (DividendPutSolution k h p b) (ContinuousBoundaryPutSolution k h p b) :=
  ⟨DividendPutSolution.toContinuousBoundaryPutSolution⟩

/-- The CCJZ (2008), (1.1) zero-dividend contract, with the stopping-region extension and
initial payoff on all log prices: the case `h = 0` of `DividendPutSolution`. The smoothness
requirements describe the intended classical solution class. The actual stopping price is proved
to satisfy the `ContinuousBoundaryPutSolution` part (`canonicalPrice_continuousBoundaryPutSolution`);
smoothness of its boundary (`boundary_smooth`) is the remaining separate obligation. -/
abbrev NormalizedPutSolution (k : ℝ) (p : ℝ → ℝ → ℝ) (b : ℝ → ℝ) : Prop :=
  DividendPutSolution k 0 p b

namespace DividendPutSolution

variable {k h : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}

/-- Regularity supplies actual derivatives, avoiding Lean's default derivative
value for a nondifferentiable function. -/
theorem boundary_hasDerivAt (hp : DividendPutSolution k h p b) {t : ℝ} (ht : 0 < t) :
    HasDerivAt b (deriv b t) t :=
  ((hp.boundary_smooth.contDiffAt (isOpen_Ioi.mem_nhds ht)).differentiableAt
    (by simp)).hasDerivAt

theorem boundary_hasDerivAt_deriv (hp : DividendPutSolution k h p b)
    {t : ℝ} (ht : 0 < t) : HasDerivAt (deriv b) (deriv (deriv b) t) t := by
  have hs : ContDiffOn ℝ ∞ (deriv b) (Ioi 0) :=
    hp.boundary_smooth.deriv_of_isOpen isOpen_Ioi (by simp)
  exact ((hs.contDiffAt (isOpen_Ioi.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt

/-- The remaining analytic curvature input suffices for the stock boundary.
This is a reduction lemma, not a proof of that input. -/
theorem stock_curvature_of_log_curvature (hp : DividendPutSolution k h p b)
    {E σ expiry T : ℝ} (hE : 0 < E) (hσ : 0 < σ) (hT : T < expiry)
    (hcurvature : 0 < deriv (deriv b) (normalizedTime σ expiry T)) :
    0 < deriv (deriv (stockBoundary E σ expiry b)) T :=
  deriv2_stockBoundary_pos hE hσ hT (fun _ ht => hp.boundary_hasDerivAt ht)
    (hp.boundary_hasDerivAt_deriv (normalizedTime_pos hσ hT)) hcurvature

end DividendPutSolution

/-- OPEN analytic goal (CCJZ's strict log curvature), deliberately a proposition
definition and not a theorem. Existence and stochastic identification must additionally
be proved. -/
def NormalizedCurvatureClaim : Prop :=
  ∀ (k : ℝ) (p : ℝ → ℝ → ℝ) (b : ℝ → ℝ),
    NormalizedPutSolution k p b → ∀ t, 0 < t → 0 < deriv (deriv b) t

/-- OPEN non-vacuity obligation, separate from the conditional curvature claim. -/
def NormalizedExistenceClaim : Prop :=
  ∀ k : ℝ, 0 < k → ∃ p b, NormalizedPutSolution k p b

/-- Classical-solution target, proved in `ComparisonConclusion.lean`.
This definition alone is not a proof or an identification with a stopping value. -/
def DividendCurvatureClaim : Prop :=
  ∀ (k h : ℝ) (p : ℝ → ℝ → ℝ) (b : ℝ → ℝ),
    DividendPutSolution k h p b → ∀ t, 0 < t → 0 ≤ deriv (deriv b) t

/-- Zero-dividend milestone, proved in `ComparisonConclusion.lean`. The published CCJZ
target `NormalizedCurvatureClaim` is stronger: it requires STRICT positivity. -/
def ZeroDividendWeakCurvatureClaim : Prop :=
  ∀ (k : ℝ) (p : ℝ → ℝ → ℝ) (b : ℝ → ℝ),
    NormalizedPutSolution k p b → ∀ t, 0 < t → 0 ≤ deriv (deriv b) t

/-- Specialization to Liu's parameter range, proved in `ComparisonConclusion.lean`,
retaining the proposed weak logarithmic-curvature conclusion. -/
def LiuRangeCurvatureClaim : Prop :=
  ∀ (k h : ℝ) (p : ℝ → ℝ → ℝ) (b : ℝ → ℝ),
    DividendPutSolution k h p b → h + 1 ≤ k →
      ∀ t, 0 < t → 0 ≤ deriv (deriv b) t

/-- A reduction between the claims. Their proofs are supplied separately in
`ComparisonConclusion.lean`. -/
theorem dividendCurvature_specializations (hmain : DividendCurvatureClaim) :
    ZeroDividendWeakCurvatureClaim ∧ LiuRangeCurvatureClaim :=
  ⟨fun k p b hb => hmain k 0 p b hb, fun k h p b hb _ => hmain k h p b hb⟩

/-- The published strict theorem would imply the weak zero-dividend milestone.
The strict hypothesis remains open; the weak claim is now proved by the
alternative comparison route in `ComparisonConclusion.lean`. -/
theorem publishedCurvature_implies_weak (hccjz : NormalizedCurvatureClaim) :
    ZeroDividendWeakCurvatureClaim :=
  fun k p b hb t ht => (hccjz k p b hb t ht).le

end MathFin.BlackScholes.AmericanPut.Boundary
