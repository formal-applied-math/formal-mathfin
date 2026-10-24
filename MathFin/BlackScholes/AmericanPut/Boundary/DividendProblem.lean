/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.Problem

/-!
# The dividend extension and its zero-dividend consistency check

This is the classical solution contract for the proposed theorem. No boundary
monotonicity, curvature, zero-count invariant, or comparison principle is assumed.
Existence remains an obligation; stochastic identification from this contract
is proved in `Stopping/ClassicalSupermartingale` and `Stopping/UsualBrownianValue`.
At zero dividends the contract is equivalent to the existing CCJZ contract.

## Result

Public entry points include `dividendSpatialOperator`, `normalized_dividend_regime`,
`liu_condition_normalization`, `DividendPutSolution`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Filter
open scoped Topology ContDiff

/-- The spatial Black--Scholes operator with dividends: `f'' + (k - h - 1) * f' - k * f`. -/
noncomputable def dividendSpatialOperator (k h : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv f) x + (k - h - 1) * deriv f x - k * f x

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

@[simp] theorem dividendSpatialOperator_zero (k : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    dividendSpatialOperator k 0 f x = spatialOperator k f x := by
  simp [dividendSpatialOperator, spatialOperator]

/-- Classical normalized put solution in the regime `0 ≤ h ≤ k`, `0 < k`.
Pairs are `(log spot, time remaining)`. Boundary derivatives are one-sided. -/
structure DividendPutSolution (k h : ℝ) (p : ℝ → ℝ → ℝ) (b : ℝ → ℝ) : Prop where
  rate_pos : 0 < k
  dividend_nonneg : 0 ≤ h
  dividend_le_rate : h ≤ k
  boundary_initial : b 0 = 0
  boundary_continuous : ContinuousOn b (Set.Ici 0)
  boundary_smooth : ContDiffOn ℝ ∞ b (Set.Ioi 0)
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
    (-Real.exp (b t)) (Set.Ici (b t)) (b t)
  gradient_trace : ∀ t, 0 < t →
    Tendsto (fun x => deriv (fun y => p y t) x)
      (nhdsWithin (b t) (Set.Ioi (b t))) (nhds (-Real.exp (b t)))
  decay : ∀ t, 0 ≤ t → Tendsto (fun x => p x t) atTop (nhds 0)

namespace DividendPutSolution

variable {k h : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}

theorem boundary_nonpos (hp : DividendPutSolution k h p b) {t : ℝ} (ht : 0 < t) :
    b t ≤ 0 := by
  have hv := (putPayoff_nonneg (b t)).trans (hp.dominates (b t) t ht.le)
  rw [hp.exercise (b t) t ht le_rfl] at hv
  exact Real.exp_le_one_iff.mp (by linarith)

/-- Interior smoothness at a space-time point follows from the moving-domain
contract and continuity of the boundary; no smoothness across it is assumed. -/
theorem price_contDiffAt (hp : DividendPutSolution k h p b)
    {x t : ℝ} (ht : 0 < t) (hx : b t < x) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => p z.1 z.2) (x, t) := by
  have hb : ContinuousAt b t := hp.boundary_continuous.continuousAt (Ici_mem_nhds ht)
  have hbt : ContinuousAt (fun z : ℝ × ℝ => b z.2) (x, t) := hb.comp continuousAt_snd
  have ht' : ∀ᶠ z : ℝ × ℝ in nhds (x, t), 0 < z.2 :=
    continuousAt_const.eventually_lt continuousAt_snd ht
  have hx' : ∀ᶠ z : ℝ × ℝ in nhds (x, t), b z.2 < z.1 :=
    hbt.eventually_lt continuousAt_fst hx
  apply hp.price_smooth.contDiffAt
  exact ht'.and hx'

end DividendPutSolution

/-- No changed model is hidden in the zero-dividend specialization. -/
theorem dividendPutSolution_zero_iff {k : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} :
    DividendPutSolution k 0 p b ↔ NormalizedPutSolution k p b := by
  constructor
  · intro h
    exact {
      rate_pos := h.rate_pos
      boundary_initial := h.boundary_initial
      boundary_continuous := h.boundary_continuous
      boundary_smooth := h.boundary_smooth
      price_continuous := h.price_continuous
      price_smooth := h.price_smooth
      initial := h.initial
      dominates := h.dominates
      bounded := h.bounded
      exercise := h.exercise
      continuation := h.continuation
      equation := fun x t ht hx => by simpa using h.equation x t ht hx
      smooth_fit := h.smooth_fit
      gradient_trace := h.gradient_trace
      decay := h.decay }
  · intro h
    exact {
      rate_pos := h.rate_pos
      dividend_nonneg := le_rfl
      dividend_le_rate := h.rate_pos.le
      boundary_initial := h.boundary_initial
      boundary_continuous := h.boundary_continuous
      boundary_smooth := h.boundary_smooth
      price_continuous := h.price_continuous
      price_smooth := h.price_smooth
      initial := h.initial
      dominates := h.dominates
      bounded := h.bounded
      exercise := h.exercise
      continuation := h.continuation
      equation := fun x t ht hx => by simpa using h.equation x t ht hx
      smooth_fit := h.smooth_fit
      gradient_trace := h.gradient_trace
      decay := h.decay }

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
    ZeroDividendWeakCurvatureClaim ∧ LiuRangeCurvatureClaim := by
  constructor
  · intro k p b hb t ht
    exact hmain k 0 p b (dividendPutSolution_zero_iff.mpr hb) t ht
  · intro k h p b hb _ t ht
    exact hmain k h p b hb t ht

/-- The published strict theorem would imply the weak zero-dividend milestone.
The strict hypothesis remains open; the weak claim is now proved by the
alternative comparison route in `ComparisonConclusion.lean`. -/
theorem publishedCurvature_implies_weak (hccjz : NormalizedCurvatureClaim) :
    ZeroDividendWeakCurvatureClaim := by
  intro k p b hb t ht
  exact (hccjz k p b hb t ht).le

end MathFin.BlackScholes.AmericanPut.Boundary
