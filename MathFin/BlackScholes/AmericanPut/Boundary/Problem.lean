/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.Coordinates

/-!
# A classical normalized American-put problem

CCJZ (2008), (1.1), with the stopping-region extension and initial payoff on
ALL log prices. Arguments are always `(x, t)`, with `t` time remaining.
This is a solution predicate, not an existence or stochastic verification theorem.
No monotonicity, convexity, or curvature is included among its assumptions.

Interior derivatives are ordinary derivatives. At the moving boundary, smooth
fit is a right derivative and a right trace; no second derivative of the
payoff-extended price across the boundary is required. No smoothness at expiry
is imposed. The global-in-time formulation can be restricted to any maturity.

## Result

Public entry points include `normalizedRate`, `normalizedRate_pos`, `putPayoff`,
`continuationRegion`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Filter
open scoped Topology ContDiff

/-- Positive-rate, zero-dividend Black--Scholes normalization. -/
noncomputable def normalizedRate (r σ : ℝ) : ℝ := 2 * r / σ ^ 2

theorem normalizedRate_pos {r σ : ℝ} (hr : 0 < r) (hσ : 0 < σ) :
    0 < normalizedRate r σ := by
  unfold normalizedRate
  positivity

/-- Strike-normalized put payoff in log spot. -/
noncomputable def putPayoff (x : ℝ) : ℝ := max (1 - Real.exp x) 0

/-- Open continuation region; pairs are `(log spot, time remaining)`. -/
def continuationRegion (s : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {z | 0 < z.2 ∧ s z.2 < z.1}

/-- The spatial Black--Scholes operator after normalization. -/
noncomputable def spatialOperator (k : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv f) x + (k - 1) * deriv f x - k * f x

/-- Analytic characterization to be connected to the GBM stopping value.
The smoothness requirements describe the intended classical solution class;
proving that the financial value belongs to it is a separate obligation. -/
structure NormalizedPutSolution (k : ℝ) (p : ℝ → ℝ → ℝ) (s : ℝ → ℝ) : Prop where
  rate_pos : 0 < k
  boundary_initial : s 0 = 0
  boundary_continuous : ContinuousOn s (Set.Ici 0)
  boundary_smooth : ContDiffOn ℝ ∞ s (Set.Ioi 0)
  price_continuous : ContinuousOn (fun z : ℝ × ℝ => p z.1 z.2) {z | 0 ≤ z.2}
  price_smooth : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => p z.1 z.2) (continuationRegion s)
  initial : ∀ x, p x 0 = putPayoff x
  dominates : ∀ x t, 0 ≤ t → putPayoff x ≤ p x t
  bounded : ∀ x t, 0 ≤ t → p x t ≤ 1
  exercise : ∀ x t, 0 < t → x ≤ s t → p x t = 1 - Real.exp x
  continuation : ∀ x t, 0 < t → s t < x → putPayoff x < p x t
  equation : ∀ x t, 0 < t → s t < x →
    deriv (p x) t = spatialOperator k (fun y => p y t) x
  smooth_fit : ∀ t, 0 < t → HasDerivWithinAt (fun x => p x t)
    (-Real.exp (s t)) (Set.Ici (s t)) (s t)
  gradient_trace : ∀ t, 0 < t →
    Tendsto (fun x => deriv (fun y => p y t) x)
      (nhdsWithin (s t) (Set.Ioi (s t))) (nhds (-Real.exp (s t)))
  decay : ∀ t, 0 ≤ t → Tendsto (fun x => p x t) atTop (nhds 0)

theorem putPayoff_nonneg (x : ℝ) : 0 ≤ putPayoff x := le_max_right _ _

theorem putPayoff_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    putPayoff x = 1 - Real.exp x := by
  exact max_eq_left (sub_nonneg.mpr (Real.exp_le_one_iff.mpr hx))

/-- The normalized payoff is exactly the usual monetary put payoff. -/
theorem putPayoff_in_stock_units {E S : ℝ} (hE : 0 < E) (hS : 0 < S) :
    E * putPayoff (Real.log (S / E)) = max (E - S) 0 := by
  unfold putPayoff
  rw [Real.exp_log (div_pos hS hE), mul_max_of_nonneg _ _ hE.le]
  congr 1
  · field_simp
  · ring

namespace NormalizedPutSolution

variable {k : ℝ} {p : ℝ → ℝ → ℝ} {s : ℝ → ℝ}

/-- The contact condition and nonnegative value force the threshold below strike. -/
theorem boundary_nonpos (h : NormalizedPutSolution k p s) {t : ℝ} (ht : 0 < t) :
    s t ≤ 0 := by
  have hp := (putPayoff_nonneg (s t)).trans (h.dominates (s t) t ht.le)
  rw [h.exercise (s t) t ht le_rfl] at hp
  exact Real.exp_le_one_iff.mp (by linarith)

/-- Before expiry the contact set is exactly the lower half-line. -/
theorem contact_iff (h : NormalizedPutSolution k p s) {x t : ℝ} (ht : 0 < t) :
    p x t = putPayoff x ↔ x ≤ s t := by
  constructor
  · intro heq
    by_contra hx
    have hlt := h.continuation x t ht (lt_of_not_ge hx)
    rw [heq] at hlt
    exact (lt_irrefl _ hlt)
  · intro hx
    rw [h.exercise x t ht hx, putPayoff_of_nonpos (hx.trans (h.boundary_nonpos ht))]

/-- In particular, the boundary is recoverable from the value function. -/
theorem contactSet (h : NormalizedPutSolution k p s) {t : ℝ} (ht : 0 < t) :
    {x | p x t = putPayoff x} = Set.Iic (s t) := by
  ext x
  exact h.contact_iff ht

theorem boundary_eq_sSup_contact (h : NormalizedPutSolution k p s)
    {t : ℝ} (ht : 0 < t) : s t = sSup {x | p x t = putPayoff x} := by
  rw [h.contactSet ht, csSup_Iic]

/-- Uniqueness of the threshold for a FIXED price, not PDE uniqueness. -/
theorem boundary_unique (h : NormalizedPutSolution k p s) {r : ℝ → ℝ}
    (hr : NormalizedPutSolution k p r) {t : ℝ} (ht : 0 ≤ t) : s t = r t := by
  rcases ht.eq_or_lt with ht | ht
  · subst t
    rw [h.boundary_initial, hr.boundary_initial]
  · rw [h.boundary_eq_sSup_contact ht, hr.boundary_eq_sSup_contact ht]

/-- At expiry the contact set is all of log-price space, unlike positive times. -/
theorem contactSet_expiry (h : NormalizedPutSolution k p s) :
    {x | p x 0 = putPayoff x} = Set.univ := by
  ext x
  simp [h.initial]

/-- The reconstructed boundary is positive and does not exceed strike. -/
theorem stockBoundary_bounds (h : NormalizedPutSolution k p s)
    {E σ expiry T : ℝ} (hE : 0 < E) (hσ : 0 < σ) (hT : T < expiry) :
    0 < stockBoundary E σ expiry s T ∧ stockBoundary E σ expiry s T ≤ E := by
  constructor
  · exact mul_pos hE (Real.exp_pos _)
  · have hs := h.boundary_nonpos (normalizedTime_pos hσ hT)
    simpa [stockBoundary] using
      mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr hs) hE.le

/-- Price/payoff coincidence expressed in the original positive stock variable. -/
theorem contact_in_stock_units (h : NormalizedPutSolution k p s)
    {E S t : ℝ} (hE : 0 < E) (hS : 0 < S) (ht : 0 < t) :
    E * p (Real.log (S / E)) t = max (E - S) 0 ↔ S ≤ E * Real.exp (s t) := by
  rw [← putPayoff_in_stock_units hE hS, mul_right_inj' hE.ne', h.contact_iff ht]
  rw [← Real.exp_le_exp, Real.exp_log (div_pos hS hE), div_le_iff₀ hE]
  rw [mul_comm E]

/-- Regularity supplies actual derivatives, avoiding Lean's default derivative
value for a nondifferentiable function. -/
theorem boundary_hasDerivAt (h : NormalizedPutSolution k p s) {t : ℝ} (ht : 0 < t) :
    HasDerivAt s (deriv s t) t :=
  ((h.boundary_smooth.contDiffAt (isOpen_Ioi.mem_nhds ht)).differentiableAt
    (by simp)).hasDerivAt

theorem boundary_hasDerivAt_deriv (h : NormalizedPutSolution k p s)
    {t : ℝ} (ht : 0 < t) : HasDerivAt (deriv s) (deriv (deriv s) t) t := by
  have hs : ContDiffOn ℝ ∞ (deriv s) (Set.Ioi 0) :=
    h.boundary_smooth.deriv_of_isOpen isOpen_Ioi (by simp)
  exact ((hs.contDiffAt (isOpen_Ioi.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt

/-- The remaining analytic curvature input suffices for the stock boundary.
This is a reduction lemma, not a proof of that input. -/
theorem stock_curvature_of_log_curvature (h : NormalizedPutSolution k p s)
    {E σ expiry T : ℝ} (hE : 0 < E) (hσ : 0 < σ) (hT : T < expiry)
    (hcurvature : 0 < deriv (deriv s) (normalizedTime σ expiry T)) :
    0 < deriv (deriv (stockBoundary E σ expiry s)) T :=
  deriv2_stockBoundary_pos hE hσ hT (fun _ ht => h.boundary_hasDerivAt ht)
    (h.boundary_hasDerivAt_deriv (normalizedTime_pos hσ hT)) hcurvature

end NormalizedPutSolution

/-- OPEN analytic goal, deliberately a proposition definition and not a theorem.
Existence and stochastic identification must additionally be proved. -/
def NormalizedCurvatureClaim : Prop :=
  ∀ (k : ℝ) (p : ℝ → ℝ → ℝ) (s : ℝ → ℝ),
    NormalizedPutSolution k p s → ∀ t, 0 < t → 0 < deriv (deriv s) t

/-- OPEN non-vacuity obligation, separate from the conditional curvature claim. -/
def NormalizedExistenceClaim : Prop :=
  ∀ k : ℝ, 0 < k → ∃ p s, NormalizedPutSolution k p s

end MathFin.BlackScholes.AmericanPut.Boundary
