/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.Init
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-!
# The normalized American-put problem: coordinates, payoff, operator

CCJZ (2008), (1.1), in normalized coordinates. Arguments are always `(x, t)`, with `x` the
log price relative to strike and `t` the normalized time remaining. This file holds the
ingredients the classical solution contracts are stated in: the normalized rate, the
strike-normalized payoff, `PutEnvelope` (the payoff-level properties of any put price, classical
or the stopping value itself), the continuation region of a candidate boundary, and the
spatial operator. The contracts themselves are `ContinuousBoundaryPutSolution`,
`DividendPutSolution` and its zero-dividend case `NormalizedPutSolution`.

## Main definitions

* `normalizedRate`: the normalization `2 r / σ²` of a rate.
* `putPayoff`: the strike-normalized put payoff `max (1 − eˣ) 0` in log spot.
* `continuationRegion`: the open set `{(x, t) | 0 < t ∧ s t < x}` above a candidate boundary `s`,
  in `(log spot, time remaining)` coordinates.
* `dividendSpatialOperator`: the normalized spatial operator `f'' + (k − h − 1) f' − k f` with
  dividend yield `h`.
* `PutEnvelope`: the payoff-level properties of a put price `p`: continuity for `t ≥ 0`,
  `p x 0 = putPayoff x`, domination of the payoff, and `p x t ≤ 1`.

## Main results

* `normalizedRate_pos`: for `0 < r` and `0 < σ`, `normalizedRate r σ` is positive.
* `normalizedRate_sqrt_two`: at volatility `√2` the normalized rate is `r` (a `simp` lemma).
* `putPayoff_nonneg`, `putPayoff_of_nonpos`: the payoff is nonnegative, and equals `1 − eˣ` for
  `x ≤ 0`.
* `PutEnvelope.nonneg`: for a `PutEnvelope p`, `p x t ≥ 0` for `t ≥ 0`.
* `putPayoff_in_stock_units`: for `0 < E` and `0 < S`,
  `E · putPayoff (log (S / E)) = max (E − S) 0`.

## Tags

normalized American put, free boundary problem, continuation region, put payoff, spatial operator,
Chen–Chadam–Jiang–Zheng, MSC 35R35, MSC 91G20, JEL G13
-/
@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

/-- The Black--Scholes normalization `2 r / σ ^ 2` of a rate; applied to the dividend yield
it gives the normalized dividend `h`. -/
noncomputable def normalizedRate (r σ : ℝ) : ℝ := 2 * r / σ ^ 2

theorem normalizedRate_pos {r σ : ℝ} (hr : 0 < r) (hσ : 0 < σ) :
    0 < normalizedRate r σ := by
  unfold normalizedRate
  positivity

/-- At volatility `√2` the normalized rate is the rate itself. -/
@[simp] theorem normalizedRate_sqrt_two (r : ℝ) : normalizedRate r √2 = r := by
  simp [normalizedRate]

/-- Strike-normalized put payoff in log spot. -/
noncomputable def putPayoff (x : ℝ) : ℝ := max (1 - Real.exp x) 0

/-- Open continuation region; pairs are `(log spot, time remaining)`. -/
def continuationRegion (s : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {z | 0 < z.2 ∧ s z.2 < z.1}

/-- The spatial Black--Scholes operator after normalization, with dividend yield `h`:
`f'' + (k - h - 1) * f' - k * f`. The zero-dividend operator is the case `h = 0`. -/
noncomputable def dividendSpatialOperator (k h : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv f) x + (k - h - 1) * deriv f x - k * f x

theorem putPayoff_nonneg (x : ℝ) : 0 ≤ putPayoff x := le_max_right _ _

/-- The four properties of a put price that the stopping verification uses before any PDE:
`p x t` is continuous in `(x, t)` for `t ≥ 0`, equals the payoff at expiry, dominates the
payoff, and is at most the strike (here normalized to `1`). Pairs are `(log spot, time remaining)`.
No boundary, equation or regularity is assumed, so it is satisfied by the stopping value itself
as well as by any classical solution. -/
structure PutEnvelope (p : ℝ → ℝ → ℝ) : Prop where
  price_continuous : ContinuousOn (fun z : ℝ × ℝ => p z.1 z.2) {z | 0 ≤ z.2}
  initial : ∀ x, p x 0 = putPayoff x
  dominates : ∀ x t, 0 ≤ t → putPayoff x ≤ p x t
  bounded : ∀ x t, 0 ≤ t → p x t ≤ 1

theorem PutEnvelope.nonneg {p : ℝ → ℝ → ℝ} (hp : PutEnvelope p) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ p x t :=
  (putPayoff_nonneg x).trans (hp.dominates x t ht)

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

end MathFin.BlackScholes.AmericanPut.Boundary
