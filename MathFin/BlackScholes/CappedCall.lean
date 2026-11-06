/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
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
# Capped call payoff decomposition

A capped call with strikes `K₁ ≤ K₂` pays `min(max(S − K₁, 0), K₂ − K₁)`. Below
`K₁` the payoff is `0`; between `K₁` and `K₂` it tracks `S − K₁`; above `K₂` it
is capped at `K₂ − K₁`. Algebraically this equals the bull-call spread

`max(S − K₁, 0) − max(S − K₂, 0)`,

so a capped call is replicated by a long call at `K₁` and a short call at `K₂`.

## Main results

* `cappedCall_eq_bull_spread`: case-by-case over `S` vs `K₁, K₂`.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 11.2

## Tags

capped call, bull call spread, payoff decomposition, static replication, option strategy, MSC 91G20,
JEL G13
-/

@[expose] public section

namespace MathFin

/-- **Capped call as a bull call spread**: for `K₁ ≤ K₂`,
`min(max(S − K₁, 0), K₂ − K₁) = max(S − K₁, 0) − max(S − K₂, 0)`. -/
lemma cappedCall_eq_bull_spread (S K₁ K₂ : ℝ) (h : K₁ ≤ K₂) :
    min (max (S - K₁) 0) (K₂ - K₁) =
      max (S - K₁) 0 - max (S - K₂) 0 := by
  by_cases h1 : S ≤ K₁
  · have e1 : max (S - K₁) 0 = 0 := max_eq_right (by linarith)
    have e2 : max (S - K₂) 0 = 0 := max_eq_right (by linarith)
    rw [e1, e2]
    rw [min_eq_left (by linarith : (0:ℝ) ≤ K₂ - K₁)]; ring
  push Not at h1
  by_cases h2 : S ≤ K₂
  · have e1 : max (S - K₁) 0 = S - K₁ := max_eq_left (by linarith)
    have e2 : max (S - K₂) 0 = 0 := max_eq_right (by linarith)
    rw [e1, e2]
    rw [min_eq_left (by linarith : S - K₁ ≤ K₂ - K₁)]; ring
  · push Not at h2
    have e1 : max (S - K₁) 0 = S - K₁ := max_eq_left (by linarith)
    have e2 : max (S - K₂) 0 = S - K₂ := max_eq_left (by linarith)
    rw [e1, e2]
    rw [min_eq_right (by linarith : K₂ - K₁ ≤ S - K₁)]; ring

end MathFin
