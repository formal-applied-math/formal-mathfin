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

/-! # Lifting a square root of −1 through a nilpotent

Part of the SVI polynomial-sign certificate (#174).

In a commutative ring in which `2` is invertible, if `x² + 1` is nilpotent then `−1` has an exact
square root (`exists_sq_neg_one_of_nilpotent`).

## Main results

* `exists_sq_neg_one_of_nilpotent`: in a nontrivial commutative ring with `2 * half = 1`, if
  `x ^ 2 + 1` is nilpotent for some `x`, then there is `u` with `u ^ 2 = -1`.

## Tags

nilpotent lifting, square root of minus one, Hensel-type lifting, SVI, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI

/-- Lift a square root of -1 through a nilpotent error. Each correction
squares the error, so the construction terminates after finitely many steps.
No reducedness assumption is needed. -/
theorem exists_sq_neg_one_of_nilpotent {A : Type*} [CommRing A] [Nontrivial A]
    (half : A) (hh : 2 * half = 1) (x : A) (hx : IsNilpotent (x ^ 2 + 1)) :
    ∃ u : A, u^2 = -1 := by
  obtain ⟨r, hr⟩ := hx
  induction r using Nat.strong_induction_on generalizing x with
  | h r ih =>
    rcases r with _ | (_ | n)
    · norm_num at hr
    · exact ⟨x, by simpa only [Nat.zero_add, pow_one, add_eq_zero_iff_eq_neg] using hr⟩
    · let e := x^2+1
      let y := x*(1+e*half)
      have he : y^2+1 = e^2*(e+3)*half^2 := by
        dsimp [y, e]
        linear_combination -(x^2+1+2*(x^2+1)^2*half) * hh
      have hy : (y^2+1)^(n+1) = 0 := by
        rw [he, mul_pow, mul_pow, ← pow_mul]
        have hz : e^(2*(n+1)) = 0 := pow_eq_zero_of_le (by omega) hr
        rw [hz, zero_mul, zero_mul]
      exact ih (n+1) (by omega) y hy

end SVI
end MathFin
