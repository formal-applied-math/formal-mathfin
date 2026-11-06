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
# Macaulay vs modified duration under discrete compounding

For a bond with discrete-compounded yield `y` and cashflows `c_i` at times
`t_i ∈ ℕ`, define the duration numerators

  `MacNum(y) = Σ t_i · c_i / (1 + y)^{t_i}`,
  `ModNum(y) = Σ t_i · c_i / (1 + y)^{t_i + 1}`.

Modified duration is `ModNum / Price`, Macaulay duration is `MacNum / Price`.
The discrete-compounding identity is

`ModNum(y) = MacNum(y) / (1 + y)`,

i.e. modified duration differs from Macaulay duration by exactly one factor of
the discount step. (Under continuous compounding the two coincide.)

## Main definitions

* `bondPriceDisc`: the bond price under discrete annual compounding with integer cashflow times.
* `macaulayNumerator`: the Macaulay duration numerator `MacNum(y) = Σ t_i · c_i / (1 + y)^{t_i}`.
* `modifiedNumerator`: the modified duration numerator
  `ModNum(y) = Σ t_i · c_i / (1 + y)^{t_i + 1}`.

## Main results

* `modifiedNumerator_eq_macaulayNumerator_div`: the algebraic identity.

## References

* [Fabozzi, *Fixed Income Mathematics*][FabozziFIM], 4.3

## Tags

Macaulay duration, modified duration, discrete compounding, bond duration, interest rate risk,
MSC 91G30, JEL G12
-/

@[expose] public section

namespace MathFin

open Finset

variable {ι : Type*}

/-- Bond price under discrete annual compounding with integer cashflow times. -/
noncomputable def bondPriceDisc (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (y : ℝ) : ℝ :=
  ∑ i ∈ s, c i / (1 + y) ^ t i

/-- Macaulay duration numerator. -/
noncomputable def macaulayNumerator (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (y : ℝ) : ℝ :=
  ∑ i ∈ s, (t i : ℝ) * c i / (1 + y) ^ t i

/-- Modified duration numerator. -/
noncomputable def modifiedNumerator (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (y : ℝ) : ℝ :=
  ∑ i ∈ s, (t i : ℝ) * c i / (1 + y) ^ (t i + 1)

/-- **Modified = Macaulay / (1 + y)** at the level of numerators, hence at the
level of durations themselves. -/
lemma modifiedNumerator_eq_macaulayNumerator_div
    (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (y : ℝ) (hy : 1 + y ≠ 0) :
    modifiedNumerator s t c y =
      macaulayNumerator s t c y / (1 + y) := by
  unfold modifiedNumerator macaulayNumerator
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [pow_succ]
  field_simp

end MathFin
