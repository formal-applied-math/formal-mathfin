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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

/-!
# The product of two standard simplices

`Convexity.StdSimplex R X` is the finitely supported probability distributions on `X`. Mathlib has
the monad structure (`StdSimplex.map`, `StdSimplex.join`) and no product of independent
distributions. `StdSimplex.prod p q` is the monadic bind of `p` against `x ↦ q.map (x, ·)`, so its
weights are nonnegative and sum to one by the monad's own proofs, and its weight at `(x, y)` is the
product `p x * q y` (`StdSimplex.weights_prod`).

## Main definitions

* `StdSimplex.prod`: the product distribution of `p : StdSimplex R X` and `q : StdSimplex R Y`,
  the monadic bind of `p` against `x ↦ q.map (x, ·)`.

## Main results

* `StdSimplex.weights_prod`: the weight of `p.prod q` at `(x, y)` is `p.weights x * q.weights y`.

## Tags

product of distributions, independent distributions, standard simplex,
finitely supported probability, monad bind, MSC 60E05
-/

@[expose] public section

namespace Convexity.StdSimplex

variable {R : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] {X Y : Type*}

/-- The **product distribution** of independent `p` on `X` and `q` on `Y`. -/
noncomputable def prod (p : StdSimplex R X) (q : StdSimplex R Y) : StdSimplex R (X × Y) :=
  (p.map fun x ↦ q.map (x, ·)).join

/-- The weight of the product distribution at `(x, y)` is `p x * q y`. -/
@[simp] theorem weights_prod (p : StdSimplex R X) (q : StdSimplex R Y) (x : X) (y : Y) :
    (p.prod q).weights (x, y) = p.weights x * q.weights y := by
  classical
  have key : ((p.weights.mapDomain fun x ↦ q.map (x, ·)).sum fun d r ↦ r • d.weights) =
      p.weights.sum fun x r ↦ r • (q.map (x, ·)).weights :=
    Finsupp.sum_mapDomain_index (fun _ ↦ zero_smul _ _) fun _ _ _ ↦ add_smul _ _ _
  rw [prod, weights_join, weights_map, key, Finsupp.sum_apply, Finsupp.sum_eq_single x]
  · simp [Finsupp.mapDomain_apply_of_injective (Prod.mk_right_injective x)]
  · intro x' _ hx'
    have hn : ((x, y) : X × Y) ∉ Set.range fun y' ↦ (x', y') := by
      rintro ⟨y', hy'⟩
      exact hx' (congrArg Prod.fst hy')
    simp [Finsupp.mapDomain_of_notMem_range _ _ hn]
  · intro _
    simp

end Convexity.StdSimplex
