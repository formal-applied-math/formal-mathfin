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
public import Mathlib.Algebra.Ring.IsFormallyReal
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

/-! # Traces at a repeated real root

Part of the SVI polynomial-sign certificate (#174).

In `ℝ[X]/((X − c)ʳ)` every element differs from its value at `c` by a nilpotent, and its trace is
`r` times that value.

## Main definitions

* `realRootEval`: evaluation at `c`, as an `ℝ`-algebra map `AdjoinRoot ((X - C c)^r) → ℝ` for
  `r > 0`.

## Main results

* `realRootEval_mk`: `realRootEval` sends the class of `p` to `p.eval c`.
* `realRoot_nilpotent_remainder`: every element of `AdjoinRoot ((X - C c)^r)` differs from the
  image of its value at `c` by a nilpotent.
* `trace_realRoot_component`: the algebra trace of `x` in `AdjoinRoot ((X - C c)^r)` is
  `r * realRootEval c r hr x`.

## Tags

repeated root, nilpotent trace, quotient ring trace, SVI, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI
open Polynomial

/-- Evaluation at `c` on `ℝ[X]/((X − c)ʳ)`, for `r > 0`. -/
noncomputable def realRootEval (c : ℝ) (r : ℕ) (hr : 0 < r) :
    AdjoinRoot ((X - C c)^r) →ₐ[ℝ] ℝ :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId ℝ ℝ) c (by simp [ne_of_gt hr])

theorem realRootEval_mk (c : ℝ) (r : ℕ) (hr : 0 < r) (p : ℝ[X]) :
    realRootEval c r hr (AdjoinRoot.mk ((X-C c)^r) p) = p.eval c := by
  simp [realRootEval, AdjoinRoot.liftAlgHom_mk]

/-- In a repeated real-root component, every element differs from its value
at the root by a nilpotent. -/
theorem realRoot_nilpotent_remainder (c : ℝ) (r : ℕ) (hr : 0 < r)
    (x : AdjoinRoot ((X - C c) ^ r)) :
    IsNilpotent (x - algebraMap ℝ _ (realRootEval c r hr x)) := by
  induction x using AdjoinRoot.induction_on with
  | ih p =>
    rw [realRootEval_mk]
    have hnil : IsNilpotent (AdjoinRoot.mk ((X-C c)^r) (X-C c)) := by
      refine ⟨r, ?_⟩
      rw [← map_pow, AdjoinRoot.mk_self]
    have hdiv : X-C c ∣ p-C (p.eval c) := dvd_iff_isRoot.mpr (by simp [IsRoot])
    obtain ⟨q, hq⟩ := hdiv
    have he : AdjoinRoot.mk ((X-C c)^r) p - algebraMap ℝ _ (p.eval c) =
        AdjoinRoot.mk ((X-C c)^r) (p-C (p.eval c)) := by simp
    rw [he, hq, map_mul]
    obtain ⟨m, hm⟩ := hnil
    exact ⟨m, by rw [mul_pow, hm, zero_mul]⟩

/-- A root of multiplicity r contributes r times its evaluation to the
algebra trace. This is the key boundary-safe multiplicity identity. -/
theorem trace_realRoot_component (c : ℝ) (r : ℕ) (hr : 0 < r)
    (x : AdjoinRoot ((X - C c) ^ r)) :
    Algebra.trace ℝ _ x = (r : ℝ) * realRootEval c r hr x := by
  have hf : (X-C c)^r ≠ (0 : ℝ[X]) := pow_ne_zero _ (X_sub_C_ne_zero c)
  let pb := AdjoinRoot.powerBasis hf
  let : Module.Free ℝ (AdjoinRoot ((X-C c)^r)) := Module.Free.of_basis pb.basis
  have hz := (Algebra.isNilpotent_trace_of_isNilpotent
    (R := ℝ) (realRoot_nilpotent_remainder c r hr x)).eq_zero
  rw [map_sub, Algebra.trace_algebraMap] at hz
  have hdim : Module.finrank ℝ (AdjoinRoot ((X-C c)^r)) = r := by
    rw [pb.finrank]
    simp [pb, AdjoinRoot.powerBasis_dim, natDegree_pow]
  rw [hdim, nsmul_eq_mul] at hz
  exact sub_eq_zero.mp hz

end SVI
end MathFin
