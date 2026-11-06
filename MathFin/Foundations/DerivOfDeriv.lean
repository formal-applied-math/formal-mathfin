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
public import Mathlib.Analysis.Convex.Deriv
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
# Second derivatives, from a formula or from convexity

A higher-order sensitivity is usually computed by differentiating an explicit formula for a
lower-order one: gamma as `∂_S Φ(d₁)`, because the call delta is `Φ(d₁)`. That computation is a
statement about the formula. It becomes a statement about the price once the formula is known
to *be* the price's derivative on a neighbourhood of the point: then `deriv` of the price agrees
with the formula near the point, and so do their derivatives there.

* `hasDerivAt_deriv_of_eventually`: `f' = g` near `x` and `g'(x) = c` give `(deriv f)'(x) = c`.
* `hasDerivAt_deriv_param_of_eventually`: the same for a mixed partial `s ↦ ∂_y F(s, y)` at
  `x`, when `∂_y F(s, y) = g s` for every `s` near `x`.
* `deriv_deriv_nonneg_of_convexOn`: the converse direction of the second-derivative test. A
  convex function's second derivative is non-negative on an open set where it is
  differentiable.

## Main results

* `hasDerivAt_deriv_param_of_eventually`: if `F s` has derivative `g s` at `y` for all `s` near
  `x` and `g` has derivative `g'` at `x`, then `s ↦ deriv (F s) y` has derivative `g'` at `x`.
* `deriv_deriv_nonneg_of_convexOn`: a function convex on an open set `S` and differentiable at
  every point of `S` has `0 ≤ deriv (deriv f) x` for `x ∈ S`.

## Tags

gamma, second derivative, convexity test, Greeks, sensitivity, differentiation of formula,
MSC 91G20, JEL G13
-/

@[expose] public section

open Topology

namespace MathFin

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- If `f` has derivative `g y` at every `y` near `x`, and `g` has derivative `g'` at `x`,
then `deriv f` has derivative `g'` at `x`: the second derivative of `f` at `x` is the
derivative of its first-derivative formula. -/
theorem hasDerivAt_deriv_of_eventually {f g : 𝕜 → E} {x : 𝕜} {g' : E}
    (hf : ∀ᶠ y in 𝓝 x, HasDerivAt f (g y) y) (hg : HasDerivAt g g' x) :
    HasDerivAt (deriv f) g' x :=
  hg.congr_of_eventuallyEq (hf.mono fun _ hy ↦ hy.deriv)

/-- The mixed-partial form: if for every `s` near `x` the function `F s` has derivative
`g s` at `y`, and `g` has derivative `g'` at `x`, then `s ↦ deriv (F s) y` has derivative
`g'` at `x`. -/
theorem hasDerivAt_deriv_param_of_eventually {F : 𝕜 → 𝕜 → E} {g : 𝕜 → E} {x y : 𝕜} {g' : E}
    (hF : ∀ᶠ s in 𝓝 x, HasDerivAt (F s) (g s) y) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun s ↦ deriv (F s) y) g' x :=
  hg.congr_of_eventuallyEq (hF.mono fun _ hs ↦ hs.deriv)

/-- A convex function has a non-negative second derivative on an open set where it is
differentiable: its derivative is monotone there (`ConvexOn.monotoneOn_deriv`), and a monotone
function's derivative is non-negative. The converse direction of `convexOn_of_deriv2_nonneg'`. -/
theorem deriv_deriv_nonneg_of_convexOn {S : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ S f)
    (hS : IsOpen S) (hd : ∀ x ∈ S, DifferentiableAt ℝ f x) {x : ℝ} (hx : x ∈ S) :
    0 ≤ deriv (deriv f) x := by
  rw [← derivWithin_of_isOpen hS hx]
  exact (hf.monotoneOn_deriv hd).derivWithin_nonneg

end MathFin
