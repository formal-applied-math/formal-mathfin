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
# `extendOfNorm` of a pointwise isometry is a global isometry

The single generic lemma `LinearMap.norm_extendOfNorm_eq_of_isometry`: if a linear map `e` has dense
range and a (semi)linear map `f` is a pointwise isometry along it (`‖f x‖ = ‖e x‖`), then the
norm-continuous extension `f.extendOfNorm e` is a global isometry `‖f.extendOfNorm e y‖ = ‖y‖`.

This is the shared analytic kernel of every `L²`-isometry-by-density construction in the library —
the Wiener integral, the Itô CLM, the predictable Itô `L²` integral, and the Itô–Lévy compensated
integral. It lives in its own `Mathlib`-only leaf so both the Brownian (`WienerIntegral`) and jump
(`PoissonCompensatedIntegralOperator`) towers consume it without depending on each other.

The `≤` half is Mathlib's `LinearMap.norm_extendOfNorm_apply_le` (with `C = 1`); the reverse half is
`DenseRange.induction_on`, propagating the pointwise isometry off the dense range to a closed
equality set.

## Main results

* `norm_extendOfNorm_eq_of_isometry`: if `e` has dense range and `f` is a pointwise isometry along
  `e` (`‖f x‖ = ‖e x‖`), then its norm-continuous extension satisfies `‖f.extendOfNorm e y‖ = ‖y‖`
  for all `y`.

## Tags

isometry extension, Itô integral, Wiener integral, density argument, L2 isometry, MSC 60H05,
MSC 60G51
-/

@[expose] public section

namespace LinearMap

variable {𝕜 𝕜₂ E Eₗ F : Type*}
  [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  [AddCommGroup E] [SeminormedAddCommGroup Eₗ] [NormedAddCommGroup F]
  [Module 𝕜 E] [Module 𝕜₂ F] [IsBoundedSMul 𝕜₂ F] [Module 𝕜 Eₗ] [IsBoundedSMul 𝕜 Eₗ]
  [CompleteSpace F]
  {f : E →ₛₗ[σ₁₂] F} {e : E →ₗ[𝕜] Eₗ}

/-- If `e` has dense range and `f` is a pointwise isometry along `e`
(`‖f x‖ = ‖e x‖`), then the `extendOfNorm` extension of `f` along `e` is a global
isometry `‖f.extendOfNorm e y‖ = ‖y‖`. The shared kernel of the Wiener,
Itô-CLM, predictable-Itô, and Itô–Lévy `L²` isometries. -/
theorem norm_extendOfNorm_eq_of_isometry
    (h_dense : DenseRange e) (h_isom : ∀ x, ‖f x‖ = ‖e x‖) (y : Eₗ) :
    ‖f.extendOfNorm e y‖ = ‖y‖ := by
  have h_on_range : ∀ x, ‖f.extendOfNorm e (e x)‖ = ‖e x‖ := fun x ↦ by
    rw [LinearMap.extendOfNorm_eq h_dense ⟨1, fun z ↦ by rw [one_mul]; exact (h_isom z).le⟩,
        h_isom]
  exact h_dense.induction_on (p := fun z ↦ ‖f.extendOfNorm e z‖ = ‖z‖) y
    (isClosed_eq (continuous_norm.comp (f.extendOfNorm e).continuous) continuous_norm)
    h_on_range

end LinearMap
