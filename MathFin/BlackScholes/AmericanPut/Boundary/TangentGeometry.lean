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
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TotallySplit
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
# Strict concave tangent geometry at positive times

Local negative curvature puts a smooth function strictly below its tangent on
both sides. This is a real-calculus theorem, independent of any parabolic or
financial assumptions.

## Main results

* `eventually_lt_tangent_of_second_deriv_neg`: if `b` is smooth on `(0, ∞)`, `T > 0` and
  `deriv (deriv b) T < 0`, then `b t < b T + deriv b T · (t − T)` for all `t ≠ T` near `T`.

## Tags

concave tangent, second derivative, local curvature, tangent line, MSC 35R35, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set Filter
open scoped Topology ContDiff

theorem eventually_lt_tangent_of_second_deriv_neg {b : ℝ → ℝ} {T : ℝ}
    (hb : ContDiffOn ℝ ∞ b (Ioi 0)) (hT : 0 < T) (hneg : deriv (deriv b) T < 0) :
    ∀ᶠ t in 𝓝 T, t ≠ T → b t < b T + deriv b T * (t - T) := by
  have hs : ContDiffAt ℝ 2 b T :=
    (hb.contDiffAt (Ioi_mem_nhds hT)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hs₁ : ContDiffAt ℝ 1 (deriv b) T := hs.derivWithin (by norm_num)
  have hc₂ : ContinuousAt (deriv (deriv b)) T :=
      (hs₁.derivWithin (m := 0) (by norm_num)).continuousAt
  have hpositive : ∀ᶠ t in 𝓝 T, 0 < t := Ioi_mem_nhds hT
  have hnear : ∀ᶠ t in 𝓝 T, 0 < t ∧ deriv (deriv b) t < 0 :=
    hpositive.and (hc₂.eventually (Iio_mem_nhds hneg))
  obtain ⟨l,r,⟨hl,hr⟩,hsub⟩ := hnear.exists_Ioo_subset
  have hcont : ContinuousOn b (Ioo l r) := hb.continuousOn.mono (fun t ht => (hsub ht).1)
  have hconc : StrictConcaveOn ℝ (Ioo l r) b := strictConcaveOn_of_deriv2_neg (convex_Ioo l r) hcont
    (fun t ht => (hsub (interior_subset ht)).2)
  filter_upwards [Ioo_mem_nhds hl hr] with t ht hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hsl := hconc.deriv_lt_slope ht ⟨hl,hr⟩ hlt (hs.differentiableAt (by norm_num))
    rw [slope_def_field, lt_div_iff₀ (sub_pos.mpr hlt)] at hsl
    nlinarith
  · have hsl := hconc.slope_lt_deriv ⟨hl,hr⟩ ht hgt (hs.differentiableAt (by norm_num))
    rw [slope_def_field, div_lt_iff₀ (sub_pos.mpr hgt)] at hsl
    nlinarith

end MathFin.BlackScholes.AmericanPut.Boundary
