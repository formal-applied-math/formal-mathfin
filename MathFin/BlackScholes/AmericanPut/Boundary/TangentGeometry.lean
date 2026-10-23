/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Mathlib

/-!
# Strict concave tangent geometry at positive times

Local negative curvature puts a smooth function strictly below its tangent on
both sides. This is a real-calculus theorem, independent of any parabolic or
financial assumptions.

## Result

Public entry points include `eventually_lt_tangent_of_second_deriv_neg`.
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
