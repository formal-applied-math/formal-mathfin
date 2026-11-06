/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.Init
public import Mathlib.Analysis.Convex.Deriv

/-! # Right derivative trace of a convex function

The derivative is squeezed between a boundary secant and a secant whose
endpoints both approach the boundary. No second derivative is required.

## Main results

* `convex_deriv_tendsto_right`: if `f` is convex on `[b, ∞)`, has right derivative `d` at `b`
  and is differentiable on `(b, ∞)`, then `deriv f x → d` as `x ↓ b`.

## Tags

convex function, right derivative, secant slopes, derivative limit, MSC 35R35, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter
open scoped Topology

theorem convex_deriv_tendsto_right {f : ℝ → ℝ} {b d : ℝ}
    (hc : ConvexOn ℝ (Ici b) f)
    (hfit : HasDerivWithinAt f d (Ici b) b)
    (hd : ∀ x, b < x → DifferentiableAt ℝ f x) :
    Tendsto (deriv f) (𝓝[>] b) (𝓝 d) := by
  have hs : Tendsto (slope f b) (𝓝[>] b) (𝓝 d) :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : b ∉ Ioi b)).mp hfit.Ioi_of_Ici
  have hdouble : Tendsto (fun x : ℝ => 2*x-b) (𝓝[>] b) (𝓝[>] b) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hid : Tendsto (fun x : ℝ => x) (𝓝[>] b) (𝓝 b) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have he : Tendsto (fun x : ℝ => 2*x-b) (𝓝[>] b) (𝓝 (2*b-b)) :=
        (tendsto_const_nhds.mul hid).sub tendsto_const_nhds
      simpa only [id_eq,show 2*b-b=b by ring] using he
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change b < 2*x-b
      change b < x at hx
      linarith
  have hupper : Tendsto (fun x => 2*slope f b (2*x-b)-slope f b x)
      (𝓝[>] b) (𝓝 d) := by
    have he : Tendsto (fun x => 2*slope f b (2*x-b)-slope f b x)
        (𝓝[>] b) (𝓝 (2*d-d)) :=
      (tendsto_const_nhds.mul (hs.comp hdouble)).sub hs
    simpa only [show 2*d-d=d by ring] using he
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hs hupper
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change b < x at hx
    exact hc.slope_le_deriv (by simp) (show x ∈ Ici b from hx.le) hx (hd x hx)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change b < x at hx
    have hu := hc.deriv_le_slope (show x ∈ Ici b from hx.le)
      (show 2*x-b ∈ Ici b by change b ≤ 2*x-b; linarith)
      (show x < 2*x-b by linarith) (hd x hx)
    have he : slope f x (2*x-b) = 2*slope f b (2*x-b)-slope f b x := by
      simp only [slope,vsub_eq_sub,smul_eq_mul,← div_eq_inv_mul]
      have h1 : x-b ≠ 0 := ne_of_gt (sub_pos.mpr hx)
      have h2 : 2*x-b-b ≠ 0 := by linarith
      have h3 : 2*x-b-x ≠ 0 := by linarith
      field_simp
      ring
    rwa [he] at hu

end MathFin.BlackScholes.AmericanPut.Stopping
