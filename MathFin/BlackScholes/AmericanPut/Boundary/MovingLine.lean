/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Mathlib

/-!
# Exact change to coordinates relative to a decreasing straight line

The time chain rule changes the drift from `D` to `D-c`. Spatial first
and second derivatives are translations. No PDE or smoothness hypothesis
is silently added by this coordinate change.

## Result

Public entry points include `movingLineTransform`, `movingLineTransform_deriv_x`,
`movingLineTransform_deriv2_x`, `movingLineTransform_hasDeriv_t`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

/-- `V` read in coordinates moving with the line `x = d - c * t`: `V (y + (d - c * t)) t`. -/
noncomputable def movingLineTransform (V : ℝ → ℝ → ℝ) (c d y t : ℝ) : ℝ :=
  V (y + (d - c * t)) t

theorem movingLineTransform_deriv_x (V : ℝ → ℝ → ℝ) (c d y t : ℝ) :
    deriv (fun z => movingLineTransform V c d z t) y =
      deriv (fun x => V x t) (y + (d - c * t)) := by
  simpa only [movingLineTransform] using deriv_comp_add_const (fun x : ℝ => V x t) (d - c * t) y

theorem movingLineTransform_deriv2_x (V : ℝ → ℝ → ℝ) (c d y t : ℝ) :
    deriv (deriv (fun z => movingLineTransform V c d z t)) y =
      deriv (deriv (fun x => V x t)) (y + (d - c * t)) := by
  rw [show deriv (fun z => movingLineTransform V c d z t) =
    fun z => deriv (fun x => V x t) (z + (d - c * t)) from
      funext (fun z => movingLineTransform_deriv_x V c d z t)]
  exact deriv_comp_add_const _ _ _

theorem movingLineTransform_hasDeriv_t {V : ℝ → ℝ → ℝ} {c d y t : ℝ}
    (hV : DifferentiableAt ℝ (fun z : ℝ × ℝ => V z.1 z.2) (y + (d - c * t),t)) :
    HasDerivAt (movingLineTransform V c d y)
      (deriv (V (y + (d - c * t))) t - c * deriv (fun x => V x t) (y + (d - c * t))) t := by
  let x := y + (d - c * t)
  let A := fderiv ℝ (fun z : ℝ × ℝ => V z.1 z.2) (x,t)
  have hA : HasFDerivAt (fun z : ℝ × ℝ => V z.1 z.2) A (x,t) := hV.hasFDerivAt
  have hx : HasDerivAt (fun z => V z t) (A (1,0)) x := by
    simpa only [Function.comp_def, id_eq] using
      hA.comp_hasDerivAt x ((hasDerivAt_id x).prodMk (hasDerivAt_const x t))
  have ht : HasDerivAt (V x) (A (0,1)) t := by
    simpa only [Function.comp_def, id_eq] using
      hA.comp_hasDerivAt t ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
  have hpath : HasDerivAt (fun s : ℝ => (y + (d - c * s), s)) (-c,1) t := by
    convert! (((hasDerivAt_const t d).sub ((hasDerivAt_id t).const_mul c)).const_add y).prodMk
      (hasDerivAt_id t) using 1
    simp
  rw [ht.deriv, hx.deriv]
  convert! hA.comp_hasDerivAt (f := fun s : ℝ => (y + (d - c * s),s)) t hpath using 1
  rw [show ((-c,1) : ℝ × ℝ) = (0,1) - c • (1,0) by ext <;> simp]
  simp only [map_sub, map_smul, smul_eq_mul]

theorem movingLineTransform_equation {V D : ℝ → ℝ → ℝ} {c d y t : ℝ}
    (hV : DifferentiableAt ℝ (fun z : ℝ × ℝ => V z.1 z.2) (y + (d - c * t),t))
    (heq : deriv (V (y + (d - c * t))) t =
      deriv (deriv (fun x => V x t)) (y + (d - c * t)) +
        D (y + (d - c * t)) t * deriv (fun x => V x t) (y + (d - c * t))) :
    deriv (movingLineTransform V c d y) t =
      deriv (deriv (fun z => movingLineTransform V c d z t)) y +
        (D (y + (d - c * t)) t - c) * deriv (fun z => movingLineTransform V c d z t) y := by
  rw [(movingLineTransform_hasDeriv_t hV).deriv,
    movingLineTransform_deriv2_x, movingLineTransform_deriv_x, heq]
  ring

end MathFin.BlackScholes.AmericanPut.Boundary
