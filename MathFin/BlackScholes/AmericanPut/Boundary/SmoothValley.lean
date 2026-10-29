/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Mathlib

/-!
# Smooth three-point detectors of a positive valley

Smooth approximations to `max(x,0)` and `min(x,z)` have strictly positive
partial derivatives. Their difference detects a valley between two positive
values, while remaining nonpositive at spatial collisions and nonpositive
endpoints. These elementary functions will be used for parabolic comparison.

## Result

Public entry points include `smoothPositive`, `smoothPositiveSlope`, `smoothMinimum`,
`smoothValley`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

/-- Smooth approximation to `max x 0`: `(x + Real.sqrt (x^2+δ^2))/2`. -/
noncomputable def smoothPositive (δ x : ℝ) : ℝ :=
  (x + Real.sqrt (x^2+δ^2))/2

/-- Slope of the smoothed positive part: `(1 + x/Real.sqrt (x^2+δ^2))/2`. -/
noncomputable def smoothPositiveSlope (δ x : ℝ) : ℝ :=
  (1+x/Real.sqrt (x^2+δ^2))/2

/-- Smooth approximation to `min x z`: `x - smoothPositive δ (x-z)`. -/
noncomputable def smoothMinimum (δ x z : ℝ) : ℝ := x-smoothPositive δ (x-z)

/-- Three-point detector `smoothMinimum δ x z - smoothPositive δ y`, comparing a smoothed
minimum of `x` and `z` against a smoothed positive part of `y`. -/
noncomputable def smoothValley (δ x y z : ℝ) : ℝ :=
  smoothMinimum δ x z - smoothPositive δ y

theorem smoothPositive_continuous (δ : ℝ) : Continuous (smoothPositive δ) := by
  unfold smoothPositive
  fun_prop

theorem smoothPositive_hasDeriv {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    HasDerivAt (smoothPositive δ) (smoothPositiveSlope δ x) x := by
  have hrad : 0 < x^2+δ^2 := by positivity
  have hs : 0 < Real.sqrt (x^2+δ^2) := Real.sqrt_pos.mpr hrad
  have hd := (((hasDerivAt_id x).pow 2).add_const (δ^2)).sqrt hrad.ne'
  convert! ((hasDerivAt_id x).add hd).div_const 2 using 1
  simp only [smoothPositiveSlope,Pi.pow_apply,id_eq]
  field_simp
  ring

theorem smoothPositiveSlope_bounds {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    0 < smoothPositiveSlope δ x ∧ smoothPositiveSlope δ x < 1 := by
  have hrad : 0 < x^2+δ^2 := by positivity
  have hs : 0 < Real.sqrt (x^2+δ^2) := Real.sqrt_pos.mpr hrad
  have hsq := Real.sq_sqrt hrad.le
  have hxl : -Real.sqrt (x^2+δ^2) < x := by nlinarith [sq_pos_of_pos hδ]
  have hxr : x < Real.sqrt (x^2+δ^2) := by nlinarith [sq_pos_of_pos hδ]
  have hl : -1 < x/Real.sqrt (x^2+δ^2) := (lt_div_iff₀ hs).mpr (by linarith)
  have hr : x/Real.sqrt (x^2+δ^2) < 1 := (div_lt_iff₀ hs).mpr (by linarith)
  unfold smoothPositiveSlope
  constructor <;> linarith

theorem smoothPositive_bounds {δ : ℝ} (hδ : 0 ≤ δ) (x : ℝ) :
    max x 0 ≤ smoothPositive δ x ∧ smoothPositive δ x ≤ max x 0+δ/2 := by
  have hs : 0 ≤ Real.sqrt (x^2+δ^2) := Real.sqrt_nonneg _
  have hsq := Real.sq_sqrt (show 0 ≤ x^2+δ^2 by positivity)
  have hlow : |x| ≤ Real.sqrt (x^2+δ^2) := by nlinarith [sq_abs x,abs_nonneg x]
  have hup : Real.sqrt (x^2+δ^2) ≤ |x|+δ := by
    nlinarith [sq_abs x,abs_nonneg x,mul_nonneg (abs_nonneg x) hδ]
  unfold smoothPositive
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx,abs_of_nonneg hx] at *
    constructor <;> linarith
  · rw [max_eq_right hx,abs_of_nonpos hx] at *
    constructor <;> linarith

theorem smoothMinimum_bounds {δ : ℝ} (hδ : 0 ≤ δ) (x z : ℝ) :
    min x z-δ/2 ≤ smoothMinimum δ x z ∧ smoothMinimum δ x z ≤ min x z := by
  have hb := smoothPositive_bounds hδ (x-z)
  unfold smoothMinimum
  rcases le_total x z with hxz | hzx
  · rw [min_eq_left hxz,max_eq_right (sub_nonpos.mpr hxz)] at *
    constructor <;> linarith
  · rw [min_eq_right hzx,max_eq_left (sub_nonneg.mpr hzx)] at *
    constructor <;> linarith

theorem smoothPositive_strictMono {δ : ℝ} (hδ : 0 < δ) : StrictMono (smoothPositive δ) := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(smoothPositive_hasDeriv hδ x).deriv]
  exact (smoothPositiveSlope_bounds hδ x).1

theorem smoothMinimum_hasDeriv_left {δ : ℝ} (hδ : 0 < δ) (x z : ℝ) :
    HasDerivAt (fun y => smoothMinimum δ y z) (1-smoothPositiveSlope δ (x-z)) x := by
  convert! (hasDerivAt_id x).sub
    ((smoothPositive_hasDeriv hδ (x-z)).comp x ((hasDerivAt_id x).sub_const z)) using 1
  simp

theorem smoothMinimum_hasDeriv_right {δ : ℝ} (hδ : 0 < δ) (x z : ℝ) :
    HasDerivAt (smoothMinimum δ x) (smoothPositiveSlope δ (x-z)) z := by
  convert! (hasDerivAt_const z x).sub
    ((smoothPositive_hasDeriv hδ (x-z)).comp z ((hasDerivAt_id z).const_sub x)) using 1
  simp

theorem smoothMinimum_strictMono_left {δ : ℝ} (hδ : 0 < δ) (z : ℝ) :
    StrictMono (fun x => smoothMinimum δ x z) := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(smoothMinimum_hasDeriv_left hδ x z).deriv]
  linarith [(smoothPositiveSlope_bounds hδ (x-z)).2]

theorem smoothMinimum_strictMono_right {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    StrictMono (smoothMinimum δ x) := by
  apply strictMono_of_deriv_pos
  intro z
  rw [(smoothMinimum_hasDeriv_right hδ x z).deriv]
  exact (smoothPositiveSlope_bounds hδ (x-z)).1

theorem smoothValley_bounds {δ : ℝ} (hδ : 0 ≤ δ) (x y z : ℝ) :
    min x z-max y 0-δ ≤ smoothValley δ x y z ∧
      smoothValley δ x y z ≤ min x z-max y 0 := by
  have hm := smoothMinimum_bounds hδ x z
  have hp := smoothPositive_bounds hδ y
  unfold smoothValley
  constructor <;> linarith

theorem smoothValley_hasDeriv {δ t f' g' j' : ℝ} {f g j : ℝ → ℝ}
    (hδ : 0 < δ) (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) (hj : HasDerivAt j j' t) :
    HasDerivAt (fun s => smoothValley δ (f s) (g s) (j s))
      ((1-smoothPositiveSlope δ (f t-j t))*f' +
        smoothPositiveSlope δ (f t-j t)*j' - smoothPositiveSlope δ (g t)*g') t := by
  convert! (hf.sub ((smoothPositive_hasDeriv hδ (f t-j t)).comp t (hf.sub hj))).sub
    ((smoothPositive_hasDeriv hδ (g t)).comp t hg) using 1
  ring

end MathFin.BlackScholes.AmericanPut.Boundary
