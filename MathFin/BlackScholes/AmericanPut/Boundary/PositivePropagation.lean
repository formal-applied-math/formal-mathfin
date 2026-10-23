/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.PositiveBump
public import MathFin.BlackScholes.AmericanPut.Boundary.MovingLine

/-!
# Propagation of a positive patch along a straight parabolic tube

A compact positive bottom edge gives a positive multiple of an explicit
decaying polynomial bump. Weak comparison transports its positivity to the
interior at later times. Moving-line coordinates allow the patch to travel.
No strong maximum principle is assumed.

## Result

Public entry points include `positive_rectangle_of_positive_bottom`, `positive_straight_tube`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set
open scoped Topology ContDiff

theorem positive_rectangle_of_positive_bottom {U D : ℝ → ℝ → ℝ} {L a T M : ℝ}
    (hL : 0 < L) (haT : a ≤ T)
    (hU : ContinuousOn (fun z : ℝ × ℝ => U z.1 z.2) (movingStrip (fun _ => 0) L a T))
    (hs : ∀ x t, 0 < x → x < L → a < t → t ≤ T →
      ContDiffAt ℝ 2 (fun z : ℝ × ℝ => U z.1 z.2) (x,t))
    (hpde : ∀ x t, 0 < x → x < L → a < t → t ≤ T →
      deriv (deriv (fun y => U y t)) x + D x t * deriv (fun y => U y t) x ≤ deriv (U x) t)
    (hD : ∀ x t, 0 < x → x < L → a < t → t ≤ T → |D x t| ≤ M)
    (hbottom : ∀ x ∈ Icc 0 L, 0 < U x a)
    (hleft : ∀ t ∈ Icc a T, 0 ≤ U 0 t)
    (hright : ∀ t ∈ Icc a T, 0 ≤ U L t) :
    ∀ x t, 0 < x → x < L → a ≤ t → t ≤ T → 0 < U x t := by
  have hc : ContinuousOn (fun x => U x a) (Icc 0 L) :=
    hU.comp (continuousOn_id.prodMk continuousOn_const) (fun _ hx => ⟨le_rfl,haT,hx⟩)
  obtain ⟨x₀,hx₀,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hL.le) hc
  let m := U x₀ a
  have hm : 0 < m := hbottom x₀ hx₀
  let η := m/(L^4+1)
  have hη : 0 < η := div_pos hm (by positivity)
  have hscale : η*(L^4+1) = m := div_mul_cancel₀ _ (by positivity)
  let B := decayingBump L M η a
  have hB : ContDiff ℝ 2 (fun z : ℝ × ℝ => B z.1 z.2) :=
    (decayingBump_contDiff L M η a).of_le (WithTop.coe_le_coe.mpr le_top)
  have hBx (x t : ℝ) : ContDiffAt ℝ 2 (B · t) x := by
    exact hB.contDiffAt.comp x (show ContDiffAt ℝ 2 (fun y : ℝ => (y,t)) x by fun_prop)
  have hBt (x t : ℝ) : DifferentiableAt ℝ (B x) t :=
    (decayingBump_hasDeriv_t L M η a x t).differentiableAt
  let W := fun x t => B x t-U x t
  have hW : ContinuousOn (fun z : ℝ × ℝ => W z.1 z.2) (movingStrip (fun _ => 0) L a T) :=
    hB.continuous.continuousOn.sub hU
  have hUt (x t : ℝ) (hx : 0 < x) (hxL : x < L) (hat : a < t) (htT : t ≤ T) :
      DifferentiableAt ℝ (U x) t :=
    ((hs x t hx hxL hat htT).comp t
      (show ContDiffAt ℝ 2 (fun s : ℝ => (x,s)) t by fun_prop)).differentiableAt (by norm_num)
  have hWpde (x t : ℝ) (hat : a < t) (htT : t ≤ T) (hx : 0 < x) (hxL : x < L) :
      deriv (W x) t ≤ deriv (deriv (fun y => W y t)) x + D x t*deriv (fun y => W y t) x := by
    have hUx : ContDiffAt ℝ 2 (fun y => U y t) x := by
      simpa only [Function.comp_def] using (hs x t hx hxL hat htT).comp x
        (show ContDiffAt ℝ 2 (fun y : ℝ => (y,t)) x by fun_prop)
    have hsecond : deriv (deriv (fun y => W y t)) x =
        deriv (deriv (fun y => B y t)) x-deriv (deriv (fun y => U y t)) x := by
      simpa only [iteratedDeriv_succ,iteratedDeriv_zero,W] using
        iteratedDeriv_fun_sub (n := 2) (hBx x t) hUx
    rw [hsecond]
    dsimp [W]
    rw [deriv_fun_sub (hBt x t) (hUt x t hx hxL hat htT),
      deriv_fun_sub ((hBx x t).differentiableAt (by norm_num)) (hUx.differentiableAt (by norm_num))]
    have hh := decayingBump_subsolution (a := a) (t := t) (x := x) hL hη.le (hD x t hx hxL hat htT)
    have hp := hpde x t hx hxL hat htT
    change deriv (B x) t ≤ deriv (deriv (fun y => B y t)) x+D x t*deriv (fun y => B y t) x at hh
    nlinarith
  have hinit (x : ℝ) (hx : 0 ≤ x) (hxL : x ≤ L) : W x a ≤ 0 := by
    have hq : positiveBump L x ≤ L^4 := by
      unfold positiveBump
      calc
        x^2*(L-x)^2 ≤ L^2*L^2 := by gcongr; linarith
        _ = L^4 := by ring
    have hb : B x a = η*positiveBump L x := by simp [B,decayingBump]
    have hh := hmin ⟨hx,hxL⟩
    change m ≤ U x a at hh
    dsimp [W]
    rw [hb]
    nlinarith [mul_le_mul_of_nonneg_left hq hη.le]
  have hcomp := parabolic_maximum (u := W) (D := D) continuousOn_const (fun _ _ => hL.le) hW
    (fun x t hat htT hx hxL => (hBt x t).sub (hUt x t hx hxL hat htT)) hWpde hinit
    (fun t hat htT => by
      simpa [W,B,decayingBump,positiveBump] using neg_nonpos.mpr (hleft t ⟨hat,htT⟩))
    (fun t hat htT => by
      simpa [W,B,decayingBump,positiveBump] using neg_nonpos.mpr (hright t ⟨hat,htT⟩))
  intro x t hx hxL hat htT
  have hb : 0 < B x t := mul_pos (mul_pos hη (Real.exp_pos _)) (positiveBump_pos hx hxL)
  exact hb.trans_le (sub_nonpos.mp (hcomp (x,t) ⟨hat,htT,hx.le,hxL.le⟩))

/-- Transport of a positive bottom patch along a straight tube. The drift
bound changes by at most the absolute speed of the tube. -/
theorem positive_straight_tube {U D : ℝ → ℝ → ℝ} {L a T M c d : ℝ}
    (hL : 0 < L) (haT : a ≤ T)
    (hU : ContinuousOn (fun z : ℝ × ℝ => U (z.1+(d-c*z.2)) z.2)
      (movingStrip (fun _ => 0) L a T))
    (hs : ∀ x t, 0 < x → x < L → a < t → t ≤ T →
      ContDiffAt ℝ 2 (fun z : ℝ × ℝ => U z.1 z.2) (x+(d-c*t),t))
    (hpde : ∀ x t, 0 < x → x < L → a < t → t ≤ T →
      deriv (U (x+(d-c*t))) t = deriv (deriv (fun y => U y t)) (x+(d-c*t)) +
        D (x+(d-c*t)) t*deriv (fun y => U y t) (x+(d-c*t)))
    (hD : ∀ x t, 0 < x → x < L → a < t → t ≤ T → |D (x+(d-c*t)) t| ≤ M)
    (hbottom : ∀ x ∈ Icc 0 L, 0 < U (x+(d-c*a)) a)
    (hnonneg : ∀ x t, 0 ≤ x → x ≤ L → a ≤ t → t ≤ T → 0 ≤ U (x+(d-c*t)) t) :
    ∀ x t, 0 < x → x < L → a ≤ t → t ≤ T → 0 < U (x+(d-c*t)) t := by
  apply positive_rectangle_of_positive_bottom (U := movingLineTransform U c d)
    (D := fun x t => D (x+(d-c*t)) t-c) (M := M+|c|) hL haT hU
  · intro x t hx hxL hat htT
    exact (hs x t hx hxL hat htT).comp (x,t)
      (show ContDiffAt ℝ 2 (fun z : ℝ × ℝ => (z.1+(d-c*z.2),z.2)) (x,t) by fun_prop)
  · intro x t hx hxL hat htT
    exact (movingLineTransform_equation ((hs x t hx hxL hat htT).differentiableAt (by norm_num))
      (hpde x t hx hxL hat htT)).ge
  · intro x t hx hxL hat htT
    exact (abs_sub _ _).trans (by linarith [hD x t hx hxL hat htT])
  · exact hbottom
  · intro t ht
    exact hnonneg 0 t le_rfl hL.le ht.1 ht.2
  · intro t ht
    exact hnonneg L t hL.le le_rfl ht.1 ht.2

end MathFin.BlackScholes.AmericanPut.Boundary
