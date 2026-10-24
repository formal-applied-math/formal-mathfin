/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.IncrementPositivity
public import MathFin.BlackScholes.AmericanPut.Boundary.FlatTail
public import MathFin.BlackScholes.AmericanPut.Boundary.ParabolicHopf

/-!
# Strictly negative boundary speed from the classical pricing contract

A hypothetical flat tail makes the positive normalized time increment share
value and smooth fit at the fixed boundary. A backward rectangle with a
slanted left edge lies strictly in continuation before terminal contact. The
proved terminal Hopf barrier then contradicts the zero spatial derivative.
Combined with weak log curvature, this excludes zero speed everywhere.

## Result

Public entry points include `boundary_no_flat_tail`, `boundary_deriv_neg`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary.DividendPutSolution

open Set
open scoped Topology ContDiff

variable {k h : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}

theorem boundary_no_flat_tail (hp : DividendPutSolution k h p b)
    {A : ℝ} (hA : 0 < A) : ¬ (∀ s, A ≤ s → b s = b A) := by
  intro hflat
  let F := incrementGauge p k h 1
  let a := A+1
  let T := A+2
  let d := b A+T
  let u := movingLineTransform F 1 d
  let D := fun x t => incrementDrift k h (x+(d-1*t))-1
  have ha : A < a := by dsimp [a]; linarith
  have haT : a < T := by dsimp [a,T]; linarith
  have hT : 0 < T := hA.trans (ha.trans haT)
  have hpoint (x t : ℝ) (hx : 0 ≤ x) (htT : t ≤ T) (hi : 0 < x ∨ t < T) :
      b A < x+(d-1*t) := by
    dsimp [d]
    rcases hi with hi | hi <;> linarith
  have hU : ContinuousOn (fun z : ℝ × ℝ => u z.1 z.2) (movingStrip (fun _ => 0) 1 a T) :=
    (hp.incrementGauge_continuousOn (δ := 1) (by norm_num)).comp
      (show ContinuousOn (fun z : ℝ × ℝ => (z.1+(d-1*z.2),z.2))
        (movingStrip (fun _ => 0) 1 a T) by fun_prop)
      (fun _ hz => hA.le.trans (ha.le.trans hz.1))
  have hbase (x t : ℝ) (hx : 0 < x) (hat : a < t) (htT : t ≤ T) :
      ContDiffAt ℝ 2 (fun z : ℝ × ℝ => F z.1 z.2) (x+(d-1*t),t) :=
    hp.incrementGauge_contDiffAt (by norm_num) (hA.trans (ha.trans hat))
      (by rw [hflat t (ha.le.trans hat.le)]; exact hpoint x t hx.le htT (Or.inl hx))
  have hs (x t : ℝ) (hx : 0 < x) (hat : a < t) (htT : t ≤ T) :
      ContDiffAt ℝ 2 (fun z : ℝ × ℝ => u z.1 z.2) (x,t) := by
    simpa only [Function.comp_def,u,movingLineTransform] using (hbase x t hx hat htT).comp (x,t)
      (show ContDiffAt ℝ 2 (fun z : ℝ × ℝ => (z.1+(d-1*z.2),z.2)) (x,t) by fun_prop)
  have heq (x t : ℝ) (hx : 0 < x) (hat : a < t) (htT : t ≤ T) :
      deriv (u x) t = deriv (deriv (fun y => u y t)) x+D x t*deriv (fun y => u y t) x := by
    exact movingLineTransform_equation (D := fun x _ => incrementDrift k h x)
      ((hbase x t hx hat htT).differentiableAt (by norm_num))
      (hp.incrementGauge_equation (δ := 1) (by norm_num) (hA.trans (ha.trans hat))
        (by rw [hflat t (ha.le.trans hat.le)]; exact hpoint x t hx.le htT (Or.inl hx)))
  have hpos (x t : ℝ) (hx : 0 ≤ x) (hat : a ≤ t) (htT : t ≤ T) (hi : 0 < x ∨ t < T) :
      0 < u x t :=
    hp.incrementGauge_pos_on_flat_tail (by norm_num) hA hflat (hpoint x t hx htT hi)
        (ha.trans_le hat)
  have hfit := hp.incrementGauge_fit_of_same_boundary (δ := 1) (by norm_num) hT
    (by rw [hflat (T+1) (by linarith [ha.trans haT]),hflat T (ha.le.trans haT.le)])
  rw [hflat T (ha.le.trans haT.le)] at hfit
  have huT : (fun y => u y T) = fun y => F (y+b A) T := by
    funext y
    dsimp [u,movingLineTransform,d]
    congr 2
    ring
  have hzero : u 0 T = 0 := by rw [congrFun huT 0,zero_add]; exact hfit.1
  have hd : HasDerivWithinAt (fun y => u y T) 0 (Ici 0) 0 := by
    rw [huT]
    have hh : HasDerivAt (fun y => F (y+b A) T) 0 0 := by
      convert! hfit.2.comp_of_eq 0 ((hasDerivAt_id (0 : ℝ)).add_const (b A)) (by simp) using 1
      simp
    exact hh.hasDerivWithinAt
  obtain ⟨M,hM⟩ := incrementDrift_bounded (h := h) hp.rate_pos
  have hhopf := terminal_hopf (u := u) (D := D) (L := 1) (M := M+1)
    (by norm_num) haT.le hU
    (by
      intro x t hx _ hat htT
      simpa only [Function.comp_def] using (hs x t hx hat htT).comp x
        (show ContDiffAt ℝ 2 (fun y : ℝ => (y,t)) x by fun_prop))
    (fun x t hx _ hat htT =>
      ((hs x t hx hat htT).comp t
        (show ContDiffAt ℝ 2 (fun s : ℝ => (x,s)) t by fun_prop)).differentiableAt (by norm_num))
    (fun x t hx _ hat htT => (heq x t hx hat htT).ge)
    (by
      intro x t _ _ _ _
      have hh := (abs_le.mp (hM (x+(d-1*t)))).1
      dsimp [D]
      linarith)
    (fun x hx => hpos x a hx.1 le_rfl haT.le (Or.inr haT))
    (fun t hat _ => hp.incrementGauge_nonneg (by norm_num) (hA.le.trans (ha.le.trans hat)) _)
    (fun t ht => hpos 1 t (by norm_num) ht.1 ht.2 (Or.inl (by norm_num))) hzero hd
  exact (lt_irrefl 0) hhopf

theorem boundary_deriv_neg (hp : DividendPutSolution k h p b) {t : ℝ} (ht : 0 < t) :
    deriv b t < 0 := by
  apply lt_of_le_of_ne (hp.boundary_deriv_nonpos ht)
  intro hz
  exact hp.boundary_no_flat_tail ht (hp.boundary_flat_tail_of_zero_speed ht hz)

end MathFin.BlackScholes.AmericanPut.Boundary.DividendPutSolution
