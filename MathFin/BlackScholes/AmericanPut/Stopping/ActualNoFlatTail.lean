/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ActualIncrementPositivity
public import MathFin.BlackScholes.AmericanPut.Boundary.ParabolicHopf

/-! # The actual exercise boundary cannot have a flat tail

A flat tail gives a positive time increment in the continuation half-line,
but its value and spatial derivative vanish at the shared exercise boundary.
The explicit terminal Hopf barrier contradicts this. Boundary time derivatives
are not used.

## Main results

* `canonicalLogBoundary_no_flat_tail`: for `0 < k`, `0 ≤ h ≤ k` and `A > 0`, the actual log
  boundary is not constant on `[A, ∞)`.

## Tags

flat tail, Hopf barrier, exercise boundary, boundary speed, American put, MSC 35R35, MSC 91G20,
JEL G13
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Boundary
open scoped Topology ContDiff

theorem canonicalLogBoundary_no_flat_tail {k h A : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (hA : 0 < A) :
    ¬ (∀ s, A ≤ s → canonicalLogBoundary k h s = canonicalLogBoundary k h A) := by
  intro hflat
  let b := canonicalLogBoundary k h
  let F := canonicalIncrementGauge k h 1
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
    ((canonicalIncrementGauge_continuous hk 1).comp
      (show Continuous (fun z : ℝ × ℝ => (z.1+(d-1*z.2),z.2)) by fun_prop)).continuousOn
  have hbase (x t : ℝ) (hx : 0 < x) (hat : a < t) (htT : t ≤ T) :
      ContDiffAt ℝ 2 (fun z : ℝ × ℝ => F z.1 z.2) (x+(d-1*t),t) :=
    canonicalIncrementGauge_contDiffAt hk hh hhk (by norm_num) (hA.trans (ha.trans hat))
      (by rw [hflat t (ha.le.trans hat.le)]; exact hpoint x t hx.le htT (Or.inl hx))
  have hs (x t : ℝ) (hx : 0 < x) (hat : a < t) (htT : t ≤ T) :
      ContDiffAt ℝ 2 (fun z : ℝ × ℝ => u z.1 z.2) (x,t) := by
    simpa only [Function.comp_def,u,movingLineTransform] using (hbase x t hx hat htT).comp (x,t)
      (show ContDiffAt ℝ 2 (fun z : ℝ × ℝ => (z.1+(d-1*z.2),z.2)) (x,t) by fun_prop)
  have heq (x t : ℝ) (hx : 0 < x) (hat : a < t) (htT : t ≤ T) :
      deriv (u x) t = deriv (deriv (fun y => u y t)) x+D x t*deriv (fun y => u y t) x := by
    exact movingLineTransform_equation (D := fun x _ => incrementDrift k h x)
      ((hbase x t hx hat htT).differentiableAt (by norm_num))
      (canonicalIncrementGauge_equation hk hh hhk (δ := 1) (by norm_num)
        (hA.trans (ha.trans hat))
        (by rw [hflat t (ha.le.trans hat.le)]; exact hpoint x t hx.le htT (Or.inl hx)))
  have hpos (x t : ℝ) (hx : 0 ≤ x) (hat : a ≤ t) (htT : t ≤ T) (hi : 0 < x ∨ t < T) :
      0 < u x t :=
    canonicalIncrementGauge_pos_on_flat_tail hk hh hhk (by norm_num) hA hflat
      (hpoint x t hx htT hi) (ha.trans_le hat)
  have hfit := canonicalIncrementGauge_fit_of_same_boundary hk hh hhk
    (δ := 1) (by norm_num) hT
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
    have hder : HasDerivAt (fun y => F (y+b A) T) 0 0 := by
      convert! hfit.2.comp_of_eq 0 ((hasDerivAt_id (0 : ℝ)).add_const (b A)) (by simp [b]) using 1
      simp
    exact hder.hasDerivWithinAt
  obtain ⟨M,hM⟩ := incrementDrift_bounded (h := h) hk
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
      have hbound := (abs_le.mp (hM (x+(d-1*t)))).1
      dsimp [D]
      linarith)
    (fun x hx => hpos x a hx.1 le_rfl haT.le (Or.inr haT))
    (fun t _ _ => canonicalIncrementGauge_nonneg hk (by norm_num) _ t)
    (fun t ht => hpos 1 t (by norm_num) ht.1 ht.2 (Or.inl (by norm_num))) hzero hd
  exact (lt_irrefl 0) hhopf

end MathFin.BlackScholes.AmericanPut.Stopping
