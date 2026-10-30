/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.ParabolicUnimodality
public import MathFin.BlackScholes.AmericanPut.Boundary.ComparisonMaximum

/-!
# The comparison difference has one positive interval

The direct three-point maximum principle is applied to the normalized PDE.
The initial shape, boundary signs, uniform right truncation and interior
smoothness have all been proved from the pricing contract. No Sturm theorem
or initial spatial derivative trace is a premise of this route.

## Result

Public entry points include `straightDifference_three_point_bound`,
`straightDifference_superlevel_interval`, `straightDifference_positive_interval`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary.Comparison

open Set
open scoped ContDiff

variable {k h c d : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}

theorem straightDifference_three_point_bound (hp : ContinuousBoundaryPutSolution k h p b)
    (hc : 0 < c) (hd : d ≤ 0) {x y z t : ℝ} (ht : 0 < t)
    (hx : b t ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) :
    min (straightDifference p k h c d x t) (straightDifference p k h c d z t) ≤
      max (straightDifference p k h c d y t) 0 := by
  obtain ⟨X,hX,htail⟩ := straightDifference_right_negative hp hc hd
  let R := max X (z+1)
  have hR : 0 < R := hX.trans_le (le_max_left _ _)
  have hzR : z ≤ R := by dsimp [R]; linarith [le_max_right X (z+1)]
  let f := profile (k-h-1-c) k
  let g := profile (k-h-1+2-c) h
  have hf : ProfileData (k-h-1-c) k f := profile_data hp.rate_pos.le
  have hg : ProfileData (k-h-1+2-c) h g := profile_data hp.dividend_nonneg
  have hb : ContinuousOn b (Icc 0 t) := hp.boundary_continuous.mono (fun _ hs => hs.1)
  have hbR : ∀ s ∈ Icc 0 t, b s ≤ R := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with he | he
    · simpa [← he,hp.boundary_initial] using hR.le
    · exact (hp.boundary_nonpos he).trans hR.le
  have hinit : ∀ a m e, b 0 ≤ a → a ≤ m → m ≤ e → e ≤ R →
      min (straightDifference p k h c d a 0) (straightDifference p k h c d e 0) ≤
        max (straightDifference p k h c d m 0) 0 := by
    intro a m e ha ham hme _
    rw [hp.boundary_initial] at ha
    rcases eq_or_lt_of_le ha with he | he
    · subst a
      have hh := straightDifference_boundary_nonpos hp hc.le hd (t := 0) le_rfl
      rw [hp.boundary_initial] at hh
      exact (min_le_left _ _).trans (hh.trans (le_max_right _ _))
    · apply three_point_bound_of_positive_superlevels
        (S := Ioi (0 : ℝ)) (F := fun a => straightDifference p k h c d a 0) _ he
        (he.trans_le (ham.trans hme)) ham hme
      intro ε hε
      exact normalizedDifference_initial_superlevel hp hc (by linarith) d
  exact parabolic_three_point_bound (U := straightDifference p k h c d)
    (D := fun a s => k-h-1+2*deriv f (a+c*s-d)/f (a+c*s-d)) hb hbR
    ((normalizedDifference_continuousOn (c := c) (d := d) hp hf hg).mono (fun _ hs => hs.1))
    (fun a s hs _ hba _ => (normalizedDifference_contDiffAt hp hf hg hs hba).of_le
      (WithTop.coe_le_coe.mpr le_top))
    (fun a s hs _ hba _ => normalizedDifference_equation hp hf hg hs hba)
    (fun s hs _ => straightDifference_boundary_nonpos hp hc.le hd hs)
    (fun s hs _ => (htail R (le_max_left _ _) s hs).le)
    hinit ht.le le_rfl hx hxy hyz hzR

/-- All nonnegative strict superlevel sets of the actual comparison are
intervals. This is the propagation invariant, with no unproved analytic input. -/
theorem straightDifference_superlevel_interval (hp : ContinuousBoundaryPutSolution k h p b)
    (hc : 0 < c) (hd : d ≤ 0) {t ε : ℝ} (ht : 0 < t) (hε : 0 ≤ ε) :
    OrdConnected {x | b t < x ∧ ε < straightDifference p k h c d x t} := by
  rw [ordConnected_iff]
  intro x hx z hz _ y hy
  refine ⟨hx.1.trans_le hy.1,?_⟩
  by_contra hn
  have hmid : straightDifference p k h c d y t ≤ ε := le_of_not_gt hn
  have hh := straightDifference_three_point_bound hp hc hd ht hx.1.le hy.1 hy.2
  have hlo := lt_min hx.2 hz.2
  have hhi : max (straightDifference p k h c d y t) 0 ≤ ε := max_le hmid hε
  linarith

theorem straightDifference_positive_interval (hp : ContinuousBoundaryPutSolution k h p b)
    (hc : 0 < c) (hd : d ≤ 0) {t : ℝ} (ht : 0 < t) :
    OrdConnected {x | b t < x ∧ 0 < straightDifference p k h c d x t} :=
  straightDifference_superlevel_interval hp hc hd ht le_rfl

end MathFin.BlackScholes.AmericanPut.Boundary.Comparison
