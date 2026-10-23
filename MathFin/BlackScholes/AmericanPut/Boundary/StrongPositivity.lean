/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.PositivePropagation

/-!
# Strict positivity propagates from one point to a later half-line slice

Continuity supplies a small positive patch. A straight tube carries that
patch to any prescribed interior point at a strictly later time. The tube
stays inside the spatial half-line. The result is derived from an explicit
barrier and weak comparison, not imported as a PDE axiom.

## Result

Public entry points include `positive_later_of_positive_point`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set Filter
open scoped Topology ContDiff

theorem positive_later_of_positive_point {U D : ℝ → ℝ → ℝ} {β a T M x y : ℝ}
    (haT : a < T) (hx : β < x) (hy : β < y)
    (hU : ContinuousOn (fun z : ℝ × ℝ => U z.1 z.2) (Ioi β ×ˢ Icc a T))
    (hs : ∀ z t, β < z → a < t → t ≤ T →
      ContDiffAt ℝ 2 (fun w : ℝ × ℝ => U w.1 w.2) (z,t))
    (hpde : ∀ z t, β < z → a < t → t ≤ T →
      deriv (U z) t = deriv (deriv (fun w => U w t)) z + D z t*deriv (fun w => U w t) z)
    (hD : ∀ z t, β < z → a < t → t ≤ T → |D z t| ≤ M)
    (hnonneg : ∀ z t, β < z → a ≤ t → t ≤ T → 0 ≤ U z t)
    (hsource : 0 < U x a) : 0 < U y T := by
  have hcont : ContinuousAt (fun z => U z a) x := by
    have hc : ContinuousOn (fun z => U z a) (Ioi β) :=
      hU.comp (continuousOn_id.prodMk continuousOn_const) (fun _ hz => ⟨hz,le_rfl,haT.le⟩)
    exact hc.continuousAt (Ioi_mem_nhds hx)
  have hnear : ∀ᶠ z in 𝓝 x, β < z ∧ 0 < U z a :=
    (show ∀ᶠ z in 𝓝 x, β < z from Ioi_mem_nhds hx).and
      (hcont.eventually (Ioi_mem_nhds hsource))
  obtain ⟨l,r,⟨hl,hr⟩,hsub⟩ := hnear.exists_Ioo_subset
  let ρ := min ((x-l)/2) (min ((r-x)/2) ((y-β)/2))
  have hρ : 0 < ρ := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hρl : ρ < x-l := by
    have := min_le_left ((x-l)/2) (min ((r-x)/2) ((y-β)/2)); dsimp [ρ]; linarith
  have hρr : ρ < r-x := by
    have hh := (min_le_right ((x-l)/2) (min ((r-x)/2) ((y-β)/2))).trans (min_le_left _ _)
    change ρ ≤ (r-x)/2 at hh
    linarith
  have hρy : ρ < y-β := by
    have hh := (min_le_right ((x-l)/2) (min ((r-x)/2) ((y-β)/2))).trans (min_le_right _ _)
    change ρ ≤ (y-β)/2 at hh
    linarith
  let c := (x-y)/(T-a)
  let d := x-ρ+c*a
  have hlineA : d-c*a = x-ρ := by dsimp [d]; ring
  have hlineT : d-c*T = y-ρ := by
    dsimp [d,c]
    field_simp [ne_of_gt (sub_pos.mpr haT)]
    ring
  have hβA : β < d-c*a := by
    rw [hlineA]
    exact (hsub (show x-ρ ∈ Ioo l r by constructor <;> linarith)).1
  have hβT : β < d-c*T := by rw [hlineT]; linarith
  have hline (t : ℝ) (hat : a ≤ t) (htT : t ≤ T) : β < d-c*t := by
    rcases le_total c 0 with hc | hc
    · have hh := mul_nonpos_of_nonpos_of_nonneg hc (sub_nonneg.mpr hat)
      nlinarith
    · have hh := mul_nonneg hc (sub_nonneg.mpr htT)
      nlinarith
  have hpoint (z t : ℝ) (hz : 0 ≤ z) (hat : a ≤ t) (htT : t ≤ T) : β < z+(d-c*t) := by
    linarith [hline t hat htT]
  have htube := positive_straight_tube (U := U) (D := D) (M := M) (c := c) (d := d)
    (L := 2*ρ) (by positivity) haT.le
    (hU.comp (show ContinuousOn (fun w : ℝ × ℝ => (w.1+(d-c*w.2),w.2))
      (movingStrip (fun _ => 0) (2*ρ) a T) by fun_prop)
      (fun w hw => ⟨hpoint w.1 w.2 hw.2.2.1 hw.1 hw.2.1,hw.1,hw.2.1⟩))
    (fun z t hz _ hat htT => hs _ _ (hpoint z t hz.le hat.le htT) hat htT)
    (fun z t hz _ hat htT => hpde _ _ (hpoint z t hz.le hat.le htT) hat htT)
    (fun z t hz _ hat htT => hD _ _ (hpoint z t hz.le hat.le htT) hat htT)
    (by
      intro z hz
      rw [hlineA]
      exact (hsub (show z+(x-ρ) ∈ Ioo l r by constructor <;> linarith [hz.1,hz.2])).2)
    (fun z t hz _ hat htT => hnonneg _ _ (hpoint z t hz hat htT) hat htT)
    ρ T hρ (by linarith) haT.le le_rfl
  have hfinal : ρ+(d-c*T) = y := by rw [hlineT]; ring
  rwa [hfinal] at htube

end MathFin.BlackScholes.AmericanPut.Boundary
