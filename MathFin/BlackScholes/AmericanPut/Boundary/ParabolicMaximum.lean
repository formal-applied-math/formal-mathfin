/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Topology.Order.Compact

/-!
# A weak parabolic maximum principle

This module proves, rather than assumes, the elementary maximum principle
needed in Steps 4 and 5. The terminal time is included. The moving left boundary
needs continuity, not a bounded velocity at expiry.

## Result

Public entry points include `second_deriv_nonpos_at_local_max`, `deriv_nonneg_at_left_max`,
`movingStrip`, `movingStrip_isCompact`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set Filter
open scoped Topology

/-- A local spatial maximum has nonpositive second derivative. Continuity of
the function suffices; if the second derivative were positive, the second
derivative test and the maximum would make the function locally constant. -/
theorem second_deriv_nonpos_at_local_max {f : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra hn
  have hp : 0 < deriv (deriv f) x := lt_of_not_ge hn
  have hmin := isLocalMin_of_deriv_deriv_pos hp hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hm, hmin] with y hy hy'
    exact le_antisymm hy hy'
  have hzero := he.deriv.deriv_eq
  simp only [deriv_const'] at hzero
  linarith

/-- At a maximum over a left-hand time neighborhood, the ordinary time
derivative is nonnegative. This includes a terminal-time maximum. -/
theorem deriv_nonneg_at_left_max {f : ℝ → ℝ} {t : ℝ}
    (hd : DifferentiableAt ℝ f t)
    (hm : ∀ᶠ s in 𝓝[<] t, f s ≤ f t) : 0 ≤ deriv f t := by
  have hs := hd.hasDerivAt.tendsto_slope.mono_left (nhdsLT_le_nhdsNE t)
  apply ge_of_tendsto hs
  filter_upwards [hm, self_mem_nhdsWithin] with s hs (hst : s < t)
  simpa only [slope, vsub_eq_sub, smul_eq_mul, div_eq_inv_mul] using
    div_nonneg_of_nonpos (sub_nonpos.mpr hs) (sub_nonpos.mpr hst.le)

/-- Closed space-time strip with a moving left endpoint and fixed right end. -/
def movingStrip (b : ℝ → ℝ) (R a T : ℝ) : Set (ℝ × ℝ) :=
  {z | a ≤ z.2 ∧ z.2 ≤ T ∧ b z.2 ≤ z.1 ∧ z.1 ≤ R}

/-- Parameterizing each spatial section by the unit interval proves
compactness without differentiating the moving boundary. -/
theorem movingStrip_isCompact {b : ℝ → ℝ} {R a T : ℝ}
    (hb : ContinuousOn b (Icc a T)) (hR : ∀ t ∈ Icc a T, b t ≤ R) :
    IsCompact (movingStrip b R a T) := by
  let F : ℝ × ℝ → ℝ × ℝ := fun z => (b z.2 + (R - b z.2) * z.1, z.2)
  have hbc : ContinuousOn (fun z : ℝ × ℝ => b z.2) (Icc (0 : ℝ) 1 ×ˢ Icc a T) :=
    hb.comp continuousOn_snd (fun _ hz => hz.2)
  have hF : ContinuousOn F (Icc (0 : ℝ) 1 ×ˢ Icc a T) :=
    (hbc.add ((continuousOn_const.sub hbc).mul continuousOn_fst)).prodMk continuousOn_snd
  have heq : F '' (Icc (0 : ℝ) 1 ×ˢ Icc a T) = movingStrip b R a T := by
    ext z
    constructor
    · rintro ⟨⟨s,t⟩, ⟨hs,ht⟩, rfl⟩
      have hRt := hR t ht
      refine ⟨ht.1, ht.2, ?_, ?_⟩ <;> dsimp [F] <;> nlinarith [hs.1, hs.2]
    · intro hz
      obtain ⟨ha,hT,hb',hR'⟩ := hz
      by_cases he : b z.2 = R
      · refine ⟨(0,z.2), ⟨by norm_num, ha, hT⟩, ?_⟩
        have hx : z.1 = b z.2 := by linarith
        ext <;> simp [F, hx]
      · have hwidth : 0 < R - b z.2 := sub_pos.mpr (lt_of_le_of_ne (hR z.2 ⟨ha,hT⟩) he)
        refine ⟨((z.1 - b z.2) / (R - b z.2),z.2), ⟨?_, ha, hT⟩, ?_⟩
        · exact ⟨div_nonneg (sub_nonneg.mpr hb') hwidth.le,
            (div_le_one hwidth).mpr (by linarith)⟩
        · ext <;> dsimp [F]
          · field_simp
            ring
  rw [← heq]
  exact (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn hF

/-- A strictly subcaloric function cannot have a positive maximum away from
the initial or lateral boundary. Compactness is supplied separately so this
lemma can also be reused for other compact space-time geometries. -/
theorem strict_parabolic_maximum {u D : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {R a T : ℝ}
    (hQ : IsCompact (movingStrip b R a T))
    (hb : ContinuousOn b (Icc a T))
    (hu : ContinuousOn (fun z : ℝ × ℝ => u z.1 z.2) (movingStrip b R a T))
    (htd : ∀ x t, a < t → t ≤ T → b t < x → x < R → DifferentiableAt ℝ (u x) t)
    (hpde : ∀ x t, a < t → t ≤ T → b t < x → x < R →
      deriv (u x) t < deriv (deriv (fun y => u y t)) x + D x t * deriv (fun y => u y t) x)
    (hinitial : ∀ x, b a ≤ x → x ≤ R → u x a ≤ 0)
    (hleft : ∀ t, a ≤ t → t ≤ T → u (b t) t ≤ 0)
    (hright : ∀ t, a ≤ t → t ≤ T → u R t ≤ 0) :
    ∀ z ∈ movingStrip b R a T, u z.1 z.2 ≤ 0 := by
  intro z hz
  by_contra hn
  have hzpos : 0 < u z.1 z.2 := lt_of_not_ge hn
  obtain ⟨w, hw, hmax⟩ := hQ.exists_isMaxOn ⟨z, hz⟩ hu
  have hwpos : 0 < u w.1 w.2 := hzpos.trans_le (hmax hz)
  obtain ⟨hwa, hwT, hwb, hwR⟩ := hw
  have hat : a < w.2 := lt_of_le_of_ne hwa (by
    intro he; have hh := hinitial w.1 (by simpa [← he] using hwb) hwR
    have : u w.1 w.2 ≤ 0 := by simpa [he] using hh
    linarith)
  have hbx : b w.2 < w.1 := lt_of_le_of_ne hwb (by
    intro he; have := hleft w.2 hwa hwT; rw [he] at this; linarith)
  have hxR : w.1 < R := lt_of_le_of_ne hwR (by
    intro he; have := hright w.2 hwa hwT; rw [← he] at this; linarith)
  have hspace : ∀ᶠ y in 𝓝 w.1, (y, w.2) ∈ movingStrip b R a T := by
    filter_upwards [Ioo_mem_nhds hbx hxR] with y hy
    exact ⟨hwa, hwT, hy.1.le, hy.2.le⟩
  have hmspace : IsLocalMax (fun y => u y w.2) w.1 := by
    filter_upwards [hspace] with y hy
    exact hmax hy
  have hcspace : ContinuousAt (fun y => u y w.2) w.1 := by
    exact Tendsto.comp (hu w ⟨hwa, hwT, hwb, hwR⟩) (tendsto_nhdsWithin_iff.mpr
      ⟨continuousAt_id.prodMk continuousAt_const, hspace⟩)
  have hbcont := hb w.2 ⟨hwa, hwT⟩
  have htime : ∀ᶠ s in 𝓝[<] w.2, (w.1, s) ∈ movingStrip b R a T := by
    have hi : ∀ᶠ s in 𝓝[<] w.2, s ∈ Icc a T := by
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hat), self_mem_nhdsWithin] with s hs hs'
      exact ⟨hs.le, (show s < w.2 from hs').le.trans hwT⟩
    have hbsmall : ∀ᶠ s in 𝓝[<] w.2, b s < w.1 :=
      (hbcont.mono_left (le_inf nhdsWithin_le_nhds (le_principal_iff.mpr hi))).eventually
        (Iio_mem_nhds hbx)
    filter_upwards [hi, hbsmall] with s hs hbs
    exact ⟨hs.1, hs.2, hbs.le, hwR⟩
  have hmt : ∀ᶠ s in 𝓝[<] w.2, u w.1 s ≤ u w.1 w.2 := by
    filter_upwards [htime] with s hs
    exact hmax hs
  have hdt := deriv_nonneg_at_left_max (htd w.1 w.2 hat hwT hbx hxR) hmt
  have hdxx := second_deriv_nonpos_at_local_max hmspace hcspace
  have hineq := hpde w.1 w.2 hat hwT hbx hxR
  rw [hmspace.deriv_eq_zero, mul_zero, add_zero] at hineq
  linarith

/-- Weak maximum principle for `u_t <= u_xx + D*u_x` on a continuous
moving strip. No coefficient bound or boundary derivative is needed here:
at an interior spatial maximum the drift term vanishes exactly. -/
theorem parabolic_maximum {u D : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {R a T : ℝ}
    (hb : ContinuousOn b (Icc a T)) (hR : ∀ t ∈ Icc a T, b t ≤ R)
    (hu : ContinuousOn (fun z : ℝ × ℝ => u z.1 z.2) (movingStrip b R a T))
    (htd : ∀ x t, a < t → t ≤ T → b t < x → x < R → DifferentiableAt ℝ (u x) t)
    (hpde : ∀ x t, a < t → t ≤ T → b t < x → x < R →
      deriv (u x) t ≤ deriv (deriv (fun y => u y t)) x + D x t * deriv (fun y => u y t) x)
    (hinitial : ∀ x, b a ≤ x → x ≤ R → u x a ≤ 0)
    (hleft : ∀ t, a ≤ t → t ≤ T → u (b t) t ≤ 0)
    (hright : ∀ t, a ≤ t → t ≤ T → u R t ≤ 0) :
    ∀ z ∈ movingStrip b R a T, u z.1 z.2 ≤ 0 := by
  intro z hz
  by_contra hn
  have hpos : 0 < u z.1 z.2 := lt_of_not_ge hn
  have htime : 0 < z.2 - a + 1 := by have := hz.1; linarith
  let ε := u z.1 z.2 / (2 * (z.2 - a + 1))
  have hε : 0 < ε := div_pos hpos (by positivity)
  let v : ℝ → ℝ → ℝ := fun x t => u x t - ε * (t - a + 1)
  have hv : ContinuousOn (fun z : ℝ × ℝ => v z.1 z.2) (movingStrip b R a T) :=
    hu.sub
        (continuousOn_const.mul ((continuousOn_snd.sub continuousOn_const).add continuousOn_const))
  have hdt (x t : ℝ) (hat : a < t) (htT : t ≤ T) (hbx : b t < x) (hxR : x < R) :
      HasDerivAt (v x) (deriv (u x) t - ε) t := by
    convert! (htd x t hat htT hbx hxR).hasDerivAt.sub
      (((hasDerivAt_id t).sub_const a).add_const 1 |>.const_mul ε) using 1
    simp
  have hstrict (x t : ℝ) (hat : a < t) (htT : t ≤ T) (hbx : b t < x) (hxR : x < R) :
      deriv (v x) t < deriv (deriv (fun y => v y t)) x + D x t * deriv (fun y => v y t) x := by
    rw [(hdt x t hat htT hbx hxR).deriv]
    simp only [v, deriv_sub_const_fun]
    have := hpde x t hat htT hbx hxR
    linarith
  have hvnonpos := strict_parabolic_maximum (movingStrip_isCompact hb hR) hb hv
    (fun x t hat htT hbx hxR => (hdt x t hat htT hbx hxR).differentiableAt) hstrict
    (fun x hbx hxR => by dsimp [v]; have := hinitial x hbx hxR; nlinarith)
    (fun t hat htT => by
      dsimp [v]
      have := hleft t hat htT
      have : 0 ≤ ε * (t - a + 1) := mul_nonneg hε.le (by linarith)
      linarith)
    (fun t hat htT => by
      dsimp [v]
      have := hright t hat htT
      have : 0 ≤ ε * (t - a + 1) := mul_nonneg hε.le (by linarith)
      linarith) z hz
  have he : ε * (z.2 - a + 1) = u z.1 z.2 / 2 := by
    dsimp [ε]
    field_simp
  dsimp [v] at hvnonpos
  rw [he] at hvnonpos
  linarith

end MathFin.BlackScholes.AmericanPut.Boundary
