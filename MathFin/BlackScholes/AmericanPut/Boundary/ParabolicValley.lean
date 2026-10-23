/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.SmoothValley
public import MathFin.BlackScholes.AmericanPut.Boundary.OrderedTriples

/-!
# A direct maximum principle for a positive valley

The proof uses an ordered triple of spatial points, not a zero-number theorem.
Strict monotonicity of the smooth detector forces spatial maxima at its two
endpoints and a spatial minimum in the middle at a positive contact maximum.
The equation without a zero-order term then gives incompatible time signs.

## Result

Public entry points include `second_deriv_nonneg_at_local_min`, `valleyOnTriple`,
`valleyOnTriple_continuousOn`, `parabolic_smoothValley_nonpos`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set Filter
open scoped Topology ContDiff

theorem second_deriv_nonneg_at_local_min {F : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMin F x) (hc : ContinuousAt F x) : 0 ≤ deriv (deriv F) x := by
  by_contra hn
  have hneg := lt_of_not_ge hn
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hm.deriv_eq_zero hc
  have he : F =ᶠ[𝓝 x] (fun _ => F x) := by
    filter_upwards [hm,hmax] with y hy hy'
    exact le_antisymm hy' hy
  have hz := he.deriv.deriv_eq
  simp only [deriv_const'] at hz
  linarith

/-- The smooth valley detector of `U` at the three points of `w`, less the time penalty
`η * t` taken at the first point. -/
noncomputable def valleyOnTriple (U : ℝ → ℝ → ℝ) (δ η : ℝ) (w : SpaceTimeTriple) : ℝ :=
  smoothValley δ (U w.1.1 w.1.2) (U w.2.1.1 w.2.1.2) (U w.2.2.1 w.2.2.2) - η*w.1.2

theorem valleyOnTriple_continuousOn {U : ℝ → ℝ → ℝ} {Q : Set (ℝ × ℝ)}
    (hU : ContinuousOn (fun z : ℝ × ℝ => U z.1 z.2) Q) (δ η : ℝ) :
    ContinuousOn (valleyOnTriple U δ η) (orderedTriples Q) := by
  have hx : ContinuousOn (fun w : SpaceTimeTriple => U w.1.1 w.1.2) (orderedTriples Q) :=
    hU.comp (by fun_prop) (fun _ hw => hw.1.1)
  have hy : ContinuousOn (fun w : SpaceTimeTriple => U w.2.1.1 w.2.1.2) (orderedTriples Q) :=
    hU.comp (by fun_prop) (fun _ hw => hw.1.2.1)
  have hz : ContinuousOn (fun w : SpaceTimeTriple => U w.2.2.1 w.2.2.2) (orderedTriples Q) :=
    hU.comp (by fun_prop) (fun _ hw => hw.1.2.2)
  unfold valleyOnTriple smoothValley smoothMinimum smoothPositive
  exact ((hx.sub
      (((hx.sub hz).add (((hx.sub hz).pow 2).add continuousOn_const).sqrt).div_const 2)).sub
    ((hy.add ((hy.pow 2).add continuousOn_const).sqrt).div_const 2)).sub
    (continuousOn_const.mul
        (show ContinuousOn (fun w : SpaceTimeTriple => w.1.2) (orderedTriples Q) by fun_prop))

/-- No positive maximum of the smoothed valley detector minus a strictly
increasing time penalty. Initial data need only be continuous and satisfy the
three-point shape inequality; no initial derivative convergence is required. -/
theorem parabolic_smoothValley_nonpos {U D : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {R T δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 < η)
    (hb : ContinuousOn b (Icc 0 T)) (hbR : ∀ t ∈ Icc 0 T, b t ≤ R)
    (hU : ContinuousOn (fun z : ℝ × ℝ => U z.1 z.2) (movingStrip b R 0 T))
    (hs : ∀ x t, 0 < t → t ≤ T → b t < x → x < R →
      ContDiffAt ℝ 2 (fun z : ℝ × ℝ => U z.1 z.2) (x,t))
    (hpde : ∀ x t, 0 < t → t ≤ T → b t < x → x < R →
      deriv (U x) t = deriv (deriv (fun y => U y t)) x + D x t * deriv (fun y => U y t) x)
    (hleft : ∀ t, 0 ≤ t → t ≤ T → U (b t) t ≤ 0)
    (hright : ∀ t, 0 ≤ t → t ≤ T → U R t ≤ 0)
    (hinit : ∀ x y z, b 0 ≤ x → x ≤ y → y ≤ z → z ≤ R →
      min (U x 0) (U z 0) ≤ max (U y 0) 0) :
    ∀ w ∈ orderedTriples (movingStrip b R 0 T), valleyOnTriple U δ η w ≤ 0 := by
  intro q hq
  by_contra hn
  have hpos : 0 < valleyOnTriple U δ η q := lt_of_not_ge hn
  have hK := orderedTriples_isCompact (movingStrip_isCompact hb hbR)
  obtain ⟨w,hw,hmax⟩ := hK.exists_isMaxOn ⟨q,hq⟩ (valleyOnTriple_continuousOn hU δ η)
  have hwpos := hpos.trans_le (hmax hq)
  rcases w with ⟨⟨x,t⟩,⟨y,s⟩,⟨z,r⟩⟩
  rcases hw with ⟨⟨hwx,hwy,hwz⟩,h12,h13,hxy,hyz⟩
  change t = s at h12
  change t = r at h13
  subst s
  subst r
  change 0 ≤ t ∧ t ≤ T ∧ b t ≤ x ∧ x ≤ R at hwx
  change 0 ≤ t ∧ t ≤ T ∧ b t ≤ z ∧ z ≤ R at hwz
  change x ≤ y at hxy
  change y ≤ z at hyz
  change 0 < smoothValley δ (U x t) (U y t) (U z t) - η*t at hwpos
  have hgap : max (U y t) 0 < min (U x t) (U z t) := by
    have hh := (smoothValley_bounds hδ.le (U x t) (U y t) (U z t)).2
    nlinarith [mul_nonneg hη.le hwx.1]
  have hxp : 0 < U x t := (le_max_right _ _).trans_lt (hgap.trans_le (min_le_left _ _))
  have hzp : 0 < U z t := (le_max_right _ _).trans_lt (hgap.trans_le (min_le_right _ _))
  have hxy' : x < y := lt_of_le_of_ne hxy (by
    intro he; subst y; linarith [min_le_left (U x t) (U z t),le_max_left (U x t) 0])
  have hyz' : y < z := lt_of_le_of_ne hyz (by
    intro he; subst z; linarith [min_le_right (U x t) (U y t),le_max_left (U y t) 0])
  have ht : 0 < t := lt_of_le_of_ne hwx.1 (by
    intro he; subst t
    exact (not_lt_of_ge (hinit x y z hwx.2.2.1 hxy hyz hwz.2.2.2)) hgap)
  have hbx : b t < x := lt_of_le_of_ne hwx.2.2.1 (by
    intro he; have hh := hleft t hwx.1 hwx.2.1; rw [he] at hh; linarith)
  have hzR : z < R := lt_of_le_of_ne hwz.2.2.2 (by
    intro he; have hh := hright t hwx.1 hwx.2.1; rw [← he] at hh; linarith)
  have hmX : IsLocalMax (fun a => U a t) x := by
    filter_upwards [Ioo_mem_nhds hbx hxy'] with a ha
    have hh := hmax (sameTimeTriple_mem hwx.1 hwx.2.1 ha.1.le ha.2.le hyz hzR.le)
    change smoothValley δ (U a t) (U y t) (U z t)-η*t ≤
      smoothValley δ (U x t) (U y t) (U z t)-η*t at hh
    apply (smoothMinimum_strictMono_left hδ (U z t)).le_iff_le.mp
    unfold smoothValley at hh
    linarith
  have hmZ : IsLocalMax (fun a => U a t) z := by
    filter_upwards [Ioo_mem_nhds hyz' hzR] with a ha
    have hh := hmax (sameTimeTriple_mem hwx.1 hwx.2.1 hbx.le hxy ha.1.le ha.2.le)
    change smoothValley δ (U x t) (U y t) (U a t)-η*t ≤
      smoothValley δ (U x t) (U y t) (U z t)-η*t at hh
    apply (smoothMinimum_strictMono_right hδ (U x t)).le_iff_le.mp
    unfold smoothValley at hh
    linarith
  have hmY : IsLocalMin (fun a => U a t) y := by
    filter_upwards [Ioo_mem_nhds hxy' hyz'] with a ha
    have hh := hmax (sameTimeTriple_mem hwx.1 hwx.2.1 hbx.le ha.1.le ha.2.le hzR.le)
    change smoothValley δ (U x t) (U a t) (U z t)-η*t ≤
      smoothValley δ (U x t) (U y t) (U z t)-η*t at hh
    apply (smoothPositive_strictMono hδ).le_iff_le.mp
    unfold smoothValley at hh
    linarith
  have hxR := (hxy'.trans hyz').trans hzR
  have hby := hbx.trans hxy'
  have hyR := hyz'.trans hzR
  have hbz := hby.trans hyz'
  have hcx : ContinuousAt (fun a => U a t) x := by
    exact Tendsto.comp (g := fun q : ℝ × ℝ => U q.1 q.2) (f := fun a : ℝ => (a,t))
      (hs x t ht hwx.2.1 hbx hxR).continuousAt
      (show ContinuousAt (fun a : ℝ => (a,t)) x by fun_prop)
  have hcy : ContinuousAt (fun a => U a t) y := by
    exact Tendsto.comp (g := fun q : ℝ × ℝ => U q.1 q.2) (f := fun a : ℝ => (a,t))
      (hs y t ht hwx.2.1 hby hyR).continuousAt
      (show ContinuousAt (fun a : ℝ => (a,t)) y by fun_prop)
  have hcz : ContinuousAt (fun a => U a t) z := by
    exact Tendsto.comp (g := fun q : ℝ × ℝ => U q.1 q.2) (f := fun a : ℝ => (a,t))
      (hs z t ht hwx.2.1 hbz hzR).continuousAt
      (show ContinuousAt (fun a : ℝ => (a,t)) z by fun_prop)
  have htx : deriv (U x) t ≤ 0 := by
    rw [hpde x t ht hwx.2.1 hbx hxR,hmX.deriv_eq_zero,mul_zero,add_zero]
    exact second_deriv_nonpos_at_local_max hmX hcx
  have htz : deriv (U z) t ≤ 0 := by
    rw [hpde z t ht hwx.2.1 hbz hzR,hmZ.deriv_eq_zero,mul_zero,add_zero]
    exact second_deriv_nonpos_at_local_max hmZ hcz
  have hty : 0 ≤ deriv (U y) t := by
    rw [hpde y t ht hwx.2.1 hby hyR,hmY.deriv_eq_zero,mul_zero,add_zero]
    exact second_deriv_nonneg_at_local_min hmY hcy
  have hdt (a : ℝ) (hba : b t < a) (haR : a < R) : HasDerivAt (U a) (deriv (U a) t) t :=
    ((hs a t ht hwx.2.1 hba haR).comp t
      (show ContDiffAt ℝ 2 (fun s : ℝ => (a,s)) t by fun_prop)).differentiableAt
          (by norm_num) |>.hasDerivAt
  have hd := (smoothValley_hasDeriv hδ (hdt x hbx hxR) (hdt y hby hyR) (hdt z hbz hzR)).sub
    ((hasDerivAt_id t).const_mul η)
  have htime : ∀ᶠ s in 𝓝[<] t, 0 ≤ s ∧ s ≤ T := by
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds ht),self_mem_nhdsWithin] with s hs hst
    exact ⟨hs.le,(show s < t from hst).le.trans hwx.2.1⟩
  have hbs : ∀ᶠ s in 𝓝[<] t, b s < x :=
    ((hb t ⟨hwx.1,hwx.2.1⟩).mono_left
      (le_inf nhdsWithin_le_nhds (le_principal_iff.mpr htime))).eventually (Iio_mem_nhds hbx)
  have htm : ∀ᶠ s in 𝓝[<] t,
      smoothValley δ (U x s) (U y s) (U z s)-η*s ≤ smoothValley δ (U x t) (U y t) (U z t)-η*t := by
    filter_upwards [htime,hbs] with s hs hsb
    exact hmax (sameTimeTriple_mem hs.1 hs.2 hsb.le hxy hyz hzR.le)
  have hnonneg := deriv_nonneg_at_left_max hd.differentiableAt htm
  rw [hd.deriv] at hnonneg
  have hdx := smoothPositiveSlope_bounds hδ (U x t-U z t)
  have hdy := smoothPositiveSlope_bounds hδ (U y t)
  have htermx := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hdx.2.le) htx
  have htermz := mul_nonpos_of_nonneg_of_nonpos hdx.1.le htz
  have htermy := mul_nonneg hdy.1.le hty
  linarith

end MathFin.BlackScholes.AmericanPut.Boundary
