/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ActualInteriorRegularity
public import MathFin.BlackScholes.AmericanPut.Boundary.ParabolicMaximum

/-! # Actual-price comparison with locally smooth upper supports

The comparator may have a jump in its second derivative. At each potential
positive maximum it suffices to have a smooth majorant touching the comparator.
The actual price is smooth there because the comparator dominates the payoff.

## Result

Public entry points include `canonicalPrice_no_positive_supported_max`,
`canonicalPrice_le_of_upper_supports`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter Boundary
open scoped Topology ContDiff

theorem canonicalPrice_no_positive_supported_max {k h : ℝ} (hk : 0 < k)
    {F : ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    (hz : z ∈ canonicalContinuationRegion k h)
    (hF : ContDiffAt ℝ 2 F z)
    (hspace : IsLocalMax (fun x => canonicalPrice k h x z.2 - F (x, z.2)) z.1)
    (htime : ∀ᶠ t in 𝓝[<] z.2,
      canonicalPrice k h z.1 t - F (z.1, t) ≤ canonicalPrice k h z.1 z.2 - F z)
    (hpos : F z < canonicalPrice k h z.1 z.2)
    (hsuper : 0 ≤ pricingOperator k h F z) : False := by
  have hp : ContDiffAt ℝ 2 (fun w : ℝ × ℝ => canonicalPrice k h w.1 w.2) z :=
    (canonicalPrice_contDiffAt hk.le hz).of_le (WithTop.coe_le_coe.mpr le_top)
  have hpx : ContDiffAt ℝ 2 (fun x => canonicalPrice k h x z.2) z.1 :=
    hp.comp (f := fun x : ℝ => (x,z.2)) z.1 (by fun_prop)
  have hFx : ContDiffAt ℝ 2 (fun x => F (x,z.2)) z.1 :=
    hF.comp z.1 (show ContDiffAt ℝ 2 (fun x : ℝ => (x,z.2)) z.1 by fun_prop)
  have hpt : DifferentiableAt ℝ (fun t => canonicalPrice k h z.1 t) z.2 :=
    (hp.comp (f := fun t : ℝ => (z.1,t)) z.2 (by fun_prop)).differentiableAt
      (by norm_num)
  have hFt : DifferentiableAt ℝ (fun t => F (z.1,t)) z.2 :=
    (hF.comp z.2 (show ContDiffAt ℝ 2 (fun t : ℝ => (z.1,t)) z.2 by fun_prop)).differentiableAt
      (by norm_num)
  have hdt := deriv_nonneg_at_left_max (hpt.sub hFt) htime
  rw [deriv_sub hpt hFt] at hdt
  have hdx := hspace.deriv_eq_zero
  rw [deriv_fun_sub (hpx.differentiableAt (by norm_num))
    (hFx.differentiableAt (by norm_num))] at hdx
  have hdxx := second_deriv_nonpos_at_local_max hspace (hpx.continuousAt.sub hFx.continuousAt)
  have he : deriv (deriv (fun x => canonicalPrice k h x z.2 - F (x,z.2))) z.1 =
      deriv (deriv (fun x => canonicalPrice k h x z.2)) z.1 -
        deriv (deriv (fun x => F (x,z.2))) z.1 := by
    simpa [iteratedDeriv_succ] using iteratedDeriv_fun_sub (n := 2) hpx hFx
  rw [he] at hdxx
  have hpde := canonicalPrice_pricingOperator hk.le hz
  unfold pricingOperator at hpde hsuper
  dsimp only at hpde
  have hfirst : deriv (fun x => canonicalPrice k h x z.2) z.1 =
      deriv (fun x => F (x,z.2)) z.1 := sub_eq_zero.mp hdx
  rw [hfirst] at hpde
  nlinarith [mul_pos hk (sub_pos.mpr hpos)]

/-- Comparison needs no regularity of the unknown exercise boundary or of the
comparator across its own interfaces. Terminal time is included. -/
theorem canonicalPrice_le_of_upper_supports {k h : ℝ} (hk : 0 < k)
    {U : ℝ × ℝ → ℝ} {L R T : ℝ}
    (hU : ContinuousOn U (Icc L R ×ˢ Icc 0 T))
    (hobstacle : ∀ z ∈ Icc L R ×ˢ Icc 0 T, putPayoff z.1 ≤ U z)
    (hsupport : ∀ z ∈ Ioo L R ×ˢ Ioc 0 T,
      ∃ F : ℝ × ℝ → ℝ, ContDiffAt ℝ 2 F z ∧ F z = U z ∧
        (∀ᶠ w in 𝓝 z, U w ≤ F w) ∧ 0 ≤ pricingOperator k h F z)
    (hbottom : ∀ x ∈ Icc L R, canonicalPrice k h x 0 ≤ U (x, 0))
    (hleft : ∀ t ∈ Icc 0 T, canonicalPrice k h L t ≤ U (L, t))
    (hright : ∀ t ∈ Icc 0 T, canonicalPrice k h R t ≤ U (R, t)) :
    ∀ z ∈ Icc L R ×ˢ Icc 0 T, canonicalPrice k h z.1 z.2 ≤ U z := by
  intro z hz
  by_contra! hpos
  let V : ℝ × ℝ → ℝ := fun w => canonicalPrice k h w.1 w.2 - U w
  have hVc : ContinuousOn V (Icc L R ×ˢ Icc 0 T) :=
    (canonicalPrice_continuous hk.le).continuousOn.sub hU
  obtain ⟨w,hw,hmax⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn ⟨z,hz⟩ hVc
  have hVp : 0 < V w := (sub_pos.mpr hpos).trans_le (hmax hz)
  have hgap : U w < canonicalPrice k h w.1 w.2 := sub_pos.mp hVp
  have hwL : L < w.1 := lt_of_le_of_ne hw.1.1 (by
    intro he
    have hh := hleft w.2 hw.2
    have hwe : (L,w.2) = w := by ext <;> simp [he]
    rw [hwe] at hh
    rw [he] at hh
    linarith)
  have hwR : w.1 < R := lt_of_le_of_ne hw.1.2 (by
    intro he
    have hh := hright w.2 hw.2
    have hwe : (R,w.2) = w := by ext <;> simp [he]
    rw [hwe] at hh
    rw [← he] at hh
    linarith)
  have hwt : 0 < w.2 := lt_of_le_of_ne hw.2.1 (by
    intro he
    have hh := hbottom w.1 hw.1
    have hwe : (w.1,0) = w := by ext <;> simp [he]
    rw [hwe] at hh
    rw [he] at hh
    linarith)
  obtain ⟨F,hF,he,hmajor,hsuper⟩ := hsupport w ⟨⟨hwL,hwR⟩,hwt,hw.2.2⟩
  have hspace : IsLocalMax (fun x => canonicalPrice k h x w.2 - F (x,w.2)) w.1 := by
    have hm := (show Tendsto (fun x : ℝ => (x,w.2)) (𝓝 w.1) (𝓝 w) by
        convert! (continuous_id.prodMk continuous_const).tendsto w.1 using 1).eventually hmajor
    filter_upwards [Ioo_mem_nhds hwL hwR,hm] with x hx hm
    have hh := hmax (show (x,w.2) ∈ Icc L R ×ˢ Icc 0 T from ⟨⟨hx.1.le,hx.2.le⟩,hw.2⟩)
    dsimp [V] at hh
    simpa only [Prod.mk.eta,he] using (sub_le_sub_left hm _).trans hh
  have htime : ∀ᶠ t in 𝓝[<] w.2,
      canonicalPrice k h w.1 t - F (w.1,t) ≤ canonicalPrice k h w.1 w.2 - F w := by
    have hm := (show Tendsto (fun t : ℝ => (w.1,t)) (𝓝 w.2) (𝓝 w) by
        convert! (continuous_const.prodMk continuous_id).tendsto w.2 using 1).eventually hmajor
    filter_upwards [nhdsWithin_le_nhds hm,nhdsWithin_le_nhds (Ioi_mem_nhds hwt),
      self_mem_nhdsWithin] with t hm ht htW
    have hh := hmax (show (w.1,t) ∈ Icc L R ×ˢ Icc 0 T from
      ⟨hw.1,ht.le,(show t < w.2 from htW).le.trans hw.2.2⟩)
    dsimp [V] at hh
    rw [he]
    exact (sub_le_sub_left hm _).trans hh
  exact canonicalPrice_no_positive_supported_max hk
    ⟨hwt,(hobstacle w hw).trans_lt hgap⟩ hF hspace htime (by rwa [he]) hsuper

end MathFin.BlackScholes.AmericanPut.Stopping
