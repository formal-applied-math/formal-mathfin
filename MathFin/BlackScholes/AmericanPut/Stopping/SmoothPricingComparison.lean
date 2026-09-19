/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.PricingTests

/-! # Parabolic comparison from smooth pricing tests

Only the comparator is smooth. A time-weighted maximum avoids applying a
two-sided touching test at terminal time; continuity recovers the terminal slice.

## Result

Public entry points include `pricingOperator`, `SmoothPricingSubsolutionOn`, `pricingOperator_barrier`, `smoothPricingSubsolution_le_before_terminal`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory
open scoped Topology ContDiff

/-- The parabolic operator `∂ₜ F - ∂ₓ∂ₓ F - (k-h-1)*∂ₓ F + k*F`, with `z.1` the space variable
and `z.2` the time variable. -/
noncomputable def pricingOperator (k h : ℝ) (F : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  deriv (fun t => F (z.1,t)) z.2 - deriv (deriv (fun x => F (x,z.2))) z.1 -
    (k-h-1)*deriv (fun x => F (x,z.2)) z.1 + k*F z

/-- The smooth-test subsolution property on `U`: at every `z ∈ U`, every `C³` function `F` that
agrees with `u` at `z` and dominates it nearby satisfies `pricingOperator k h F z ≤ 0`. -/
def SmoothPricingSubsolutionOn (k h : ℝ) (u : ℝ × ℝ → ℝ) (U : Set (ℝ × ℝ)) : Prop :=
  ∀ z ∈ U, ∀ F : ℝ × ℝ → ℝ, ContDiff ℝ 3 F → F z = u z →
    (∀ᶠ y in 𝓝 z, u y ≤ F y) → pricingOperator k h F z ≤ 0

theorem pricingOperator_barrier {F G : ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    (hF : DifferentiableAt ℝ F z) (k h M T : ℝ) (ht : z.2 < T)
    (he : G =ᶠ[𝓝 z] (fun y => F y + M/(T-y.2))) :
    pricingOperator k h G z = pricingOperator k h F z + M/(T-z.2)^2 + k*(M/(T-z.2)) := by
  have hne : T-z.2 ≠ 0 := ne_of_gt (sub_pos.mpr ht)
  have hdt : HasDerivAt (fun t => M/(T-t)) (M/(T-z.2)^2) z.2 := by
    convert! ((((hasDerivAt_const z.2 T).sub (hasDerivAt_id z.2)).inv hne).const_mul M) using 1
    simp [div_eq_mul_inv]
  have hfdt : DifferentiableAt ℝ (fun t => F (z.1,t)) z.2 :=
    hF.comp z.2
      (show DifferentiableAt ℝ (fun t : ℝ => (z.1,t)) z.2 by fun_prop)
  have hsum : HasDerivAt (fun t => F (z.1,t)+M/(T-t))
      (deriv (fun t => F (z.1,t)) z.2+M/(T-z.2)^2) z.2 := hfdt.hasDerivAt.add hdt
  have het : (fun t => G (z.1,t)) =ᶠ[𝓝 z.2] (fun t => F (z.1,t)+M/(T-t)) :=
    he.comp_tendsto (by convert! (continuous_const.prodMk continuous_id).tendsto z.2 using 1)
  have hex : (fun x => G (x,z.2)) =ᶠ[𝓝 z.1] (fun x => F (x,z.2)+M/(T-z.2)) :=
    he.comp_tendsto (by convert! (continuous_id.prodMk continuous_const).tendsto z.1 using 1)
  unfold pricingOperator
  rw [het.deriv_eq,hsum.deriv,
    hex.deriv.deriv_eq,hex.deriv_eq,deriv_add_const',he.self_of_nhds]
  ring

theorem smoothPricingSubsolution_le_before_terminal {k h : ℝ} (hk : 0 ≤ k)
    {u F : ℝ × ℝ → ℝ} {L R a T : ℝ}
    (hu : ContinuousOn u (Icc L R ×ˢ Icc a T))
    (hF : ContinuousOn F (Icc L R ×ˢ Icc a T))
    (hFs : ContDiffOn ℝ 3 F (Ioo L R ×ˢ Ioo a T))
    (hsub : SmoothPricingSubsolutionOn k h u (Ioo L R ×ˢ Ioo a T))
    (hsuper : ∀ z ∈ Ioo L R ×ˢ Ioo a T, 0 ≤ pricingOperator k h F z)
    (hbottom : ∀ x ∈ Icc L R, u (x,a) ≤ F (x,a))
    (hleft : ∀ t ∈ Icc a T, u (L,t) ≤ F (L,t))
    (hright : ∀ t ∈ Icc a T, u (R,t) ≤ F (R,t)) :
    ∀ z ∈ Icc L R ×ˢ Ico a T, u z ≤ F z := by
  intro z hz
  by_contra! hpos
  let Q := Icc L R ×ˢ Icc a T
  let V : ℝ × ℝ → ℝ := fun y => (T-y.2)*(u y-F y)
  have hzQ : z ∈ Q := ⟨hz.1,hz.2.1,hz.2.2.le⟩
  have hVc : ContinuousOn V Q :=
    (continuousOn_const.sub continuousOn_snd).mul (hu.sub hF)
  obtain ⟨w,hw,hmax⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn ⟨z,hzQ⟩ hVc
  have hVp : 0 < V w := (mul_pos (sub_pos.mpr hz.2.2) (sub_pos.mpr hpos)).trans_le (hmax hzQ)
  have hwT : w.2 < T := lt_of_le_of_ne hw.2.2 (by
    intro he
    have hv0 : V w = 0 := by simp [V,he]
    linarith)
  have hgap : 0 < u w-F w := (mul_pos_iff.mp hVp).resolve_right (by
    intro hn; linarith [hn.1]) |>.2
  have hwL : L < w.1 := lt_of_le_of_ne hw.1.1 (by
    intro he
    have hh := hleft w.2 hw.2
    have hwe : (L,w.2) = w := by ext <;> simp [he]
    rw [hwe] at hh
    linarith)
  have hwR : w.1 < R := lt_of_le_of_ne hw.1.2 (by
    intro he
    have hh := hright w.2 hw.2
    have hwe : (R,w.2) = w := by ext <;> simp [he]
    rw [hwe] at hh
    linarith)
  have hwa : a < w.2 := lt_of_le_of_ne hw.2.1 (by
    intro he
    have hh := hbottom w.1 hw.1
    have hwe : (w.1,a) = w := by ext <;> simp [he]
    rw [hwe] at hh
    linarith)
  have hwint : w ∈ Ioo L R ×ˢ Ioo a T := ⟨⟨hwL,hwR⟩,hwa,hwT⟩
  have hnear : Ioo L R ×ˢ Ioo a T ∈ 𝓝 w :=
    (isOpen_Ioo.prod isOpen_Ioo).mem_nhds hwint
  have hne : T-w.2 ≠ 0 := ne_of_gt (sub_pos.mpr hwT)
  have hlocal : ContDiffOn ℝ 3 (fun y : ℝ × ℝ => F y+V w/(T-y.2))
      (Ioo L R ×ˢ Ioo a T) :=
    hFs.add (contDiffOn_const.div (contDiffOn_const.sub contDiffOn_snd)
      (fun y hy => ne_of_gt (sub_pos.mpr hy.2.2)))
  obtain ⟨G,hG,_hc,heG⟩ := exists_compact_set_localization (isCompact_singleton (x := w))
    (isOpen_Ioo.prod isOpen_Ioo) (singleton_subset_iff.mpr hwint) hlocal
  have he : G =ᶠ[𝓝 w] (fun y => F y+V w/(T-y.2)) :=
    heG.filter_mono (nhds_le_nhdsSet (mem_singleton w))
  have hG0 : G w = u w := by
    rw [he.self_of_nhds]
    dsimp [V]
    field_simp
    ring
  have htouch : ∀ᶠ y in 𝓝 w, u y ≤ G y := by
    filter_upwards [hnear,he] with y hy heq
    rw [heq]
    have hyQ : y ∈ Q := ⟨⟨hy.1.1.le,hy.1.2.le⟩,hy.2.1.le,hy.2.2.le⟩
    have hh := hmax hyQ
    have hden : 0 < T-y.2 := sub_pos.mpr hy.2.2
    have hd : u y-F y ≤ V w/(T-y.2) := (le_div_iff₀ hden).mpr (by
      simpa only [mem_ofPred_eq,V,mul_comm] using hh)
    linarith
  have htest := hsub w hwint G hG hG0 htouch
  rw [pricingOperator_barrier ((hFs.contDiffAt hnear).differentiableAt (by norm_num))
    k h (V w) T hwT he] at htest
  have hstrict : 0 < V w/(T-w.2)^2 := div_pos hVp (sq_pos_of_pos (sub_pos.mpr hwT))
  have hnonneg : 0 ≤ k*(V w/(T-w.2)) := mul_nonneg hk (div_pos hVp (sub_pos.mpr hwT)).le
  linarith [hsuper w hwint]

/-- Comparison on the full closed cylinder, including terminal time. Only
initial and lateral boundary inequalities are assumed. -/
theorem smoothPricingSubsolution_le {k h : ℝ} (hk : 0 ≤ k)
    {u F : ℝ × ℝ → ℝ} {L R a T : ℝ} (haT : a < T)
    (hu : ContinuousOn u (Icc L R ×ˢ Icc a T))
    (hF : ContinuousOn F (Icc L R ×ˢ Icc a T))
    (hFs : ContDiffOn ℝ 3 F (Ioo L R ×ˢ Ioo a T))
    (hsub : SmoothPricingSubsolutionOn k h u (Ioo L R ×ˢ Ioo a T))
    (hsuper : ∀ z ∈ Ioo L R ×ˢ Ioo a T, 0 ≤ pricingOperator k h F z)
    (hbottom : ∀ x ∈ Icc L R, u (x,a) ≤ F (x,a))
    (hleft : ∀ t ∈ Icc a T, u (L,t) ≤ F (L,t))
    (hright : ∀ t ∈ Icc a T, u (R,t) ≤ F (R,t)) :
    ∀ z ∈ Icc L R ×ˢ Icc a T, u z ≤ F z := by
  have he : closure (Icc L R ×ˢ Ico a T) = Icc L R ×ˢ Icc a T := by
    rw [closure_prod_eq,isClosed_Icc.closure_eq,closure_Ico haT.ne]
  have hh := smoothPricingSubsolution_le_before_terminal hk hu hF hFs hsub hsuper hbottom hleft hright
  intro z hz
  apply le_on_closure hh
  · rwa [he]
  · rwa [he]
  · rwa [he]

end MathFin.BlackScholes.AmericanPut.Stopping
