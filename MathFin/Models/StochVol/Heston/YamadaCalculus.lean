/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Models.StochVol.Heston.YamadaSmoothing
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Yamada Calculus

Calculus for the explicit Yamada smoothing profile.

## Main results

* `yamada_sub_le_phi_of_nonneg`
* `yamada_sub_le_phi`
* `yamada_phi_approx_bounds`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

noncomputable section
namespace MathFin.Heston
open Real Set Filter MeasureTheory
open scoped Topology

theorem yamada_hasDerivAt_if_lt {f g : Real → Real} {a d : Real}
    (hf : HasDerivAt f d a) (hg : HasDerivAt g d a) (hfg : f a = g a) :
    HasDerivAt (fun x => if x < a then f x else g x) d a := by
  rw [hasDerivAt_iff_tendsto_slope]
  have he : slope (fun x => if x < a then f x else g x) a =
      fun x => if x < a then slope f a x else slope g a x := by
    funext x
    by_cases hx : x < a
    · simp [slope, hx, hfg]
    · simp [slope, hx]
  rw [he]
  exact (hasDerivAt_iff_tendsto_slope.mp hf).if' (hasDerivAt_iff_tendsto_slope.mp hg)

theorem yamada_rawPsi_a (p : YamadaParams) : yamada_rawPsi p p.a = 0 := by
  simp [yamada_rawPsi, yamada_logCoord_a]

theorem yamada_rawPsi_b (p : YamadaParams) : yamada_rawPsi p p.b = 0 := by
  simp [yamada_rawPsi, yamada_logCoord_b]

theorem yamada_psi_a (p : YamadaParams) : yamada_psi p p.a = 0 := by
  rw [yamada_psi_of_mem p ⟨le_rfl, p.hab.le⟩, yamada_rawPsi_a]

theorem yamada_psi_b (p : YamadaParams) : yamada_psi p p.b = 0 := by
  rw [yamada_psi_of_mem p ⟨p.hab.le, le_rfl⟩, yamada_rawPsi_b]

theorem yamada_continuousAt_rawPsi (p : YamadaParams) {x : Real} (hx : 0 < x) :
    ContinuousAt (yamada_rawPsi p) x := by
  have hc : ContinuousAt (yamada_logCoord p) x :=
    ((Real.continuousAt_log hx.ne').sub continuousAt_const).div_const _
  exact ((continuousAt_const.mul hc).mul (continuousAt_const.sub hc)).div
    (continuousAt_const.mul continuousAt_id) (mul_ne_zero (yamada_m_ne_zero p) hx.ne')

theorem yamada_continuous_psi (p : YamadaParams) : Continuous (yamada_psi p) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases lt_trichotomy x p.a with hx | rfl | hax
  · have he : yamada_psi p =ᶠ[𝓝 x] fun _ => (0 : Real) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact yamada_psi_of_lt p hy
    exact continuousAt_const.congr_of_eventuallyEq he
  · rw [ContinuousAt, yamada_psi_a]
    have hc := yamada_continuousAt_rawPsi p p.ha_pos
    rw [ContinuousAt, yamada_rawPsi_a] at hc
    exact hc.if' tendsto_const_nhds
  · rcases lt_trichotomy x p.b with hxb | rfl | hbx
    · have he : yamada_psi p =ᶠ[𝓝 x] yamada_rawPsi p := by
        filter_upwards [Ioo_mem_nhds hax hxb] with y hy
        exact yamada_psi_of_mem p ⟨hy.1.le, hy.2.le⟩
      exact (yamada_continuousAt_rawPsi p (p.ha_pos.trans hax)).congr_of_eventuallyEq he
    · rw [ContinuousAt, yamada_psi_b]
      have hc := yamada_continuousAt_rawPsi p (p.ha_pos.trans p.hab)
      rw [ContinuousAt, yamada_rawPsi_b] at hc
      exact hc.if' tendsto_const_nhds
    · have he : yamada_psi p =ᶠ[𝓝 x] fun _ => (0 : Real) := by
        filter_upwards [Ioi_mem_nhds hbx] with y hy
        exact yamada_psi_of_gt p hy
      exact continuousAt_const.congr_of_eventuallyEq he

theorem yamada_hasDerivAt_phiPrime_pos (p : YamadaParams) (x : Real) :
    HasDerivAt (yamada_phiPrime_pos p) (yamada_psi p x) x := by
  rcases lt_trichotomy x p.a with hx | rfl | hax
  · have he : yamada_phiPrime_pos p =ᶠ[𝓝 x] fun _ => (0 : Real) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact yamada_phiPrime_pos_of_lt p hy
    rw [yamada_psi_of_lt p hx]
    exact (hasDerivAt_const x (0 : Real)).congr_of_eventuallyEq he
  · have hr : HasDerivAt (yamada_rawPrim p) 0 p.a := by
      simpa only [yamada_rawPsi_a] using yamada_hasDerivAt_rawPrim p p.ha_pos
    have hd := yamada_hasDerivAt_if_lt (hasDerivAt_const p.a (0 : Real)) hr
      (yamada_rawPrim_a p).symm
    have he : yamada_phiPrime_pos p =ᶠ[𝓝 p.a]
        fun y => if y < p.a then 0 else yamada_rawPrim p y := by
      filter_upwards [Iio_mem_nhds p.hab] with y hy
      simp only [yamada_phiPrime_pos, ite_eq_left (show y ≤ p.b from le_of_lt hy)]
    rw [yamada_psi_a]
    exact hd.congr_of_eventuallyEq he
  · rcases lt_trichotomy x p.b with hxb | rfl | hbx
    · have he : yamada_phiPrime_pos p =ᶠ[𝓝 x] yamada_rawPrim p := by
        filter_upwards [Ioo_mem_nhds hax hxb] with y hy
        exact yamada_phiPrime_pos_of_mem p ⟨hy.1.le, hy.2.le⟩
      rw [yamada_psi_of_mem p ⟨hax.le, hxb.le⟩]
      exact (yamada_hasDerivAt_rawPrim p (p.ha_pos.trans hax)).congr_of_eventuallyEq he
    · have hr : HasDerivAt (yamada_rawPrim p) 0 p.b := by
        simpa only [yamada_rawPsi_b] using yamada_hasDerivAt_rawPrim p (p.ha_pos.trans p.hab)
      have hd := yamada_hasDerivAt_if_lt hr (hasDerivAt_const p.b (1 : Real))
        (yamada_rawPrim_b p)
      have he : yamada_phiPrime_pos p =ᶠ[𝓝 p.b]
          fun y => if y < p.b then yamada_rawPrim p y else 1 := by
        filter_upwards [Ioi_mem_nhds p.hab] with y hy
        rcases lt_trichotomy y p.b with h | rfl | h
        · simp [yamada_phiPrime_pos, not_lt.mpr (show p.a ≤ y from le_of_lt hy), h.le, h]
        · simp [yamada_phiPrime_pos, not_lt.mpr p.hab.le, yamada_rawPrim_b]
        · simp [yamada_phiPrime_pos, not_lt.mpr (show p.a ≤ y from le_of_lt hy),
            not_le.mpr h, not_lt.mpr h.le]
      rw [yamada_psi_b]
      exact hd.congr_of_eventuallyEq he
    · have he : yamada_phiPrime_pos p =ᶠ[𝓝 x] fun _ => (1 : Real) := by
        filter_upwards [Ioi_mem_nhds hbx] with y hy
        exact yamada_phiPrime_pos_of_gt p hy
      rw [yamada_psi_of_gt p hbx]
      exact (hasDerivAt_const x (1 : Real)).congr_of_eventuallyEq he

theorem yamada_phiPrime_eq_zero_of_abs_lt (p : YamadaParams) {x : Real} (hx : |x| < p.a) :
    yamada_phiPrime p x = 0 := by
  unfold yamada_phiPrime
  split_ifs
  · exact yamada_phiPrime_pos_of_lt p ((le_abs_self x).trans_lt hx)
  · rw [yamada_phiPrime_pos_of_lt p ((neg_le_abs x).trans_lt hx), neg_zero]
  · rfl

theorem yamada_hasDerivAt_phiPrime (p : YamadaParams) (x : Real) :
    HasDerivAt (yamada_phiPrime p) (yamada_psi p |x|) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have he : yamada_phiPrime p =ᶠ[𝓝 x] fun y => -(yamada_phiPrime_pos p (-y)) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      have hy' : y < 0 := hy
      simp [yamada_phiPrime, hy', not_lt.mpr hy'.le]
    have hd := ((yamada_hasDerivAt_phiPrime_pos p (-x)).comp x (hasDerivAt_id x).neg).neg
    simpa only [abs_of_neg hx, mul_neg, mul_one, neg_neg] using hd.congr_of_eventuallyEq he
  · have he : yamada_phiPrime p =ᶠ[𝓝 (0 : Real)] fun _ => (0 : Real) := by
      have hn : {y : Real | |y| < p.a} ∈ 𝓝 (0 : Real) := by
        exact (continuous_abs.tendsto 0).eventually_lt_const (by simpa using p.ha_pos)
      filter_upwards [hn] with y hy
      exact yamada_phiPrime_eq_zero_of_abs_lt p hy
    simpa only [abs_zero, yamada_psi_of_lt p p.ha_pos] using
      (hasDerivAt_const (0 : Real) (0 : Real)).congr_of_eventuallyEq he
  · have he : yamada_phiPrime p =ᶠ[𝓝 x] yamada_phiPrime_pos p := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      simp only [yamada_phiPrime, ite_eq_left (show 0 < y from hy)]
    simpa only [abs_of_pos hx] using
      (yamada_hasDerivAt_phiPrime_pos p x).congr_of_eventuallyEq he

theorem yamada_continuous_phiPrime (p : YamadaParams) : Continuous (yamada_phiPrime p) :=
  continuous_iff_continuousAt.mpr fun x => (yamada_hasDerivAt_phiPrime p x).continuousAt

theorem yamada_hasDerivAt_phi (p : YamadaParams) (x : Real) :
    HasDerivAt (yamada_phi p) (yamada_phiPrime p x) x :=
  intervalIntegral.integral_hasDerivAt_right
    ((yamada_continuous_phiPrime p).intervalIntegrable 0 x)
    ((yamada_continuous_phiPrime p).stronglyMeasurableAtFilter volume (𝓝 x))
    (yamada_continuous_phiPrime p).continuousAt

theorem yamada_contDiff_phi (p : YamadaParams) : ContDiff Real 2 (yamada_phi p) := by
  have hd : deriv (yamada_phi p) = yamada_phiPrime p :=
    funext fun x => (yamada_hasDerivAt_phi p x).deriv
  have hdd : deriv (yamada_phiPrime p) = fun x => yamada_psi p |x| :=
    funext fun x => (yamada_hasDerivAt_phiPrime p x).deriv
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (yamada_hasDerivAt_phi p x).differentiableAt, ?_, ?_⟩
  · norm_num
  · rw [hd, contDiff_one_iff_deriv, hdd]
    exact ⟨fun x => (yamada_hasDerivAt_phiPrime p x).differentiableAt,
      (yamada_continuous_psi p).comp continuous_abs⟩

theorem yamada_phi_le_abs (p : YamadaParams) (x : Real) : yamada_phi p x ≤ |x| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : Real)) (b := x)
    (C := 1) (f := yamada_phiPrime p) (fun t _ => by
      simpa only [Real.norm_eq_abs] using yamada_abs_phiPrime_le_one p t)
  simp only [Real.norm_eq_abs, sub_zero, one_mul] at h
  exact (le_abs_self _).trans h

theorem yamada_phiPrime_nonneg_of_nonneg (p : YamadaParams) {x : Real} (hx : 0 ≤ x) :
    0 ≤ yamada_phiPrime p x := by
  rcases hx.eq_or_lt with rfl | h
  · rw [yamada_phiPrime_zero]
  · simpa only [yamada_phiPrime, ite_eq_left h] using yamada_phiPrime_pos_nonneg p x

theorem yamada_phi_nonneg_of_nonneg (p : YamadaParams) {x : Real} (hx : 0 ≤ x) :
    0 ≤ yamada_phi p x :=
  intervalIntegral.integral_nonneg hx fun _ ht => yamada_phiPrime_nonneg_of_nonneg p ht.1

theorem yamada_phiPrime_eq_one_of_ge (p : YamadaParams) {x : Real} (hx : p.b ≤ x) :
    yamada_phiPrime p x = 1 := by
  have hxpos := (p.ha_pos.trans p.hab).trans_le hx
  simp only [yamada_phiPrime, ite_eq_left hxpos]
  rcases hx.eq_or_lt with rfl | h
  · rw [yamada_phiPrime_pos_of_mem p ⟨p.hab.le, le_rfl⟩, yamada_rawPrim_b]
  · exact yamada_phiPrime_pos_of_gt p h

theorem yamada_sub_le_phi_of_nonneg (p : YamadaParams) {x : Real} (hx : 0 ≤ x) :
    x - p.b ≤ yamada_phi p x := by
  by_cases hxb : x ≤ p.b
  · exact (sub_nonpos.mpr hxb).trans (yamada_phi_nonneg_of_nonneg p hx)
  · have hbx : p.b ≤ x := (lt_of_not_ge hxb).le
    have hi : (∫ t in p.b..x, yamada_phiPrime p t) = x - p.b := by
      calc
        (∫ t in p.b..x, yamada_phiPrime p t) = ∫ _ in p.b..x, (1 : Real) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [Set.uIcc_of_le hbx] at ht
          exact yamada_phiPrime_eq_one_of_ge p ht.1
        _ = x - p.b := by simp
    have hs := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((yamada_continuous_phiPrime p).intervalIntegrable 0 p.b)
      ((yamada_continuous_phiPrime p).intervalIntegrable p.b x)
    rw [hi] at hs
    have hb := yamada_phi_nonneg_of_nonneg p (p.ha_pos.trans p.hab).le
    change 0 ≤ ∫ t in 0..p.b, yamada_phiPrime p t at hb
    change x - p.b ≤ ∫ t in 0..x, yamada_phiPrime p t
    linarith

theorem yamada_sub_le_phi (p : YamadaParams) (x : Real) : |x| - p.b ≤ yamada_phi p x := by
  rcases le_total 0 x with hx | hx
  · simpa only [abs_of_nonneg hx] using yamada_sub_le_phi_of_nonneg p hx
  · have h := yamada_sub_le_phi_of_nonneg p (neg_nonneg.mpr hx)
    simpa only [yamada_phi_even, abs_of_nonpos hx] using h

theorem yamada_phi_approx_bounds (p : YamadaParams) (x : Real) :
    |x| - p.b ≤ yamada_phi p x ∧ yamada_phi p x ≤ |x| :=
  ⟨yamada_sub_le_phi p x, yamada_phi_le_abs p x⟩

end MathFin.Heston
