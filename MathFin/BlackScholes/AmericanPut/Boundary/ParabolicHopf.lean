/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.ParabolicMaximum
public import Mathlib

/-!
# Terminal-time boundary derivative from an explicit parabolic barrier

The stationary barrier `eta*(exp(lam*x)-1)` is a subsolution when
`lam + D >= 0`. Weak comparison on a backward rectangle gives a strictly
positive RIGHT derivative at its terminal left corner. No extension past the
terminal time, spatial derivative across the boundary, or Hopf axiom is used.

## Result

Public entry points include `expBarrier`, `expBarrier_smooth`, `expBarrier_hasDeriv`,
`expBarrier_deriv2`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set Filter
open scoped Topology ContDiff

/-- The stationary barrier `η * (Real.exp (lam * x) - 1)`, which vanishes at `x = 0`. -/
noncomputable def expBarrier (η lam x : ℝ) : ℝ := η * (Real.exp (lam * x) - 1)

theorem expBarrier_smooth (η lam : ℝ) : ContDiff ℝ ∞ (expBarrier η lam) := by
  unfold expBarrier
  fun_prop

theorem expBarrier_hasDeriv (η lam x : ℝ) :
    HasDerivAt (expBarrier η lam) (η * lam * Real.exp (lam * x)) x := by
  convert! ((((hasDerivAt_id x).const_mul lam).exp).sub_const 1).const_mul η using 1
  simp only [id_eq]
  ring

theorem expBarrier_deriv2 (η lam x : ℝ) :
    deriv (deriv (expBarrier η lam)) x = η * lam ^ 2 * Real.exp (lam * x) := by
  rw [show deriv (expBarrier η lam) = fun y => η * lam * Real.exp (lam * y) from
    funext (fun y => (expBarrier_hasDeriv η lam y).deriv)]
  convert! ((((hasDerivAt_id x).const_mul lam).exp).const_mul (η * lam)).deriv using 1
  simp only [id_eq]
  ring

theorem expBarrier_operator_nonneg {η lam D x : ℝ}
    (hη : 0 ≤ η) (hlam : 0 ≤ lam) (hD : 0 ≤ lam + D) :
    0 ≤ deriv (deriv (expBarrier η lam)) x + D * deriv (expBarrier η lam) x := by
  rw [expBarrier_deriv2, (expBarrier_hasDeriv η lam x).deriv]
  have he : 0 ≤ η * lam * Real.exp (lam * x) * (lam + D) := by positivity
  nlinarith

/-- A linear lower bound on a right neighborhood bounds the one-sided
derivative from below. Only the derivative within `Ici 0` is needed. -/
theorem right_deriv_ge_of_linear_lower {F : ℝ → ℝ} {L m v : ℝ}
    (hL : 0 < L) (hzero : F 0 = 0) (hd : HasDerivWithinAt F v (Ici 0) 0)
    (hlower : ∀ x, 0 < x → x ≤ L → m * x ≤ F x) : m ≤ v := by
  have ht : Tendsto (slope F 0) (𝓝[>] 0) (𝓝 v) :=
    (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Ioi 0 by simp)).mp
      (hd.mono Ioi_subset_Ici_self)
  apply ge_of_tendsto ht
  filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hL), self_mem_nhdsWithin] with x hx hx0
  have he := (le_div_iff₀ (show 0 < x from hx0)).mpr (hlower x hx0 hx.le)
  simpa only [slope, hzero, vsub_eq_sub, sub_zero, smul_eq_mul, div_eq_inv_mul] using he

/-- Quantitative terminal Hopf estimate. The bottom and right edges dominate
the barrier, and the left edge is nonnegative. The PDE is a supersolution
inequality, so equality is not necessary. -/
theorem terminal_hopf_of_barrier {u D : ℝ → ℝ → ℝ} {L a T η lam v : ℝ}
    (hL : 0 < L) (haT : a ≤ T) (hη : 0 < η) (hlam : 0 < lam)
    (hu : ContinuousOn (fun z : ℝ × ℝ => u z.1 z.2) (movingStrip (fun _ => 0) L a T))
    (hux : ∀ x t, 0 < x → x < L → a < t → t ≤ T → ContDiffAt ℝ 2 (fun y => u y t) x)
    (hut : ∀ x t, 0 < x → x < L → a < t → t ≤ T → DifferentiableAt ℝ (u x) t)
    (hpde : ∀ x t, 0 < x → x < L → a < t → t ≤ T →
      deriv (deriv (fun y => u y t)) x + D x t * deriv (fun y => u y t) x ≤ deriv (u x) t)
    (hD : ∀ x t, 0 < x → x < L → a < t → t ≤ T → 0 ≤ lam + D x t)
    (hbottom : ∀ x, 0 ≤ x → x ≤ L → expBarrier η lam x ≤ u x a)
    (hleft : ∀ t, a ≤ t → t ≤ T → 0 ≤ u 0 t)
    (hright : ∀ t, a ≤ t → t ≤ T → expBarrier η lam L ≤ u L t)
    (hzero : u 0 T = 0) (hd : HasDerivWithinAt (fun x => u x T) v (Ici 0) 0) :
    η * lam ≤ v := by
  let w : ℝ → ℝ → ℝ := fun x t => expBarrier η lam x - u x t
  have hB : ContDiff ℝ 2 (expBarrier η lam) :=
    (expBarrier_smooth η lam).of_le (WithTop.coe_le_coe.mpr le_top)
  have hw : ContinuousOn (fun z : ℝ × ℝ => w z.1 z.2) (movingStrip (fun _ => 0) L a T) :=
    ((hB.continuous.comp continuous_fst).continuousOn).sub hu
  have hwt (x t : ℝ) (hat : a < t) (htT : t ≤ T) (hx : 0 < x) (hxL : x < L) :
      DifferentiableAt ℝ (w x) t :=
    (hasDerivAt_const t (expBarrier η lam x)).differentiableAt.sub (hut x t hx hxL hat htT)
  have hwpde (x t : ℝ) (hat : a < t) (htT : t ≤ T) (hx : 0 < x) (hxL : x < L) :
      deriv (w x) t ≤ deriv (deriv (fun y => w y t)) x + D x t * deriv (fun y => w y t) x := by
    have hs := hux x t hx hxL hat htT
    have hxx : deriv (deriv (fun y => w y t)) x =
        deriv (deriv (expBarrier η lam)) x - deriv (deriv (fun y => u y t)) x := by
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero, w] using
        iteratedDeriv_fun_sub (n := 2) hB.contDiffAt hs
    rw [hxx]
    dsimp [w]
    rw [deriv_const_sub, deriv_fun_sub (hB.differentiable (by norm_num) x)
      (hs.differentiableAt (by norm_num))]
    have hbar := expBarrier_operator_nonneg (x := x) hη.le hlam.le (hD x t hx hxL hat htT)
    have hineq := hpde x t hx hxL hat htT
    nlinarith
  have hcomp := parabolic_maximum (u := w) (D := D) (b := fun _ => 0)
    continuousOn_const (fun _ _ => hL.le) hw hwt hwpde
    (fun x hx hxL => sub_nonpos.mpr (hbottom x hx hxL))
    (fun t hat htT => by simpa [w, expBarrier] using neg_nonpos.mpr (hleft t hat htT))
    (fun t hat htT => sub_nonpos.mpr (hright t hat htT))
  apply right_deriv_ge_of_linear_lower hL hzero hd
  intro x hx hxL
  have he := Real.add_one_le_exp (lam * x)
  have hb : η * lam * x ≤ expBarrier η lam x := by
    dsimp [expBarrier]
    nlinarith [mul_le_mul_of_nonneg_left he hη.le]
  exact hb.trans (sub_nonpos.mp (hcomp (x,T) ⟨haT, le_rfl, hx.le, hxL⟩))

/-- Strict positivity on the compact bottom and right edges supplies a
positive barrier scale. This is a proved compactness step, not an extra
quantitative lower-bound premise. -/
theorem exists_expBarrier_below_edges {u : ℝ → ℝ → ℝ} {L a T lam : ℝ}
    (hL : 0 < L) (haT : a ≤ T) (hlam : 0 ≤ lam)
    (hbottom : ContinuousOn (fun x => u x a) (Icc 0 L))
    (hright : ContinuousOn (u L) (Icc a T))
    (hbp : ∀ x ∈ Icc 0 L, 0 < u x a)
    (hrp : ∀ t ∈ Icc a T, 0 < u L t) :
    ∃ η : ℝ, 0 < η ∧
      (∀ x, 0 ≤ x → x ≤ L → expBarrier η lam x ≤ u x a) ∧
      (∀ t, a ≤ t → t ≤ T → expBarrier η lam L ≤ u L t) := by
  obtain ⟨x₀,hx₀,hxmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hL.le) hbottom
  obtain ⟨t₀,ht₀,htmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr haT) hright
  let m := min (u x₀ a) (u L t₀)
  have hm : 0 < m := lt_min (hbp x₀ hx₀) (hrp t₀ ht₀)
  let η := m / Real.exp (lam * L)
  have hη : 0 < η := div_pos hm (Real.exp_pos _)
  have hbound (x : ℝ) (hxL : x ≤ L) : expBarrier η lam x ≤ m := by
    have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxL hlam)
    have heq : η * Real.exp (lam * L) = m := div_mul_cancel₀ _ (Real.exp_pos _).ne'
    dsimp [expBarrier]
    nlinarith [mul_le_mul_of_nonneg_left he hη.le]
  refine ⟨η,hη,?_,?_⟩
  · intro x hx hxL
    exact (hbound x hxL).trans ((min_le_left _ _).trans (hxmin ⟨hx,hxL⟩))
  · intro t hat htT
    exact (hbound L le_rfl).trans ((min_le_right _ _).trans (htmin ⟨hat,htT⟩))

/-- Terminal boundary-point lemma with qualitative positivity hypotheses.
Only a lower bound on the drift and a one-sided terminal derivative are used.
The needed positive barrier scale is constructed by compactness. -/
theorem terminal_hopf {u D : ℝ → ℝ → ℝ} {L a T M v : ℝ}
    (hL : 0 < L) (haT : a ≤ T)
    (hu : ContinuousOn (fun z : ℝ × ℝ => u z.1 z.2) (movingStrip (fun _ => 0) L a T))
    (hux : ∀ x t, 0 < x → x < L → a < t → t ≤ T → ContDiffAt ℝ 2 (fun y => u y t) x)
    (hut : ∀ x t, 0 < x → x < L → a < t → t ≤ T → DifferentiableAt ℝ (u x) t)
    (hpde : ∀ x t, 0 < x → x < L → a < t → t ≤ T →
      deriv (deriv (fun y => u y t)) x + D x t * deriv (fun y => u y t) x ≤ deriv (u x) t)
    (hD : ∀ x t, 0 < x → x < L → a < t → t ≤ T → -M ≤ D x t)
    (hbottom : ∀ x ∈ Icc 0 L, 0 < u x a)
    (hleft : ∀ t, a ≤ t → t ≤ T → 0 ≤ u 0 t)
    (hright : ∀ t ∈ Icc a T, 0 < u L t)
    (hzero : u 0 T = 0) (hd : HasDerivWithinAt (fun x => u x T) v (Ici 0) 0) :
    0 < v := by
  have hbcont : ContinuousOn (fun x => u x a) (Icc 0 L) := by
    exact hu.comp (continuousOn_id.prodMk continuousOn_const) (fun _ hx => ⟨le_rfl,haT,hx⟩)
  have hrcont : ContinuousOn (u L) (Icc a T) := by
    exact hu.comp (continuousOn_const.prodMk continuousOn_id) (fun _ ht => ⟨ht.1,ht.2,hL.le,le_rfl⟩)
  let lam := |M| + 1
  have hlam : 0 < lam := by dsimp [lam]; positivity
  obtain ⟨η,hη,hb,hr⟩ := exists_expBarrier_below_edges hL haT hlam.le hbcont hrcont hbottom hright
  have hderiv := terminal_hopf_of_barrier hL haT hη hlam hu hux hut hpde
    (fun x t hx hxL hat htT => by
      have := hD x t hx hxL hat htT
      dsimp [lam]
      linarith [le_abs_self M]) hb hleft hr hzero hd
  exact (mul_pos hη hlam).trans_le hderiv

end MathFin.BlackScholes.AmericanPut.Boundary
