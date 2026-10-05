/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.SVI.BlackScholesBridge

/-! # The zero-scale slice and its derivatives

Part of the SVI polynomial-sign certificate (#174).

The piecewise-affine SVI variance at σ = 0: ordinary derivatives on
the two open wings and one-sided derivatives at their common endpoint. -/

@[expose] public section

namespace MathFin
namespace SVI
open Real ProbabilityTheory Set

theorem sigmaZero_variance_hasDerivAt (p : Params) (hs : p.sigma = 0) (k : ℝ) (hk : k ≠ p.m) :
    HasDerivAt (variance p) (slope p k) k := by
  have hpos : 0 < (k - p.m)^2 + p.sigma^2 := by rw [hs]; simpa using sq_pos_of_ne_zero (sub_ne_zero.mpr hk)
  have hx := (hasDerivAt_id k).sub_const p.m
  have hr := ((hx.pow 2).add_const (p.sigma^2)).sqrt (ne_of_gt hpos)
  have h := ((hx.const_mul p.rho).add hr).const_mul p.b |>.const_add p.a
  convert h using 1 <;> first | rfl | (dsimp [slope]; ring)

theorem sigmaZero_slope_hasDerivAt (p : Params) (hs : p.sigma = 0) (k : ℝ) (hk : k ≠ p.m) :
    HasDerivAt (slope p) (curvature p k) k := by
  have hpos : 0 < (k - p.m)^2 + p.sigma^2 := by rw [hs]; simpa using sq_pos_of_ne_zero (sub_ne_zero.mpr hk)
  have hroot : Real.sqrt ((k - p.m)^2 + p.sigma^2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hx := (hasDerivAt_id k).sub_const p.m
  have hr := ((hx.pow 2).add_const (p.sigma^2)).sqrt (ne_of_gt hpos)
  have h := ((hx.div hr hroot).const_add p.rho).const_mul p.b
  convert h using 1 <;> try rfl
  · dsimp [curvature]
    have he := Real.sq_sqrt hpos.le
    field_simp
    rw [he]
    ring


theorem sigmaZero_rootVariance_hasDerivAt (p : Params) (hs : p.sigma = 0) (k : ℝ) (hk : k ≠ p.m)
    (hw : 0 < variance p k) :
    HasDerivAt (rootVariance p) (slope p k / (2*rootVariance p k)) k :=
  (sigmaZero_variance_hasDerivAt p hs k hk).sqrt (ne_of_gt hw)

theorem sigmaZero_blackMinus_hasDerivAt (p : Params) (hs : p.sigma = 0) (k : ℝ) (hk : k ≠ p.m)
    (hw : 0 < variance p k) :
    HasDerivAt (blackMinus p) (blackMinusSlope p k) k := by
  have hr := sigmaZero_rootVariance_hasDerivAt p hs k hk hw
  have hn := ne_of_gt (rootVariance_pos p k hw)
  have h := (((hasDerivAt_id k).neg).div hr hn).sub (hr.div_const 2)
  convert h using 1 <;> try rfl
  dsimp [blackMinusSlope]
  field_simp
  ring

theorem sigmaZero_blackPlus_hasDerivAt (p : Params) (hs : p.sigma = 0) (k : ℝ) (hk : k ≠ p.m)
    (hw : 0 < variance p k) :
    HasDerivAt (blackPlus p)
      (blackMinusSlope p k + slope p k / (2*rootVariance p k)) k := by
  have h := (sigmaZero_blackMinus_hasDerivAt p hs k hk hw).add (sigmaZero_rootVariance_hasDerivAt p hs k hk hw)
  convert h using 1 <;> try rfl
  funext x
  dsimp [blackPlus, blackMinus]
  ring

theorem sigmaZero_logBlackCall_hasDerivAt (p : Params) (hs : p.sigma = 0) (k : ℝ) (hk : k ≠ p.m)
    (hw : 0 < variance p k) :
    HasDerivAt (logBlackCall p) (Real.exp k * blackDelta p k) k := by
  have hp := (MathFin.hasDerivAt_Phi (blackPlus p k)).comp k (sigmaZero_blackPlus_hasDerivAt p hs k hk hw)
  have hm := (MathFin.hasDerivAt_Phi (blackMinus p k)).comp k (sigmaZero_blackMinus_hasDerivAt p hs k hk hw)
  have h := hp.sub ((Real.hasDerivAt_exp k).mul hm)
  convert h using 1 <;> try rfl
  rw [black_density_identity p k hw]
  dsimp [blackDelta]
  ring

theorem sigmaZero_blackDelta_hasDerivAt (p : Params) (hs : p.sigma = 0) (k : ℝ) (hk : k ≠ p.m)
    (hw : 0 < variance p k) :
    HasDerivAt (blackDelta p)
      (gaussianPDFReal 0 1 (blackMinus p k) / rootVariance p k * durrleman p k) k := by
  have hm := sigmaZero_blackMinus_hasDerivAt p hs k hk hw
  have hp := (MathFin.hasDerivAt_gaussianPDFReal_zero_one (blackMinus p k)).comp k hm
  have hc := (MathFin.hasDerivAt_Phi (blackMinus p k)).comp k hm
  have hr := sigmaZero_rootVariance_hasDerivAt p hs k hk hw
  have hn := ne_of_gt (rootVariance_pos p k hw)
  have h := ((hp.mul (sigmaZero_slope_hasDerivAt p hs k hk)).div (hr.const_mul 2)
    (mul_ne_zero (by norm_num) hn)).sub hc
  convert h using 1 <;> try rfl
  dsimp [durrleman, blackMinusSlope, blackMinus]
  rw [← rootVariance_sq p k hw.le]
  field_simp
  ring


/-- The slope `b(ρ − 1)` of the zero-scale variance left of `m`. -/
def leftSlope (p : Params) : ℝ := p.b * (p.rho - 1)
/-- The slope `b(ρ + 1)` of the zero-scale variance right of `m`. -/
def rightSlope (p : Params) : ℝ := p.b * (p.rho + 1)

theorem sigmaZero_variance_left (p : Params) (hs : p.sigma = 0) (k : ℝ)
    (hk : k ≤ p.m) : variance p k = p.a + leftSlope p * (k-p.m) := by
  simp only [variance, hs, sq, mul_zero, add_zero, Real.sqrt_mul_self_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr hk), leftSlope]
  ring

theorem sigmaZero_variance_right (p : Params) (hs : p.sigma = 0) (k : ℝ)
    (hk : p.m ≤ k) : variance p k = p.a + rightSlope p * (k-p.m) := by
  simp only [variance, hs, sq, mul_zero, add_zero, Real.sqrt_mul_self_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hk), rightSlope]
  ring

theorem sigmaZero_variance_at_m (p : Params) (hs : p.sigma = 0) :
    variance p p.m = p.a := by simp [variance, hs]

theorem leftSlope_nonpos (p : Params) (hb : 0 ≤ p.b) (hr : 0 ≤ 1-p.rho^2) :
    leftSlope p ≤ 0 := by
  have : p.rho ≤ 1 := by nlinarith [sq_nonneg (p.rho-1)]
  exact mul_nonpos_of_nonneg_of_nonpos hb (sub_nonpos.mpr this)

theorem rightSlope_nonneg (p : Params) (hb : 0 ≤ p.b) (hr : 0 ≤ 1-p.rho^2) :
    0 ≤ rightSlope p := by
  have : -1 ≤ p.rho := by nlinarith [sq_nonneg (p.rho+1)]
  exact mul_nonneg hb (by linarith)

theorem sigmaZero_variance_ge (p : Params) (hs : p.sigma = 0)
    (hb : 0 ≤ p.b) (hr : 0 ≤ 1-p.rho^2) (k : ℝ) : p.a ≤ variance p k := by
  rcases le_total k p.m with hk | hk
  · rw [sigmaZero_variance_left p hs k hk]
    have := mul_nonneg_of_nonpos_of_nonpos (leftSlope_nonpos p hb hr) (sub_nonpos.mpr hk)
    linarith
  · rw [sigmaZero_variance_right p hs k hk]
    have := mul_nonneg (rightSlope_nonneg p hb hr) (sub_nonneg.mpr hk)
    linarith

theorem sigmaZero_variance_pos_iff (p : Params) (hs : p.sigma = 0)
    (hb : 0 ≤ p.b) (hr : 0 ≤ 1-p.rho^2) :
    (∀ k : ℝ, 0 < variance p k) ↔ 0 < p.a := by
  constructor
  · intro h
    simpa [sigmaZero_variance_at_m p hs] using h p.m
  · intro ha k
    exact lt_of_lt_of_le ha (sigmaZero_variance_ge p hs hb hr k)

theorem sigmaZero_slope_left (p : Params) (hs : p.sigma = 0) (k : ℝ)
    (hk : k < p.m) : slope p k = leftSlope p := by
  have hn : k-p.m ≠ 0 := sub_ne_zero.mpr (ne_of_lt hk)
  simp only [slope, hs, sq, mul_zero, add_zero, Real.sqrt_mul_self_eq_abs,
    abs_of_neg (sub_neg.mpr hk), div_neg, div_self hn, leftSlope]
  ring

theorem sigmaZero_slope_right (p : Params) (hs : p.sigma = 0) (k : ℝ)
    (hk : p.m < k) : slope p k = rightSlope p := by
  have hn : k-p.m ≠ 0 := sub_ne_zero.mpr (ne_of_gt hk)
  simp only [slope, hs, sq, mul_zero, add_zero, Real.sqrt_mul_self_eq_abs,
    abs_of_pos (sub_pos.mpr hk), div_self hn, rightSlope]

theorem sigmaZero_curvature (p : Params) (hs : p.sigma = 0) (k : ℝ) :
    curvature p k = 0 := by simp [curvature, hs]

/-- `blackDelta` with the variance slope replaced by the constant slope `s` of a wing. -/
noncomputable def branchDelta (p : Params) (s k : ℝ) : ℝ :=
  gaussianPDFReal 0 1 (blackMinus p k) * s / (2*rootVariance p k) -
    MathFin.Phi (blackMinus p k)

/-- The log-price chain rule only needs a one-sided variance derivative. -/
theorem logBlackCall_hasDerivWithinAt (p : Params) (s k : ℝ) (S : Set ℝ)
    (hw : 0 < variance p k) (hv : HasDerivWithinAt (variance p) s S k) :
    HasDerivWithinAt (logBlackCall p) (Real.exp k * branchDelta p s k) S k := by
  have hr : HasDerivWithinAt (rootVariance p) (s / (2*rootVariance p k)) S k :=
    hv.sqrt (ne_of_gt hw)
  have hn := ne_of_gt (rootVariance_pos p k hw)
  let dm := -1 / rootVariance p k + k*s / (2*(rootVariance p k)^3) - s / (4*rootVariance p k)
  have hm : HasDerivWithinAt (blackMinus p) dm S k := by
    have h := (((hasDerivWithinAt_id k S).neg).div hr hn).sub (hr.div_const 2)
    convert h using 1 <;> try rfl
    dsimp [dm]
    field_simp
    ring
  have hp : HasDerivWithinAt (blackPlus p) (dm + s / (2*rootVariance p k)) S k := by
    convert hm.add hr using 1 <;> try rfl
    funext x
    dsimp [blackPlus, blackMinus]
    ring
  have hp' := (MathFin.hasDerivAt_Phi (blackPlus p k)).comp_hasDerivWithinAt k hp
  have hm' := (MathFin.hasDerivAt_Phi (blackMinus p k)).comp_hasDerivWithinAt k hm
  have h := hp'.sub ((Real.hasDerivAt_exp k).hasDerivWithinAt.mul hm')
  convert h using 1 <;> try rfl
  rw [black_density_identity p k hw]
  dsimp [branchDelta]
  ring

theorem sigmaZero_variance_hasDerivWithinAt_left (p : Params) (hs : p.sigma = 0) :
    HasDerivWithinAt (variance p) (leftSlope p) (Iic p.m) p.m := by
  have h := (((hasDerivAt_id p.m).sub_const p.m).const_mul (leftSlope p)).const_add p.a
  simpa using (h.hasDerivWithinAt (s := Iic p.m)).congr
    (fun k hk ↦ sigmaZero_variance_left p hs k hk)
    (sigmaZero_variance_left p hs p.m le_rfl)

theorem sigmaZero_variance_hasDerivWithinAt_right (p : Params) (hs : p.sigma = 0) :
    HasDerivWithinAt (variance p) (rightSlope p) (Ici p.m) p.m := by
  have h := (((hasDerivAt_id p.m).sub_const p.m).const_mul (rightSlope p)).const_add p.a
  simpa using (h.hasDerivWithinAt (s := Ici p.m)).congr
    (fun k hk ↦ sigmaZero_variance_right p hs k hk)
    (sigmaZero_variance_right p hs p.m le_rfl)

end SVI
end MathFin
