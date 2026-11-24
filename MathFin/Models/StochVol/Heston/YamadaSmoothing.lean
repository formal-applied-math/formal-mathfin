/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Yamada-Watanabe Smoothing Construction for CIR Absolute Value

This module constructs the classic Yamada-Watanabe smoothing density and its derivative profiles
approximating |x| for pathwise uniqueness arguments of CIR / Heston variance processes.

## Analytic Architecture

1. `YamadaParams`: Parameters `0 < a < b` with logarithmic ratio `m = log (b / a) > 0`.
2. `yamada_logCoord`: Normalizing coordinate `r(x) = (log x - log a) / m` mapping `[a, b]` to
`[0, 1]`.
3. `yamada_polyPrim`: Cubic polynomial primitive `Q(r) = 3 r^2 - 2 r^3` with derivative `6 r (1
- r)`.
4. `yamada_psi`: Second-derivative density `psi(x)` supported in `[a, b]`, non-negative, with
   pointwise bound `psi(x) <= 2 / (m * x)` for `x > 0`.
5. `yamada_phiPrime`: First-derivative profile `phi'(x)` smoothly interpolating from `0` on
`(-infty, a]`
   to `1` on `[b, infty)`. Symmetrized to an odd function on all of `ℝ`.
6. `yamada_phi`: Integrated smoothed absolute value `phi(x) = int_0^x phi'(t) dt`.

The derivative gluing, C² regularity and approximation bounds are proved in
`Heston.YamadaCalculus`. These are deterministic analytic ingredients; neither
file asserts existence or pathwise uniqueness of the CIR stochastic process.

## Main definitions

* `yamada_phiPrime_pos`
* `yamada_phiPrime`
* `yamada_phi`

## Main results

* `yamada_abs_phiPrime_le_one`
* `yamada_phi_zero`
* `yamada_phi_even`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

noncomputable section
namespace MathFin.Heston
open Real Set Filter MeasureTheory intervalIntegral

/-- Parameters for the Yamada smoothing construction. -/
structure YamadaParams where
  a : ℝ
  b : ℝ
  ha_pos : 0 < a
  hab : a < b

/-- The logarithmic interval length m = log (b / a). -/
def yamada_m (p : YamadaParams) : ℝ := Real.log (p.b / p.a)

lemma yamada_m_pos (p : YamadaParams) : 0 < yamada_m p := by
  unfold yamada_m
  have hdiv_pos : 0 < p.b / p.a := div_pos (p.ha_pos.trans p.hab) p.ha_pos
  rw [Real.log_pos_iff hdiv_pos.le]
  exact (one_lt_div p.ha_pos).mpr p.hab

lemma yamada_m_ne_zero (p : YamadaParams) : yamada_m p ≠ 0 := (yamada_m_pos p).ne'

lemma yamada_log_b_sub_log_a (p : YamadaParams) : Real.log p.b - Real.log p.a = yamada_m p := by
  unfold yamada_m
  exact (Real.log_div (p.ha_pos.trans p.hab).ne' p.ha_pos.ne').symm

/-- The normalized logarithmic coordinate r(x) mapping [a, b] to [0, 1]. -/
def yamada_logCoord (p : YamadaParams) (x : ℝ) : ℝ :=
  (Real.log x - Real.log p.a) / yamada_m p

lemma yamada_logCoord_a (p : YamadaParams) : yamada_logCoord p p.a = 0 := by
  unfold yamada_logCoord
  simp

lemma yamada_logCoord_b (p : YamadaParams) : yamada_logCoord p p.b = 1 := by
  unfold yamada_logCoord
  rw [yamada_log_b_sub_log_a, div_self (yamada_m_ne_zero p)]

lemma yamada_logCoord_nonneg (p : YamadaParams) {x : ℝ} (hx : p.a ≤ x) : 0 ≤ yamada_logCoord p x
      := by
  unfold yamada_logCoord
  have hlog : Real.log p.a ≤ Real.log x := Real.log_le_log p.ha_pos hx
  exact div_nonneg (sub_nonneg.mpr hlog) (yamada_m_pos p).le

lemma yamada_logCoord_le_one (p : YamadaParams) {x : ℝ} (hx_pos : 0 < x) (hx : x ≤ p.b) :
      yamada_logCoord p x ≤ 1 := by
  unfold yamada_logCoord
  rw [div_le_iff₀ (yamada_m_pos p), ← yamada_log_b_sub_log_a]
  have hlog : Real.log x ≤ Real.log p.b := Real.log_le_log hx_pos hx
  linarith

/-- Normalized cubic polynomial primitive on [0, 1]: Q(r) = 3 r^2 - 2 r^3. -/
def yamada_polyPrim (r : ℝ) : ℝ := 3 * r ^ 2 - 2 * r ^ 3

lemma yamada_polyPrim_zero : yamada_polyPrim 0 = 0 := by
  unfold yamada_polyPrim
  ring

lemma yamada_polyPrim_one : yamada_polyPrim 1 = 1 := by
  unfold yamada_polyPrim
  ring

lemma yamada_hasDerivAt_polyPrim (r : ℝ) : HasDerivAt yamada_polyPrim (6 * r * (1 - r)) r := by
  unfold yamada_polyPrim
  have h1 : HasDerivAt (fun r => 3 * r ^ 2) (3 * (2 * r ^ 1)) r := by
    simpa using (hasDerivAt_pow 2 r).const_mul 3
  have h2 : HasDerivAt (fun r => 2 * r ^ 3) (2 * (3 * r ^ 2)) r := by
    simpa using (hasDerivAt_pow 3 r).const_mul 2
  have h := h1.sub h2
  have heq : 3 * (2 * r ^ 1) - 2 * (3 * r ^ 2) = 6 * r * (1 - r) := by ring
  rw [heq] at h
  exact h

/-- Pointwise polynomial upper bound: 6 * r * (1 - r) ≤ 3/2 for all real r. -/
lemma yamada_poly_le_three_halves (r : ℝ) : 6 * r * (1 - r) ≤ 3 / 2 := by
  have hid : 6 * r * (1 - r) = 3 / 2 - 6 * (r - 1 / 2) ^ 2 := by ring
  rw [hid]
  have hsq : 0 ≤ 6 * (r - 1 / 2) ^ 2 := by positivity
  linarith

/-- Pointwise polynomial lower bound: 6 * r * (1 - r) ≥ 0 on [0, 1]. -/
lemma yamada_poly_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : 0 ≤ 6 * r * (1 - r) := by
  have h1 : 0 ≤ 1 - r := sub_nonneg.mpr hr1
  positivity

/-- The core Yamada density on [a, b]. -/
def yamada_rawPsi (p : YamadaParams) (x : ℝ) : ℝ :=
  let r := yamada_logCoord p x
  6 * r * (1 - r) / (yamada_m p * x)

/-- The extended density function psi on all of ℝ, supported in [a, b]. -/
def yamada_psi (p : YamadaParams) (x : ℝ) : ℝ :=
  if p.a ≤ x ∧ x ≤ p.b then yamada_rawPsi p x else 0

lemma yamada_psi_of_mem (p : YamadaParams) {x : ℝ} (hx : x ∈ Icc p.a p.b) : yamada_psi p x =
      yamada_rawPsi p x :=
  if_pos hx

lemma yamada_psi_of_lt (p : YamadaParams) {x : ℝ} (hx : x < p.a) : yamada_psi p x = 0 := by
  unfold yamada_psi
  split_ifs with h
  · linarith
  · rfl

lemma yamada_psi_of_gt (p : YamadaParams) {x : ℝ} (hx : p.b < x) : yamada_psi p x = 0 := by
  unfold yamada_psi
  split_ifs with h
  · linarith
  · rfl

/-- Non-negativity of psi everywhere. -/
theorem yamada_psi_nonneg (p : YamadaParams) (x : ℝ) : 0 ≤ yamada_psi p x := by
  unfold yamada_psi
  split_ifs with h
  · unfold yamada_rawPsi
    have hr0 := yamada_logCoord_nonneg p h.1
    have hr1 := yamada_logCoord_le_one p (p.ha_pos.trans_le h.1) h.2
    have hpoly := yamada_poly_nonneg hr0 hr1
    have hdenom : 0 < yamada_m p * x := mul_pos (yamada_m_pos p) (p.ha_pos.trans_le h.1)
    exact div_nonneg hpoly hdenom.le
  · exact le_rfl

/-- Sharp upper bound: psi(x) ≤ 3 / (2 * m * x) for all x > 0. -/
theorem yamada_psi_le_three_div_two_mx (p : YamadaParams) {x : ℝ} (hx : 0 < x) :
    yamada_psi p x ≤ 3 / (2 * (yamada_m p * x)) := by
  unfold yamada_psi
  split_ifs with h
  · unfold yamada_rawPsi
    have hdenom : 0 < yamada_m p * x := mul_pos (yamada_m_pos p) (p.ha_pos.trans_le h.1)
    have hpoly := yamada_poly_le_three_halves (yamada_logCoord p x)
    have hdiv : 6 * yamada_logCoord p x * (1 - yamada_logCoord p x) / (yamada_m p * x) ≤ (3 / 2)
          / (yamada_m p * x) :=
      div_le_div_of_nonneg_right hpoly hdenom.le
    have heq : (3 / 2) / (yamada_m p * x) = 3 / (2 * (yamada_m p * x)) := by ring
    rwa [heq] at hdiv
  · have hdenom : 0 < 2 * (yamada_m p * x) := mul_pos two_pos (mul_pos (yamada_m_pos p) hx)
    exact div_nonneg (by norm_num) hdenom.le

/-- Standard Yamada upper bound: psi(x) ≤ 2 / (m * x) for all x > 0. -/
theorem yamada_psi_le_two_div_mx (p : YamadaParams) {x : ℝ} (hx : 0 < x) :
    yamada_psi p x ≤ 2 / (yamada_m p * x) := by
  have hbound := yamada_psi_le_three_div_two_mx p hx
  have hdenom : 0 < yamada_m p * x := mul_pos (yamada_m_pos p) hx
  have hle : (3 : ℝ) / (2 * (yamada_m p * x)) ≤ 2 / (yamada_m p * x) := by
    have heq1 : (3 : ℝ) / (2 * (yamada_m p * x)) = (3 / 2 : ℝ) / (yamada_m p * x) := by ring
    rw [heq1]
    have hnum : (3 / 2 : ℝ) ≤ 2 := by norm_num
    exact div_le_div_of_nonneg_right hnum hdenom.le
  exact hbound.trans hle

/-- Symmetrized second derivative bound: psi(|x|) ≤ 2 / (m * |x|) for x ≠ 0. -/
theorem yamada_psi_abs_le_two_div_m_abs (p : YamadaParams) {x : ℝ} (hx : x ≠ 0) :
    yamada_psi p (|x|) ≤ 2 / (yamada_m p * |x|) :=
  yamada_psi_le_two_div_mx p (abs_pos.mpr hx)

/-- Explicit continuous primitive of rawPsi on (0, infty):
    F(x) = polyPrim (logCoord x) = 3 r^2 - 2 r^3. -/
def yamada_rawPrim (p : YamadaParams) (x : ℝ) : ℝ :=
  yamada_polyPrim (yamada_logCoord p x)

lemma yamada_rawPrim_a (p : YamadaParams) : yamada_rawPrim p p.a = 0 := by
  unfold yamada_rawPrim
  rw [yamada_logCoord_a, yamada_polyPrim_zero]

lemma yamada_rawPrim_b (p : YamadaParams) : yamada_rawPrim p p.b = 1 := by
  unfold yamada_rawPrim
  rw [yamada_logCoord_b, yamada_polyPrim_one]

lemma yamada_hasDerivAt_rawPrim (p : YamadaParams) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (yamada_rawPrim p) (yamada_rawPsi p x) x := by
  have hcoord : HasDerivAt (yamada_logCoord p) (x⁻¹ / yamada_m p) x := by
    exact ((Real.hasDerivAt_log hx.ne').sub_const (Real.log p.a)).div_const (yamada_m p)
  have hd := (yamada_hasDerivAt_polyPrim (yamada_logCoord p x)).comp x hcoord
  have he : (6 * yamada_logCoord p x * (1 - yamada_logCoord p x)) * (x⁻¹ / yamada_m p) =
      yamada_rawPsi p x := by
    unfold yamada_rawPsi
    ring
  rw [he] at hd
  exact hd

/-- Extended smoothed sign profile on [0, infty):
    phi'(x) = 0 for x < a, F(x) for x in [a, b], and 1 for x > b. -/
def yamada_phiPrime_pos (p : YamadaParams) (x : ℝ) : ℝ :=
  if x < p.a then 0
  else if x ≤ p.b then yamada_rawPrim p x
  else 1

lemma yamada_phiPrime_pos_of_lt (p : YamadaParams) {x : ℝ} (hx : x < p.a) : yamada_phiPrime_pos
      p x = 0 :=
  if_pos hx

lemma yamada_phiPrime_pos_of_mem (p : YamadaParams) {x : ℝ} (hx : x ∈ Icc p.a p.b) :
    yamada_phiPrime_pos p x = yamada_rawPrim p x := by
  unfold yamada_phiPrime_pos
  split_ifs with h1 h2
  · linarith [hx.1]
  · rfl
  · linarith [hx.2]

lemma yamada_phiPrime_pos_of_gt (p : YamadaParams) {x : ℝ} (hx : p.b < x) : yamada_phiPrime_pos
      p x = 1 := by
  unfold yamada_phiPrime_pos
  split_ifs with h1 h2
  · linarith [p.hab]
  · linarith
  · rfl

lemma yamada_phiPrime_pos_nonneg (p : YamadaParams) (x : ℝ) : 0 ≤ yamada_phiPrime_pos p x := by
  unfold yamada_phiPrime_pos
  split_ifs with h1 h2
  · exact le_rfl
  · unfold yamada_rawPrim
    have hr0 := yamada_logCoord_nonneg p (x := x) (not_lt.mp h1)
    have hr1 := yamada_logCoord_le_one p (p.ha_pos.trans_le (not_lt.mp h1)) h2
    have heq : yamada_polyPrim (yamada_logCoord p x) = (yamada_logCoord p x) ^ 2 * (3 - 2 *
          yamada_logCoord p x) := by
      unfold yamada_polyPrim; ring
    rw [heq]
    have hpos : 0 ≤ 3 - 2 * yamada_logCoord p x := by linarith
    positivity
  · exact zero_le_one

lemma yamada_phiPrime_pos_le_one (p : YamadaParams) (x : ℝ) : yamada_phiPrime_pos p x ≤ 1 := by
  unfold yamada_phiPrime_pos
  split_ifs with h1 h2
  · exact zero_le_one
  · unfold yamada_rawPrim
    have hr0 := yamada_logCoord_nonneg p (x := x) (not_lt.mp h1)
    have hr1 := yamada_logCoord_le_one p (p.ha_pos.trans_le (not_lt.mp h1)) h2
    have heq : 1 - yamada_polyPrim (yamada_logCoord p x) = (1 - yamada_logCoord p x) ^ 2 * (1 +
          2 * yamada_logCoord p x) := by
      unfold yamada_polyPrim; ring
    have hnonneg : 0 ≤ (1 - yamada_logCoord p x) ^ 2 * (1 + 2 * yamada_logCoord p x) := by
      have h1 : 0 ≤ 1 + 2 * yamada_logCoord p x := by linarith
      positivity
    linarith [heq, hnonneg]
  · exact le_rfl

/-- Symmetrized first derivative phi'(x) on all of ℝ: odd function. -/
def yamada_phiPrime (p : YamadaParams) (x : ℝ) : ℝ :=
  if 0 < x then yamada_phiPrime_pos p x
  else if x < 0 then -yamada_phiPrime_pos p (-x)
  else 0

lemma yamada_phiPrime_zero (p : YamadaParams) : yamada_phiPrime p 0 = 0 := by
  unfold yamada_phiPrime
  simp

lemma yamada_phiPrime_neg (p : YamadaParams) (x : ℝ) : yamada_phiPrime p (-x) = -yamada_phiPrime
      p x := by
  unfold yamada_phiPrime
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hpos : 0 < -x := neg_pos.mpr hx
    have hnotpos : ¬ 0 < x := asymm hx
    simp [hpos, hx, hnotpos]
  · simp
  · have hneg : -x < 0 := neg_lt_zero.mpr hx
    have hnotneg : ¬ x < 0 := asymm hx
    simp [hx, hneg, hnotneg]

/-- Bound on first derivative: |phi'(x)| <= 1 everywhere on ℝ. -/
theorem yamada_abs_phiPrime_le_one (p : YamadaParams) (x : ℝ) : |yamada_phiPrime p x| ≤ 1 := by
  unfold yamada_phiPrime
  split_ifs with h1 h2
  · have hpos := yamada_phiPrime_pos_nonneg p x
    have hle := yamada_phiPrime_pos_le_one p x
    rw [abs_of_nonneg hpos]
    exact hle
  · have hpos := yamada_phiPrime_pos_nonneg p (-x)
    have hle := yamada_phiPrime_pos_le_one p (-x)
    rw [abs_neg, abs_of_nonneg hpos]
    exact hle
  · simp

/-- Extended smoothed absolute value function phi(x) = int_0^x phi'(t) dt. -/
def yamada_phi (p : YamadaParams) (x : ℝ) : ℝ :=
  ∫ t in 0..x, yamada_phiPrime p t

lemma yamada_phi_zero (p : YamadaParams) : yamada_phi p 0 = 0 := by
  unfold yamada_phi
  simp

lemma yamada_phi_even (p : YamadaParams) (x : ℝ) : yamada_phi p (-x) = yamada_phi p x := by
  unfold yamada_phi
  have hc : (∫ t in -x..0, yamada_phiPrime p t) = -(∫ t in 0..x, yamada_phiPrime p t) := by
    simpa only [neg_zero, yamada_phiPrime_neg, intervalIntegral.integral_neg] using
      (intervalIntegral.integral_comp_neg (f := yamada_phiPrime p) (a := 0) (b := x)).symm
  rw [intervalIntegral.integral_symm (-x) 0, hc, neg_neg]

end MathFin.Heston
