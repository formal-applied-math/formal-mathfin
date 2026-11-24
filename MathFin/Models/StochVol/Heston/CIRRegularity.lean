/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Models.StochVol.Heston.Definitions
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Regularity and Local Lipschitz bounds for the CIR Diffusion

This file formalizes the drift and diffusion coefficients of the Cox-Ingersoll-Ross (CIR)
variance process in the Heston model:
  d v_t = kappa * (theta - v_t) dt + xi * sqrt(v_t) d W_t

We provide:
1. Definitions of `cirDrift` and `cirDiffusion`.
2. The algebraic identity for the squared diffusion coefficient on `v ≥ 0`.
3. Derivative of `cirDrift` everywhere on ℝ.
4. Derivative of `cirDiffusion` on the positive half-line `v > 0`.
5. Local Lipschitz continuity on half-lines `[ε, +∞)` for `ε > 0`.
6. Proof that `Real.sqrt` is not globally Lipschitz on `[0, +∞)`, establishing that
   the standard Picard-Lindelöf existence framework (which requires global Lipschitz bounds)
   cannot be directly applied to the square-root diffusion without localization/truncation.

## Main definitions

* `cirDrift`
* `cirDiffusion`

## Main results

* `cirDiffusion_not_globally_lipschitz`
* `sqrt_holder_sq`
* `cirDiffusion_holder_sq`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

noncomputable section
namespace MathFin.Heston

open Set
open scoped Topology

/-- Drift coefficient of the CIR variance process: `b(v) = κ (θ - v)`. -/
def cirDrift (p : Parameters) (v : Real) : Real :=
  p.kappa * (p.theta - v)

/-- Diffusion coefficient of the CIR variance process: `σ(v) = ξ √v`. -/
def cirDiffusion (p : Parameters) (v : Real) : Real :=
  p.xi * Real.sqrt v

/-- Squared diffusion identity for `v ≥ 0`: `σ(v)² = ξ² v`. -/
theorem cirDiffusion_sq (p : Parameters) (v : Real) (hv : 0 ≤ v) :
    cirDiffusion p v ^ 2 = p.xi ^ 2 * v := by
  unfold cirDiffusion
  rw [mul_pow, Real.sq_sqrt hv]

/-- The CIR drift is differentiable everywhere with derivative `-κ`. -/
theorem hasDerivAt_cirDrift (p : Parameters) (v : Real) :
    HasDerivAt (cirDrift p) (-p.kappa) v := by
  unfold cirDrift
  have hlin : HasDerivAt (fun x : Real ↦ p.theta - x) (-1) v := by
    simpa only [id_eq] using (hasDerivAt_id v).const_sub p.theta
  simpa only [mul_neg, mul_one] using hlin.const_mul p.kappa

/-- The CIR diffusion is differentiable on the open half-line `v > 0`. -/
theorem hasDerivAt_cirDiffusion (p : Parameters) (v : Real) (hv : 0 < v) :
    HasDerivAt (cirDiffusion p) (p.xi / (2 * Real.sqrt v)) v := by
  unfold cirDiffusion
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt v)) v :=
    Real.hasDerivAt_sqrt hv.ne'
  simpa only [mul_one_div] using hsqrt.const_mul p.xi

/-- On any half-line `[ε, +∞)` with `ε > 0`, the derivative of `Real.sqrt` is bounded
by `1 / (2 √ε)`. -/
theorem deriv_sqrt_bound_on_Ici {ε : Real} (hε : 0 < ε) (x : Real) (hx : x ∈ Ici ε) :
    ‖deriv Real.sqrt x‖ ≤ 1 / (2 * Real.sqrt ε) := by
  have hxpos : 0 < x := lt_of_lt_of_le hε (mem_Ici.mp hx)
  have hd : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x :=
    Real.hasDerivAt_sqrt hxpos.ne'
  rw [hd.deriv, Real.norm_eq_abs]
  have hpos_denom : 0 < 2 * Real.sqrt x := mul_pos two_pos (Real.sqrt_pos.mpr hxpos)
  have hval_pos : 0 < 1 / (2 * Real.sqrt x) := one_div_pos.mpr hpos_denom
  rw [abs_of_pos hval_pos]
  have hsqrt_le : Real.sqrt ε ≤ Real.sqrt x := Real.sqrt_le_sqrt (mem_Ici.mp hx)
  have hdenom_le : 2 * Real.sqrt ε ≤ 2 * Real.sqrt x :=
    mul_le_mul_of_nonneg_left hsqrt_le zero_le_two
  have hdiv : 0 < 2 * Real.sqrt ε := mul_pos two_pos (Real.sqrt_pos.mpr hε)
  exact one_div_le_one_div_of_le hdiv hdenom_le

/-- `Real.sqrt` is Lipschitz away from the singular endpoint. -/
theorem lipschitzOnWith_sqrt_Ici {ε : Real} (hε : 0 < ε) :
    LipschitzOnWith (Real.toNNReal (1 / (2 * Real.sqrt ε))) Real.sqrt (Ici ε) := by
  apply (convex_Ici ε).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x hx => (Real.hasDerivAt_sqrt (lt_of_lt_of_le hε hx).ne').hasDerivWithinAt)
  intro x hx
  apply NNReal.coe_le_coe.mp
  rw [Real.coe_toNNReal _ (by positivity)]
  change ‖1 / (2 * Real.sqrt x)‖ ≤ 1 / (2 * Real.sqrt ε)
  simpa only [(Real.hasDerivAt_sqrt (lt_of_lt_of_le hε hx).ne').deriv] using
    deriv_sqrt_bound_on_Ici hε x hx

/-- A coefficient bound suitable for localization on `[ε, +∞)`. -/
theorem lipschitzOnWith_cirDiffusion_Ici (p : Parameters) {ε : Real} (hε : 0 < ε) :
    LipschitzOnWith (Real.toNNReal (|p.xi| * (1 / (2 * Real.sqrt ε))))
      (cirDiffusion p) (Ici ε) := by
  apply (convex_Ici ε).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x hx => (hasDerivAt_cirDiffusion p x (lt_of_lt_of_le hε hx)).hasDerivWithinAt)
  intro x hx
  apply NNReal.coe_le_coe.mp
  rw [Real.coe_toNNReal _ (by positivity)]
  change ‖p.xi / (2 * Real.sqrt x)‖ ≤ |p.xi| * (1 / (2 * Real.sqrt ε))
  have hb := deriv_sqrt_bound_on_Ici hε x hx
  rw [(Real.hasDerivAt_sqrt (lt_of_lt_of_le hε hx).ne').deriv] at hb
  calc
    ‖p.xi / (2 * Real.sqrt x)‖ = |p.xi| * ‖1 / (2 * Real.sqrt x)‖ := by
      rw [div_eq_mul_one_div, norm_mul, Real.norm_eq_abs]
    _ ≤ |p.xi| * (1 / (2 * Real.sqrt ε)) :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg _)

/-- There is no finite linear bound on the square root at zero. -/
theorem sqrt_has_no_linear_bound_at_zero :
    ¬ ∃ L : Real, ∀ x : Real, 0 < x → Real.sqrt x ≤ L * x := by
  intro ⟨L, hL⟩
  let c : Real := max L 0 + 1
  have hc : 0 < c := by dsimp [c]; linarith [le_max_right L 0]
  have hLc : L < c := by dsimp [c]; linarith [le_max_left L 0]
  have hx : 0 < (1 / c) ^ 2 := pow_pos (one_div_pos.mpr hc) 2
  have hs := hL ((1 / c) ^ 2) hx
  rw [Real.sqrt_sq (one_div_pos.mpr hc).le] at hs
  have hm := mul_lt_mul_of_pos_right hLc hx
  have hid : c * (1 / c) ^ 2 = 1 / c := by field_simp
  rw [hid] at hm
  exact (not_lt_of_ge hs) hm

/-- A global Lipschitz Picard theorem cannot be applied to this coefficient unchanged. -/
theorem sqrt_not_globally_lipschitz (L : NNReal) : ¬ LipschitzWith L Real.sqrt := by
  intro h
  apply sqrt_has_no_linear_bound_at_zero
  refine ⟨(L : Real), ?_⟩
  intro x hx
  simpa only [Real.dist_eq, Real.sqrt_zero, sub_zero,
    abs_of_nonneg (Real.sqrt_nonneg x), abs_of_nonneg hx.le] using h.dist_le_mul x 0

/-- Nonzero vol-of-vol preserves the obstruction to a global Lipschitz bound. -/
theorem cirDiffusion_not_globally_lipschitz (p : Parameters) (hxi : p.xi ≠ 0) (L : NNReal) :
    ¬ LipschitzWith L (cirDiffusion p) := by
  intro h
  apply sqrt_has_no_linear_bound_at_zero
  refine ⟨(L : Real) / |p.xi|, ?_⟩
  intro x hx
  have ha : 0 < |p.xi| := abs_pos.mpr hxi
  have hb : |p.xi| * Real.sqrt x ≤ (L : Real) * x := by
    simpa only [Real.dist_eq, cirDiffusion, Real.sqrt_zero, mul_zero, sub_zero, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg x), abs_of_nonneg hx.le] using h.dist_le_mul x 0
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ ha).mpr
  simpa only [mul_comm] using hb

/-- The square-root modulus used in the non-Lipschitz pathwise uniqueness route. -/
theorem sqrt_holder_sq (x y : Real) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (Real.sqrt x - Real.sqrt y) ^ 2 ≤ |x - y| := by
  have hsx := Real.sq_sqrt hx
  have hsy := Real.sq_sqrt hy
  rcases le_total x y with hxy | hyx
  · have hp := mul_nonneg (Real.sqrt_nonneg x)
      (sub_nonneg.mpr (Real.sqrt_le_sqrt hxy))
    rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    nlinarith
  · have hp := mul_nonneg (Real.sqrt_nonneg y)
      (sub_nonneg.mpr (Real.sqrt_le_sqrt hyx))
    rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    nlinarith

theorem cirDiffusion_holder_sq (p : Parameters) (x y : Real) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (cirDiffusion p x - cirDiffusion p y) ^ 2 ≤ p.xi ^ 2 * |x - y| := by
  simp only [cirDiffusion, ← mul_sub, mul_pow]
  exact mul_le_mul_of_nonneg_left (sqrt_holder_sq x y hx hy) (sq_nonneg p.xi)

end MathFin.Heston
