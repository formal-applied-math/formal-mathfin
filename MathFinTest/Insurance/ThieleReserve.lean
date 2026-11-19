/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/

import MathFin

/-!
# Thiele reserve checks

Specializations of `thieleReserve` and `hasDerivAt_thieleReserve` (Thiele's
differential equation):

* constant coefficients with balanced premium (`prem = μ * b`): the reserve is the
  discounted terminal payment in closed form, and the endpoint gives its derivative.
* zero hazard (`μ = 0`): the factor drops mortality and the endpoint reduces to the
  pure interest form; with no premiums or benefits the reserve is the discounted
  terminal payment.
* boundary value: the reserve at the horizon `T` is the terminal payment `g`.
-/

open MathFin

/-- Constant coefficients give the factor in closed form. -/
theorem thiele_const_factor (d m t s : ℝ) :
    thieleFactor (fun _ => d) (fun _ => m) t s
      = Real.exp (-(d + m) * (s - t)) := by
  rw [show thieleFactor (fun _ => d) (fun _ => m) t s
      = Real.exp (-∫ _ in t..s, (d + m)) from rfl,
    intervalIntegral.integral_const, smul_eq_mul, mul_comm, neg_mul]

/-- With constant coefficients and balanced premium the reserve is the discounted
terminal payment. -/
theorem thiele_const_reserve (d m q g T t : ℝ) :
    thieleReserve (fun _ => d) (fun _ => m) (fun _ => m * q) (fun _ => q) g T t
      = Real.exp (-(d + m) * (T - t)) * g := by
  have hF := thiele_const_factor d m t T
  have hzero : (∫ s in t..T, thieleFactor (fun _ => d) (fun _ => m) t s
      * ((fun _ => m) s * (fun _ => q) s - (fun _ => m * q) s)) = 0 := by
    rw [show (fun s : ℝ => thieleFactor (fun _ => d) (fun _ => m) t s
        * ((fun _ => m) s * (fun _ => q) s - (fun _ => m * q) s))
        = fun _ => (0:ℝ) from by
      funext s
      change thieleFactor (fun _ => d) (fun _ => m) t s * (m * q - m * q) = 0
      rw [sub_self, mul_zero]]
    exact intervalIntegral.integral_zero
  unfold thieleReserve
  rw [hzero, hF, zero_add]

/-- The endpoint computes the derivative for constant coefficients. -/
theorem thiele_const_hasDerivAt (d m q g T t : ℝ) (hT : 0 < T) (ht0 : 0 < t)
    (htT : t < T) :
    HasDerivAt
      (thieleReserve (fun _ => d) (fun _ => m) (fun _ => m * q) (fun _ => q) g T)
      ((d + m) * (Real.exp (-(d + m) * (T - t)) * g)) t := by
  have h := hasDerivAt_thieleReserve (fun _ => d) (fun _ => m) (fun _ => m * q)
    (fun _ => q) g T hT continuous_const.continuousOn
    continuous_const.continuousOn continuous_const.continuousOn
    continuous_const.continuousOn t ht0 htT
  have hV := thiele_const_reserve d m q g T t
  rw [hV] at h
  simpa using h

/-- Numeric pin of the constant-coefficient reserve at the horizon. -/
theorem thiele_const_boundaryNum (q g : ℝ) :
    thieleReserve (fun _ => (1:ℝ)) (fun _ => (2:ℝ)) (fun _ => (2:ℝ) * q)
      (fun _ => q) g 3 3 = g := by
  have h := thiele_const_reserve 1 2 q g 3 3
  rw [sub_self, mul_zero, Real.exp_zero, one_mul] at h
  exact h

/-- With zero hazard the factor integrates interest only. -/
theorem thiele_zeroHazard_factor (δ : ℝ → ℝ) (t s : ℝ) :
    thieleFactor δ (fun _ => 0) t s = Real.exp (-∫ u in t..s, δ u) := by
  rw [show thieleFactor δ (fun _ => 0) t s
      = Real.exp (-∫ u in t..s, (δ u + (fun _ => (0:ℝ)) u)) from rfl]
  congr 1
  congr 1
  apply intervalIntegral.integral_congr
  intro u _
  change δ u + (fun _ => (0:ℝ)) u = δ u
  simp

/-- With zero hazard the endpoint reduces to the pure interest form. -/
theorem thiele_zeroHazard_hasDerivAt (δ prem b : ℝ → ℝ) (g T t : ℝ) (hT : 0 < T)
    (hδ : ContinuousOn δ (Set.Icc 0 T)) (hprem : ContinuousOn prem (Set.Icc 0 T))
    (hb : ContinuousOn b (Set.Icc 0 T)) (ht0 : 0 < t) (htT : t < T) :
    HasDerivAt (thieleReserve δ (fun _ => 0) prem b g T)
      (δ t * thieleReserve δ (fun _ => 0) prem b g T t + prem t) t := by
  have h := hasDerivAt_thieleReserve δ (fun _ => 0) prem b g T hT hδ
    continuous_const.continuousOn hprem hb t ht0 htT
  simpa using h

/-- With zero hazard and no premiums or benefits the reserve is the discounted
terminal payment. -/
theorem thiele_pureEndowment (δ : ℝ → ℝ) (g T t : ℝ) :
    thieleReserve δ (fun _ => 0) (fun _ => 0) (fun _ => 0) g T t
      = thieleFactor δ (fun _ => 0) t T * g := by
  unfold thieleReserve
  have hzero : (∫ s in t..T, thieleFactor δ (fun _ => 0) t s
      * ((fun _ => (0:ℝ)) s * (fun _ => (0:ℝ)) s - (fun _ => (0:ℝ)) s)) = 0 := by
    rw [show (fun s : ℝ => thieleFactor δ (fun _ => 0) t s
        * ((fun _ => (0:ℝ)) s * (fun _ => (0:ℝ)) s - (fun _ => (0:ℝ)) s))
        = fun _ => (0:ℝ) from by
      funext s
      change thieleFactor δ (fun _ => 0) t s * (0 * 0 - 0) = 0
      simp]
    exact intervalIntegral.integral_zero
  rw [hzero, zero_add]

/-- The reserve at the horizon is the terminal payment. -/
theorem thiele_boundary (δ μ prem b : ℝ → ℝ) (g T : ℝ) :
    thieleReserve δ μ prem b g T T = g := by
  simp only [thieleReserve, thieleFactor, intervalIntegral.integral_same,
    neg_zero, Real.exp_zero, zero_add, one_mul]
