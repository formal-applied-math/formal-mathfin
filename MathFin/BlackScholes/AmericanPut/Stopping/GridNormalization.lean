/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ShrinkingGrids

/-! # Exact strike and time rescaling of finite-grid American put prices

The deterministic Bellman recursion only sees log drift and Gaussian variance
over each step. Both are unchanged by the Black--Scholes normalization.

## Result

Public entry points include `cappedGridTime_scale`, `brownianGridMarkovAux_scale`,
`discountedLogPayoff_scale`, `brownianGridPrice_scale`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped NNReal Topology

theorem cappedGridTime_scale (a T δ : ℝ≥0) (i : ℕ) :
    cappedGridTime (a*T) (a*δ) i = a*cappedGridTime T δ i := by
  simp only [cappedGridTime,mul_min]
  congr 1
  ring

theorem brownianGridMarkovAux_scale {Z Z' : ℕ → ℝ → ℝ} {K d β β' σ σ' : ℝ}
    {a : ℝ≥0} (hK : 0 ≤ K) (hβ : β' * (a : ℝ) = β) (hσ : σ' ^ 2 * (a : ℝ) = σ ^ 2)
    (hZ : ∀ i x, Z i (x + d) = K * Z' i x) (T δ : ℝ≥0) (n i : ℕ) (x : ℝ) :
    brownianGridMarkovAux Z T δ β σ n i (x+d) =
      K*brownianGridMarkovAux Z' (a*T) (a*δ) β' σ' n i x := by
  induction n generalizing i x with
  | zero => exact hZ i x
  | succ n ih =>
    have htime : σ'^2*((cappedGridTime (a*T) (a*δ) (i+1) : ℝ)-
        (cappedGridTime (a*T) (a*δ) i : ℝ)) =
        σ^2*((cappedGridTime T δ (i+1) : ℝ)-(cappedGridTime T δ i : ℝ)) := by
      simp only [cappedGridTime_scale,NNReal.coe_mul,← mul_sub,← mul_assoc,hσ]
    have hdrift : β'*((cappedGridTime (a*T) (a*δ) (i+1) : ℝ)-
        (cappedGridTime (a*T) (a*δ) i : ℝ)) =
        β*((cappedGridTime T δ (i+1) : ℝ)-(cappedGridTime T δ i : ℝ)) := by
      simp only [cappedGridTime_scale,NNReal.coe_mul,← mul_sub,← mul_assoc,hβ]
    simp only [brownianGridMarkovAux]
    rw [mul_max_of_nonneg _ _ hK,hZ]
    congr 1
    rw [htime,hdrift]
    unfold brownianHeatFlow
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro ω
    convert! ih (i+1) (x+β*((cappedGridTime T δ (i+1) : ℝ)-
      (cappedGridTime T δ i : ℝ))+brownian
        (σ^2*((cappedGridTime T δ (i+1) : ℝ)-(cappedGridTime T δ i : ℝ))).toNNReal ω) using 1
    simp only [add_assoc,add_comm]

theorem discountedLogPayoff_scale {K r k : ℝ} {a : ℝ≥0}
    (hK : 0 < K) (hk : k * (a : ℝ) = r) (t : ℝ≥0) (x : ℝ) :
    discountedLogPayoff K r t (x+Real.log K) = K*discountedLogPayoff 1 k (a*t) x := by
  have hpay : max (K-Real.exp (x+Real.log K)) 0 = K*max (1-Real.exp x) 0 := by
    rw [mul_max_of_nonneg _ _ hK.le,Real.exp_add,Real.exp_log hK,mul_zero]
    congr 1
    ring
  unfold discountedLogPayoff
  rw [hpay]
  simp only [NNReal.coe_mul,neg_mul,← mul_assoc,hk]
  ring

theorem brownianGridPrice_scale {K r q σ k h : ℝ} {a : ℝ≥0}
    (hK : 0 < K) (ha : 0 < a) (hk : k * (a : ℝ) = r) (hh : h * (a : ℝ) = q)
    (hσ : 2 * (a : ℝ) = σ ^ 2) (T δ : ℝ≥0) (x : ℝ) :
    brownianGridPrice K r q σ T δ (x+Real.log K) =
      K*brownianGridPrice 1 k h (Real.sqrt 2) (a*T) (a*δ) x := by
  have hcount : a*T/(a*δ) = T/δ := mul_div_mul_left T δ ha.ne'
  have hβ : (k-h-(Real.sqrt 2)^2/2)*(a : ℝ) = r-q-σ^2/2 := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [hk,hh,hσ]
  have hv : (Real.sqrt 2)^2*(a : ℝ) = σ^2 := by
    rwa [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  unfold brownianGridPrice
  rw [hcount]
  apply brownianGridMarkovAux_scale hK.le hβ hv
  intro i y
  rw [cappedGridTime_scale]
  exact discountedLogPayoff_scale hK hk _ y

theorem brownianGridPrice_normalization {K r q σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    (T δ : ℝ≥0) (x : ℝ) :
    brownianGridPrice K r q σ T δ (x+Real.log K) =
      K*brownianGridPrice 1 (normalizedRate r σ) (normalizedRate q σ) (Real.sqrt 2)
        ((σ^2/2).toNNReal*T) ((σ^2/2).toNNReal*δ) x := by
  have ha : 0 < σ^2/2 := by positivity
  apply brownianGridPrice_scale hK (Real.toNNReal_pos.mpr ha)
  · rw [Real.coe_toNNReal _ ha.le]
    unfold normalizedRate
    field_simp
  · rw [Real.coe_toNNReal _ ha.le]
    unfold normalizedRate
    field_simp
  · rw [Real.coe_toNNReal _ ha.le]
    ring

end MathFin.BlackScholes.AmericanPut.Stopping
