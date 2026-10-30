/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.AmericanWaiting
public import MathFin.BlackScholes.AmericanPut.Stopping.ActualContact

/-! # Supermartingality of the actual normalized American price

This process is built from the stopping supremum, not from an assumed classical
solution. The waiting inequality supplies the conditional supermartingale bound.

## Result

Public entry points include `canonicalPrice_transition`, `canonicalDiscountedPrice`,
`canonicalDiscountedPrice_initial`, `canonicalDiscountedPrice_eq_classicalCandidate`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped NNReal Topology
open MathFin.ItoLocalMartingale (nullAugmentation supermartingale_nullAugmentation)

theorem canonicalPrice_transition {k h : ℝ} (hk : 0 ≤ k) {i j T : ℝ≥0}
    (hij : i ≤ j) (hjT : j ≤ T) (x : ℝ) :
    Real.exp (-k*(j : ℝ))*brownianHeatFlow (fun y => canonicalPrice k h y ((T : ℝ)-(j : ℝ)))
      (2*((j : ℝ)-(i : ℝ))).toNNReal (x+(k-h-1)*((j : ℝ)-(i : ℝ))) ≤
      Real.exp (-k*(i : ℝ))*canonicalPrice k h x ((T : ℝ)-(i : ℝ)) := by
  have he := mul_le_mul_of_nonneg_left (canonicalPrice_wait (h := h) hk (j-i) (T-j) x)
    (Real.exp_pos (-k*(i : ℝ))).le
  have hexp : Real.exp (-k*(i : ℝ))*Real.exp (-k*((j-i : ℝ≥0) : ℝ)) =
      Real.exp (-k*(j : ℝ)) := by
    rw [← Real.exp_add,NNReal.coe_sub hij]
    congr 1
    ring
  have htime : (((j-i)+(T-j) : ℝ≥0) : ℝ) = (T : ℝ)-(i : ℝ) := by
    rw [NNReal.coe_add,NNReal.coe_sub hij,NNReal.coe_sub hjT]
    ring
  rw [← mul_assoc,hexp,htime,NNReal.coe_sub hij,NNReal.coe_sub hjT] at he
  exact he

/-- The canonical price along the Brownian log-state at remaining time `T-min t T`,
discounted by `Real.exp (-k*(min t T))`. -/
noncomputable def canonicalDiscountedPrice (k h x : ℝ) (T t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  Real.exp (-k*(min t T : ℝ≥0))*canonicalPrice k h
    (brownianLogState (k-h-1) (Real.sqrt 2) x (min t T) ω) ((T : ℝ)-(min t T : ℝ≥0))

theorem canonicalDiscountedPrice_initial (k h x : ℝ) (T : ℝ≥0) :
    canonicalDiscountedPrice k h x T 0 =ᵐ[gaussianLimit] fun _ => canonicalPrice k h x (T : ℝ) := by
  filter_upwards [isBrownianReal_brownian.eval_zero_ae_eq_zero] with ω hω
  simp [canonicalDiscountedPrice,brownianLogState,hω]

/-- The discounted price process is the classical candidate at strike `1`, rate `k`, dividend
`h`, volatility `Real.sqrt 2` and spot `Real.exp x`. -/
theorem canonicalDiscountedPrice_eq_classicalCandidate (k h x : ℝ) (T : ℝ≥0) :
    canonicalDiscountedPrice k h x T =
      classicalCandidate brownian 1 k h (Real.sqrt 2) (Real.exp x) (canonicalPrice k h) T := by
  funext t ω
  simp only [canonicalDiscountedPrice,classicalCandidate,classicalLogSpot_canonical,
    sqrt_two_sq_div_two_mul,one_mul,brownianLogState]

theorem canonicalDiscountedPrice_dominates {k h : ℝ} (hk : 0 ≤ k) (x : ℝ)
    (T t : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    frozenPutReward brownian 1 k h (Real.sqrt 2) (Real.exp x) T t ω ≤
      canonicalDiscountedPrice k h x T t ω := by
  rw [canonicalDiscountedPrice_eq_classicalCandidate]
  exact sub_nonneg.mp (classicalGap_nonneg (W := brownian) (K := 1) (r := k) (q := h)
    (σ := Real.sqrt 2) (S := Real.exp x) (canonicalPrice_putEnvelope hk) one_pos
    (Real.exp_pos x) T t ω)

theorem canonicalDiscountedPrice_bound {k h : ℝ} (hk : 0 ≤ k) (x : ℝ)
    (T t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ‖canonicalDiscountedPrice k h x T t ω‖ ≤ 1 := by
  obtain ⟨hlo,hhi⟩ := classicalCandidate_bounds (q := h) (σ := Real.sqrt 2) (S := Real.exp x)
    (canonicalPrice_putEnvelope hk) brownian zero_le_one hk T t ω
  rw [canonicalDiscountedPrice_eq_classicalCandidate,Real.norm_eq_abs,abs_of_nonneg hlo]
  exact hhi

theorem canonicalDiscountedPrice_continuous {k h : ℝ} (hk : 0 ≤ k) (x : ℝ)
    (T : ℝ≥0) (ω : ℝ≥0 → ℝ) : Continuous (fun t => canonicalDiscountedPrice k h x T t ω) := by
  rw [canonicalDiscountedPrice_eq_classicalCandidate]
  exact classicalCandidate_continuous (canonicalPrice_putEnvelope hk) continuous_brownian T ω

theorem canonicalDiscountedPrice_adapted {k h : ℝ} (hk : 0 ≤ k) (x : ℝ) (T : ℝ≥0) :
    Adapted brownianFiltration (canonicalDiscountedPrice k h x T) := by
  rw [canonicalDiscountedPrice_eq_classicalCandidate]
  exact classicalCandidate_adapted (canonicalPrice_putEnvelope hk) brownian_adapted T

theorem canonicalDiscountedPrice_condExp_le {k h : ℝ} (hk : 0 ≤ k) (x : ℝ)
    {i j T : ℝ≥0} (hij : i ≤ j) (hjT : j ≤ T) :
    gaussianLimit[canonicalDiscountedPrice k h x T j | brownianFiltration i] ≤ᵐ[gaussianLimit]
      canonicalDiscountedPrice k h x T i := by
  let f : ℝ → ℝ := fun y => Real.exp (-k*(j : ℝ))*canonicalPrice k h y ((T : ℝ)-(j : ℝ))
  have hf : Continuous f := continuous_const.mul
    ((canonicalPrice_continuous hk).comp (continuous_id.prodMk continuous_const))
  have hb (y : ℝ) : ‖f y‖ ≤ 1 := by
    obtain ⟨hlo,hhi⟩ := canonicalPrice_bounds (h := h) hk y ((T : ℝ)-(j : ℝ))
    have hp0 : 0 ≤ canonicalPrice k h y ((T : ℝ)-(j : ℝ)) := (le_max_right _ _).trans hlo
    have he : Real.exp (-k*(j : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [j.coe_nonneg])
    change ‖Real.exp (-k*(j : ℝ))*canonicalPrice k h y ((T : ℝ)-(j : ℝ))‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hp0)]
    exact (mul_le_mul_of_nonneg_left hhi (Real.exp_pos _).le).trans (by simpa using he)
  have ht := brownianLogState_isGaussianMarkov (k-h-1) (Real.sqrt 2) x hf hb hij
  have hj : (fun ω => f (brownianLogState (k-h-1) (Real.sqrt 2) x j ω)) =
      canonicalDiscountedPrice k h x T j := by
    funext ω
    simp only [canonicalDiscountedPrice,min_eq_left hjT,f]
  rw [hj] at ht
  filter_upwards [ht] with ω htω
  rw [htω]
  have hc :=
      canonicalPrice_transition (h := h) hk hij hjT (brownianLogState (k-h-1) (Real.sqrt 2) x i ω)
  simpa only [brownianHeatFlow,f,integral_const_mul,Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
    canonicalDiscountedPrice,min_eq_left (hij.trans hjT)] using hc

theorem canonicalDiscountedPrice_supermartingale {k h : ℝ} (hk : 0 ≤ k) (x : ℝ) (T : ℝ≥0) :
    Supermartingale (canonicalDiscountedPrice k h x T) brownianFiltration gaussianLimit := by
  let U := canonicalDiscountedPrice k h x T
  have ha : StronglyAdapted brownianFiltration U :=
    fun t => (canonicalDiscountedPrice_adapted hk x T t).stronglyMeasurable
  have hi (t : ℝ≥0) : Integrable (U t) gaussianLimit :=
    (integrable_const (1 : ℝ)).mono' ((ha t).mono (brownianFiltration.le t)).aestronglyMeasurable
      (Eventually.of_forall (canonicalDiscountedPrice_bound hk x T t))
  refine ⟨ha,?_,hi⟩
  intro i j hij
  change gaussianLimit[U j | brownianFiltration i] ≤ᵐ[gaussianLimit] U i
  by_cases hjT : j ≤ T
  · exact canonicalDiscountedPrice_condExp_le hk x hij hjT
  · have hTj := le_of_not_ge hjT
    have hj : U j = U T := by
      funext ω
      simp only [U,canonicalDiscountedPrice,min_eq_right hTj,min_self]
    rw [hj]
    by_cases hiT : i ≤ T
    · exact canonicalDiscountedPrice_condExp_le hk x hiT le_rfl
    · have hTi := le_of_not_ge hiT
      have hiU : U i = U T := by
        funext ω
        simp only [U,canonicalDiscountedPrice,min_eq_right hTi,min_self]
      rw [← hiU,condExp_of_stronglyMeasurable (brownianFiltration.le i) (ha i) (hi i)]

theorem canonicalDiscountedPrice_usual_supermartingale {k h : ℝ} (hk : 0 ≤ k) (x : ℝ) (T : ℝ≥0) :
    Supermartingale (canonicalDiscountedPrice k h x T) brownianUsualFiltration
      (completedMeasure gaussianLimit) := by
  have hu := bounded_supermartingale_completion gaussianLimit
    (canonicalDiscountedPrice_supermartingale (h := h) hk x T)
        (canonicalDiscountedPrice_bound hk x T)
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  exact bounded_continuous_supermartingale_rightCont (supermartingale_nullAugmentation hu)
    (canonicalDiscountedPrice_continuous hk x T) (canonicalDiscountedPrice_bound hk x T)

end MathFin.BlackScholes.AmericanPut.Stopping
