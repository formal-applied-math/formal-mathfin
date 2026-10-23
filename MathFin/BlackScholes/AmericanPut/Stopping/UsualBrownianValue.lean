/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.CompletedSpace
public import MathFin.BlackScholes.AmericanPut.Stopping.AugmentedValue

/-! # The American value on the completed usual Brownian filtration 
## Result

Public entry points include `brownianUsualFiltration`, `brownian_completedRaw_le_usual`,
`brownian_completed_measurable`, `brownianUsualAmericanPut`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped NNReal Topology

/-- The usual filtration of `brownian`: the completed raw filtration, null-augmented and then
made right-continuous. -/
noncomputable def brownianUsualFiltration :
    Filtration ℝ≥0 (completedMeasurableSpace gaussianLimit) :=
  (ambientNullAugmentation (mΩ := completedMeasurableSpace gaussianLimit)
    (completedAmbientFiltration gaussianLimit brownianFiltration)
    (completedMeasure gaussianLimit)).rightCont

theorem brownian_completedRaw_le_usual :
    completedAmbientFiltration gaussianLimit brownianFiltration ≤ brownianUsualFiltration :=
  le_trans le_sup_left (ambientNullAugmentation (mΩ := completedMeasurableSpace gaussianLimit)
    (completedAmbientFiltration gaussianLimit brownianFiltration)
        (completedMeasure gaussianLimit)).le_rightCont

instance brownianUsualFiltration_isRightContinuous : brownianUsualFiltration.IsRightContinuous :=
  inferInstanceAs ((ambientNullAugmentation (mΩ := completedMeasurableSpace gaussianLimit)
    (completedAmbientFiltration gaussianLimit brownianFiltration)
    (completedMeasure gaussianLimit)).rightCont.IsRightContinuous)

instance brownianUsualFiltration_isComplete :
    brownianUsualFiltration.IsComplete (completedMeasure gaussianLimit) := by
  constructor
  intro s hs t
  apply (ambientNullAugmentation (mΩ := completedMeasurableSpace gaussianLimit)
    (completedAmbientFiltration gaussianLimit brownianFiltration)
    (completedMeasure gaussianLimit)).le_rightCont t
  apply (show MathFin.ItoLocalMartingale.nullsAlg _ (completedMeasure gaussianLimit) ≤
    ambientNullAugmentation (mΩ := completedMeasurableSpace gaussianLimit)
      (completedAmbientFiltration gaussianLimit brownianFiltration)
      (completedMeasure gaussianLimit) t from le_sup_right)
  exact MeasurableSpace.measurableSet_generateFrom ⟨measurableSet_of_null hs,hs⟩

theorem brownian_completed_measurable :
    @Measurable (ℝ≥0 × (ℝ≥0 → ℝ)) ℝ
      ((inferInstance : MeasurableSpace ℝ≥0).prod (completedMeasurableSpace gaussianLimit))
      inferInstance brownian.uncurry := by
  have hm (t : ℝ≥0) : Measurable[completedMeasurableSpace gaussianLimit] (brownian t) :=
    (measurable_brownian t).mono (ambient_le_completion gaussianLimit) le_rfl
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  exact measurable_uncurry_of_continuous_of_measurable continuous_brownian
    hm

/-- The `americanPutValue` of `brownian` on `brownianUsualFiltration`, under the completed
Gaussian limit measure. -/
noncomputable def brownianUsualAmericanPut (K r q σ S : ℝ) (T : ℝ≥0) : ℝ :=
  @americanPutValue (ℝ≥0 → ℝ) (completedMeasurableSpace gaussianLimit)
    (completedMeasure gaussianLimit) brownianUsualFiltration brownian K r q σ S T

theorem brownianClassicalCandidate_usual_supermartingale {K r q σ S : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hσ : 0 < σ) (T : ℝ≥0) :
    Supermartingale (classicalCandidate brownian K r q σ S p T)
      brownianUsualFiltration (completedMeasure gaussianLimit) := by
  have hb (t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ‖classicalCandidate brownian K r q σ S p T t ω‖ ≤ K := by
    obtain ⟨hlo,hhi⟩ := classicalCandidate_bounds (q := q) (σ := σ) (S := S) hp brownian hK hr T t ω
    simpa only [Real.norm_eq_abs,abs_of_nonneg hlo] using hhi
  have hu := bounded_supermartingale_completion gaussianLimit
    (brownianClassicalCandidate_supermartingale hp hK hr hσ T) hb
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  exact bounded_continuous_supermartingale_rightCont (supermartingale_ambientNullAugmentation hu)
    (classicalCandidate_continuous hp continuous_brownian T) hb

theorem brownianUsualAmericanPut_eq_raw {K r q σ S : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 < K) (hr : 0 ≤ r) (hσ : 0 < σ) (hS : 0 < S) (T : ℝ≥0) :
    brownianUsualAmericanPut K r q σ S T = brownianAmericanPut K r q σ S T := by
  have hb (t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ‖classicalCandidate brownian K r q σ S p T t ω‖ ≤ K := by
    obtain ⟨hlo,hhi⟩ :=
        classicalCandidate_bounds (q := q) (σ := σ) (S := S) hp brownian hK.le hr T t ω
    simpa only [Real.norm_eq_abs,abs_of_nonneg hlo] using hhi
  have hU0 : StronglyMeasurable (classicalCandidate brownian K r q σ S p T 0) :=
    ((classicalCandidate_adapted hp brownian_adapted T 0).mono (brownianFiltration.le 0)
        le_rfl).stronglyMeasurable
  have hI0 := integral_completion_original gaussianLimit hU0
  have hinitial :=
      classicalCandidate_initial isBrownianReal_brownian.eval_zero_ae_eq_zero K r q σ S p T
  let θ := brownianClassicalContactRule hp hK hS T
  have hreward := integral_completion_original gaussianLimit
    (putReward_measurable measurable_brownian_uncurry K r q σ S
        θ.measurable_time).stronglyMeasurable
  have hcontact := brownianClassicalContactRule_expectedReward T hp hK hr hS hσ
  have hprice := brownian_price_identification (T := T) hp hK hr hS hσ
  have hsuper := brownianClassicalCandidate_usual_supermartingale (S := S) hp hK.le hr hσ T
  let θtime := θ.time
  have θstop := θ.stopping
  have θbound := θ.le_horizon
  let μ := completedMeasure gaussianLimit
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  let θ' : BoundedRule brownianUsualFiltration T :=
    { time := θtime
      stopping := fun t => brownian_completedRaw_le_usual t _ (θstop t)
      le_horizon := θbound }
  apply le_antisymm
  · have hu := value_le_supermartingale_candidate brownian_completed_measurable hK.le hr hS.le
      hsuper (classicalCandidate_continuous hp continuous_brownian T) hb
      (fun _ ht ω => classicalCandidate_dominates hp brownian hK hS ht ω)
    rw [hI0,integral_congr_ae hinitial] at hu
    simp only [integral_const,probReal_univ,one_smul] at hu
    rw [hprice]
    convert! hu using 1
  · have hl := expectedReward_le_value (P := μ) (q := q) (σ := σ)
      brownian_completed_measurable hK.le hr hS.le θ'
    change (∫ ω, putReward brownian K r q σ S θtime ω ∂_) ≤ _ at hl
    rw [hreward] at hl
    rw [hprice]
    rw [hcontact] at hl
    exact hl

/-- The `exerciseThreshold` of `brownian` on `brownianUsualFiltration`, under the completed
Gaussian limit measure. -/
noncomputable def brownianUsualExerciseBoundary (K r q σ : ℝ) (T : ℝ≥0) : ℝ :=
  @exerciseThreshold (ℝ≥0 → ℝ) (completedMeasurableSpace gaussianLimit)
    (completedMeasure gaussianLimit) brownianUsualFiltration brownian K r q σ T

theorem brownianUsual_boundary_eq_classical {K r q σ : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 < K) (hr : 0 ≤ r) (hσ : 0 < σ) {τ : ℝ} (hτ : 0 < τ) :
    brownianUsualExerciseBoundary K r q σ τ.toNNReal = K*Real.exp (b (σ^2/2*τ)) := by
  have hprice (S : ℝ) (hS : 0 < S) : brownianUsualAmericanPut K r q σ S τ.toNNReal =
      K*p (Real.log (S/K)) (σ^2/2*τ) := by
    rw [brownianUsualAmericanPut_eq_raw hp hK hr hσ hS,
      brownian_price_identification hp hK hr hS hσ,Real.coe_toNNReal _ hτ.le]
  have hz : ∀ᵐ ω ∂completedMeasure gaussianLimit, brownian 0 ω = 0 :=
    isBrownianReal_brownian.eval_zero_ae_eq_zero
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  exact threshold_eq_of_price_identification hp brownian_completed_measurable hz hK hr
    (mul_pos (div_pos (sq_pos_of_pos hσ) (by norm_num)) hτ) hprice

theorem brownianUsual_boundary_conclusions {K r q σ : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 < K) (hr : 0 ≤ r) (hσ : 0 < σ) {τ : ℝ} (hτ : 0 < τ) :
    (0 ≤ deriv
        (deriv (fun s : ℝ => Real.log (brownianUsualExerciseBoundary K r q σ s.toNNReal/K))) τ) ∧
      0 < deriv (deriv (fun s : ℝ => brownianUsualExerciseBoundary K r q σ s.toNNReal)) τ := by
  have he : (fun s : ℝ => brownianUsualExerciseBoundary K r q σ s.toNNReal) =ᶠ[𝓝 τ]
      (fun s : ℝ => brownianExerciseBoundary K r q σ s.toNNReal) := by
    filter_upwards [Ioi_mem_nhds hτ] with s hs
    rw [brownianUsual_boundary_eq_classical hp hK hr hσ hs,brownian_boundary_eq_classical
        hp hK hr hσ hs]
  have hlog := he.fun_comp (fun y => Real.log (y/K))
  simp only [Function.comp_def] at hlog
  rw [he.deriv.deriv_eq,hlog.deriv.deriv_eq]
  exact brownian_boundary_conclusions hp hK hr hσ hτ

end MathFin.BlackScholes.AmericanPut.Stopping
