/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.InteriorIto

/-!
# Martingality of the classical candidate stopped at first contact

Interior Ito representations, stopping stability, bounded promotion and the
contact-time limit discharge the contact-martingale verification obligation.
The global supermartingale property is separate.

## Result

Public entry points include `localMartingale_of_ae_path_eq`, `localMartingale_stopped_indicator`,
`brownianInteriorRule_martingale`, `brownianClassicalContactRule_martingale`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped NNReal Topology

theorem localMartingale_of_ae_path_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {X Y : ℝ≥0 → Ω → ℝ} (hX : IsLocalMartingale X 𝓕 P)
    (hY : StronglyAdapted 𝓕 Y) (hcY : ∀ ω, Continuous (fun t => Y t ω))
    (heq : ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω) : IsLocalMartingale Y 𝓕 P := by
  classical
  obtain ⟨τ,hτ,hlocal⟩ := hX
  refine ⟨τ,hτ,fun n => ⟨?_,?_⟩⟩
  · apply (hlocal n).1.congr
      (hY.stoppedProcess_indicator (fun ω => (hcY ω).isCadlag.right_continuous)
          (hτ.isStoppingTime n))
    intro t
    filter_upwards [heq] with ω hω
    simp only [stoppedProcess]
    by_cases hs : ω ∈ {ω | ⊥ < τ n ω}
    · simp only [indicator_of_mem hs,hω]
    · simp only [indicator_of_notMem hs]
  · exact isStable_isCadlag Y (fun ω => (hcY ω).isCadlag) (τ n) (hτ.isStoppingTime n)

theorem localMartingale_stopped_indicator {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {M : ℝ≥0 → Ω → ℝ} (hM : IsLocalMartingale M 𝓕 P)
    {θ : Ω → ℝ≥0} (hθ : IsStoppingTime 𝓕 (fun ω => (θ ω : WithTop ℝ≥0))) :
    IsLocalMartingale (fun t ω => {ω | 0 < θ ω}.indicator (fun ω => M (min t (θ ω)) ω) ω) 𝓕 P := by
  have hh := isStable_martingale.locally M hM (fun ω => (θ ω : WithTop ℝ≥0)) hθ
  have he : stoppedProcess (fun i => {ω | ⊥ < (θ ω : WithTop ℝ≥0)}.indicator (M i))
      (fun ω => (θ ω : WithTop ℝ≥0)) =
      (fun t ω => {ω | 0 < θ ω}.indicator (fun ω => M (min t (θ ω)) ω) ω) := by
    funext t ω
    have htime : (min (t : WithTop ℝ≥0) (θ ω : WithTop ℝ≥0)).untopA = min t (θ ω) := by
      rw [← WithTop.coe_min]
      rfl
    have hsets : {ω | (⊥ : WithTop ℝ≥0) < (θ ω : WithTop ℝ≥0)} = {ω | 0 < θ ω} := by
      ext ω
      exact WithTop.coe_lt_coe
    simp only [stoppedProcess,htime,hsets]
    by_cases hpos : 0 < θ ω <;> simp [hpos]
  rw [he] at hh
  exact hh

theorem brownianInteriorRule_martingale {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {K r q σ S : ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 < K) (hr : 0 ≤ r) (hS : 0 < S) (hσ : 0 < σ) (T : ℝ≥0) (n : ℕ) :
    Martingale (fun t ω => classicalCandidate brownian K r q σ S p T
      (min t ((brownianInteriorRule (K := K) (S := S) hp T n).time ω)) ω)
      brownianFiltration gaussianLimit := by
  let θ := brownianInteriorRule (K := K) (S := S) hp T n
  let U := classicalCandidate brownian K r q σ S p T
  let X : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ := fun t ω => U (min t (θ.time ω)) ω-U 0 ω
  have hA := stoppedClassicalCandidate_stronglyAdapted
    (K := K) (r := r) (q := q) (σ := σ) (S := S) hp brownian_adapted continuous_brownian θ
  have hU0 : StronglyMeasurable[brownianFiltration 0] (U 0) :=
    (classicalCandidate_adapted hp.toPutEnvelope brownian_adapted T 0).stronglyMeasurable
  have hXadapt : StronglyAdapted brownianFiltration X :=
    fun t => (hA t).sub (hU0.mono (brownianFiltration.mono zero_le))
  have hXcont : ∀ ω, Continuous (fun t => X t ω) := fun ω =>
    ((classicalCandidate_continuous hp.toPutEnvelope continuous_brownian T ω).comp
      (continuous_id.min continuous_const)).sub continuous_const
  have hb : ∀ t ω, ‖U t ω‖ ≤ K :=
    classicalCandidate_norm_le (q := q) (σ := σ) (S := S) hp.toPutEnvelope brownian hK.le hr T
  obtain ⟨M,_hMcont,hM,heq⟩ := brownianInteriorRule_ito_representation hp hK hS hσ T n
  have hθ : IsStoppingTime brownianAugFiltration (fun ω => (θ.time ω : WithTop ℝ≥0)) :=
    fun t => brownianFiltration_le_aug t _ (θ.stopping t)
  have hlocal : IsLocalMartingale X brownianAugFiltration gaussianLimit :=
    localMartingale_of_ae_path_eq (localMartingale_stopped_indicator hM hθ)
      (fun t => (hXadapt t).mono (brownianFiltration_le_aug t)) hXcont
      (heq.mono (fun ω hω t => (hω t).symm))
  have hXM : Martingale X brownianFiltration gaussianLimit :=
    martingale_smaller_filtration brownianFiltration_le_aug
      (bounded_localMartingale_is_martingale hlocal
        (fun t => (hXadapt t).mono (brownianFiltration_le_aug t))
        (fun t ω => (norm_sub_le _ _).trans (add_le_add (hb _ ω) (hb 0 ω)))) hXadapt
  have hint : Integrable (U 0) gaussianLimit :=
    (integrable_const K).mono' (hU0.mono (brownianFiltration.le 0)).aestronglyMeasurable
      (Eventually.of_forall (hb 0))
  have hinit := martingale_const_fun brownianFiltration gaussianLimit hU0 hint
  convert! hXM.add hinit using 1
  ext t ω
  exact (sub_add_cancel _ _).symm

theorem brownianClassicalContactRule_martingale {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {K r q σ S : ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 < K) (hr : 0 ≤ r) (hS : 0 < S) (hσ : 0 < σ) (T : ℝ≥0) :
    Martingale (fun t ω => classicalCandidate brownian K r q σ S p T
      (min t ((brownianClassicalContactRule hp hK hS T).time ω)) ω)
      brownianFiltration gaussianLimit :=
  stoppedCandidate_martingale_of_rule_limit hp brownian_adapted continuous_brownian hK.le hr
    (brownianClassicalContactRule hp hK hS T) (brownianInteriorRule hp T)
    (Eventually.of_forall (brownianInteriorRule_tendsto hp hK hS T))
    (brownianInteriorRule_martingale hp hK hr hS hσ T)

theorem brownianClassicalContactRule_expectedReward {K r q σ S : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} (T : ℝ≥0)
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 < K) (hr : 0 ≤ r) (hS : 0 < S) (hσ : 0 < σ) :
    (∫ ω, putReward brownian K r q σ S (brownianClassicalContactRule hp hK hS T).time ω
      ∂gaussianLimit) = K*p (Real.log (S/K)) (σ^2/2*(T : ℝ)) := by
  let θ := brownianClassicalContactRule hp hK hS T
  let U := classicalCandidate brownian K r q σ S p T
  have hm := (brownianClassicalContactRule_martingale hp hK hr hS hσ T).setIntegral_eq
    (i := 0) (j := T) zero_le (s := univ) MeasurableSet.univ
  simp only [setIntegral_univ,zero_min] at hm
  have he : (fun ω => U (min T (θ.time ω)) ω) = (fun ω => U (θ.time ω) ω) := by
    funext ω
    rw [min_eq_right (θ.le_horizon ω)]
  change (∫ ω, U 0 ω ∂gaussianLimit) = ∫ ω, U (min T (θ.time ω)) ω ∂gaussianLimit at hm
  rw [he] at hm
  calc
    _ = ∫ ω, U (θ.time ω) ω ∂gaussianLimit := integral_congr_ae
      (Eventually.of_forall (fun ω => (classicalContactRule_contact
        hp.toPutEnvelope brownian_adapted continuous_brownian hK hS T ω).symm))
    _ = ∫ ω, U 0 ω ∂gaussianLimit := hm.symm
    _ = _ := by
      rw [integral_congr_ae (classicalCandidate_initial
        isBrownianReal_brownian.eval_zero_ae_eq_zero K r q σ S p T)]
      simp

theorem classicalPrice_le_brownianAmericanPut {K r q σ S : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} (T : ℝ≥0)
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 < K) (hr : 0 ≤ r) (hS : 0 < S) (hσ : 0 < σ) :
    K*p (Real.log (S/K)) (σ^2/2*(T : ℝ)) ≤ brownianAmericanPut K r q σ S T := by
  rw [← brownianClassicalContactRule_expectedReward T hp hK hr hS hσ]
  exact expectedReward_le_value measurable_brownian_uncurry hK.le hr hS.le _

theorem brownian_price_identification_of_supermartingale {K r q σ S : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {T : ℝ≥0}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 < K) (hr : 0 ≤ r) (hS : 0 < S) (hσ : 0 < σ)
    (hsuper : Supermartingale (classicalCandidate brownian K r q σ S p T) brownianFiltration
        gaussianLimit) :
    brownianAmericanPut K r q σ S T = K*p (Real.log (S/K)) (σ^2/2*(T : ℝ)) :=
  brownian_price_identification_of_martingales hp hK hr hS hsuper
    (brownianClassicalContactRule_martingale hp hK hr hS hσ T)

theorem brownian_boundary_curvature_of_supermartingales {K r q σ : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 < K) (hr : 0 ≤ r) (hσ : 0 < σ)
    (hsuper : ∀ (T : ℝ≥0) (S : ℝ), 0 < S →
      Supermartingale (classicalCandidate brownian K r q σ S p T) brownianFiltration gaussianLimit)
    {τ : ℝ} (hτ : 0 < τ) :
    0 < deriv (deriv (fun s : ℝ => brownianExerciseBoundary K r q σ s.toNNReal)) τ :=
  brownian_boundary_curvature_of_martingales hp hK hr hσ hsuper
    (fun T _ hS => brownianClassicalContactRule_martingale hp hK hr hS hσ T) hτ

end MathFin.BlackScholes.AmericanPut.Stopping
