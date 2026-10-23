/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.BrownianBellman
public import MathFin.BlackScholes.AmericanPut.Stopping.BrownianUsualTransition

/-! # The same Gaussian Bellman prices in the raw and usual Brownian filtrations

Finite-grid identification and convergence remove the classical-solution premise
from raw/usual American-value equality at positive spot.

## Result

Public entry points include `usualBellmanAux_eq_brownianGridMarkovAux`,
`brownianGridPrice_eq_usualGridValue`, `brownianGridPrice_tendsto_usual`,
`brownianUsualAmericanPut_eq_raw_of_pos`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

theorem usualBellmanAux_eq_brownianGridMarkovAux {Z : ℕ → ℝ → ℝ} {C : ℝ}
    (hc : ∀ i, Continuous (Z i)) (hb : ∀ i x, ‖Z i x‖ ≤ C)
    (T δ : ℝ≥0) (β σ x : ℝ) (n i : ℕ) :
    @bellmanAux (ℝ≥0 → ℝ) (completedMeasurableSpace gaussianLimit)
      (completedMeasure gaussianLimit)
      (@cappedGridFiltration (ℝ≥0 → ℝ) (completedMeasurableSpace gaussianLimit)
          brownianUsualFiltration T δ)
      (fun j ω => Z j (brownianLogState β σ x (cappedGridTime T δ j) ω)) n i
      =ᵐ[completedMeasure gaussianLimit]
      fun ω => brownianGridMarkovAux Z T δ β σ n i
        (brownianLogState β σ x (cappedGridTime T δ i) ω) := by
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  induction n generalizing i with
  | zero => exact Eventually.of_forall (fun _ => rfl)
  | succ n ih =>
    have hcond :=
        condExp_congr_ae (m := cappedGridFiltration brownianUsualFiltration T δ i) (ih (i+1))
    have ht := brownianLogState_usual_condExp_transition
      (brownianGridMarkovAux_continuous hc hb T δ β σ n (i+1))
      (brownianGridMarkovAux_bound hb T δ β σ n (i+1))
      (cappedGridTime_mono T δ (Nat.le_succ i)) β σ x
    filter_upwards [hcond,ht] with ω hω htω
    change max _ _ = max _ _
    rw [hω]
    exact congrArg (max _) htω

theorem brownianGridPrice_eq_usualGridValue {K r q σ : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r)
    (T : ℝ≥0) {δ : ℝ≥0} (hδ : 0 < δ) (x : ℝ) :
    brownianGridPrice K r q σ T δ x =
      @gridAmericanPutValue (ℝ≥0 → ℝ) (completedMeasurableSpace gaussianLimit)
        (completedMeasure gaussianLimit) brownianUsualFiltration brownian
        K r q σ (Real.exp x) T δ := by
  let μ := completedMeasure gaussianLimit
  have hz : ∀ᵐ ω ∂μ, brownian 0 ω = 0 := isBrownianReal_brownian.eval_zero_ae_eq_zero
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  rw [gridValue_eq_bellman brownian_completed_measurable brownianUsual_adapted hK hr
      (Real.exp_pos x).le hδ]
  have he := usualBellmanAux_eq_brownianGridMarkovAux
    (fun i => discountedLogPayoff_continuous K r (cappedGridTime T δ i))
    (fun i y => discountedLogPayoff_bound hK hr (cappedGridTime T δ i) y)
    T δ (r-q-σ^2/2) σ x ⌈T/δ⌉₊ 0
  rw [gridReward_eq_discountedLogPayoff]
  simp only [finiteBellman,Nat.sub_zero,min_eq_left (Nat.zero_le _)]
  rw [integral_congr_ae he]
  have he0 : (fun ω => brownianGridMarkovAux
      (fun i => discountedLogPayoff K r (cappedGridTime T δ i))
      T δ (r-q-σ^2/2) σ ⌈T/δ⌉₊ 0
      (brownianLogState (r-q-σ^2/2) σ x (cappedGridTime T δ 0) ω)) =ᵐ[μ]
      fun _ => brownianGridPrice K r q σ T δ x := by
    filter_upwards [hz] with ω hω
    simp [cappedGridTime,brownianLogState,hω,brownianGridPrice]
  rw [integral_congr_ae he0]
  simp

theorem brownianGridPrice_tendsto_usual {K r q σ : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r)
    (T : ℝ≥0) (x : ℝ) :
    Tendsto (fun n => brownianGridPrice K r q σ T (gridStep n) x) atTop
      (𝓝 (brownianUsualAmericanPut K r q σ (Real.exp x) T)) := by
  let μ := completedMeasure gaussianLimit
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  have he : (fun n => brownianGridPrice K r q σ T (gridStep n) x) =
      fun n => gridAmericanPutValue μ brownianUsualFiltration brownian
        K r q σ (Real.exp x) T (gridStep n) :=
    funext (fun n => brownianGridPrice_eq_usualGridValue hK hr T (gridStep_pos n) x)
  rw [he]
  exact gridValue_tendsto_americanValue brownian_completed_measurable continuous_brownian hK hr
      (Real.exp_pos x).le

/-- No classical solution, volatility sign, or dividend restriction is needed. -/
theorem brownianUsualAmericanPut_eq_raw_of_pos {K r q σ S : ℝ}
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 < S) (T : ℝ≥0) :
    brownianUsualAmericanPut K r q σ S T = brownianAmericanPut K r q σ S T := by
  have he := tendsto_nhds_unique
    (brownianGridPrice_tendsto_usual (q := q) (σ := σ) hK hr T (Real.log S))
    (brownianGridPrice_tendsto (q := q) (σ := σ) hK hr T (Real.log S))
  simpa only [Real.exp_log hS] using he

theorem brownianGridPrice_tendsto_canonical {k h : ℝ} (hk : 0 ≤ k) (x t : ℝ) :
    Tendsto (fun n => brownianGridPrice 1 k h (Real.sqrt 2) t.toNNReal (gridStep n) x)
      atTop (𝓝 (canonicalPrice k h x t)) :=
  brownianGridPrice_tendsto_usual (by norm_num) hk t.toNNReal x

end MathFin.BlackScholes.AmericanPut.Stopping
