/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.Models.BlackScholes.American.Stopping.BrownianBellman
public import MathFin.Models.BlackScholes.American.Stopping.BrownianUsualTransition

/-! # The same Gaussian Snell-envelope prices in the raw and usual Brownian filtrations

Finite-grid identification and convergence remove the classical-solution premise
from raw/usual American-value equality at positive spot.

## Main results

* `brownianGridPrice_eq_usualGridValue`: for `0 ≤ K`, `0 ≤ r` and mesh `δ > 0`, the raw Brownian
  grid price equals the grid American put value computed in the usual filtration, at spot
  `exp x`.
* `brownianGridPrice_tendsto_usual`: for `0 ≤ K`, `0 ≤ r`, the grid prices along the meshes
  `gridStep n` converge to the usual-filtration American put price at spot `exp x`.
* `brownianUsualAmericanPut_eq_raw_of_pos`: for `0 ≤ K`, `0 ≤ r` and `S > 0`, with no classical
  solution assumed, the usual and raw American put values agree.
* `brownianGridPrice_tendsto_canonical`: for `0 ≤ k`, the normalized grid prices converge to the
  canonical price.

## Tags

raw and usual filtration, finite-grid price, Snell envelope, Gaussian Markov, American put,
MSC 60G40, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

theorem brownianGridPrice_eq_usualGridValue {K r q σ : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r)
    (T : ℝ≥0) {δ : ℝ≥0} (hδ : 0 < δ) (x : ℝ) :
    brownianGridPrice K r q σ T δ x =
      @gridAmericanPutValue (ℝ≥0 → ℝ) (completedMeasurableSpace gaussianLimit)
        (completedMeasure gaussianLimit) brownianUsualFiltration brownian
        K r q σ (Real.exp x) T δ := by
  have hz : ∀ᵐ ω ∂completedMeasure gaussianLimit, brownian 0 ω = 0 :=
    isBrownianReal_brownian.eval_zero_ae_eq_zero
  exact @brownianGridPrice_eq_gridAmericanPutValue (completedMeasurableSpace gaussianLimit)
    (completedMeasure gaussianLimit) _ brownianUsualFiltration brownian_completed_measurable
    brownianUsual_adapted hz brownianLogState_usual_isGaussianMarkov _ _ _ _ hK hr T _ hδ x

theorem brownianGridPrice_tendsto_usual {K r q σ : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r)
    (T : ℝ≥0) (x : ℝ) :
    Tendsto (fun n => brownianGridPrice K r q σ T (gridStep n) x) atTop
      (𝓝 (brownianUsualAmericanPut K r q σ (Real.exp x) T)) := by
  let μ := completedMeasure gaussianLimit
  let : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
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
