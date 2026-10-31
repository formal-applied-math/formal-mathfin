/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.LocalizationTimes
public import MathFin.BlackScholes.AmericanPut.Stopping.MartingaleLimits

/-!
# Interior approximation of the constructed Brownian first-contact rule

The sequence is explicit and converges pathwise. This module reduces contact
martingality to the interior local properties. `ContactMartingale` subsequently
proves the interior martingale properties from the PDE and Ito's formula.

## Result

Public entry points include `brownianInteriorRule`, `brownianInteriorRule_tendsto`,
`brownian_contact_martingale_of_interior_localMartingales`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory ProbabilityTheory Boundary Filter
open scoped NNReal Topology

variable {K r q σ S : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}

/-- The `n`-th interior localization rule of the constructed Brownian model: `interiorRule`
applied to the classical gap `classicalGap brownian K r q σ S p T`. -/
noncomputable def brownianInteriorRule
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (T : ℝ≥0) (n : ℕ) : StoppingRule brownianFiltration T :=
  interiorRule (Z := classicalGap brownian K r q σ S p T)
    (classicalGap_adapted hp.toPutEnvelope brownian_adapted T) brownian_adapted
    (classicalGap_continuous hp.toPutEnvelope continuous_brownian T) continuous_brownian T n

theorem brownianInteriorRule_tendsto
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 < K) (hS : 0 < S) (T : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    Tendsto (fun n => (brownianInteriorRule (K := K) (S := S) hp T n).time ω) atTop
      (𝓝 ((brownianClassicalContactRule hp hK hS T).time ω)) :=
  interiorRule_tendsto_contact (classicalGap_adapted hp.toPutEnvelope brownian_adapted T)
    brownian_adapted (classicalGap_continuous hp.toPutEnvelope continuous_brownian T)
    continuous_brownian (classicalGap_nonneg hp.toPutEnvelope hK hS T)
    (classicalGap_terminal hp.toPutEnvelope hK hS T) ω

theorem brownian_contact_martingale_of_interior_localMartingales
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 < K) (hr : 0 ≤ r) (hS : 0 < S) (T : ℝ≥0)
    (hlocal : ∀ n, IsLocalMartingale (fun t ω => classicalCandidate brownian K r q σ S p T
      (min t ((brownianInteriorRule (K := K) (S := S) hp T n).time ω)) ω) brownianAugFiltration
          gaussianLimit) :
    Martingale (fun t ω => classicalCandidate brownian K r q σ S p T
      (min t ((brownianClassicalContactRule hp hK hS T).time ω)) ω) brownianFiltration
          gaussianLimit :=
  stoppedCandidate_martingale_of_rule_limit hp brownian_adapted continuous_brownian hK.le hr
    (brownianClassicalContactRule hp hK hS T) (brownianInteriorRule hp T)
    (Eventually.of_forall (brownianInteriorRule_tendsto hp hK hS T))
    (fun n => brownian_stoppedCandidate_martingale_of_local hp hK hr _ (hlocal n))

end MathFin.BlackScholes.AmericanPut.Stopping
