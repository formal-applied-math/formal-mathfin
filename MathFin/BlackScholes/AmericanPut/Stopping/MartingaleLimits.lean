/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.BrownianLocalVerification

/-!
# Bounded martingale limits and stopping-rule approximation

Preserve the conditional expectation identities by dominated convergence on
earlier measurable events. This is the limit step for interior stopping times
approaching first contact; no martingale property is assumed for the limit.

## Result

Public entry points include `martingale_of_bounded_limits`,
`stoppedCandidate_martingale_of_rule_limit`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory ProbabilityTheory Set Filter Boundary
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem martingale_of_bounded_limits {X : ℝ≥0 → Ω → ℝ} {Y : ℕ → ℝ≥0 → Ω → ℝ}
    (hadapt : StronglyAdapted 𝓕 X) (hY : ∀ n, Martingale (Y n) 𝓕 P) {C : ℝ}
    (hXbound : ∀ t ω, ‖X t ω‖ ≤ C) (hYbound : ∀ n t ω, ‖Y n t ω‖ ≤ C)
    (hlim : ∀ t, ∀ᵐ ω ∂P, Tendsto (fun n => Y n t ω) atTop (𝓝 (X t ω))) :
    Martingale X 𝓕 P := by
  have hint : ∀ t, Integrable (X t) P := fun t =>
    (integrable_const C).mono' ((hadapt t).mono (𝓕.le t)).aestronglyMeasurable
      (Eventually.of_forall (hXbound t))
  apply martingale_of_setIntegral_eq hadapt hint
  intro i j hij s hs
  have hconv (t : ℝ≥0) : Tendsto (fun n => ∫ ω in s, Y n t ω ∂P) atTop
      (𝓝 (∫ ω in s, X t ω ∂P)) :=
    tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => ((hY n).integrable t).aestronglyMeasurable.restrict) (integrable_const C)
      (fun n => Eventually.of_forall (hYbound n t)) (ae_restrict_of_ae (hlim t))
  have hi := hconv i
  have heq : (fun n => ∫ ω in s, Y n i ω ∂P) = (fun n => ∫ ω in s, Y n j ω ∂P) :=
    funext (fun n => (hY n).setIntegral_eq hij hs)
  rw [heq] at hi
  exact tendsto_nhds_unique hi (hconv j)

theorem stoppedCandidate_martingale_of_rule_limit {W : ℝ≥0 → Ω → ℝ}
    {k h K r q σ S : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {T : ℝ≥0}
    (hp : DividendPutSolution k h p b) (hadapt : Adapted 𝓕 W)
    (hpaths : ∀ ω, Continuous (fun t => W t ω)) (hK : 0 ≤ K) (hr : 0 ≤ r)
    (θ : StoppingRule 𝓕 T) (θn : ℕ → StoppingRule 𝓕 T)
    (hθ : ∀ᵐ ω ∂P, Tendsto (fun n => (θn n).time ω) atTop (𝓝 (θ.time ω)))
    (hmart : ∀ n, Martingale (fun t ω => classicalCandidate W K r q σ S p T
      (min t ((θn n).time ω)) ω) 𝓕 P) :
    Martingale (fun t ω => classicalCandidate W K r q σ S p T (min t (θ.time ω)) ω) 𝓕 P := by
  have hb : ∀ t ω, ‖classicalCandidate W K r q σ S p T t ω‖ ≤ K := by
    intro t ω
    obtain ⟨hlo,hhi⟩ := classicalCandidate_bounds (q := q) (σ := σ) (S := S) hp W hK hr T t ω
    simpa only [Real.norm_eq_abs,abs_of_nonneg hlo] using hhi
  apply martingale_of_bounded_limits
    (stoppedClassicalCandidate_stronglyAdapted hp hadapt hpaths θ) hmart
    (fun t ω => hb _ ω) (fun n t ω => hb _ ω)
  intro t
  filter_upwards [hθ] with ω hω
  exact ((classicalCandidate_continuous hp hpaths T ω).tendsto (min t (θ.time ω))).comp
    (tendsto_const_nhds.min hω)

end MathFin.BlackScholes.AmericanPut.Stopping
