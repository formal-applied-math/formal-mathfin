/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.BoundedLocalMartingale
public import MathFin.BlackScholes.AmericanPut.Stopping.BrownianVerification

/-!
# Bounded stopped-candidate promotion and raw-filtration transfer

The classical contract supplies the boundedness and raw adaptation needed to
promote a stopped local martingale on the null augmentation and transfer it to
our financial model's raw natural filtration. The local hypothesis is explicit
in this module; `ContactMartingale` later assembles the Ito representations and
proves the raw contact-martingale property without that extra hypothesis.

## Result

Public entry points include `brownianAugFiltration`, `brownianFiltration_le_aug`,
`stoppedClassicalCandidate_stronglyAdapted`, `brownian_stoppedCandidate_martingale_of_local`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory ProbabilityTheory Boundary
open scoped NNReal

/-- The raw Brownian filtration with the `gaussianLimit`-null measurable sets adjoined at each
time, via `augFiltration`. -/
noncomputable def brownianAugFiltration :=
  MathFin.ItoIntegralProcessLocalMartingaleGeneral.augFiltration (μ := gaussianLimit)
      measurable_brownian

theorem brownianFiltration_le_aug : brownianFiltration ≤ brownianAugFiltration :=
  le_sup_left

theorem stoppedClassicalCandidate_stronglyAdapted {Ω : Type*} [MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → ℝ}
    {k h K r q σ S : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {T : ℝ≥0}
    (hp : DividendPutSolution k h p b) (hadapt : Adapted 𝓕 W)
    (hpaths : ∀ ω, Continuous (fun t => W t ω)) (θ : BoundedRule 𝓕 T) :
    StronglyAdapted 𝓕 (fun t ω => classicalCandidate W K r q σ S p T (min t (θ.time ω)) ω) := by
  have hA : StronglyAdapted 𝓕 (classicalCandidate W K r q σ S p T) :=
    fun t => (classicalCandidate_adapted hp hadapt T t).stronglyMeasurable
  convert! hA.stoppedProcess (classicalCandidate_continuous hp hpaths T) θ.stopping using 1

theorem brownian_stoppedCandidate_martingale_of_local {K r q σ S : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {T : ℝ≥0}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 < K) (hr : 0 ≤ r) (θ : BoundedRule brownianFiltration T)
    (hlocal : IsLocalMartingale (fun t ω => classicalCandidate brownian K r q σ S p T
      (min t (θ.time ω)) ω) brownianAugFiltration gaussianLimit) :
    Martingale (fun t ω => classicalCandidate brownian K r q σ S p T
      (min t (θ.time ω)) ω) brownianFiltration gaussianLimit := by
  have hadapt := stoppedClassicalCandidate_stronglyAdapted
    (K := K) (r := r) (q := q) (σ := σ) (S := S) hp brownian_adapted continuous_brownian θ
  apply martingale_smaller_filtration brownianFiltration_le_aug _ hadapt
  apply bounded_localMartingale_is_martingale hlocal
    (fun t => (hadapt t).mono (brownianFiltration_le_aug t)) (C := K)
  intro t ω
  obtain ⟨hlo,hhi⟩ := classicalCandidate_bounds (q := q) (σ := σ) (S := S)
    hp brownian hK.le hr T (min t (θ.time ω)) ω
  simpa only [Real.norm_eq_abs,abs_of_nonneg hlo] using hhi

theorem brownian_price_identification_of_localMartingale {K r q σ S : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {T : ℝ≥0}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 < K) (hr : 0 ≤ r) (hS : 0 < S)
    (hsuper : Supermartingale (classicalCandidate brownian K r q σ S p T)
        brownianFiltration gaussianLimit)
    (hlocal : IsLocalMartingale (fun t ω => classicalCandidate brownian K r q σ S p T
      (min t ((brownianClassicalContactRule hp hK hS T).time ω)) ω) brownianAugFiltration
          gaussianLimit) :
    brownianAmericanPut K r q σ S T = K*p (Real.log (S/K)) (σ^2/2*(T : ℝ)) :=
  brownian_price_identification_of_martingales hp hK hr hS hsuper
    (brownian_stoppedCandidate_martingale_of_local hp hK hr _ hlocal)

theorem brownian_boundary_curvature_of_localMartingales {K r q σ : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 < K) (hr : 0 ≤ r) (hσ : 0 < σ)
    (hsuper : ∀ (T : ℝ≥0) (S : ℝ), 0 < S →
      Supermartingale (classicalCandidate brownian K r q σ S p T) brownianFiltration gaussianLimit)
    (hlocal : ∀ (T : ℝ≥0) (S : ℝ) (hS : 0 < S),
      IsLocalMartingale (fun t ω => classicalCandidate brownian K r q σ S p T
        (min t ((brownianClassicalContactRule hp hK hS T).time ω)) ω)
            brownianAugFiltration gaussianLimit)
    {τ : ℝ} (hτ : 0 < τ) :
    0 < deriv (deriv (fun s : ℝ => brownianExerciseBoundary K r q σ s.toNNReal)) τ :=
  brownian_boundary_curvature_of_martingales hp hK hr hσ hsuper
    (fun T S hS => brownian_stoppedCandidate_martingale_of_local hp hK hr _ (hlocal T S hS)) hτ

end MathFin.BlackScholes.AmericanPut.Stopping
