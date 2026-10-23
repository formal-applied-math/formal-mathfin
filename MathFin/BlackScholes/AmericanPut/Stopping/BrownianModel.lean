/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ExerciseRegion
public import BrownianMotion.Gaussian.BrownianMotion

/-!
# A constructed Brownian model for the American stopping value

The dependency constructs a continuous Brownian motion on its Gaussian
probability space. We use its natural filtration, prove the filtered Brownian
property, and instantiate the finite-horizon American value. No existence of
a PDE solution is assumed or proved here. Equality with a value defined using
the usual augmented filtration is a separate verification obligation.

## Result

Public entry points include `brownianFiltration`, `brownian_filtered`, `brownian_adapted`,
`brownianAmericanPut`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The natural filtration of the constructed Brownian motion on the path space `ℝ≥0 → ℝ`. -/
noncomputable def brownianFiltration : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)) :=
  Filtration.natural brownian (fun t => (measurable_brownian t).stronglyMeasurable)

theorem brownian_filtered : IsFilteredPreBrownian brownian brownianFiltration gaussianLimit :=
  isBrownianReal_brownian.toIsPreBrownianReal.isFilteredPreBrownian measurable_brownian

theorem brownian_adapted : Adapted brownianFiltration brownian :=
  (Filtration.stronglyAdapted_natural
    (fun t => (measurable_brownian t).stronglyMeasurable)).adapted

/-- The finite-horizon American put value of the constructed Brownian model, taken over the
rules of the raw natural filtration `brownianFiltration`. -/
noncomputable def brownianAmericanPut (K r q σ S : ℝ) (T : ℝ≥0) : ℝ :=
  americanPutValue gaussianLimit brownianFiltration brownian K r q σ S T

theorem brownianAmericanPut_bounds {K r q σ S : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S)
    (T : ℝ≥0) : max (K-S) 0 ≤ brownianAmericanPut K r q σ S T ∧
      brownianAmericanPut K r q σ S T ≤ K :=
  ⟨payoff_le_value measurable_brownian_uncurry
      isBrownianReal_brownian.eval_zero_ae_eq_zero hK hr hS,
    value_le_strike measurable_brownian_uncurry hK hr hS⟩

theorem brownianAmericanPut_at_expiry {K r q σ S : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) :
    brownianAmericanPut K r q σ S 0 = max (K-S) 0 :=
  value_at_expiry measurable_brownian_uncurry isBrownianReal_brownian.eval_zero_ae_eq_zero hK hr hS

theorem brownianAmericanPut_mono_horizon {K r q σ S : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S) :
    Monotone (brownianAmericanPut K r q σ S) :=
  fun _ _ hTU => value_mono_horizon measurable_brownian_uncurry hK hr hS hTU

theorem brownianAmericanPut_convexOn_spot {K r q σ : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (T : ℝ≥0) :
    ConvexOn ℝ (Set.Ici 0) (fun S => brownianAmericanPut K r q σ S T) :=
  value_convexOn_spot measurable_brownian_uncurry hK hr

theorem brownianAmericanPut_continuousOn_spot {K r q σ : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (T : ℝ≥0) :
    ContinuousOn (fun S => brownianAmericanPut K r q σ S T) (Set.Ici 0) :=
  value_continuousOn_spot measurable_brownian_uncurry
      isBrownianReal_brownian.eval_zero_ae_eq_zero hK hr

/-- The in-the-money contact threshold of the actual Brownian stopping value.
It is not assumed positive or smooth. Those facts are still to be proved. -/
noncomputable def brownianExerciseBoundary (K r q σ : ℝ) (T : ℝ≥0) : ℝ :=
  exerciseThreshold gaussianLimit brownianFiltration brownian K r q σ T

theorem brownianExerciseBoundary_bounds {K r q σ : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (T : ℝ≥0) :
    0 ≤ brownianExerciseBoundary K r q σ T ∧ brownianExerciseBoundary K r q σ T ≤ K :=
  threshold_bounds measurable_brownian_uncurry isBrownianReal_brownian.eval_zero_ae_eq_zero hK hr

theorem brownianExerciseBoundary_at_expiry {K r q σ : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) :
    brownianExerciseBoundary K r q σ 0 = K :=
  threshold_at_expiry measurable_brownian_uncurry isBrownianReal_brownian.eval_zero_ae_eq_zero hK hr

theorem brownianExerciseBoundary_antitone {K r q σ : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) :
    Antitone (brownianExerciseBoundary K r q σ) :=
  threshold_antitone_horizon measurable_brownian_uncurry
      isBrownianReal_brownian.eval_zero_ae_eq_zero hK hr

theorem brownianExerciseBoundary_contact_set {K r q σ : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (T : ℝ≥0) :
    {S | 0 ≤ S ∧ S ≤ K ∧ brownianAmericanPut K r q σ S T = K-S} =
      Set.Icc 0 (brownianExerciseBoundary K r q σ T) :=
  exerciseSet_eq_interval measurable_brownian_uncurry
      isBrownianReal_brownian.eval_zero_ae_eq_zero hK hr

end MathFin.BlackScholes.AmericanPut.Stopping
