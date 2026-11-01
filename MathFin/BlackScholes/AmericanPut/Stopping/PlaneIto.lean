/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.SmoothLocalization
public import MathFin.Foundations.ItoFormulaUnrestrictedLocMart
public import MathFin.BlackScholes.AmericanPut.Stopping.PlanePartial

/-!
# Ito's formula for globally C2 plane functions

This adapter derives the three partial derivatives (`f_t`, `f_x`, `f_xx`) required by MathFin's Ito
theorem from one joint C2 hypothesis. The resulting local martingale uses the
upstream null-augmented Brownian filtration, explicitly, not the raw filtration.

## Result

Public entry points include `planeGenerator` and `plane_ito_localMartingale` (the partials
`planePartial` live in `PlanePartial`).
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The second-order operator
`planePartial G (1,0) z + (1/2)*planePartial (planePartial G (0,1)) (0,1) z`, i.e. the time
derivative plus half the second space derivative. -/
noncomputable def planeGenerator (G : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  planePartial G (1,0) z + (1/2)*planePartial (planePartial G (0,1)) (0,1) z

theorem planeGenerator_eq_partials {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 2 G) (t w : ℝ) :
    planeGenerator G (t,w) = deriv (fun s => G (s,w)) t +
      (1/2)*deriv (deriv (fun y => G (t,y))) w := by
  have hd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hx : ContDiff ℝ 1 (planePartial G (0,1)) := planePartial_contDiff hG _
  have he : (fun y => planePartial G (0,1) (t,y)) = deriv (fun y => G (t,y)) := by
    funext y
    exact (planePartial_hasDeriv_space (hd (t,y))).deriv.symm
  unfold planeGenerator
  rw [← (planePartial_hasDeriv_time (hd (t,w))).deriv,
    ← (planePartial_hasDeriv_space (hx.differentiable (by norm_num) (t,w))).deriv,he]

theorem plane_ito_localMartingale {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → ℝ}
    (hW : IsPreBrownianReal W P) (hmeas : ∀ t, Measurable (W t))
    (hpaths : ∀ ω, Continuous (fun t => W t ω))
    {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 2 G) :
    ∃ M : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous (fun t => M t ω)) ∧
      IsLocalMartingale M
          (MathFin.ItoIntegralProcessLocalMartingaleGeneral.augFiltration (μ := P) hmeas) P ∧
      ∀ t : ℝ≥0, (fun ω => G (t,W t ω)-G (0,W 0 ω)) =ᵐ[P]
        (fun ω => M t ω + ∫ s in Set.Ioc 0 t,
          planeGenerator G (s,W s ω) ∂MathFin.ItoIntegralL2.timeMeasure) := by
  have ht : ContDiff ℝ 1 (planePartial G (1,0)) := planePartial_contDiff hG _
  have hx : ContDiff ℝ 1 (planePartial G (0,1)) := planePartial_contDiff hG _
  have hxx : ContDiff ℝ 0 (planePartial (planePartial G (0,1)) (0,1)) :=
    planePartial_contDiff hx _
  exact MathFin.ito_formula_unrestricted hW hmeas hpaths
    (fun t w => planePartial_hasDeriv_time (hG.differentiable (by norm_num) (t,w)))
    (fun t w => planePartial_hasDeriv_space (hG.differentiable (by norm_num) (t,w)))
    (fun t w => planePartial_hasDeriv_space (hx.differentiable (by norm_num) (t,w)))
    hG.continuous ht.continuous hx.continuous hxx.continuous

end MathFin.BlackScholes.AmericanPut.Stopping
