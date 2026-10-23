/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.SmoothLocalization
public import MathFin.Foundations.ItoFormulaUnrestrictedLocMart

/-!
# Ito's formula for globally C3 plane functions

This adapter derives all six partial derivatives required by MathFin's Ito
theorem from one joint C3 hypothesis. The resulting local martingale uses the
upstream null-augmented Brownian filtration, explicitly, not the raw filtration.

## Result

Public entry points include `planePartial`, `planeGenerator`, and `plane_ito_localMartingale`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The directional derivative `fderiv ℝ G z v` of a plane function `G` at `z` along `v`. -/
noncomputable def planePartial (G : ℝ × ℝ → ℝ) (v : ℝ × ℝ) (z : ℝ × ℝ) : ℝ :=
  fderiv ℝ G z v

/-- The second-order operator
`planePartial G (1,0) z + (1/2)*planePartial (planePartial G (0,1)) (0,1) z`, i.e. the time
derivative plus half the second space derivative. -/
noncomputable def planeGenerator (G : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  planePartial G (1,0) z + (1/2)*planePartial (planePartial G (0,1)) (0,1) z

theorem planePartial_contDiff {G : ℝ × ℝ → ℝ} {n : ℕ} (hG : ContDiff ℝ (n + 1) G)
    (v : ℝ × ℝ) : ContDiff ℝ n (planePartial G v) :=
  (hG.fderiv_right (m := n) (by norm_cast)).clm_apply contDiff_const

theorem planePartial_hasDeriv_time {G : ℝ × ℝ → ℝ} {t w : ℝ}
    (hG : DifferentiableAt ℝ G (t, w)) :
    HasDerivAt (fun s => G (s,w)) (planePartial G (1,0) (t,w)) t := by
  simpa only [Function.comp_def,id_eq,planePartial] using hG.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t w))

theorem planePartial_hasDeriv_space {G : ℝ × ℝ → ℝ} {t w : ℝ}
    (hG : DifferentiableAt ℝ G (t, w)) :
    HasDerivAt (fun y => G (t,y)) (planePartial G (0,1) (t,w)) w := by
  simpa only [Function.comp_def,id_eq,planePartial] using hG.hasFDerivAt.comp_hasDerivAt w
    ((hasDerivAt_const w t).prodMk (hasDerivAt_id w))

theorem planeGenerator_eq_partials {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 3 G) (t w : ℝ) :
    planeGenerator G (t,w) = deriv (fun s => G (s,w)) t +
      (1/2)*deriv (deriv (fun y => G (t,y))) w := by
  have hd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hx : ContDiff ℝ 2 (planePartial G (0,1)) := planePartial_contDiff hG _
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
    {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 3 G) :
    ∃ M : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous (fun t => M t ω)) ∧
      IsLocalMartingale M
          (MathFin.ItoIntegralProcessLocalMartingaleGeneral.augFiltration (μ := P) hmeas) P ∧
      ∀ t : ℝ≥0, (fun ω => G (t,W t ω)-G (0,W 0 ω)) =ᵐ[P]
        (fun ω => M t ω + ∫ s in Set.Ioc 0 t,
          planeGenerator G (s,W s ω) ∂MathFin.ItoIntegralL2.timeMeasure) := by
  have ht : ContDiff ℝ 2 (planePartial G (1,0)) := planePartial_contDiff hG _
  have hx : ContDiff ℝ 2 (planePartial G (0,1)) := planePartial_contDiff hG _
  have htt : ContDiff ℝ 1 (planePartial (planePartial G (1,0)) (1,0)) := planePartial_contDiff ht _
  have htx : ContDiff ℝ 1 (planePartial (planePartial G (1,0)) (0,1)) := planePartial_contDiff ht _
  have hxx : ContDiff ℝ 1 (planePartial (planePartial G (0,1)) (0,1)) := planePartial_contDiff hx _
  have hxxx : ContDiff ℝ 0 (planePartial (planePartial (planePartial G (0,1)) (0,1)) (0,1)) :=
    planePartial_contDiff hxx _
  exact MathFin.ito_formula_unrestricted hW hmeas hpaths
    (fun t w => planePartial_hasDeriv_time (hG.differentiable (by norm_num) (t,w)))
    (fun t w => planePartial_hasDeriv_time (ht.differentiable (by norm_num) (t,w)))
    (fun t w => planePartial_hasDeriv_space (ht.differentiable (by norm_num) (t,w)))
    (fun t w => planePartial_hasDeriv_space (hG.differentiable (by norm_num) (t,w)))
    (fun t w => planePartial_hasDeriv_space (hx.differentiable (by norm_num) (t,w)))
    (fun t w => planePartial_hasDeriv_space (hxx.differentiable (by norm_num) (t,w)))
    hG.continuous ht.continuous hx.continuous hxx.continuous htt.continuous htx.continuous
        hxxx.continuous

end MathFin.BlackScholes.AmericanPut.Stopping
