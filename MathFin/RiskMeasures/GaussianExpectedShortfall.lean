/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.RiskMeasures.ExpectedShortfall
public import MathFin.RiskMeasures.GaussianValueAtRisk
public import MathFin.RiskMeasures.RockafellarUryasev

/-!
# Expected shortfall of a Gaussian loss

`RiskMeasures/RockafellarUryasev.lean` minimizes the Rockafellar–Uryasev objective of the Gaussian
loss `L = m + σ Z`, written against the standard normal density. It finds the closed form
`gaussianCVaR m σ z α = m + σ ϕ(z)/(1 − α)` at `Φ(z) = α`. The general Rockafellar–Uryasev theorem
(`RiskMeasures/ExpectedShortfall.lean`) shows that the minimum of the same objective, written
against the law, is the expected shortfall.

The two objectives are the same function of the threshold
(`rockafellarUryasev_of_hasLaw_gaussianReal`), so the two minima agree. The Gaussian closed form is
therefore the expected shortfall of the normal law (`expectedShortfall_of_hasLaw_gaussianReal`). No
new integral is computed here. The Gaussian file supplies the value and the general theorem
supplies its meaning.

## Main results

* `integrable_of_hasLaw_gaussianReal`: a Gaussian loss is integrable.
* `rockafellarUryasev_of_hasLaw_gaussianReal`: the law-side objective equals `ruObjective`.
* `expectedShortfall_of_hasLaw_gaussianReal`: `ES_α(X) = m + σ ϕ(Φ⁻¹(α))/(1 − α)` for
  `X ~ N(m, σ²)` with `σ > 0`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ} {α : ℝ}

omit [IsProbabilityMeasure P] in
/-- A Gaussian loss is integrable. -/
lemma integrable_of_hasLaw_gaussianReal {m : ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal m v) P) :
    Integrable X P := by
  have h : Integrable id (gaussianReal m v) := (memLp_id_gaussianReal 1).integrable (by simp)
  rw [← hX.map_eq] at h
  exact (integrable_map_measure aestronglyMeasurable_id hX.aemeasurable).1 h

omit [IsProbabilityMeasure P] in
/-- The Rockafellar–Uryasev objective of a Gaussian loss, written against its law, is the objective
`ruObjective` of `RiskMeasures/RockafellarUryasev.lean`, written against the standard normal
density. -/
theorem rockafellarUryasev_of_hasLaw_gaussianReal {m : ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal m v) P) (c : ℝ) :
    rockafellarUryasev X P α c = ruObjective m √(v : ℝ) α c := by
  have hlaw : ∫ ω, max (X ω - c) 0 ∂P =
      ∫ x, max (m + √(v : ℝ) * x - c) 0 * gaussianPDFReal 0 1 x := by
    calc ∫ ω, max (X ω - c) 0 ∂P = ∫ y, max (y - c) 0 ∂gaussianReal m v :=
          hX.integral_comp (f := fun y ↦ max (y - c) 0) (by fun_prop)
      _ = ∫ x, max (√(v : ℝ) * x + m - c) 0 ∂gaussianReal 0 1 := by
          rw [gaussianReal_eq_map_standard, integral_map (by fun_prop) (by fun_prop)]
      _ = ∫ x, max (m + √(v : ℝ) * x - c) 0 * gaussianPDFReal 0 1 x := by
          rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
          congr with x
          rw [smul_eq_mul, mul_comm, add_comm (√(v : ℝ) * x)]
  rw [rockafellarUryasev, ruObjective, hlaw, div_eq_inv_mul]

/-- **The expected shortfall of a Gaussian loss**: for `X ~ N(m, σ²)` with `σ > 0`,
`ES_α(X) = m + σ ϕ(Φ⁻¹(α))/(1 − α)`, the closed form `gaussianCVaR` of
`RiskMeasures/Gaussian.lean` at the normal quantile. -/
theorem expectedShortfall_of_hasLaw_gaussianReal {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX : HasLaw X (gaussianReal m v) P) (hα : α ∈ Ioo 0 1) :
    expectedShortfall X P α = gaussianCVaR m √(v : ℝ) (PhiInv α) α := by
  have hσ : 0 < √(v : ℝ) := Real.sqrt_pos.2 (by positivity)
  have h := isLeast_rockafellarUryasev (integrable_of_hasLaw_gaussianReal hX) hα
  rw [show rockafellarUryasev X P α = ruObjective m √(v : ℝ) α from
    funext (rockafellarUryasev_of_hasLaw_gaussianReal hX)] at h
  exact h.unique (gaussianCVaR_isLeast_ruObjective m _ _ α hσ (Phi_PhiInv hα) hα.2)

end MathFin
