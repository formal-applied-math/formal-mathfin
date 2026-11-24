/-
Copyright (c) 2026 Raphael Coelho, Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.ItoIntegralL2

/-!
# Brownian increments on a specified filtration

The old integral tower fixes the natural filtration of one scalar driver.  This
module starts the extension to a common filtration.  `BrownianOn` contains only
the Brownian law, adaptedness and independence of future increments from the
specified past.  It contains no integral, martingale, Itô or pricing conclusion.

The moment arguments below generalize the natural-filtration arguments in
MathFin/Foundations/ItoIsometryAdapted.lean (Raphael Coelho, Apache-2.0).

## Main definitions

* `BrownianOn`

## Main results

* `brownianOn_natural`
* `BrownianOn.integral_increment`
* `BrownianOn.integral_increment_sq`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto
namespace CommonNoise
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ}

/-- A scalar Brownian driver relative to the supplied filtration.  Independence
is tested against all real measurable functions of its past sigma-algebra. -/
structure BrownianOn (ℱ : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ)
    (μ : Measure Ω) : Prop where
  law : IsPreBrownianReal B μ
  adapted : StronglyAdapted ℱ B
  future_independent : ∀ (s : ℝ≥0), ∀ {f : Ω → ℝ}, Measurable[ℱ s] f →
    IndepFun f (fun ω u => B (s + u) ω - B s ω) μ

theorem BrownianOn.measurable (h : BrownianOn ℱ B μ) (t : ℝ≥0) :
    Measurable (B t) := (h.adapted t).measurable.mono (ℱ.le t) le_rfl

theorem BrownianOn.independent (h : BrownianOn ℱ B μ)
    {s t : ℝ≥0} (hst : s ≤ t) {f : Ω → ℝ} (hf : Measurable[ℱ s] f) :
    IndepFun f (fun ω => B t ω - B s ω) μ := by
  have hi := (h.future_independent s hf).comp measurable_id (measurable_pi_apply (t-s))
  simpa only [Function.comp_def, id_eq, add_tsub_cancel_of_le hst] using hi

/-- The joint-past independence hypothesis implies the library's filtered Brownian condition. -/
theorem BrownianOn.isFilteredPreBrownian (h : BrownianOn ℱ B μ) :
    IsFilteredPreBrownian B ℱ μ where
  toIsPreBrownianReal := h.law
  stronglyAdapted := h.adapted
  indep s t hst := by
    apply Indep.symm
    rw [Indep_iff]
    rintro A _ hA ⟨S, hS, rfl⟩
    have hA' : A = A.indicator (1 : Ω → ℝ) ⁻¹' ({1} : Set ℝ) := by
      ext ω
      by_cases hω : ω ∈ A <;> simp [Set.indicator, hω]
    have hi := h.independent hst (measurable_const.indicator hA :
      Measurable[ℱ s] (A.indicator (1 : Ω → ℝ)))
    rw [hA']
    exact hi.measure_inter_preimage_eq_mul ({1} : Set ℝ) S (by simp) hS


/-- The interface is inhabited by every existing natural-filtration driver. -/
theorem brownianOn_natural (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, Measurable (B t)) :
    BrownianOn (MathFin.ItoIntegralL2.natFiltration hBm) B μ := by
  refine ⟨hB, Filtration.stronglyAdapted_natural _, ?_⟩
  intro s f hf
  apply (IndepFun_iff_Indep _ _ _).2
  apply indep_of_indep_of_le_left _ hf.comap_le
  change Indep (Filtration.natural B _ s) _ μ
  rw [Filtration.natural_eq_comap]
  exact ((IndepFun_iff_Indep _ _ _).1 (hB.indepFun_shift s)).symm

theorem BrownianOn.integral_increment (h : BrownianOn ℱ B μ) (s t : ℝ≥0) :
    (∫ ω, (B t ω - B s ω) ∂μ) = 0 := by
  have hh := (h.law.hasLaw_sub t s).integral_eq
  rwa [integral_id_gaussianReal] at hh

theorem BrownianOn.integral_increment_sq (h : BrownianOn ℱ B μ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, (B t ω - B s ω) ^ 2 ∂μ) = (t : ℝ) - s :=
  MathFin.ItoIsometryAdapted.integral_increment_sq h.law hst

end CommonNoise
end MathFin.FilteredIto
