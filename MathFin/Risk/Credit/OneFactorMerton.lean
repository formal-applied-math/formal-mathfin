/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Models.Credit.KMVMerton
public import MathFin.Probability.Analysis.IndepFreezing
public import MathFin.Risk.Credit.BernoulliMixture

/-!
# The one-factor credit portfolio is Merton's

Gordy's one-factor model (`Risk/Credit/BernoulliMixture.lean`) is Merton's firm-value model
(`Models/Credit/KMVMerton.lean`) with correlated drivers. Let the standardised log firm value of a
name be `√ρ M + √(1 − ρ) ε`, with the systematic factor `M` and the idiosyncratic shock `ε`
independent standard normals, and let the name default at `T` when the firm value
`bsTerminal V₀ r σ T (√ρ M + √(1 − ρ) ε)` is below the face value `F`. Unconditionally this
is Merton's default, of probability `kmvPD V₀ F r σ T = Φ(−d₂)`; given the factor `M` it is
the Bernoulli mixture of the one-factor model, with probability
`oneFactorPD (kmvPD V₀ F r σ T) ρ M`. The default event is `{√ρ M + √(1 − ρ) ε < −d₂}`
(`bsTerminal_lt_iff`), and `−d₂ = Φ⁻¹(kmvPD)`; freezing `M` and integrating out `ε`
(`condExp_comp_prodMk_of_indep`) gives the conditional probability.

## Main results

* `condDefault_eq_oneFactorPD`: the conditional expectation, given `M`, of the Merton default
  indicator is `oneFactorPD (kmvPD V₀ F r σ T) ρ M` almost surely.

## References

* [R. C. Merton, *On the pricing of corporate debt: the risk structure of interest
  rates*][Merton1974]
* [O. Vasicek, *Loan portfolio value*][Vasicek2002]

## Tags

Merton model, one-factor model, Gaussian copula, conditional default probability, KMV,
MSC 91G40, JEL G33, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

/-- **The conditional default probability of a Merton name is `oneFactorPD`.** If the standardised
log firm value is `√ρ M + √(1 − ρ) ε` with `M`, `ε` independent standard normals (`M` measurable),
then given `M` the name defaults at `T` (firm value below the face value `F`) with probability
`oneFactorPD (kmvPD V₀ F r σ T) ρ M`. -/
theorem condDefault_eq_oneFactorPD {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    [IsProbabilityMeasure Q] {M ε : Ω → ℝ} (hMm : Measurable M) (hM : HasLaw M (gaussianReal 0 1) Q)
    (hε : HasLaw ε (gaussianReal 0 1) Q) (hind : M ⟂ᵢ[Q] ε) {V₀ F r σ T ρ : ℝ} (hV₀ : 0 < V₀)
    (hF : 0 < F) (hσ : 0 < σ) (hT : 0 < T) (hρ1 : ρ < 1) :
    Q[{ω | bsTerminal V₀ r σ T (√ρ * M ω + √(1 - ρ) * ε ω) < F}.indicator
        (fun _ ↦ (1 : ℝ)) | MeasurableSpace.comap M inferInstance]
      =ᵐ[Q] fun ω ↦ oneFactorPD (kmvPD V₀ F r σ T) ρ (M ω) := by
  have hs : 0 < √(1 - ρ) := Real.sqrt_pos.2 (sub_pos.2 hρ1)
  have hc : PhiInv (kmvPD V₀ F r σ T) = -bsd2 V₀ F r σ T := by
    rw [kmvPD, kmvDistanceToDefault_eq_bsd2 _ _ _ _ _ hV₀ hF, PhiInv_Phi]
  set S : Set (ℝ × ℝ) := {p | √ρ * p.1 + √(1 - ρ) * p.2 < -bsd2 V₀ F r σ T} with hS
  have hSm : MeasurableSet S := measurableSet_lt (by fun_prop) measurable_const
  have hev : {ω | bsTerminal V₀ r σ T (√ρ * M ω + √(1 - ρ) * ε ω) < F} =
      (fun ω ↦ (M ω, ε ω)) ⁻¹' S :=
    Set.ext fun ω ↦ bsTerminal_lt_iff hV₀ hF hσ hT _
  have hg : StronglyMeasurable (S.indicator fun _ : ℝ × ℝ ↦ (1 : ℝ)) :=
    (measurable_const.indicator hSm).stronglyMeasurable
  have hgi : Integrable (fun ω ↦ S.indicator (fun _ : ℝ × ℝ ↦ (1 : ℝ)) (M ω, ε ω)) Q :=
    Integrable.of_bound (hg.aestronglyMeasurable.comp_aemeasurable
      (hMm.aemeasurable.prodMk hε.aemeasurable)) 1
      (ae_of_all _ fun ω ↦ by by_cases h : (M ω, ε ω) ∈ S <;> simp [h])
  have key := condExp_comp_prodMk_of_indep (m := MeasurableSpace.comap M inferInstance)
    hMm.comap_le (comap_measurable M) hε.aemeasurable hind.symm hg hgi
  rw [hev, ← Set.indicator_comp_right (fun ω ↦ (M ω, ε ω)) (f := fun _ ↦ (1 : ℝ))]
  refine key.trans (Filter.Eventually.of_forall fun ω ↦ ?_)
  have : NullSingletonClass (gaussianReal (0 : ℝ) 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hset : {y | (M ω, y) ∈ S} = Set.Iio ((PhiInv (kmvPD V₀ F r σ T) - √ρ * M ω) / √(1 - ρ)) := by
    ext y
    simp only [hS, Set.mem_setOf_eq, Set.mem_Iio, hc, lt_div_iff₀ hs]
    constructor <;> intro h <;> linarith
  have h1 : ∫ y, S.indicator (fun _ : ℝ × ℝ ↦ (1 : ℝ)) (M ω, y) ∂(Q.map ε) =
      ∫ y, {y | (M ω, y) ∈ S}.indicator (fun _ ↦ (1 : ℝ)) y ∂(Q.map ε) := rfl
  rw [Function.comp_apply, Function.comp_def] at *
  simp only [Function.comp_def]
  rw [h1, integral_indicator_one (by exact measurable_prodMk_left hSm), hε.map_eq, hset,
    Measure.real, measure_congr Iio_ae_eq_Iic, ← Phi_def]
  rfl

end MathFin
