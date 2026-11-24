/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.StochasticIntegralCharacterisation
public import MathFin.Probability.Brownian.Ito.ItoIntegralProcessContinuousModification

/-!
# Predictable versions of stochastic integrals

A terminal L² operator can be evaluated on a process via a predictable version. Replacing
the integrator by a fixed-time modification preserves all elementary increments.

## Main definitions

* `PredictableL2Version`, `predictableL2Domain` and `predictableL2Class` give the
  process-domain interface for a measure on the predictable sigma algebra.

## Main results

* `predictableL2Class_bracket` identifies the class used by the native bracket integral.
* `isStochasticIntegral_itoContinuousMod` applies BrownianMotion's characterization
  to the stopped continuous version.

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

stochastic integration, predictable processes, MSC 60H05
-/

@[expose] public section

namespace MathFin.StochasticIntegralCharacterisation
open MeasureTheory ProbabilityTheory Filter Topology
open MathFin.ItoIntegralL2 MathFin.ItoIntegralCLM MathFin.ItoIntegralAgainstMartingale
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- A process which agrees indistinguishably with a predictable representative in L²
for the specified measure on the predictable σ-algebra. -/
def PredictableL2Version (μ : Measure Ω) (ℱ : Filtration ℝ≥0 mΩ)
    (ν : @Measure (ℝ≥0 × Ω) ℱ.predictable) (X V : ℝ≥0 → Ω → ℝ) : Prop :=
  Measurable[ℱ.predictable] (Function.uncurry V) ∧
    MemLp (Function.uncurry V) 2 ν ∧ X ≡ᵐ[μ] V

/-- Process domain of a continuous L² stochastic integral. -/
def predictableL2Domain (μ : Measure Ω) (ℱ : Filtration ℝ≥0 mΩ)
    (ν : @Measure (ℝ≥0 × Ω) ℱ.predictable) : Set (ℝ≥0 → Ω → ℝ) :=
  {X | ∃ V, PredictableL2Version μ ℱ ν X V}

open scoped Classical in
/-- Select a representative for applying a continuous linear integral on predictable L². -/
noncomputable def predictableL2Class (μ : Measure Ω) (ℱ : Filtration ℝ≥0 mΩ)
    (ν : @Measure (ℝ≥0 × Ω) ℱ.predictable) (X : ℝ≥0 → Ω → ℝ) : Lp ℝ 2 ν :=
  if h : X ∈ predictableL2Domain μ ℱ ν then h.choose_spec.2.1.toLp _ else 0

variable {T : ℝ≥0} {hBmeas : ∀ t, Measurable (B t)}
  {φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)}

omit [IsProbabilityMeasure μ] in
/-- On the natural filtration with the bracket measure the process domain is the library's
canonical one. -/
theorem predictableL2Domain_bracket :
    predictableL2Domain μ (natFiltration hBmeas) (bracketMeasure T hBmeas φ) =
      domain T hBmeas φ := rfl

omit [IsProbabilityMeasure μ] in
/-- Applying the generic class selector on the bracket measure returns the original L² class. -/
theorem predictableL2Class_bracket (X : ℝ≥0 → Ω → ℝ) :
    predictableL2Class μ (natFiltration hBmeas) (bracketMeasure T hBmeas φ) X =
      integrandLp T hBmeas φ X := rfl

omit [IsProbabilityMeasure μ] in
private theorem extension_congr_integrator {ι : Type*} [LinearOrder ι] [OrderBot ι]
    {Y Z : ι → Ω → ℝ} {ℱ : Filtration ι mΩ} {I : SIntegral} {S : Domain}
    (h : IsRiemannStieltjesExtension μ Y ℱ I S) (hYZ : ∀ t, Y t =ᵐ[μ] Z t) :
    IsRiemannStieltjesExtension μ Z ℱ I S where
  measurable := h.measurable
  elementary_ioc i j hij X := by
    obtain ⟨hm, he⟩ := h.elementary_ioc i j hij X
    refine ⟨hm, he.trans ?_⟩
    filter_upwards [hYZ i, hYZ j] with ω hi hj
    change X ω * (Y j ω - Y i ω) = X ω * (Z j ω - Z i ω)
    rw [hi, hj]
  elementary_iic i X := by
    obtain ⟨hm, he⟩ := h.elementary_iic i X
    refine ⟨hm, he.trans ?_⟩
    filter_upwards [hYZ i, hYZ ⊥] with ω hi hb
    change X ω * (Y i ω - Y ⊥ ω) = X ω * (Z i ω - Z ⊥ ω)
    rw [hi, hb]
  integral_add := h.integral_add
  integral_smul := h.integral_smul
  integral_indistinguishable := h.integral_indistinguishable
  integral_dct := h.integral_dct

/-- Any fixed-time modification of the stopped integrator has the same stochastic
integral on the same domain. Elementary integrals only depend on a pair of endpoints. -/
theorem isStochasticIntegral_of_modification (hB : IsPreBrownianReal B μ)
    {Y : ℝ≥0 → Ω → ℝ} (hY : ∀ t, Y t =ᵐ[μ] integrator T hBmeas φ hB t) :
    IsStochasticIntegral μ Y (natFiltration hBmeas)
      (sIntegral T hBmeas φ hB) (domain T hBmeas φ) where
  toIsRiemannStieltjesExtension :=
    extension_congr_integrator (isRiemannStieltjesExtension (T := T) (hBmeas := hBmeas) (φ := φ) hB)
      (fun t ↦ (hY t).symm)
  consistent I' S' h X hX :=
    (isStochasticIntegral (T := T) (hBmeas := hBmeas) (φ := φ) hB).consistent I' S'
      (extension_congr_integrator h hY) X hX

/-- The stopped continuous modification of the Itô process represents the same
integrator in BrownianMotion's characterization. -/
theorem isStochasticIntegral_itoContinuousMod (hB : IsPreBrownianReal B μ)
    (hcont : ∀ ω, Continuous (fun t ↦ B t ω)) :
    IsStochasticIntegral μ
      (fun t ↦ ItoIntegralProcessContinuousModification.itoContinuousMod T hBmeas φ (min t T))
      (natFiltration hBmeas) (sIntegral T hBmeas φ hB) (domain T hBmeas φ) :=
  isStochasticIntegral_of_modification hB fun t ↦
    ItoIntegralProcessContinuousModification.itoContinuousMod_modification hB T hBmeas
      hcont φ (min_le_right t T)

end MathFin.StochasticIntegralCharacterisation
