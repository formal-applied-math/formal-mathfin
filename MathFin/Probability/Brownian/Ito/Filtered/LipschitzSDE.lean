/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.DriftContinuous
public import MathFin.Probability.Brownian.SDE.SDEPathwise

/-!
# Lipschitz SDE

Continuous, adapted realization of the genuine Picard fixed point on a
contractive finite horizon. This is a Lipschitz SDE theorem; the square-root
CIR limit and arbitrary-horizon extension are separate proof obligations.

## Main results

* `lipComp_coeFn`
* `exists_continuous_lipschitz_sde_on_small_horizon`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open MathFin.SDEExistence MathFin.ItoIntegralL2 MathFin.ItoIntegralCLM
open MathFin.ItoIntegralProcess MathFin.ItoIntegralProcessGeneral
open MathFin.ItoIntegralProcessContinuousModification

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}

theorem lipComp_coeFn (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (Z : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ⇑(lipComp T hBmeas f L hf Z) =ᵐ[trimMeasure (μ := μ) T hBmeas]
      fun z => f (Z z) := by
  unfold lipComp
  filter_upwards [Lp.coeFn_add (Lp.const 2 (trimMeasure (μ := μ) T hBmeas) (f 0))
      ((lipschitz_sub_const hf).compLp (by simp) Z),
    Lp.coeFn_const (p := 2) (μ := trimMeasure (μ := μ) T hBmeas) (c := f 0),
    (lipschitz_sub_const hf).coeFn_compLp (by simp) Z] with z hsum hconst hcomp
  simp only [hsum, Pi.add_apply, hconst, hcomp, Function.const_apply, Function.comp_apply]
  ring

/-- The approximating solution is constructed, not supplied as an assumption.
The diffusion witness is identified with the coefficient of that same process
in the predictable L² space; the integral equation holds on one full-measure
set simultaneously for every time in the horizon. -/
theorem exists_continuous_lipschitz_sde_on_small_horizon
    (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
    {b σ : ℝ → ℝ} {Lb Lσ : ℝ≥0}
    (hb : LipschitzWith Lb b) (hσ : LipschitzWith Lσ σ) (x₀ : ℝ)
    (hc : (T : ℝ) * Lb + Real.sqrt (T : ℝ) * Lσ < 1) :
    ∃ (X : ℝ≥0 → Ω → ℝ) (H : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)),
      IsStronglyPredictable (natFiltration hBmeas) X ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) (Set.Icc 0 T)) ∧
      MemLp (Function.uncurry X) 2 (trimMeasure (μ := μ) T hBmeas) ∧
      (⇑H =ᵐ[trimMeasure (μ := μ) T hBmeas] fun z => σ (X z.1 z.2)) ∧
      (∀ᵐ ω ∂μ, ∀ t : ℝ≥0, t ≤ T →
        X t ω = x₀ + (∫ s in Set.Ioc 0 t, b (X s ω) ∂timeMeasure)
          + itoContinuousMod T hBmeas H t ω) := by
  let η := Lp.const 2 (trimMeasure (μ := μ) T hBmeas) x₀
  let Z := picardSolution hB T hBmeas hBcont hb hσ η hc
  let G := lipComp T hBmeas b Lb hb Z
  let H := lipComp T hBmeas σ Lσ hσ Z
  let X : ℝ≥0 → Ω → ℝ := fun t ω =>
    x₀ + driftContinuousMod T hBmeas G t ω + itoContinuousMod T hBmeas H t ω
  have hZ : ⇑Z =ᵐ[trimMeasure (μ := μ) T hBmeas] Function.uncurry X := by
    filter_upwards [sde_pathwise_decomposition hB T hBmeas hBcont hb hσ η hc,
      Lp.coeFn_const (p := 2) (μ := trimMeasure (μ := μ) T hBmeas) (c := x₀)]
      with z hz hη
    have hη' : η z = x₀ := hη
    change Z z = η z + driftContinuousMod T hBmeas G z.1 z.2
      + itoContinuousMod T hBmeas H z.1 z.2 at hz
    rw [hη'] at hz
    exact hz
  have hG : ⇑G =ᵐ[trimMeasure (μ := μ) T hBmeas] fun z => b (X z.1 z.2) := by
    filter_upwards [lipComp_coeFn T hBmeas hb Z, hZ] with z hg hz
    exact hg.trans (congrArg b hz)
  have hH : ⇑H =ᵐ[trimMeasure (μ := μ) T hBmeas] fun z => σ (X z.1 z.2) := by
    filter_upwards [lipComp_coeFn T hBmeas hσ Z, hZ] with z hh hz
    exact hh.trans (congrArg σ hz)
  refine ⟨X, H, ?_, ?_, (Lp.memLp Z).ae_eq hZ, hH, ?_⟩
  · exact (stronglyMeasurable_const.add (driftContinuousMod_isStronglyPredictable T hBmeas G)).add
      (itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont H)
  · filter_upwards [driftContinuousMod_continuousOn T hBmeas G,
      itoContinuousMod_continuousOn hB T hBmeas hBcont H] with ω hd hi
    exact (continuousOn_const.add hd).add hi
  · have hGprod : ⇑G =ᵐ[(timeMeasureHorizon T).prod μ] fun z => b (X z.1 z.2) :=
      ae_eq_of_ae_eq_trim hG
    have hGswap : ∀ᵐ z ∂μ.prod (timeMeasureHorizon T), G (z.2, z.1) = b (X z.2 z.1) :=
      (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hGprod)
    filter_upwards [Measure.ae_ae_of_ae_prod hGswap,
      driftContinuousMod_eq_setIntegral_all T hBmeas G] with ω hcoeff hdrift
    intro t ht
    have hi : (∫ s in Set.Ioc 0 t, G (s, ω) ∂timeMeasure) =
        ∫ s in Set.Ioc 0 t, b (X s ω) ∂timeMeasure := by
      apply integral_congr_ae
      exact hcoeff.filter_mono (ae_mono
        (Measure.restrict_mono (Set.Ioc_subset_Ioc_right ht) le_rfl))
    change x₀ + driftContinuousMod T hBmeas G t ω + itoContinuousMod T hBmeas H t ω = _
    rw [hdrift t ht, hi]

end MathFin.FilteredIto
