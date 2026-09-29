/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfredo Garcia
-/
module

public import MathFin.Foundations.MarketCompletenessInPrice
public import MathFin.Foundations.DriftProcessModification

/-! # A price with a drift: `S = S₀ + ∫b ds + (σ●B)`

The price `S_t = S₀ + ∫₀ᵗ b ds + (σ●B)_t` with drift `b` and volatility `σ`, and the integral
`∫ψ dS := ∫ψb ds + ∫ψ dM` against it, where `M = σ●B`.

The drift term is `ItoIntegralProcessContinuousModification.driftContinuousMod`, which
`driftContinuousMod_eq_setIntegral` identifies with the Lebesgue integral `∫₀ᵗ b(s,ω) ds`. The
rest of the price is `MarketCompletenessInPrice.pricePath`, and `∫ψ dM` is
`ItoIntegralAgainstMartingale.itoIntegralAgainstCLM`.

## Scope

`∫ψ dM` needs `ψ` square-integrable against the bracket `σ²·trim`; the drift term needs `ψb`
square-integrable against `trim`, which that does not imply, so it is the hypothesis `hψb` of
`gainsDrift`. On `{σ = 0, b ≠ 0}` the gains depend on the representative `⇑ψ`, since the bracket
determines `ψ` only where `σ ≠ 0`; for a discounted price no arbitrage forces `b = σλ` and that
set is null. With `b ≠ 0`, `S` is not a martingale under `μ`.

## Result

* `pricePathDrift` — `S_t = S₀ + D_t + (σ●B)_t`, with `D = driftContinuousMod b`.
* `pricePathDrift_eq_setIntegral` — for each `t ≤ T`, a.e., `S_t = S₀ + ∫₀ᵗ b ds + (σ●B)_t`.
* `pricePathDrift_zero_drift` — at `b = 0`, `pricePath`, a.e. for each `t ≤ T`.
* `gainsDrift` — `∫₀ᵀ ψ dS`, under the side condition `hψb`.
* `gainsDrift_eq_setIntegral` — a.e., `∫₀ᵀ ψb ds + ∫ψ dM`.
* `gainsDrift_zero_drift` — at `b = 0`, `itoIntegralAgainstCLM`, a.e.
* `memLp_mul_zero_drift` — at `b = 0`, `hψb` holds for every holding.
-/

@[expose] public section

namespace MathFin
namespace PricePathDrift

open MeasureTheory ProbabilityTheory Filter ItoIntegralCLM ItoIntegralAgainstMartingale
  ItoIntegralProcessGeneral ItoIntegralProcessContinuousModification MarketCompletenessInPrice
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {hB : IsPreBrownianReal B μ}

/-- The price driven by `B` with drift `b` and volatility `σ`: `S_t = S₀ + ∫₀ᵗ b ds + (σ●B)_t`,
the drift taken as the pathwise object `driftContinuousMod`. -/
noncomputable def pricePathDrift (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (S₀ : ℝ)
    (b σ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ pricePath hB T hBmeas S₀ σ t ω + driftContinuousMod T hBmeas b t ω

/-- A `trim`-a.e. identity between two predictable functions holds on a.e. `ω`-slice, for a.e.
time. The trim transfers it to the product, and predictability makes the set measurable, which
is what lets the two a.e. quantifiers be swapped. -/
private theorem ae_slice_of_ae_trim (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) {f g : ℝ≥0 × Ω → ℝ}
    (hf : StronglyMeasurable[(ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable] f)
    (hg : StronglyMeasurable[(ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable] g)
    (hfg : f =ᵐ[trimMeasure_T (μ := μ) T hBmeas] g) :
    ∀ᵐ ω ∂μ, ∀ᵐ s ∂timeMeasure_T T, f (s, ω) = g (s, ω) := by
  have hle := (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod
  have hprod : ∀ᵐ z ∂(timeMeasure_T T).prod μ, f z = g z := ae_eq_of_ae_eq_trim hfg
  have hms : MeasurableSet {z : ℝ≥0 × Ω | f (z.1, z.2) = g (z.1, z.2)} :=
    (hf.mono hle).measurableSet_eq_fun (hg.mono hle)
  exact (Measure.ae_ae_comm hms).mp (Measure.ae_ae_of_ae_prod hprod)

/-- The time integral of a slice vanishes when the slice vanishes a.e. on `(0, T]`. -/
private theorem setIntegral_slice_eq_zero {T t : ℝ≥0} (ht : t ≤ T) {f : ℝ≥0 → ℝ}
    (hf : ∀ᵐ s ∂timeMeasure_T T, f s = 0) :
    ∫ s in Set.Ioc (0 : ℝ≥0) t, f s ∂ItoIntegralL2.timeMeasure = 0 := by
  refine integral_eq_zero_of_ae ?_
  exact ae_restrict_of_ae_restrict_of_subset (Set.Ioc_subset_Ioc_right ht) hf

/-- **The drift, identified.** For each `t ≤ T`, a.e., the price is `S₀ + ∫₀ᵗ b ds + (σ●B)_t`
with the time integral the genuine Lebesgue integral of `b`'s slice. -/
theorem pricePathDrift_eq_setIntegral (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) (S₀ : ℝ)
    (b σ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {t : ℝ≥0} (ht : t ≤ T) :
    ∀ᵐ ω ∂μ, pricePathDrift hB T hBmeas S₀ b σ t ω
      = S₀ + (∫ s in Set.Ioc (0 : ℝ≥0) t, ⇑b (s, ω) ∂ItoIntegralL2.timeMeasure)
        + (itoProcessCLM hB T t hBmeas σ : Ω → ℝ) ω := by
  filter_upwards [driftContinuousMod_eq_setIntegral T hBmeas b ht] with ω hω
  simp only [pricePathDrift, pricePath, hω]
  ring

/-- **The driftless case is `b = 0`.** For each `t ≤ T`, a.e., `pricePathDrift` with zero drift
is `pricePath`. -/
theorem pricePathDrift_zero_drift (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) (S₀ : ℝ)
    (σ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {t : ℝ≥0} (ht : t ≤ T) :
    pricePathDrift hB T hBmeas S₀ 0 σ t =ᵐ[μ] pricePath hB T hBmeas S₀ σ t := by
  have h0 := ae_slice_of_ae_trim (μ := μ) T hBmeas (Lp.stronglyMeasurable _)
    stronglyMeasurable_const (Lp.coeFn_zero ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
  filter_upwards [pricePathDrift_eq_setIntegral (hB := hB) T hBmeas S₀ 0 σ ht, h0]
    with ω hω h0ω
  rw [hω, setIntegral_slice_eq_zero ht h0ω]
  simp [pricePath]

/-- **The integral against the price**, `∫₀ᵀ ψ dS := ∫₀ᵀ ψb ds + ∫ψ dM`. The holding `ψ` is
square-integrable against the bracket, as for `M` alone; `hψb` is the extra side condition the
drift term needs, and it is not implied by the first. See the module docstring for why the
drift term reads `⇑ψ` off the bracket's support. -/
noncomputable def gainsDrift (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (b σ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (ψ : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas σ))
    (hψb : MemLp (fun z ↦ ψ z * b z) 2 (trimMeasure_T (μ := μ) T hBmeas)) : Ω → ℝ :=
  fun ω ↦ driftContinuousMod T hBmeas (hψb.toLp _) T ω
    + (itoIntegralAgainstCLM hB T hBmeas σ ψ : Ω → ℝ) ω

/-- **The gains, identified.** A.e., `∫₀ᵀ ψ dS` is the Lebesgue integral of `ψb` along the path
plus the Itô integral of `ψ` against `M`. -/
theorem gainsDrift_eq_setIntegral (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (b σ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (ψ : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas σ))
    (hψb : MemLp (fun z ↦ ψ z * b z) 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ∀ᵐ ω ∂μ, gainsDrift hB T hBmeas b σ ψ hψb ω
      = (∫ s in Set.Ioc (0 : ℝ≥0) T, ψ (s, ω) * b (s, ω) ∂ItoIntegralL2.timeMeasure)
        + (itoIntegralAgainstCLM hB T hBmeas σ ψ : Ω → ℝ) ω := by
  have hslice := ae_slice_of_ae_trim (μ := μ) T hBmeas (g := fun z ↦ ψ z * b z)
    (Lp.stronglyMeasurable _) ((Lp.stronglyMeasurable ψ).mul (Lp.stronglyMeasurable b))
    hψb.coeFn_toLp
  filter_upwards [driftContinuousMod_eq_setIntegral T hBmeas (hψb.toLp _) le_rfl, hslice]
    with ω hω hsω
  simp only [gainsDrift, hω]
  congr 1
  exact integral_congr_ae hsω

omit [IsProbabilityMeasure μ] in
/-- At zero drift the side condition holds for every holding: `ψ·0` is `0` a.e. -/
theorem memLp_mul_zero_drift (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (σ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (ψ : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas σ)) :
    MemLp (fun z ↦ ψ z * (0 : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) z) 2
      (trimMeasure_T (μ := μ) T hBmeas) := by
  refine (MemLp.zero' : MemLp (fun _ : ℝ≥0 × Ω ↦ (0 : ℝ)) 2 _).ae_eq ?_
  filter_upwards [Lp.coeFn_zero ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)] with z hz
  rw [hz, Pi.zero_apply, mul_zero]

/-- **The driftless integral is `b = 0`.** A.e., the gains against a zero-drift price are
`∫ψ dM`, which is `itoIntegralAgainstCLM` — the integral `MarketCompletenessInPrice` hedges
with. -/
theorem gainsDrift_zero_drift (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (σ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (ψ : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas σ)) :
    gainsDrift hB T hBmeas 0 σ ψ (memLp_mul_zero_drift T hBmeas σ ψ)
      =ᵐ[μ] ⇑(itoIntegralAgainstCLM hB T hBmeas σ ψ) := by
  have h0 := ae_slice_of_ae_trim (μ := μ) T hBmeas
    (f := fun z ↦ ψ z * (0 : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) z)
    ((Lp.stronglyMeasurable ψ).mul (Lp.stronglyMeasurable _)) stronglyMeasurable_const
    (by
      filter_upwards [Lp.coeFn_zero ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)] with z hz
      rw [hz, Pi.zero_apply, mul_zero])
  filter_upwards [gainsDrift_eq_setIntegral (hB := hB) T hBmeas 0 σ ψ
    (memLp_mul_zero_drift T hBmeas σ ψ), h0] with ω hω h0ω
  rw [hω, setIntegral_slice_eq_zero le_rfl h0ω, zero_add]

end PricePathDrift
end MathFin
