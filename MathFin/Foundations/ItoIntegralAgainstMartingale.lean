/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralLocality
public import MathFin.Foundations.PredictableDensityGeneral

/-! # The Itô integral against an Itô integral, and the chain rule

For a fixed predictable `φ ∈ L²(trim_T)` write `M := φ●B` for the Itô integral process
`M_t = (φ●B)_t`. This file integrates *against* `M`.

`M` is a continuous `L²` martingale whose bracket is `d⟨M⟩ = φ² ds ⊗ dμ`, so the integrands
square-integrable against it are `L²(⟨M⟩) = L²(φ²·trim_T)` — the `bracketMeasure` below. The
integral is then

  `∫ψ dM := ∫ ψφ dB`,

obtained by composing the multiplication isometry `ψ ↦ ψφ` of `LpMulIsometry` with
`itoIntegralCLM_T`. Because both factors are isometries, so is the composite:

  `‖∫ψ dM‖_{L²(μ)} = ‖ψ‖_{L²(⟨M⟩)}`,

which is the Itô isometry against `M`. That identity is the reason the weighted space is the
right domain, and it is what would come out wrong if the integral were defined on the flat
`L²(trim_T)` instead.

## Why this is the stochastic integral and not a notation

Defining `∫ψ dM` by a formula proves nothing on its own. What earns the name is
`itoIntegralAgainst_elementary`: on an elementary integrand `Z·1_{(a,b]}` with `Z` bounded and
`𝓕_a`-measurable, the definition returns

  `Z·(M_b − M_a)`,

the Riemann–Stieltjes sum one would have written down by hand. So the formula is a
construction, and the elementary identity is what identifies it.

**Exactly what uniqueness says here.** `itoIntegralAgainst_unique` takes agreement with
`itoIntegralAgainstCLM` on the simple processes — the dense family of
`PredictableDensityGeneral` — and concludes equality. It does *not* take agreement with
explicitly written Riemann–Stieltjes sums as its hypothesis, because the identity above is
proved for a single band `Z·1_{(a,b]}` and the extension to a general simple process, whose
integral is the sum of its band increments, is not proved in this file. Stating uniqueness
against the sums would need that extension first; it is a routine but real piece of work and
is left as a follow-up.

The proof of the elementary identity is short because the locality machinery already exists:
`1_{(a,b]}·φ` is `restrictAfterCLM a φ − restrictAfterCLM b φ`, whose integral is
`M_b − M_a` by `itoIntegralCLM_T_restrictAfterCLM` applied twice, and the `𝓕_a`-measurable
factor `Z` passes through by `itoIntegralCLM_T_smulAdapted`.

## Upstream

Degenne's package carries an axiomatic characterisation of the stochastic integral
(`IsRiemannStieltjesExtension`, `IsStochasticIntegral`), whose uniqueness clause is the same
idea in a wider frame (dominated convergence rather than `L²` density). It exists only on
`v4.33.0-rc1`, so `itoIntegralAgainst_unique` is proved here in the `L²` frame; instantiating
the upstream predicate is a follow-up for the next stable pin bump.

## Result

* `bracketMeasure` — `d⟨M⟩ = φ²·trim_T`, and its finiteness.
* `itoIntegralAgainstCLM` — `∫· dM`, as a CLM on `L²(⟨M⟩)`.
* `itoIntegralAgainst_eq_itoIntegral` — **the chain rule**: `∫ψ dM = ∫ ψφ dB`.
* `norm_itoIntegralAgainstCLM` — the Itô isometry against `M`.
* `itoIntegralAgainst_elementary` — **the identification**, on a single band:
  `∫ Z·1_{(a,b]} dM = Z·(M_b − M_a)`.
* `itoIntegralAgainst_unique` — a continuous linear map agreeing with `itoIntegralAgainstCLM`
  on the simple processes is it.
-/

@[expose] public section

namespace MathFin
namespace ItoIntegralAgainstMartingale

open MeasureTheory ProbabilityTheory Filter ItoIntegralCLM LpMulIsometry
  PredictableDensityGeneral ItoIntegralProcessGeneral ItoIntegralProcessGeneral
open scoped NNReal ENNReal InnerProductSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {hB : IsPreBrownianReal B μ}

/-! ### The bracket measure -/

/-- The bracket measure `d⟨M⟩ = φ² ds ⊗ dμ` of `M = φ●B`, as a measure on the predictable
σ-algebra. This is the domain of integration against `M`. -/
noncomputable def bracketMeasure (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    @Measure (ℝ≥0 × Ω)
      (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable :=
  sqWeight (trimMeasure_T (μ := μ) T hBmeas) (⇑φ)

omit [IsProbabilityMeasure μ] in
/-- `bracketMeasure` unfolded — the bridge to `LpMulIsometry`'s generic API. -/
theorem bracketMeasure_eq (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    bracketMeasure (μ := μ) T hBmeas φ
      = sqWeight (trimMeasure_T (μ := μ) T hBmeas) (⇑φ) := rfl

omit [IsProbabilityMeasure μ] in
/-- The bracket measure is finite, with total mass `‖φ‖²` — the energy of the driver. -/
instance instIsFiniteMeasureBracketMeasure (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    IsFiniteMeasure (bracketMeasure (μ := μ) T hBmeas φ) :=
  isFiniteMeasure_sqWeight T hBmeas (Lp.memLp φ)

/-! ### The integral against `M` -/

/-- **The Itô integral against `M = φ●B`**, as a continuous linear map from the integrands
square-integrable against the bracket. It is `itoIntegralCLM_T` precomposed with
multiplication by the driver, so the chain rule holds by construction and the isometry is
inherited from the two factors. -/
noncomputable def itoIntegralAgainstCLM (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas φ) →L[ℝ] Lp ℝ 2 μ :=
  (itoIntegralCLM_T hB T hBmeas).comp
    (mulLI (trimMeasure_T (μ := μ) T hBmeas)
      (Lp.stronglyMeasurable φ).measurable).toContinuousLinearMap

/-- **The chain rule, in bundled form**: integrating `ψ` against `M` is integrating `ψφ`
against `B`. -/
theorem itoIntegralAgainstCLM_apply (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (ψ : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas φ)) :
    itoIntegralAgainstCLM hB T hBmeas φ ψ
      = itoIntegralCLM_T hB T hBmeas
          (mulLI (trimMeasure_T (μ := μ) T hBmeas)
            (Lp.stronglyMeasurable φ).measurable ψ) := rfl

/-- **The chain rule** in the form a caller uses it: if `χ` is any predictable `L²` integrand
a.e. equal to `φ·ψ`, then `∫ψ dM = ∫χ dB`. -/
theorem itoIntegralAgainst_eq_itoIntegral (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (ψ : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas φ))
    (χ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (hχ : ⇑χ =ᵐ[trimMeasure_T (μ := μ) T hBmeas]
      fun z ↦ (φ : ℝ≥0 × Ω → ℝ) z * (ψ : ℝ≥0 × Ω → ℝ) z) :
    itoIntegralAgainstCLM hB T hBmeas φ ψ = itoIntegralCLM_T hB T hBmeas χ := by
  rw [itoIntegralAgainstCLM_apply]
  congr 1
  refine Lp.ext ?_
  exact (coeFn_mulLI _ (Lp.stronglyMeasurable φ).measurable ψ).trans hχ.symm

/-- **The Itô isometry against `M`**: `‖∫ψ dM‖_{L²(μ)} = ‖ψ‖_{L²(⟨M⟩)}`. Both factors of the
composite are isometries. -/
theorem norm_itoIntegralAgainstCLM (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (ψ : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas φ)) :
    ‖itoIntegralAgainstCLM hB T hBmeas φ ψ‖ = ‖ψ‖ := by
  rw [itoIntegralAgainstCLM_apply, itoIntegralCLM_T_norm, LinearIsometry.norm_map]
  rfl

/-! ### The elementary identity that earns the name -/

/-- The elementary integrand `Z·1_{(a,b]}`, as a function on `ℝ≥0 × Ω`. -/
noncomputable def elemIntegrand (a b : ℝ≥0) (Z : Ω → ℝ) : ℝ≥0 × Ω → ℝ :=
  fun z ↦ (Set.Ioc a b).indicator (fun _ ↦ (1 : ℝ)) z.1 * Z z.2

/-- `1_{(a,b]}·φ`, as an element of the flat predictable `L²`: the difference of the two
restrictions the locality file already provides. -/
noncomputable def bandRestrict (T a b : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) :=
  restrictAfterCLM T a hBmeas φ - restrictAfterCLM T b hBmeas φ

omit [IsProbabilityMeasure μ] in
/-- `bandRestrict` is what its name says: `φ` cut down to the time band `(a, b]`. -/
theorem coeFn_bandRestrict (T a b : ℝ≥0) (hab : a ≤ b) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ⇑(bandRestrict (μ := μ) T a b hBmeas φ) =ᵐ[trimMeasure_T (μ := μ) T hBmeas]
      fun z ↦ (Set.Ioc a b).indicator (fun _ ↦ (1 : ℝ)) z.1 * (φ : ℝ≥0 × Ω → ℝ) z := by
  simp only [bandRestrict]
  filter_upwards [Lp.coeFn_sub (restrictAfterCLM T a hBmeas φ) (restrictAfterCLM T b hBmeas φ),
    coeFn_restrictAfterCLM T a hBmeas φ, coeFn_restrictAfterCLM T b hBmeas φ] with z hsub ha hb
  rw [hsub, Pi.sub_apply, ha, hb]
  by_cases hza : a < z.1
  · by_cases hzb : b < z.1
    · rw [if_pos hza, if_pos hzb, sub_self,
        Set.indicator_of_notMem (fun hmem ↦ absurd hmem.2 (not_le.mpr hzb)), zero_mul]
    · rw [if_pos hza, if_neg hzb, sub_zero,
        Set.indicator_of_mem (by exact ⟨hza, not_lt.mp hzb⟩), one_mul]
  · have hzb : ¬ b < z.1 := fun h ↦ hza (lt_of_le_of_lt hab h)
    rw [if_neg hza, if_neg hzb, sub_zero,
      Set.indicator_of_notMem (fun hmem ↦ hza hmem.1), zero_mul]

omit [IsProbabilityMeasure μ] in
/-- `bandRestrict` vanishes on `[0, a]`, which is the support hypothesis the `𝓕_a`-linearity
of the Itô integral asks for. -/
theorem bandRestrict_eq_zero_of_le (T a b : ℝ≥0) (hab : a ≤ b)
    (hBmeas : ∀ t, Measurable (B t)) (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas), z.1 ≤ a →
      (bandRestrict (μ := μ) T a b hBmeas φ : ℝ≥0 × Ω → ℝ) z = 0 := by
  filter_upwards [coeFn_bandRestrict (μ := μ) T a b hab hBmeas φ] with z hz hza
  rw [hz, Set.indicator_of_notMem (fun hmem ↦ absurd hmem.1 (not_lt.mpr hza)), zero_mul]

/-- **The characterisation.** On an elementary integrand `Z·1_{(a,b]}` with `Z` bounded and
`𝓕_a`-measurable, the integral against `M` is the increment `Z·(M_b − M_a)` — the
Riemann–Stieltjes sum. This is what makes `itoIntegralAgainstCLM` the stochastic integral
against `M` rather than a name for a formula. -/
theorem itoIntegralAgainst_elementary (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    {a b : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T)
    (Z : Ω → ℝ) (hZm : Measurable[ItoIntegralL2.natFiltration hBmeas a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C)
    (ψ : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas φ))
    (hψ : ⇑ψ =ᵐ[bracketMeasure (μ := μ) T hBmeas φ] elemIntegrand a b Z) :
    ⇑(itoIntegralAgainstCLM hB T hBmeas φ ψ) =ᵐ[μ]
      fun ω ↦ Z ω * (itoProcessCLM hB T b hBmeas φ ω - itoProcessCLM hB T a hBmeas φ ω) := by
  -- the scaled band integrand, as an `L²` class
  set W := smulAdapted T a hBmeas Z hZm C hZb (bandRestrict (μ := μ) T a b hBmeas φ) with hW
  -- `mulLI ψ` and `W` are the same integrand
  have hmul : itoIntegralAgainstCLM hB T hBmeas φ ψ = itoIntegralCLM_T hB T hBmeas W := by
    refine itoIntegralAgainst_eq_itoIntegral T hBmeas φ ψ W ?_
    -- move the a.e. hypothesis across the weight: it is only `bracketMeasure`-a.e.
    have hcross : ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas),
        (φ : ℝ≥0 × Ω → ℝ) z ≠ 0 → (ψ : ℝ≥0 × Ω → ℝ) z = elemIntegrand a b Z z := by
      have := (ae_withDensity_iff (μ := trimMeasure_T (μ := μ) T hBmeas)
        (measurable_sqDensity (Lp.stronglyMeasurable φ).measurable)).1 hψ
      filter_upwards [this] with z hz hφz
      exact hz (sqDensity_ne_zero hφz)
    filter_upwards [hcross,
      coeFn_smulAdapted T a hBmeas Z hZm C hZb (bandRestrict (μ := μ) T a b hBmeas φ)
        (bandRestrict_eq_zero_of_le (μ := μ) T a b hab hBmeas φ),
      coeFn_bandRestrict (μ := μ) T a b hab hBmeas φ] with z hz hWz hbz
    simp only [hW, hWz, hbz]
    by_cases hφz : (φ : ℝ≥0 × Ω → ℝ) z = 0
    · rw [hφz, mul_zero, mul_zero, zero_mul]
    · simp only [hz hφz, elemIntegrand]
      ring
  rw [hmul]
  -- pull `Z` out, then read the band integral off the two restrictions
  have hband : itoIntegralCLM_T hB T hBmeas (bandRestrict (μ := μ) T a b hBmeas φ)
      = itoProcessCLM hB T b hBmeas φ - itoProcessCLM hB T a hBmeas φ := by
    simp only [bandRestrict]
    rw [map_sub,
      itoIntegralCLM_T_restrictAfterCLM (hB := hB) T a (hab.trans hbT) hBmeas φ,
      itoIntegralCLM_T_restrictAfterCLM (hB := hB) T b hbT hBmeas φ]
    abel
  filter_upwards [itoIntegralCLM_T_smulAdapted (hB := hB) T a hBmeas Z hZm C hZb
      (bandRestrict (μ := μ) T a b hBmeas φ)
      (bandRestrict_eq_zero_of_le (μ := μ) T a b hab hBmeas φ),
    Lp.coeFn_sub (itoProcessCLM hB T b hBmeas φ) (itoProcessCLM hB T a hBmeas φ)] with ω h1 h2
  rw [hW, h1, hband, h2, Pi.sub_apply]

/-! ### Uniqueness -/

/-- **Uniqueness.** A continuous linear map out of `L²(⟨M⟩)` that agrees with
`itoIntegralAgainstCLM` on the simple processes is `itoIntegralAgainstCLM`. With
`itoIntegralAgainst_elementary` identifying those values as the Riemann–Stieltjes sums, this
says the integral against `M` is the unique continuous linear extension of them. -/
theorem itoIntegralAgainst_unique (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (I : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas φ) →L[ℝ] Lp ℝ 2 μ)
    (hI : ∀ V : TBoundedSP T hBmeas,
      I (simpleAssemblyOfMeasure T hBmeas (bracketMeasure (μ := μ) T hBmeas φ) V)
        = itoIntegralAgainstCLM hB T hBmeas φ
            (simpleAssemblyOfMeasure T hBmeas (bracketMeasure (μ := μ) T hBmeas φ) V)) :
    I = itoIntegralAgainstCLM hB T hBmeas φ := by
  -- instance search does not unfold `bracketMeasure`, so hand it the unfolded form
  haveI : IsFiniteMeasure (sqWeight (trimMeasure_T (μ := μ) T hBmeas) (⇑φ)) :=
    instIsFiniteMeasureBracketMeasure (μ := μ) T hBmeas φ
  refine ContinuousLinearMap.ext fun ψ ↦ ?_
  exact congrFun (DenseRange.equalizer
    (simpleAssembly_sqWeight_denseRange T hBmeas (Lp.stronglyMeasurable φ).measurable)
    I.continuous (itoIntegralAgainstCLM hB T hBmeas φ).continuous (funext hI)) ψ

end ItoIntegralAgainstMartingale
end MathFin
