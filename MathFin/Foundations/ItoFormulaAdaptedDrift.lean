/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Foundations.ItoFormulaItoProcess
public import MathFin.Foundations.ItoDriftExpectation
public import MathFin.Foundations.ItoIntegralProcessGeneral
public import MathFin.Foundations.AdaptedProcessToLp
public import MathFin.Foundations.ItoIntegralRiemannBridgeAdapted
public import MathFin.Foundations.WeightedQuadraticVariation
public import MathFin.Foundations.ItoFormulaRemainder
public import MathFin.Foundations.DiscreteIto
public import MathFin.Foundations.ItoIntegralProcessIsometry
public import MathFin.Foundations.ItoIsometryAdapted
public import MathFin.Foundations.ItoIntegralBrownian
public import MathFin.Foundations.QuadraticVariationL2
public import MathFin.Foundations.GaussianMoments
public import MathFin.Foundations.AdaptedDrift

/-! # The integrated Itô–drift identity for adapted coefficients

The bounded-adapted case of the integrated Itô–drift identity — the expectation form of
Itô's formula along an Itô process with random coefficients,

  `𝔼[f(X_T)] = 𝔼[f(X_0)] + ∫₀ᵀ (𝔼[f'(X_s)·β_s] + ½·𝔼[f''(X_s)·δ_s²]) ds`,

for `β, δ` bounded, `natFiltration`-adapted and path-continuous, and `f` three times
differentiable with `f'`, `f''`, `f'''` bounded. `M` and `X` are hypotheses: a
`natFiltration`-adapted `M` with `M t =ᵐ (δ●B)_t` for every
`t ≥ 0` (`hMeq`, the process values of `itoProcessCLM` at the σ-realization `processToLp δ`),
and an `X` with `X t = c + ∫₀ᵗ β_s ds + M t` (`hXrel`) whose every path is continuous
(`hXcont`), which forces every path of `M` to be continuous.

That is a conditional theorem: no lemma in the library supplies such an `M` for general `δ`.
`exists_continuous_modification_itoProcess` is continuous only almost surely, and the
everywhere-continuous modification `exists_continuous_localMartingale_modification` is adapted
only to the augmented filtration `augFiltration`. For the process the library does construct,
the pathwise formula is `ItoFormulaAdapted.ito_formula_adapted` — and the expectation identity
itself is available for that process **unconditionally**, as
`itoDrift_expectation_identity_adapted_uncond` in `MathFin.Foundations.ItoFormulaAdaptedDriftUncond`
(a sibling module, so that this one stays free of the `ItoFormulaAdapted` import): a corollary
of the pathwise formula by centering (`integral_itoIntegralCLM_T`) and Fubini at a predictable
weight, with no `M`/`X` hypotheses (the #244 review's request; the conditional statement here
still quantifies over versions of `δ●B`). The constant-coefficient case is `ItoDriftExpectation`,
proved there separately.

Route: the per-path discrete Itô formula (`MathFin.discrete_ito_formula`) at the grid
values of `X`, integrated over `Ω`; the first-order martingale terms die exactly
(`mul_trueIncr_expect_eq_zero`, the martingale property of the adapted Itô integral
transferred along the a.e. `hMeq`); the drift block converges by pathwise Riemann–Stieltjes
sums + DCT + the Fubini interchange (`driftBlock_tendsto`); the quadratic block converges by
the summed weighted increment isometry (`quadraticSqSum_tendsto_uncond`, discharged from its
conditional form by the step-approximant `L²` convergence `deltaStepLp_tendsto`); the
drift² corrections (`quadDriftSqSum_tendsto`), the drift–martingale cross corrections
(`quadCrossSum_tendsto`) and the Taylor remainder (the cubic bound + the third-moment
estimate, `taylorRemainderSum_tendsto`, `trueIncr_pow3_le`) tend to `0` — the proofs bound
them by `O(mesh)`, `O(√mesh)` and `O(√mesh)`; only the limits are stated.

Main results: `MathFin.itoDrift_expectation_identity_adapted` (conditional, version-independent;
this file) and `MathFin.itoDrift_expectation_identity_adapted_uncond` (unconditional, for the
constructed process; `ItoFormulaAdaptedDriftUncond`). Supporting layers, bottom-up:
`bandIntegral_slice` (the band-to-slice conversion; the Fubini interchange
`expectation_pathIntegral_eq` comes from `ItoDriftExpectation`), `incrementEnergy` (the
increment-energy law), `deltaStepLp`/`deltaStepLp_tendsto` (the step approximants), the per-cell
weighted isometry (`weightedCellSq_step`, `clm_band_energy`, `stepIncr_stepCLM_ae`), the gap
decay (`errorIncr_ae`, `cellGap_le`, `gapSum_le`) and the unconditional quadratic block, the
fourth/third-moment bounds (`stepSum_pow4_le`, `trueIncr_pow4_le`, `trueIncr_pow3_le`),
the drift primitive (`AdaptedDrift.driftPath` reused, with its adaptedness
`stronglyMeasurable_driftPath`, from `Foundations/AdaptedDrift`), the drift
block, the two quadratic corrections and the Taylor-remainder convergence.

## Result

Headline (conditional, version-independent): `itoDrift_expectation_identity_adapted` — the
integrated Itô–drift identity stated above, for bounded adapted path-continuous coefficients,
under the hypotheses on `M` and `X` above. Its unconditional companion — the same identity for
the process the library constructs, derived from `ItoFormulaAdapted.ito_formula_adapted` by
centering and Fubini with strictly weaker function hypotheses — is
`itoDrift_expectation_identity_adapted_uncond` in `MathFin.Foundations.ItoFormulaAdaptedDriftUncond`.
Public supporting layers (all `MathFin.*`):

* foundations: `integral_mul_condExp_eq`, `memLp_M`, `incrementEnergy` (the increment
  isometry), `weightedCellSq_step` (the per-cell weighted isometry), the step approximants
  `deltaStepLp` / `deltaStepLp_tendsto`;
* convergence blocks: `driftBlock_tendsto` (with the drift primitive `AdaptedDrift.driftPath`
  and `driftSum_expect_tendsto`), `quadraticSqSum_tendsto` /
  `quadraticSqSum_tendsto_uncond`
  (via `gapSum_le` and the mean-function Riemann limit `frozenRiemann_tendsto`), the exact
  martingale kill `mul_trueIncr_expect_eq_zero`, the
  Taylor bound `taylorRemainderSum_tendsto` (`trueIncr_pow3_le`, `trueIncr_pow4_le`,
  `trueIncr_pow4_integrable`), and the dying corrections `quadDriftSqSum_tendsto` /
  `quadCrossSum_tendsto`.

Also public, and not used by the headline: `driftOscSum_tendsto`.

The constant-coefficient case and the Fubini interchange are `ito_drift_expectation_identity`
and `expectation_pathIntegral_eq` in `ItoDriftExpectation`.

Everything else in the file is `private` scaffolding.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace MathFin

open MathFin ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral
  QuadraticVariationL2 ItoIntegralBrownian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Telescoping over a partition: `∑_{k<n} (a_{k+1} − a_k) = a_n − a_0`. -/
private theorem sum_telescope (a : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, (a (k + 1) - a k) = a n - a 0 := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring

/-! ### Stage 2 — the bounded *adapted* coefficients (`β`, `δ` random)

The integrated Itô–drift identity for an Itô process with random adapted coefficients.
The data: a pre-Brownian motion `B` with measurable sections (path continuity of `B` is not
assumed), bounded adapted path-continuous `β, δ`, and, as hypotheses, `M` and `X` are
hypotheses: a `natFiltration`-adapted `M` with `M t =ᵐ (δ●B)_t` for every
`t ≥ 0` (`hMeq`, the process values of `itoProcessCLM` at the σ-realization `processToLp δ`),
and an `X` with `X t = c + ∫₀ᵗ β_s ds + M t` (`hXrel`) whose every path is continuous
(`hXcont`), which forces every path of `M` to be continuous.
No lemma in the library supplies such an `M` for general `δ` (see the module docstring).

`ΔX` over a cell splits into the drift increment plus the martingale increment. The proof is
the partition/Taylor skeleton of `ItoFormulaC2` at the path `k ↦ X_{tₖ}`
(`MathFin.discrete_ito_formula` — an exact per-path identity), with the three terms
dispatched by: pathwise Riemann sums (drift), the summed weighted increment isometry at the
adapted weight `f''(X)` (martingale square), and a cubic-moment bound (Taylor remainder).
Taking expectations turns
the pathwise identity into the integrated one; the drift integral crosses the expectation by
the stage-1 Fubini lemma `expectation_pathIntegral_eq`.

The per-cell second moments `E[(M_v−M_u)²]` come from the martingale property of `M`
(inherited a.e. from `itoProcessCLM`) and the time-indexed Itô isometry
`itoProcessCLM_norm_sq`. The blocks use `M` through `hMeq` and `hMadap`; path continuity
enters through the hypothesis `hXcont`. -/

section Adapted

open MeasureTheory ProbabilityTheory Filter Topology ItoIntegralProcessGeneral
open ItoIntegralL2 ItoIntegralCLM MathFin
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
  {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
  (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
  (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
  (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
  {M : ℝ≥0 → Ω → ℝ}
  (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
  (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
    (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))

/-- `E[g²] = ‖g‖²_{L²}` for the coe of an `Lp ℝ 2` element (real `L²`). -/
private theorem sqIntegral_of_Lp {ν : Measure Ω} (g : Lp ℝ 2 ν) :
    ∫ ω, g ω ^ 2 ∂ν = ‖g‖ ^ 2 := (lp_two_norm_sq g).symm

/-- **Expansion of the squared sum under the integral** (all three integrands integrable):
`E[(a+b)²] = E[a²] + 2·E[a·b] + E[b²]`. -/
private theorem integral_sq_add {α : Type*} {mα : MeasurableSpace α} {ν : Measure α}
    {a b : α → ℝ}
    (ha2 : Integrable (fun ω ↦ a ω ^ 2) ν) (hb2 : Integrable (fun ω ↦ b ω ^ 2) ν)
    (hab : Integrable (fun ω ↦ a ω * b ω) ν) :
    ∫ ω, (a ω + b ω) ^ 2 ∂ν
      = ∫ ω, a ω ^ 2 ∂ν + 2 * ∫ ω, a ω * b ω ∂ν + ∫ ω, b ω ^ 2 ∂ν := by
  have hpt : (fun ω ↦ (a ω + b ω) ^ 2) = fun ω ↦ a ω ^ 2 + 2 * (a ω * b ω) + b ω ^ 2 := by
    funext ω; ring
  have hpt : (fun ω ↦ (a ω + b ω) ^ 2) = fun ω ↦ a ω ^ 2 + 2 * (a ω * b ω) + b ω ^ 2 := by
    funext ω; ring
  rw [hpt]
  have h1 : ∫ ω, (a ω ^ 2 + 2 * (a ω * b ω) + b ω ^ 2) ∂ν
      = ∫ ω, (a ω ^ 2 + 2 * (a ω * b ω)) ∂ν + ∫ ω, b ω ^ 2 ∂ν :=
    integral_add (by exact (ha2.add (hab.const_mul 2))) hb2
  have h2 : ∫ ω, (a ω ^ 2 + 2 * (a ω * b ω)) ∂ν
      = ∫ ω, a ω ^ 2 ∂ν + 2 * ∫ ω, a ω * b ω ∂ν := by
    rw [integral_add ha2 (hab.const_mul 2), integral_const_mul]
  rw [h1, h2]

/-- **The band-slice conversion**: for a bounded adapted path-continuous `ψ`, the
`(u,v]`-band integral of its uncurried form over the predictable trim measure equals the
plain slice integral `∫_u^v 𝔼[ψ_s] ds`. Route: predictability of `(s,ω) ↦ ψ s ω`
(`isStronglyPredictable_of_bdd_adapted_cont`) drops the trim (`integral_trim`), the band
restriction moves to the time coordinate (`Measure.restrict_prod_eq_prod_univ` +
`Measure.restrict_restrict`), and the product integral Fubini-factors (`integral_prod`). -/
private theorem bandIntegral_slice (ψ : ℝ≥0 → Ω → ℝ)
    (hψadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (ψ t))
    (hψcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ ψ s ω)
    {Cψ : ℝ} (hψbdd : ∀ s ω, |ψ s ω| ≤ Cψ)
    (u v : ℝ≥0) (hvT : v ≤ T) :
    ∫ z in Set.Ioc u v ×ˢ (Set.univ : Set Ω), Function.uncurry ψ z
        ∂(trimMeasure_T (μ := μ) T hBmeas)
      = ∫ s in Set.Ioc u v, (∫ ω, ψ s ω ∂μ) ∂ItoIntegralL2.timeMeasure := by
  have hpred : IsStronglyPredictable (natFiltration hBmeas) ψ :=
    isStronglyPredictable_of_bdd_adapted_cont hBmeas hψadap hψcont
  have hband : MeasurableSet[(natFiltration hBmeas).predictable]
      (Set.Ioc u v ×ˢ (Set.univ : Set Ω)) :=
    MeasureTheory.measurableSet_predictable_Ioc_prod u v MeasurableSet.univ
  -- measurability/integrability of the band-indicatored integrand
  have hsm : StronglyMeasurable[(natFiltration hBmeas).predictable]
      ((Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ)) :=
    (show StronglyMeasurable[(natFiltration hBmeas).predictable] (Function.uncurry ψ) from
      hpred).indicator hband
  have hint : Integrable (Function.uncurry ψ) (trimMeasure_T (μ := μ) T hBmeas) :=
    (MemLp.of_bound hpred.aestronglyMeasurable Cψ
      (ae_of_all _ fun z ↦ by rw [Real.norm_eq_abs]; exact hψbdd z.1 z.2)).integrable one_le_two
  have hUVamb : MeasurableSet (Set.Ioc u v ×ˢ (Set.univ : Set Ω)) :=
    MeasurableSet.prod measurableSet_Ioc MeasurableSet.univ
  haveI : IsFiniteMeasure (ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      ItoIntegralL2.timeMeasure_Ioc]
    exact ENNReal.ofReal_lt_top
  have haesm : AEStronglyMeasurable ((Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator
      (Function.uncurry ψ)) ((ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)).prod μ) :=
    ⟨_, StronglyMeasurable.mono hsm (natFiltration hBmeas).predictable_le_prod,
      Eventually.of_forall fun _ ↦ rfl⟩
  have hint' : Integrable ((Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ))
      ((ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)).prod μ) := by
    refine Integrable.of_bound haesm (max Cψ 0) ?_
    refine Filter.Eventually.of_forall fun z ↦ ?_
    rw [Real.norm_eq_abs]
    by_cases hz : z ∈ (Set.Ioc u v ×ˢ (Set.univ : Set Ω))
    · rw [Set.indicator_of_mem hz]
      exact le_trans (hψbdd z.1 z.2) (le_max_left Cψ 0)
    · rw [Set.indicator_of_notMem hz]
      simp
  calc ∫ z in Set.Ioc u v ×ˢ (Set.univ : Set Ω), Function.uncurry ψ z
        ∂(trimMeasure_T (μ := μ) T hBmeas)
      = ∫ z, (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ) z
          ∂(trimMeasure_T (μ := μ) T hBmeas) :=
        (integral_indicator (μ := trimMeasure_T (μ := μ) T hBmeas)
          (f := Function.uncurry ψ) hband).symm
    _ = ∫ z, (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ) z
          ∂(((timeMeasure_T T).prod μ).trim
            (natFiltration hBmeas).predictable_le_prod) := rfl
    _ = ∫ z, (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ) z
          ∂((timeMeasure_T T).prod μ) :=
        (integral_trim (natFiltration hBmeas).predictable_le_prod hsm).symm
    _ = ∫ z, (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ) z
          ∂((ItoIntegralL2.timeMeasure.prod μ).restrict (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω))) := by
        rw [show (((timeMeasure_T T).prod μ : Measure (ℝ≥0 × Ω))
            = (ItoIntegralL2.timeMeasure.prod μ).restrict
              (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω))) from by
          rw [timeMeasure_T, Measure.restrict_prod_eq_prod_univ]]
    _ = ∫ z, (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)).indicator
          ((Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ)) z
          ∂(ItoIntegralL2.timeMeasure.prod μ) :=
        (integral_indicator (MeasurableSet.prod measurableSet_Ioc
          MeasurableSet.univ)).symm
    _ = ∫ z, (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ) z
          ∂(ItoIntegralL2.timeMeasure.prod μ) := by
        have hsub : (Set.Ioc u v ×ˢ (Set.univ : Set Ω))
            ⊆ (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)) := by
          rintro z hz
          exact ⟨⟨lt_of_le_of_lt (NNReal.coe_nonneg _) hz.1.1, le_trans hz.1.2 hvT⟩, hz.2⟩
        refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
        by_cases hz : z ∈ (Set.Ioc u v ×ˢ (Set.univ : Set Ω))
        · rw [Set.indicator_of_mem (hsub hz), Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz]
          by_cases hz2 : z ∈ (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω))
          · rw [Set.indicator_of_mem hz2, Set.indicator_of_notMem hz]
          · rw [Set.indicator_of_notMem hz2]
    _ = ∫ z in Set.Ioc u v ×ˢ (Set.univ : Set Ω), Function.uncurry ψ z
          ∂(ItoIntegralL2.timeMeasure.prod μ) := integral_indicator hUVamb
    _ = ∫ z, (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ) z
          ∂((ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)).prod μ) := by
        haveI : SFinite ItoIntegralL2.timeMeasure := inferInstance
        have hmeas : ((ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)).prod μ)
            = (ItoIntegralL2.timeMeasure.prod μ).restrict
              (Set.Ioc u v ×ˢ (Set.univ : Set Ω)) := by
          rw [Measure.restrict_prod_eq_prod_univ]
        rw [hmeas, integral_indicator hUVamb,
          Measure.restrict_restrict_of_subset
            (Set.Subset.refl (Set.Ioc u v ×ˢ (Set.univ : Set Ω)))]
    _ = ∫ s, (∫ ω, (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ) (s, ω) ∂μ)
          ∂(ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)) :=
        integral_prod _ hint'
    _ = ∫ s in Set.Ioc u v, (∫ ω, ψ s ω ∂μ) ∂ItoIntegralL2.timeMeasure := by
        refine setIntegral_congr_fun measurableSet_Ioc (fun s hs ↦ ?_)
        have hslice : ∀ ω' : Ω, (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator
            (Function.uncurry ψ) (s, ω') = ψ s ω' := by
          intro ω'
          rw [Set.indicator_of_mem
            (Set.mem_prod.mpr ⟨hs, Set.mem_univ ω'⟩)]
          rfl
        exact integral_congr_ae (Eventually.of_forall fun ω ↦ by
          show (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ) (s, ω) = _
          rw [hslice ω])

/-! ### Stages 3–5 — the weighted increment isometry, the third-moment bound, and the
assembly of the adapted drift identity

The data: a pre-Brownian `B` with measurable sections; bounded adapted path-continuous
`β, δ`; and the hypothesized `M` — a `natFiltration`-strongly-adapted *version* of the Itô
integral of `δ` (`M t =ᵐ (δ●B)_t` for every `t`, the CLM process values of the σ-realization
`processToLp δ`). The process under test, `X t = c + ∫₀ᵗ β_s ds + M t`, is likewise a
hypothesis (`hXrel`), and its path continuity is assumed (`hXcont`).

* `integral_mul_condExp_eq` — the expectation pull-out `𝔼[h · g] = 𝔼[h · 𝔼[g | 𝓕]]`;
* `incrementEnergy` — the unweighted increment isometry `𝔼[(M_v − M_u)²] = ∫_{(u,v]} δ² d(trim)`
  (`= ∫_u^v 𝔼[δ_s²] ds`), by the martingale pull-out `𝔼[M_u M_v] = 𝔼[M_u²]` plus the
  time-indexed isometry `itoProcessCLM_norm_sq` and the stage-2 `bandIntegral_slice`. It
  uses `M` only through `hMeq` and the adaptedness `hMadap`. -/

end Adapted

section AdaptedData

open MeasureTheory ProbabilityTheory Filter Topology ItoIntegralProcessGeneral
open ItoIntegralL2 ItoIntegralCLM ItoIsometryAdapted MathFin
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
  {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
  (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
  (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
  (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
  {M : ℝ≥0 → Ω → ℝ}
  (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
  (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
    (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))

include hB hBmeas hδadap hδcont hδbdd hMadap hMeq

/-! #### Stage 3 foundations — the expectation pull-out and the increment-energy law -/

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- **Expectation pull-out across a sub-σ-algebra** (the tower step): an `𝓕`-measurable
factor crosses the conditional expectation, `𝔼[h·g] = 𝔼[h·𝔼[g | 𝓕]]`. -/
theorem integral_mul_condExp_eq {𝓕 : MeasurableSpace Ω} (h𝓕 : 𝓕 ≤ mΩ)
    {h g : Ω → ℝ} (hh : StronglyMeasurable[𝓕] h) (hgh : Integrable (h * g) μ)
    (hg : Integrable g μ) :
    ∫ ω, h ω * g ω ∂μ = ∫ ω, h ω * μ[g | 𝓕] ω ∂μ := by
  calc ∫ ω, h ω * g ω ∂μ
      = ∫ ω, μ[h * g | 𝓕] ω ∂μ := (integral_condExp h𝓕).symm
    _ = ∫ ω, h ω * μ[g | 𝓕] ω ∂μ :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hh hgh hg)

omit hMadap in
/-- The Itô-integral process `M` is square-integrable at every time (its values are
a.e.-equal to `L²` CLM values). -/
theorem memLp_M (t : ℝ≥0) : MemLp (M t) 2 μ := by
  have h := Lp.memLp (itoProcessCLM hB T t hBmeas
    (processToLp T hBmeas hδadap hδcont hδbdd))
  refine ⟨h.1.congr (hMeq t).symm, ?_⟩
  rw [eLpNorm_congr_ae (hMeq t)]
  exact h.2

/-- **The increment-energy law** (the unweighted half of stage 3): for `u ≤ v ≤ T`,

  `𝔼[(M_v − M_u)²] = ∫_u^v 𝔼[δ_s²] ds`,

the energy of the Itô-integral increment over a time band is the predictable energy
of the band. Route: expand the square under the expectation and kill the cross term
by the martingale pull-out `𝔼[M_u M_v] = 𝔼[M_u²]` (the Itô integral is an
`𝓕_u`-martingale and `M_u` is `𝓕_u`-measurable), read the two second moments as
band energies by the time-indexed isometry `itoProcessCLM_norm_sq`, split the nested
bands `(0,u]` ⊔ `(u,v]` = `(0,v]`, and convert the band to the slice integral by the
stage-2 `bandIntegral_slice`. It uses `M` only through its a.e. agreement with the CLM
process (`hMeq`) and its adaptedness (`hMadap`). -/
theorem incrementEnergy {u v : ℝ≥0} (huv : u ≤ v) (hvT : v ≤ T) :
    ∫ ω, (M v ω - M u ω) ^ 2 ∂μ
      = ∫ s in Set.Ioc u v, (∫ ω, δ s ω * δ s ω ∂μ)
          ∂ItoIntegralL2.timeMeasure := by
  set φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) :=
    processToLp T hBmeas hδadap hδcont hδbdd with hφdef
  -- the martingale congruence `μ[M v | 𝓕_u] =ᵐ M u`
  have hmart : μ[M v | natFiltration hBmeas u] =ᵐ[μ] M u :=
    condExp_congr_ae (hMeq v) |>.trans
      ((itoIntegralProcessGen_isMartingale hB T hBmeas φ huv).trans (hMeq u).symm)
  -- the cross-term pull-out: `E[M_u M_v] = E[M_u²]`
  have hMM : ∫ ω, M u ω * M v ω ∂μ = ∫ ω, M u ω ^ 2 ∂μ := by
    have hprod : Integrable (fun ω ↦ M u ω * M v ω) μ :=
      (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq u).integrable_mul
        (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq v)
    have hcond : μ[(fun ω ↦ M u ω * M v ω) | natFiltration hBmeas u]
        =ᵐ[μ] (fun ω ↦ M u ω * μ[M v | natFiltration hBmeas u] ω) :=
      condExp_mul_of_stronglyMeasurable_left (hMadap u) hprod
        ((memLp_M hB hBmeas hδadap hδcont hδbdd hMeq v).integrable one_le_two)
    have hle : (natFiltration hBmeas u) ≤ mΩ := (natFiltration hBmeas).le u
    calc ∫ ω, M u ω * M v ω ∂μ
        = ∫ ω, μ[(fun ω ↦ M u ω * M v ω) | natFiltration hBmeas u] ω ∂μ :=
          (integral_condExp hle).symm
      _ = ∫ ω, M u ω * M u ω ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hcond, hmart] with ω hω hm
          rw [hω, hm]
      _ = ∫ ω, M u ω ^ 2 ∂μ := by
          exact integral_congr_ae (Eventually.of_forall fun ω ↦ by ring)
  -- second moment as band energy of the σ-realization (coe form)
  have hM2 : ∀ t : ℝ≥0, t ≤ T → ∫ ω, M t ω ^ 2 ∂μ
      = ∫ z in Set.Ioc (0:ℝ≥0) t ×ˢ (Set.univ : Set Ω), (φ : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas) := by
    intro t htT
    calc ∫ ω, M t ω ^ 2 ∂μ
        = ∫ ω, (itoProcessCLM hB T t hBmeas φ : Ω → ℝ) ω ^ 2 ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hMeq t] with ω hω
          rw [hω, hφdef]
      _ = ‖itoProcessCLM hB T t hBmeas φ‖ ^ 2 := sqIntegral_of_Lp _
      _ = ∫ z in Set.Ioc (0:ℝ≥0) t ×ˢ (Set.univ : Set Ω), (φ : ℝ≥0 × Ω → ℝ) z ^ 2
            ∂(trimMeasure_T (μ := μ) T hBmeas) := itoProcessCLM_norm_sq hB htT hBmeas φ
  -- the nested-band split of the band energies
  have hbandv := hM2 v hvT
  have hbandu := hM2 u (le_trans huv hvT)
  have hdisj : Disjoint
      ((Set.Ioc (0:ℝ≥0) u) ×ˢ (Set.univ : Set Ω)) ((Set.Ioc u v) ×ˢ (Set.univ : Set Ω)) :=
    Set.disjoint_left.2 fun a ha hb ↦ by
      have h1 : (u : ℝ) < (a.1 : ℝ) := by exact_mod_cast hb.1.1
      have h2 : (a.1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast ha.1.2
      linarith
  have hint : Integrable (fun z : ℝ≥0 × Ω ↦ (φ : ℝ≥0 × Ω → ℝ) z ^ 2)
      (trimMeasure_T (μ := μ) T hBmeas) := (Lp.memLp φ).integrable_sq
  have hintUU : IntegrableOn (fun z : ℝ≥0 × Ω ↦ (φ : ℝ≥0 × Ω → ℝ) z ^ 2)
      ((Set.Ioc (0:ℝ≥0) u) ×ˢ (Set.univ : Set Ω)) (trimMeasure_T (μ := μ) T hBmeas) :=
    hint.mono_measure Measure.restrict_le_self
  have hintUV : IntegrableOn (fun z : ℝ≥0 × Ω ↦ (φ : ℝ≥0 × Ω → ℝ) z ^ 2)
      ((Set.Ioc u v) ×ˢ (Set.univ : Set Ω)) (trimMeasure_T (μ := μ) T hBmeas) :=
    hint.mono_measure Measure.restrict_le_self
  have hbandsplit : ∫ z in Set.Ioc (0:ℝ≥0) v ×ˢ (Set.univ : Set Ω),
      (φ : ℝ≥0 × Ω → ℝ) z ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas)
      = ∫ z in Set.Ioc (0:ℝ≥0) u ×ˢ (Set.univ : Set Ω),
          (φ : ℝ≥0 × Ω → ℝ) z ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas)
        + ∫ z in Set.Ioc u v ×ˢ (Set.univ : Set Ω),
          (φ : ℝ≥0 × Ω → ℝ) z ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas) := by
    have hprod0 : (Set.Ioc (0:ℝ≥0) u ×ˢ (Set.univ : Set Ω))
        ∪ (Set.Ioc u v ×ˢ (Set.univ : Set Ω))
        = (Set.Ioc (0:ℝ≥0) v) ×ˢ (Set.univ : Set Ω) := by
      rw [← Set.union_prod, Set.Ioc_union_Ioc_eq_Ioc (by norm_num : (0:ℝ≥0) ≤ u) huv]
    rw [← hprod0]
    exact setIntegral_union hdisj
      (MeasureTheory.measurableSet_predictable_Ioc_prod u v MeasurableSet.univ)
      hintUU hintUV
  -- the band-to-slice conversion (stage-2 `bandIntegral_slice` at `δ²`)
  have hbandδ : ∀ a b : ℝ≥0, a ≤ b → b ≤ T →
      ∫ z in Set.Ioc a b ×ˢ (Set.univ : Set Ω), (φ : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas)
        = ∫ s in Set.Ioc a b, (∫ ω, δ s ω * δ s ω ∂μ)
            ∂ItoIntegralL2.timeMeasure := by
    intro a b hab hbT
    have hcoe : ∫ z in Set.Ioc a b ×ˢ (Set.univ : Set Ω),
        (φ : ℝ≥0 × Ω → ℝ) z ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas)
        = ∫ z in Set.Ioc a b ×ˢ (Set.univ : Set Ω),
            Function.uncurry (fun s ω ↦ δ s ω * δ s ω) z
            ∂(trimMeasure_T (μ := μ) T hBmeas) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae
        (processToLp_coeFn T hBmeas hδadap hδcont hδbdd)] with z hz
      show (φ : ℝ≥0 × Ω → ℝ) z ^ 2 = Function.uncurry (fun s ω ↦ δ s ω * δ s ω) z
      rw [hz, pow_two]
      rfl
    rw [hcoe, bandIntegral_slice hBmeas (μ := μ)
      (ψ := fun (t : ℝ≥0) (ω : Ω) ↦ δ t ω * δ t ω)
      (hψadap := fun t ↦ (hδadap t).mul (hδadap t))
      (hψcont := fun ω ↦ (hδcont ω).mul (hδcont ω))
      (hψbdd := fun s ω ↦ by
        rw [abs_mul]
        calc |δ s ω| * |δ s ω| ≤ Dd * |δ s ω| :=
              mul_le_mul_of_nonneg_right (hδbdd s ω) (abs_nonneg _)
          _ ≤ Dd * Dd := mul_le_mul_of_nonneg_left (hδbdd s ω)
              (le_trans (abs_nonneg _) (hδbdd 0 ω)))
      a b hbT]
  -- expansion of the squared increment under the expectation
  have hprod : Integrable (fun ω ↦ M u ω * M v ω) μ :=
    (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq u).integrable_mul
      (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq v)
  have hsplit : ∫ ω, (M v ω - M u ω) ^ 2 ∂μ
      = ∫ ω, M v ω ^ 2 ∂μ - ∫ ω, M u ω ^ 2 ∂μ := by
    have hint1 : Integrable (fun ω ↦ M v ω ^ 2) μ :=
      (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq v).integrable_sq
    have hint2 : Integrable (fun ω ↦ M u ω ^ 2) μ :=
      (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq u).integrable_sq
    have hA : Integrable (fun ω ↦ M v ω ^ 2 - 2 * (M u ω * M v ω)) μ :=
      hint1.sub (hprod.const_mul 2)
    have hstep : ∫ ω, (M v ω ^ 2 - 2 * (M u ω * M v ω) + M u ω ^ 2) ∂μ
        = ∫ ω, M v ω ^ 2 ∂μ - ∫ ω, M u ω ^ 2 ∂μ := by
      calc ∫ ω, (M v ω ^ 2 - 2 * (M u ω * M v ω) + M u ω ^ 2) ∂μ
          = ∫ ω, (M v ω ^ 2 - 2 * (M u ω * M v ω)) ∂μ + ∫ ω, M u ω ^ 2 ∂μ :=
            integral_add hA hint2
        _ = (∫ ω, M v ω ^ 2 ∂μ - ∫ ω, 2 * (M u ω * M v ω) ∂μ) + ∫ ω, M u ω ^ 2 ∂μ :=
            by rw [integral_sub hint1 (hprod.const_mul 2)]
        _ = ∫ ω, M v ω ^ 2 ∂μ - ∫ ω, M u ω ^ 2 ∂μ := by
            rw [integral_const_mul, hMM]
            ring
    calc ∫ ω, (M v ω - M u ω) ^ 2 ∂μ
        = ∫ ω, (M v ω ^ 2 - 2 * (M u ω * M v ω) + M u ω ^ 2) ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun ω ↦ ?_)
          show (M v ω - M u ω) ^ 2 = M v ω ^ 2 - 2 * (M u ω * M v ω) + M u ω ^ 2
          ring
      _ = ∫ ω, M v ω ^ 2 ∂μ - ∫ ω, M u ω ^ 2 ∂μ := hstep
  rw [hsplit, hbandv, hbandu, hbandsplit,
    hbandδ (0:ℝ≥0) u (by norm_num : (0:ℝ≥0) ≤ u) (le_trans huv hvT),
    hbandδ u v huv hvT]
  ring

/-! #### Stage 3 — the weighted increment isometry via left-endpoint step approximants

The route: for the left-endpoint step approximant `δⁿ` of `δ` on the uniform
partition, the per-cell increment of the approximant integral is the single-rectangle
integral `δ(tₖ)·ΔBₖ`, so the weighted second-moment identity is independence algebra
(`integral_adapted_mul_increment_sq`); the passage `n → ∞` is the `L²`-contraction
of the Itô isometry plus `‖δ − δⁿ‖_{L²(trim)} → 0`. The convergence
`deltaStepLp_tendsto` needs no new analytic work: the terminal Itô isometry is an
isometry, so it transfers the Riemann bridge's `L²` convergence of the Itô sums
(`itoIntegralCLM_T_of_bdd_adapted_cont`) to the integrand classes. -/

open ItoIntegralRiemannBridge

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- The `n`-th left-endpoint step approximant of the integrand `δ`, as an element of
the Itô-integrand space (the `simpleAssembly_T` embedding of `stepσ n`). -/
noncomputable def deltaStepLp (hBmeas : ∀ t, Measurable (B t))
    {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδbdd : ∀ t ω, |δ t ω| ≤ Dd) (n : ℕ) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) :=
  simpleAssembly_T (μ := μ) T hBmeas (stepσ hBmeas hδadap hδbdd T n)

omit hB hMadap hMeq in
omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- **`L²`-convergence of the step approximants**: `‖δⁿ − δ‖_{L²(trim)} → 0`. The
terminal Itô isometry `itoIntegralCLM_T_norm` is an isometry, so the norm of the
integrand difference equals the norm of the difference of the Itô sums — the
Riemann bridge's `L²` convergence (`itoIntegralCLM_T_of_bdd_adapted_cont`), with the
step-integrand sum identified with the Riemann sum by `itoIntegralCLM_T_stepσ`. -/
theorem deltaStepLp_tendsto (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    (hδbdd : ∀ t ω, |δ t ω| ≤ Dd) :
    Tendsto (fun n : ℕ ↦ (deltaStepLp hBmeas hδadap hδbdd n :
        Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))) atTop
      (𝓝 (processToLp T hBmeas hδadap hδcont hδbdd)) := by
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  have hiso : ∀ ψ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      ‖ψ‖ = ‖itoIntegralCLM_T hB T hBmeas ψ‖ := fun ψ ↦
    (itoIntegralCLM_T_norm hB T hBmeas ψ).symm
  have hstep : ∀ n : ℕ, itoIntegralCLM_T hB T hBmeas (deltaStepLp hBmeas hδadap hδbdd n)
      = (memLp_riemannσ hB hBmeas hδadap hδbdd T n).toLp (riemannσ δ T n) :=
    fun n ↦ itoIntegralCLM_T_stepσ hB hBmeas hδadap hδbdd T n
  have key : ∀ n : ℕ,
      ‖(deltaStepLp hBmeas hδadap hδbdd n
          - processToLp T hBmeas hδadap hδcont hδbdd : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖
      = ‖((memLp_riemannσ hB hBmeas hδadap hδbdd T n).toLp (riemannσ δ T n)
          - itoIntegralCLM_T hB T hBmeas (processToLp T hBmeas hδadap hδcont hδbdd) :
            Lp ℝ 2 μ)‖ := by
    intro n
    rw [hiso _]
    congr 1
    rw [map_sub, hstep n]
  have hbridge := itoIntegralCLM_T_of_bdd_adapted_cont hB hBmeas hδadap hδcont hδbdd T
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hbridge ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hN' := hN n hn
  rw [dist_eq_norm] at hN'
  rw [key n, dist_eq_norm, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  exact hN' 

end AdaptedData

/-! #### Stage 4 — the weighted increment isometry (per-cell step identification, the
gap decay, and the summed isometry)

The route: for the left-endpoint step approximant `δⁿ` of `δ`
on the uniform partition, the per-cell increment of the approximant process is the single
rectangle `δ(tₖ)·ΔBₖ` (min-algebra on `itoSimpleProcess_apply`), so the weighted
second-moment identity on the approximant is the independence isometry kernel
`integral_adapted_mul_increment_sq` at `χ = wₖ·δ(tₖ)²`; the true increment decomposes as
`ΔMₖ = δ(tₖ)ΔBₖ + δεₖ` with `δεₖ` the band-restricted CLM increment of the integrand
error `φ − δⁿ`, whose `L²` norm is exactly the cell band energy (`clm_band_energy`),
and Cauchy–Schwarz pairs each cell band with the cell energy. Summing kills the gap at
rate `√T·‖δ − δⁿ‖_{L²(trim)} → 0` (`deltaStepLp_tendsto`). -/

section StageFour

open MeasureTheory ProbabilityTheory Filter Topology ItoIntegralProcessGeneral
open ItoIntegralL2 ItoIntegralCLM ItoIntegralRiemannBridge ItoIsometryAdapted
open ItoIntegralProcess QuadraticVariationL2 MathFin
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Real `L²` pairing bound: `∫ |f g| ≤ ‖f‖₂·‖g‖₂` (Hölder at exponents `2, 2`). -/
private theorem integral_abs_mul_le_L2L2 {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ ω, |f ω * g ω| ∂μ
      ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂μ) * Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
  have hp : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hf' : MemLp |f| (ENNReal.ofReal 2) μ := by simpa using hf.abs
  have hg' : MemLp |g| (ENNReal.ofReal 2) μ := by simpa using hg.abs
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hp
    (f := fun ω ↦ |f ω|) (g := fun ω ↦ |g ω|)
    (ae_of_all μ fun ω ↦ abs_nonneg _) (ae_of_all μ fun ω ↦ abs_nonneg _)
    hf' hg'
  have h2f : ∫ a, |f a| ^ (2 : ℝ) ∂μ = ∫ a, f a ^ 2 ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun a ↦ ?_)
    show |f a| ^ (2 : ℝ) = f a ^ 2
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  have h2g : ∫ a, |g a| ^ (2 : ℝ) ∂μ = ∫ a, g a ^ 2 ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun a ↦ ?_)
    show |g a| ^ (2 : ℝ) = g a ^ 2
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [h2f, h2g] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  have hfin : ∫ a, |f a| * |g a| ∂μ = ∫ a, |f a * g a| ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun a ↦ ?_)
    show |f a| * |g a| = |f a * g a|
    rw [abs_mul]
  rw [hfin] at h
  exact h

/-- The process-level elementary Itô integral is additive over finite sums of simple
processes (the `itoSimpleProcess` analogue of `ItoIntegralBrownian.itoSimple_sum`). -/
private lemma itoSimpleProcess_finsetSum {B : ℝ≥0 → Ω → ℝ} (hBmeas : ∀ t, Measurable (B t))
    {ι' : Type*} (s : Finset ι') (V : ι' → SimpleProcess ℝ (natFiltration hBmeas)) (t : ℝ≥0) :
    itoSimpleProcess hBmeas (∑ i ∈ s, V i) t = ∑ i ∈ s, itoSimpleProcess hBmeas (V i) t := by
  classical
  induction s using Finset.induction with
  | empty => funext ω; simp [itoSimpleProcess]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, itoSimpleProcess_add, ih]

/-- A single bounded adapted step evaluated at an arbitrary time is the coefficient times
the truncated increment. -/
private lemma itoSimpleProcess_stepSP_apply {B : ℝ≥0 → Ω → ℝ} (hBmeas : ∀ t, Measurable (B t))
    {T a b : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T) {φ : Ω → ℝ}
    (hφ : Measurable[natFiltration hBmeas a] φ) {Mφ : ℝ} (hφM : ∀ ω, |φ ω| ≤ Mφ)
    (t : ℝ≥0) (ω : Ω) :
    itoSimpleProcess hBmeas (stepSP hBmeas hab hbT hφ hφM).val t ω
      = φ ω * (B (min b t) ω - B (min a t) ω) := by
  rw [itoSimpleProcess_apply]
  show (Finsupp.single (a, b) φ).sum (fun p v ↦ v ω * (B (min p.2 t) ω - B (min p.1 t) ω)) = _
  rw [Finsupp.sum_single_index (by simp)]

/-- **Per-cell step identification** (min-algebra): over cell `k` of the uniform partition,
the `n`-step left-endpoint step process increments by exactly the single rectangle
`δ(tₖ)·(B_{tₖ₊₁} − B_{tₖ})` — every other cell telescopes to zero and the diagonal cell
is untruncated. -/
private lemma itoSimpleProcess_stepσ_incr {B : ℝ≥0 → Ω → ℝ} (hBmeas : ∀ t, Measurable (B t))
    {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδbdd : ∀ t ω, |δ t ω| ≤ Dd) (T : ℝ≥0) {n k : ℕ} (hk : k < n) (ω : Ω) :
    itoSimpleProcess hBmeas (stepσ hBmeas hδadap hδbdd T n).val (unifPart T n (k + 1)) ω
        - itoSimpleProcess hBmeas (stepσ hBmeas hδadap hδbdd T n).val (unifPart T n k) ω
      = δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) := by
  have hmono : Monotone (unifPart T n) := unifPart_mono T n
  set t : ℕ → ℝ≥0 := unifPart T n with ht
  -- both process values as sums of per-cell single-rectangle evaluations
  have hstepval : ∀ t' : ℝ≥0,
      itoSimpleProcess hBmeas (stepσ hBmeas hδadap hδbdd T n).val t' ω
        = ∑ j ∈ (Finset.range n).attach,
            δ (t j.1) ω * (B (min (t (j.1 + 1)) t') ω - B (min (t j.1) t') ω) := by
    intro t'
    rw [stepσ, AddSubmonoidClass.coe_finsetSum, itoSimpleProcess_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [itoSimpleProcess_stepSP_apply hBmeas (unifPart_mono T n (Nat.le_succ j.1))
      (unifPart_le_T (Finset.mem_range.mp j.2)) (hδadap (t j.1)).measurable]
  rw [hstepval, hstepval, ← Finset.sum_sub_distrib]
  have hzero : ∀ j ∈ (Finset.range n).attach,
      j ≠ ⟨k, Finset.mem_range.mpr hk⟩ →
        δ (t ↑j) ω * (B (min (t (↑j + 1)) (t (k + 1))) ω - B (min (t ↑j) (t (k + 1))) ω)
          - δ (t ↑j) ω * (B (min (t (↑j + 1)) (t k)) ω - B (min (t ↑j) (t k)) ω) = 0 := by
    rintro j _ hj
    have hjk : (j : ℕ) ≠ k := fun h => hj (Subtype.ext h)
    by_cases hlt : (j : ℕ) < k
    · have h1 : min (t ((j : ℕ) + 1)) (t (k + 1)) = t ((j : ℕ) + 1) :=
        min_eq_left (hmono (by omega))
      have h2 : min (t (j : ℕ)) (t (k + 1)) = t (j : ℕ) := min_eq_left (hmono (by omega))
      have h3 : min (t ((j : ℕ) + 1)) (t k) = t ((j : ℕ) + 1) := min_eq_left (hmono (by omega))
      have h4 : min (t (j : ℕ)) (t k) = t (j : ℕ) := min_eq_left (hmono (by omega))
      rw [h1, h2, h3, h4]; ring
    · have h1 : min (t ((j : ℕ) + 1)) (t (k + 1)) = t (k + 1) :=
        min_eq_right (hmono (by omega))
      have h2 : min (t (j : ℕ)) (t (k + 1)) = t (k + 1) := min_eq_right (hmono (by omega))
      have h3 : min (t ((j : ℕ) + 1)) (t k) = t k := min_eq_right (hmono (by omega))
      have h4 : min (t (j : ℕ)) (t k) = t k := min_eq_right (hmono (by omega))
      rw [h1, h2, h3, h4]; ring
  rw [Finset.sum_eq_single_of_mem (f := fun j : {x // x ∈ Finset.range n} ↦
      δ (t j.1) ω * (B (min (t (j.1 + 1)) (t (k + 1))) ω - B (min (t j.1) (t (k + 1))) ω)
        - δ (t j.1) ω * (B (min (t (j.1 + 1)) (t k)) ω - B (min (t j.1) (t k)) ω))
    (⟨k, Finset.mem_range.mpr hk⟩) (Finset.mem_attach _ _) hzero]
  show δ (t k) ω * (B (min (t (k + 1)) (t (k + 1))) ω - B (min (t k) (t (k + 1))) ω)
      - δ (t k) ω * (B (min (t (k + 1)) (t k)) ω - B (min (t k) (t k)) ω)
    = δ (t k) ω * (B (t (k + 1)) ω - B (t k) ω)
  rw [min_self, min_self,
    min_eq_left (hmono (Nat.le_succ k)), min_eq_right (hmono (Nat.le_succ k))]
  ring

/-- **The CLM band-energy law**: the `L²` energy of the increment of the CLM Itô-integral
process of an arbitrary integrand class `φ'` over a band `(u,v]` is the band energy of the
integrand — the version-free analogue of `incrementEnergy`, proved directly at the CLM
level (the a.e. pull-out for the martingale cross term, the time-indexed isometry
`itoProcessCLM_norm_sq`, and the nested-band split). -/
private theorem clm_band_energy {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (φ' : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {u v : ℝ≥0} (huv : u ≤ v) (hvT : v ≤ T) :
    ∫ ω, ((itoProcessCLM hB T v hBmeas φ' : Ω → ℝ) ω
        - (itoProcessCLM hB T u hBmeas φ' : Ω → ℝ) ω) ^ 2 ∂μ
      = ∫ z in Set.Ioc u v ×ˢ (Set.univ : Set Ω), (φ' : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas) := by
  set A := itoProcessCLM hB T v hBmeas φ' with hAdef
  set b := itoProcessCLM hB T u hBmeas φ' with hbdef
  -- the martingale congruence at CLM level
  have hmart : μ[(A : Ω → ℝ) | natFiltration hBmeas u] =ᵐ[μ] (b : Ω → ℝ) :=
    itoIntegralProcessGen_isMartingale hB T hBmeas φ' huv
  have hAmem := Lp.memLp A
  have hbmem := Lp.memLp b
  have hAint : Integrable (A : Ω → ℝ) μ := hAmem.integrable one_le_two
  have hbint : Integrable (b : Ω → ℝ) μ := hbmem.integrable one_le_two
  -- cross-term kill through the a.e. pull-out (CLM values are a.e. 𝓕_u-measurable)
  have hbae : AEStronglyMeasurable[natFiltration hBmeas u] (b : Ω → ℝ) μ :=
    itoProcessCLM_aeStronglyMeasurable (μ := μ) hB T u hBmeas φ'
  have hAprod : Integrable (fun ω ↦ (b : Ω → ℝ) ω * (A : Ω → ℝ) ω) μ :=
    hbmem.integrable_mul hAmem
  have hcross : ∫ ω, (b : Ω → ℝ) ω * (A : Ω → ℝ) ω ∂μ
      = ∫ ω, (b : Ω → ℝ) ω * (b : Ω → ℝ) ω ∂μ := by
    calc ∫ ω, (b : Ω → ℝ) ω * (A : Ω → ℝ) ω ∂μ
        = ∫ ω, μ[(fun ω' ↦ (b : Ω → ℝ) ω' * (A : Ω → ℝ) ω') | natFiltration hBmeas u] ω ∂μ :=
          (integral_condExp ((natFiltration hBmeas).le u)).symm
      _ = ∫ ω, (b : Ω → ℝ) ω * μ[(A : Ω → ℝ) | natFiltration hBmeas u] ω ∂μ :=
          integral_congr_ae (condExp_mul_of_aestronglyMeasurable_left hbae hAprod hAint)
      _ = ∫ ω, (b : Ω → ℝ) ω * (b : Ω → ℝ) ω ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hmart] with ω hω
          rw [hω]
  have hAmem2 : Integrable (fun ω ↦ (A : Ω → ℝ) ω ^ 2) μ := hAmem.integrable_sq
  have hbmem2 : Integrable (fun ω ↦ (b : Ω → ℝ) ω ^ 2) μ := hbmem.integrable_sq
  -- expansion of the squared increment
  have hsplit : ∫ ω, ((A : Ω → ℝ) ω - (b : Ω → ℝ) ω) ^ 2 ∂μ
      = ∫ ω, (A : Ω → ℝ) ω ^ 2 ∂μ - ∫ ω, (b : Ω → ℝ) ω ^ 2 ∂μ := by
    have hsq : ∫ ω, ((A : Ω → ℝ) ω - (b : Ω → ℝ) ω) ^ 2 ∂μ
        = ∫ ω, ((A : Ω → ℝ) ω ^ 2 - 2 * ((b : Ω → ℝ) ω * (A : Ω → ℝ) ω)
            + (b : Ω → ℝ) ω ^ 2) ∂μ := by
      refine integral_congr_ae (Eventually.of_forall fun ω ↦ ?_)
      show ((A : Ω → ℝ) ω - (b : Ω → ℝ) ω) ^ 2 = _
      ring
    rw [hsq]
    have h1 : ∫ ω, ((A : Ω → ℝ) ω ^ 2 - 2 * ((b : Ω → ℝ) ω * (A : Ω → ℝ) ω)
        + (b : Ω → ℝ) ω ^ 2) ∂μ
        = ∫ ω, ((A : Ω → ℝ) ω ^ 2 - 2 * ((b : Ω → ℝ) ω * (A : Ω → ℝ) ω)) ∂μ
          + ∫ ω, (b : Ω → ℝ) ω ^ 2 ∂μ :=
      integral_add (hAmem2.sub (hAprod.const_mul 2)) hbmem2
    rw [h1]
    have h2 : ∫ ω, ((A : Ω → ℝ) ω ^ 2 - 2 * ((b : Ω → ℝ) ω * (A : Ω → ℝ) ω)) ∂μ
        = ∫ ω, (A : Ω → ℝ) ω ^ 2 ∂μ - ∫ ω, 2 * ((b : Ω → ℝ) ω * (A : Ω → ℝ) ω) ∂μ :=
      integral_sub hAmem2 (hAprod.const_mul 2)
    rw [h2, integral_const_mul, hcross]
    have hbb : ∫ ω, (b : Ω → ℝ) ω * (b : Ω → ℝ) ω ∂μ = ∫ ω, (b : Ω → ℝ) ω ^ 2 ∂μ :=
      integral_congr_ae (Eventually.of_forall fun ω ↦ by
        show (b : Ω → ℝ) ω * (b : Ω → ℝ) ω = _
        ring)
    rw [hbb]
    ring
  -- band energies through the time-indexed isometry
  have hband : ∀ w : ℝ≥0, w ≤ T →
      ∫ ω, (itoProcessCLM hB T w hBmeas φ' : Ω → ℝ) ω ^ 2 ∂μ
        = ∫ z in Set.Ioc (0:ℝ≥0) w ×ˢ (Set.univ : Set Ω), (φ' : ℝ≥0 × Ω → ℝ) z ^ 2
            ∂(trimMeasure_T (μ := μ) T hBmeas) := by
    intro w hwT
    calc ∫ ω, (itoProcessCLM hB T w hBmeas φ' : Ω → ℝ) ω ^ 2 ∂μ
        = ‖itoProcessCLM hB T w hBmeas φ'‖ ^ 2 := sqIntegral_of_Lp _
      _ = ∫ z in Set.Ioc (0:ℝ≥0) w ×ˢ (Set.univ : Set Ω), (φ' : ℝ≥0 × Ω → ℝ) z ^ 2
            ∂(trimMeasure_T (μ := μ) T hBmeas) := itoProcessCLM_norm_sq hB hwT hBmeas φ'
  have hint : Integrable (fun z : ℝ≥0 × Ω ↦ (φ' : ℝ≥0 × Ω → ℝ) z ^ 2)
      (trimMeasure_T (μ := μ) T hBmeas) := (Lp.memLp φ').integrable_sq
  have hintU : IntegrableOn (fun z : ℝ≥0 × Ω ↦ (φ' : ℝ≥0 × Ω → ℝ) z ^ 2)
      ((Set.Ioc (0:ℝ≥0) u) ×ˢ (Set.univ : Set Ω)) (trimMeasure_T (μ := μ) T hBmeas) :=
    hint.mono_measure Measure.restrict_le_self
  have hintUV : IntegrableOn (fun z : ℝ≥0 × Ω ↦ (φ' : ℝ≥0 × Ω → ℝ) z ^ 2)
      ((Set.Ioc u v) ×ˢ (Set.univ : Set Ω)) (trimMeasure_T (μ := μ) T hBmeas) :=
    hint.mono_measure Measure.restrict_le_self
  have hdisj : Disjoint
      ((Set.Ioc (0:ℝ≥0) u) ×ˢ (Set.univ : Set Ω)) ((Set.Ioc u v) ×ˢ (Set.univ : Set Ω)) :=
    Set.disjoint_left.2 fun a ha hb ↦ by
      have h1 : (u : ℝ) < (a.1 : ℝ) := by exact_mod_cast hb.1.1
      have h2 : (a.1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast ha.1.2
      linarith
  have hbandsplit : ∫ z in Set.Ioc (0:ℝ≥0) v ×ˢ (Set.univ : Set Ω),
      (φ' : ℝ≥0 × Ω → ℝ) z ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas)
      = ∫ z in Set.Ioc (0:ℝ≥0) u ×ˢ (Set.univ : Set Ω), (φ' : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas)
        + ∫ z in Set.Ioc u v ×ˢ (Set.univ : Set Ω), (φ' : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas) := by
    have hprod0 : (Set.Ioc (0:ℝ≥0) u ×ˢ (Set.univ : Set Ω))
        ∪ (Set.Ioc u v ×ˢ (Set.univ : Set Ω))
        = (Set.Ioc (0:ℝ≥0) v) ×ˢ (Set.univ : Set Ω) := by
      rw [← Set.union_prod, Set.Ioc_union_Ioc_eq_Ioc (by norm_num : (0:ℝ≥0) ≤ u) huv]
    rw [← hprod0]
    exact setIntegral_union hdisj
      (MeasureTheory.measurableSet_predictable_Ioc_prod u v MeasurableSet.univ)
      hintU hintUV
  rw [hsplit, hband v hvT, hband u (le_trans huv hvT), hbandsplit]
  ring

end StageFour

/-! #### Stage 4 (headline) — the per-cell weighted identity, the gap decay, and the
summed weighted increment isometry -/

section StageFourB

open MeasureTheory ProbabilityTheory Filter Topology ItoIntegralProcessGeneral
open ItoIntegralL2 ItoIntegralCLM ItoIntegralRiemannBridge ItoIsometryAdapted
open ItoIntegralProcess QuadraticVariationL2 MathFin
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- The uniform-partition band split: the `(0,T]`-band integral of an integrable
space-time function is the sum of its uniform cell integrals (iterated
`setIntegral_union` over the nested left endpoints). -/
private lemma uniform_band_split (hBmeas : ∀ t, Measurable (B t)) {T : ℝ≥0} {n : ℕ}
    (hn : 0 < n) {F : ℝ≥0 × Ω → ℝ}
    (hFint : Integrable F (trimMeasure_T (μ := μ) T hBmeas)) :
    ∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω), F z
        ∂(trimMeasure_T (μ := μ) T hBmeas)
      = ∑ k ∈ Finset.range n,
          ∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ (Set.univ : Set Ω),
            F z ∂(trimMeasure_T (μ := μ) T hBmeas) := by
  have hTn : unifPart T n n = T := by
    have hne : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    simp only [unifPart, div_self hne, one_mul]
  have hintOn : ∀ m : ℕ, m ≤ n →
      IntegrableOn F ((Set.Ioc (0:ℝ≥0) (unifPart T n m)) ×ˢ (Set.univ : Set Ω))
        (trimMeasure_T (μ := μ) T hBmeas) := by
    intro m hm
    exact hFint.mono_measure (Measure.restrict_le_self)
  have key : ∀ m : ℕ, 0 < m → m ≤ n →
      ∫ z in Set.Ioc (0:ℝ≥0) (unifPart T n m) ×ˢ (Set.univ : Set Ω), F z
          ∂(trimMeasure_T (μ := μ) T hBmeas)
        = ∑ k ∈ Finset.range m,
            ∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ (Set.univ : Set Ω),
              F z ∂(trimMeasure_T (μ := μ) T hBmeas) := by
    intro m
    induction m with
    | zero => intro hm; exact absurd hm (Nat.not_lt_zero 0)
    | succ m ih =>
      intro hm hmT
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0
        have h0 : unifPart T n 0 = 0 := by
          unfold unifPart
          norm_num
        rw [Finset.range_one, Finset.sum_singleton, h0]
      · have hmt : unifPart T n m ≤ unifPart T n (m + 1) :=
          unifPart_mono T n (Nat.le_succ m)
        have hunion : (Set.Ioc (0:ℝ≥0) (unifPart T n m) ×ˢ (Set.univ : Set Ω))
            ∪ (Set.Ioc (unifPart T n m) (unifPart T n (m + 1)) ×ˢ (Set.univ : Set Ω))
            = (Set.Ioc (0:ℝ≥0) (unifPart T n (m + 1))) ×ˢ (Set.univ : Set Ω) := by
          rw [← Set.union_prod, Set.Ioc_union_Ioc_eq_Ioc
            (show (0:ℝ≥0) ≤ unifPart T n m from by simp only [unifPart]; positivity) hmt]
        have hdisj : Disjoint
            ((Set.Ioc (0:ℝ≥0) (unifPart T n m)) ×ˢ (Set.univ : Set Ω))
            ((Set.Ioc (unifPart T n m) (unifPart T n (m + 1))) ×ˢ (Set.univ : Set Ω)) :=
          Set.disjoint_left.2 fun a ha hb ↦ by
            have h1 : ((unifPart T n m : ℝ)) < (a.1 : ℝ) := by exact_mod_cast hb.1.1
            have h2 : (a.1 : ℝ) ≤ ((unifPart T n m : ℝ)) := by exact_mod_cast ha.1.2
            linarith
        have hintV : IntegrableOn F
            ((Set.Ioc (unifPart T n m) (unifPart T n (m + 1))) ×ˢ (Set.univ : Set Ω))
            (trimMeasure_T (μ := μ) T hBmeas) := by
          exact hFint.mono_measure (Measure.restrict_le_self)
        calc ∫ z in Set.Ioc (0:ℝ≥0) (unifPart T n (m + 1)) ×ˢ (Set.univ : Set Ω), F z
              ∂(trimMeasure_T (μ := μ) T hBmeas)
            = ∫ z in (Set.Ioc (0:ℝ≥0) (unifPart T n m) ×ˢ (Set.univ : Set Ω))
                ∪ (Set.Ioc (unifPart T n m) (unifPart T n (m + 1)) ×ˢ (Set.univ : Set Ω)),
                F z ∂(trimMeasure_T (μ := μ) T hBmeas) := by rw [hunion]
          _ = ∫ z in Set.Ioc (0:ℝ≥0) (unifPart T n m) ×ˢ (Set.univ : Set Ω), F z
                ∂(trimMeasure_T (μ := μ) T hBmeas)
              + ∫ z in Set.Ioc (unifPart T n m) (unifPart T n (m + 1)) ×ˢ (Set.univ : Set Ω),
                F z ∂(trimMeasure_T (μ := μ) T hBmeas) :=
              setIntegral_union hdisj
                (MeasureTheory.measurableSet_predictable_Ioc_prod (unifPart T n m)
                  (unifPart T n (m + 1)) MeasurableSet.univ)
                (hintOn m (by omega)) hintV
          _ = ∑ k ∈ Finset.range m,
                ∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ (Set.univ : Set Ω),
                  F z ∂(trimMeasure_T (μ := μ) T hBmeas)
              + ∫ z in Set.Ioc (unifPart T n m) (unifPart T n (m + 1)) ×ˢ (Set.univ : Set Ω),
                F z ∂(trimMeasure_T (μ := μ) T hBmeas) := by
              rw [ih hm0 (by omega)]
          _ = ∑ k ∈ Finset.range (m + 1),
                ∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ (Set.univ : Set Ω),
                  F z ∂(trimMeasure_T (μ := μ) T hBmeas) := (Finset.sum_range_succ _ m).symm
  have hkey := key n hn (le_refl n)
  rw [hTn] at hkey
  exact hkey

/-- **Per-cell step identification at CLM level**: the increment over cell `k` of the
uniform partition of the step-approximant CLM process is a.e. the single rectangle
`δ(tₖ)·ΔBₖ`. -/
private theorem stepIncr_stepCLM_ae (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδbdd : ∀ t ω, |δ t ω| ≤ Dd) {n k : ℕ} (hk : k < n) :
    (fun ω ↦ (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (simpleAssembly_T (μ := μ) T hBmeas (stepσ hBmeas hδadap hδbdd T n)) : Ω → ℝ) ω
      - (itoProcessCLM hB T (unifPart T n k) hBmeas
          (simpleAssembly_T (μ := μ) T hBmeas (stepσ hBmeas hδadap hδbdd T n)) : Ω → ℝ) ω)
      =ᵐ[μ] (fun ω ↦ δ (unifPart T n k) ω
          * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) := by
  have hcoe : ∀ t : ℝ≥0,
      (itoProcessCLM hB T t hBmeas
          (simpleAssembly_T (μ := μ) T hBmeas (stepσ hBmeas hδadap hδbdd T n)) : Ω → ℝ)
        =ᵐ[μ] itoSimpleProcess hBmeas (stepσ hBmeas hδadap hδbdd T n).val t := by
    intro t
    rw [itoProcessCLM_simpleAssembly_T hB T t hBmeas (stepσ hBmeas hδadap hδbdd T n)]
    exact (memLp_itoSimpleProcess hB hBmeas (stepσ hBmeas hδadap hδbdd T n).val t).coeFn_toLp
  filter_upwards [hcoe (unifPart T n (k + 1)), hcoe (unifPart T n k)] with ω h2 h3
  show (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
        (simpleAssembly_T (μ := μ) T hBmeas (stepσ hBmeas hδadap hδbdd T n)) : Ω → ℝ) ω
      - (itoProcessCLM hB T (unifPart T n k) hBmeas
        (simpleAssembly_T (μ := μ) T hBmeas (stepσ hBmeas hδadap hδbdd T n)) : Ω → ℝ) ω
    = δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)
  rw [h2, h3, itoSimpleProcess_stepσ_incr hBmeas hδadap hδbdd T hk ω]

omit [IsProbabilityMeasure μ] in
/-- **The per-cell weighted identity** (the stage-4 core): for an `𝓕_{tₖ}`-measurable
weight `w`, the weighted second moment of the single rectangle `δ(tₖ)·ΔBₖ` is the frozen
rectangle energy `𝔼[w·δ(tₖ)²]·(tₖ₊₁ − tₖ)` — the isometry kernel
`integral_adapted_mul_increment_sq` at `χ = w·δ(tₖ)²` (adapted by the Doob–Dynkin bridge
`adaptedAt_of_measurable_natural` and its closure under products). -/
theorem weightedCellSq_step {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    {n k : ℕ} {w : Ω → ℝ}
    (hwm : Measurable[natFiltration hBmeas (unifPart T n k)] w) :
    ∫ ω, w ω * (δ (unifPart T n k) ω
        * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ
      = (∫ ω, w ω * δ (unifPart T n k) ω ^ 2 ∂μ)
        * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
  have hcongr : (fun ω ↦ w ω * (δ (unifPart T n k) ω
        * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2)
      =ᵐ[μ] (fun ω ↦ (w ω * (δ (unifPart T n k) ω * δ (unifPart T n k) ω))
          * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) := by
    filter_upwards [] with ω
    show w ω * (δ (unifPart T n k) ω
        * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 = _
    ring
  have hχ : ItoIsometryAdapted.AdaptedAt B (unifPart T n k)
      (fun ω ↦ w ω * (δ (unifPart T n k) ω * δ (unifPart T n k) ω)) :=
    (adaptedAt_of_measurable_natural hBmeas hwm).mul
      ((adaptedAt_of_measurable_natural hBmeas
        (hδadap (unifPart T n k)).measurable).mul
      (adaptedAt_of_measurable_natural hBmeas
        (hδadap (unifPart T n k)).measurable))
  have hcongr2 : (∫ ω, w ω * δ (unifPart T n k) ω ^ 2 ∂μ)
      = ∫ ω, w ω * (δ (unifPart T n k) ω * δ (unifPart T n k) ω) ∂μ :=
    integral_congr_ae (Eventually.of_forall fun ω ↦ by
      show w ω * δ (unifPart T n k) ω ^ 2 = _
      rw [pow_two])
  rw [integral_congr_ae hcongr, hcongr2]
  exact integral_adapted_mul_increment_sq hB hBmeas (unifPart_mono T n (Nat.le_succ k)) hχ

end StageFourB

/-! #### Stage 4 (headline) — the gap decay, the summed weighted increment isometry,
and the convergence of the quadratic block -/

section StageFourC

open MeasureTheory ProbabilityTheory Filter Topology ItoIntegralProcessGeneral
open ItoIntegralL2 ItoIntegralCLM ItoIntegralRiemannBridge ItoIsometryAdapted
open ItoIntegralProcess QuadraticVariationL2 MathFin
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))

omit hB in
/-- The mean function of a bounded measurable path-continuous family is continuous
(the stage-1 DCT interchange, factored out). -/
private lemma continuous_mean_of_bdd_cont {g : ℝ≥0 → Ω → ℝ}
    (hgmeas : ∀ s, Measurable (g s)) (hgcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ g s ω)
    {C : ℝ} (hgbdd : ∀ s ω, |g s ω| ≤ C) :
    Continuous fun s : ℝ≥0 ↦ ∫ ω, g s ω ∂μ :=
  continuous_iff_continuousAt.mpr fun s₀ ↦
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ : Ω ↦ C)
      (Eventually.of_forall fun s ↦ (hgmeas s).aestronglyMeasurable)
      (Eventually.of_forall fun s ↦ Eventually.of_forall fun ω ↦ by
        simpa [Real.norm_eq_abs] using hgbdd s ω)
      (integrable_const C)
      (Eventually.of_forall fun ω ↦ (hgcont ω).continuousAt)

omit hB in
/-- **The frozen Riemann convergence**: the left-endpoint Riemann sums of the deterministic
mean function of a bounded measurable path-continuous family converge to the time integral
of the means (the deterministic `tendsto_riemann_continuous` applied to the mean function). -/
theorem frozenRiemann_tendsto {g : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}
    (hgmeas : ∀ s, Measurable (g s)) (hgcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ g s ω)
    {C : ℝ} (hgbdd : ∀ s ω, |g s ω| ≤ C) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
        (∫ ω, g (unifPart T n k) ω ∂μ) * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
      atTop (𝓝 (∫ s in Set.Ioc 0 T, (∫ ω, g s ω ∂μ) ∂ItoIntegralL2.timeMeasure)) := by
  have hmeanbdd : ∀ s : ℝ≥0, |∫ ω, g s ω ∂μ| ≤ C := fun s ↦ by
    calc |∫ ω, g s ω ∂μ| ≤ ∫ ω, |g s ω| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ ω, C ∂μ := integral_mono_of_nonneg
          (Eventually.of_forall fun ω ↦ abs_nonneg _)
          (integrable_const C)
          (Eventually.of_forall fun ω ↦ by simpa [Real.norm_eq_abs] using hgbdd s ω)
      _ = C := by rw [integral_const]; simp
  exact tendsto_riemann_continuous (continuous_mean_of_bdd_cont hgmeas hgcont hgbdd) T
    (fun s _ ↦ hmeanbdd s)

variable {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
  (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
  (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
  (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
  {M : ℝ≥0 → Ω → ℝ}
  (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
  (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
    (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))

include hB hBmeas hδadap hδcont hδbdd hMadap hMeq

/-- The energy of the true increment: `𝔼[(M_v − M_u)²] ≤ D_δ²·(v−u)` for `u ≤ v ≤ T`
(`incrementEnergy` plus the pointwise `δ`-bound on the mean function). -/
private theorem trueIncr_sq_le {u v : ℝ≥0} (huv : u ≤ v) (hvT : v ≤ T) :
    ∫ ω, (M v ω - M u ω) ^ 2 ∂μ ≤ Dd ^ 2 * ((v : ℝ) - u) := by
  rw [incrementEnergy hB hBmeas hδadap hδcont hδbdd hMadap hMeq huv hvT]
  have hgmeas : ∀ s : ℝ≥0, Measurable (fun ω ↦ δ s ω * δ s ω) :=
    fun s ↦ (((hδadap s).measurable.mul (hδadap s).measurable).mono
      ((natFiltration hBmeas).le s) le_rfl)
  have hgcont : ∀ ω : Ω, Continuous fun s : ℝ≥0 ↦ δ s ω * δ s ω :=
    fun ω ↦ (hδcont ω).mul (hδcont ω)
  have hDsq2 : |Dd| * |Dd| = Dd * Dd := by
    rcases le_total 0 Dd with h | h
    · rw [abs_of_nonneg h]
    · rcases eq_or_lt_of_le h with rfl | h'
      · simp
      · rw [abs_of_neg h']
        ring
  have hmeanbdd : ∀ s : ℝ≥0, |∫ ω, δ s ω * δ s ω ∂μ| ≤ Dd * Dd := by
    intro s
    calc |∫ ω, δ s ω * δ s ω ∂μ| ≤ ∫ ω, |δ s ω * δ s ω| ∂μ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ ω, (|Dd| * |Dd|) ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ abs_nonneg _)
            (integrable_const (μ := μ) (|Dd| * |Dd|)) ?_
          filter_upwards [] with ω
          show |δ s ω * δ s ω| ≤ |Dd| * |Dd|
          rw [abs_mul]
          calc |δ s ω| * |δ s ω| ≤ |Dd| * |δ s ω| :=
                mul_le_mul_of_nonneg_right
                  (le_trans (hδbdd s ω) (le_abs_self Dd)) (abs_nonneg _)
            _ ≤ |Dd| * |Dd| := mul_le_mul_of_nonneg_left
                  (le_trans (hδbdd s ω) (le_abs_self Dd)) (abs_nonneg _)
      _ = Dd * Dd := by
          rw [integral_const, hDsq2]
          simp
  have hmeanmeas : Measurable (fun s : ℝ≥0 ↦ ∫ ω, δ s ω * δ s ω ∂μ) :=
    (continuous_mean_of_bdd_cont hgmeas hgcont (fun s ω ↦ by
      show |δ s ω * δ s ω| ≤ |Dd| * |Dd|
      rw [abs_mul]
      calc |δ s ω| * |δ s ω| ≤ |Dd| * |δ s ω| :=
            mul_le_mul_of_nonneg_right (le_trans (hδbdd s ω) (le_abs_self Dd))
              (abs_nonneg _)
        _ ≤ |Dd| * |Dd| := mul_le_mul_of_nonneg_left
            (le_trans (hδbdd s ω) (le_abs_self Dd)) (abs_nonneg _))).measurable
  haveI : IsFiniteMeasure
      (ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      ItoIntegralL2.timeMeasure_Ioc]
    exact ENNReal.ofReal_lt_top
  have hconst : ∫ s in Set.Ioc u v, (|Dd| * |Dd|) ∂ItoIntegralL2.timeMeasure
      = (|Dd| * |Dd|) * ((v : ℝ) - u) := by
    rw [MeasureTheory.setIntegral_const, measureReal_def,
      ItoIntegralL2.timeMeasure_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (NNReal.coe_le_coe.mpr huv))]
    ring
  refine le_trans (integral_mono_of_nonneg
    (Eventually.of_forall fun s ↦ integral_nonneg (μ := μ)
      (f := fun ω ↦ δ s ω * δ s ω)
      (fun ω ↦ by
        show (0:ℝ) ≤ δ s ω * δ s ω
        rw [← pow_two]
        exact sq_nonneg (δ s ω)))
    (integrable_const (μ := ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v))
      (|Dd| * |Dd|))
    (Eventually.of_forall fun s ↦ by
      show (fun s : ℝ≥0 ↦ ∫ ω, δ s ω * δ s ω ∂μ) s
        ≤ (fun _ : ℝ≥0 ↦ |Dd| * |Dd|) s
      exact le_trans (le_of_eq rfl)
        (le_trans (le_abs_self (∫ ω, δ s ω * δ s ω ∂μ))
          (le_trans (hmeanbdd s) (le_of_eq hDsq2.symm))))) ?_
  calc ∫ s in Set.Ioc u v, (|Dd| * |Dd|) ∂ItoIntegralL2.timeMeasure
      = (|Dd| * |Dd|) * ((v : ℝ) - u) := hconst
    _ ≤ Dd ^ 2 * ((v : ℝ) - u) := by
        show |Dd| * |Dd| * ((v : ℝ) - u) ≤ Dd ^ 2 * ((v : ℝ) - u)
        rw [sq Dd, hDsq2]

set_option maxHeartbeats 1600000 in
omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- **The convergence of the quadratic block** (the summed weighted increment isometry,
conditional on a gap bound): if for some null sequence `r` the weighted second-moment sum
along the uniform partition differs from the frozen rectangle sum by at most
`2·|C_w|·|D_δ|·√T·r n` for `n > 0` (`gapSum_le` supplies one, with
`r n = ‖φ − δⁿ‖_{L²(trim)}`), then the sum converges to the quadratic block
`∫₀ᵀ 𝔼[w·δ²] ds`. -/
theorem quadraticSqSum_tendsto (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
    {M : ℝ≥0 → Ω → ℝ}
    (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
      (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))
    {w : ℝ≥0 → Ω → ℝ} {Cw : ℝ}
    (hwadap : ∀ t, Measurable[natFiltration hBmeas t] (w t))
    (hwcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ w s ω)
    (hwbdd : ∀ s ω, |w s ω| ≤ Cw)
    (hgap : ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ ∀ n : ℕ, 0 < n →
      |∑ k ∈ Finset.range n,
          ∫ ω, w (unifPart T n k) ω
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
        - ∑ k ∈ Finset.range n,
            (∫ ω, w (unifPart T n k) ω * δ (unifPart T n k) ω ^ 2 ∂μ)
              * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)|
        ≤ 2 * |Cw| * |Dd| * Real.sqrt (T : ℝ) * r n) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
        ∫ ω, w (unifPart T n k) ω
          * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)
      atTop (𝓝 (∫ s in Set.Ioc 0 T,
          (∫ ω, w s ω * (δ s ω * δ s ω) ∂μ) ∂ItoIntegralL2.timeMeasure)) := by
  have hgmeas : ∀ s, Measurable (fun ω ↦ w s ω * (δ s ω * δ s ω)) := by
    intro s
    exact (((hwadap s).mono ((natFiltration hBmeas).le s) le_rfl).mul
      (((hδadap s).mono ((natFiltration hBmeas).le s)).measurable.mul
        ((hδadap s).mono ((natFiltration hBmeas).le s)).measurable))
  have hgcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ w s ω * (δ s ω * δ s ω) :=
    fun ω ↦ (hwcont ω).mul ((hδcont ω).mul (hδcont ω))
  have hgbdd : ∀ s ω, |w s ω * (δ s ω * δ s ω)| ≤ |Cw| * (Dd * Dd) := by
    intro s ω
    have hDd : |Dd| * |Dd| = Dd * Dd := by
      rcases le_total 0 Dd with h | h
      · rw [abs_of_nonneg h]
      · rcases eq_or_lt_of_le h with rfl | h'
        · simp
        · rw [abs_of_neg h']
          ring
    have hd2 : |δ s ω * δ s ω| ≤ |Dd| * |Dd| := by
      rw [abs_mul]
      exact mul_le_mul (le_trans (hδbdd s ω) (le_abs_self Dd))
        (le_trans (hδbdd s ω) (le_abs_self Dd)) (abs_nonneg _)
        (abs_nonneg Dd)
    show |w s ω * (δ s ω * δ s ω)| ≤ |Cw| * (Dd * Dd)
    rw [abs_mul]
    exact (mul_le_mul (le_trans (hwbdd s ω) (le_abs_self Cw)) hd2 (abs_nonneg _)
      (abs_nonneg _)).trans (by rw [hDd])
  -- the frozen sums converge to the quadratic block
  have hF := frozenRiemann_tendsto (μ := μ) (T := T) hgmeas hgcont hgbdd
  have hFeq : ∀ n : ℕ,
      (∑ k ∈ Finset.range n,
          (∫ ω, w (unifPart T n k) ω * δ (unifPart T n k) ω ^ 2 ∂μ)
            * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
        = ∑ k ∈ Finset.range n,
            (∫ ω, w (unifPart T n k) ω * (δ (unifPart T n k) ω * δ (unifPart T n k) ω) ∂μ)
              * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
    intro n
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ω ↦ by show _ = _; ring)
  obtain ⟨r, hr0, hgap'⟩ := hgap
  -- the gap dies along the null sequence r
  have hSFabs : Tendsto (fun n : ℕ ↦ |(∑ k ∈ Finset.range n,
      ∫ ω, w (unifPart T n k) ω
        * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)
    - ∑ k ∈ Finset.range n,
        (∫ ω, w (unifPart T n k) ω
          * (δ (unifPart T n k) ω * δ (unifPart T n k) ω) ∂μ)
          * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)|) atTop (𝓝 0) := by
    refine squeeze_zero' (g := fun n : ℕ ↦ 2 * |Cw| * |Dd| * Real.sqrt (T : ℝ) * r n)
      (Eventually.of_forall fun n ↦ abs_nonneg _) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have h := hgap' n hn
      rw [hFeq n] at h
      exact h
    · simpa using (tendsto_const_nhds
        (x := 2 * |Cw| * |Dd| * Real.sqrt (T : ℝ))).mul hr0
  have hSF : Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.range n,
        ∫ ω, w (unifPart T n k) ω
          * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)
      - ∑ k ∈ Finset.range n,
          (∫ ω, w (unifPart T n k) ω
            * (δ (unifPart T n k) ω * δ (unifPart T n k) ω) ∂μ)
            * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) atTop (𝓝 0) := by
    refine tendsto_iff_dist_tendsto_zero.mpr ?_
    refine Filter.Tendsto.congr' (Eventually.of_forall fun n ↦ ?_) hSFabs
    show |(∑ k ∈ Finset.range n,
          ∫ ω, w (unifPart T n k) ω
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)
        - ∑ k ∈ Finset.range n,
            (∫ ω, w (unifPart T n k) ω
              * (δ (unifPart T n k) ω * δ (unifPart T n k) ω) ∂μ)
              * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)|
      = dist ((∑ k ∈ Finset.range n,
          ∫ ω, w (unifPart T n k) ω
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)
        - ∑ k ∈ Finset.range n,
            (∫ ω, w (unifPart T n k) ω
              * (δ (unifPart T n k) ω * δ (unifPart T n k) ω) ∂μ)
              * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) 0
    rw [Real.dist_eq, sub_zero]
  have key := hSF.add hF
  rw [zero_add] at key
  exact key.congr' (Eventually.of_forall fun n ↦ by
    show (∑ k ∈ Finset.range n,
          ∫ ω, w (unifPart T n k) ω
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
        - ∑ k ∈ Finset.range n,
            (∫ ω, w (unifPart T n k) ω
              * (δ (unifPart T n k) ω * δ (unifPart T n k) ω) ∂μ)
              * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
      + ∑ k ∈ Finset.range n,
          (∫ ω, w (unifPart T n k) ω
            * (δ (unifPart T n k) ω * δ (unifPart T n k) ω) ∂μ)
            * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)
      = _
    ring)

end StageFourC

/-! #### Stage 5a — the gap decay, unconditional

The per-cell Cauchy–Schwarz pairing of the error increment `δεₖ = ΔMₖ − δ(tₖ)·ΔBₖ`
against the cell energy. The error increment is the band increment of the CLM process of
the integrand error `ψₙ = φ − δⁿ` (linearity of the CLM map + the per-cell step
identification), so its band energy is `∫_{bandₖ} ψₙ²` (`clm_band_energy`) and the summed
band energies telescope to `‖ψₙ‖²_{L²(trim)}` (`uniform_band_split` + the `Lp` norm).
The pairing gives exactly the constant `2·|C_w|·|D_δ|·√T` of `quadraticSqSum_tendsto`'s
`hgap`, and `deltaStepLp_tendsto` makes the bound a null sequence. -/

section StageFiveA

open MeasureTheory ProbabilityTheory Filter Topology ItoIntegralProcessGeneral
open ItoIntegralL2 ItoIntegralCLM ItoIntegralRiemannBridge ItoIsometryAdapted
open ItoIntegralProcess QuadraticVariationL2 MathFin
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
  {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
  (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
  (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
  (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
  {M : ℝ≥0 → Ω → ℝ}
  (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
  (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
    (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))

include hB hBmeas hδadap hδcont hδbdd hMadap hMeq

omit hδadap hδcont hδbdd hMadap hMeq in
/-- Coe-linearity of the CLM process in the integrand class (the a.e. form). -/
private theorem clm_coe_sub_ae (T t : ℝ≥0)
    (φ₁ φ₂ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ((itoProcessCLM hB T t hBmeas (φ₁ - φ₂) : Lp ℝ 2 μ) : Ω → ℝ)
      =ᵐ[μ] (fun ω ↦ (itoProcessCLM hB T t hBmeas φ₁ : Ω → ℝ) ω
        - (itoProcessCLM hB T t hBmeas φ₂ : Ω → ℝ) ω) := by
  rw [map_sub]
  exact Lp.coeFn_sub _ _

omit hMadap in
/-- The per-cell error increment `δεₖ := ΔMₖ − δ(tₖ)·ΔBₖ` is a.e. the band increment of the
CLM process of the integrand error `φ − δⁿ`. -/
private theorem errorIncr_ae {n k : ℕ} (hk : k < n) :
    (fun ω ↦ M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
        - δ (unifPart T n k) ω
          * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))
      =ᵐ[μ] (fun ω ↦ (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              (processToLp T hBmeas hδadap hδcont hδbdd
                - deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω
        - (itoProcessCLM hB T (unifPart T n k) hBmeas
              (processToLp T hBmeas hδadap hδcont hδbdd
                - deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω) := by
  have h1 := hMeq (unifPart T n (k + 1))
  have h0 := hMeq (unifPart T n k)
  have hsub1 := clm_coe_sub_ae (μ := μ) hB hBmeas T (unifPart T n (k + 1))
    (processToLp T hBmeas hδadap hδcont hδbdd) (deltaStepLp hBmeas hδadap hδbdd n)
  have hsub0 := clm_coe_sub_ae (μ := μ) hB hBmeas T (unifPart T n k)
    (processToLp T hBmeas hδadap hδcont hδbdd) (deltaStepLp hBmeas hδadap hδbdd n)
  have hstep : (fun ω ↦ (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω
      - (itoProcessCLM hB T (unifPart T n k) hBmeas
        (deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω)
      =ᵐ[μ] (fun ω ↦ δ (unifPart T n k) ω
          * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) :=
    stepIncr_stepCLM_ae (μ := μ) (B := B) (hB := hB) (hBmeas := hBmeas)
    (hδadap := hδadap) (hδbdd := hδbdd) (T := T) (n := n) (k := k) hk
  filter_upwards [h1, h0, hsub1, hsub0, hstep] with ω h1 h0 hsub1 hsub0 hstep
  calc M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
        - δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)
      = (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ) ω
        - (itoProcessCLM hB T (unifPart T n k) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ) ω
        - ((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω
          - (itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω) := by
        rw [h1, h0, ← hstep]
    _ = ((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ) ω
          - (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω)
        - ((itoProcessCLM hB T (unifPart T n k) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ) ω
          - (itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω) := by ring
    _ = (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω
        - (itoProcessCLM hB T (unifPart T n k) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω := by
        rw [hsub1, hsub0]

set_option linter.unusedSectionVars false in
omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- Generic weighted-square transfer: if `f =ᵐ g`, `g²` is integrable with energy `E`,
and `|w| ≤ C`, then `𝔼[(w·f)²] ≤ C²·E`. -/
private theorem weighted_sq_le_of_congr {f g w : Ω → ℝ} {C E : ℝ}
    (hwb : ∀ ω, |w ω| ≤ C) (hcongr : f =ᵐ[μ] g)
    (hint2 : Integrable (fun ω ↦ g ω ^ 2) μ) (hE : ∫ ω, g ω ^ 2 ∂μ = E) :
    ∫ ω, (w ω * f ω) ^ 2 ∂μ ≤ C ^ 2 * E := by
  have hw : ∀ ω : Ω, w ω ^ 2 ≤ C ^ 2 := fun ω ↦ by
    have h := mul_self_le_mul_self (abs_nonneg (w ω)) (hwb ω)
    have e1 : |w ω| * |w ω| = w ω ^ 2 := by
      rw [← pow_two, sq_abs]
    have e2 : C * C = C ^ 2 := (sq C).symm
    rwa [e1, e2] at h
  have hdom : Integrable (fun ω ↦ (C * g ω) ^ 2) μ :=
    (hint2.const_mul (C ^ 2)).congr
      (Eventually.of_forall fun ω ↦ by ring)
  calc ∫ ω, (w ω * f ω) ^ 2 ∂μ
      = ∫ ω, (w ω * g ω) ^ 2 ∂μ := integral_congr_ae
          (by filter_upwards [hcongr] with ω hω; rw [hω])
    _ ≤ ∫ ω, (C * g ω) ^ 2 ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ sq_nonneg _)
          hdom (Eventually.of_forall fun ω ↦ ?_)
        show (w ω * g ω) ^ 2 ≤ (C * g ω) ^ 2
        have h1 : (w ω * g ω) ^ 2 = w ω ^ 2 * g ω ^ 2 := by ring
        have h2 : (C * g ω) ^ 2 = C ^ 2 * g ω ^ 2 := by ring
        rw [h1, h2]
        exact mul_le_mul_of_nonneg_right (hw ω) (sq_nonneg _)
    _ = C ^ 2 * E := by
        rw [integral_congr_ae (Eventually.of_forall fun ω ↦ by
          show (C * g ω) ^ 2 = C ^ 2 * g ω ^ 2; ring), integral_const_mul, hE]

include hB hMadap hMeq in
/-- **Weighted error energy**: the second moment of `w·δεₖ` is at most `C_w²` cell-band
energies of the integrand error (`|w| ≤ C_w` pointwise). -/
private theorem weightedErrorIncr_sq_le {n k : ℕ} (hk : k < n) {w : Ω → ℝ} {Cw : ℝ}
    (hwm : Measurable[natFiltration hBmeas (unifPart T n k)] w)
    (hwb : ∀ ω, |w ω| ≤ Cw) :
    ∫ ω, (w ω * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
        - δ (unifPart T n k) ω
          * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))) ^ 2 ∂μ
      ≤ Cw ^ 2 * ∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ
            (Set.univ : Set Ω),
          ((processToLp T hBmeas hδadap hδcont hδbdd
              - deltaStepLp hBmeas hδadap hδbdd n :
                Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas) := by
  -- the CLM error increment and its square integrability
  have hDmem : MemLp
      (fun ω ↦ (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd
              - deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω
        - (itoProcessCLM hB T (unifPart T n k) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω) 2 μ :=
    (Lp.memLp (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
      (processToLp T hBmeas hδadap hδcont hδbdd
        - deltaStepLp hBmeas hδadap hδbdd n))).sub
      (Lp.memLp (itoProcessCLM hB T (unifPart T n k) hBmeas
        (processToLp T hBmeas hδadap hδcont hδbdd
          - deltaStepLp hBmeas hδadap hδbdd n)))
  -- the energy of the CLM error increment is the band energy
  have hbandE : ∫ ω, ((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
        (processToLp T hBmeas hδadap hδcont hδbdd
          - deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω
      - (itoProcessCLM hB T (unifPart T n k) hBmeas
        (processToLp T hBmeas hδadap hδcont hδbdd
          - deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω) ^ 2 ∂μ
      = ∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ (Set.univ : Set Ω),
          ((processToLp T hBmeas hδadap hδcont hδbdd
              - deltaStepLp hBmeas hδadap hδbdd n :
                Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas) :=
    (clm_band_energy hB hBmeas T
      (processToLp T hBmeas hδadap hδcont hδbdd - deltaStepLp hBmeas hδadap hδbdd n)
      (unifPart_mono T n (Nat.le_succ k))
      (unifPart_le_T hk))
  exact weighted_sq_le_of_congr hwb
    (errorIncr_ae hB hBmeas hδadap hδcont hδbdd hMeq hk)
    hDmem.integrable_sq hbandE

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- The real `L²` triangle inequality at the integral level: `‖a + b‖₂ ≤ ‖a‖₂ + ‖b‖₂`. -/
private theorem sqrtIntegral_sq_add_le {a b : Ω → ℝ}
    (ham : MemLp a 2 μ) (hbm : MemLp b 2 μ) :
    Real.sqrt (∫ ω, (a ω + b ω) ^ 2 ∂μ)
      ≤ Real.sqrt (∫ ω, a ω ^ 2 ∂μ) + Real.sqrt (∫ ω, b ω ^ 2 ∂μ) := by
  have ha2 := ham.integrable_sq
  have hb2 := hbm.integrable_sq
  have hab := ham.integrable_mul hbm
  have hexp : ∫ ω, (a ω + b ω) ^ 2 ∂μ
      = ∫ ω, a ω ^ 2 ∂μ + 2 * ∫ ω, a ω * b ω ∂μ + ∫ ω, b ω ^ 2 ∂μ :=
    integral_sq_add ha2 hb2 hab
  have hcs : ∫ ω, a ω * b ω ∂μ
      ≤ Real.sqrt (∫ ω, a ω ^ 2 ∂μ) * Real.sqrt (∫ ω, b ω ^ 2 ∂μ) := by
    refine le_trans (integral_mono hab hab.abs (fun ω ↦ le_abs_self _)) ?_
    exact integral_abs_mul_le_L2L2 ham hbm
  calc Real.sqrt (∫ ω, (a ω + b ω) ^ 2 ∂μ)
      = Real.sqrt (∫ ω, a ω ^ 2 ∂μ + 2 * ∫ ω, a ω * b ω ∂μ + ∫ ω, b ω ^ 2 ∂μ) := by
        rw [hexp]
    _ ≤ Real.sqrt ((Real.sqrt (∫ ω, a ω ^ 2 ∂μ) + Real.sqrt (∫ ω, b ω ^ 2 ∂μ)) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        have hA : Real.sqrt (∫ ω, a ω ^ 2 ∂μ) ^ 2 = ∫ ω, a ω ^ 2 ∂μ :=
          Real.sq_sqrt (integral_nonneg fun ω ↦ sq_nonneg _)
        have hB : Real.sqrt (∫ ω, b ω ^ 2 ∂μ) ^ 2 = ∫ ω, b ω ^ 2 ∂μ :=
          Real.sq_sqrt (integral_nonneg fun ω ↦ sq_nonneg _)
        have hrw : (Real.sqrt (∫ ω, a ω ^ 2 ∂μ) + Real.sqrt (∫ ω, b ω ^ 2 ∂μ)) ^ 2
            = Real.sqrt (∫ ω, a ω ^ 2 ∂μ) ^ 2
              + 2 * (Real.sqrt (∫ ω, a ω ^ 2 ∂μ) * Real.sqrt (∫ ω, b ω ^ 2 ∂μ))
              + Real.sqrt (∫ ω, b ω ^ 2 ∂μ) ^ 2 := by ring
        rw [hrw, hA, hB]
        linarith [hcs]
    _ = Real.sqrt (∫ ω, a ω ^ 2 ∂μ) + Real.sqrt (∫ ω, b ω ^ 2 ∂μ) :=
        Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- **Per-cell gap bound**: the absolute difference over one cell between the expectations
of the weighted true-increment square and of the weighted rectangle square — the
Cauchy–Schwarz pairing of the
error increment `δεₖ` against the cell energy `ΔMₖ + δ(tₖ)ΔBₖ`, each factor bounded by the
weighted error energy (`weightedErrorIncr_sq_le`) and the `2·|D_δ|·√cell` cell energy
(`trueIncr_sq_le` + the rectangle second moment). -/
private theorem cellGap_le {n k : ℕ} (hk : k < n) {w : Ω → ℝ} {Cw : ℝ}
    (hwm : Measurable[natFiltration hBmeas (unifPart T n k)] w)
    (hwb : ∀ ω, |w ω| ≤ Cw) :
    |∫ ω, w ω * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
        - ∫ ω, w ω * (δ (unifPart T n k) ω
            * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ|
      ≤ 2 * |Cw| * |Dd| * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k)
        * Real.sqrt (∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ
            (Set.univ : Set Ω),
          ((processToLp T hBmeas hδadap hδcont hδbdd
              - deltaStepLp hBmeas hδadap hδbdd n :
                Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas)) := by
  have huv : unifPart T n k ≤ unifPart T n (k + 1) := unifPart_mono T n (Nat.le_succ k)
  have hδm : Measurable (δ (unifPart T n k)) :=
    ((hδadap (unifPart T n k)).measurable.mono ((natFiltration hBmeas).le _) le_rfl)
  have hdBm : Measurable (fun ω ↦ B (unifPart T n (k + 1)) ω
      - B (unifPart T n k) ω) := (hBmeas _).sub (hBmeas _)
  have hwm' : Measurable w := hwm.mono ((natFiltration hBmeas).le _) le_rfl
  have hsmeas : Measurable (fun ω ↦ δ (unifPart T n k) ω
      * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) := hδm.mul hdBm
  have hMsub : MemLp (fun ω ↦ M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) 2 μ :=
    (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq (unifPart T n (k + 1))).sub
      (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq (unifPart T n k))
  have hMsub2 : Integrable (fun ω ↦ (M (unifPart T n (k + 1)) ω
      - M (unifPart T n k) ω) ^ 2) μ := hMsub.integrable_sq
  have hdB : MemLp (fun ω ↦ B (unifPart T n (k + 1)) ω
      - B (unifPart T n k) ω) 2 μ := hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two
  -- the rectangle increment `s = δ(tₖ)·ΔBₖ` is `L²`
  have hs : MemLp (fun ω ↦ δ (unifPart T n k) ω
      * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) 2 μ :=
    MemLp.mono' (hdB.const_mul (|Dd|)).abs
      hsmeas.aestronglyMeasurable
      (ae_of_all _ fun ω ↦ by
        show ‖δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)‖
          ≤ |(|Dd| * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))|
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (abs_nonneg Dd)]
        exact mul_le_mul_of_nonneg_right (le_trans (hδbdd (unifPart T n k) ω)
          (le_abs_self Dd)) (abs_nonneg _))
  -- measurability of the true increment
  have hM1m : Measurable (M (unifPart T n (k + 1))) :=
    ((hMadap (unifPart T n (k + 1))).measurable.mono ((natFiltration hBmeas).le _) le_rfl)
  have hM0m : Measurable (M (unifPart T n k)) :=
    ((hMadap (unifPart T n k)).measurable.mono ((natFiltration hBmeas).le _) le_rfl)
  have hMsubm : Measurable (fun ω ↦ M (unifPart T n (k + 1)) ω
      - M (unifPart T n k) ω) := hM1m.sub hM0m
  -- integrability of the two weighted terms
  have hwM2 : Integrable (fun ω ↦ w ω * (M (unifPart T n (k + 1)) ω
      - M (unifPart T n k) ω) ^ 2) μ := by
    refine Integrable.mono' (hMsub2.const_mul Cw)
      (hwm'.mul (hMsubm.pow_const 2)).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ by
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (sq_nonneg (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω))]
        exact mul_le_mul_of_nonneg_right (hwb ω) (sq_nonneg _))
  have hws2 : Integrable (fun ω ↦ w ω * (δ (unifPart T n k) ω
      * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2) μ := by
    refine Integrable.mono' ((hdB.integrable_sq).const_mul (Cw * Dd ^ 2))
      (hwm'.mul (hsmeas.pow_const 2)).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ by
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_mul]
        have hδ2 : |δ (unifPart T n k) ω| ≤ |Dd| :=
          le_trans (hδbdd (unifPart T n k) ω) (le_abs_self Dd)
        have hAB : |δ (unifPart T n k) ω| * |B (unifPart T n (k + 1)) ω
            - B (unifPart T n k) ω| ≤ |Dd| * |B (unifPart T n (k + 1)) ω
            - B (unifPart T n k) ω| :=
          mul_le_mul_of_nonneg_right hδ2 (abs_nonneg _)
        have h2 := sq_le_sq' (by
          have hB0 := mul_nonneg (abs_nonneg (|Dd|))
            (abs_nonneg (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))
          have hA0 := mul_nonneg (abs_nonneg (δ (unifPart T n k) ω))
            (abs_nonneg (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))
          linarith) hAB
        have h3 : (|Dd| * |B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω|) ^ 2
            = Dd ^ 2 * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2 := by
          rw [mul_pow, sq_abs, sq_abs]
        calc |w ω| * (|δ (unifPart T n k) ω| * |B (unifPart T n (k + 1)) ω
                - B (unifPart T n k) ω|) ^ 2
            ≤ |w ω| * ((|Dd| * |B (unifPart T n (k + 1)) ω
              - B (unifPart T n k) ω|) ^ 2) :=
              mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
          _ ≤ Cw * ((|Dd| * |B (unifPart T n (k + 1)) ω
              - B (unifPart T n k) ω|) ^ 2) :=
              mul_le_mul_of_nonneg_right (hwb ω) (sq_nonneg _)
          _ = Cw * Dd ^ 2 * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2 := by
              rw [h3]; ring)
  -- the square identity and the integral form of the gap
  have key : ∫ ω, w ω * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
        - ∫ ω, w ω * (δ (unifPart T n k) ω
            * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ
      = ∫ ω, w ω * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
            - δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))
          * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
            + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ∂μ := by
    rw [← integral_sub hwM2 hws2]
    exact integral_congr_ae (Eventually.of_forall fun ω ↦ by ring)
  -- the Cauchy–Schwarz pairing
  have hDmem : MemLp (fun ω ↦ (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
        (processToLp T hBmeas hδadap hδcont hδbdd
          - deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω
      - (itoProcessCLM hB T (unifPart T n k) hBmeas
        (processToLp T hBmeas hδadap hδcont hδbdd
          - deltaStepLp hBmeas hδadap hδbdd n) : Ω → ℝ) ω) 2 μ :=
    (Lp.memLp (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
      (processToLp T hBmeas hδadap hδcont hδbdd
        - deltaStepLp hBmeas hδadap hδbdd n))).sub
      (Lp.memLp (itoProcessCLM hB T (unifPart T n k) hBmeas
        (processToLp T hBmeas hδadap hδcont hδbdd
          - deltaStepLp hBmeas hδadap hδbdd n)))
  have haede := errorIncr_ae hB hBmeas hδadap hδcont hδbdd hMeq hk
  have hδεsm : AEStronglyMeasurable (fun ω ↦ M (unifPart T n (k + 1)) ω
      - M (unifPart T n k) ω
      - δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) μ :=
    AEStronglyMeasurable.congr hDmem.1 haede.symm
  have hpair : ∫ ω, |w ω * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
          - δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)))
        * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
          + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))| ∂μ
      ≤ Real.sqrt (∫ ω, (w ω * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
            - δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)))) ^ 2 ∂μ)
        * Real.sqrt (∫ ω, ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
          + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ) :=
    integral_abs_mul_le_L2L2
      (MemLp.mono' ((hDmem.abs).const_mul (|Cw|))
        (hwm'.aestronglyMeasurable.mul hδεsm)
        (by
          filter_upwards [haede] with ω hω
          rw [Real.norm_eq_abs, abs_mul, hω]
          exact mul_le_mul_of_nonneg_right (le_trans (hwb ω) (le_abs_self Cw))
            (abs_nonneg _)))
      (hMsub.add hs)
  -- the two energy factors
  have hwde := weightedErrorIncr_sq_le hB hBmeas hδadap hδcont hδbdd hMadap hMeq hk hwm hwb
  have htri : Real.sqrt (∫ ω, ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
        + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ)
      ≤ Real.sqrt (∫ ω, (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)
        + Real.sqrt (∫ ω, (δ (unifPart T n k) ω
          * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ) :=
    sqrtIntegral_sq_add_le hMsub hs
  have hM2le := trueIncr_sq_le hB hBmeas hδadap hδcont hδbdd hMadap hMeq huv
    (unifPart_le_T hk)
  have hs2le : ∫ ω, (δ (unifPart T n k) ω
      * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ
      ≤ Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
    have hdom : Integrable (fun ω ↦ Dd ^ 2
        * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) μ :=
      (hdB.integrable_sq.const_mul (Dd ^ 2)).congr
        (Eventually.of_forall fun ω ↦ by ring)
    refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ sq_nonneg _)
      hdom (ae_of_all _ fun ω ↦ ?_)) ?_
    · show (δ (unifPart T n k) ω
        * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ≤ _
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right
        ((sq_le_sq).mpr (le_trans (hδbdd (unifPart T n k) ω) (le_abs_self Dd))) (sq_nonneg _)
    · rw [integral_const_mul]
      have hΔ : ∫ ω, (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2 ∂μ
          = ((unifPart T n (k + 1) : ℝ) - unifPart T n k) :=
        integral_increment_sq hB (unifPart_mono T n (Nat.le_succ k))
      rw [hΔ]
  -- the two sqrt bounds
  have hsqrtM : Real.sqrt (∫ ω, (M (unifPart T n (k + 1)) ω
      - M (unifPart T n k) ω) ^ 2 ∂μ) ≤ |Dd| * Real.sqrt ((unifPart T n (k + 1) : ℝ)
      - unifPart T n k) := by
    refine le_trans (Real.sqrt_le_sqrt hM2le) ?_
    rw [Real.sqrt_mul (sq_nonneg Dd), Real.sqrt_sq_eq_abs]
  have hsqrts : Real.sqrt (∫ ω, (δ (unifPart T n k) ω
      * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ)
      ≤ |Dd| * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
    refine le_trans (Real.sqrt_le_sqrt hs2le) ?_
    rw [Real.sqrt_mul (sq_nonneg Dd), Real.sqrt_sq_eq_abs]
  have hsqrttri : Real.sqrt (∫ ω, ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
        + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ)
      ≤ 2 * |Dd| * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
    have h1 := htri
    have h2 := hsqrtM
    have h3 := hsqrts
    nlinarith [Real.sqrt_nonneg (∫ ω, (M (unifPart T n (k + 1)) ω
      - M (unifPart T n k) ω) ^ 2 ∂μ), Real.sqrt_nonneg (∫ ω, (δ (unifPart T n k) ω
      * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ)]
  -- assembly
  calc |∫ ω, w ω * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
          - ∫ ω, w ω * (δ (unifPart T n k) ω
              * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ|
      = |∫ ω, w ω * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
              - δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)))
            * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
              + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ∂μ| :=
        by rw [key]
    _ ≤ ∫ ω, |w ω * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
              - δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)))
            * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
              + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ Real.sqrt (∫ ω, (w ω * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
              - δ (unifPart T n k) ω
                * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)))) ^ 2 ∂μ)
          * Real.sqrt (∫ ω, ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
            + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ) :=
        hpair
    _ ≤ (|Cw| * Real.sqrt (∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ
              (Set.univ : Set Ω),
            ((processToLp T hBmeas hδadap hδcont hδbdd
                - deltaStepLp hBmeas hδadap hδbdd n :
                  Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
            ∂(trimMeasure_T (μ := μ) T hBmeas)))
          * Real.sqrt (∫ ω, ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
            + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ) :=
        mul_le_mul_of_nonneg_right
          (by
            calc Real.sqrt (∫ ω, (w ω * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
                      - δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω
                        - B (unifPart T n k) ω)))) ^ 2 ∂μ)
                ≤ Real.sqrt (Cw ^ 2 * ∫ z in Set.Ioc (unifPart T n k)
                    (unifPart T n (k + 1)) ×ˢ (Set.univ : Set Ω),
                  ((processToLp T hBmeas hδadap hδcont hδbdd
                      - deltaStepLp hBmeas hδadap hδbdd n :
                        Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
                  ∂(trimMeasure_T (μ := μ) T hBmeas)) := Real.sqrt_le_sqrt hwde
              _ = |Cw| * Real.sqrt (∫ z in Set.Ioc (unifPart T n k)
                    (unifPart T n (k + 1)) ×ˢ (Set.univ : Set Ω),
                  ((processToLp T hBmeas hδadap hδcont hδbdd
                      - deltaStepLp hBmeas hδadap hδbdd n :
                        Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
                  ∂(trimMeasure_T (μ := μ) T hBmeas)) := by
                  rw [Real.sqrt_mul (sq_nonneg Cw), Real.sqrt_sq_eq_abs])
          (Real.sqrt_nonneg _)
    _ ≤ (|Cw| * Real.sqrt (∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ
              (Set.univ : Set Ω),
            ((processToLp T hBmeas hδadap hδcont hδbdd
                - deltaStepLp hBmeas hδadap hδbdd n :
                  Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
            ∂(trimMeasure_T (μ := μ) T hBmeas)))
          * (2 * |Dd| * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) :=
        mul_le_mul_of_nonneg_left hsqrttri
          (mul_nonneg (abs_nonneg Cw) (Real.sqrt_nonneg _))
    _ = 2 * |Cw| * |Dd| * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k)
          * Real.sqrt (∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ
              (Set.univ : Set Ω),
            ((processToLp T hBmeas hδadap hδcont hδbdd
                - deltaStepLp hBmeas hδadap hδbdd n :
                  Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
            ∂(trimMeasure_T (μ := μ) T hBmeas)) := by ring

/-- **The summed gap bound** (the `hgap` witness of `quadraticSqSum_tendsto`, made
unconditional): the absolute difference between the summed weighted second moments and
the frozen rectangle sum is at most `2·|C_w|·|D_δ|·√T` times the `L²`
norm of the integrand error `φ − δⁿ` — per-cell Cauchy–Schwarz (`cellGap_le`), then
finite-sum Cauchy–Schwarz against the cell lengths (telescoping to `T`) and the summed band
energies of the error class (telescoping to `‖φ − δⁿ‖²` via `uniform_band_split` and the
`Lp` norm). -/
theorem gapSum_le (n : ℕ) (hn : 0 < n) {w : ℝ≥0 → Ω → ℝ} {Cw : ℝ}
    (hwadap : ∀ t, Measurable[natFiltration hBmeas t] (w t))
    (hwbdd : ∀ t ω, |w t ω| ≤ Cw) :
    |∑ k ∈ Finset.range n,
        ∫ ω, w (unifPart T n k) ω
          * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
      - ∑ k ∈ Finset.range n,
          (∫ ω, w (unifPart T n k) ω * δ (unifPart T n k) ω ^ 2 ∂μ)
            * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)|
      ≤ 2 * |Cw| * |Dd| * Real.sqrt (T : ℝ)
        * Real.sqrt (∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
          ((processToLp T hBmeas hδadap hδcont hδbdd
              - deltaStepLp hBmeas hδadap hδbdd n :
                Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas)) := by
  -- the cell lengths and the band energies of the integrand error
  set cell : ℕ → ℝ := fun k ↦ ((unifPart T n (k + 1) : ℝ) - unifPart T n k) with hcelldef
  set bandE : ℕ → ℝ := fun k ↦ ∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ
      (Set.univ : Set Ω),
      ((processToLp T hBmeas hδadap hδcont hδbdd
          - deltaStepLp hBmeas hδadap hδbdd n :
            Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
      ∂(trimMeasure_T (μ := μ) T hBmeas) with hbandEdef
  -- bridge the frozen sum to the rectangle sum (the per-cell weighted identity)
  have hsumbridge : ∑ k ∈ Finset.range n,
      (∫ ω, w (unifPart T n k) ω * δ (unifPart T n k) ω ^ 2 ∂μ) * cell k
      = ∑ k ∈ Finset.range n, ∫ ω, w (unifPart T n k) ω
          * (δ (unifPart T n k) ω
            * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ :=
    Finset.sum_congr rfl fun k _ ↦
      (weightedCellSq_step hB hBmeas hδadap (hwadap (unifPart T n k))).symm
  -- per-cell gap bounds
  have hpercell : ∀ k ∈ Finset.range n,
      |∫ ω, w (unifPart T n k) ω
          * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
        - ∫ ω, w (unifPart T n k) ω * (δ (unifPart T n k) ω
            * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ|
        ≤ 2 * |Cw| * |Dd| * Real.sqrt (cell k) * Real.sqrt (bandE k) :=
    fun k hk => cellGap_le hB hBmeas hδadap hδcont hδbdd hMadap hMeq (Finset.mem_range.mp hk)
      (hwadap (unifPart T n k)) (hwbdd (unifPart T n k))
  -- the cell lengths telescope to `T`; the band energies telescope to `‖φ − δⁿ‖²`
  have hsumcell : ∑ k ∈ Finset.range n, cell k = (T : ℝ) := by
    rw [sum_telescope (a := fun k ↦ ((unifPart T n k : ℝ)))]
    have hnT : unifPart T n n = T := by
      have hne : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      simp only [unifPart, div_self hne, one_mul]
    have h0 : unifPart T n 0 = 0 := by simp only [unifPart]; norm_num
    rw [hnT, h0]; simp
  have hbandsum : ∑ k ∈ Finset.range n, bandE k
      = ∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
        ((processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
        ∂(trimMeasure_T (μ := μ) T hBmeas) :=
    (uniform_band_split hBmeas hn
      (hFint := (Lp.memLp (processToLp T hBmeas hδadap hδcont hδbdd
        - deltaStepLp hBmeas hδadap hδbdd n)).integrable_sq)).symm
  -- finite-sum Cauchy–Schwarz on the cell/band pairing
  have hf2 : ∀ k : ℕ, (Real.sqrt (cell k)) ^ 2 = cell k := fun k ↦
    Real.sq_sqrt (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (unifPart_mono T n (Nat.le_succ k))))
  have hg2 : ∀ k : ℕ, (Real.sqrt (bandE k)) ^ 2 = bandE k := fun k ↦
    Real.sq_sqrt (integral_nonneg fun z ↦ sq_nonneg _)
  have hsq : (∑ k ∈ Finset.range n, (Real.sqrt (cell k) * Real.sqrt (bandE k))) ^ 2
      ≤ (T : ℝ) * ∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
        ((processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
        ∂(trimMeasure_T (μ := μ) T hBmeas) := by
    have key := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n)
      (f := fun k : ℕ ↦ Real.sqrt (cell k)) (g := fun k : ℕ ↦ Real.sqrt (bandE k))
    rw [Finset.sum_congr rfl fun k _ ↦ hf2 k, Finset.sum_congr rfl fun k _ ↦ hg2 k,
      hsumcell, hbandsum] at key
    exact key
  have hpair : ∑ k ∈ Finset.range n, (Real.sqrt (cell k) * Real.sqrt (bandE k))
      ≤ Real.sqrt (T : ℝ) * Real.sqrt (∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
        ((processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
        ∂(trimMeasure_T (μ := μ) T hBmeas)) := by
    have hX0 : 0 ≤ ∑ k ∈ Finset.range n, (Real.sqrt (cell k) * Real.sqrt (bandE k)) :=
      Finset.sum_nonneg fun k _ ↦ mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc ∑ k ∈ Finset.range n, (Real.sqrt (cell k) * Real.sqrt (bandE k))
        ≤ Real.sqrt ((∑ k ∈ Finset.range n,
          (Real.sqrt (cell k) * Real.sqrt (bandE k))) ^ 2) := by
          rw [Real.sqrt_sq hX0]
      _ ≤ Real.sqrt ((T : ℝ) * ∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
          ((processToLp T hBmeas hδadap hδcont hδbdd
              - deltaStepLp hBmeas hδadap hδbdd n :
                Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas)) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (T : ℝ) * Real.sqrt (∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
          ((processToLp T hBmeas hδadap hδcont hδbdd
              - deltaStepLp hBmeas hδadap hδbdd n :
                Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas)) := by
          rw [Real.sqrt_mul (NNReal.coe_nonneg T)]
  -- assembly
  calc |∑ k ∈ Finset.range n,
          ∫ ω, w (unifPart T n k) ω
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
        - ∑ k ∈ Finset.range n,
            (∫ ω, w (unifPart T n k) ω * δ (unifPart T n k) ω ^ 2 ∂μ) * cell k|
      = |∑ k ∈ Finset.range n,
          (∫ ω, w (unifPart T n k) ω
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
          - ∫ ω, w (unifPart T n k) ω * (δ (unifPart T n k) ω
            * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ)| := by
        rw [hsumbridge, ← Finset.sum_sub_distrib]
    _ ≤ ∑ k ∈ Finset.range n,
          |∫ ω, w (unifPart T n k) ω
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
          - ∫ ω, w (unifPart T n k) ω * (δ (unifPart T n k) ω
            * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, 2 * |Cw| * |Dd| * (Real.sqrt (cell k)
          * Real.sqrt (bandE k)) :=
        Finset.sum_le_sum fun k hk ↦ by
          rw [show (2:ℝ) * |Cw| * |Dd| * (Real.sqrt (cell k) * Real.sqrt (bandE k))
              = 2 * |Cw| * |Dd| * Real.sqrt (cell k) * Real.sqrt (bandE k) from by ring]
          exact hpercell k hk
    _ = 2 * |Cw| * |Dd| * ∑ k ∈ Finset.range n,
          (Real.sqrt (cell k) * Real.sqrt (bandE k)) := by
        rw [← Finset.mul_sum]
    _ ≤ 2 * |Cw| * |Dd| * (Real.sqrt (T : ℝ) * Real.sqrt (∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ
          (Set.univ : Set Ω),
        ((processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
        ∂(trimMeasure_T (μ := μ) T hBmeas))) :=
        mul_le_mul_of_nonneg_left hpair
          (mul_nonneg (mul_nonneg zero_le_two (abs_nonneg Cw)) (abs_nonneg Dd))
    _ = 2 * |Cw| * |Dd| * Real.sqrt (T : ℝ)
          * Real.sqrt (∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
        ((processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
        ∂(trimMeasure_T (μ := μ) T hBmeas)) := by ring

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- **The convergence of the quadratic block, unconditional** (the `hgap` hypothesis of
`quadraticSqSum_tendsto` discharged by `gapSum_le` + `deltaStepLp_tendsto`). -/
theorem quadraticSqSum_tendsto_uncond (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t))
    {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
    {M : ℝ≥0 → Ω → ℝ}
    (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
    (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
      (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))
    {w : ℝ≥0 → Ω → ℝ} {Cw : ℝ}
    (hwadap : ∀ t, Measurable[natFiltration hBmeas t] (w t))
    (hwcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ w s ω)
    (hwbdd : ∀ s ω, |w s ω| ≤ Cw) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
        ∫ ω, w (unifPart T n k) ω
          * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)
      atTop (𝓝 (∫ s in Set.Ioc 0 T,
          (∫ ω, w s ω * (δ s ω * δ s ω) ∂μ) ∂ItoIntegralL2.timeMeasure)) := by
  refine quadraticSqSum_tendsto hB hBmeas hδadap hδcont hδbdd hMeq hwadap hwcont hwbdd
    ⟨fun n ↦ Real.sqrt (∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
      ((processToLp T hBmeas hδadap hδcont hδbdd
          - deltaStepLp hBmeas hδadap hδbdd n :
            Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
      ∂(trimMeasure_T (μ := μ) T hBmeas)), ?_, ?_⟩
  · -- `r n` is squeezed by `‖φ − δⁿ‖ → 0` (the band integral is at most the full norm²)
    have htend := deltaStepLp_tendsto (T := T) hB hBmeas hδadap hδcont hδbdd
    have hnorm := (tendsto_iff_norm_sub_tendsto_zero.mp htend).congr'
      (Eventually.of_forall fun n ↦ by rw [norm_sub_rev])
    refine squeeze_zero' (Eventually.of_forall fun n ↦ Real.sqrt_nonneg _) ?_ hnorm
    filter_upwards [] with n
    refine le_trans (Real.sqrt_le_sqrt ?_)
      (le_of_eq (show Real.sqrt (‖(processToLp T hBmeas hδadap hδcont hδbdd
          - deltaStepLp hBmeas hδadap hδbdd n :
            Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖ ^ 2)
        = ‖(processToLp T hBmeas hδadap hδcont hδbdd
          - deltaStepLp hBmeas hδadap hδbdd n :
            Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖ from
        Real.sqrt_sq (norm_nonneg _)))
    have hsqint : Integrable (fun z ↦
        ((processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2)
        (trimMeasure_T (μ := μ) T hBmeas) :=
      (Lp.memLp (processToLp T hBmeas hδadap hδcont hδbdd
        - deltaStepLp hBmeas hδadap hδbdd n)).integrable_sq
    have hintband : IntegrableOn (fun z ↦
        ((processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2)
        (Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω)) (trimMeasure_T (μ := μ) T hBmeas) :=
      hsqint.mono_measure Measure.restrict_le_self
    have hbandmsP : MeasurableSet[(natFiltration hBmeas).predictable]
        (Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω)) :=
      measurableSet_predictable_Ioc_prod (0:ℝ≥0) T MeasurableSet.univ
    have hbandms : MeasurableSet (Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω)) :=
      MeasurableSet.prod (measurableSet_Ioc (α := ℝ≥0)) MeasurableSet.univ
    have hintInd : Integrable ((Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω)).indicator
        (fun z ↦ ((processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2))
        (trimMeasure_T (μ := μ) T hBmeas) :=
      (integrable_indicator_iff (μ := trimMeasure_T (μ := μ) T hBmeas)
        (f := fun z : ℝ≥0 × Ω ↦
          ((processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2)
        hbandmsP).mpr hintband
    calc ∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
        ((processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
        ∂(trimMeasure_T (μ := μ) T hBmeas)
        = ∫ z, (Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω)).indicator
            (fun z ↦ ((processToLp T hBmeas hδadap hδcont hδbdd
              - deltaStepLp hBmeas hδadap hδbdd n :
                Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2) z
          ∂(trimMeasure_T (μ := μ) T hBmeas) :=
          (integral_indicator (μ := trimMeasure_T (μ := μ) T hBmeas)
            (f := fun z : ℝ≥0 × Ω ↦
              ((processToLp T hBmeas hδadap hδcont hδbdd
                - deltaStepLp hBmeas hδadap hδbdd n :
                  Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2)
            hbandmsP).symm
      _ ≤ ∫ z, ((processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas) :=
          integral_mono hintInd hsqint (fun z ↦ by
            by_cases hz : z ∈ Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω)
            · rw [Set.indicator_of_mem hz]
            · rw [Set.indicator_of_notMem hz]
              exact sq_nonneg _)
      _ = ‖(processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖ ^ 2 :=
          (lp_two_norm_sq (processToLp T hBmeas hδadap hδcont hδbdd
            - deltaStepLp hBmeas hδadap hδbdd n)).symm
  · exact fun n hn ↦ gapSum_le hB hBmeas hδadap hδcont hδbdd hMadap hMeq n hn hwadap hwbdd

end StageFiveA

/-! #### Stage 5b — the third-moment bound

The fourth moment of the true increment over a uniform cell, obtained from the step-sum
recursion `stepSum_pow4_le` (the potential `3S² + 6D²SC + 3D⁴Q`: each refined-band Riemann
sum of the bounded adapted integrand has fourth moment at most `3·(D²·band length)²`),
passed to the true increment through the step approximants' `L²` convergence
(`clm_band_energy` + `deltaStepLp_tendsto`), convergence in measure, an a.e. subsequence,
and Fatou (`lintegral_liminf_le`). The cube bound then drops out by Cauchy–Schwarz
interpolation (`∫|X|³ ≤ ‖X‖₂·‖X‖₄²·...`). -/

section StageFiveB

open MeasureTheory ProbabilityTheory Filter Topology ItoIntegralProcessGeneral
open ItoIntegralL2 ItoIntegralCLM ItoIntegralRiemannBridge ItoIsometryAdapted
open ItoIntegralProcess QuadraticVariationL2 MathFin
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
  {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
  (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
  (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
  (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
  {M : ℝ≥0 → Ω → ℝ}
  (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
  (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
    (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))

include hB hBmeas hδadap hδcont hδbdd hMadap hMeq

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- Pointwise fourth-power domination from an absolute-value bound
(the `sq_le_sq'`/`abs_le` elaboration-order trap, spelled out). -/
private theorem pow4_le_pow4_of_abs_le {a b : ℝ} (h : |a| ≤ b) : a ^ 4 ≤ b ^ 4 := by
  have e1 : a ^ 4 = |a| ^ 4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity)]
  calc a ^ 4 = |a| ^ 4 := e1
    _ ≤ b ^ 4 := pow_le_pow_left₀ (abs_nonneg a) h 4

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- Pointwise square domination from an absolute-value bound. -/
private theorem sq_le_sq_of_abs_le {a b : ℝ} (h : |a| ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have e1 : a ^ 2 = |a| ^ 2 := by
    rw [← abs_pow, abs_of_nonneg (by positivity)]
  calc a ^ 2 = |a| ^ 2 := e1
    _ ≤ b ^ 2 := pow_le_pow_left₀ (abs_nonneg a) h 2

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- Young's pointwise inequality `|a|³|b| ≤ 3a⁴/4 + b⁴/4`: from
`(a − b)²(2a² + (a+b)²) = 3a⁴ + b⁴ − 4a³b ≥ 0`, evaluated at `(|a|, |b|)`. -/
private theorem young34 (a b : ℝ) : |a| ^ 3 * |b| ≤ 3 * a ^ 4 / 4 + b ^ 4 / 4 := by
  have h1 : (0:ℝ) ≤ (abs a - abs b) ^ 2 := sq_nonneg _
  have h2 : (0:ℝ) ≤ 2 * abs a ^ 2 + (abs a + abs b) ^ 2 := by positivity
  have h3 : (abs a - abs b) ^ 2 * (2 * abs a ^ 2 + (abs a + abs b) ^ 2)
      = 3 * abs a ^ 4 + abs b ^ 4 - 4 * abs a ^ 3 * abs b := by ring
  have h4 : |a| ^ 4 = a ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have h5 : |b| ^ 4 = b ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have key : (0:ℝ) ≤ 3 * a ^ 4 + b ^ 4 - 4 * |a| ^ 3 * |b| := by
    have hpro := mul_nonneg h1 h2
    rw [h3, h4, h5] at hpro
    linarith
  linarith

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- Young's pointwise inequality, the symmetric instance `|a|·|b|³ ≤ a⁴/4 + 3b⁴/4`. -/
private theorem young134 (a b : ℝ) : |a| * |b| ^ 3 ≤ a ^ 4 / 4 + 3 * b ^ 4 / 4 := by
  linarith [young34 b a, mul_comm (abs b ^ 3) (abs a)]

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- Third moment of a centered real Gaussian (odd moment, by density symmetry). -/
private theorem integral_pow3_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 3 ∂(gaussianReal 0 v) = 0 := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [gaussianReal_zero_var]
    simp
  · rw [integral_gaussianReal_eq_integral_smul hv]
    simp only [smul_eq_mul]
    have hmap : Measure.map (fun x : ℝ => -x) (volume : Measure ℝ) = volume :=
      (Measure.measurePreserving_neg (μ := (volume : Measure ℝ))).map_eq
    have hpdfneg : ∀ x : ℝ, gaussianPDFReal 0 v (-x) = gaussianPDFReal 0 v x := by
      intro x
      simp only [gaussianPDFReal, sub_zero, neg_sq]
    have hsub : ∫ y, gaussianPDFReal 0 v y * y ^ 3 ∂volume
        = ∫ x, gaussianPDFReal 0 v (-x) * (-x) ^ 3 ∂volume := by
      have h1 : ∫ y, gaussianPDFReal 0 v y * y ^ 3 ∂volume
          = ∫ y, gaussianPDFReal 0 v y * y ^ 3
              ∂(Measure.map (fun x : ℝ => -x) (volume : Measure ℝ)) := by
        rw [hmap]
      rw [h1]
      exact integral_map_equiv (MeasurableEquiv.neg (G := ℝ))
        (fun y : ℝ ↦ gaussianPDFReal 0 v y * y ^ 3)
    rw [hsub]
    have hcongr : ∫ x, gaussianPDFReal 0 v (-x) * (-x) ^ 3 ∂volume
        = -∫ x, gaussianPDFReal 0 v x * x ^ 3 ∂volume := by
      have hpt : ∀ x : ℝ, gaussianPDFReal 0 v (-x) * (-x) ^ 3
          = -(gaussianPDFReal 0 v x * x ^ 3) := by
        intro x
        rw [hpdfneg x]
        ring
      rw [integral_congr_ae (Eventually.of_forall hpt), integral_neg]
    rw [hcongr]
    linarith

omit hδadap hδcont hδbdd hMadap hMeq in
/-- Third moment of a Brownian increment: `E[(B_{t₁} − B_{t₀})³] = 0` for `t₀ ≤ t₁`
(the law-transfer of the vanishing odd Gaussian moment). -/
private theorem integral_increment_pow3
    {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁) :
    ∫ ω, (B t₁ ω - B t₀ ω) ^ 3 ∂μ = 0 := by
  have hv : nndist (t₁ : ℝ) (t₀ : ℝ) = t₁ - t₀ := by
    apply NNReal.coe_injective
    rw [coe_nndist, Real.dist_eq, NNReal.coe_sub ht,
      abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr ht))]
  have hlaw : HasLaw (fun ω ↦ B t₁ ω - B t₀ ω) (gaussianReal 0 (t₁ - t₀)) μ := by
    rw [← hv]; exact hB.hasLaw_sub t₁ t₀
  have hcomp := hlaw.integral_comp (f := fun x : ℝ ↦ x ^ 3)
    (measurable_id.pow_const 3).aestronglyMeasurable
  simp only [Function.comp_def] at hcomp
  rw [hcomp, integral_pow3_gaussianReal]

omit hδadap hδcont hδbdd hMadap hMeq in
/-- Fourth-power isometry kernel: for `χ` measurable in the natural filtration at `t₀`,
`E[χ·(B t₁ − B t₀)⁴] = E[χ]·3·(t₁ − t₀)²`. -/
private theorem integral_natMeasurable_mul_increment_pow4
    {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁)
    {χ : Ω → ℝ} (hχ : Measurable[natFiltration hBmeas t₀] χ) :
    ∫ ω, χ ω * (B t₁ ω - B t₀ ω) ^ 4 ∂μ
      = (∫ ω, χ ω ∂μ) * (3 * ((t₁ : ℝ) - t₀) ^ 2) := by
  have hχ' := adaptedAt_of_measurable_natural hBmeas hχ
  have hχm : Measurable χ := hχ'.measurable hBmeas
  have hΔm : Measurable (fun ω ↦ B t₁ ω - B t₀ ω) := (hBmeas t₁).sub (hBmeas t₀)
  have hindep := adapted_indepFun_increment hB hBmeas ht hχ'
  have hindep2 := hindep.comp (φ := (id : ℝ → ℝ)) (ψ := fun x : ℝ ↦ x ^ 4)
    measurable_id (by fun_prop)
  have key := hindep2.integral_fun_mul_eq_mul_integral
    hχm.aestronglyMeasurable (hΔm.pow_const 4).aestronglyMeasurable
  simp only [Function.comp_apply, id_eq] at key
  rw [key, integral_increment_pow4 hB ht]

omit hδadap hδcont hδbdd hMadap hMeq in
set_option maxHeartbeats 1600000 in
/-- **The step-sum fourth-moment recursion**: for a bounded integrand sampled along a
monotone time grid (`φ j` measurable in `𝓕_{s j}`, `|φ| ≤ D`), the fourth moment of the
Itô sum is at most `3·(D²·total gap)²`. -/
private theorem stepSum_pow4_le {s : ℕ → ℝ≥0} (hsmono : Monotone s) {φ : ℕ → Ω → ℝ}
    (hφm : ∀ j, Measurable[natFiltration hBmeas (s j)] (φ j))
    {D : ℝ} (hφbdd : ∀ j ω, |φ j ω| ≤ D) (N : ℕ) :
    ∫⁻ ω, ENNReal.ofReal
        ((∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4) ∂μ
      ≤ ENNReal.ofReal
        (3 * (D ^ 2 * ∑ k ∈ Finset.range N, ((s (k + 1) : ℝ) - s k)) ^ 2) := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  induction N with
  | zero => simp
  | succ N ihN =>
    have hexpan : ∀ ω : Ω,
        (∑ k ∈ Finset.range (N + 1), φ k ω * (B (s (k + 1)) ω - B (s k) ω))
          = (∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω))
            + φ N ω * (B (s (N + 1)) ω - B (s N) ω) := fun ω ↦ by
      rw [Finset.sum_range_succ]
    have hgapexpan : (∑ k ∈ Finset.range (N + 1), ((s (k + 1) : ℝ) - s k))
        = (∑ k ∈ Finset.range N, ((s (k + 1) : ℝ) - s k))
          + ((s (N + 1) : ℝ) - s N) := by
      rw [Finset.sum_range_succ]
    have hexpan4 : ∀ ω : Ω,
        (∑ k ∈ Finset.range (N + 1), φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4
          = ((∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω))
            + φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 := fun ω ↦ by
      rw [hexpan ω]
    -- measurability at the later grid point
    have hφmN : ∀ k : ℕ, k ≤ N → Measurable[natFiltration hBmeas (s N)] (φ k) := fun k hk ↦
      (hφm k).mono ((natFiltration hBmeas).mono (hsmono hk)) le_rfl
    have hBle : ∀ {u : ℝ≥0}, u ≤ s N →
        Measurable[natFiltration hBmeas (s N)] (B u) := by
      intro u hu
      have hle : MeasurableSpace.comap (B u) (inferInstance : MeasurableSpace ℝ)
          ≤ natFiltration hBmeas (s N) := le_iSup₂_of_le u hu le_rfl
      exact (measurable_iff_comap_le.mpr le_rfl).mono hle le_rfl
    have hYm : ∀ k : ℕ, k < N → Measurable[natFiltration hBmeas (s N)]
        (fun ω ↦ φ k ω * (B (s (k + 1)) ω - B (s k) ω)) := by
      intro k hk
      exact (hφmN k (Nat.le_of_lt hk)).mul
        ((hBle (hsmono (Nat.succ_le_of_lt hk))).sub (hBle (hsmono (Nat.le_of_lt hk))))
    have hZm : Measurable[natFiltration hBmeas (s N)]
        (fun ω ↦ ∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) :=
      Finset.measurable_sum _ fun k hk ↦ hYm k (Finset.mem_range.mp hk)
    have hZadapt : AdaptedAt B (s N)
        (fun ω ↦ ∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) :=
      adaptedAt_of_measurable_natural hBmeas hZm
    have hyadapt : AdaptedAt B (s N) (φ N) :=
      adaptedAt_of_measurable_natural hBmeas (hφmN N (Nat.le_refl N))
    -- the exact second moment via the discrete Itô isometry
    have hφL2 : ∀ k : ℕ, MemLp (φ k) 2 μ := fun k ↦
      MemLp.of_bound (((hφm k).mono ((natFiltration hBmeas).le _) le_rfl)).aestronglyMeasurable
        D (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hφbdd k ω)
    have hZ2 : ∫ ω, (∑ k ∈ Finset.range N,
        φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2 ∂μ
        = ∑ k ∈ Finset.range N, (∫ ω, (φ k ω) ^ 2 ∂μ) * ((s (k + 1) : ℝ) - s k) :=
      ito_isometry_discrete hB hBmeas hsmono
        (fun k ↦ adaptedAt_of_measurable_natural hBmeas (hφm k)) hφL2
    -- the fourth moment of the last rectangle and its bound
    have hy4 : ∫ ω, (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 ∂μ
        = (∫ ω, (φ N ω) ^ 4 ∂μ) * (3 * ((s (N + 1) : ℝ) - s N) ^ 2) := by
      have h := integral_natMeasurable_mul_increment_pow4 hB hBmeas
        (hsmono (Nat.le_succ N))
        (χ := fun ω ↦ (φ N ω) ^ 4) ((hφmN N (Nat.le_refl N)).pow_const 4)
      rw [integral_congr_ae (Eventually.of_forall fun ω ↦ by rw [mul_pow])]
      exact h
    have hy4le : ∫ ω, (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 ∂μ
        ≤ 3 * (D ^ 2 * ((s (N + 1) : ℝ) - s N)) ^ 2 := by
      rw [hy4]
      have hφ4 : ∫ ω, (φ N ω) ^ 4 ∂μ ≤ D ^ 4 := by
        refine le_trans (integral_mono_of_nonneg (μ := μ)
          (Eventually.of_forall fun ω ↦ show (0:ℝ) ≤ φ N ω ^ 4 from by positivity)
          (integrable_const (D ^ 4)) (ae_of_all μ fun ω ↦ ?_)) ?_
        · exact pow4_le_pow4_of_abs_le (hφbdd N ω)
        · rw [integral_const]
          simp
      calc (∫ ω, (φ N ω) ^ 4 ∂μ) * (3 * ((s (N + 1) : ℝ) - s N) ^ 2)
          ≤ D ^ 4 * (3 * ((s (N + 1) : ℝ) - s N) ^ 2) :=
            mul_le_mul_of_nonneg_right hφ4 (mul_nonneg zero_le_three (sq_nonneg _))
        _ = 3 * (D ^ 2 * ((s (N + 1) : ℝ) - s N)) ^ 2 := by ring
    -- integrability of the rectangle products
    have hY4mem : ∀ k : ℕ, MemLp (fun ω ↦ φ k ω * (B (s (k + 1)) ω - B (s k) ω)) 4 μ := by
      intro k
      have hφ4 : Integrable (fun ω ↦ (φ k ω) ^ 4) μ :=
        Integrable.mono' (integrable_const (D ^ 4))
          (((hφm k).mono ((natFiltration hBmeas).le _) le_rfl).pow_const
            4 |>.aestronglyMeasurable)
          (ae_of_all μ fun ω ↦ by
            show ‖(φ k ω) ^ 4‖ ≤ D ^ 4
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (φ k ω) ^ 4)]
            exact pow4_le_pow4_of_abs_le (hφbdd k ω))
      have hΔ4 : Integrable (fun ω ↦ (B (s (k + 1)) ω - B (s k) ω) ^ 4) μ := by
        have h := (memLp_increment_four hB (s k) (s (k + 1))).integrable_norm_pow
          (by norm_num)
        refine h.congr (Eventually.of_forall fun ω ↦ ?_)
        show ‖B (s (k + 1)) ω - B (s k) ω‖ ^ 4 = (B (s (k + 1)) ω - B (s k) ω) ^ 4
        rw [Real.norm_eq_abs, pow_abs]
        exact abs_of_nonneg (by positivity : (0:ℝ) ≤
          (B (s (k + 1)) ω - B (s k) ω) ^ 4)
      have hindep4 := (adapted_indepFun_increment hB hBmeas (hsmono (Nat.le_succ k))
        (adaptedAt_of_measurable_natural hBmeas (hφm k))).comp
        (φ := fun x : ℝ ↦ x ^ 4) (ψ := fun x : ℝ ↦ x ^ 4) (by fun_prop) (by fun_prop)
      have hint4 : Integrable (fun ω ↦ (φ k ω) ^ 4
          * (B (s (k + 1)) ω - B (s k) ω) ^ 4) μ := hindep4.integrable_mul hφ4 hΔ4
      have hpt : ∀ ω : Ω, ‖φ k ω * (B (s (k + 1)) ω - B (s k) ω)‖ ^ 4
          = (φ k ω) ^ 4 * (B (s (k + 1)) ω - B (s k) ω) ^ 4 := by
        intro ω
        show ‖φ k ω * (B (s (k + 1)) ω - B (s k) ω)‖ ^ 4 = _
        rw [Real.norm_eq_abs, abs_mul, mul_pow,
          ← abs_pow (φ k ω) 4, ← abs_pow (B (s (k + 1)) ω - B (s k) ω) 4,
          abs_of_nonneg (show (0:ℝ) ≤ φ k ω ^ 4 from by positivity),
          abs_of_nonneg (show (0:ℝ) ≤ (B (s (k + 1)) ω - B (s k) ω) ^ 4
            from by positivity)]
      have hint4' : Integrable (fun ω ↦
          ‖φ k ω * (B (s (k + 1)) ω - B (s k) ω)‖ ^ 4) μ :=
        hint4.congr (Eventually.of_forall fun ω ↦ (hpt ω).symm)
      have hsm : AEStronglyMeasurable
          (fun ω ↦ φ k ω * (B (s (k + 1)) ω - B (s k) ω)) μ :=
        (((hφm k).mono ((natFiltration hBmeas).le _) le_rfl).mul
          ((hBmeas (s (k + 1))).sub (hBmeas (s k)))).aestronglyMeasurable
      have hint4'' : Integrable (fun ω ↦
          ‖φ k ω * (B (s (k + 1)) ω - B (s k) ω)‖
            ^ ((4 : ℕ) : ℝ≥0∞).toReal) μ := by
        have h4r : ((4 : ℕ) : ℝ≥0∞).toReal = (4 : ℝ) := by norm_num
        rw [h4r]
        have hint4' : Integrable (fun ω ↦
            ‖φ k ω * (B (s (k + 1)) ω - B (s k) ω)‖ ^ 4) μ :=
          hint4.congr (Eventually.of_forall fun ω ↦ (hpt ω).symm)
        have hcongr : (fun ω ↦ ‖φ k ω * (B (s (k + 1)) ω - B (s k) ω)‖ ^ (4 : ℝ))
            = (fun ω ↦ ‖φ k ω * (B (s (k + 1)) ω - B (s k) ω)‖ ^ 4) := by
          funext ω
          exact Real.rpow_natCast _ 4
        rw [hcongr]
        exact hint4'
      exact (integrable_norm_rpow_iff hsm (by norm_num) (by simp)).mp hint4''
    have hZ4mem : MemLp (fun ω ↦ ∑ k ∈ Finset.range N,
        φ k ω * (B (s (k + 1)) ω - B (s k) ω)) 4 μ :=
      memLp_finsetSum _ fun k _ ↦ hY4mem k
    have hZaesm := hZ4mem.1
    have hintZ4 : Integrable (fun ω ↦ (∑ k ∈ Finset.range N,
        φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4) μ := by
      have h := hZ4mem.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
      refine h.congr (Eventually.of_forall fun ω ↦ ?_)
      show ‖(∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω))‖ ^ 4
        = (∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4
      rw [Real.norm_eq_abs,
        ← abs_pow (∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) 4,
        abs_of_nonneg (by positivity : (0:ℝ) ≤
          (∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4)]
    have hZmeas : Measurable (fun ω ↦ ∑ k ∈ Finset.range N,
        φ k ω * (B (s (k + 1)) ω - B (s k) ω)) :=
      hZm.mono ((natFiltration hBmeas).le (s N)) le_rfl
    have hintZ2 : Integrable (fun ω ↦ (∑ k ∈ Finset.range N,
        φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2) μ :=
      Integrable.mono' (integrable_norm_pow_of_le (p := 2) (q := 4) hZaesm (by norm_num)
        (hZ4mem.integrable_norm_pow (by norm_num)))
        (hZmeas.pow_const 2).aestronglyMeasurable
        (ae_of_all μ fun ω ↦ by rw [norm_pow])
    have hintYN4 : Integrable (fun ω ↦ (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4) μ :=
      (hY4mem N).integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
      |>.congr (Eventually.of_forall fun ω ↦ by
        show ‖φ N ω * (B (s (N + 1)) ω - B (s N) ω)‖ ^ 4
          = (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4
        rw [Real.norm_eq_abs,
          ← abs_pow (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) 4,
          abs_of_nonneg (by positivity : (0:ℝ) ≤
            (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4)])
    have hφmeasN : Measurable (φ N) :=
      (hφmN N (Nat.le_refl N)).mono ((natFiltration hBmeas).le (s N)) le_rfl
    have hΔmeasN : Measurable (fun ω ↦ B (s (N + 1)) ω - B (s N) ω) :=
      (hBmeas (s (N + 1))).sub (hBmeas (s N))
    -- the odd-term integrabilities (Young domination by fourth powers)
    have hintZY0 : Integrable (fun ω ↦ (∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3
        * (φ N ω * (B (s (N + 1)) ω - B (s N) ω))) μ :=
      Integrable.mono' ((hintZ4.const_mul (3 / 4)).add (hintYN4.const_mul (1 / 4)))
        ((hZmeas.pow_const 3).mul (hφmeasN.mul hΔmeasN)).aestronglyMeasurable
        (ae_of_all μ fun ω ↦ by
          show ‖(∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3
              * (φ N ω * (B (s (N + 1)) ω - B (s N) ω))‖
            ≤ 3 / 4 * (∑ k ∈ Finset.range N,
                φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4
              + 1 / 4 * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4
          rw [Real.norm_eq_abs, abs_mul, abs_pow]
          have hy := young34 (∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω))
            (φ N ω * (B (s (N + 1)) ω - B (s N) ω))
          linarith)
    have hintSY3 : Integrable (fun ω ↦ (∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω))
        * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 3) μ :=
      Integrable.mono' ((hintZ4.const_mul (1 / 4)).add (hintYN4.const_mul (3 / 4)))
        (hZmeas.mul ((hφmeasN.mul hΔmeasN).pow_const 3)).aestronglyMeasurable
        (ae_of_all μ fun ω ↦ by
          show ‖(∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω))
              * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 3‖
            ≤ 1 / 4 * (∑ k ∈ Finset.range N,
                φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4
              + 3 / 4 * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4
          rw [Real.norm_eq_abs, abs_mul, abs_pow]
          have hy := young134 (∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω))
            (φ N ω * (B (s (N + 1)) ω - B (s N) ω))
          linarith)
    have hintZY2 : Integrable (fun ω ↦ (∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
        * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2) μ :=
      Integrable.mono' ((hintZ4.const_mul (1 / 2)).add (hintYN4.const_mul (1 / 2)))
        (Measurable.aestronglyMeasurable (Measurable.mul
          (Measurable.pow_const hZmeas 2)
          (Measurable.pow_const
            (Measurable.mul hφmeasN hΔmeasN) 2)))
        (ae_of_all μ fun ω ↦ by
          show ‖(∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
              * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2‖
            ≤ 1 / 2 * (∑ k ∈ Finset.range N,
                φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4
              + 1 / 2 * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4
          have habs : ‖(∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
              * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2‖
              = (∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
                * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2 :=
            abs_of_nonneg (by positivity)
          rw [habs]
          have hgen : ∀ a b : ℝ, (2:ℝ) * (a ^ 2 * b ^ 2) ≤ a ^ 4 + b ^ 4 := by
            intro a b
            have hx : (a ^ 2 - b ^ 2) ^ 2 = a ^ 4 + b ^ 4 - 2 * (a ^ 2 * b ^ 2) := by ring
            have h : (0:ℝ) ≤ (a ^ 2 - b ^ 2) ^ 2 := sq_nonneg _
            rw [hx] at h
            linarith
          have hsq := hgen (∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω))
            (φ N ω * (B (s (N + 1)) ω - B (s N) ω))
          linarith)
    -- the martingale-difference zeros (odd kernels) and the weighted even term
    have hZ3adapt : AdaptedAt B (s N) (fun ω ↦
        (∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3 * φ N ω) := by
      obtain ⟨g, hg, hgf⟩ := hZadapt
      obtain ⟨g', hg', hgf'⟩ := hyadapt
      refine ⟨fun p => (g p) ^ 3 * g' p, hg.pow_const 3 |>.mul hg', ?_⟩
      funext ω
      have h1 := congrFun hgf ω
      have h2 := congrFun hgf' ω
      rw [h1, h2]
      rfl
    have hZY0 : ∫ ω, (∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3
        * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ∂μ = 0 := by
      rw [show (fun ω ↦ (∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3
          * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)))
        = (fun ω ↦ ((∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3 * φ N ω)
          * (B (s (N + 1)) ω - B (s N) ω)) from by funext ω; ring]
      exact integral_adapted_mul_increment hB hBmeas (hsmono (Nat.le_succ N)) hZ3adapt
    have hcoef3 : AdaptedAt B (s N) (fun ω ↦
        (∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) * (φ N ω) ^ 3) := by
      obtain ⟨g, hg, hgf⟩ := hZadapt
      obtain ⟨g', hg', hgf'⟩ := hyadapt
      refine ⟨fun p => g p * (g' p) ^ 3, hg.mul (hg'.pow_const 3), ?_⟩
      funext ω
      have h1 := congrFun hgf ω
      have h2 := congrFun hgf' ω
      rw [h1, h2]
      rfl
    have hY30 : ∫ ω, (∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω))
        * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 3 ∂μ = 0 := by
      have hcoefm : Measurable (fun ω ↦
          (∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) * (φ N ω) ^ 3) :=
        (hZm.mul ((hφmN N (Nat.le_refl N)).pow_const 3)).mono
          ((natFiltration hBmeas).le (s N)) le_rfl
      have hΔm3 : Measurable (fun ω ↦ (B (s (N + 1)) ω - B (s N) ω) ^ 3) :=
        hΔmeasN.pow_const 3
      have hindep3 := (adapted_indepFun_increment hB hBmeas (hsmono (Nat.le_succ N))
        hcoef3).comp (φ := (id : ℝ → ℝ)) (ψ := fun x : ℝ ↦ x ^ 3)
        measurable_id (by fun_prop)
      have key := hindep3.integral_fun_mul_eq_mul_integral
        hcoefm.aestronglyMeasurable hΔm3.aestronglyMeasurable
      simp only [Function.comp_apply, id_eq] at key
      rw [show (fun ω ↦ (∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω))
          * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 3)
        = (fun ω ↦ ((∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω)) * (φ N ω) ^ 3)
          * (B (s (N + 1)) ω - B (s N) ω) ^ 3) from by funext ω; ring]
      rw [key, integral_increment_pow3 hB hBmeas (hsmono (Nat.le_succ N)), mul_zero]
    -- the even mixed term: isometry kernel at `χ = Z²φN²`
    have hZ2adapt : AdaptedAt B (s N) (fun ω ↦
        (∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
          * (φ N ω) ^ 2) := by
      obtain ⟨g, hg, hgf⟩ := hZadapt
      obtain ⟨g', hg', hgf'⟩ := hyadapt
      refine ⟨fun p => (g p) ^ 2 * (g' p) ^ 2, hg.pow_const 2 |>.mul (hg'.pow_const 2), ?_⟩
      funext ω
      have h1 := congrFun hgf ω
      have h2 := congrFun hgf' ω
      rw [h1, h2]
      rfl
    have hZ2le : ∫ ω, (∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2 ∂μ
        ≤ D ^ 2 * ∑ k ∈ Finset.range N, ((s (k + 1) : ℝ) - s k) := by
      rw [hZ2]
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun k _ ↦
        mul_le_mul_of_nonneg_right
          (by
            have hmono : ∫ (a : Ω), φ k a ^ 2 ∂μ ≤ ∫ (a : Ω), D ^ 2 ∂μ :=
              integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ sq_nonneg _)
                (integrable_const (D ^ 2)) (ae_of_all _ fun ω ↦
                  sq_le_sq_of_abs_le (hφbdd k ω))
            rw [integral_const] at hmono
            simpa using hmono)
          (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (hsmono (Nat.le_succ k))))
    have hZ2phi2 : ∫ ω, (∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2 * (φ N ω) ^ 2 ∂μ
        ≤ D ^ 2 * ∫ ω, (∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2 ∂μ := by
      refine le_trans (integral_mono_of_nonneg (μ := μ)
        (Eventually.of_forall fun ω ↦ show (0:ℝ) ≤
          (∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
            * (φ N ω) ^ 2 from by positivity)
        (hintZ2.const_mul (D ^ 2)) (ae_of_all μ fun ω ↦ ?_)) ?_
      · calc (∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2 * (φ N ω) ^ 2
            ≤ (∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2 * D ^ 2 :=
              mul_le_mul_of_nonneg_left (sq_le_sq_of_abs_le (hφbdd N ω))
                (pow_two_nonneg (∑ k ∈ Finset.range N,
                  φ k ω * (B (s (k + 1)) ω - B (s k) ω)))
        _ = D ^ 2 * (∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2 := mul_comm _ _
      · rw [integral_const_mul]
    have hZY2 : ∫ ω, (∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
        * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2 ∂μ
        = (∫ ω, (∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2 * (φ N ω) ^ 2 ∂μ)
          * ((s (N + 1) : ℝ) - s N) := by
      rw [show (fun ω ↦ (∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
          * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2)
        = (fun ω ↦ ((∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2 * (φ N ω) ^ 2)
          * (B (s (N + 1)) ω - B (s N) ω) ^ 2) from by funext ω; ring]
      exact integral_adapted_mul_increment_sq hB hBmeas (hsmono (Nat.le_succ N)) hZ2adapt
    have hZY2le : ∫ ω, (∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
        * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2 ∂μ
        ≤ (D ^ 2 * (D ^ 2 * ∑ k ∈ Finset.range N, ((s (k + 1) : ℝ) - s k)))
          * ((s (N + 1) : ℝ) - s N) := by
      rw [hZY2]
      calc (∫ ω, (∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2 * (φ N ω) ^ 2 ∂μ)
            * ((s (N + 1) : ℝ) - s N)
          ≤ (D ^ 2 * ∫ ω, (∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2 ∂μ)
            * ((s (N + 1) : ℝ) - s N) :=
            mul_le_mul_of_nonneg_right hZ2phi2 (sub_nonneg.mpr
              (NNReal.coe_le_coe.mpr (hsmono (Nat.le_succ N))))
        _ ≤ (D ^ 2 * (D ^ 2 * ∑ k ∈ Finset.range N, ((s (k + 1) : ℝ) - s k)))
            * ((s (N + 1) : ℝ) - s N) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hZ2le (sq_nonneg D)) (sub_nonneg.mpr
                (NNReal.coe_le_coe.mpr (hsmono (Nat.le_succ N))))
    -- the full expansion, odd kernels zeroed
    have hintBIG2 : Integrable (fun ω ↦ (∑ k ∈ Finset.range N,
        φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4
      + 4 * ((∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3
          * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)))) μ :=
      hintZ4.add (hintZY0.const_mul 4)
    have hintBIG3 : Integrable (fun ω ↦ (∑ k ∈ Finset.range N,
        φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4
      + 4 * ((∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3
          * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)))
      + 6 * ((∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
          * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2)) μ :=
      hintBIG2.add (hintZY2.const_mul 6)
    have hintBIG4 : Integrable (fun ω ↦ (∑ k ∈ Finset.range N,
        φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4
      + 4 * ((∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3
          * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)))
      + 6 * ((∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
          * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2)
      + 4 * ((∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω))
          * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 3)) μ :=
      hintBIG3.add (hintSY3.const_mul 4)
    have hexp : ∫ ω, ((∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω))
          + φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 ∂μ
        = ∫ ω, (∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4 ∂μ
          + 6 * ∫ ω, (∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
            * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2 ∂μ
          + ∫ ω, (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 ∂μ := by
      calc ∫ ω, ((∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω))
            + φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 ∂μ
          = ∫ ω, ((∑ k ∈ Finset.range N,
                φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4
              + 4 * ((∑ k ∈ Finset.range N,
                    φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3
                  * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)))
              + 6 * ((∑ k ∈ Finset.range N,
                    φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
                  * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2)
              + 4 * ((∑ k ∈ Finset.range N,
                    φ k ω * (B (s (k + 1)) ω - B (s k) ω))
                  * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 3)
              + (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4) ∂μ :=
            integral_congr_ae (Eventually.of_forall fun ω ↦ by ring)
        _ = ∫ ω, ((∑ k ∈ Finset.range N,
                φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4
              + 4 * ((∑ k ∈ Finset.range N,
                    φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3
                  * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)))
              + 6 * ((∑ k ∈ Finset.range N,
                    φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
                  * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2)
              + 4 * ((∑ k ∈ Finset.range N,
                    φ k ω * (B (s (k + 1)) ω - B (s k) ω))
                  * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 3)) ∂μ
            + ∫ ω, (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 ∂μ :=
            integral_add hintBIG4 hintYN4
        _ = (∫ ω, ((∑ k ∈ Finset.range N,
                φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4
              + 4 * ((∑ k ∈ Finset.range N,
                    φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3
                  * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)))
              + 6 * ((∑ k ∈ Finset.range N,
                    φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
                  * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2)) ∂μ
            + ∫ ω, 4 * ((∑ k ∈ Finset.range N,
                  φ k ω * (B (s (k + 1)) ω - B (s k) ω))
                * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 3) ∂μ)
            + ∫ ω, (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 ∂μ :=
            by rw [integral_add hintBIG3 (hintSY3.const_mul 4)]
        _ = ((∫ ω, ((∑ k ∈ Finset.range N,
                φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4
              + 4 * ((∑ k ∈ Finset.range N,
                    φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3
                  * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)))) ∂μ
            + ∫ ω, 6 * ((∑ k ∈ Finset.range N,
                  φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
                * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2) ∂μ)
            + ∫ ω, 4 * ((∑ k ∈ Finset.range N,
                  φ k ω * (B (s (k + 1)) ω - B (s k) ω))
                * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 3) ∂μ)
            + ∫ ω, (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 ∂μ :=
            by rw [integral_add hintBIG2 (hintZY2.const_mul 6)]
        _ = (((∫ ω, (∑ k ∈ Finset.range N,
                φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4 ∂μ
            + ∫ ω, 4 * ((∑ k ∈ Finset.range N,
                  φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3
                * (φ N ω * (B (s (N + 1)) ω - B (s N) ω))) ∂μ)
            + ∫ ω, 6 * ((∑ k ∈ Finset.range N,
                  φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
                * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2) ∂μ)
            + ∫ ω, 4 * ((∑ k ∈ Finset.range N,
                  φ k ω * (B (s (k + 1)) ω - B (s k) ω))
                * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 3) ∂μ)
            + ∫ ω, (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 ∂μ :=
            by rw [integral_add hintZ4 (hintZY0.const_mul 4)]
        _ = ∫ ω, (∑ k ∈ Finset.range N,
                φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4 ∂μ
              + 6 * ∫ ω, (∑ k ∈ Finset.range N,
                    φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
                  * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2 ∂μ
              + ∫ ω, (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 ∂μ := by
            rw [integral_const_mul, integral_const_mul, integral_const_mul]
            rw [hZY0, hY30]
            ring
    -- the real-form IH (the ∫⁻ ihN converted through the internal integrability)
    have ihNreal : ∫ ω, (∑ k ∈ Finset.range N,
        φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4 ∂μ
        ≤ 3 * (D ^ 2 * ∑ k ∈ Finset.range N, ((s (k + 1) : ℝ) - s k)) ^ 2 := by
      have h1 : ENNReal.ofReal (∫ ω, (∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4 ∂μ)
          = ∫⁻ ω, ENNReal.ofReal ((∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hintZ4
          (Eventually.of_forall fun ω ↦ show (0:ℝ) ≤ (∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4 from by positivity)
      have h2 := ihN
      rw [← h1] at h2
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2
    -- assemble (real form)
    have hreal : ∫ ω, (∑ k ∈ Finset.range (N + 1),
        φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4 ∂μ
      ≤ 3 * (D ^ 2 * ∑ k ∈ Finset.range (N + 1), ((s (k + 1) : ℝ) - s k)) ^ 2 := by
      rw [hgapexpan, integral_congr_ae (Eventually.of_forall hexpan4)]
      calc ∫ ω, ((∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω))
            + φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 ∂μ
          = ∫ ω, (∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4 ∂μ
            + 6 * ∫ ω, (∑ k ∈ Finset.range N,
                φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
              * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2 ∂μ
            + ∫ ω, (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 ∂μ := hexp
        _ ≤ 3 * (D ^ 2 * ∑ k ∈ Finset.range N, ((s (k + 1) : ℝ) - s k)) ^ 2
            + 6 * ((D ^ 2 * (D ^ 2 * ∑ k ∈ Finset.range N, ((s (k + 1) : ℝ) - s k)))
              * ((s (N + 1) : ℝ) - s N))
            + 3 * (D ^ 2 * ((s (N + 1) : ℝ) - s N)) ^ 2 :=
            add_le_add (add_le_add ihNreal
              (mul_le_mul_of_nonneg_left hZY2le (by norm_num))) hy4le
        _ = 3 * (D ^ 2 * ((∑ k ∈ Finset.range N, ((s (k + 1) : ℝ) - s k))
              + ((s (N + 1) : ℝ) - s N))) ^ 2 := by
            ring
    -- integrability of the step sum's fourth power, and the ∫⁻ conversion
    have hintS : Integrable (fun ω ↦ (∑ k ∈ Finset.range (N + 1),
        φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4) μ := by
      refine (hintBIG4.add hintYN4).congr (Eventually.of_forall fun ω ↦ ?_)
      simp only [Pi.add_apply]
      rw [hexpan4 ω]
      ring
    rw [← ofReal_integral_eq_lintegral_ofReal hintS
      (Eventually.of_forall fun ω ↦ show (0:ℝ) ≤ (∑ k ∈ Finset.range (N + 1),
        φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4 from by positivity)]
    exact ENNReal.ofReal_le_ofReal hreal
omit hB hδcont hMadap hMeq in
/-- The step-approximant process value at a grid point of its own partition, as the
running Itô sum (the range form of `itoSimpleProcess_stepσ_incr`). -/
private theorem stepValue_eq_sum {m J : ℕ} (hJm : J ≤ m) (ω : Ω) :
    itoSimpleProcess hBmeas (stepσ hBmeas hδadap hδbdd T m).val (unifPart T m J) ω
      = ∑ j ∈ Finset.range J, δ (unifPart T m j) ω
          * (B (unifPart T m (j + 1)) ω - B (unifPart T m j) ω) := by
  induction J with
  | zero =>
    have h0 : unifPart T m 0 = 0 := by
      simp only [unifPart, Nat.cast_zero, zero_div, zero_mul]
    rw [h0]
    simp
  | succ J ihJ =>
    have hJm' : J < m := Nat.lt_of_succ_le hJm
    have hincr := itoSimpleProcess_stepσ_incr hBmeas hδadap hδbdd T (n := m) (k := J) hJm' ω
    rw [Finset.sum_range_succ, ← ihJ (Nat.le_of_succ_le hJm)]
    rw [show itoSimpleProcess hBmeas (stepσ hBmeas hδadap hδbdd T m).val
          (unifPart T m (J + 1)) ω
        = itoSimpleProcess hBmeas (stepσ hBmeas hδadap hδbdd T m).val (unifPart T m J) ω
          + δ (unifPart T m J) ω
            * (B (unifPart T m (J + 1)) ω - B (unifPart T m J) ω) from by rw [← hincr]; ring]

omit hMadap hMeq in
/-- **The `∫⁻` fourth-moment bound** for the CLM increment over a uniform cell (the Fatou
passage from the step approximants):
`∫⁻ ω, ENNReal.ofReal ((CLM_v − CLM_u) ω ^ 4) ∂μ ≤ ENNReal.ofReal (3·(D_δ²·cell)²)`.
Route: refine each cell into `2^p` sub-cells (the grid `m = n·2^p` contains the cell
endpoints), so the step-approximant band increment is exactly an Itô sum over consecutive
refined grid points (`stepSum_pow4_le` bounds its fourth moment uniformly in `p`); the `L²`
contraction (`itoProcessCLM_norm_le`) plus `deltaStepLp_tendsto` converge the increments in
measure, an a.e. subsequence (`TendstoInMeasure.exists_seq_tendsto_ae`) and Fatou
(`lintegral_liminf_le'`) pass the bound to the true increment. The `∫⁻` form is the honest
one: it feeds both the `Integrable` extraction and the real-integral bound. -/
private theorem trueIncr_pow4_lintegral_le {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k < n) :
    ∫⁻ ω, ENNReal.ofReal
        ((((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              (processToLp T hBmeas hδadap hδcont hδbdd)
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              (processToLp T hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4) ∂μ
      ≤ ENNReal.ofReal (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2) := by
  -- grid arithmetic: the refined partition `m = n·2^p` contains the cell endpoints
  have hgrid : ∀ (p j : ℕ), unifPart T (n * 2 ^ p) (2 ^ p * j) = unifPart T n j := by
    intro p j
    have hn0 : ((n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
    have h2r : (2 : ℝ) ^ p ≠ 0 := pow_ne_zero _ (by norm_num)
    refine NNReal.coe_injective ?_
    push_cast [unifPart]
    field_simp [hn0, h2r]
  have hJ1le : ∀ p : ℕ, 2 ^ p * k ≤ n * 2 ^ p := fun p ↦
    (Nat.mul_le_mul (le_refl (2 ^ p)) hk.le).trans_eq (Nat.mul_comm (2 ^ p) n)
  have hJ2le : ∀ p : ℕ, 2 ^ p * (k + 1) ≤ n * 2 ^ p := fun p ↦
    (Nat.mul_le_mul (le_refl (2 ^ p)) hk).trans_eq (Nat.mul_comm (2 ^ p) n)
  -- the a.e. identification of the CLM process of a step embedding
  have hcoe : ∀ (p : ℕ) (t : ℝ≥0),
      (itoProcessCLM hB T t hBmeas (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)) : Ω → ℝ)
        =ᵐ[μ] itoSimpleProcess hBmeas (stepσ hBmeas hδadap hδbdd T (n * 2 ^ p)).val t := by
    intro p t
    rw [show (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p))
          = simpleAssembly_T (μ := μ) T hBmeas
            (stepσ hBmeas hδadap hδbdd T (n * 2 ^ p)) from rfl,
      itoProcessCLM_simpleAssembly_T hB T t hBmeas
        (stepσ hBmeas hδadap hδbdd T (n * 2 ^ p))]
    exact (memLp_itoSimpleProcess hB hBmeas
      (stepσ hBmeas hδadap hδbdd T (n * 2 ^ p)).val t).coeFn_toLp
  -- the refined step-sum identification (a.e.)
  have hsumae : ∀ (p : ℕ),
      (fun ω ↦ (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)) : Ω → ℝ) ω
        - (itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)) : Ω → ℝ) ω)
        =ᵐ[μ] (fun ω ↦ ∑ j ∈ Finset.range (2 ^ p),
            δ (unifPart T (n * 2 ^ p) (2 ^ p * k + j)) ω
              * (B (unifPart T (n * 2 ^ p) (2 ^ p * k + j + 1)) ω
                - B (unifPart T (n * 2 ^ p) (2 ^ p * k + j)) ω)) := by
    intro p
    filter_upwards [hcoe p (unifPart T n (k + 1)), hcoe p (unifPart T n k)] with ω h1 h2
    rw [← hgrid p (k + 1)] at h1
    rw [← hgrid p k] at h2
    have hv1 := stepValue_eq_sum (T := T) hBmeas hδadap hδbdd (hJ2le p) ω
    have hv0 := stepValue_eq_sum (T := T) hBmeas hδadap hδbdd (hJ1le p) ω
    rw [← hgrid p (k + 1), ← hgrid p k, h1, h2, hv1, hv0,
      show ((2:ℕ) ^ p * (k + 1)) = 2 ^ p * k + 2 ^ p from by ring, Finset.sum_range_add,
      add_sub_cancel_left]
  -- the refined-band gap telescopes to the cell length
  have hgapsum : ∀ p : ℕ, ∑ j ∈ Finset.range (2 ^ p),
      ((unifPart T (n * 2 ^ p) (2 ^ p * k + (j + 1)) : ℝ)
        - unifPart T (n * 2 ^ p) (2 ^ p * k + j))
      = ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
    intro p
    rw [sum_telescope (a := fun j : ℕ ↦ ((unifPart T (n * 2 ^ p) (2 ^ p * k + j) : ℝ)))]
    simp only [Nat.add_zero]
    rw [show ((2 : ℕ) ^ p * k + 2 ^ p) = 2 ^ p * (k + 1) from by ring, hgrid p (k + 1),
      hgrid p k]
  -- the per-refinement fourth-moment bound (uniform in `p`, `∫⁻` form)
  have hperp : ∀ p : ℕ,
      ∫⁻ ω, ENNReal.ofReal ((∑ j ∈ Finset.range (2 ^ p),
          δ (unifPart T (n * 2 ^ p) (2 ^ p * k + j)) ω
            * (B (unifPart T (n * 2 ^ p) (2 ^ p * k + (j + 1))) ω
              - B (unifPart T (n * 2 ^ p) (2 ^ p * k + j)) ω)) ^ 4) ∂μ
        ≤ ENNReal.ofReal
          (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2) := by
    intro p
    refine le_trans (stepSum_pow4_le hB hBmeas
      (Monotone.comp (unifPart_mono T (n * 2 ^ p))
        fun i j hij ↦ Nat.add_le_add_left hij (2 ^ p * k))
      (fun j ↦ (hδadap (unifPart T (n * 2 ^ p) (2 ^ p * k + j))).measurable)
      (fun j ω ↦ hδbdd (unifPart T (n * 2 ^ p) (2 ^ p * k + j)) ω) (2 ^ p)) ?_
    show ENNReal.ofReal (3 * (Dd ^ 2 * ∑ j ∈ Finset.range (2 ^ p),
        ((unifPart T (n * 2 ^ p) (2 ^ p * k + (j + 1)) : ℝ)
          - unifPart T (n * 2 ^ p) (2 ^ p * k + j))) ^ 2)
      ≤ ENNReal.ofReal
        (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2)
    rw [hgapsum p]
  -- the `L²` contraction convergence of the band increments
  have hconv : Tendsto (fun p : ℕ ↦
      ‖((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p))
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)))
        - (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd)
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd)) : Lp ℝ 2 μ)‖) atTop (𝓝 0) := by
    have hemb : Tendsto (fun p : ℕ ↦ n * 2 ^ p) atTop atTop := by
      refine Filter.tendsto_atTop_atTop.mpr fun j ↦ ⟨j, fun p hp ↦ ?_⟩
      calc j ≤ p := hp
        _ ≤ 2 ^ p := Nat.lt_two_pow_self.le
        _ ≤ n * 2 ^ p :=
          (Nat.le_mul_of_pos_right (2 ^ p) hn).trans_eq (Nat.mul_comm (2 ^ p) n)
    have hsub := deltaStepLp_tendsto (T := T) hB hBmeas hδadap hδcont hδbdd
    have hFp : Tendsto (fun p : ℕ ↦
        ‖(deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
          - processToLp T hBmeas hδadap hδcont hδbdd :
            Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖) atTop (𝓝 0) :=
      (tendsto_iff_norm_sub_tendsto_zero.mp hsub).comp hemb
    refine squeeze_zero' (Eventually.of_forall fun _p ↦ norm_nonneg _)
      (Eventually.of_forall fun p ↦ ?_)
      (by simpa using hFp.mul (tendsto_const_nhds (x := (2 : ℝ))))
    have hdec : ∀ p : ℕ,
        ((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p))
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)))
        - (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd)
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd)) : Lp ℝ 2 μ)
        = (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
              - processToLp T hBmeas hδadap hδcont hδbdd)
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
              - processToLp T hBmeas hδadap hδcont hδbdd)) := by
      intro p
      simp only [map_sub]
      abel
    rw [hdec p]
    calc ‖(itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
              - processToLp T hBmeas hδadap hδcont hδbdd)
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
              - processToLp T hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ)‖
        ≤ ‖itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
              - processToLp T hBmeas hδadap hδcont hδbdd)‖
          + ‖itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
              - processToLp T hBmeas hδadap hδcont hδbdd)‖ := norm_sub_le _ _
      _ ≤ ‖(deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
              - processToLp T hBmeas hδadap hδcont hδbdd :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖ * 2 := by
          have h1 := itoProcessCLM_norm_le hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
              - processToLp T hBmeas hδadap hδcont hδbdd)
          have h2 := itoProcessCLM_norm_le hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
              - processToLp T hBmeas hδadap hδcont hδbdd)
          have h3 : ‖(deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
                - processToLp T hBmeas hδadap hδcont hδbdd :
                Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖ * 2
              = ‖(deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
                  - processToLp T hBmeas hδadap hδcont hδbdd :
                  Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖
              + ‖(deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
                  - processToLp T hBmeas hδadap hδcont hδbdd :
                  Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖ := by ring
          rw [h3]
          exact add_le_add h1 h2
      _ = _ := rfl
  -- convergence in measure, a.e. subsequence, Fatou
  haveI h2inst : Fact (1 ≤ 2) := ⟨by norm_num⟩
  have hLp : Tendsto (fun p : ℕ ↦
      (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p))
        - itoProcessCLM hB T (unifPart T n k) hBmeas
          (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)) : Lp ℝ 2 μ)) atTop
      (𝓝 (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd)
        - itoProcessCLM hB T (unifPart T n k) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hconv
  have htmi : TendstoInMeasure μ (fun p : ℕ ↦
      ((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p))
        - itoProcessCLM hB T (unifPart T n k) hBmeas
          (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)) : Lp ℝ 2 μ) : Ω → ℝ)) atTop
      ((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd)
        - itoProcessCLM hB T (unifPart T n k) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ) : Ω → ℝ) :=
    tendstoInMeasure_of_tendsto_Lp (p := 2) hLp
  obtain ⟨ns, _hnsmono, hae⟩ := htmi.exists_seq_tendsto_ae
  -- the Fatou functions and their a.e. limit (coe-of-difference forms throughout)
  have hXmeas : ∀ i : ℕ, AEMeasurable
      (fun ω : Ω ↦ ENNReal.ofReal
        ((((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ ns i))
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ ns i)) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4)) μ :=
    fun i ↦ (ENNReal.continuous_ofReal.measurable).comp_aemeasurable
      (AEMeasurable.pow_const
        (Lp.aestronglyMeasurable
          (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ ns i))
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ ns i)) :
            Lp ℝ 2 μ)).aemeasurable 4)
  have hbound : ∀ i : ℕ,
      ∫⁻ ω, ENNReal.ofReal
        ((((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ ns i))
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ ns i)) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4) ∂μ
      ≤ ENNReal.ofReal (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2) := by
    intro i
    have hc : ∀ᵐ ω : Ω ∂μ, ENNReal.ofReal
        ((((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ ns i))
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ ns i)) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4)
        = ENNReal.ofReal ((∑ j ∈ Finset.range (2 ^ ns i),
          δ (unifPart T (n * 2 ^ ns i) (2 ^ ns i * k + j)) ω
            * (B (unifPart T (n * 2 ^ ns i) (2 ^ ns i * k + j + 1)) ω
              - B (unifPart T (n * 2 ^ ns i) (2 ^ ns i * k + j)) ω)) ^ 4) := by
      filter_upwards [Lp.coeFn_sub
          (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ ns i)))
          (itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ ns i))),
        hsumae (ns i)] with ω h1 h2
      rw [h1, Pi.sub_apply, h2]
    rw [lintegral_congr_ae hc]
    exact hperp (ns i)
  have hGmeas : AEMeasurable
      (fun ω : Ω ↦ ENNReal.ofReal
        ((((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              (processToLp T hBmeas hδadap hδcont hδbdd)
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              (processToLp T hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4)) μ :=
    (ENNReal.continuous_ofReal.measurable).comp_aemeasurable
      (AEMeasurable.pow_const
        (Lp.aestronglyMeasurable
          (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              (processToLp T hBmeas hδadap hδcont hδbdd)
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              (processToLp T hBmeas hδadap hδcont hδbdd) :
            Lp ℝ 2 μ)).aemeasurable 4)
  have hlimfun : ∀ᵐ ω : Ω ∂μ,
      ENNReal.ofReal
        ((((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              (processToLp T hBmeas hδadap hδcont hδbdd)
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              (processToLp T hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4)
        = atTop.liminf (fun i : ℕ ↦ ENNReal.ofReal
          ((((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
                (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ ns i))
              - itoProcessCLM hB T (unifPart T n k) hBmeas
                (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ ns i)) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4)) := by
    filter_upwards [hae] with ω hw
    have hcont : Continuous fun x : ℝ ↦ ENNReal.ofReal (x ^ 4) :=
      (ENNReal.continuous_ofReal).comp (continuous_pow (4 : ℕ))
    exact ((hcont.tendsto _).comp hw).liminf_eq.symm
  have hlimint : ∫⁻ ω, ENNReal.ofReal
        ((((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              (processToLp T hBmeas hδadap hδcont hδbdd)
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              (processToLp T hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4) ∂μ
      ≤ ENNReal.ofReal (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2) := by
    rw [lintegral_congr_ae hlimfun]
    refine le_trans (lintegral_liminf_le' fun i ↦ hXmeas i) ?_
    exact Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hbound)
  -- the ∫⁻-bound is the conclusion of the lemma
  exact hlimint

omit hMadap hMeq in
/-- The CLM increment is in `L⁴` (coe-difference form): `AEStronglyMeasurable` from the
`Lp` structure, finiteness from the ∫⁻-bound of `trueIncr_pow4_lintegral_le`
(`hasFiniteIntegral_iff_ofReal` — note the elaboration-order trap of
`ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top …`: the `≠ ⊤` arguments force
`a := ENNReal.ofReal _`, so a lintegral LHS never unifies; stay in the `ofReal` world). -/
private theorem clmIncr_pow4_integrable {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k < n) :
    Integrable (fun ω ↦ (((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd)
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4) μ :=
  ⟨(Lp.aestronglyMeasurable
      (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd)
        - itoProcessCLM hB T (unifPart T n k) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd) :
        Lp ℝ 2 μ)).pow 4,
    by
      rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω ↦ by positivity)]
      exact lt_of_le_of_lt
        (trueIncr_pow4_lintegral_le hB hBmeas hδadap hδcont hδbdd hn k hk)
        ENNReal.ofReal_lt_top⟩

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- Pointwise un-absolutization of the fourth power (even power). -/
private theorem abs4_eq_pow4 (x : ℝ) : |x| ^ 4 = x ^ 4 := by
  rw [← abs_pow]
  exact abs_of_nonneg (by positivity)

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- Pointwise fourth power as a squared square. -/
private theorem sqsq_eq_pow4 (x : ℝ) : (x ^ 2) ^ 2 = x ^ 4 := by
  rw [← pow_mul]

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- Pointwise fourth power as the squared real norm (`ℝ≥0∞`-cast form, for
`integrable_norm_rpow_iff` at `p = 2`; the `(2 : ℝ) = ((2 : ℕ) : ℝ)` pre-rewrite is the
`rpow_natCast` keyed-matching unblock). -/
private theorem pow4_eq_normsq2 (x : ℝ) : x ^ 4 = ‖x ^ 2‖ ^ ((2 : ℕ) : ℝ≥0∞).toReal := by
  have h2r : ((2 : ℕ) : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  rw [h2r, Real.norm_eq_abs, show ((2 : ℝ) = ((2 : ℕ) : ℝ)) from by norm_num,
    Real.rpow_natCast, abs_pow, sq_abs, ← pow_mul]

omit hMadap in
/-- The true increment is in `L⁴` (modifying-process form): the a.e. transfer of
`clmIncr_pow4_integrable` along the `hMeq` congruence. -/
theorem trueIncr_pow4_integrable {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k < n) :
    Integrable (fun ω ↦ |M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω| ^ 4) μ := by
  have hG4 : (fun ω ↦ |M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω| ^ 4)
      =ᵐ[μ] (fun ω ↦ (((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd)
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4) := by
    filter_upwards [hMeq (unifPart T n (k + 1)), hMeq (unifPart T n k),
      Lp.coeFn_sub
        (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd))
        (itoProcessCLM hB T (unifPart T n k) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd))] with ω h1 h0 hsub
    show |M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω| ^ 4 = _
    rw [h1, h0, ← Pi.sub_apply, ← hsub, ← abs_pow]
    exact abs_of_nonneg (by positivity)
  exact (clmIncr_pow4_integrable hB hBmeas hδadap hδcont hδbdd hn k hk).congr hG4.symm

omit hMadap in
/-- **The fourth moment of the true increment** over a uniform cell:
`𝔼[(M_{tₖ₊₁} − M_{tₖ})⁴] ≤ 3·(D_δ²·cell)²` — the a.e. transfer of the CLM ∫⁻-bound to the
modifying process `M`, with the real integral recovered from the ∫⁻-bound by
`ofReal`-injectivity (`ofReal_integral_eq_lintegral_ofReal` +
`ENNReal.ofReal_le_ofReal_iff`). -/
theorem trueIncr_pow4_le {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k < n) :
    ∫ ω, |M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω| ^ 4 ∂μ
      ≤ 3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2 := by
  -- a.e. transfer to the CLM coe-difference
  have hG4 : (fun ω ↦ |M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω| ^ 4)
      =ᵐ[μ] (fun ω ↦ (((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd)
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4) := by
    filter_upwards [hMeq (unifPart T n (k + 1)), hMeq (unifPart T n k),
      Lp.coeFn_sub
        (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd))
        (itoProcessCLM hB T (unifPart T n k) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd))] with ω h1 h0 hsub
    show |M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω| ^ 4 = _
    rw [h1, h0, ← Pi.sub_apply, ← hsub, ← abs_pow]
    exact abs_of_nonneg (by positivity)
  rw [integral_congr_ae hG4]
  have hint4 : Integrable (fun ω ↦ (((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd)
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4) μ :=
    clmIncr_pow4_integrable hB hBmeas hδadap hδcont hδbdd hn k hk
  have hofR : ENNReal.ofReal (∫ ω, (((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd)
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4 ∂μ)
      ≤ ENNReal.ofReal (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint4
      (Eventually.of_forall fun ω ↦ by positivity)]
    exact trueIncr_pow4_lintegral_le hB hBmeas hδadap hδcont hδbdd hn k hk
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg zero_le_three
      (sq_nonneg (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))))).mp hofR

/-- **The third-moment bound** for the true increment (the Taylor-remainder kernel of the
adapted assembly): `𝔼|ΔM|³ ≤ √(3·(D_δ²·cell)³) = O(cell^{3/2})`. Route: Cauchy–Schwarz
interpolation `∫|X|³ = ∫|X·X²| ≤ ‖X‖₂·‖X²‖₂` (the real `L²` pairing
`integral_abs_mul_le_L2L2`), the two factors from `trueIncr_sq_le` and `trueIncr_pow4_le`;
the `L²` memberships from `memLp_M` (for `X`) and from the `L⁴` integrability
(`integrable_norm_rpow_iff` + the pointwise `‖X²‖² = X⁴` identification) for `X²`. -/
theorem trueIncr_pow3_le {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k < n) :
    ∫ ω, |M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω| ^ 3 ∂μ
      ≤ Real.sqrt (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3) := by
  -- the increment and its `L²` membership (from `memLp_M`)
  have hΔ2 : MemLp (fun ω ↦ M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) 2 μ :=
    (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq (unifPart T n (k + 1))).sub
      (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq (unifPart T n k))
  -- the two energy bounds
  have huv : unifPart T n k ≤ unifPart T n (k + 1) :=
    unifPart_mono T n (Nat.le_succ k)
  have hvT : unifPart T n (k + 1) ≤ T :=
    unifPart_le_T (Nat.lt_iff_add_one_le.mp hk)
  have hcellnn : (0:ℝ) ≤ (unifPart T n (k + 1) : ℝ) - unifPart T n k :=
    sub_nonneg.mpr (NNReal.coe_le_coe.mpr huv)
  have hint2 : ∫ ω, (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
      ≤ Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) :=
    trueIncr_sq_le hB hBmeas hδadap hδcont hδbdd hMadap hMeq huv hvT
  -- the fourth moment in un-absolutized form, and its `Integrable` witness (for `X²`)
  have hint4M : Integrable (fun ω ↦
      (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 4) μ :=
    (trueIncr_pow4_integrable hB hBmeas hδadap hδcont hδbdd hMeq hn k hk).congr
      (Eventually.of_forall fun ω ↦ abs4_eq_pow4 _)
  have hint4 : ∫ ω, (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 4 ∂μ
      ≤ 3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2 := by
    refine le_trans (le_of_eq ?_)
      (trueIncr_pow4_le hB hBmeas hδadap hδcont hδbdd hMeq hn k hk)
    exact integral_congr_ae (μ := μ)
      (Eventually.of_forall fun ω ↦ (abs4_eq_pow4 _).symm)
  -- `L²` membership of `X²`: from the `L⁴` integrability via `integrable_norm_rpow_iff`
  have hΔsq2 : MemLp (fun ω ↦
      (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2) 2 μ :=
    (integrable_norm_rpow_iff (hΔ2.1.pow 2) (by norm_num) (by simp)).mp
      (hint4M.congr (Eventually.of_forall fun ω ↦
        show (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 4
          = ‖(M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2‖
              ^ ((2 : ℕ) : ℝ≥0∞).toReal from pow4_eq_normsq2 _))
  -- Cauchy–Schwarz interpolation and the two energy bounds
  calc ∫ ω, |M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω| ^ 3 ∂μ
      = ∫ ω, |(M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
          * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2| ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun ω ↦ ?_)
        show |M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω| ^ 3
          = |(M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
              * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2|
        rw [abs_mul, abs_pow]
        ring
    _ ≤ Real.sqrt (∫ ω, (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)
        * Real.sqrt (∫ ω, (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 4 ∂μ) := by
        refine le_trans (integral_abs_mul_le_L2L2 hΔ2 hΔsq2) ?_
        refine mul_le_mul le_rfl (Real.sqrt_le_sqrt (le_of_eq ?_))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        exact integral_congr_ae (μ := μ)
          (Eventually.of_forall fun ω ↦
            show ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2) ^ 2
              = (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 4 from sqsq_eq_pow4 _)
    _ ≤ Real.sqrt (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
        * Real.sqrt (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt hint2) (Real.sqrt_le_sqrt hint4)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt ((Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
          * (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2)) :=
        (Real.sqrt_mul (mul_nonneg (sq_nonneg Dd) hcellnn)
          (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2)).symm
    _ = Real.sqrt (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3) := by
        rw [show (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
              * (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2)
            = 3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3 from by ring]

end StageFiveB

/-! #### Stage 5c — the martingale kill

Toward the integrated Itô–drift identity for `X_t = c + ∫₀ᵗ β + M_t` (`hXrel`) with bounded
adapted path-continuous `β, δ` and the hypothesized `M`. Route of the assembly: the per-path
discrete Itô formula
(`MathFin.discrete_ito_formula`) at the grid values of `X`, integrated over `Ω`; the
first-order martingale terms die **exactly** (the martingale-kill lemma
`mul_trueIncr_expect_eq_zero` below — the discrete-assembly replacement for "the
stochastic integral has zero mean"); the drift block is the pathwise left-endpoint
Riemann–Stieltjes sum (`AdaptedDrift.tendsto_sum_mul_driftPath_sub` along each path at the
weight `f'∘X` + DCT + the stage-1
Fubini `expectation_pathIntegral_eq`); the quadratic block is `quadraticSqSum_tendsto_uncond` at the
weight `f″∘X` plus the `O(mesh)` drift corrections (`𝔼|ΔM·driftIncr| ≤ 2D_βD_δ·cell^{3/2}`,
`𝔼[driftIncr²] ≤ (D_β·cell)²`, both summed to `O(√mesh)`, `O(mesh)`); the Taylor
remainder dies by `abs_discreteTaylorRemainder_le` + `trueIncr_pow3_le`
(`taylorRemainderSum_tendsto`). -/

section StageFiveC

open MeasureTheory ProbabilityTheory Filter Topology ItoIntegralProcessGeneral
open ItoIntegralL2 ItoIntegralCLM ItoIntegralRiemannBridge ItoIsometryAdapted
open ItoIntegralProcess QuadraticVariationL2 MathFin
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
  {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
  (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
  (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
  (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
  {M : ℝ≥0 → Ω → ℝ}
  (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
  (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
    (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))

include hB hBmeas hδadap hδcont hδbdd hMadap hMeq

/-- **The martingale-kill lemma** (the exact first-order cross-term zero of the adapted
assembly): for `h` bounded and `𝓕_u`-measurable, `u ≤ v`,

  `𝔼[h·(M_v − M_u)] = 0`.

Route: the conditional expectation of the increment dies
(`μ[M_v | 𝓕_u] =ᵐ M_u` — the `incrementEnergy` martingale congruence, from
`itoIntegralProcessGen_isMartingale` through the a.e. `hMeq` transfer; `condExp_sub`),
then the tower pull-out `integral_mul_condExp_eq` and the vanishing integrand. -/
theorem mul_trueIncr_expect_eq_zero {u v : ℝ≥0} (huv : u ≤ v)
    {h : Ω → ℝ} {Ch : ℝ}
    (hmadap : StronglyMeasurable[natFiltration hBmeas u] h)
    (hbdd : ∀ ω, |h ω| ≤ Ch) :
    ∫ ω, h ω * (M v ω - M u ω) ∂μ = 0 := by
  -- integrability of the increment and of the bounded product
  have hincr : Integrable (fun ω ↦ M v ω - M u ω) μ :=
    ((memLp_M hB hBmeas hδadap hδcont hδbdd hMeq v).sub
      (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq u)).integrable one_le_two
  have hMu : StronglyMeasurable (M u) :=
    (hMadap u).mono ((natFiltration hBmeas).le u)
  have hMv : StronglyMeasurable (M v) :=
    (hMadap v).mono ((natFiltration hBmeas).le v)
  have hhmeas : AEStronglyMeasurable (fun ω ↦ h ω * (M v ω - M u ω)) μ :=
    (hmadap.mono ((natFiltration hBmeas).le u)).mul (hMv.sub hMu) |>.aestronglyMeasurable
  have hprod : Integrable (fun ω ↦ h ω * (M v ω - M u ω)) μ :=
    Integrable.mono' (hincr.abs.const_mul Ch) hhmeas
      (Eventually.of_forall fun ω ↦ by
        show ‖h ω * (M v ω - M u ω)‖ ≤ Ch * |M v ω - M u ω|
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hbdd ω) (abs_nonneg _))
  -- the martingale congruences: `μ[M v | 𝓕_u] =ᵐ M u` and `μ[M u | 𝓕_u] =ᵐ M u`
  have hmartv : μ[M v | natFiltration hBmeas u] =ᵐ[μ] M u :=
    condExp_congr_ae (hMeq v) |>.trans
      ((itoIntegralProcessGen_isMartingale hB T hBmeas
        (processToLp T hBmeas hδadap hδcont hδbdd) huv).trans (hMeq u).symm)
  have hmartu : μ[M u | natFiltration hBmeas u] =ᵐ[μ] M u :=
    condExp_congr_ae (hMeq u) |>.trans
      ((itoIntegralProcessGen_isMartingale hB T hBmeas
        (processToLp T hBmeas hδadap hδcont hδbdd) (le_refl u)).trans (hMeq u).symm)
  -- so the conditional expectation of the increment is zero
  have hcond : μ[(M v - M u) | natFiltration hBmeas u]
      =ᵐ[μ] (fun _ ↦ (0 : ℝ)) := by
    have hsub := condExp_sub
      ((memLp_M hB hBmeas hδadap hδcont hδbdd hMeq v).integrable one_le_two)
      ((memLp_M hB hBmeas hδadap hδcont hδbdd hMeq u).integrable one_le_two)
      (natFiltration hBmeas u)
    refine hsub.trans ?_
    filter_upwards [hmartv, hmartu] with ω h1 h2
    show μ[M v | natFiltration hBmeas u] ω - μ[M u | natFiltration hBmeas u] ω = 0
    rw [h1, h2]
    ring
  -- the tower pull-out kills the term
  have hcongr : (fun ω ↦ h ω * μ[(M v - M u) |
        natFiltration hBmeas u] ω) =ᵐ[μ] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [hcond] with ω hc
    show h ω * μ[(M v - M u) | natFiltration hBmeas u] ω = 0
    rw [hc]
    ring
  calc ∫ ω, h ω * (M v ω - M u ω) ∂μ
      = ∫ ω, h ω * μ[(M v - M u) | natFiltration hBmeas u] ω ∂μ :=
        integral_mul_condExp_eq ((natFiltration hBmeas).le u) hmadap hprod hincr
    _ = ∫ ω, (fun _ ↦ (0 : ℝ)) ω ∂μ := integral_congr_ae (μ := μ) hcongr
    _ = 0 := by simp

end StageFiveC

/-! #### Stage 5d — the adapted assembly (`itoDrift_expectation_identity_adapted`)

The integrated Itô–drift identity for `X_t = c + ∫₀ᵗ β + M_t` with bounded adapted
path-continuous `β, δ`, under the hypotheses on `M` and `X` of the module docstring:

  `𝔼[f(X_T)] = 𝔼[f(X_0)] + ∫₀ᵀ 𝔼[f'(X_s)·β_s + ½·f''(X_s)·δ_s²] ds`,

for `f` three times differentiable with `f'`, `f''`, `f'''` bounded. Route: the per-path
discrete Itô formula (`MathFin.discrete_ito_formula`) at the grid values of `X`, integrated
over `Ω`; the first-order martingale terms die exactly (`mul_trueIncr_expect_eq_zero`); the
drift block converges by pathwise Riemann–Stieltjes sums
(`AdaptedDrift.tendsto_sum_mul_driftPath_sub` along each path at the weight `f'∘X`) + DCT
(`driftBlock_tendsto`); the quadratic block converges by `quadraticSqSum_tendsto_uncond`
at the weight `f''∘X`, with the drift–martingale cross terms (`quadCrossSum_tendsto`)
and the drift² corrections (`quadDriftSqSum_tendsto`) tending to `0`; the Taylor remainder dies by
`abs_discreteTaylorRemainder_le` + `trueIncr_pow3_le` (`taylorRemainderSum_tendsto`).
The two drift integrals cross the expectation by the stage-1 Fubini lemma
`expectation_pathIntegral_eq`. -/

section StageFiveD

open MeasureTheory ProbabilityTheory Filter Topology ItoIntegralProcessGeneral
open ItoIntegralL2 ItoIntegralCLM ItoIntegralRiemannBridge ItoIsometryAdapted
open ItoIntegralProcess QuadraticVariationL2 ItoIntegralBrownian AdaptedDrift MathFin
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
  {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
  (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
  (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
  (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
  {M : ℝ≥0 → Ω → ℝ}
  (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
  (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
    (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))

include hB hBmeas hδadap hδcont hδbdd hMadap hMeq

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- Pointwise `|a − b| ≤ |a| + |b|` (the triangle instance for differences). -/
private theorem abs_le_abs_add {a b : ℝ} : |a - b| ≤ |a| + |b| :=
  abs_sub_le a 0 b |>.trans (by simp)

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- `(a + b)³ ≤ 4·(a³ + b³)` for `a, b ≥ 0` — the Taylor-remainder kernel
(sharp at `a = b`, from `4·(a³+b³) − (a+b)³ = 3·(a−b)²·(a+b) ≥ 0`). -/
private theorem pow3_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
  have hsq : (0 : ℝ) ≤ (a - b) ^ 2 := sq_nonneg _
  have e : 4 * (a ^ 3 + b ^ 3) - (a + b) ^ 3 = 3 * (a - b) ^ 2 * (a + b) := by ring
  have hnn : (0 : ℝ) ≤ 3 * (a - b) ^ 2 * (a + b) :=
    mul_nonneg (by nlinarith) (add_nonneg ha hb)
  linarith

omit hB hδadap hδcont hδbdd hMadap hMeq in
/-- **Joint continuity of the mean absolute increment of `β`**: the two-variable mean
function `(s, u) ↦ 𝔼|β s − β u|` is continuous. Route: the one-variable slices are
continuous by the stage-4 mean-continuity DCT (`continuous_mean_of_bdd_cont`), and the
coupling `|𝔼|β s − β u| − 𝔼|β s₀ − β u₀|| ≤ 𝔼|β u₀ − β u| + |𝔼|β s − β u₀| −
𝔼|β s₀ − β u₀||` (the value-level reverse triangle `abs_sub_le`, with
`abs_abs_sub_abs_le_abs_sub` under the first integral) reduces joint continuity at
`(s₀, u₀)` to the two slice continuities, noting `𝔼|β u₀ − β u₀| = 0`. -/
private theorem continuous_jointMeanAbsDiff {β : ℝ≥0 → Ω → ℝ}
    (hβadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (β t))
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 ↦ ∫ ω, |β p.1 ω - β p.2 ω| ∂μ) := by
  have hβmeas : ∀ s : ℝ≥0, Measurable (β s) :=
    fun s ↦ ((hβadap s).measurable.mono ((natFiltration hBmeas).le s) le_rfl)
  have hDb : ∀ s ω, |β s ω| ≤ |Db| := fun s ω ↦ (hβbdd s ω).trans (le_abs_self Db)
  -- the two one-variable slices (via the stage-4 mean-continuity DCT)
  have hcont1 : ∀ u₀ : ℝ≥0, Continuous (fun s : ℝ≥0 ↦ ∫ ω, |β s ω - β u₀ ω| ∂μ) :=
    fun u₀ ↦ continuous_mean_of_bdd_cont (fun s ↦ (hβmeas s).sub (hβmeas u₀) |>.abs)
      (fun ω ↦ ((hβcont ω).sub continuous_const).abs)
      (fun s ω ↦ by
        have h1 : |β s ω - β u₀ ω| ≤ 2 * |Db| := by
          have h2 := abs_le_abs_add (a := β s ω) (b := β u₀ ω)
          linarith [hDb s ω, hDb u₀ ω]
        calc |(|β s ω - β u₀ ω|)| = |β s ω - β u₀ ω| := abs_of_nonneg (abs_nonneg _)
          _ ≤ 2 * |Db| := h1)
  have hcont2 : ∀ s₀ : ℝ≥0, Continuous (fun u : ℝ≥0 ↦ ∫ ω, |β s₀ ω - β u ω| ∂μ) :=
    fun s₀ ↦ continuous_mean_of_bdd_cont (fun u ↦ (hβmeas s₀).sub (hβmeas u) |>.abs)
      (fun ω ↦ (continuous_const.sub (hβcont ω)).abs)
      (fun u ω ↦ by
        have h1 : |β u ω - β s₀ ω| ≤ 2 * |Db| := by
          have h2 := abs_le_abs_add (a := β s₀ ω) (b := β u ω)
          rw [abs_sub_comm (β s₀ ω) (β u ω)] at h2
          linarith [hDb s₀ ω, hDb u ω]
        calc |(|β s₀ ω - β u ω|)| = |β s₀ ω - β u ω| := abs_of_nonneg (abs_nonneg _)
          _ = |β u ω - β s₀ ω| := abs_sub_comm _ _
          _ ≤ 2 * |Db| := h1)
  -- the integral-level coupling: differencing through the `s`-slice
  have hstep1 : ∀ x y z : ℝ≥0,
      |(∫ ω, |β x ω - β y ω| ∂μ) - ∫ ω, |β x ω - β z ω| ∂μ|
        ≤ ∫ ω, |β z ω - β y ω| ∂μ := by
    intro x y z
    have hint : ∀ p q : ℝ≥0, Integrable (fun ω ↦ |β p ω - β q ω|) μ := by
      intro p q
      exact Integrable.of_bound (((hβmeas p).sub (hβmeas q)).abs.aestronglyMeasurable)
        (2 * |Db|)
        (Eventually.of_forall fun ω ↦ by
          have h2 : |β p ω - β q ω| ≤ 2 * |Db| := by
            have h3 := abs_le_abs_add (a := β p ω) (b := β q ω)
            linarith [hDb p ω, hDb q ω]
          show ‖|β p ω - β q ω|‖ ≤ 2 * |Db|
          rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
          exact h2)
    calc |(∫ ω, |β x ω - β y ω| ∂μ) - ∫ ω, |β x ω - β z ω| ∂μ|
        = |∫ ω, (|β x ω - β y ω| - |β x ω - β z ω|) ∂μ| := by
          rw [← integral_sub (hint x y) (hint x z)]
      _ ≤ ∫ ω, abs (|β x ω - β y ω| - |β x ω - β z ω|) ∂μ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ ω, |β z ω - β y ω| ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ abs_nonneg _)
            (hint z y) ?_
          filter_upwards [] with ω
          have h3 := abs_abs_sub_abs_le_abs_sub
            (a := β x ω - β y ω) (b := β x ω - β z ω)
          rw [sub_sub_sub_cancel_left] at h3
          exact h3
  -- joint continuity from the two slice continuities and the coupling
  refine continuous_iff_continuousAt.mpr fun p₀ ↦ ?_
  obtain ⟨s₀, u₀⟩ := p₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δu, hδu, hδuc⟩ := Metric.continuousAt_iff.mp
    ((hcont2 u₀).continuousAt) (ε / 2) (by positivity)
  obtain ⟨δs, hδs, hδsc⟩ := Metric.continuousAt_iff.mp
    ((hcont1 u₀).continuousAt) (ε / 2) (by positivity)
  refine ⟨min δs δu, lt_min hδs hδu, fun p hp ↦ ?_⟩
  obtain ⟨s, u⟩ := p
  have hps : dist s s₀ < δs :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_left (α := ℝ) _ _) hp) (min_le_left _ _)
  have hpu : dist u u₀ < δu :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_right (α := ℝ) _ _) hp) (min_le_right _ _)
  -- the `u`-slice: `𝔼|β u₀ − β u| < ε/2` (the diagonal value is `0`)
  have h2val : ∫ ω, |β u₀ ω - β u₀ ω| ∂μ = 0 := by
    have hz : (fun ω : Ω ↦ |β u₀ ω - β u₀ ω|) = fun _ : Ω ↦ (0 : ℝ) := by
      funext ω; rw [sub_self, abs_zero]
    rw [hz, integral_zero]
  have hterm1 : ∫ ω, |β u₀ ω - β u ω| ∂μ < ε / 2 := by
    have h := hδuc hpu
    rw [Real.dist_eq, h2val, sub_zero,
      abs_of_nonneg (integral_nonneg fun ω ↦ abs_nonneg _)] at h
    exact h
  -- the `s`-slice term and the assembly
  have hterm2 : |(∫ ω, |β s ω - β u₀ ω| ∂μ) - ∫ ω, |β s₀ ω - β u₀ ω| ∂μ| < ε / 2 := by
    have h := hδsc hps
    rw [Real.dist_eq] at h
    exact h
  calc |(∫ ω, |β s ω - β u ω| ∂μ) - ∫ ω, |β s₀ ω - β u₀ ω| ∂μ|
      ≤ |(∫ ω, |β s ω - β u ω| ∂μ) - ∫ ω, |β s ω - β u₀ ω| ∂μ|
          + |(∫ ω, |β s ω - β u₀ ω| ∂μ) - ∫ ω, |β s₀ ω - β u₀ ω| ∂μ| :=
        abs_sub_le (∫ ω, |β s ω - β u ω| ∂μ) (∫ ω, |β s ω - β u₀ ω| ∂μ)
          (∫ ω, |β s₀ ω - β u₀ ω| ∂μ)
    _ ≤ ∫ ω, |β u₀ ω - β u ω| ∂μ
          + |(∫ ω, |β s ω - β u₀ ω| ∂μ) - ∫ ω, |β s₀ ω - β u₀ ω| ∂μ| :=
        add_le_add (hstep1 s u u₀) le_rfl
    _ < ε := by rw [← add_halves ε]; exact add_lt_add hterm1 hterm2

omit hB hδadap hδcont hδbdd hMadap hMeq in
/-- **The drift-cell oscillation sum dies**: the summed mean-oscillation of `β` over the
uniform cells, `∑_{k<n} ∫_{cellₖ} 𝔼|β_s − β_{tₖ}| ds`, tends to `0` as the mesh `T/n → 0`.
Not used by the headline, whose drift block goes through `driftSum_expect_tendsto`.

Route: the joint mean function `(s, u) ↦ 𝔼|β s − β u|` is continuous
(`continuous_jointMeanAbsDiff`), hence uniformly continuous on the compact square `[0,T]²`
(Heine–Cantor, `IsCompact.uniformContinuousOn_of_continuous`); on a cell of mesh `< δ` the
mean is within `ε` of the diagonal value `𝔼|β_{tₖ} − β_{tₖ}| = 0`, and the cell lengths
telescope to `T`. -/
theorem driftOscSum_tendsto {β : ℝ≥0 → Ω → ℝ}
    (hβadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (β t))
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db) (T : ℝ≥0) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
        ∫ s in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)),
          (∫ ω, |β s ω - β (unifPart T n k) ω| ∂μ) ∂ItoIntegralL2.timeMeasure)
      atTop (𝓝 0) := by
  have hjoint : Continuous (fun p : ℝ≥0 × ℝ≥0 ↦ ∫ ω, |β p.1 ω - β p.2 ω| ∂μ) :=
    continuous_jointMeanAbsDiff hBmeas hβadap hβcont hβbdd
  -- the `s`-slice of the joint mean (the per-cell integrand family)
  have hslice : ∀ u₀ : ℝ≥0, Continuous (fun s : ℝ≥0 ↦ ∫ ω, |β s ω - β u₀ ω| ∂μ) :=
    fun u₀ ↦ hjoint.comp (Continuous.prodMk_left u₀)
  have hDb : ∀ s ω, |β s ω| ≤ |Db| := fun s ω ↦ (hβbdd s ω).trans (le_abs_self Db)
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨δ, hδ0, hδc⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
      hjoint.continuousOn) (ε / ((T : ℝ) + 1)) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt ((T : ℝ) / δ)
  refine ⟨max N 1, fun n hn ↦ ?_⟩
  have hn1 : 0 < n := lt_of_lt_of_le one_pos (le_trans (le_max_right N 1) hn)
  have hnN : N ≤ n := le_trans (le_max_left N 1) hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn1.ne'
  have hNn : (↑N : ℝ) ≤ (↑n : ℝ) := by exact_mod_cast hnN
  have hgb : ∀ (k : ℕ) (s : ℝ≥0) (ω : Ω),
      |β s ω - β (unifPart T n k) ω| ≤ 2 * |Db| := by
    intro k s ω
    have h2 := abs_le_abs_add (a := β s ω) (b := β (unifPart T n k) ω)
    linarith [hDb s ω, hDb (unifPart T n k) ω]
  have hgk_le : ∀ (k : ℕ) (s : ℝ≥0),
      (∫ ω, |β s ω - β (unifPart T n k) ω| ∂μ) ≤ 2 * |Db| := by
    intro k s
    refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ abs_nonneg _)
      (integrable_const (2 * |Db|))
      (Eventually.of_forall fun ω ↦ hgb k s ω)) ?_
    rw [integral_const]
    simp
  have hcellint : ∀ k : ℕ, k < n → IntegrableOn
      (fun s : ℝ≥0 ↦ ∫ ω, |β s ω - β (unifPart T n k) ω| ∂μ)
      (Set.Ioc (unifPart T n k) (unifPart T n (k + 1))) ItoIntegralL2.timeMeasure := by
    intro k hk
    haveI : IsFiniteMeasure
        (ItoIntegralL2.timeMeasure.restrict (Set.Ioc (unifPart T n k)
          (unifPart T n (k + 1)))) :=
      ⟨by
        rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          ItoIntegralL2.timeMeasure_Ioc]
        exact ENNReal.ofReal_lt_top⟩
    exact Integrable.of_bound
      (μ := ItoIntegralL2.timeMeasure.restrict (Set.Ioc (unifPart T n k)
        (unifPart T n (k + 1))))
      (((hslice (unifPart T n k)).measurable.aestronglyMeasurable).mono_measure
        Measure.restrict_le_self)
      (2 * |Db|)
      (Eventually.of_forall fun s ↦ by
        show ‖∫ ω, |β s ω - β (unifPart T n k) ω| ∂μ‖ ≤ 2 * |Db|
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ω ↦ abs_nonneg _)]
        exact hgk_le k s)
  have hmesh : (T : ℝ) / (n : ℝ) < δ := by
    rw [div_lt_iff₀ (by exact_mod_cast hn1 : (0 : ℝ) < (n : ℝ)), mul_comm]
    exact (div_lt_iff₀ hδ0).mp (lt_of_lt_of_le hN hNn)
  -- per-cell: the mean is within `ε/(T+1)` of the vanishing diagonal
  have hcell : ∀ k : ℕ, k < n →
      ∫ s in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)),
          (∫ ω, |β s ω - β (unifPart T n k) ω| ∂μ) ∂ItoIntegralL2.timeMeasure
        ≤ (ε / ((T : ℝ) + 1)) * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
    intro k hk
    haveI : IsFiniteMeasure
        (ItoIntegralL2.timeMeasure.restrict (Set.Ioc (unifPart T n k)
          (unifPart T n (k + 1)))) :=
      ⟨by
        rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          ItoIntegralL2.timeMeasure_Ioc]
        exact ENNReal.ofReal_lt_top⟩
    have hkt : unifPart T n k ≤ T := unifPart_le_T (Nat.le_of_lt hk)
    have hkt1 : unifPart T n (k + 1) ≤ T := unifPart_le_T (Nat.succ_le_of_lt hk)
    have huv : unifPart T n k ≤ unifPart T n (k + 1) := unifPart_mono T n (Nat.le_succ k)
    have hcellen : ((unifPart T n (k + 1) : ℝ) - unifPart T n k) = (T : ℝ) / (n : ℝ) := by
      simp only [unifPart]
      push_cast
      field_simp
      ring
    have hdiag : (∫ ω, |β (unifPart T n k) ω - β (unifPart T n k) ω| ∂μ) = 0 := by
      have hz : (fun ω : Ω ↦ |β (unifPart T n k) ω - β (unifPart T n k) ω|)
          = fun _ : Ω ↦ (0 : ℝ) := by
        funext ω; rw [sub_self, abs_zero]
      rw [hz, integral_zero]
    have hpt : ∀ s ∈ Set.Ioc (unifPart T n k) (unifPart T n (k + 1)),
        (∫ ω, |β s ω - β (unifPart T n k) ω| ∂μ) ≤ ε / ((T : ℝ) + 1) := by
      intro s hs
      have hst : unifPart T n k ≤ s := le_of_lt hs.1
      have hsm : s ≤ unifPart T n (k + 1) := hs.2
      have hge : (0 : ℝ) ≤ (s : ℝ) - ↑(unifPart T n k) := by
        have h1 := NNReal.coe_nonneg (unifPart T n k)
        have h2 := NNReal.coe_le_coe.mpr hst
        linarith
      have hps : dist s (unifPart T n k) < δ := by
        rw [NNReal.dist_eq, abs_of_nonneg hge]
        calc (s : ℝ) - ↑(unifPart T n k)
            ≤ ↑(unifPart T n (k + 1)) - ↑(unifPart T n k) :=
              sub_le_sub_right (by exact_mod_cast hsm) _
          _ = (T : ℝ) / (n : ℝ) := hcellen
          _ < δ := hmesh
      have hmem : (s, unifPart T n k) ∈
          Set.Icc (0:ℝ≥0) T ×ˢ Set.Icc (0:ℝ≥0) T :=
        ⟨⟨le_trans zero_le hst, le_trans hsm hkt1⟩, ⟨le_trans zero_le le_rfl, hkt⟩⟩
      have hmemq : (unifPart T n k, unifPart T n k) ∈
          Set.Icc (0:ℝ≥0) T ×ˢ Set.Icc (0:ℝ≥0) T :=
        ⟨⟨(zero_le : (0:ℝ≥0) ≤ unifPart T n k), hkt⟩,
          ⟨(zero_le : (0:ℝ≥0) ≤ unifPart T n k), hkt⟩⟩
      have hpq : dist (s, unifPart T n k) (unifPart T n k, unifPart T n k) < δ := by
        refine lt_of_le_of_lt ?_ hps
        rw [Prod.dist_eq]
        refine max_le le_rfl ?_
        exact le_trans (le_of_eq (dist_self (unifPart T n k))) dist_nonneg
      have hval := hδc (s, unifPart T n k) hmem (unifPart T n k, unifPart T n k) hmemq hpq
      rw [Real.dist_eq] at hval
      have hval' : (∫ ω, |β s ω - β (unifPart T n k) ω| ∂μ) < ε / ((T : ℝ) + 1) := by
        have h2 : (∫ ω, |β (unifPart T n k) ω - β (unifPart T n k) ω| ∂μ) = 0 := hdiag
        rw [show ∫ ω, |β (s, unifPart T n k).1 ω - β (s, unifPart T n k).2 ω| ∂μ
              = ∫ ω, |β s ω - β (unifPart T n k) ω| ∂μ from rfl,
            show ∫ ω, |β (unifPart T n k, unifPart T n k).1 ω
                - β (unifPart T n k, unifPart T n k).2 ω| ∂μ = 0 from h2,
            sub_zero, abs_of_nonneg (integral_nonneg fun (ω : Ω) ↦
              abs_nonneg (β s ω - β (unifPart T n k) ω))] at hval
        exact hval
      exact le_of_lt hval'
    refine le_trans (setIntegral_mono_on (hcellint k hk) (integrableOn_const
      (hs := ne_of_lt (by
        rw [ItoIntegralL2.timeMeasure_Ioc]
        exact ENNReal.ofReal_lt_top))) measurableSet_Ioc hpt) ?_
    rw [setIntegral_const, smul_eq_mul, measureReal_def, ItoIntegralL2.timeMeasure_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (NNReal.coe_le_coe.mpr huv)), mul_comm]
  -- the cells telescope to `T`
  have hsum : (∑ k ∈ Finset.range n,
      ∫ s in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)),
        (∫ ω, |β s ω - β (unifPart T n k) ω| ∂μ) ∂ItoIntegralL2.timeMeasure)
      ≤ (ε / ((T : ℝ) + 1)) * (T : ℝ) := by
    refine le_trans (Finset.sum_le_sum fun k hk ↦
      hcell k (Finset.mem_range.mp hk)) ?_
    rw [← Finset.mul_sum, sum_telescope (a := fun k : ℕ ↦ ((unifPart T n k : ℝ)))]
    have hnT : unifPart T n n = T := by
      have hne : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hn1.ne'
      simp only [unifPart, div_self hne, one_mul]
    have h0 : unifPart T n 0 = 0 := by simp only [unifPart]; norm_num
    rw [hnT, h0]
    simp
  have hnn0 : (0 : ℝ) ≤ ∑ k ∈ Finset.range n,
      ∫ s in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)),
        (∫ ω, |β s ω - β (unifPart T n k) ω| ∂μ) ∂ItoIntegralL2.timeMeasure :=
    Finset.sum_nonneg fun k _ ↦ integral_nonneg fun (s : ℝ≥0) ↦ integral_nonneg
      (fun (ω : Ω) ↦ abs_nonneg (β s ω - β (unifPart T n k) ω))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn0]
  calc (∑ k ∈ Finset.range n,
        ∫ s in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)),
          (∫ ω, |β s ω - β (unifPart T n k) ω| ∂μ) ∂ItoIntegralL2.timeMeasure)
      ≤ (ε / ((T : ℝ) + 1)) * (T : ℝ) := hsum
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < (T : ℝ) + 1)]
        nlinarith [mul_lt_mul_of_pos_right (lt_add_one (T : ℝ)) hε]

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- **The drift block at the expectation level (DCT)**: the expectations of the per-cell
drift sums — `𝔼[∑ₖ g (X tₖ) · (AdaptedDrift.driftPath β tₖ₊₁ − AdaptedDrift.driftPath β tₖ)]`
— converge to the
expectation of the pathwise limit. Route: per-path Riemann–Stieltjes convergence
(`AdaptedDrift.tendsto_sum_mul_driftPath_sub` with weight `s ↦ g (X s ω)`, bounded by `C₁`)
under the global domination `|S_n| ≤ C₁·|D_β|·T` (the drift primitive is `D_β`-Lipschitz
per cell (`AdaptedDrift.abs_driftPath_sub_le`); the cells telescope to `T`;
`|g| ≤ C₁`). -/
theorem driftSum_expect_tendsto (hBmeas : ∀ t, Measurable (B t))
    {β : ℝ≥0 → Ω → ℝ} {X : ℝ≥0 → Ω → ℝ} (T : ℝ≥0)
    (hβadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (β t))
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db)
    (hXadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (X t))
    (hXcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ X s ω)
    {g : ℝ → ℝ} {C1 : ℝ} (hgcont : Continuous g) (hg1 : ∀ x, |g x| ≤ C1) :
    Tendsto (fun n : ℕ ↦ ∫ ω, ∑ k ∈ Finset.range n, g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ∂μ)
      atTop (𝓝 (∫ ω, (∫ s in Set.Ioc (0:ℝ≥0) T, g (X s ω) * β s ω
        ∂ItoIntegralL2.timeMeasure) ∂μ)) := by
  have hC1 : (0:ℝ) ≤ C1 := le_trans (abs_nonneg _) (hg1 0)
  -- measurability of the summands
  have hXm : ∀ t : ℝ≥0, Measurable (X t) :=
    fun t ↦ (hXadap t).measurable.mono ((natFiltration hBmeas).le t) le_rfl
  have hgx : ∀ t : ℝ≥0, Measurable (fun ω ↦ g (X t ω)) :=
    fun t ↦ hgcont.measurable.comp (hXm t)
  have hdp : ∀ t : ℝ≥0, Measurable (driftPath β t) :=
    fun t ↦ (stronglyMeasurable_driftPath hBmeas hβadap hβcont hβbdd t).measurable.mono
      ((natFiltration hBmeas).le t) le_rfl
  have hmeasS : ∀ n : ℕ, Measurable (fun ω ↦ ∑ k ∈ Finset.range n,
      g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)) :=
    fun n ↦ Finset.measurable_sum _ fun k _ ↦
      (hgx _).mul ((hdp _).sub (hdp _))
  -- the uniform bound `|S_n| ≤ C₁·|D_β|·T`
  have hbound : ∀ n : ℕ, ∀ ω : Ω,
      |∑ k ∈ Finset.range n, g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)|
      ≤ C1 * |Db| * (T : ℝ) := by
    intro n ω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Finset.range_zero, Finset.sum_empty, abs_zero]
      exact mul_nonneg (mul_nonneg hC1 (abs_nonneg Db)) (NNReal.coe_nonneg T)
    · have hnT : unifPart T n n = T := by
        have hne : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
        simp only [unifPart, div_self hne, one_mul]
      have h0 : unifPart T n 0 = 0 := by simp only [unifPart]; norm_num
      calc |∑ k ∈ Finset.range n, g (X (unifPart T n k) ω)
            * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)|
          ≤ ∑ k ∈ Finset.range n, |g (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k ∈ Finset.range n, |g (X (unifPart T n k) ω)|
              * |driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω| :=
            Finset.sum_congr rfl fun k _ ↦ abs_mul _ _
        _ ≤ ∑ k ∈ Finset.range n, C1 * |driftPath β (unifPart T n (k + 1)) ω
              - driftPath β (unifPart T n k) ω| :=
            Finset.sum_le_sum fun k _ ↦
              mul_le_mul_of_nonneg_right (hg1 (X (unifPart T n k) ω)) (abs_nonneg _)
        _ ≤ ∑ k ∈ Finset.range n, C1 * (|Db| * ((unifPart T n (k + 1) : ℝ)
              - unifPart T n k)) :=
            Finset.sum_le_sum fun k hk ↦ by
              refine mul_le_mul_of_nonneg_left ?_ hC1
              have hsub : (0:ℝ) ≤ (unifPart T n (k + 1) : ℝ) - unifPart T n k :=
                sub_nonneg.mpr (NNReal.coe_le_coe.mpr (unifPart_mono T n (Nat.le_succ k)))
              exact (abs_driftPath_sub_le hβcont hβbdd
                (unifPart_mono T n (Nat.le_succ k)) ω).trans
                (mul_le_mul_of_nonneg_right (le_abs_self Db) hsub)
        _ = C1 * |Db| * (T : ℝ) := by
            have hcomm : ∀ k ∈ Finset.range n, C1 * (|Db| * ((unifPart T n (k + 1) : ℝ)
                  - unifPart T n k))
                = (C1 * |Db|) * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) :=
              fun k _ ↦ by ring
            rw [Finset.sum_congr rfl hcomm, ← Finset.mul_sum,
              sum_telescope (a := fun k : ℕ ↦ ((unifPart T n k : ℝ))), hnT, h0,
              NNReal.coe_zero, sub_zero]
  refine tendsto_integral_of_dominated_convergence (fun _ : Ω ↦ C1 * |Db| * (T : ℝ))
    (fun n ↦ (hmeasS n).aestronglyMeasurable) (integrable_const _)
    (fun n ↦ Eventually.of_forall fun ω ↦ by
      simpa [Real.norm_eq_abs] using hbound n ω)
    (Eventually.of_forall fun ω ↦ tendsto_sum_mul_driftPath_sub hβcont hβbdd T ω
      (g := fun s ↦ g (X s ω)) (hgcont.comp (hXcont ω)).continuousOn fun s ↦ hg1 (X s ω))

omit hB hδadap hδcont hδbdd hMadap hMeq in
/-- **The drift block** (`driftBlock_tendsto`): for `X` adapted and path-continuous, `g`
continuous with `|g| ≤ C₁`, and `β` bounded adapted path-continuous, the per-cell drift
sums of the adapted assembly converge to the time-integral of the frozen means,

  `∑ₖ 𝔼[g (X tₖ) · (AdaptedDrift.driftPath β tₖ₊₁ − AdaptedDrift.driftPath β tₖ)]
  → ∫₀ᵀ 𝔼[g (X_s) β_s] ds`.

Route: the DCT convergence `driftSum_expect_tendsto` (per-path Riemann–Stieltjes sums +
global domination) for the expectation-of-sum form, the finite-sum/expectation interchange,
and the stage-1 Fubini lemma `expectation_pathIntegral_eq` crossing the expectation of the
limit integrand. -/
theorem driftBlock_tendsto {β : ℝ≥0 → Ω → ℝ} {X : ℝ≥0 → Ω → ℝ} (T : ℝ≥0)
    (hβadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (β t))
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db)
    (hXadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (X t))
    (hXcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ X s ω)
    {g : ℝ → ℝ} {C1 : ℝ} (hgcont : Continuous g) (hg1 : ∀ x, |g x| ≤ C1) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
        ∫ ω, g (X (unifPart T n k) ω)
          * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ∂μ)
      atTop (𝓝 (∫ s in Set.Ioc (0:ℝ≥0) T,
          (∫ ω, g (X s ω) * β s ω ∂μ) ∂ItoIntegralL2.timeMeasure)) := by
  have hC1 : (0:ℝ) ≤ C1 := le_trans (abs_nonneg _) (hg1 0)
  -- the DCT limit in expectation-of-sum form, bridged to sum-of-expectations form
  have hA : Tendsto (fun n : ℕ ↦ ∫ ω, ∑ k ∈ Finset.range n, g (X (unifPart T n k) ω)
      * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ∂μ)
    atTop (𝓝 (∫ ω, (∫ s in Set.Ioc (0:ℝ≥0) T, g (X s ω) * β s ω
      ∂ItoIntegralL2.timeMeasure) ∂μ)) :=
    driftSum_expect_tendsto hBmeas T hβadap hβcont hβbdd hXadap hXcont hgcont hg1
  have hswap : ∀ n : ℕ, (∑ k ∈ Finset.range n, ∫ ω, g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ∂μ)
      = ∫ ω, ∑ k ∈ Finset.range n, g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ∂μ := by
    intro n
    have hint : ∀ k ∈ Finset.range n, Integrable (fun ω ↦ g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)) μ := by
      intro k hk
      have hXk : Measurable (X (unifPart T n k)) :=
        (hXadap (unifPart T n k)).measurable.mono
          ((natFiltration hBmeas).le (unifPart T n k)) le_rfl
      have hdp1 : Measurable (driftPath β (unifPart T n (k + 1))) :=
        (stronglyMeasurable_driftPath hBmeas hβadap hβcont hβbdd
          (unifPart T n (k + 1))).measurable.mono
          ((natFiltration hBmeas).le (unifPart T n (k + 1))) le_rfl
      have hdp0 : Measurable (driftPath β (unifPart T n k)) :=
        (stronglyMeasurable_driftPath hBmeas hβadap hβcont hβbdd (unifPart T n k)).measurable.mono
          ((natFiltration hBmeas).le (unifPart T n k)) le_rfl
      have hm : Measurable (fun ω ↦ g (X (unifPart T n k) ω)
          * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)) :=
        (hgcont.measurable.comp hXk).mul (hdp1.sub hdp0)
      refine Integrable.of_bound hm.aestronglyMeasurable (C1 * |Db| * (T : ℝ) + 1) ?_
      filter_upwards with ω
      show ‖g (X (unifPart T n k) ω)
          * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)‖
        ≤ C1 * |Db| * (T : ℝ) + 1
      rw [Real.norm_eq_abs, abs_mul]
      have hD : |driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω|
          ≤ |Db| * (T : ℝ) := by
        have hsub : (0:ℝ) ≤ (unifPart T n (k + 1) : ℝ) - unifPart T n k :=
          sub_nonneg.mpr (NNReal.coe_le_coe.mpr (unifPart_mono T n (Nat.le_succ k)))
        have hcellle : (unifPart T n (k + 1) : ℝ) - unifPart T n k ≤ (T : ℝ) := by
          have h1 : ((unifPart T n (k + 1) : ℝ)) ≤ (T : ℝ) :=
            NNReal.coe_le_coe.mpr (unifPart_le_T (Nat.succ_le_of_lt
              (Finset.mem_range.mp hk)))
          have h2 := NNReal.coe_nonneg (unifPart T n k)
          linarith
        exact (abs_driftPath_sub_le hβcont hβbdd
          (unifPart_mono T n (Nat.le_succ k)) ω).trans
          (mul_le_mul (le_abs_self Db) hcellle hsub (abs_nonneg Db))
      refine le_trans
        (mul_le_mul (hg1 (X (unifPart T n k) ω)) hD (abs_nonneg _) hC1) ?_
      linarith
    exact (integral_finsetSum _ hint).symm
  have hB : Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
      ∫ ω, g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ∂μ)
    atTop (𝓝 (∫ ω, (∫ s in Set.Ioc (0:ℝ≥0) T, g (X s ω) * β s ω
      ∂ItoIntegralL2.timeMeasure) ∂μ)) :=
    Tendsto.congr' (Eventually.of_forall fun n ↦ (hswap n).symm) hA
  -- the Fubini interchange on the limit integrand
  have hβm : ∀ t : ℝ≥0, Measurable (β t) :=
    fun t ↦ (hβadap t).measurable.mono ((natFiltration hBmeas).le t) le_rfl
  have hEq := expectation_pathIntegral_eq (μ := μ)
    (w := fun s ω ↦ g (X s ω) * β s ω)
    (fun s ↦ (hgcont.measurable.comp ((hXadap s).measurable.mono
      ((natFiltration hBmeas).le s) le_rfl)).mul (hβm s))
    (fun ω ↦ (hgcont.comp (hXcont ω)).mul (hβcont ω))
    (mul_nonneg hC1 (abs_nonneg Db))
    (fun s ω ↦ by
      rw [abs_mul]
      exact mul_le_mul (hg1 (X s ω)) (le_trans (hβbdd s ω) (le_abs_self Db))
        (abs_nonneg _) hC1)
    T
  rw [← hEq]
  exact hB

/-! #### Stage 5e — the dying blocks of the assembly

Three convergences consumed by `itoDrift_expectation_identity_adapted`; each statement gives
only the limit `0`, and the bounds below are what the proofs establish:

* `quadDriftSqSum_tendsto` — the drift² corrections `O(mesh)`:
  `∑ₖ |𝔼[g (X tₖ)·(Δ(AdaptedDrift.driftPath β))ₖ²]| ≤ 2·C₂·D_β²·T²/(n+1) → 0`;
* `quadCrossSum_tendsto` — the drift–martingale cross corrections `O(√mesh)`:
  `∑ₖ |𝔼[g (X tₖ)·Δ(AdaptedDrift.driftPath β)ₖ·ΔMₖ]| ≤ 2·C₂·D_β·|D_δ|·T·√T/√(n+1) → 0`
  (the `D_β·cell`-bounded drift increment paired against the `D_δ²·cell`-energy
  martingale increment, `trueIncr_sq_le`);
* `taylorRemainderSum_tendsto` — the Taylor remainder: `|𝔼[∑ₖ Rₖ]|` is at most
  `4·C₃·(4·D_β³·T³/(n+1)² + 2·√(3·(D_δ²·T)³)/√(n+1)) → 0`
  (`abs_discreteTaylorRemainder_le` + `pow3_add_le` + `trueIncr_pow3_le`). -/

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- The uniform-cell length: `(tₖ₊₁ − tₖ) = T/n`. -/
private theorem cellLen_eq {T : ℝ≥0} {n : ℕ} (k : ℕ) :
    ((unifPart T n (k + 1) : ℝ) - unifPart T n k) = (T : ℝ) / (n : ℝ) := by
  simp only [unifPart]
  push_cast
  field_simp
  ring

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- The `(n+1)`-divergence and the `1/(n+1)` null sequence over the naturals. -/
private theorem tendsto_nat_add_one_atTop :
    Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)) atTop atTop := by
  refine Filter.tendsto_atTop_atTop.mpr fun x ↦ ⟨Nat.ceil x, fun n hn ↦ ?_⟩
  have h2 : (x : ℝ) ≤ ((Nat.ceil x : ℕ) : ℝ) := Nat.le_ceil x
  have h3 : ((Nat.ceil x : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hn
  linarith

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
private theorem tendsto_one_div_nat_add :
    Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  refine tendsto_nat_add_one_atTop.inv_tendsto_atTop.congr'
    (Eventually.of_forall fun n ↦ ?_)
  show ((n : ℝ) + 1)⁻¹ = (1 : ℝ) / ((n : ℝ) + 1)
  rw [one_div]

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- The `1/√(n+1)` null sequence over the naturals. -/
private theorem tendsto_inv_sqrt_nat_add :
    Tendsto (fun n : ℕ ↦ (1 : ℝ) / Real.sqrt ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun n : ℕ ↦ Real.sqrt ((1 : ℝ) / ((n : ℝ) + 1))) atTop
      (𝓝 (Real.sqrt 0)) :=
    ((Real.continuous_sqrt.tendsto (0 : ℝ)).comp tendsto_one_div_nat_add).congr'
      (Eventually.of_forall fun n ↦ rfl)
  have hsqrt2 : Tendsto (fun n : ℕ ↦ Real.sqrt ((1 : ℝ) / ((n : ℝ) + 1))) atTop
      (𝓝 (0 : ℝ)) := by
    simpa [Real.sqrt_zero] using hsqrt
  refine hsqrt2.congr' (Eventually.of_forall fun n ↦ ?_)
  show Real.sqrt ((1 : ℝ) / ((n : ℝ) + 1)) = (1 : ℝ) / Real.sqrt ((n : ℝ) + 1)
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- **The drift² corrections of the quadratic block die** (`O(mesh)`): the summed absolute
expectations of the frozen weight against the drift-increment squares are at most
`2·C₂·D_β²·T²/(n+1)` — each drift increment is pointwise `D_β·cell`
(`AdaptedDrift.abs_driftPath_sub_le`) and the cells telescope to `T`. -/
theorem quadDriftSqSum_tendsto (hBmeas : ∀ t, Measurable (B t)) {β : ℝ≥0 → Ω → ℝ}
    {X : ℝ≥0 → Ω → ℝ} (T : ℝ≥0)
    (hβadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (β t))
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db)
    (hXadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (X t))
    {g : ℝ → ℝ} {C2 : ℝ} (hgcont : Continuous g) (hg2 : ∀ x, |g x| ≤ C2) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
        ∫ ω, g (X (unifPart T n k) ω)
          * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have hC2 : (0 : ℝ) ≤ C2 := le_trans (abs_nonneg _) (hg2 0)
  -- per-cell absolute bound
  have hcell : ∀ n : ℕ, ∀ k : ℕ,
      |∫ ω, g (X (unifPart T n k) ω)
          * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2 ∂μ|
        ≤ C2 * Db ^ 2 * ((T : ℝ) / (n : ℝ)) ^ 2 := by
    intro n k
    have hXk : Measurable (X (unifPart T n k)) :=
      (hXadap (unifPart T n k)).measurable.mono
        ((natFiltration hBmeas).le (unifPart T n k)) le_rfl
    have hdpm : Measurable (driftPath β (unifPart T n (k + 1))) :=
      (stronglyMeasurable_driftPath hBmeas hβadap hβcont hβbdd
        (unifPart T n (k + 1))).measurable.mono
        ((natFiltration hBmeas).le (unifPart T n (k + 1))) le_rfl
    have hdp0 : Measurable (driftPath β (unifPart T n k)) :=
      (stronglyMeasurable_driftPath hBmeas hβadap hβcont hβbdd
        (unifPart T n k)).measurable.mono
        ((natFiltration hBmeas).le (unifPart T n k)) le_rfl
    have hmeas : Measurable (fun ω ↦ g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2) :=
      (hgcont.measurable.comp hXk).mul ((hdpm.sub hdp0).pow_const 2)
    have hbound : ∀ ω : Ω,
        |g (X (unifPart T n k) ω)
          * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2|
        ≤ C2 * Db ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 2 := by
      intro ω
      have h1 : |g (X (unifPart T n k) ω)| ≤ C2 := hg2 _
      have h2 : |driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω|
          ≤ Db * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) :=
        abs_driftPath_sub_le hβcont hβbdd
          (unifPart_mono T n (Nat.le_succ k)) ω
      have hcellnn : (0 : ℝ) ≤ (unifPart T n (k + 1) : ℝ) - unifPart T n k :=
        sub_nonneg.mpr (NNReal.coe_le_coe.mpr (unifPart_mono T n (Nat.le_succ k)))
      have h3 : (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2
          ≤ (Db * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2 := by
        refine (sq_le_sq).mpr ?_
        rw [abs_mul, abs_of_nonneg hcellnn]
        rcases le_total 0 Db with hDb | hDb
        · rw [abs_of_nonneg hDb]; exact h2
        · rw [abs_of_nonpos hDb]
          have habs : (0 : ℝ) ≤ |driftPath β (unifPart T n (k + 1)) ω
              - driftPath β (unifPart T n k) ω| := abs_nonneg _
          have hnonpos : Db * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hDb hcellnn
          linarith
      rw [abs_mul, abs_pow (a := driftPath β (unifPart T n (k + 1)) ω
        - driftPath β (unifPart T n k) ω) 2, sq_abs]
      calc |g (X (unifPart T n k) ω)|
            * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2
          ≤ C2 * (Db * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2 :=
            mul_le_mul h1 h3 (sq_nonneg _) hC2
        _ = C2 * Db ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 2 := by ring
    have hint : Integrable (fun ω ↦ g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2) μ :=
      Integrable.of_bound hmeas.aestronglyMeasurable
        (C2 * Db ^ 2 * ((T : ℝ) / (n : ℝ)) ^ 2 + 1)
        (Eventually.of_forall fun ω ↦ by
          show ‖g (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω
                - driftPath β (unifPart T n k) ω) ^ 2‖ ≤ _
          rw [Real.norm_eq_abs]
          have h := hbound ω
          rw [cellLen_eq (T := T) (n := n) k] at h
          linarith)
    calc |∫ ω, g (X (unifPart T n k) ω)
            * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2 ∂μ|
        ≤ ∫ ω, |g (X (unifPart T n k) ω)
            * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2| ∂μ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ ω, (C2 * Db ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 2) ∂μ :=
          integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ abs_nonneg _)
            (integrable_const _) (Eventually.of_forall fun ω ↦ hbound ω)
      _ = C2 * Db ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 2 := by
          rw [integral_const]; simp
      _ = C2 * Db ^ 2 * ((T : ℝ) / (n : ℝ)) ^ 2 := by rw [cellLen_eq k]
  -- squeeze: the absolute sums die, hence the signed sums die
  have hboundtendsto : Tendsto (fun n : ℕ ↦ |∑ k ∈ Finset.range n,
      ∫ ω, g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2 ∂μ|)
      atTop (𝓝 0) := by
    refine squeeze_zero' (g := fun n : ℕ ↦ 2 * C2 * Db ^ 2 * (T : ℝ) ^ 2 / ((n : ℝ) + 1))
      (Eventually.of_forall fun n ↦ abs_nonneg _) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      calc |∑ k ∈ Finset.range n,
            ∫ ω, g (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2 ∂μ|
          ≤ ∑ k ∈ Finset.range n,
            |∫ ω, g (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2 ∂μ| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range n, (C2 * Db ^ 2 * ((T : ℝ) / (n : ℝ)) ^ 2) :=
            Finset.sum_le_sum fun k _ ↦ hcell n k
        _ = (n : ℝ) * (C2 * Db ^ 2 * ((T : ℝ) / (n : ℝ)) ^ 2) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ = C2 * Db ^ 2 * (T : ℝ) ^ 2 / (n : ℝ) := by
            field_simp
        _ ≤ 2 * C2 * Db ^ 2 * (T : ℝ) ^ 2 / ((n : ℝ) + 1) := by
            rw [div_le_div_iff₀ (by exact_mod_cast hn : (0 : ℝ) < (n : ℝ))
              (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
            have hK : (0 : ℝ) ≤ C2 * Db ^ 2 * (T : ℝ) ^ 2 := by positivity
            have hnm : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            nlinarith
    · have hzero : ((2 * C2 * Db ^ 2 * (T : ℝ) ^ 2) * (0 : ℝ)) = (0 : ℝ) := mul_zero _
      have h2' : Tendsto (fun n : ℕ ↦ (2 * C2 * Db ^ 2 * (T : ℝ) ^ 2) / ((n : ℝ) + 1))
          atTop (𝓝 ((2 * C2 * Db ^ 2 * (T : ℝ) ^ 2) * 0)) := by
        refine ((tendsto_const_nhds
          (x := (2 * C2 * Db ^ 2 * (T : ℝ) ^ 2))).mul
          tendsto_nat_add_one_atTop.inv_tendsto_atTop).congr'
          (Eventually.of_forall fun n ↦ ?_)
        show (2 * C2 * Db ^ 2 * (T : ℝ) ^ 2) * ((n : ℝ) + 1)⁻¹
          = (2 * C2 * Db ^ 2 * (T : ℝ) ^ 2) / ((n : ℝ) + 1)
        rw [div_eq_mul_inv]
      rwa [hzero] at h2'
  refine tendsto_iff_dist_tendsto_zero.mpr ?_
  refine hboundtendsto.congr' (Eventually.of_forall fun n ↦ ?_)
  show |∑ k ∈ Finset.range n,
      ∫ ω, g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2 ∂μ|
    = dist (∑ k ∈ Finset.range n,
      ∫ ω, g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2 ∂μ) 0
  rw [Real.dist_eq, sub_zero]

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- The `1/√n ≤ 2/√(n+1)` comparison for `n ≥ 1`. -/
private theorem one_div_sqrt_le_two {n : ℕ} (hn : 0 < n) :
    (1 : ℝ) / Real.sqrt ((n : ℝ)) ≤ 2 / Real.sqrt (((n : ℝ)) + 1) := by
  have hne : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpos1 : (0 : ℝ) < Real.sqrt ((n : ℝ)) := Real.sqrt_pos.mpr hne
  have hpos2 : (0 : ℝ) < Real.sqrt (((n : ℝ)) + 1) := Real.sqrt_pos.mpr (by linarith)
  have hsq : Real.sqrt (((n : ℝ)) + 1) ≤ 2 * Real.sqrt ((n : ℝ)) := by
    have hnm : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    refine le_trans (Real.sqrt_le_sqrt (show ((n : ℝ)) + 1 ≤ 4 * (n : ℝ) from by nlinarith)) ?_
    rw [show (2 : ℝ) * Real.sqrt ((n : ℝ)) = Real.sqrt (4 * (n : ℝ)) from by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num]
  rw [div_le_div_iff₀ hpos1 hpos2]
  simpa using hsq

set_option maxHeartbeats 1600000 in
/-- **The drift–martingale cross corrections of the quadratic block die** (`O(√mesh)`):
the summed absolute expectations of the frozen weight against
`Δ(AdaptedDrift.driftPath β)ₖ·ΔMₖ` are at most `2·C₂·D_β·|D_δ|·T·√T/√(n+1)` —
Cauchy–Schwarz pairs the
`D_β·cell`-bounded drift increment (`AdaptedDrift.abs_driftPath_sub_le`) against the
`D_δ²·cell`-energy martingale increment (`trueIncr_sq_le`), and the cells telescope to `T`. -/
theorem quadCrossSum_tendsto {β : ℝ≥0 → Ω → ℝ} {X : ℝ≥0 → Ω → ℝ}
    (hβadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (β t))
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db)
    (hXadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (X t))
    {g : ℝ → ℝ} {C2 : ℝ} (hgcont : Continuous g) (hg2 : ∀ x, |g x| ≤ C2) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
        ∫ ω, g (X (unifPart T n k) ω)
          * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
          * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ)
      atTop (𝓝 0) := by
  have hC2 : (0 : ℝ) ≤ C2 := le_trans (abs_nonneg _) (hg2 0)
  have hβbdd' : ∀ t ω, |β t ω| ≤ |Db| := fun t ω ↦ (hβbdd t ω).trans (le_abs_self Db)
  -- per-cell absolute bound
  have hcell : ∀ n : ℕ, ∀ k : ℕ, k < n →
      |∫ ω, g (X (unifPart T n k) ω)
          * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
          * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ|
        ≤ C2 * |Db| * |Dd| * (((unifPart T n (k + 1) : ℝ) - unifPart T n k)
          * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) := by
    intro n k hk
    have hcellnn : (0 : ℝ) ≤ (unifPart T n (k + 1) : ℝ) - unifPart T n k :=
      sub_nonneg.mpr (NNReal.coe_le_coe.mpr (unifPart_mono T n (Nat.le_succ k)))
    have hXk : Measurable (X (unifPart T n k)) :=
      (hXadap (unifPart T n k)).measurable.mono
        ((natFiltration hBmeas).le (unifPart T n k)) le_rfl
    have hdpm : Measurable (driftPath β (unifPart T n (k + 1))) :=
      (stronglyMeasurable_driftPath hBmeas hβadap hβcont hβbdd
        (unifPart T n (k + 1))).measurable.mono
        ((natFiltration hBmeas).le (unifPart T n (k + 1))) le_rfl
    have hdp0 : Measurable (driftPath β (unifPart T n k)) :=
      (stronglyMeasurable_driftPath hBmeas hβadap hβcont hβbdd
        (unifPart T n k)).measurable.mono
        ((natFiltration hBmeas).le (unifPart T n k)) le_rfl
    set dI : Ω → ℝ := fun ω ↦ driftPath β (unifPart T n (k + 1)) ω
      - driftPath β (unifPart T n k) ω with hdIdef
    set tI : Ω → ℝ := fun ω ↦ M (unifPart T n (k + 1)) ω
      - M (unifPart T n k) ω with htIdef
    -- the drift increment: bounded pointwise by `|Db|·cell`, `L²`
    have hdIb : ∀ ω : Ω, |dI ω| ≤ |Db| * ((unifPart T n (k + 1) : ℝ)
        - unifPart T n k) := fun ω ↦
      abs_driftPath_sub_le hβcont hβbdd'
        (unifPart_mono T n (Nat.le_succ k)) ω
    have hdImem : MemLp dI 2 μ := by
      have hdIm : Measurable dI := by
        rw [hdIdef]
        exact hdpm.sub hdp0
      exact MemLp.of_bound hdIm.aestronglyMeasurable
        (|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
        (Eventually.of_forall fun ω ↦ by
          show ‖dI ω‖ ≤ _
          rw [Real.norm_eq_abs]
          exact hdIb ω)
    have htImem : MemLp tI 2 μ :=
      (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq
        (unifPart T n (k + 1))).sub
        (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq (unifPart T n k))
    -- the mean-integrability inputs
    have hone : MemLp (fun _ : Ω ↦ (1 : ℝ)) 2 μ :=
      MemLp.of_bound (stronglyMeasurable_const.aestronglyMeasurable) 1
        (Eventually.of_forall fun ω ↦ by norm_num)
    have hnorm1 : ∫ ω, |tI ω| ∂μ ≤ Real.sqrt (∫ ω, tI ω ^ 2 ∂μ) := by
      have h1 := integral_abs_mul_le_L2L2 (htImem.norm) hone
      have hA : (∫ ω, abs (‖tI ω‖ * 1) ∂μ) = ∫ ω, |tI ω| ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun ω ↦ ?_)
        show abs (‖tI ω‖ * 1) = |tI ω|
        rw [Real.norm_eq_abs, mul_one, abs_abs]
      have hB : (∫ ω, ‖tI ω‖ ^ 2 ∂μ) = ∫ ω, tI ω ^ 2 ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun ω ↦ ?_)
        show ‖tI ω‖ ^ 2 = tI ω ^ 2
        rw [Real.norm_eq_abs, sq_abs]
      rw [hA, hB] at h1
      simpa using h1
    have htI2 := trueIncr_sq_le hB hBmeas hδadap hδcont hδbdd hMadap hMeq
      (unifPart_mono T n (Nat.le_succ k)) (unifPart_le_T (Nat.lt_iff_add_one_le.mp hk))
    have hsqrtT : Real.sqrt (∫ ω, tI ω ^ 2 ∂μ) ≤ |Dd| * Real.sqrt
        ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
      have h2 : Real.sqrt (∫ ω, tI ω ^ 2 ∂μ)
          ≤ Real.sqrt (∫ ω, (M (unifPart T n (k + 1)) ω
            - M (unifPart T n k) ω) ^ 2 ∂μ) := by
        refine Real.sqrt_le_sqrt ?_
        simp only [htIdef]
        exact le_refl _
      refine le_trans (le_trans h2 (Real.sqrt_le_sqrt htI2)) ?_
      rw [Real.sqrt_mul (sq_nonneg Dd), Real.sqrt_sq_eq_abs]
    -- integrability of the full product
    have hprodint : Integrable (fun ω ↦ g (X (unifPart T n k) ω) * dI ω * tI ω) μ := by
      refine Integrable.mono'
        ((htImem.norm.integrable one_le_two).const_mul (C2 * |Db| * ((unifPart T n (k + 1) : ℝ)
          - unifPart T n k)))
        (((hgcont.measurable.comp hXk).aestronglyMeasurable.mul
          (MemLp.aestronglyMeasurable hdImem)).mul (MemLp.aestronglyMeasurable htImem))
        (Eventually.of_forall fun ω ↦ by
          show ‖g (X (unifPart T n k) ω) * dI ω * tI ω‖ ≤ _
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
          calc |g (X (unifPart T n k) ω)| * |dI ω| * |tI ω|
              ≤ (C2 * (|Db| * ((unifPart T n (k + 1) : ℝ)
                - unifPart T n k))) * |tI ω| :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul (hg2 _) (hdIb ω) (abs_nonneg _) hC2)
                  (abs_nonneg _)
            _ = _ := by ring)
    -- pointwise domination `|g·dI·tI| ≤ K·|tI|`
    have hptmono : ∀ ω : Ω, |g (X (unifPart T n k) ω) * dI ω * tI ω|
        ≤ (C2 * (|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))) * |tI ω| := by
      intro ω
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (hg2 _) (hdIb ω) (abs_nonneg _) hC2) (abs_nonneg _)
    set K : ℝ := C2 * (|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) with hKdef
    have hK0 : (0 : ℝ) ≤ K := by
      rw [hKdef]
      exact mul_nonneg hC2 (mul_nonneg (abs_nonneg Db) hcellnn)
    calc |∫ ω, g (X (unifPart T n k) ω) * dI ω * tI ω ∂μ|
        ≤ ∫ ω, |g (X (unifPart T n k) ω) * dI ω * tI ω| ∂μ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ ω, (K * |tI ω|) ∂μ :=
          integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ abs_nonneg _)
            ((htImem.norm.integrable one_le_two).const_mul K)
            (Eventually.of_forall hptmono)
      _ = K * ∫ ω, |tI ω| ∂μ := by rw [integral_const_mul]
      _ ≤ K * (|Dd| * Real.sqrt ((unifPart T n (k + 1) : ℝ)
            - unifPart T n k)) :=
            mul_le_mul_of_nonneg_left (le_trans hnorm1 hsqrtT) hK0
      _ = C2 * |Db| * |Dd| * (((unifPart T n (k + 1) : ℝ) - unifPart T n k)
            * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) := by
          rw [hKdef]; ring
  -- squeeze
  have hboundtendsto : Tendsto (fun n : ℕ ↦ |∑ k ∈ Finset.range n,
      ∫ ω, g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
        * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ|)
      atTop (𝓝 0) := by
    refine squeeze_zero' (g := fun n : ℕ ↦ 2 * C2 * |Db| * |Dd| * (T : ℝ)
      * Real.sqrt (T : ℝ) * (1 / Real.sqrt (((n : ℝ)) + 1)))
      (Eventually.of_forall fun n ↦ abs_nonneg _) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      have hTnn : ((n : ℝ)) * ((T : ℝ) / (n : ℝ)) = (T : ℝ) := by
        field_simp
      have hsum : ∑ k ∈ Finset.range n,
          (((unifPart T n (k + 1) : ℝ) - unifPart T n k)
            * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
          = (T : ℝ) * Real.sqrt ((T : ℝ) / (n : ℝ)) := by
        have hstep : ∀ k : ℕ, k ∈ Finset.range n →
            (((unifPart T n (k + 1) : ℝ) - unifPart T n k)
              * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
            = ((T : ℝ) / (n : ℝ)) * Real.sqrt ((T : ℝ) / (n : ℝ)) := fun k _ ↦ by
          rw [cellLen_eq (T := T) (n := n) k]
        have hsumlast : ((n : ℝ)) * (((T : ℝ) / (n : ℝ)) * Real.sqrt ((T : ℝ) / (n : ℝ)))
            = (T : ℝ) * Real.sqrt ((T : ℝ) / (n : ℝ)) := by
          field_simp
        rw [Finset.sum_congr rfl hstep, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, hsumlast]
      have hsplit : ((T : ℝ)) * Real.sqrt ((T : ℝ) / (n : ℝ))
          = ((T : ℝ)) * Real.sqrt (T : ℝ) * (1 / Real.sqrt ((n : ℝ))) := by
        rw [Real.sqrt_div (by exact_mod_cast NNReal.coe_nonneg T : (0 : ℝ) ≤ (T : ℝ)),
          one_div]
        ring
      have hTs0 : (0 : ℝ) ≤ ((T : ℝ)) * Real.sqrt (T : ℝ) :=
        mul_nonneg (NNReal.coe_nonneg T) (Real.sqrt_nonneg _)
      have hK0 : (0 : ℝ) ≤ C2 * |Db| * |Dd| := by positivity
      calc |∑ k ∈ Finset.range n,
            ∫ ω, g (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
              * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ|
          ≤ ∑ k ∈ Finset.range n,
            |∫ ω, g (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
              * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range n, (C2 * |Db| * |Dd| * (((unifPart T n (k + 1) : ℝ)
              - unifPart T n k) * Real.sqrt ((unifPart T n (k + 1) : ℝ)
              - unifPart T n k))) :=
            Finset.sum_le_sum fun k hk ↦ hcell n k (Finset.mem_range.mp hk)
        _ = C2 * |Db| * |Dd| * ((T : ℝ) * Real.sqrt ((T : ℝ) / (n : ℝ))) := by
            rw [← Finset.mul_sum, hsum]
        _ = C2 * |Db| * |Dd| * (((T : ℝ)) * Real.sqrt (T : ℝ)
              * (1 / Real.sqrt ((n : ℝ)))) := by rw [hsplit]
        _ ≤ C2 * |Db| * |Dd| * (((T : ℝ)) * Real.sqrt (T : ℝ)
              * (2 / Real.sqrt (((n : ℝ)) + 1))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (one_div_sqrt_le_two hn) hTs0) hK0
        _ = 2 * C2 * |Db| * |Dd| * ((T : ℝ)) * Real.sqrt (T : ℝ)
              * (1 / Real.sqrt (((n : ℝ)) + 1)) := by ring
    · have hzero : ((2 * C2 * |Db| * |Dd| * (T : ℝ) * Real.sqrt (T : ℝ)) * (0 : ℝ))
          = (0 : ℝ) := mul_zero _
      have h2' : Tendsto (fun n : ℕ ↦ (2 * C2 * |Db| * |Dd| * (T : ℝ)
            * Real.sqrt (T : ℝ)) * (1 / Real.sqrt (((n : ℝ)) + 1)))
          atTop (𝓝 ((2 * C2 * |Db| * |Dd| * (T : ℝ) * Real.sqrt (T : ℝ)) * 0)) :=
        (tendsto_const_nhds (x := (2 * C2 * |Db| * |Dd| * (T : ℝ)
          * Real.sqrt (T : ℝ)))).mul tendsto_inv_sqrt_nat_add
      rwa [hzero] at h2'
  refine tendsto_iff_dist_tendsto_zero.mpr ?_
  refine hboundtendsto.congr' (Eventually.of_forall fun n ↦ ?_)
  show |∑ k ∈ Finset.range n,
      ∫ ω, g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
        * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ|
    = dist (∑ k ∈ Finset.range n,
      ∫ ω, g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
        * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ) 0
  rw [Real.dist_eq, sub_zero]


set_option maxHeartbeats 1600000 in
/-- **The Taylor remainder dies**: the summed discrete Taylor remainders along the uniform
partition have expectation tending to `0` — each `|Rₖ| ≤ C₃·|ΔXₖ|³`
(`abs_discreteTaylorRemainder_le`) with `ΔXₖ = Δ(AdaptedDrift.driftPath β)ₖ + ΔMₖ` (the increment
decomposition), `(a+b)³ ≤ 4·(a³+b³)` (`pow3_add_le`), the drift increment pointwise
`D_β·cell`, and the martingale increment `𝔼|ΔM|³ ≤ √(3·(D_δ²·cell)³)`
(`trueIncr_pow3_le`); the cells telescope to `T`, giving
`|𝔼[∑ₖ Rₖ]| ≤ 4·C₃·(4·D_β³·T³/(n+1)² + 2·√(3·(D_δ²·T)³)/√(n+1)) → 0`. -/
theorem taylorRemainderSum_tendsto (hBmeas : ∀ t, Measurable (B t)) (c : ℝ)
    {β : ℝ≥0 → Ω → ℝ} {X : ℝ≥0 → Ω → ℝ}
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db)
    (hXrel : ∀ t : ℝ≥0, X t = fun ω : Ω ↦ c + driftPath β t ω + M t ω)
    (hXadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (X t))
    {f f' f'' f''' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x, HasDerivAt f'' (f''' x) x)
    {C3 : ℝ} (hg3 : ∀ x, |f''' x| ≤ C3) :
    Tendsto (fun n : ℕ ↦ ∫ ω, ∑ k ∈ Finset.range n,
        discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
          (X (unifPart T n (k + 1)) ω) ∂μ) atTop (𝓝 0) := by
  have hC3 : (0 : ℝ) ≤ C3 := le_trans (abs_nonneg _) (hg3 0)
  have hβbdd' : ∀ t ω, |β t ω| ≤ |Db| := fun t ω ↦ (hβbdd t ω).trans (le_abs_self Db)
  have hfcont : Continuous f := Differentiable.continuous fun x ↦ (hf x).differentiableAt
  have hf'cont : Continuous f' := Differentiable.continuous fun x ↦ (hf' x).differentiableAt
  have hf''cont : Continuous f'' := Differentiable.continuous fun x ↦ (hf'' x).differentiableAt
  -- measurability of the per-step remainder
  have hRmeas : ∀ n : ℕ, ∀ k : ℕ, Measurable (fun ω : Ω ↦ discreteTaylorRemainder f f' f''
      (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω)) := by
    intro n k
    have hX0 : Measurable (X (unifPart T n k)) :=
      (hXadap (unifPart T n k)).measurable.mono
        ((natFiltration hBmeas).le (unifPart T n k)) le_rfl
    have hX1 : Measurable (X (unifPart T n (k + 1))) :=
      (hXadap (unifPart T n (k + 1))).measurable.mono
        ((natFiltration hBmeas).le (unifPart T n (k + 1))) le_rfl
    unfold discreteTaylorRemainder
    exact (((hfcont.measurable.comp hX1).sub (hfcont.measurable.comp hX0)).sub
      ((hf'cont.measurable.comp hX0).mul (hX1.sub hX0))).sub
      (((hf''cont.measurable.comp hX0).mul ((hX1.sub hX0).pow_const 2)).const_mul (1 / 2))
  -- per-cell: integrability of |Rₖ| and ∫|Rₖ| ≤ 4·C₃·((|Db|·cell)³ + √(3·(D_δ²·cell)³))
  have hcell : ∀ n : ℕ, 0 < n → ∀ k : ℕ, k < n →
      Integrable (fun ω ↦ |discreteTaylorRemainder f f' f''
          (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω)|) μ ∧
      ∫ ω, |discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
          (X (unifPart T n (k + 1)) ω)| ∂μ
        ≤ 4 * C3 * ((|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3
          + Real.sqrt (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ)
            - unifPart T n k)) ^ 3)) := by
    intro n hn k hk
    have hcellnn : (0 : ℝ) ≤ (unifPart T n (k + 1) : ℝ) - unifPart T n k :=
      sub_nonneg.mpr (NNReal.coe_le_coe.mpr (unifPart_mono T n (Nat.le_succ k)))
    have hX0m : Measurable (X (unifPart T n k)) :=
      (hXadap (unifPart T n k)).measurable.mono
        ((natFiltration hBmeas).le (unifPart T n k)) le_rfl
    have hX1m : Measurable (X (unifPart T n (k + 1))) :=
      (hXadap (unifPart T n (k + 1))).measurable.mono
        ((natFiltration hBmeas).le (unifPart T n (k + 1))) le_rfl
    have hsubm : Measurable (fun ω : Ω ↦ X (unifPart T n (k + 1)) ω
        - X (unifPart T n k) ω) := hX1m.sub hX0m
    have hΔ : ∀ ω : Ω, X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω
        = (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
          + (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) := by
      intro ω
      rw [hXrel (unifPart T n (k + 1)), hXrel (unifPart T n k)]
      show (c + driftPath β (unifPart T n (k + 1)) ω
            + M (unifPart T n (k + 1)) ω)
          - (c + driftPath β (unifPart T n k) ω + M (unifPart T n k) ω) = _
      ring
    have hdIb : ∀ ω : Ω, |driftPath β (unifPart T n (k + 1)) ω
        - driftPath β (unifPart T n k) ω| ≤ |Db| * ((unifPart T n (k + 1) : ℝ)
        - unifPart T n k) := fun ω ↦
      abs_driftPath_sub_le hβcont hβbdd'
        (unifPart_mono T n (Nat.le_succ k)) ω
    have hcub : ∀ ω : Ω, (abs (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) ^ 3
        ≤ (4 : ℝ) * ((abs (driftPath β (unifPart T n (k + 1)) ω
              - driftPath β (unifPart T n k) ω)) ^ 3
            + (abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) ^ 3) := by
      intro ω
      have h1 : abs (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)
          ≤ abs (driftPath β (unifPart T n (k + 1)) ω
              - driftPath β (unifPart T n k) ω)
            + abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) := by
        rw [hΔ ω]
        exact abs_add_le _ _
      have h2 := pow3_add_le (abs_nonneg _) (abs_nonneg _)
        (a := abs (driftPath β (unifPart T n (k + 1)) ω
              - driftPath β (unifPart T n k) ω))
        (b := abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω))
      calc (abs (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) ^ 3
          ≤ (abs (driftPath β (unifPart T n (k + 1)) ω
                - driftPath β (unifPart T n k) ω)
              + abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) ^ 3 :=
            pow_le_pow_left₀ (abs_nonneg _) h1 3
        _ ≤ (4 : ℝ) * ((abs (driftPath β (unifPart T n (k + 1)) ω
                - driftPath β (unifPart T n k) ω)) ^ 3
              + (abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) ^ 3) := h2
    -- integrability of |ΔM|³ (dominated by |ΔM|⁴ + 1)
    have htdI3 : Integrable (fun ω ↦ (abs (M (unifPart T n (k + 1)) ω
          - M (unifPart T n k) ω)) ^ 3) μ := by
      refine Integrable.mono'
        (((trueIncr_pow4_integrable hB hBmeas hδadap hδcont hδbdd hMeq hn k hk
          ).const_mul 1).add (integrable_const (1 : ℝ)))
        ((((memLp_M hB hBmeas hδadap hδcont hδbdd hMeq
          (unifPart T n (k + 1))).sub
          (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq (unifPart T n k))).abs).1.pow 3)
        (Eventually.of_forall fun ω ↦ by
          rw [Real.norm_eq_abs]
          set x := abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) with hxdef
          have hx0 : (0 : ℝ) ≤ x := abs_nonneg _
          have h3 : x ^ 3 ≤ x ^ 4 + 1 := by
            rcases le_total 1 x with h1 | h1
            · have hz : (0 : ℝ) ≤ x ^ 3 * (x - 1) :=
                mul_nonneg (pow_nonneg hx0 3) (sub_nonneg.mpr h1)
              nlinarith
            · refine le_trans (pow_le_pow_left₀ hx0 h1 3) ?_
              nlinarith [pow_nonneg hx0 4]
          simpa [hxdef, abs_of_nonneg hx0] using h3)
    have hmeasX3 : AEStronglyMeasurable
        (fun ω ↦ (abs (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) ^ 3) μ :=
      (hsubm.abs.aestronglyMeasurable).pow 3
    have htdA : Integrable (fun ω ↦ (4 : ℝ) * ((|Db| * ((unifPart T n (k + 1) : ℝ)
        - unifPart T n k)) ^ 3)) μ :=
      (integrable_const ((|Db| * ((unifPart T n (k + 1) : ℝ)
        - unifPart T n k)) ^ 3)).const_mul 4
    have htdB : Integrable (fun ω ↦ (4 : ℝ) *
        (abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) ^ 3) μ :=
      htdI3.const_mul 4
    have htdom : Integrable (fun ω ↦ (4 : ℝ) * ((|Db| * ((unifPart T n (k + 1) : ℝ)
        - unifPart T n k)) ^ 3)
        + (4 : ℝ) * (abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) ^ 3) μ :=
      htdA.add htdB
    have hptX3 : ∀ ω : Ω, (abs (X (unifPart T n (k + 1)) ω
        - X (unifPart T n k) ω)) ^ 3
        ≤ (4 : ℝ) * ((|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3)
          + (4 : ℝ) * (abs (M (unifPart T n (k + 1)) ω
          - M (unifPart T n k) ω)) ^ 3 := by
      intro ω
      refine le_trans (hcub ω) ?_
      rw [mul_add]
      exact add_le_add_left (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) (hdIb ω) 3)
        (by norm_num : (0:ℝ) ≤ 4)) _
    have habsX3 : Integrable (fun ω ↦ (abs (X (unifPart T n (k + 1)) ω
        - X (unifPart T n k) ω)) ^ 3) μ := by
      refine Integrable.mono' htdom hmeasX3 (Eventually.of_forall fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hptX3 ω
    have hRk3 : ∫ ω, (abs (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) ^ 3 ∂μ
        ≤ (4 : ℝ) * ((|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3
          + Real.sqrt (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ)
            - unifPart T n k)) ^ 3)) := by
      have hdI3 : ∫ ω, (abs (driftPath β (unifPart T n (k + 1)) ω
          - driftPath β (unifPart T n k) ω)) ^ 3 ∂μ
          ≤ (|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3 := by
        refine le_trans (integral_mono_of_nonneg
          (Eventually.of_forall fun ω ↦ by positivity)
          (integrable_const ((|Db| * ((unifPart T n (k + 1) : ℝ)
            - unifPart T n k)) ^ 3))
          (Eventually.of_forall fun ω ↦ ?_)) ?_
        · exact pow_le_pow_left₀ (abs_nonneg _) (hdIb ω) 3
        · rw [integral_const]; simp
      have htI3 := trueIncr_pow3_le hB hBmeas hδadap hδcont hδbdd hMadap hMeq hn k hk
      refine le_trans (integral_mono_of_nonneg
        (Eventually.of_forall fun ω ↦ by positivity) htdom
        (Eventually.of_forall fun ω ↦ by
          show (abs (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) ^ 3
            ≤ (4 : ℝ) * ((|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3)
              + (4 : ℝ) * (abs (M (unifPart T n (k + 1)) ω
              - M (unifPart T n k) ω)) ^ 3
          exact hptX3 ω)) ?_
      rw [integral_add htdA htdB, integral_const_mul, integral_const_mul, integral_const,
        measureReal_def, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one,
        smul_eq_mul, one_mul]
      rw [mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_left le_rfl (by norm_num : (0:ℝ) ≤ 4))
        (mul_le_mul_of_nonneg_left htI3 (by norm_num : (0:ℝ) ≤ 4))
    -- |Rₖ| ≤ C₃·|ΔX|³ pointwise
    have hRb : ∀ ω : Ω, |discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
          (X (unifPart T n (k + 1)) ω)|
        ≤ C3 * (abs (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) ^ 3 :=
      fun ω ↦ abs_discreteTaylorRemainder_le hf hf' hf'' hg3 _ _
    refine ⟨?_, ?_⟩
    · refine Integrable.mono' (habsX3.const_mul C3)
        ((hRmeas n k).abs.aestronglyMeasurable)
        (Eventually.of_forall fun ω ↦ by
          show ‖|discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
            (X (unifPart T n (k + 1)) ω)|‖ ≤ _
          rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
          exact hRb ω)
    · calc ∫ ω, |discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
            (X (unifPart T n (k + 1)) ω)| ∂μ
          ≤ ∫ ω, (C3 * (abs (X (unifPart T n (k + 1)) ω
              - X (unifPart T n k) ω)) ^ 3) ∂μ :=
            integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ abs_nonneg _)
              (habsX3.const_mul C3) (Eventually.of_forall fun ω ↦ hRb ω)
        _ = (C3 : ℝ) * ∫ ω, (abs (X (unifPart T n (k + 1)) ω
              - X (unifPart T n k) ω)) ^ 3 ∂μ := by rw [integral_const_mul]
        _ ≤ (C3 : ℝ) * ((4 : ℝ) * ((|Db| * ((unifPart T n (k + 1) : ℝ)
              - unifPart T n k)) ^ 3
              + Real.sqrt (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ)
                - unifPart T n k)) ^ 3))) :=
              mul_le_mul_of_nonneg_left hRk3 hC3
        _ = 4 * C3 * ((|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3
              + Real.sqrt (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ)
                - unifPart T n k)) ^ 3)) := by ring
  -- the summed bound and the squeeze
  have hintsum : ∀ n : ℕ, 0 < n → ∫ ω : Ω, (∑ k ∈ Finset.range n,
      |discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
        (X (unifPart T n (k + 1)) ω)|) ∂μ
      = ∑ k ∈ Finset.range n, (∫ ω : Ω,
      |discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
        (X (unifPart T n (k + 1)) ω)| ∂μ) := by
    intro n hn
    refine integral_finsetSum (μ := μ) (s := Finset.range n)
      (f := fun (k : ℕ) (ω : Ω) ↦ |discreteTaylorRemainder f f' f''
        (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω)|)
      (fun k hk ↦ (hcell n hn k (Finset.mem_range.mp hk)).1)
  have hboundtendsto : Tendsto (fun n : ℕ ↦ |∫ ω : Ω, ∑ k ∈ Finset.range n,
      discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
        (X (unifPart T n (k + 1)) ω) ∂μ|)
      atTop (𝓝 0) := by
    refine squeeze_zero' (g := fun n : ℕ ↦ (4 * C3 * (4 * |Db| ^ 3 * (T : ℝ) ^ 3))
        * ((1 / ((n : ℝ) + 1)) ^ 2)
      + (4 * C3 * (2 * Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3)))
        * ((1 : ℝ) / Real.sqrt ((n : ℝ) + 1)))
      (Eventually.of_forall fun n ↦ abs_nonneg _) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      have hn0r : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hcellen : ∀ k : ℕ, k ∈ Finset.range n →
          ((unifPart T n (k + 1) : ℝ) - unifPart T n k) = ((T : ℝ) / (n : ℝ)) :=
        fun k _ ↦ cellLen_eq (T := T) (n := n) k
      set gR : Ω → ℝ := fun ω : Ω ↦ ∑ k ∈ Finset.range n,
        discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
          (X (unifPart T n (k + 1)) ω) with hgR
      have hsum1 : (∑ k ∈ Finset.range n,
          (|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3)
          = ((n : ℝ)) * (|Db| * ((T : ℝ) / (n : ℝ))) ^ 3 := by
        rw [Finset.sum_congr rfl fun k hk ↦ by rw [hcellen k hk], Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
      have hsum2 : (∑ k ∈ Finset.range n,
          Real.sqrt (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ)
            - unifPart T n k)) ^ 3))
          = ((n : ℝ)) * Real.sqrt (3 * (Dd ^ 2 * ((T : ℝ) / (n : ℝ))) ^ 3) := by
        rw [Finset.sum_congr rfl fun k hk ↦ by rw [hcellen k hk], Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
      have hpart1 : ((n : ℝ)) * (|Db| * ((T : ℝ) / (n : ℝ))) ^ 3
          = |Db| ^ 3 * (T : ℝ) ^ 3 / (n : ℝ) ^ 2 := by
        field_simp
      have hpart2 : ((n : ℝ)) * Real.sqrt (3 * (Dd ^ 2 * ((T : ℝ) / (n : ℝ))) ^ 3)
          = Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3) / Real.sqrt ((n : ℝ)) := by
        have hpos : (0 : ℝ) < Real.sqrt ((n : ℝ)) := Real.sqrt_pos.mpr hn0r
        have hXn : (3 * (Dd ^ 2 * ((T : ℝ) / (n : ℝ))) ^ 3) * (n : ℝ)
            = (3 * (Dd ^ 2 * (T : ℝ)) ^ 3) / (n : ℝ) ^ 2 := by
          field_simp
        rw [eq_div_iff hpos.ne', mul_assoc, ← Real.sqrt_mul
          (by positivity : (0 : ℝ) ≤ 3 * (Dd ^ 2 * ((T : ℝ) / (n : ℝ))) ^ 3),
          hXn, Real.sqrt_div (by positivity : (0 : ℝ) ≤
            3 * (Dd ^ 2 * (T : ℝ)) ^ 3), Real.sqrt_sq
            (by norm_num : (0 : ℝ) ≤ (n : ℝ))]
        field_simp
      have hB0 : (0 : ℝ) ≤ Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3) := Real.sqrt_nonneg _
      have hpos1 : (0 : ℝ) < Real.sqrt ((n : ℝ)) := Real.sqrt_pos.mpr hn0r
      have hpos2 : (0 : ℝ) < Real.sqrt (((n : ℝ)) + 1) :=
        Real.sqrt_pos.mpr (by linarith)
      have hstep : Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3)
          / Real.sqrt ((n : ℝ))
          ≤ (2 * Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3))
            / Real.sqrt (((n : ℝ)) + 1) := by
        have h1 : Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3)
            / Real.sqrt ((n : ℝ))
            = Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3)
              * ((1 : ℝ) / Real.sqrt ((n : ℝ))) := by
          rw [one_div]; ring
        have h2 : Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3)
            * ((1 : ℝ) / Real.sqrt ((n : ℝ)))
          ≤ Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3)
            * (2 / Real.sqrt (((n : ℝ)) + 1)) :=
          mul_le_mul_of_nonneg_left (one_div_sqrt_le_two hn) hB0
        have h3 : Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3)
            * (2 / Real.sqrt (((n : ℝ)) + 1))
          = (2 * Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3))
            / Real.sqrt (((n : ℝ)) + 1) := by
          ring
        exact le_trans (le_of_eq h1) (h2.trans h3.le)
      calc |∫ ω : Ω, gR ω ∂μ|
          ≤ ‖∫ ω : Ω, gR ω ∂μ‖ :=
            le_of_eq (by rw [Real.norm_eq_abs])
        _ ≤ ∫ ω : Ω, ‖gR ω‖ ∂μ := norm_integral_le_integral_norm gR
        _ = ∫ ω : Ω, |gR ω| ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
            show ‖gR ω‖ = |gR ω|
            rw [Real.norm_eq_abs]
        _ ≤ ∫ ω : Ω, (∑ k ∈ Finset.range n,
            |discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
              (X (unifPart T n (k + 1)) ω)|) ∂μ :=
            integral_mono_of_nonneg
              (Eventually.of_forall fun ω ↦ abs_nonneg _)
              (integrable_finsetSum _ fun k hk ↦
                (hcell n hn k (Finset.mem_range.mp hk)).1)
              (Eventually.of_forall fun ω ↦
                Finset.abs_sum_le_sum_abs _ _)
        _ = ∑ k ∈ Finset.range n,
            ∫ ω, |discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
              (X (unifPart T n (k + 1)) ω)| ∂μ := hintsum n hn
        _ ≤ ∑ k ∈ Finset.range n, (4 * C3 * ((|Db| * ((unifPart T n (k + 1) : ℝ)
              - unifPart T n k)) ^ 3
              + Real.sqrt (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ)
                - unifPart T n k)) ^ 3))) :=
            Finset.sum_le_sum fun k hk ↦
              (hcell n hn k (Finset.mem_range.mp hk)).2
        _ = (4 * C3) * ((∑ k ∈ Finset.range n,
              (|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3)
              + (∑ k ∈ Finset.range n,
              Real.sqrt (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ)
                - unifPart T n k)) ^ 3))) := by
            have hsplit : ∀ k ∈ Finset.range n,
                (4 : ℝ) * C3 * (((|Db| * ((unifPart T n (k + 1) : ℝ)
                  - unifPart T n k)) ^ 3)
                + Real.sqrt (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ)
                  - unifPart T n k)) ^ 3))
                = (4 : ℝ) * C3 * ((|Db| * ((unifPart T n (k + 1) : ℝ)
                  - unifPart T n k)) ^ 3)
                + (4 : ℝ) * C3 * (Real.sqrt (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ)
                  - unifPart T n k)) ^ 3)) := fun k _ ↦ by ring
            rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, mul_add,
              Finset.mul_sum, Finset.mul_sum]
        _ = (4 * C3) * ((|Db| ^ 3 * (T : ℝ) ^ 3 / (n : ℝ) ^ 2)
              + Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3) / Real.sqrt ((n : ℝ))) := by
            rw [hsum1, hsum2, hpart1, hpart2]
        _ ≤ (4 * C3) * ((4 * |Db| ^ 3 * (T : ℝ) ^ 3) / ((n : ℝ) + 1) ^ 2
              + (2 * Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3))
              / Real.sqrt (((n : ℝ)) + 1)) := by
            refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_)
              (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hC3)
            · have hnm : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
              have h2n : ((n : ℝ) + 1) ≤ 2 * (n : ℝ) := by linarith
              have hs : ((n : ℝ) + 1) ^ 2 ≤ (2 * (n : ℝ)) ^ 2 :=
                pow_le_pow_left₀ (by linarith) h2n 2
              rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (n:ℝ) ^ 2)
                (by positivity : (0:ℝ) < ((n : ℝ) + 1) ^ 2)]
              calc |Db| ^ 3 * (T : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2
                  ≤ |Db| ^ 3 * (T : ℝ) ^ 3 * ((2 * (n : ℝ)) ^ 2) :=
                    mul_le_mul_of_nonneg_left hs (by positivity)
                _ = 4 * |Db| ^ 3 * (T : ℝ) ^ 3 * (n : ℝ) ^ 2 := by ring
            · have hstep : Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3)
                  / Real.sqrt ((n : ℝ))
                  ≤ (2 * Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3))
                    / Real.sqrt (((n : ℝ)) + 1) := hstep
              exact hstep
        _ = (4 * C3 * (4 * |Db| ^ 3 * (T : ℝ) ^ 3)) * ((1 / ((n : ℝ) + 1)) ^ 2)
            + (4 * C3 * (2 * Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3)))
            * ((1 : ℝ) / Real.sqrt ((n : ℝ) + 1)) := by
            have hn1 : ((n : ℝ) + 1) ≠ 0 := by linarith
            field_simp [hn1]
    · have hzero : ((4 * C3 * (4 * |Db| ^ 3 * (T : ℝ) ^ 3)) * (0 : ℝ)
          + (4 * C3 * (2 * Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3))) * (0 : ℝ)) = 0 := by
        norm_num
      have h1 : Tendsto (fun n : ℕ ↦ ((1 / ((n : ℝ) + 1)) ^ 2)) atTop (𝓝 (0 : ℝ)) :=
        (tendsto_one_div_nat_add.pow 2).trans_eq
          (congrArg (fun x : ℝ => 𝓝 x) (by norm_num : ((0 : ℝ) ^ 2) = (0 : ℝ)))
      have hA : Tendsto (fun n : ℕ ↦ (4 * C3 * (4 * |Db| ^ 3 * (T : ℝ) ^ 3))
          * ((1 / ((n : ℝ) + 1)) ^ 2)) atTop
          (𝓝 ((4 * C3 * (4 * |Db| ^ 3 * (T : ℝ) ^ 3)) * (0 : ℝ))) :=
        (tendsto_const_nhds (x := (4 * C3 * (4 * |Db| ^ 3 * (T : ℝ) ^ 3)))).mul h1
      have hB : Tendsto (fun n : ℕ ↦ (4 * C3 * (2 * Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3)))
          * ((1 : ℝ) / Real.sqrt ((n : ℝ) + 1))) atTop
          (𝓝 ((4 * C3 * (2 * Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3))) * (0 : ℝ))) :=
        (tendsto_const_nhds (x := (4 * C3 * (2 * Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3))))).mul
          tendsto_inv_sqrt_nat_add
      have hfin : Tendsto (fun n : ℕ ↦ (4 * C3 * (4 * |Db| ^ 3 * (T : ℝ) ^ 3))
          * ((1 / ((n : ℝ) + 1)) ^ 2)
          + (4 * C3 * (2 * Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3)))
          * ((1 : ℝ) / Real.sqrt ((n : ℝ) + 1))) atTop (𝓝 0) := by
        have h := hA.add hB
        rw [hzero] at h
        exact h
      exact hfin
  refine tendsto_iff_dist_tendsto_zero.mpr ?_
  refine hboundtendsto.congr' (Eventually.of_forall fun n ↦ ?_)
  show |∫ ω : Ω, ∑ k ∈ Finset.range n,
      discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
        (X (unifPart T n (k + 1)) ω) ∂μ|
    = dist (∫ ω : Ω, ∑ k ∈ Finset.range n,
      discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
        (X (unifPart T n (k + 1)) ω) ∂μ) 0
  rw [Real.dist_eq, sub_zero]


set_option maxHeartbeats 1600000 in
omit hMadap in
/-- **Per-cell Taylor-remainder integrability** (assembly input): along the adapted process
`X` with the decomposition `X t = c + AdaptedDrift.driftPath β t + M t`, the `k`-th cell's
discrete Taylor remainder is integrable — `|Rₖ| ≤ C₃·|ΔXₖ|³` (`abs_discreteTaylorRemainder_le`)
with `ΔXₖ = Δ(AdaptedDrift.driftPath β)ₖ + ΔMₖ` (pointwise, from `hXrel`), the drift
increment bounded
by `|D_β|·cell` (`AdaptedDrift.abs_driftPath_sub_le`), and the martingale increment in `L³` by the
fourth-moment bound `trueIncr_pow4_integrable` (the domination `x³ ≤ x⁴ + 1`). -/
private theorem remainderCell_integrable {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : k < n)
    {β : ℝ≥0 → Ω → ℝ} {X : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db)
    (hXrel : ∀ t : ℝ≥0, X t = fun ω : Ω ↦ c + driftPath β t ω + M t ω)
    (hXadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (X t))
    {f f' f'' f''' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x, HasDerivAt f'' (f''' x) x)
    {C3 : ℝ} (hg3 : ∀ x, |f''' x| ≤ C3) :
    Integrable (fun ω : Ω ↦ discreteTaylorRemainder f f' f''
      (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω)) μ := by
  have hcellnn : (0 : ℝ) ≤ (unifPart T n (k + 1) : ℝ) - unifPart T n k :=
    sub_nonneg.mpr (NNReal.coe_le_coe.mpr (unifPart_mono T n (Nat.le_succ k)))
  have hβbdd' : ∀ t ω, |β t ω| ≤ |Db| := fun t ω ↦ (hβbdd t ω).trans (le_abs_self Db)
  have hfcont : Continuous f := Differentiable.continuous fun x ↦ (hf x).differentiableAt
  have hf'cont : Continuous f' := Differentiable.continuous fun x ↦ (hf' x).differentiableAt
  have hf''cont : Continuous f'' := Differentiable.continuous fun x ↦ (hf'' x).differentiableAt
  -- measurability of the endpoints and of the remainder
  have hX0m : Measurable (X (unifPart T n k)) :=
    (hXadap (unifPart T n k)).measurable.mono
      ((natFiltration hBmeas).le (unifPart T n k)) le_rfl
  have hX1m : Measurable (X (unifPart T n (k + 1))) :=
    (hXadap (unifPart T n (k + 1))).measurable.mono
      ((natFiltration hBmeas).le (unifPart T n (k + 1))) le_rfl
  have hRm : Measurable (fun ω : Ω ↦ discreteTaylorRemainder f f' f''
      (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω)) := by
    unfold discreteTaylorRemainder
    exact (((hfcont.measurable.comp hX1m).sub (hfcont.measurable.comp hX0m)).sub
      ((hf'cont.measurable.comp hX0m).mul (hX1m.sub hX0m))).sub
      (((hf''cont.measurable.comp hX0m).mul ((hX1m.sub hX0m).pow_const 2)).const_mul (1 / 2))
  -- the increment decomposition and the pointwise drift bound
  have hΔ : ∀ ω : Ω, X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω
      = (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
        + (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) := by
    intro ω
    rw [hXrel (unifPart T n (k + 1)), hXrel (unifPart T n k)]
    show (c + driftPath β (unifPart T n (k + 1)) ω + M (unifPart T n (k + 1)) ω)
        - (c + driftPath β (unifPart T n k) ω + M (unifPart T n k) ω) = _
    ring
  have hdIb : ∀ ω : Ω, |driftPath β (unifPart T n (k + 1)) ω
      - driftPath β (unifPart T n k) ω| ≤ |Db| * ((unifPart T n (k + 1) : ℝ)
      - unifPart T n k) := fun ω ↦
    abs_driftPath_sub_le hβcont hβbdd'
      (unifPart_mono T n (Nat.le_succ k)) ω
  -- `𝔼|ΔM|³ < ∞` (the `L⁴` bound via `trueIncr_pow4_integrable`, dominated by `x⁴ + 1`)
  have htdI3 : Integrable (fun ω ↦ (abs (M (unifPart T n (k + 1)) ω
      - M (unifPart T n k) ω)) ^ 3) μ := by
    refine Integrable.mono'
      (((trueIncr_pow4_integrable hB hBmeas hδadap hδcont hδbdd hMeq hn k hk
        ).const_mul 1).add (integrable_const (1 : ℝ)))
      ((((memLp_M hB hBmeas hδadap hδcont hδbdd hMeq
        (unifPart T n (k + 1))).sub
        (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq (unifPart T n k))).abs).1.pow 3)
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs]
        set x := abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) with hxdef
        have hx0 : (0 : ℝ) ≤ x := abs_nonneg _
        have h3 : x ^ 3 ≤ x ^ 4 + 1 := by
          rcases le_total 1 x with h1 | h1
          · have hz : (0 : ℝ) ≤ x ^ 3 * (x - 1) :=
              mul_nonneg (pow_nonneg hx0 3) (sub_nonneg.mpr h1)
            nlinarith
          · refine le_trans (pow_le_pow_left₀ hx0 h1 3) ?_
            nlinarith [pow_nonneg hx0 4]
        simpa [hxdef, abs_of_nonneg hx0] using h3)
  -- the cubic domination `|ΔX|³ ≤ 4·((|D_β|·cell)³ + |ΔM|³)` pointwise
  have hsubm : Measurable (fun ω : Ω ↦ X (unifPart T n (k + 1)) ω
      - X (unifPart T n k) ω) := hX1m.sub hX0m
  have hcub : ∀ ω : Ω, (abs (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) ^ 3
      ≤ (4 : ℝ) * ((|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3
        + (abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) ^ 3) := by
    intro ω
    have h1 : abs (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)
        ≤ abs (driftPath β (unifPart T n (k + 1)) ω
            - driftPath β (unifPart T n k) ω)
          + abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) := by
      rw [hΔ ω]
      exact abs_add_le _ _
    have h2 := pow3_add_le (abs_nonneg _) (abs_nonneg _)
      (a := abs (driftPath β (unifPart T n (k + 1)) ω
            - driftPath β (unifPart T n k) ω))
      (b := abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω))
    calc (abs (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) ^ 3
        ≤ (abs (driftPath β (unifPart T n (k + 1)) ω
              - driftPath β (unifPart T n k) ω)
            + abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) ^ 3 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 3
      _ ≤ (4 : ℝ) * ((abs (driftPath β (unifPart T n (k + 1)) ω
              - driftPath β (unifPart T n k) ω)) ^ 3
            + (abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) ^ 3) := h2
      _ ≤ (4 : ℝ) * (((|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3
            + (abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) ^ 3)) :=
          mul_le_mul_of_nonneg_left
            (add_le_add_left (pow_le_pow_left₀ (abs_nonneg _) (hdIb ω) 3)
              (abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 3))
            (by norm_num : (0 : ℝ) ≤ 4)
  have hdom : Integrable (fun ω ↦ (4 : ℝ) * ((|Db| * ((unifPart T n (k + 1) : ℝ)
      - unifPart T n k)) ^ 3)
      + (4 : ℝ) * (abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) ^ 3) μ :=
    (integrable_const ((|Db| * ((unifPart T n (k + 1) : ℝ)
      - unifPart T n k)) ^ 3)).const_mul 4 |>.add (htdI3.const_mul 4)
  have habsX3 : Integrable (fun ω ↦ (abs (X (unifPart T n (k + 1)) ω
      - X (unifPart T n k) ω)) ^ 3) μ :=
    Integrable.mono' hdom ((hsubm.abs.aestronglyMeasurable).pow 3)
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        calc (abs (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) ^ 3
            ≤ (4 : ℝ) * ((|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3
              + (abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) ^ 3) := hcub ω
          _ = (4 : ℝ) * ((|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3)
              + (4 : ℝ) * (abs (M (unifPart T n (k + 1)) ω
                - M (unifPart T n k) ω)) ^ 3 := by rw [mul_add])
  -- `|Rₖ| ≤ C₃·|ΔX|³` closes
  refine Integrable.mono' (habsX3.const_mul C3) hRm.aestronglyMeasurable
    (Eventually.of_forall fun ω ↦ by
      show ‖discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
        (X (unifPart T n (k + 1)) ω)‖ ≤ C3 * (abs (X (unifPart T n (k + 1)) ω
          - X (unifPart T n k) ω)) ^ 3
      rw [Real.norm_eq_abs]
      exact abs_discreteTaylorRemainder_le hf hf' hf'' hg3 _ _)


set_option maxHeartbeats 1600000 in
/-- **The integrated Itô–drift identity for adapted coefficients**, conditional on the
process `M`. For `β, δ` bounded, `natFiltration`-adapted and path-continuous, a hypothesized
`natFiltration`-adapted `M` with `M t =ᵐ (δ●B)_t` for every `t` (`hMeq`), and a hypothesized
`X` with `X_t = c + ∫₀ᵗ β_s ds + M_t` (`hXrel`, the `AdaptedDrift.driftPath β` decomposition)
and every path continuous (`hXcont`, which forces every path of `M` to be continuous), and `f` three
times differentiable with `f'`, `f''`, `f'''` bounded,

  `𝔼[f(X_T)] = 𝔼[f(X_0)] + ∫₀ᵀ (𝔼[f'(X_s)·β_s] + ½·𝔼[f''(X_s)·δ_s²]) ds`.

No lemma in the library supplies such an `M` for general `δ` (see the module docstring).

Route: the per-path discrete Itô formula (`MathFin.discrete_ito_formula`) at the grid
values of `X`, integrated over `Ω`; the first-order martingale terms die exactly
(`mul_trueIncr_expect_eq_zero` at the `𝓕_{tₖ}`-measurable bounded test `f' ∘ X`); the
drift block converges to `∫₀ᵀ 𝔼[f'∘X·β]` (`driftBlock_tendsto`); the quadratic block
converges to `∫₀ᵀ 𝔼[f''∘X·δ²]` (`quadraticSqSum_tendsto_uncond` at the weight `f''∘X`);
the drift² corrections, the drift–martingale cross corrections and the Taylor remainder
die (`quadDriftSqSum_tendsto`, `quadCrossSum_tendsto`,
`taylorRemainderSum_tendsto`); the two time integrals cross the expectation by the
stage-1 Fubini lemma (already folded into the sub-lemma conclusions). -/
theorem itoDrift_expectation_identity_adapted
    {β : ℝ≥0 → Ω → ℝ}
    (hβadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (β t))
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db)
    {X : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (hXcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ X s ω)
    (hXrel : ∀ t : ℝ≥0, X t = fun ω : Ω ↦ c + driftPath β t ω + M t ω)
    {f f' f'' f''' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x, HasDerivAt f'' (f''' x) x)
    {C1 C2 C3 : ℝ} (hg1 : ∀ x, |f' x| ≤ C1) (hg2 : ∀ x, |f'' x| ≤ C2)
    (hg3 : ∀ x, |f''' x| ≤ C3) :
    ∫ ω, f (X T ω) ∂μ
      = ∫ ω, f (X (0 : ℝ≥0) ω) ∂μ
        + ∫ s in Set.Ioc (0 : ℝ≥0) T,
            ((∫ ω, f' (X s ω) * β s ω ∂μ)
              + (1 / 2) * (∫ ω, f'' (X s ω) * (δ s ω * δ s ω) ∂μ))
          ∂ItoIntegralL2.timeMeasure := by
  have hC1 : (0 : ℝ) ≤ C1 := le_trans (abs_nonneg _) (hg1 0)
  have hC2 : (0 : ℝ) ≤ C2 := le_trans (abs_nonneg _) (hg2 0)
  have hfcont : Continuous f := Differentiable.continuous fun x ↦ (hf x).differentiableAt
  have hf'c : Continuous f' := Differentiable.continuous fun x ↦ (hf' x).differentiableAt
  have hf''c : Continuous f'' := Differentiable.continuous fun x ↦ (hf'' x).differentiableAt
  -- `X` is adapted, by the decomposition (the one new measurability fact of 5d)
  have hXadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (X t) := by
    intro t
    rw [hXrel t]
    exact (((stronglyMeasurable_driftPath hBmeas hβadap hβcont hβbdd t).measurable.const_add c).add
      (hMadap t).measurable).stronglyMeasurable
  -- `f ∘ X` is integrable (linear growth of `f` from `|f'| ≤ C₁`)
  have hf_lin : ∀ x, |f x| ≤ |f 0| + C1 * |x| := by
    intro x
    have hmv : |f x - f 0| ≤ C1 * |x| := by
      have h := abs_sub_le_of_hasDerivAt (g := f) (g' := f') hf hg1 0 x
      simpa using h
    calc |f x| = |f 0 + (f x - f 0)| := by congr 1; ring
      _ ≤ |f 0| + |f x - f 0| := abs_add_le _ _
      _ ≤ |f 0| + C1 * |x| := by linarith
  have hMint : ∀ t : ℝ≥0, Integrable (fun ω ↦ |M t ω|) μ :=
    fun t ↦ (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq t).norm.integrable one_le_two
  have hdpb : ∀ t : ℝ≥0, ∀ ω, |driftPath β t ω| ≤ |Db| * (t : ℝ) := by
    intro t ω
    have h0 : driftPath β (0 : ℝ≥0) ω = 0 := by
      simp only [driftPath, Set.Ioc_self, setIntegral_empty]
    have h := abs_driftPath_sub_le hβcont hβbdd
      (show (0 : ℝ≥0) ≤ t from zero_le) ω
    rw [h0, sub_zero, NNReal.coe_zero, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self Db) (NNReal.coe_nonneg t))
  have hXint : ∀ t : ℝ≥0, Integrable (fun ω ↦ f (X t ω)) μ := by
    intro t
    have hmeas : AEStronglyMeasurable (fun ω ↦ f (X t ω)) μ :=
      (hfcont.measurable.comp
        ((hXadap t).measurable.mono ((natFiltration hBmeas).le t) le_rfl)).aestronglyMeasurable
    have hdom : Integrable (fun ω ↦ (|f 0| + C1 * (|c| + |Db| * ((t : ℝ) + 1)))
        + C1 * |M t ω|) μ :=
      (integrable_const _).add ((hMint t).const_mul C1)
    refine Integrable.mono' hdom hmeas (Eventually.of_forall fun ω ↦ ?_)
    have harg : |X t ω| ≤ |c| + |Db| * ((t : ℝ) + 1) + |M t ω| := by
      have h1 : |X t ω| = |c + driftPath β t ω + M t ω| := by rw [hXrel t]
      rw [h1]
      calc |c + driftPath β t ω + M t ω| ≤ |c + driftPath β t ω| + |M t ω| :=
            abs_add_le _ _
        _ ≤ |c| + |driftPath β t ω| + |M t ω| := by
            have := abs_add_le c (driftPath β t ω); linarith
        _ ≤ |c| + |Db| * ((t : ℝ) + 1) + |M t ω| := by
            have h2 := hdpb t ω
            have h3 : |Db| * (t : ℝ) ≤ |Db| * ((t : ℝ) + 1) :=
              mul_le_mul_of_nonneg_left (show (t : ℝ) ≤ (t : ℝ) + 1 by
                linarith [NNReal.coe_nonneg t]) (abs_nonneg Db)
            linarith
    calc |f (X t ω)| ≤ |f 0| + C1 * |X t ω| := hf_lin _
      _ ≤ |f 0| + C1 * (|c| + |Db| * ((t : ℝ) + 1) + |M t ω|) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left harg hC1)
      _ = (|f 0| + C1 * (|c| + |Db| * ((t : ℝ) + 1))) + C1 * |M t ω| := by ring
  -- the five block convergences
  have hA : Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
      ∫ ω, f' (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ∂μ)
    atTop (𝓝 (∫ s in Set.Ioc (0 : ℝ≥0) T,
        (∫ ω, f' (X s ω) * β s ω ∂μ) ∂ItoIntegralL2.timeMeasure)) :=
    driftBlock_tendsto hBmeas T hβadap hβcont hβbdd hXadap hXcont hf'c hg1
  have hB0 : Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
      ∫ ω, f'' (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2 ∂μ)
    atTop (𝓝 0) :=
    quadDriftSqSum_tendsto hBmeas T hβadap hβcont hβbdd hXadap hf''c hg2
  have hC0 : Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
      ∫ ω, f'' (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
        * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ)
    atTop (𝓝 0) :=
    quadCrossSum_tendsto hB hBmeas hδadap hδcont hδbdd hMadap hMeq
      hβadap hβcont hβbdd hXadap hf''c hg2
  have hE0 : Tendsto (fun n : ℕ ↦ ∫ ω, ∑ k ∈ Finset.range n,
      discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
        (X (unifPart T n (k + 1)) ω) ∂μ) atTop (𝓝 0) :=
    taylorRemainderSum_tendsto hB hBmeas hδadap hδcont hδbdd hMadap hMeq hBmeas c
      hβcont hβbdd hXrel hXadap hf hf' hf'' hg3
  have hD0 : Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
      ∫ ω, f'' (X (unifPart T n k) ω)
        * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)
    atTop (𝓝 (∫ s in Set.Ioc (0 : ℝ≥0) T,
        (∫ ω, f'' (X s ω) * (δ s ω * δ s ω) ∂μ) ∂ItoIntegralL2.timeMeasure)) :=
    quadraticSqSum_tendsto_uncond hB hBmeas hδadap hδcont hδbdd hMadap hMeq
      (w := fun s ω ↦ f'' (X s ω)) (Cw := C2)
      (fun t ↦ hf''c.measurable.comp (hXadap t).measurable)
      (fun ω ↦ hf''c.comp (hXcont ω))
      (fun s ω ↦ hg2 (X s ω))
  -- the per-partition identity (expectation of the discrete Itô expansion)
  have key : ∀ n : ℕ, 0 < n →
      (∫ ω, f (X T ω) ∂μ - ∫ ω, f (X (0 : ℝ≥0) ω) ∂μ)
        = (∑ k ∈ Finset.range n, ∫ ω, f' (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω
                - driftPath β (unifPart T n k) ω) ∂μ)
          + (1 / 2) * ((∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω
                - driftPath β (unifPart T n k) ω) ^ 2 ∂μ)
            + 2 * (∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω
                - driftPath β (unifPart T n k) ω)
              * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ)
            + (∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
              * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ))
          + (∫ ω, ∑ k ∈ Finset.range n, discreteTaylorRemainder f f' f''
              (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω) ∂μ) := by
    intro n hn
    have hTnn : unifPart T n n = T := by
      have hne : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      simp only [unifPart, div_self hne, one_mul]
    have hTn0 : unifPart T n 0 = 0 := by simp only [unifPart]; norm_num
    have hcellen : ∀ k : ℕ, ((unifPart T n (k + 1) : ℝ) - unifPart T n k)
        = (T : ℝ) / (n : ℝ) := fun k ↦ cellLen_eq (T := T) (n := n) k
    have hcellT : ∀ k : ℕ, ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ≤ (T : ℝ) := by
      intro k
      rw [hcellen k]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hT0 : (0 : ℝ) ≤ (T : ℝ) := NNReal.coe_nonneg T
      rw [div_le_iff₀ hn0]
      nlinarith [mul_le_mul_of_nonneg_left hn1 hT0]
    have hTfrac : ((T : ℝ) / (n : ℝ)) ≤ (T : ℝ) + 1 := by
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hT0 : (0 : ℝ) ≤ (T : ℝ) := NNReal.coe_nonneg T
      rw [div_le_iff₀ hn0]
      nlinarith [mul_le_mul_of_nonneg_left hn1 hT0]
    -- the per-cell increment decomposition
    have hΔ : ∀ k : ℕ, ∀ ω : Ω, X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω
        = (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
          + (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) := by
      intro k ω
      rw [hXrel (unifPart T n (k + 1)), hXrel (unifPart T n k)]
      show (c + driftPath β (unifPart T n (k + 1)) ω + M (unifPart T n (k + 1)) ω)
          - (c + driftPath β (unifPart T n k) ω + M (unifPart T n k) ω) = _
      ring
    -- measurability of the grid-value factors
    have hXm : ∀ t : ℝ≥0, Measurable (X t) := fun t ↦
      (hXadap t).measurable.mono ((natFiltration hBmeas).le t) le_rfl
    have hdpm : ∀ t : ℝ≥0, Measurable (driftPath β t) := fun t ↦
      (stronglyMeasurable_driftPath hBmeas hβadap hβcont hβbdd t).measurable.mono
        ((natFiltration hBmeas).le t) le_rfl
    have hf'Xk : ∀ k : ℕ, Measurable (fun ω ↦ f' (X (unifPart T n k) ω)) := fun k ↦
      hf'c.measurable.comp (hXm (unifPart T n k))
    have hf''Xk : ∀ k : ℕ, Measurable (fun ω ↦ f'' (X (unifPart T n k) ω)) := fun k ↦
      hf''c.measurable.comp (hXm (unifPart T n k))
    have hdMm : ∀ k : ℕ, Measurable (fun ω ↦ M (unifPart T n (k + 1)) ω
        - M (unifPart T n k) ω) := fun k ↦
      ((hMadap (unifPart T n (k + 1))).measurable.mono
        ((natFiltration hBmeas).le (unifPart T n (k + 1))) le_rfl).sub
      ((hMadap (unifPart T n k)).measurable.mono
        ((natFiltration hBmeas).le (unifPart T n k)) le_rfl)
    have hdIb : ∀ k : ℕ, ∀ ω : Ω, |driftPath β (unifPart T n (k + 1)) ω
        - driftPath β (unifPart T n k) ω| ≤ |Db| * ((unifPart T n (k + 1) : ℝ)
        - unifPart T n k) := fun k ω ↦
      abs_driftPath_sub_le hβcont
        (fun t ω ↦ (hβbdd t ω).trans (le_abs_self Db))
        (unifPart_mono T n (Nat.le_succ k)) ω
    have hdIbT : ∀ k : ℕ, ∀ ω : Ω, |driftPath β (unifPart T n (k + 1)) ω
        - driftPath β (unifPart T n k) ω| ≤ |Db| * ((T : ℝ) + 1) := by
      intro k ω
      calc |driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω|
          ≤ |Db| * ((T : ℝ) / (n : ℝ)) := by
            have h := hdIb k ω
            rw [← hcellen k]
            exact h
        _ ≤ |Db| * ((T : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hTfrac (abs_nonneg Db)
    -- per-cell integrabilities
    have hdMint : ∀ k : ℕ, Integrable (fun ω ↦ M (unifPart T n (k + 1)) ω
        - M (unifPart T n k) ω) μ := fun k ↦
      ((memLp_M hB hBmeas hδadap hδcont hδbdd hMeq (unifPart T n (k + 1))).sub
        (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq (unifPart T n k))).integrable
          one_le_two
    have hint1 : ∀ k : ℕ, Integrable (fun ω ↦ f' (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω
          - driftPath β (unifPart T n k) ω)) μ := by
      intro k
      refine Integrable.of_bound
        (((hf'Xk k).mul ((hdpm (unifPart T n (k + 1))).sub
          (hdpm (unifPart T n k)))).aestronglyMeasurable)
        (C1 * |Db| * ((T : ℝ) + 1)) ?_
      filter_upwards with ω
      show ‖f' (X (unifPart T n k) ω)
          * (driftPath β (unifPart T n (k + 1)) ω
            - driftPath β (unifPart T n k) ω)‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul]
      have hstep : |f' (X (unifPart T n k) ω)| * |driftPath β (unifPart T n (k + 1)) ω
          - driftPath β (unifPart T n k) ω| ≤ C1 * (|Db| * ((T : ℝ) + 1)) :=
        mul_le_mul (hg1 (X (unifPart T n k) ω)) (hdIbT k ω) (abs_nonneg _) hC1
      exact hstep.trans (le_of_eq (by ring))
    have hint2 : ∀ k : ℕ, Integrable (fun ω ↦ f' (X (unifPart T n k) ω)
        * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) μ := fun k ↦
      Integrable.mono' (hdMint k |>.abs.const_mul C1)
        (((hf'Xk k).mul (hdMm k)).aestronglyMeasurable)
        (Eventually.of_forall fun ω ↦ by
          show ‖f' (X (unifPart T n k) ω)
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)‖ ≤ _
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right (hg1 _) (abs_nonneg _))
    have hint3 : ∀ k : ℕ, Integrable (fun ω ↦ f'' (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω
          - driftPath β (unifPart T n k) ω) ^ 2) μ := by
      intro k
      refine Integrable.of_bound
        (((hf''Xk k).mul (((hdpm (unifPart T n (k + 1))).sub
          (hdpm (unifPart T n k))).pow_const 2)).aestronglyMeasurable)
        (C2 * |Db| ^ 2 * ((T : ℝ) + 1) ^ 2) ?_
      filter_upwards with ω
      show ‖f'' (X (unifPart T n k) ω)
          * (driftPath β (unifPart T n (k + 1)) ω
            - driftPath β (unifPart T n k) ω) ^ 2‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      have hstep : |f'' (X (unifPart T n k) ω)| * |driftPath β (unifPart T n (k + 1)) ω
          - driftPath β (unifPart T n k) ω| ^ 2
          ≤ C2 * ((|Db| * ((T : ℝ) + 1)) ^ 2) :=
        mul_le_mul (hg2 _) (pow_le_pow_left₀ (abs_nonneg _) (hdIbT k ω) 2)
          (sq_nonneg _) hC2
      refine hstep.trans ?_
      rw [show ((|Db| * ((T : ℝ) + 1)) ^ 2)
            = |Db| ^ 2 * ((T : ℝ) + 1) ^ 2 from by ring, mul_assoc]
    have hint4 : ∀ k : ℕ, Integrable (fun ω ↦ f'' (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω
          - driftPath β (unifPart T n k) ω)
        * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) μ := fun k ↦
      Integrable.mono' (hdMint k |>.abs.const_mul (C2 * (|Db| * ((T : ℝ) + 1))))
        (((hf''Xk k).mul ((hdpm (unifPart T n (k + 1))).sub
          (hdpm (unifPart T n k)))).mul (hdMm k) |>.aestronglyMeasurable)
        (Eventually.of_forall fun ω ↦ by
          show ‖f'' (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω
                - driftPath β (unifPart T n k) ω)
              * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)‖ ≤ _
          rw [Real.norm_eq_abs, abs_mul, abs_mul]
          have hstep : |f'' (X (unifPart T n k) ω)| * |driftPath β (unifPart T n (k + 1)) ω
              - driftPath β (unifPart T n k) ω| ≤ C2 * (|Db| * ((T : ℝ) + 1)) :=
            mul_le_mul (hg2 _) (hdIbT k ω) (abs_nonneg _) hC2
          exact mul_le_mul_of_nonneg_right hstep (abs_nonneg _))
    have hint5 : ∀ k : ℕ, Integrable (fun ω ↦ f'' (X (unifPart T n k) ω)
        * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2) μ := fun k ↦
      Integrable.mono'
        (((memLp_M hB hBmeas hδadap hδcont hδbdd hMeq
            (unifPart T n (k + 1))).sub
          (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq (unifPart T n k))).integrable_sq.const_mul C2)
        (((hf''Xk k).mul ((hdMm k).pow_const 2)).aestronglyMeasurable)
        (Eventually.of_forall fun ω ↦ by
          show ‖f'' (X (unifPart T n k) ω)
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2‖ ≤ _
          rw [Real.norm_eq_abs, abs_mul, abs_pow, sq_abs]
          exact mul_le_mul_of_nonneg_right (hg2 _) (sq_nonneg _))
    have hintStwo : ∀ k : ℕ, Integrable (fun ω : Ω ↦ 2 * (f'' (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
        * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω))
        + f'' (X (unifPart T n k) ω)
          * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2) μ := fun k ↦
      ((hint4 k).const_mul 2).add (hint5 k)
    have hint6 : ∀ k ∈ Finset.range n, Integrable (fun ω ↦
        discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
          (X (unifPart T n (k + 1)) ω)) μ := fun k hk ↦
      remainderCell_integrable hB hBmeas hδadap hδcont hδbdd hMeq
        (n := n) hn (k := k) (Finset.mem_range.mp hk) c hβcont hβbdd hXrel hXadap
        hf hf' hf'' hg3
    -- integrability of the full increments `f'·ΔX`, `f''·ΔX²`
    have hintΔX : ∀ k : ℕ, Integrable (fun ω ↦ f' (X (unifPart T n k) ω)
        * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) μ := by
      intro k
      refine ((hint1 k).add (hint2 k)).congr (Eventually.of_forall fun ω ↦ ?_)
      show f' (X (unifPart T n k) ω)
            * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
          + f' (X (unifPart T n k) ω)
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
        = f' (X (unifPart T n k) ω)
          * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)
      rw [hΔ k ω]
      ring
    have hintΔX2 : ∀ k : ℕ, Integrable (fun ω ↦ f'' (X (unifPart T n k) ω)
        * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2) μ := by
      intro k
      refine ((hint3 k).add (((hint4 k).const_mul 2).add (hint5 k))).congr
        (Eventually.of_forall fun ω ↦ ?_)
      show f'' (X (unifPart T n k) ω)
            * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2
          + (2 * (f'' (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω
                - driftPath β (unifPart T n k) ω)
              * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω))
            + f'' (X (unifPart T n k) ω)
              * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2)
        = f'' (X (unifPart T n k) ω)
          * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2
      rw [hΔ k ω]
      ring
    have hintS1int : Integrable (fun ω ↦ ∑ k ∈ Finset.range n,
        f' (X (unifPart T n k) ω)
          * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) μ :=
      integrable_finsetSum _ fun k _ ↦ hintΔX k
    have hintS2int : Integrable (fun ω ↦ ∑ k ∈ Finset.range n,
        f'' (X (unifPart T n k) ω)
          * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2) μ :=
      integrable_finsetSum _ fun k _ ↦ hintΔX2 k
    have hintS3int : Integrable (fun ω ↦ ∑ k ∈ Finset.range n,
        discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
          (X (unifPart T n (k + 1)) ω)) μ :=
      integrable_finsetSum _ fun k hk ↦ hint6 k hk
    have hintShalf : Integrable (fun ω : Ω ↦ (1 / 2) * (∑ k ∈ Finset.range n,
        f'' (X (unifPart T n k) ω)
          * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2)) μ :=
      hintS2int.const_mul (1 / 2)
    have hintShalfS3 : Integrable (fun ω : Ω ↦ (1 / 2) * (∑ k ∈ Finset.range n,
        f'' (X (unifPart T n k) ω)
          * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2)
        + (∑ k ∈ Finset.range n, discreteTaylorRemainder f f' f''
          (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω))) μ :=
      hintShalf.add hintS3int
    -- the per-path discrete Itô identity at the grid values of `X`
    have hpath : ∀ ω : Ω, f (X T ω) - f (X (0 : ℝ≥0) ω)
        = (∑ k ∈ Finset.range n, f' (X (unifPart T n k) ω)
            * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω))
          + ((1 / 2) * (∑ k ∈ Finset.range n, f'' (X (unifPart T n k) ω)
            * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2)
          + (∑ k ∈ Finset.range n, discreteTaylorRemainder f f' f''
            (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω))) := by
      intro ω
      have hformula := discrete_ito_formula (N := n)
        (X := fun j : ℕ ↦ X (unifPart T n j) ω) f f' f''
      simp only [hTnn, hTn0] at hformula
      rw [add_assoc] at hformula
      exact hformula
    -- the first-order martingale terms die exactly
    have hzero1 : (∑ k ∈ Finset.range n, ∫ ω, f' (X (unifPart T n k) ω)
        * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ) = 0 := by
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      exact mul_trueIncr_expect_eq_zero hB hBmeas hδadap hδcont hδbdd hMadap hMeq
        (unifPart_mono T n (Nat.le_succ k))
        ((hf'c.measurable.comp (hXadap (unifPart T n k)).measurable).stronglyMeasurable)
        (fun ω ↦ hg1 (X (unifPart T n k) ω))
    -- the per-cell integral splits
    have hintS1 : (∫ ω, (∑ k ∈ Finset.range n, f' (X (unifPart T n k) ω)
          * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) ∂μ)
        = (∑ k ∈ Finset.range n, ∫ ω, f' (X (unifPart T n k) ω)
            * (driftPath β (unifPart T n (k + 1)) ω
              - driftPath β (unifPart T n k) ω) ∂μ)
          + (∑ k ∈ Finset.range n, ∫ ω, f' (X (unifPart T n k) ω)
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ) := by
      rw [integral_finsetSum (μ := μ) (s := Finset.range n)
          (f := fun (k : ℕ) (ω : Ω) ↦ f' (X (unifPart T n k) ω)
            * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω))
          (fun k _ ↦ hintΔX k)]
      have hsplit : ∀ k ∈ Finset.range n,
          (∫ ω, f' (X (unifPart T n k) ω)
              * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ∂μ)
            = (∫ ω, f' (X (unifPart T n k) ω)
                * (driftPath β (unifPart T n (k + 1)) ω
                  - driftPath β (unifPart T n k) ω) ∂μ)
              + (∫ ω, f' (X (unifPart T n k) ω)
                * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ) := by
        intro k _
        rw [← integral_add (hint1 k) (hint2 k)]
        exact integral_congr_ae (Eventually.of_forall fun ω ↦ by
          show f' (X (unifPart T n k) ω)
              * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)
            = f' (X (unifPart T n k) ω)
                * (driftPath β (unifPart T n (k + 1)) ω
                  - driftPath β (unifPart T n k) ω)
              + f' (X (unifPart T n k) ω)
                * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
          rw [hΔ k ω]
          ring)
      rw [Finset.sum_congr rfl (fun k hk ↦ hsplit k hk), Finset.sum_add_distrib]
    have hintS2 : (∫ ω, (∑ k ∈ Finset.range n, f'' (X (unifPart T n k) ω)
          * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2) ∂μ)
        = (∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
            * (driftPath β (unifPart T n (k + 1)) ω
              - driftPath β (unifPart T n k) ω) ^ 2 ∂μ)
          + 2 * (∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
            * (driftPath β (unifPart T n (k + 1)) ω
              - driftPath β (unifPart T n k) ω)
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ)
          + (∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ) := by
      rw [integral_finsetSum (μ := μ) (s := Finset.range n)
          (f := fun (k : ℕ) (ω : Ω) ↦ f'' (X (unifPart T n k) ω)
            * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2)
          (fun k _ ↦ hintΔX2 k)]
      have hsplit : ∀ k ∈ Finset.range n,
          (∫ ω, f'' (X (unifPart T n k) ω)
              * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2 ∂μ)
            = (∫ ω, f'' (X (unifPart T n k) ω)
                * (driftPath β (unifPart T n (k + 1)) ω
                  - driftPath β (unifPart T n k) ω) ^ 2 ∂μ)
              + (2 * (∫ ω, f'' (X (unifPart T n k) ω)
                * (driftPath β (unifPart T n (k + 1)) ω
                  - driftPath β (unifPart T n k) ω)
                * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ)
              + (∫ ω, f'' (X (unifPart T n k) ω)
                * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)) := by
        intro k _
        calc ∫ ω, f'' (X (unifPart T n k) ω)
              * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2 ∂μ
            = ∫ ω, (f'' (X (unifPart T n k) ω)
                * (driftPath β (unifPart T n (k + 1)) ω
                  - driftPath β (unifPart T n k) ω) ^ 2
              + (2 * (f'' (X (unifPart T n k) ω)
                * (driftPath β (unifPart T n (k + 1)) ω
                  - driftPath β (unifPart T n k) ω)
                * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω))
              + f'' (X (unifPart T n k) ω)
                * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2)) ∂μ :=
              integral_congr_ae (Eventually.of_forall fun ω ↦ by
                show f'' (X (unifPart T n k) ω)
                    * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2 = _
                rw [hΔ k ω]
                ring)
          _ = (∫ ω, f'' (X (unifPart T n k) ω)
                * (driftPath β (unifPart T n (k + 1)) ω
                  - driftPath β (unifPart T n k) ω) ^ 2 ∂μ)
              + (∫ ω, (2 * (f'' (X (unifPart T n k) ω)
                  * (driftPath β (unifPart T n (k + 1)) ω
                    - driftPath β (unifPart T n k) ω)
                  * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω))
                + f'' (X (unifPart T n k) ω)
                  * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2) ∂μ) :=
              integral_add (hint3 k) (hintStwo k)
          _ = (∫ ω, f'' (X (unifPart T n k) ω)
                * (driftPath β (unifPart T n (k + 1)) ω
                  - driftPath β (unifPart T n k) ω) ^ 2 ∂μ)
              + (2 * (∫ ω, f'' (X (unifPart T n k) ω)
                  * (driftPath β (unifPart T n (k + 1)) ω
                    - driftPath β (unifPart T n k) ω)
                  * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ)
                + (∫ ω, f'' (X (unifPart T n k) ω)
                  * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)) := by
              rw [integral_add ((hint4 k).const_mul 2) (hint5 k), integral_const_mul]
      rw [Finset.sum_congr rfl (fun k hk ↦ hsplit k hk), Finset.sum_add_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    -- assemble the per-partition identity
    calc (∫ ω, f (X T ω) ∂μ - ∫ ω, f (X (0 : ℝ≥0) ω) ∂μ)
        = (∫ ω, ((∑ k ∈ Finset.range n, f' (X (unifPart T n k) ω)
              * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω))
            + ((1 / 2) * (∑ k ∈ Finset.range n, f'' (X (unifPart T n k) ω)
              * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2)
            + (∑ k ∈ Finset.range n, discreteTaylorRemainder f f' f''
              (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω)))) ∂μ) := by
          rw [← integral_sub (hXint T) (hXint (0 : ℝ≥0))]
          exact integral_congr_ae (Eventually.of_forall fun ω ↦ hpath ω)
      _ = (∫ ω, (∑ k ∈ Finset.range n, f' (X (unifPart T n k) ω)
              * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) ∂μ)
          + (∫ ω, ((1 / 2) * (∑ k ∈ Finset.range n, f'' (X (unifPart T n k) ω)
              * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2)
            + (∑ k ∈ Finset.range n, discreteTaylorRemainder f f' f''
              (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω))) ∂μ) := by
          rw [integral_add hintS1int hintShalfS3]
      _ = (∫ ω, (∑ k ∈ Finset.range n, f' (X (unifPart T n k) ω)
              * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) ∂μ)
          + (1 / 2) * (∫ ω, (∑ k ∈ Finset.range n, f'' (X (unifPart T n k) ω)
              * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2) ∂μ)
          + (∫ ω, (∑ k ∈ Finset.range n, discreteTaylorRemainder f f' f''
              (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω)) ∂μ) := by
          rw [integral_add hintShalf hintS3int, integral_const_mul]
          ring
      _ = (∑ k ∈ Finset.range n, ∫ ω, f' (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω
                - driftPath β (unifPart T n k) ω) ∂μ)
          + (1 / 2) * ((∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω
                - driftPath β (unifPart T n k) ω) ^ 2 ∂μ)
            + 2 * (∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω
                - driftPath β (unifPart T n k) ω)
              * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ)
            + (∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
              * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ))
          + (∫ ω, ∑ k ∈ Finset.range n, discreteTaylorRemainder f f' f''
              (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω) ∂μ) := by
          rw [hintS1, hintS2, hzero1]
          ring
  -- the limit of the right-hand side
  have hR : Tendsto (fun n : ℕ ↦
      (∑ k ∈ Finset.range n, ∫ ω, f' (X (unifPart T n k) ω)
          * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ∂μ)
        + (1 / 2) * ((∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
            * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2 ∂μ)
          + 2 * (∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
            * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ)
          + (∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ))
        + (∫ ω, ∑ k ∈ Finset.range n, discreteTaylorRemainder f f' f''
            (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω) ∂μ))
    atTop (𝓝 ((∫ s in Set.Ioc (0 : ℝ≥0) T,
          (∫ ω, f' (X s ω) * β s ω ∂μ) ∂ItoIntegralL2.timeMeasure)
        + (1 / 2) * ((0 : ℝ) + 2 * 0
          + (∫ s in Set.Ioc (0 : ℝ≥0) T,
              (∫ ω, f'' (X s ω) * (δ s ω * δ s ω) ∂μ) ∂ItoIntegralL2.timeMeasure))
        + 0)) :=
    (hA.add ((tendsto_const_nhds (x := (1 : ℝ) / 2)).mul
      ((hB0.add ((tendsto_const_nhds (x := (2 : ℝ))).mul hC0)).add hD0))).add hE0
  have hL : Tendsto (fun n : ℕ ↦
      (∑ k ∈ Finset.range n, ∫ ω, f' (X (unifPart T n k) ω)
          * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ∂μ)
        + (1 / 2) * ((∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
            * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2 ∂μ)
          + 2 * (∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
            * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ)
          + (∑ k ∈ Finset.range n, ∫ ω, f'' (X (unifPart T n k) ω)
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ))
        + (∫ ω, ∑ k ∈ Finset.range n, discreteTaylorRemainder f f' f''
            (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω) ∂μ))
    atTop (𝓝 (∫ ω, f (X T ω) ∂μ - ∫ ω, f (X (0 : ℝ≥0) ω) ∂μ)) := by
    refine (tendsto_const_nhds
      (x := (∫ ω, f (X T ω) ∂μ - ∫ ω, f (X (0 : ℝ≥0) ω) ∂μ))).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact key n hn
  have hfin := tendsto_nhds_unique hL hR
  -- the band integrabilities and the merge of the two time integrals
  have hbdd_d : ∀ s : ℝ≥0, ∀ ω : Ω, |f' (X s ω) * β s ω| ≤ C1 * |Db| := by
    intro s ω
    rw [abs_mul]
    exact mul_le_mul (hg1 (X s ω)) (le_trans (hβbdd s ω) (le_abs_self Db)) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hg1 0))
  have hDsq2 : |Dd| * |Dd| = Dd * Dd := by
    rcases le_total 0 Dd with h | h
    · rw [abs_of_nonneg h]
    · rcases eq_or_lt_of_le h with rfl | h'
      · simp
      · rw [abs_of_neg h']
        ring
  have hbdd_q : ∀ s : ℝ≥0, ∀ ω : Ω, |f'' (X s ω) * (δ s ω * δ s ω)| ≤ C2 * (Dd * Dd) := by
    intro s ω
    have hd2 : |δ s ω * δ s ω| ≤ |Dd| * |Dd| := by
      rw [abs_mul]
      exact mul_le_mul (le_trans (hδbdd s ω) (le_abs_self Dd))
        (le_trans (hδbdd s ω) (le_abs_self Dd)) (abs_nonneg _) (abs_nonneg Dd)
    rw [abs_mul]
    refine (mul_le_mul (hg2 (X s ω)) hd2 (abs_nonneg _)
      (le_trans (abs_nonneg _) (hg2 0))).trans ?_
    rw [hDsq2]
  have hdm : ∀ s : ℝ≥0, Measurable (fun ω ↦ f' (X s ω) * β s ω) := fun s ↦
    (hf'c.measurable.comp
      ((hXadap s).measurable.mono ((natFiltration hBmeas).le s) le_rfl)).mul
      ((hβadap s).measurable.mono ((natFiltration hBmeas).le s) le_rfl)
  have hqm : ∀ s : ℝ≥0, Measurable (fun ω ↦ f'' (X s ω) * (δ s ω * δ s ω)) := fun s ↦
    (hf''c.measurable.comp
      ((hXadap s).measurable.mono ((natFiltration hBmeas).le s) le_rfl)).mul
      (((hδadap s).measurable.mono ((natFiltration hBmeas).le s) le_rfl).mul
        ((hδadap s).measurable.mono ((natFiltration hBmeas).le s) le_rfl))
  have hcontd : Continuous fun s : ℝ≥0 ↦ ∫ ω, f' (X s ω) * β s ω ∂μ :=
    continuous_mean_of_bdd_cont hdm (fun ω ↦ (hf'c.comp (hXcont ω)).mul (hβcont ω)) hbdd_d
  have hcontq : Continuous fun s : ℝ≥0 ↦ ∫ ω, f'' (X s ω) * (δ s ω * δ s ω) ∂μ :=
    continuous_mean_of_bdd_cont hqm
      (fun ω ↦ (hf''c.comp (hXcont ω)).mul ((hδcont ω).mul (hδcont ω))) hbdd_q
  have hdint : IntegrableOn (fun s : ℝ≥0 ↦ (∫ ω, f' (X s ω) * β s ω ∂μ))
      (Set.Ioc (0 : ℝ≥0) T) ItoIntegralL2.timeMeasure := by
    haveI : IsFiniteMeasure
        (ItoIntegralL2.timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        ItoIntegralL2.timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
    refine Integrable.of_bound
      (μ := ItoIntegralL2.timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T))
      ((hcontd.measurable.aestronglyMeasurable).mono_measure Measure.restrict_le_self)
      (C1 * |Db|) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s _
    show ‖(fun s : ℝ≥0 ↦ (∫ ω, f' (X s ω) * β s ω ∂μ)) s‖ ≤ C1 * |Db|
    rw [Real.norm_eq_abs]
    calc |∫ ω, f' (X s ω) * β s ω ∂μ| ≤ ∫ ω, |f' (X s ω) * β s ω| ∂μ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ ω, (C1 * |Db|) ∂μ := integral_mono_of_nonneg
            (Eventually.of_forall fun ω ↦ abs_nonneg _) (integrable_const _)
            (Eventually.of_forall fun ω ↦ hbdd_d s ω)
      _ = C1 * |Db| := by rw [integral_const]; simp
  have hqint : IntegrableOn (fun s : ℝ≥0 ↦ (∫ ω, f'' (X s ω) * (δ s ω * δ s ω) ∂μ))
      (Set.Ioc (0 : ℝ≥0) T) ItoIntegralL2.timeMeasure := by
    haveI : IsFiniteMeasure
        (ItoIntegralL2.timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        ItoIntegralL2.timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
    refine Integrable.of_bound
      (μ := ItoIntegralL2.timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T))
      ((hcontq.measurable.aestronglyMeasurable).mono_measure Measure.restrict_le_self)
      (C2 * (Dd * Dd)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s _
    show ‖(fun s : ℝ≥0 ↦ (∫ ω, f'' (X s ω) * (δ s ω * δ s ω) ∂μ)) s‖ ≤ C2 * (Dd * Dd)
    rw [Real.norm_eq_abs]
    calc |∫ ω, f'' (X s ω) * (δ s ω * δ s ω) ∂μ|
          ≤ ∫ ω, |f'' (X s ω) * (δ s ω * δ s ω)| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ ω, (C2 * (Dd * Dd)) ∂μ := integral_mono_of_nonneg
            (Eventually.of_forall fun ω ↦ abs_nonneg _) (integrable_const _)
            (Eventually.of_forall fun ω ↦ hbdd_q s ω)
      _ = C2 * (Dd * Dd) := by rw [integral_const]; simp
  have hintqhalf : IntegrableOn (fun s : ℝ≥0 ↦ (1 / 2) * (∫ ω, f'' (X s ω)
      * (δ s ω * δ s ω) ∂μ)) (Set.Ioc (0 : ℝ≥0) T) ItoIntegralL2.timeMeasure :=
    hqint.const_mul (1 / 2)
  have hmerge : (∫ s in Set.Ioc (0 : ℝ≥0) T,
        ((∫ ω, f' (X s ω) * β s ω ∂μ)
          + (1 / 2) * (∫ ω, f'' (X s ω) * (δ s ω * δ s ω) ∂μ)) ∂ItoIntegralL2.timeMeasure)
      = (∫ s in Set.Ioc (0 : ℝ≥0) T, (∫ ω, f' (X s ω) * β s ω ∂μ) ∂ItoIntegralL2.timeMeasure)
        + (1 / 2) * (∫ s in Set.Ioc (0 : ℝ≥0) T,
            (∫ ω, f'' (X s ω) * (δ s ω * δ s ω) ∂μ) ∂ItoIntegralL2.timeMeasure) := by
    rw [integral_add (μ := ItoIntegralL2.timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T))
      hdint hintqhalf, integral_const_mul]
  -- conclude
  simp only [add_zero, mul_zero, zero_add] at hfin
  rw [hmerge]
  linarith

end MathFin.StageFiveD
