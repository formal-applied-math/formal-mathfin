/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
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

/-! # The increment energy of an adapted Itô integral (the discrete route, stages 2–3)

The first layer of the integrated Itô–drift identity for adapted coefficients
(`ItoFormulaAdaptedDrift`): the band-to-slice conversion `bandIntegral_slice`, the expectation
pull-out `integral_mul_condExp_eq`, the increment-energy law `incrementEnergy`
(`𝔼[(M_v − M_u)²] = ∫_{(u,v]} δ² d(trim)`), and the left-endpoint step approximants
`deltaStepLp` with their `L²` convergence `deltaStepLp_tendsto`. `M` is a hypothesis: a
`natFiltration`-adapted version of the Itô integral of `δ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace MathFin.ItoDriftConditional

open MathFin ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral
  QuadraticVariationL2 ItoIntegralBrownian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Stage 2 — the bounded *adapted* coefficients (`β`, `δ` random)

(Stage 1, the constant-coefficient identity, is `ito_drift_expectation_identity` in
`MathFin/Foundations/ItoDriftExpectation`.)

The integrated Itô–drift identity for an Itô process with random adapted coefficients.
The data: a pre-Brownian motion `B` with measurable sections (path continuity of `B` is not
assumed), bounded adapted path-continuous `β, δ`, and two hypothesized processes: a
`natFiltration`-adapted `M` with `M t =ᵐ (δ●B)_t` for every
`t ≥ 0` (`hMeq`, the process values of `itoProcessCLM` at the σ-realization `processToLp δ`),
and an `X` with `X t = c + ∫₀ᵗ β_s ds + M t` (`hXrel`) whose paths are continuous almost surely
(`hXcont`). For `B` with continuous paths, the constructed Itô process provides such an `M` (see
the module docstring of `ItoFormulaAdaptedDrift`).

`ΔX` over a cell splits into the drift increment plus the martingale increment. The proof is
the partition/Taylor skeleton of `ItoFormulaTD` (with `f_t = 0`) at the path `k ↦ X_{tₖ}`
(`MathFin.discrete_ito_formula` — an exact per-path identity), with the three terms
dispatched by: pathwise Riemann sums (drift), the summed weighted increment isometry at the
adapted weight `f''(X)` (martingale square), and a cubic-moment bound (Taylor remainder).
Taking expectations turns
the pathwise identity into the integrated one; the drift integral crosses the expectation by
the stage-1 Fubini lemma `expectation_pathIntegral_eq`.

The per-cell second moments `E[(M_v−M_u)²]` come from the martingale property of `M`
(inherited a.e. from `itoProcessCLM`) and the time-indexed Itô isometry
`itoProcessCLM_norm_sq`. The blocks use `M` through `hMeq` and `hMadap`; almost sure path
continuity enters through the hypothesis `hXcont`. -/

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
theorem sqIntegral_of_Lp {ν : Measure Ω} (g : Lp ℝ 2 ν) :
    ∫ ω, g ω ^ 2 ∂ν = ‖g‖ ^ 2 := (lp_two_norm_sq g).symm

/-- **Expansion of the squared sum under the integral** (all three integrands integrable):
`E[(a+b)²] = E[a²] + 2·E[a·b] + E[b²]`. -/
theorem integral_sq_add {α : Type*} {mα : MeasurableSpace α} {ν : Measure α}
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
          change (Set.Ioc u v ×ˢ (Set.univ : Set Ω)).indicator (Function.uncurry ψ) (s, ω) = _
          rw [hslice ω])

/-! ### Stages 3–5 — the weighted increment isometry, the third-moment bound, and the
assembly of the adapted drift identity

The data: a pre-Brownian `B` with measurable sections; bounded adapted path-continuous
`β, δ`; and the hypothesized `M` — a `natFiltration`-strongly-adapted *version* of the Itô
integral of `δ` (`M t =ᵐ (δ●B)_t` for every `t`, the CLM process values of the σ-realization
`processToLp δ`). The process under test, `X t = c + ∫₀ᵗ β_s ds + M t`, is likewise a
hypothesis (`hXrel`), and its paths are assumed continuous almost surely (`hXcont`).

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
          change (M v ω - M u ω) ^ 2 = M v ω ^ 2 - 2 * (M u ω * M v ω) + M u ω ^ 2
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
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hbridge ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  have hN' := hN n hn
  rw [dist_eq_norm] at hN'
  rw [key n, dist_eq_norm, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  exact hN' 

end AdaptedData

end MathFin.ItoDriftConditional
