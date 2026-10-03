/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralAgainstMartingale
public import BrownianMotion.StochasticIntegral.StochasticIntegral

/-! # The integral against an Itô integral is a stochastic integral, in BrownianMotion's sense

BrownianMotion's `StochasticIntegral.lean` characterises a stochastic integral axiomatically.
`IsRiemannStieltjesExtension P Y 𝓕 I S` asks that a map `I` from processes to random variables,
defined on a domain `S`, return the Riemann–Stieltjes sum `X·(Y_j − Y_i)` on every elementary
process `𝟙_{(i,j]}·X` with a simple `𝓕_i`-measurable coefficient (and `X·(Y_i − Y_0)` on
`𝟙_{[0,i]}·X`), be linear, respect indistinguishability, and pass to the limit under dominated
convergence. `IsStochasticIntegral` adds that `I` agrees almost surely with every such extension
on the intersection of their domains.

This file instantiates both for the integral against `M = φ●B` of `ItoIntegralAgainstMartingale`
(`isStochasticIntegral`), with integrator `M` stopped at `T`, the natural Brownian filtration, and
the processes indistinguishable from a predictable process square-integrable against the bracket
`⟨M⟩` as domain. BrownianMotion does not instantiate the predicate anywhere at this pin.

## Three design points

* **The integrator is stopped at `T`.** The upstream integral runs over the whole time axis, ours
  over `[0, T]`. `integrator` is `t ↦ M_{t∧T}`, so a band past `T` integrates to `0` on both
  sides.
* **The domain is closed under indistinguishability, not `⟨M⟩`-a.e. equality.** The predicate
  asks for that closure, and a process indistinguishable from a predictable one need not be
  predictable, or even jointly measurable, whatever the filtration. The domain is the processes
  with a predictable version (`IsPredictableVersion`),
  and the integral reads the `L²(⟨M⟩)` class of a version, which does not depend on the version
  chosen (`integrandLp_eq`, through `ae_bracketMeasure_of_ae_forall`).
* **Uniqueness is a monotone-class argument, not density.** An extension in the upstream sense
  is not assumed `L²`-continuous, nor even defined on `L²(⟨M⟩)`, so `itoIntegralAgainst_unique`,
  which is uniqueness among continuous linear maps, does not reach it. Every extension does have
  dominated convergence, and
  the proof runs on that: agreement on predictable indicators by a Dynkin argument over the
  predictable rectangles, then on simple functions, on bounded processes, and finally on the whole
  common domain by truncation, a process dominating its own truncations.

Mathlib at this pin has dominated convergence in `L^p` only for `p = 1`
(`tendsto_lintegral_norm_of_dominated_convergence`). Elsewhere the library reaches `L²` through
BrownianMotion's `uniformIntegrable_of_dominated_singleton` and Vitali's theorem
(`tendsto_Lp_finite_of_tendsto_ae`), which need `1 ≤ p` and a finite measure. Here it is proved
directly, for every `p < ∞` and every measure (`tendsto_eLpNorm_sub_of_dominated_convergence`).

## Result

* `isStochasticIntegral` — **the characterisation**: the integral against `M` is an
  `IsStochasticIntegral` for `M` stopped at `T`.
* `isRiemannStieltjesExtension` — its extension half: elementary values, linearity,
  indistinguishability, dominated convergence (`sIntegral_dct`).
* `sIntegral_ae_eq_of_isRiemannStieltjesExtension` — its uniqueness half: every extension agrees
  with this one on the common domain.
* `sIntegral_band`, `sIntegral_bottomBand` — the elementary values, on processes.
* `tendsto_eLpNorm_sub_of_dominated_convergence` — dominated convergence in `L^p`, `p < ∞`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

section DominatedLp

variable {α E : Type*} {m : MeasurableSpace α} {ν : Measure α} [NormedAddCommGroup E]

/-- **Dominated convergence in `L^p`**, for `p < ∞`: a sequence that converges almost everywhere
and is dominated by a single `L^p` function converges to its limit in `L^p`. The measure is
arbitrary and `p < 1` is allowed. -/
theorem tendsto_eLpNorm_sub_of_dominated_convergence {p : ℝ≥0∞} (hp : p ≠ ∞)
    {F : ℕ → α → E} {f : α → E} (bound : α → ℝ)
    (F_measurable : ∀ n, AEStronglyMeasurable (F n) ν) (bound_memLp : MemLp bound p ν)
    (h_bound : ∀ n, ∀ᵐ x ∂ν, ‖F n x‖ ≤ bound x)
    (h_lim : ∀ᵐ x ∂ν, Tendsto (fun n ↦ F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n ↦ eLpNorm (F n - f) p ν) atTop (𝓝 0) := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hfm : AEStronglyMeasurable f ν := aestronglyMeasurable_of_tendsto_ae _ F_measurable h_lim
  -- the `p`-th powers of `‖F n − f‖ₑ` are dominated by `(2‖bound‖ₑ)^p` and tend to `0`
  have hdom (n : ℕ) : (fun x ↦ ‖(F n - f) x‖ₑ ^ p.toReal) ≤ᵐ[ν]
      fun x ↦ (2 * ‖bound x‖ₑ) ^ p.toReal := by
    filter_upwards [h_lim, ae_all_iff.2 h_bound] with x hx hall
    have hle (y : E) (hy : ‖y‖ ≤ bound x) : ‖y‖ₑ ≤ ‖bound x‖ₑ :=
      enorm_le_iff_norm_le.2 (hy.trans (Real.le_norm_self _))
    gcongr
    calc ‖(F n - f) x‖ₑ ≤ ‖F n x‖ₑ + ‖f x‖ₑ := enorm_sub_le
      _ ≤ ‖bound x‖ₑ + ‖bound x‖ₑ :=
        add_le_add (hle _ (hall n)) (hle _ (le_of_tendsto' hx.norm hall))
      _ = 2 * ‖bound x‖ₑ := (two_mul _).symm
  have hfin : ∫⁻ x, (2 * ‖bound x‖ₑ) ^ p.toReal ∂ν ≠ ∞ := by
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp_pos.le]
    rw [lintegral_const_mul' _ _ (by simp)]
    exact ENNReal.mul_ne_top (by simp)
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp bound_memLp.eLpNorm_lt_top).ne
  have hzero : ∀ᵐ x ∂ν, Tendsto (fun n ↦ ‖(F n - f) x‖ₑ ^ p.toReal) atTop (𝓝 0) := by
    filter_upwards [h_lim] with x hx
    simpa [ENNReal.zero_rpow_of_pos hp_pos] using
      (tendsto_sub_nhds_zero_iff.2 hx).enorm.ennrpow_const p.toReal
  have hlin := tendsto_lintegral_of_dominated_convergence' _
    (fun n ↦ ((F_measurable n).sub hfm).enorm.pow_const _) hdom hfin hzero
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp]
  simpa [ENNReal.zero_rpow_of_pos (inv_pos.2 hp_pos)] using hlin.ennrpow_const (1 / p.toReal)

end DominatedLp

namespace StochasticIntegralCharacterisation

open ProbabilityTheory ItoIntegralAgainstMartingale ItoIntegralCLM ItoIntegralL2 LpMulIsometry
  ItoIntegralProcessGeneral

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-! ### From "every time, almost surely" to "`⟨M⟩`-almost everywhere" -/

/-- A property of `(t, ω)` that holds `μ`-almost surely for every `t` at once holds
`⟨M⟩`-almost everywhere, provided the set where it holds is predictable.

The exceptional set then sits inside `ℝ≥0 × N` for a `μ`-null `N`. That product need not be
predictable, the natural filtration not being complete, which is why the predictability of the
set itself is assumed: it is what lets the trim be computed as the product measure. -/
theorem ae_bracketMeasure_of_ae_forall (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {q : ℝ≥0 × Ω → Prop}
    (hq : MeasurableSet[(natFiltration (mΩ := mΩ) hBmeas).predictable] {z | q z})
    (h : ∀ᵐ ω ∂μ, ∀ t, q (t, ω)) :
    ∀ᵐ z ∂(bracketMeasure (μ := μ) T hBmeas φ), q z := by
  have hnull : trimMeasure_T (μ := μ) T hBmeas {z | ¬ q z} = 0 := by
    unfold trimMeasure_T
    rw [trim_measurableSet_eq _
      (show MeasurableSet[(natFiltration (mΩ := mΩ) hBmeas).predictable] {z | ¬ q z} from hq.compl)]
    refine measure_mono_null (t := Set.univ ×ˢ {ω | ¬ ∀ t, q (t, ω)})
      (fun z hz ↦ ⟨Set.mem_univ _, fun hall ↦ hz (hall z.1)⟩) ?_
    rw [Measure.prod_prod, ae_iff.1 h, mul_zero]
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_iff.2 hnull)

/-! ### The domain: processes with a predictable square-integrable version -/

variable (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))

/-- `X'` is a **predictable square-integrable version** of the process `X`: predictable as a
function of `(t, ω)`, square-integrable against the bracket `⟨M⟩`, and indistinguishable from
`X`. Indistinguishability, not `⟨M⟩`-a.e. equality, is the relation the upstream
characterisation is stated for, and it is genuinely different: a process indistinguishable from
a predictable one need not be predictable, or even jointly measurable, whatever the filtration. -/
def IsPredictableVersion (X X' : ℝ≥0 → Ω → ℝ) : Prop :=
  Measurable[(natFiltration (mΩ := mΩ) hBmeas).predictable] (Function.uncurry X') ∧
    MemLp (Function.uncurry X') 2 (bracketMeasure (μ := μ) T hBmeas φ) ∧ X ≡ᵐ[μ] X'

/-- **The domain** of the integral against `M`: the processes with a predictable
square-integrable version. -/
def domain : Set (ℝ≥0 → Ω → ℝ) := {X | ∃ X', IsPredictableVersion T hBmeas φ X X'}

variable {T hBmeas φ}

/-- Two predictable versions of one process are equal `⟨M⟩`-almost everywhere. -/
theorem uncurry_ae_eq_of_isPredictableVersion {X X₁ X₂ : ℝ≥0 → Ω → ℝ}
    (h₁ : IsPredictableVersion T hBmeas φ X X₁) (h₂ : IsPredictableVersion T hBmeas φ X X₂) :
    Function.uncurry X₁ =ᵐ[bracketMeasure (μ := μ) T hBmeas φ] Function.uncurry X₂ := by
  refine ae_bracketMeasure_of_ae_forall T hBmeas φ
    (q := fun z ↦ Function.uncurry X₁ z = Function.uncurry X₂ z)
    (measurableSet_eq_fun h₁.1 h₂.1) ?_
  filter_upwards [h₁.2.2, h₂.2.2] with ω h1 h2 t
  exact (h1 t).symm.trans (h2 t)

variable (T hBmeas φ) in
open scoped Classical in
/-- The class in `L²(⟨M⟩)` of a process in the domain, read off any predictable version
(`integrandLp_eq`); `0` off the domain. -/
noncomputable def integrandLp (X : ℝ≥0 → Ω → ℝ) : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas φ) :=
  if h : X ∈ domain T hBmeas φ then h.choose_spec.2.1.toLp _ else 0

/-- `integrandLp` does not depend on the version chosen. -/
theorem integrandLp_eq {X X' : ℝ≥0 → Ω → ℝ} (h : IsPredictableVersion T hBmeas φ X X') :
    integrandLp T hBmeas φ X = h.2.1.toLp _ := by
  have hX : X ∈ domain T hBmeas φ := ⟨X', h⟩
  rw [integrandLp, dif_pos hX]
  exact MemLp.toLp_congr _ _ (uncurry_ae_eq_of_isPredictableVersion hX.choose_spec h)

/-! ### The integrator and the integral -/

variable (T hBmeas φ) in
/-- **The integrator**: `M = φ●B` stopped at `T`, `t ↦ M_{t ∧ T}`, read through a representative
of each `M_t`. The upstream predicate integrates over the whole time axis; stopping the
integrator at `T` is what makes that the integral over `[0, T]`. The predicate reads the
integrator only through increments `Y_j − Y_i` almost surely, at fixed times, so the choice of
representatives does not matter. -/
noncomputable def integrator (hB : IsPreBrownianReal B μ) : ℝ≥0 → Ω → ℝ :=
  fun t ↦ ⇑(itoProcessCLM hB T (min t T) hBmeas φ)

variable (T hBmeas φ) in
/-- **The integral against `M`, on processes**: integrate the `L²(⟨M⟩)` class of the process.
Named after the upstream `SIntegral`, the type of maps from processes to random variables. -/
noncomputable def sIntegral (hB : IsPreBrownianReal B μ) : (ℝ≥0 → Ω → ℝ) → Ω → ℝ :=
  fun X ↦ ⇑(itoIntegralAgainstCLM hB T hBmeas φ (integrandLp T hBmeas φ X))

/-- The bracket lives on `(0, T] × Ω`: it charges neither the time origin nor any time after `T`.
Read off `trim_T` through the density. -/
theorem ae_fst_mem_Ioc_bracketMeasure :
    ∀ᵐ z ∂(bracketMeasure (μ := μ) T hBmeas φ), z.1 ∈ Set.Ioc 0 T :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_fst_mem_Ioc_trimMeasure_T T hBmeas)

/-! ### The elementary processes -/

omit mΩ in
/-- The band process `1_{(i,j]}(t)·X(ω)`, uncurried, is the elementary integrand. -/
theorem uncurry_band (i j : ℝ≥0) (X : Ω → ℝ) :
    Function.uncurry (fun k ω ↦ if k ∈ Set.Ioc i j then X ω else 0) = elemIntegrand i j X := by
  funext z
  simp only [Function.uncurry, elemIntegrand, Set.indicator_apply]
  split_ifs <;> simp

omit [IsProbabilityMeasure μ] in
/-- A band with a bounded `𝓕_i`-measurable coefficient is its own predictable version. -/
theorem isPredictableVersion_band {i j : ℝ≥0} (hij : i ≤ j) {X : Ω → ℝ}
    (hXm : Measurable[natFiltration hBmeas i] X) {C : ℝ} (hC : ∀ ω, ‖X ω‖ ≤ C) :
    IsPredictableVersion T hBmeas φ (fun k ω ↦ if k ∈ Set.Ioc i j then X ω else 0)
      (fun k ω ↦ if k ∈ Set.Ioc i j then X ω else 0) := by
  have hm := measurable_elemIntegrand hBmeas hij hXm
  refine ⟨by rw [uncurry_band]; exact hm, ?_, .rfl⟩
  rw [uncurry_band]
  exact MemLp.of_bound hm.aestronglyMeasurable C
    (Eventually.of_forall fun z ↦ norm_elemIntegrand_le hC z)

/-- **The band identity, on processes**: the integral of `1_{(i,j]}·X` against `M` is
`X·(M_{j∧T} − M_{i∧T})`, with the band cut off at `T`. -/
theorem sIntegral_band (hB : IsPreBrownianReal B μ) {i j : ℝ≥0} (hij : i ≤ j) {X : Ω → ℝ}
    (hXm : Measurable[natFiltration hBmeas i] X) {C : ℝ} (hC : ∀ ω, ‖X ω‖ ≤ C) :
    sIntegral T hBmeas φ hB (fun k ω ↦ if k ∈ Set.Ioc i j then X ω else 0)
      =ᵐ[μ] X * (integrator T hBmeas φ hB j - integrator T hBmeas φ hB i) := by
  have hv := isPredictableVersion_band (T := T) (φ := φ) hij hXm hC
  simp only [sIntegral, integrandLp_eq hv]
  by_cases hiT : i ≤ T
  · have hcut : ⇑(hv.2.1.toLp _) =ᵐ[bracketMeasure (μ := μ) T hBmeas φ]
        elemIntegrand i (min j T) X := by
      filter_upwards [MemLp.coeFn_toLp hv.2.1, ae_fst_mem_Ioc_bracketMeasure (T := T) (φ := φ)]
        with z hz hzT
      rw [hz, uncurry_band]
      simp only [elemIntegrand, Set.indicator_apply, Set.mem_Ioc, le_min_iff, hzT.2, and_true]
    filter_upwards [itoIntegralAgainst_elementary (hB := hB) T hBmeas φ (le_min hij hiT)
      (min_le_right _ _) X hXm C hC (hv.2.1.toLp _) hcut] with ω hω
    simp only [hω, integrator, Pi.mul_apply, Pi.sub_apply, min_eq_left hiT]
  · rw [not_le] at hiT
    have hzero : hv.2.1.toLp _ = 0 := by
      refine Lp.ext ?_
      filter_upwards [MemLp.coeFn_toLp hv.2.1, ae_fst_mem_Ioc_bracketMeasure (T := T) (φ := φ),
        Lp.coeFn_zero ℝ 2 (bracketMeasure (μ := μ) T hBmeas φ)] with z hz hzT h0
      rw [hz, h0, uncurry_band]
      simp only [elemIntegrand, Set.indicator_apply, Set.mem_Ioc, Pi.zero_apply]
      rw [if_neg fun h ↦ absurd (hiT.trans h.1) (not_lt.2 hzT.2), zero_mul]
    rw [hzero, map_zero]
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with ω hω
    simp [integrator, min_eq_right hiT.le, min_eq_right (hiT.le.trans hij)]

omit mΩ in
/-- The initial band `1_{[0,i]}(t)·X(ω)` is the elementary integrand on `(0, i]` away from the time
origin. -/
theorem uncurry_bottomBand_of_ne_zero (i : ℝ≥0) (X : Ω → ℝ) {z : ℝ≥0 × Ω} (hz : z.1 ≠ 0) :
    Function.uncurry (fun k ω ↦ if k ∈ Set.Iic i then X ω else 0) z = elemIntegrand 0 i X z := by
  simp only [Function.uncurry, elemIntegrand, Set.indicator_apply, Set.mem_Iic, Set.mem_Ioc,
    pos_iff_ne_zero.2 hz, true_and]
  split_ifs <;> simp

/-- The initial band, with an `𝓕_0`-measurable coefficient, is predictable. Unlike the later bands
it charges the time origin, through `{0} × Ω`. -/
theorem measurable_bottomBand (i : ℝ≥0) {X : Ω → ℝ}
    (hXm : Measurable[natFiltration hBmeas ⊥] X) :
    Measurable[(natFiltration (mΩ := mΩ) hBmeas).predictable]
      (Function.uncurry (fun k ω ↦ if k ∈ Set.Iic i then X ω else 0)) := by
  have hX : Measurable[(natFiltration (mΩ := mΩ) hBmeas).predictable] fun z : ℝ≥0 × Ω ↦ X z.2 :=
    fun S hS ↦ by
      have h := measurableSet_predictable_univ_prod (𝓕 := natFiltration hBmeas) (hXm hS)
      rw [Set.univ_prod] at h
      exact h
  convert hX.indicator
    (measurableSet_predictable_Iic_prod (i := i) (s := Set.univ) MeasurableSet.univ) using 1
  funext z
  by_cases hz : z.1 ≤ i <;> simp [Function.uncurry, hz]

omit [IsProbabilityMeasure μ] in
/-- The initial band with a bounded `𝓕_0`-measurable coefficient is its own predictable
version. -/
theorem isPredictableVersion_bottomBand (i : ℝ≥0) {X : Ω → ℝ}
    (hXm : Measurable[natFiltration hBmeas ⊥] X) {C : ℝ} (hC : ∀ ω, ‖X ω‖ ≤ C) :
    IsPredictableVersion T hBmeas φ (fun k ω ↦ if k ∈ Set.Iic i then X ω else 0)
      (fun k ω ↦ if k ∈ Set.Iic i then X ω else 0) := by
  refine ⟨measurable_bottomBand i hXm, ?_, .rfl⟩
  refine MemLp.of_bound (measurable_bottomBand i hXm).aestronglyMeasurable C
    (Eventually.of_forall fun z ↦ ?_)
  simp only [Function.uncurry]
  split_ifs
  · exact hC _
  · simpa using (norm_nonneg (X z.2)).trans (hC z.2)

/-- **The initial band identity**: the integral of `1_{[0,i]}·X` against `M` is
`X·(M_{i∧T} − M_0)`. The time origin is `⟨M⟩`-null, so the initial band has the class of the band
on `(0, i]`, and the band identity applies. -/
theorem sIntegral_bottomBand (hB : IsPreBrownianReal B μ) (i : ℝ≥0) {X : Ω → ℝ}
    (hXm : Measurable[natFiltration hBmeas ⊥] X) {C : ℝ} (hC : ∀ ω, ‖X ω‖ ≤ C) :
    sIntegral T hBmeas φ hB (fun k ω ↦ if k ∈ Set.Iic i then X ω else 0)
      =ᵐ[μ] X * (integrator T hBmeas φ hB i - integrator T hBmeas φ hB ⊥) := by
  have hv := isPredictableVersion_bottomBand (T := T) (φ := φ) i hXm hC
  have hv' := isPredictableVersion_band (T := T) (φ := φ) (zero_le : (0 : ℝ≥0) ≤ i) hXm hC
  have hclass : hv.2.1.toLp _ = hv'.2.1.toLp _ := by
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [ae_fst_mem_Ioc_bracketMeasure (T := T) (φ := φ)] with z hz
    rw [uncurry_band, uncurry_bottomBand_of_ne_zero i X hz.1.ne']
  have hband := sIntegral_band (T := T) (φ := φ) hB (zero_le : (0 : ℝ≥0) ≤ i) hXm hC
  simp only [sIntegral, integrandLp_eq hv, integrandLp_eq hv'] at hband ⊢
  rw [hclass]
  exact hband

/-! ### Versions are closed under the operations the characterisation asks for -/

omit [IsProbabilityMeasure μ] in
theorem IsPredictableVersion.add {X₁ X₂ X₁' X₂' : ℝ≥0 → Ω → ℝ}
    (h₁ : IsPredictableVersion T hBmeas φ X₁ X₁') (h₂ : IsPredictableVersion T hBmeas φ X₂ X₂') :
    IsPredictableVersion T hBmeas φ (X₁ + X₂) (X₁' + X₂') :=
  ⟨h₁.1.add h₂.1, h₁.2.1.add h₂.2.1, h₁.2.2.add h₂.2.2⟩

omit [IsProbabilityMeasure μ] in
theorem IsPredictableVersion.const_smul {X X' : ℝ≥0 → Ω → ℝ}
    (h : IsPredictableVersion T hBmeas φ X X') (c : ℝ) :
    IsPredictableVersion T hBmeas φ (c • X) (c • X') :=
  ⟨h.1.const_smul c, h.2.1.const_smul c, h.2.2.const_smul⟩

omit [IsProbabilityMeasure μ] in
theorem IsPredictableVersion.of_indistinguishable {X Y X' : ℝ≥0 → Ω → ℝ}
    (h : IsPredictableVersion T hBmeas φ X X') (hXY : X ≡ᵐ[μ] Y) :
    IsPredictableVersion T hBmeas φ Y X' :=
  ⟨h.1, h.2.1, hXY.symm.trans h.2.2⟩

theorem integrandLp_add {X₁ X₂ X₁' X₂' : ℝ≥0 → Ω → ℝ}
    (h₁ : IsPredictableVersion T hBmeas φ X₁ X₁') (h₂ : IsPredictableVersion T hBmeas φ X₂ X₂') :
    integrandLp T hBmeas φ (X₁ + X₂) = integrandLp T hBmeas φ X₁ + integrandLp T hBmeas φ X₂ := by
  rw [integrandLp_eq (h₁.add h₂), integrandLp_eq h₁, integrandLp_eq h₂]
  exact MemLp.toLp_add _ _

theorem integrandLp_const_smul {X X' : ℝ≥0 → Ω → ℝ} (h : IsPredictableVersion T hBmeas φ X X')
    (c : ℝ) : integrandLp T hBmeas φ (c • X) = c • integrandLp T hBmeas φ X := by
  rw [integrandLp_eq (h.const_smul c), integrandLp_eq h]
  exact MemLp.toLp_const_smul c _

/-! ### Dominated convergence -/

/-- **Dominated convergence for the integral against `M`.** A sequence in the domain, converging
at every time and outcome and dominated by one process of the domain, has its limit in the domain,
and the integrals converge in measure. -/
theorem sIntegral_dct (hB : IsPreBrownianReal B μ) (X : ℕ → ℝ≥0 → Ω → ℝ)
    (X_dom X_lim : ℝ≥0 → Ω → ℝ) (h₁ : ∀ n, X n ∈ domain T hBmeas φ)
    (h₂ : X_dom ∈ domain T hBmeas φ) (h_dom : ∀ n i ω, |X n i ω| ≤ |X_dom i ω|)
    (h_lim : ∀ i ω, Tendsto (X · i ω) atTop (𝓝 (X_lim i ω))) :
    X_lim ∈ domain T hBmeas φ ∧
      TendstoInMeasure μ (fun n ↦ sIntegral T hBmeas φ hB (X n)) atTop
        (sIntegral T hBmeas φ hB X_lim) := by
  have h₁' : ∀ n, ∃ V, IsPredictableVersion T hBmeas φ (X n) V := h₁
  choose V hV using h₁'
  obtain ⟨Vd, hVd⟩ := h₂
  set pred := (natFiltration (mΩ := mΩ) hBmeas).predictable
  -- the limit version, pathwise
  set Vl : ℝ≥0 → Ω → ℝ := fun t ω ↦ limUnder atTop (fun n ↦ V n t ω)
  have hall : ∀ᵐ ω ∂μ, (∀ n t, V n t ω = X n t ω) ∧ ∀ t, Vd t ω = X_dom t ω := by
    filter_upwards [ae_all_iff.2 fun n ↦ (hV n).2.2, hVd.2.2] with ω hn hd
    exact ⟨fun n t ↦ (hn n t).symm, fun t ↦ (hd t).symm⟩
  have htend : ∀ᵐ ω ∂μ, ∀ t, Tendsto (fun n ↦ V n t ω) atTop (𝓝 (X_lim t ω)) := by
    filter_upwards [hall] with ω hω t
    simpa only [hω.1 _ t] using h_lim t ω
  have hVl_eq : ∀ᵐ ω ∂μ, ∀ t, Vl t ω = X_lim t ω := by
    filter_upwards [htend] with ω hω t
    exact (hω t).limUnder_eq
  have hVm (n : ℕ) : StronglyMeasurable[pred] (Function.uncurry (V n)) :=
    (hV n).1.stronglyMeasurable
  have hVl_meas : Measurable[pred] (Function.uncurry Vl) :=
    (StronglyMeasurable.limUnder (l := atTop) hVm).measurable
  -- domination and convergence, `⟨M⟩`-almost everywhere
  have hdom (n : ℕ) : ∀ᵐ z ∂(bracketMeasure (μ := μ) T hBmeas φ),
      ‖Function.uncurry (V n) z‖ ≤ ‖Function.uncurry Vd z‖ := by
    refine ae_bracketMeasure_of_ae_forall T hBmeas φ
      (measurableSet_le (hV n).1.norm hVd.1.norm) ?_
    filter_upwards [hall] with ω hω t
    simpa only [Function.uncurry_apply_pair, Real.norm_eq_abs, hω.1 n t, hω.2 t] using h_dom n t ω
  have hconv : ∀ᵐ z ∂(bracketMeasure (μ := μ) T hBmeas φ),
      Tendsto (fun n ↦ Function.uncurry (V n) z) atTop (𝓝 (Function.uncurry Vl z)) := by
    have hex : ∀ᵐ z ∂(bracketMeasure (μ := μ) T hBmeas φ),
        ∃ c, Tendsto (fun n ↦ Function.uncurry (V n) z) atTop (𝓝 c) := by
      refine ae_bracketMeasure_of_ae_forall T hBmeas φ
        (StronglyMeasurable.measurableSet_exists_tendsto hVm) ?_
      filter_upwards [htend] with ω hω t
      exact ⟨_, hω t⟩
    filter_upwards [hex] with z hz
    exact tendsto_nhds_limUnder hz
  have hdom_lim : ∀ᵐ z ∂(bracketMeasure (μ := μ) T hBmeas φ),
      ‖Function.uncurry Vl z‖ ≤ ‖Function.uncurry Vd z‖ := by
    filter_upwards [hconv, ae_all_iff.2 hdom] with z hz hzd
    exact le_of_tendsto' hz.norm hzd
  have hVl : IsPredictableVersion T hBmeas φ X_lim Vl :=
    ⟨hVl_meas, hVd.2.1.of_le hVl_meas.stronglyMeasurable.aestronglyMeasurable hdom_lim,
      hVl_eq.mono fun ω h t ↦ (h t).symm⟩
  refine ⟨⟨Vl, hVl⟩, ?_⟩
  -- convergence in `L²(⟨M⟩)`, then through the isometry, then in measure
  have hLp : Tendsto (fun n ↦ integrandLp T hBmeas φ (X n)) atTop
      (𝓝 (integrandLp T hBmeas φ X_lim)) := by
    have hseq : (fun n ↦ integrandLp T hBmeas φ (X n)) = fun n ↦ (hV n).2.1.toLp _ :=
      funext fun n ↦ integrandLp_eq (hV n)
    rw [hseq, integrandLp_eq hVl]
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun n ↦ (hV n).2.1) _ hVl.2.1).2
      (tendsto_eLpNorm_sub_of_dominated_convergence ENNReal.ofNat_ne_top _
        (fun n ↦ (hVm n).aestronglyMeasurable) hVd.2.1.norm hdom hconv)
  exact tendstoInMeasure_of_tendsto_Lp
    (((itoIntegralAgainstCLM hB T hBmeas φ).continuous.tendsto _).comp hLp)

/-! ### The integral against `M` extends the Riemann–Stieltjes integral -/

/-- **The integral against `M` is an extension of the Riemann–Stieltjes integral**, in the sense of
BrownianMotion's `IsRiemannStieltjesExtension`: on elementary processes it is the Riemann–Stieltjes sum
against `M` stopped at `T`, and it respects linearity, indistinguishability and dominated
convergence. -/
theorem isRiemannStieltjesExtension (hB : IsPreBrownianReal B μ) :
    IsRiemannStieltjesExtension μ (integrator T hBmeas φ hB) (natFiltration hBmeas)
      (sIntegral T hBmeas φ hB) (domain T hBmeas φ) where
  measurable _ _ := Lp.aestronglyMeasurable _
  elementary_ioc i j hij X := by
    -- a simple function over `𝓕_i` is bounded and `𝓕_i`-measurable
    obtain ⟨⟨C, hC⟩, hXm⟩ : (∃ C, ∀ ω, ‖X ω‖ ≤ C) ∧ Measurable[natFiltration hBmeas i] X := by
      letI : MeasurableSpace Ω := natFiltration hBmeas i
      exact ⟨X.exists_forall_norm_le, X.measurable⟩
    exact ⟨⟨_, isPredictableVersion_band hij hXm hC⟩, sIntegral_band hB hij hXm hC⟩
  elementary_iic i X := by
    obtain ⟨⟨C, hC⟩, hXm⟩ : (∃ C, ∀ ω, ‖X ω‖ ≤ C) ∧ Measurable[natFiltration hBmeas ⊥] X := by
      letI : MeasurableSpace Ω := natFiltration hBmeas ⊥
      exact ⟨X.exists_forall_norm_le, X.measurable⟩
    exact ⟨⟨_, isPredictableVersion_bottomBand i hXm hC⟩, sIntegral_bottomBand hB i hXm hC⟩
  integral_add X₁ X₂ h₁ h₂ := by
    obtain ⟨V₁, hV₁⟩ := h₁
    obtain ⟨V₂, hV₂⟩ := h₂
    refine ⟨⟨_, hV₁.add hV₂⟩, ?_⟩
    simp only [sIntegral]
    rw [integrandLp_add hV₁ hV₂, map_add]
    exact Lp.coeFn_add _ _
  integral_smul X c h := by
    obtain ⟨V, hV⟩ := h
    refine ⟨⟨_, hV.const_smul c⟩, ?_⟩
    simp only [sIntegral]
    rw [integrandLp_const_smul hV, map_smul]
    exact Lp.coeFn_smul _ _
  integral_indistinguishable X₁ X₂ h₁ h₂ := by
    obtain ⟨V, hV⟩ := h₁
    refine ⟨⟨V, hV.of_indistinguishable h₂⟩, ?_⟩
    simp only [sIntegral]
    rw [integrandLp_eq hV, integrandLp_eq (hV.of_indistinguishable h₂)]
  integral_dct := sIntegral_dct hB

/-! ### Uniqueness: every extension agrees with this one on the common domain

The uniqueness clause of `IsStochasticIntegral` ranges over *every* Riemann–Stieltjes extension
`I'` with domain `S'`. Such an `I'` is not assumed `L²`-continuous, nor even defined on
`L²(⟨M⟩)`, so the density argument behind `itoIntegralAgainst_unique` does not reach it; what
`I'` does have is dominated convergence. The proof is therefore a monotone-class argument, and
nothing in it uses `M`: it needs only that both integrals are Riemann–Stieltjes extensions for
the same integrator and filtration. The class `Agree` of processes on which the two integrals
agree contains the elementary processes and is closed under sums, scalings and dominated limits.
A Dynkin argument over the predictable rectangles puts every predictable indicator cut at a time
`K` into it. The cut is needed because the constant process `1` need not lie in `S'`, while the
elementary `𝟙_{[0,K]}` does and dominates every process bounded by one and switched off after
`K`. Simple functions follow by linearity, bounded predictable processes by bounded pointwise
approximation, and then everything in the common domain by truncation, a process serving as its
own dominating function. -/

section Uniqueness

variable (hB : IsPreBrownianReal B μ) (I' : (ℝ≥0 → Ω → ℝ) → Ω → ℝ) (S' : Set (ℝ≥0 → Ω → ℝ))

variable (T hBmeas φ) in
/-- The processes in both domains on which the integral against `M` and `I'` agree. -/
def Agree (Z : ℝ≥0 → Ω → ℝ) : Prop :=
  Z ∈ domain T hBmeas φ ∧ Z ∈ S' ∧ sIntegral T hBmeas φ hB Z =ᵐ[μ] I' Z

variable {hB I' S'}

/-- The other extension, as a hypothesis. -/
abbrev IsOtherExtension (hB : IsPreBrownianReal B μ) (I' : (ℝ≥0 → Ω → ℝ) → Ω → ℝ)
    (S' : Set (ℝ≥0 → Ω → ℝ)) : Prop :=
  IsRiemannStieltjesExtension μ (integrator T hBmeas φ hB) (natFiltration hBmeas) I' S'

theorem Agree.add (hI' : IsOtherExtension (T := T) (φ := φ) hB I' S') {Z₁ Z₂ : ℝ≥0 → Ω → ℝ}
    (h₁ : Agree T hBmeas φ hB I' S' Z₁) (h₂ : Agree T hBmeas φ hB I' S' Z₂) :
    Agree T hBmeas φ hB I' S' (Z₁ + Z₂) := by
  obtain ⟨hS, hI⟩ := (isRiemannStieltjesExtension (T := T) (φ := φ) hB).integral_add Z₁ Z₂
    h₁.1 h₂.1
  obtain ⟨hS', hI''⟩ := hI'.integral_add Z₁ Z₂ h₁.2.1 h₂.2.1
  exact ⟨hS, hS', hI.trans ((h₁.2.2.add h₂.2.2).trans hI''.symm)⟩

theorem Agree.const_smul (hI' : IsOtherExtension (T := T) (φ := φ) hB I' S')
    {Z : ℝ≥0 → Ω → ℝ} (h : Agree T hBmeas φ hB I' S' Z) (c : ℝ) :
    Agree T hBmeas φ hB I' S' (c • Z) := by
  obtain ⟨hS, hI⟩ := (isRiemannStieltjesExtension (T := T) (φ := φ) hB).integral_smul Z c h.1
  obtain ⟨hS', hI''⟩ := hI'.integral_smul Z c h.2.1
  exact ⟨hS, hS', hI.trans ((h.2.2.const_smul c).trans hI''.symm)⟩

theorem Agree.sub (hI' : IsOtherExtension (T := T) (φ := φ) hB I' S') {Z₁ Z₂ : ℝ≥0 → Ω → ℝ}
    (h₁ : Agree T hBmeas φ hB I' S' Z₁) (h₂ : Agree T hBmeas φ hB I' S' Z₂) :
    Agree T hBmeas φ hB I' S' (Z₁ - Z₂) := by
  simpa [sub_eq_add_neg] using h₁.add hI' (h₂.const_smul hI' (-1))

/-- **`Agree` is closed under dominated limits**: both integrals pass to the limit in measure,
and limits in measure are almost surely unique. -/
theorem Agree.of_tendsto (hI' : IsOtherExtension (T := T) (φ := φ) hB I' S')
    {Z : ℕ → ℝ≥0 → Ω → ℝ} {Zd Zl : ℝ≥0 → Ω → ℝ} (hZ : ∀ n, Agree T hBmeas φ hB I' S' (Z n))
    (hZd : Zd ∈ domain T hBmeas φ ∧ Zd ∈ S') (hdom : ∀ n t ω, |Z n t ω| ≤ |Zd t ω|)
    (hlim : ∀ t ω, Tendsto (Z · t ω) atTop (𝓝 (Zl t ω))) : Agree T hBmeas φ hB I' S' Zl := by
  obtain ⟨hS, hconv⟩ := (isRiemannStieltjesExtension (T := T) (φ := φ) hB).integral_dct Z Zd Zl
    (fun n ↦ (hZ n).1) hZd.1 hdom hlim
  obtain ⟨hS', hconv'⟩ := hI'.integral_dct Z Zd Zl (fun n ↦ (hZ n).2.1) hZd.2 hdom hlim
  exact ⟨hS, hS', tendstoInMeasure_ae_unique hconv
    (hconv'.congr_left fun n ↦ ((hZ n).2.2).symm)⟩

theorem agree_band (hI' : IsOtherExtension (T := T) (φ := φ) hB I' S') {i j : ℝ≥0} (hij : i ≤ j)
    (X : @SimpleFunc Ω (natFiltration hBmeas i) ℝ) :
    Agree T hBmeas φ hB I' S' (fun k ω ↦ if k ∈ Set.Ioc i j then X ω else 0) := by
  obtain ⟨hS, hI⟩ := (isRiemannStieltjesExtension (T := T) (φ := φ) hB).elementary_ioc i j hij X
  obtain ⟨hS', hI''⟩ := hI'.elementary_ioc i j hij X
  exact ⟨hS, hS', hI.trans hI''.symm⟩

theorem agree_bottomBand (hI' : IsOtherExtension (T := T) (φ := φ) hB I' S') (i : ℝ≥0)
    (X : @SimpleFunc Ω (natFiltration hBmeas ⊥) ℝ) :
    Agree T hBmeas φ hB I' S' (fun k ω ↦ if k ∈ Set.Iic i then X ω else 0) := by
  obtain ⟨hS, hI⟩ := (isRiemannStieltjesExtension (T := T) (φ := φ) hB).elementary_iic i X
  obtain ⟨hS', hI''⟩ := hI'.elementary_iic i X
  exact ⟨hS, hS', hI.trans hI''.symm⟩

/-! #### Predictable indicators, cut at a time -/

omit mΩ in
/-- A function of `(t, ω)` switched off after time `K`, as a process. -/
noncomputable def cut (Z : ℝ≥0 × Ω → ℝ) (K : ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ (Set.Iic K ×ˢ (Set.univ : Set Ω)).indicator Z (t, ω)

omit mΩ in
theorem cut_add (Z₁ Z₂ : ℝ≥0 × Ω → ℝ) (K : ℝ≥0) : cut (Z₁ + Z₂) K = cut Z₁ K + cut Z₂ K := by
  funext t ω
  simp only [cut, Pi.add_apply]
  rw [Set.indicator_add']
  rfl

theorem agree_cut_univ (hI' : IsOtherExtension (T := T) (φ := φ) hB I' S') (K : ℝ≥0) :
    Agree T hBmeas φ hB I' S' (cut 1 K) := by
  convert agree_bottomBand hI' K (@SimpleFunc.const Ω ℝ (natFiltration hBmeas ⊥) 1) using 1
  funext t ω
  by_cases h : t ≤ K <;> simp [cut, h]

theorem agree_zero (hI' : IsOtherExtension (T := T) (φ := φ) hB I' S') :
    Agree T hBmeas φ hB I' S' 0 := by
  simpa using (agree_cut_univ hI' 0).const_smul hI' 0

/-- **Predictable indicators**: for every predictable `A`, the integrals agree on `𝟙_A` cut at `K`.
A Dynkin argument over the predictable rectangles, on which agreement is the elementary
identity. -/
theorem agree_cut_indicator (hI' : IsOtherExtension (T := T) (φ := φ) hB I' S') (K : ℝ≥0) :
    ∀ A, MeasurableSet[(natFiltration (mΩ := mΩ) hBmeas).predictable] A →
      Agree T hBmeas φ hB I' S' (cut (A.indicator 1) K) := by
  classical
  refine MeasurableSpace.induction_on_inter (m := (natFiltration (mΩ := mΩ) hBmeas).predictable)
    (C := fun A _ ↦ Agree T hBmeas φ hB I' S' (cut (A.indicator 1) K))
    (generateFrom_predictableRect hBmeas).symm (isPiSystem_predictableRect hBmeas) ?_ ?_ ?_ ?_
  · convert agree_zero hI' using 1
    funext t ω
    simp [cut]
  · intro A hA
    rcases hA with ⟨F₀, hF₀, rfl⟩ | ⟨a, b, hab, F, hF, rfl⟩
    · -- the bottom rectangle `{0} × F₀` is the initial band at time `0`
      convert agree_bottomBand hI' ⊥ (@SimpleFunc.piecewise Ω ℝ (natFiltration hBmeas ⊥) F₀ hF₀
        (@SimpleFunc.const Ω ℝ (natFiltration hBmeas ⊥) 1)
        (@SimpleFunc.const Ω ℝ (natFiltration hBmeas ⊥) 0)) using 1
      funext t ω
      by_cases ht : t = 0 <;> by_cases hω : ω ∈ F₀ <;>
        simp [cut, Set.indicator_apply, ht, hω]
    · -- a rectangle `(a, b] × F`, cut at `K`, is a band, or nothing if it starts after `K`
      by_cases haK : a ≤ K
      · convert agree_band hI' (le_min hab.le haK)
          (@SimpleFunc.piecewise Ω ℝ (natFiltration hBmeas a) F hF
            (@SimpleFunc.const Ω ℝ (natFiltration hBmeas a) 1)
            (@SimpleFunc.const Ω ℝ (natFiltration hBmeas a) 0)) using 1
        funext t ω
        by_cases h1 : t ≤ K <;> by_cases h2 : a < t <;> by_cases h3 : t ≤ b <;>
          by_cases hω : ω ∈ F <;> simp [cut, h1, h2, h3, hω]
      · convert agree_zero hI' using 1
        funext t ω
        simp only [cut, Pi.zero_apply]
        rw [Set.indicator_apply]
        split_ifs with h1
        · exact Set.indicator_of_notMem (fun h ↦ haK (h.1.1.le.trans h1.1)) _
        · rfl
  · intro A _ hA
    convert (agree_cut_univ hI' K).sub hI' hA using 1
    funext t ω
    by_cases h : (t, ω) ∈ A <;> simp [cut, Set.indicator_apply, h]
  · intro f hdisj _ hf
    -- the partial unions agree, by additivity
    have hpart (N : ℕ) :
        Agree T hBmeas φ hB I' S' (cut ((⋃ n ∈ Finset.range N, f n).indicator 1) K) := by
      induction N with
      | zero =>
        convert agree_zero hI' using 1
        funext t ω
        simp [cut]
      | succ N ih =>
        have hdj : Disjoint (⋃ n ∈ Finset.range N, f n) (f N) :=
          Set.disjoint_iUnion₂_left.2 fun n hn ↦ hdisj (Finset.mem_range.1 hn).ne
        rw [Finset.range_add_one, Finset.set_biUnion_insert, Set.union_comm,
          Set.indicator_union_of_disjoint hdj]
        have hsum := ih.add hI' (hf N)
        rwa [← cut_add] at hsum
    refine Agree.of_tendsto hI' hpart ⟨(agree_cut_univ hI' K).1, (agree_cut_univ hI' K).2.1⟩
      (fun N t ω ↦ ?_) (fun t ω ↦ ?_)
    · simp only [cut, Set.indicator_apply, Pi.one_apply]
      split_ifs <;> simp
    · by_cases hz : (t, ω) ∈ ⋃ n, f n
      · obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hz
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_gt_atTop m] with N hN
        have hmem : (t, ω) ∈ ⋃ n ∈ Finset.range N, f n :=
          Set.mem_biUnion (Finset.mem_range.2 hN) hm
        simp only [cut, Set.indicator_apply, hz, hmem, if_true, Pi.one_apply]
      · refine tendsto_const_nhds.congr' (Eventually.of_forall fun N ↦ ?_)
        have hmem : (t, ω) ∉ ⋃ n ∈ Finset.range N, f n := fun h ↦
          hz (Set.mem_iUnion.2 (by obtain ⟨n, -, hn⟩ := Set.mem_iUnion₂.1 h; exact ⟨n, hn⟩))
        simp only [cut, Set.indicator_apply, hz, hmem, if_false]

/-- **Simple predictable functions**, cut at `K`, by linearity. -/
theorem agree_cut_simpleFunc (hI' : IsOtherExtension (T := T) (φ := φ) hB I' S') (K : ℝ≥0)
    (f : @SimpleFunc (ℝ≥0 × Ω) (natFiltration (mΩ := mΩ) hBmeas).predictable ℝ) :
    Agree T hBmeas φ hB I' S' (cut f K) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := (natFiltration (mΩ := mΩ) hBmeas).predictable
  induction f using SimpleFunc.induction with
  | @const c A hA =>
    convert (agree_cut_indicator hI' K A hA).const_smul hI' c using 1
    funext t ω
    by_cases h : (t, ω) ∈ A <;> simp [cut, Set.indicator_apply, h]
  | @add f g _ hf hg =>
    rw [SimpleFunc.coe_add, cut_add]
    exact hf.add hI' hg

/-- **Bounded predictable processes**, cut at `K`: a bounded approximation by simple functions,
dominated by the constant. -/
theorem agree_cut_bounded (hI' : IsOtherExtension (T := T) (φ := φ) hB I' S') (K : ℝ≥0)
    {Z : ℝ≥0 × Ω → ℝ} (hZ : Measurable[(natFiltration (mΩ := mΩ) hBmeas).predictable] Z)
    {C : ℝ} (hC : 0 ≤ C) (hZC : ∀ z, ‖Z z‖ ≤ C) : Agree T hBmeas φ hB I' S' (cut Z K) := by
  have hsm := hZ.stronglyMeasurable
  have hdom := (agree_cut_univ hI' K).const_smul hI' C
  refine Agree.of_tendsto hI' (Z := fun n ↦ cut (hsm.approxBounded C n) K) (Zd := C • cut 1 K)
    (fun n ↦ agree_cut_simpleFunc hI' K _) ⟨hdom.1, hdom.2.1⟩ (fun n t ω ↦ ?_) (fun t ω ↦ ?_)
  · simp only [cut, Pi.smul_apply, smul_eq_mul, Set.indicator_apply, Pi.one_apply]
    split_ifs
    · rw [mul_one, abs_of_nonneg hC, ← Real.norm_eq_abs]
      exact StronglyMeasurable.norm_approxBounded_le hsm hC n _
    · simp
  · simp only [cut, Set.indicator_apply]
    split_ifs
    · exact StronglyMeasurable.tendsto_approxBounded_of_norm_le hsm (hZC _)
    · exact tendsto_const_nhds

/-- **Uniqueness, in full.** Every Riemann–Stieltjes extension agrees with the integral against
`M` on their common domain. Truncating a predictable version at height and time `n` gives bounded
processes on which they agree; the version itself dominates the truncations, so both integrals
pass to the limit. -/
theorem sIntegral_ae_eq_of_isRiemannStieltjesExtension
    (hI' : IsOtherExtension (T := T) (φ := φ) hB I' S') {X : ℝ≥0 → Ω → ℝ}
    (hX : X ∈ domain T hBmeas φ) (hX' : X ∈ S') : sIntegral T hBmeas φ hB X =ᵐ[μ] I' X := by
  obtain ⟨V, hV⟩ := hX
  have hVV : IsPredictableVersion T hBmeas φ V V := ⟨hV.1, hV.2.1, .rfl⟩
  obtain ⟨hVS', hI'V⟩ := hI'.integral_indistinguishable X V hX' hV.2.2
  -- truncate the version at height and time `n`
  set W : ℕ → ℝ≥0 → Ω → ℝ := fun n ↦
    cut ({z | |Function.uncurry V z| ≤ n}.indicator (Function.uncurry V)) n
  have hWagree (n : ℕ) : Agree T hBmeas φ hB I' S' (W n) := by
    have hm : Measurable[(natFiltration (mΩ := mΩ) hBmeas).predictable]
        ({z | |Function.uncurry V z| ≤ n}.indicator (Function.uncurry V)) := by
      letI : MeasurableSpace (ℝ≥0 × Ω) := (natFiltration (mΩ := mΩ) hBmeas).predictable
      exact hV.1.indicator (measurableSet_le hV.1.abs measurable_const)
    refine agree_cut_bounded hI' n hm (Nat.cast_nonneg n) fun z ↦ ?_
    by_cases h : |Function.uncurry V z| ≤ n
    · simpa [Set.indicator_of_mem (s := {z | |Function.uncurry V z| ≤ n}) h] using h
    · simp [Set.indicator_of_notMem (s := {z | |Function.uncurry V z| ≤ n}) h]
  have hVagree : Agree T hBmeas φ hB I' S' V := by
    refine Agree.of_tendsto hI' hWagree ⟨⟨V, hVV⟩, hVS'⟩
      (fun n t ω ↦ by
        simp only [W, cut, ← Real.norm_eq_abs]
        exact (norm_indicator_le_norm_self _ _).trans (norm_indicator_le_norm_self _ _))
      (fun t ω ↦ tendsto_const_nhds.congr' ?_)
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ≥0)).eventually_ge_atTop t,
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop |V t ω|] with n htn hVn
    simp only [W, cut, Set.indicator_of_mem
      (show (t, ω) ∈ Set.Iic (n : ℝ≥0) ×ˢ (Set.univ : Set Ω) from ⟨htn, Set.mem_univ _⟩)]
    rw [Set.indicator_of_mem (s := {z | |Function.uncurry V z| ≤ (n : ℝ)}) hVn]
    rfl
  have hXV : sIntegral T hBmeas φ hB X = sIntegral T hBmeas φ hB V := by
    simp only [sIntegral, integrandLp_eq hV, integrandLp_eq hVV]
  rw [hXV]
  exact hVagree.2.2.trans hI'V.symm

end Uniqueness

/-! ### The characterisation -/

/-- **The integral against `M = φ●B` is a stochastic integral in BrownianMotion's sense.**

`IsStochasticIntegral` asks for an extension of the Riemann–Stieltjes integral (elementary values,
linearity, indistinguishability, dominated convergence) that agrees with every other such
extension on their common domain. The integrator is `M` stopped at `T`, the filtration is the
natural Brownian filtration, and the domain is the processes indistinguishable from a predictable
process square-integrable against the bracket. -/
theorem isStochasticIntegral (hB : IsPreBrownianReal B μ) :
    IsStochasticIntegral μ (integrator T hBmeas φ hB) (natFiltration hBmeas)
      (sIntegral T hBmeas φ hB) (domain T hBmeas φ) where
  toIsRiemannStieltjesExtension := isRiemannStieltjesExtension hB
  consistent _ _ h _ hX := sIntegral_ae_eq_of_isRiemannStieltjesExtension h hX.1 hX.2


end StochasticIntegralCharacterisation

end MathFin
