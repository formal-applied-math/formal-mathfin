/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralBrownian

/-!
# `𝓕_a`-linearity of the Itô integral

The Itô integral is linear over the reals by construction — it is a CLM. It is
in fact linear over something much larger: over the **`𝓕_a`-measurable random
scalars**, provided the integrand lives on `(a, T]`. Concretely,

  `∫₀ᵀ Z·φ dB = Z·∫₀ᵀ φ dB`   whenever `Z` is `𝓕_a`-measurable and `φ = 0` on `[0,a]`.

This is the *locality* of the stochastic integral: what the integral does after
time `a` may be scaled by anything the past has already decided, and the scaling
commutes with the integration. It is the structural fact behind every "freeze
the past, integrate the future" argument — the multiplicative decomposition of a
Doléans exponential over a partition, the Markov/tower manipulations of
`∫ₐᵀ`, and the induction that builds a step-integrand Doléans exponential out of
the constant-integrand one. Nothing in the tower had it; it is proved here once,
for a general bounded (and then, by localisation, a general `L²`-compatible)
factor `Z`.

## The proof, and the definitional wrinkle it has to survive

`(t, ω) ↦ Z ω` is **not** a predictable process: predictability at times `t < a`
would force `Z` to be `𝓕_t`-measurable. What *is* predictable is `Z` switched on
after `a`,

  `afterFactor a Z (t, ω) = 𝟙_{a < t}·Z ω`,

because `Ioi a ×ˢ F` with `F ∈ 𝓕_a` is one of the generating predictable
rectangles. So the scaling operator `smulAdaptedCLM` multiplies by `afterFactor`,
which makes it a genuine norm-`≤ |C|` CLM on the *whole* of `L²(trim_T)` (a
`Z`-independent bonus: `Z = 1` gives the restriction-to-`(a,T]` projection
`restrictAfterCLM`), and the identity `Z·φ` for the coefficient is recovered
exactly on the integrands supported after `a` (`coeFn_smulAdapted`).

With that in place the proof is the standard two-step:

* **simple processes** — a `T`-bounded simple process `V` restarted at `a` and
  scaled by `Z` (`afterStepSP`) is again a `T`-bounded simple process: the
  rectangle `(p.1, p.2]` becomes `(a ⊔ p.1, p.2]`, and `Z·V(p)` is still
  measurable at the new left endpoint precisely because `a ≤ a ⊔ p.1`. Its
  elementary integral is `Z` times the unscaled one, term by term.
* **density** — both sides are continuous in `φ`, and the simple embeddings are
  dense (`simpleAssembly_T_denseRange`), so `DenseRange.equalizer` closes it.

The unbounded corollary needs no dominated convergence: apply the bounded result
twice on the `𝓕_a`-set `{|Z| ≤ M}` — once with factor `𝟙` against the integrand
`Z·φ`, once with factor `𝟙·Z` against `φ` — the two scaled integrands coincide,
and `⋃_M {|Z| ≤ M} = Ω` finishes by countable union of a.e. statements.

The reusable abstraction extracted along the way is `mulBddCLM`: multiplication
by a bounded measurable function as a continuous operator on `L²`, for an
arbitrary measure. Both the integrand-side scaling (on `trim_T`) and the
sample-side scaling (on `μ`) are instances of it.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter ItoIntegralCLM ItoIntegralL2
open scoped NNReal ENNReal Topology

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

/-! ### Multiplication by a bounded measurable function on `L²`

The one reusable abstraction of this file. Both scalings we need — by
`afterFactor a Z` on the predictable `L²(trim_T)`, and by `Z` itself on `L²(μ)`
— are instances. -/

section MulBdd

variable {α : Type*} {mα : MeasurableSpace α} {ν : Measure α}

/-- `g·f` is `L²` whenever `f` is and `g` is measurable and bounded. -/
theorem memLp_mul_of_bdd {g : α → ℝ} (hg : Measurable g) {C : ℝ} (hgC : ∀ x, |g x| ≤ C)
    (f : Lp ℝ 2 ν) : MemLp (fun x ↦ g x * f x) 2 ν := by
  refine MemLp.mono ((Lp.memLp f).const_mul C)
    (hg.stronglyMeasurable.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right ((hgC x).trans (le_abs_self C)) (abs_nonneg _)

/-- **Multiplication by a bounded measurable function is a continuous operator on `L²`**,
of operator norm at most `|C|`. Pointwise multiplication descends to `Lp` classes
because the pointwise bound `|g·f| ≤ |C|·|f|` survives the a.e. quotient. -/
noncomputable def mulBddCLM (ν : Measure α) {g : α → ℝ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, |g x| ≤ C) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (memLp_mul_of_bdd hg hgC f).toLp _
      map_add' := fun f₁ f₂ ↦ by
        refine Lp.ext ?_
        filter_upwards [(memLp_mul_of_bdd hg hgC (f₁ + f₂)).coeFn_toLp,
          Lp.coeFn_add ((memLp_mul_of_bdd hg hgC f₁).toLp (fun x ↦ g x * f₁ x))
            ((memLp_mul_of_bdd hg hgC f₂).toLp (fun x ↦ g x * f₂ x)),
          (memLp_mul_of_bdd hg hgC f₁).coeFn_toLp, (memLp_mul_of_bdd hg hgC f₂).coeFn_toLp,
          Lp.coeFn_add f₁ f₂] with x e0 e1 e2 e3 e4
        simp only [e0, e1, e2, e3, e4, Pi.add_apply]
        ring
      map_smul' := fun c f ↦ by
        refine Lp.ext ?_
        filter_upwards [(memLp_mul_of_bdd hg hgC (c • f)).coeFn_toLp,
          Lp.coeFn_smul c ((memLp_mul_of_bdd hg hgC f).toLp (fun x ↦ g x * f x)),
          (memLp_mul_of_bdd hg hgC f).coeFn_toLp, Lp.coeFn_smul c f] with x e0 e1 e2 e3
        simp only [e0, e1, e2, e3, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        ring }
    |C| (fun f ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [(memLp_mul_of_bdd hg hgC f).coeFn_toLp] with x hx
      rw [hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right ((hgC x).trans (le_abs_self C)) (abs_nonneg _))

/-- The characterising a.e. identity for `mulBddCLM`. -/
theorem coeFn_mulBddCLM (ν : Measure α) {g : α → ℝ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, |g x| ≤ C) (f : Lp ℝ 2 ν) :
    ⇑(mulBddCLM ν hg hgC f) =ᵐ[ν] fun x ↦ g x * f x :=
  (memLp_mul_of_bdd hg hgC f).coeFn_toLp

end MulBdd

/-! ### The `𝓕_a`-measurable factor, switched on after `a` -/

/-- A `𝓕_a`-measurable factor `Z`, switched on strictly after time `a`:
`(t, ω) ↦ 𝟙_{a < t}·Z ω`. The switch is not cosmetic — `(t, ω) ↦ Z ω` is not a
predictable process, and this is the smallest correction that makes it one. -/
noncomputable def afterFactor (a : ℝ≥0) (Z : Ω → ℝ) : ℝ≥0 × Ω → ℝ :=
  fun p ↦ if a < p.1 then Z p.2 else 0

omit mΩ in
/-- `afterFactor` inherits a bound on `Z` (the `max … 0` covers the switched-off
region without assuming `Ω` nonempty). -/
lemma abs_afterFactor_le {a : ℝ≥0} {Z : Ω → ℝ} {C : ℝ} (hZb : ∀ ω, |Z ω| ≤ C)
    (p : ℝ≥0 × Ω) : |afterFactor a Z p| ≤ max C 0 := by
  simp only [afterFactor]
  split_ifs with h
  · exact (hZb p.2).trans (le_max_left _ _)
  · simp

/-- **`afterFactor` is predictable.** The two-case preimage computation: on
`{a < t}` the level set is the predictable rectangle `Ioi a ×ˢ Z⁻¹(S)`
(`Z⁻¹(S) ∈ 𝓕_a`, which is exactly what generates the predictable σ-algebra),
and off it the function is constantly `0`. -/
lemma measurable_afterFactor {a : ℝ≥0} (hBmeas : ∀ t, Measurable (B t)) {Z : Ω → ℝ}
    (hZm : Measurable[ItoIntegralL2.natFiltration hBmeas a] Z) :
    Measurable[(ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable] (afterFactor a Z) := by
  set 𝓕 := ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas
  intro S hS
  have hIoi : MeasurableSet[𝓕.predictable] (Set.Ioi a ×ˢ (Z ⁻¹' S)) :=
    MeasureTheory.measurableSet_predictable_Ioi_prod (𝓕 := 𝓕) (hZm hS)
  have hoff : MeasurableSet[𝓕.predictable] ((Set.Ioi a ×ˢ (Set.univ : Set Ω))ᶜ) :=
    (MeasureTheory.measurableSet_predictable_Ioi_prod (𝓕 := 𝓕) (i := a)
      MeasurableSet.univ).compl
  by_cases h0 : (0 : ℝ) ∈ S
  · have hset : afterFactor a Z ⁻¹' S
        = Set.Ioi a ×ˢ (Z ⁻¹' S) ∪ (Set.Ioi a ×ˢ (Set.univ : Set Ω))ᶜ := by
      ext p
      simp only [afterFactor, Set.mem_preimage, Set.mem_union, Set.mem_prod, Set.mem_Ioi,
        Set.mem_compl_iff, Set.mem_univ, and_true]
      by_cases h : a < p.1 <;> simp [h, h0]
    rw [hset]
    exact hIoi.union hoff
  · have hset : afterFactor a Z ⁻¹' S = Set.Ioi a ×ˢ (Z ⁻¹' S) := by
      ext p
      simp only [afterFactor, Set.mem_preimage, Set.mem_prod, Set.mem_Ioi]
      by_cases h : a < p.1 <;> simp [h, h0]
    rw [hset]
    exact hIoi

/-! ### Scaling a predictable `L²` integrand by a bounded `𝓕_a`-measurable factor -/

/-- **The scaling operator** `φ ↦ 𝟙_{a < t}·Z·φ` on the predictable `L²` space,
as a CLM. Total (defined on every `φ`, not just those supported after `a`) and
continuous — both properties are what the density argument consumes. -/
noncomputable def smulAdaptedCLM (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ItoIntegralL2.natFiltration hBmeas a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) →L[ℝ]
      Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) :=
  mulBddCLM (trimMeasure_T (μ := μ) T hBmeas) (measurable_afterFactor hBmeas hZm)
    (abs_afterFactor_le hZb)

omit [IsProbabilityMeasure μ] in
/-- The characterising a.e. identity for `smulAdaptedCLM`. -/
theorem coeFn_smulAdaptedCLM (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ItoIntegralL2.natFiltration hBmeas a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ⇑(smulAdaptedCLM T a hBmeas Z hZm C hZb φ)
      =ᵐ[trimMeasure_T (μ := μ) T hBmeas] fun p ↦ afterFactor a Z p * φ p :=
  coeFn_mulBddCLM _ _ _ φ

/-- Scaling a predictable `L²` integrand by a bounded `𝓕_a`-measurable factor —
which, to stay inside the predictable `L²`, must be `Z` *switched on after `a`*:
the integrand is `afterFactor a Z · φ = 𝟙_{a < t}·Z ω·φ (t,ω)`, not `Z ω·φ (t,ω)`
(the latter is not predictable, and is not a.e. equal to anything that is). The
switch is invisible on the integrands this file is about — those supported on
`(a, T]` — where the coefficient is exactly `Z ω·φ (t,ω)`: see
`coeFn_smulAdapted`. Unconditionally, `coeFn_smulAdapted_afterFactor`. -/
noncomputable def smulAdapted (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ItoIntegralL2.natFiltration hBmeas a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) :=
  smulAdaptedCLM T a hBmeas Z hZm C hZb φ

omit [IsProbabilityMeasure μ] in
/-- `smulAdapted` unfolded: the integrand is `Z` switched on after `a`, times `φ`. -/
theorem coeFn_smulAdapted_afterFactor (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ItoIntegralL2.natFiltration hBmeas a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ⇑(smulAdapted T a hBmeas Z hZm C hZb φ)
      =ᵐ[trimMeasure_T (μ := μ) T hBmeas] fun p ↦ afterFactor a Z p * φ p :=
  coeFn_smulAdaptedCLM T a hBmeas Z hZm C hZb φ

omit [IsProbabilityMeasure μ] in
/-- **The characterising a.e. identity for `smulAdapted`** (the API the density
argument rewrites along; without it `smulAdapted` is opaque). The support
hypothesis `hφ` is exactly what makes the switch invisible: on `[0,a]` the
integrand already vanishes, so `𝟙_{a<t}·Z·φ = Z·φ`. -/
theorem coeFn_smulAdapted (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ItoIntegralL2.natFiltration hBmeas a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (hφ : ∀ᵐ p ∂(trimMeasure_T (μ := μ) T hBmeas), p.1 ≤ a → φ p = 0) :
    ⇑(smulAdapted T a hBmeas Z hZm C hZb φ)
      =ᵐ[trimMeasure_T (μ := μ) T hBmeas] fun p ↦ Z p.2 * φ p := by
  filter_upwards [coeFn_smulAdapted_afterFactor T a hBmeas Z hZm C hZb φ, hφ] with p e1 e2
  rw [e1]
  simp only [afterFactor]
  split_ifs with h
  · rfl
  · rw [e2 (not_lt.mp h), mul_zero, mul_zero]

/-- **Restriction to `(a, T]`** — the `Z = 1` instance of `smulAdaptedCLM`. On `L²`
this is the orthogonal projection onto the integrands supported after `a`. -/
noncomputable def restrictAfterCLM (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) →L[ℝ]
      Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) :=
  smulAdaptedCLM T a hBmeas (fun _ ↦ (1 : ℝ)) measurable_const 1 (fun _ ↦ abs_one.le)

omit [IsProbabilityMeasure μ] in
/-- **On an integrand already supported after `a` the restriction is the identity.** -/
theorem restrictAfterCLM_eq (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (hφ : ∀ᵐ p ∂(trimMeasure_T (μ := μ) T hBmeas), p.1 ≤ a → φ p = 0) :
    restrictAfterCLM T a hBmeas φ = φ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_smulAdaptedCLM T a hBmeas (fun _ ↦ (1 : ℝ)) measurable_const 1
    (fun _ ↦ abs_one.le) φ, hφ] with p e1 e2
  rw [show (restrictAfterCLM T a hBmeas φ : ℝ≥0 × Ω → ℝ) p
      = afterFactor a (fun _ ↦ (1 : ℝ)) p * (φ : ℝ≥0 × Ω → ℝ) p from e1]
  simp only [afterFactor]
  split_ifs with h
  · rw [one_mul]
  · rw [zero_mul, e2 (not_lt.mp h)]

/-! ### Simple processes restarted at `a` -/

/-- The time origin `{0}` is `trim_T`-null, so pointwise identities off it are a.e.
identities. (`trim_T` is the *predictable* trim: the fibre is a bottom rectangle.) -/
lemma ae_fst_ne_zero (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    ∀ᵐ p ∂(trimMeasure_T (μ := μ) T hBmeas), p.1 ≠ 0 := by
  set 𝓕 := ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas
  have hbot : MeasurableSet[𝓕.predictable] (({(⊥ : ℝ≥0)} : Set ℝ≥0) ×ˢ (Set.univ : Set Ω)) :=
    MeasureTheory.measurableSet_predictable_singleton_bot_prod (𝓕 := 𝓕) MeasurableSet.univ
  have htime : timeMeasure_T T ({(⊥ : ℝ≥0)} : Set ℝ≥0) = 0 :=
    nonpos_iff_eq_zero.mp
      ((Measure.restrict_apply_le _ _).trans
        (ItoIntegralL2.timeMeasure_singleton (⊥ : ℝ≥0)).le)
  have hnull : (trimMeasure_T (μ := μ) T hBmeas)
      (({(⊥ : ℝ≥0)} : Set ℝ≥0) ×ˢ (Set.univ : Set Ω)) = 0 := by
    unfold trimMeasure_T
    rw [MeasureTheory.trim_measurableSet_eq _ hbot, Measure.prod_prod, htime, zero_mul]
  have hset : {p : ℝ≥0 × Ω | ¬ p.1 ≠ 0}
      = ({(⊥ : ℝ≥0)} : Set ℝ≥0) ×ˢ (Set.univ : Set Ω) := by
    ext p
    simp
  rw [ae_iff, hset]
  exact hnull

/-- A finite sum of simple processes evaluates pointwise as the sum of the values. -/
private lemma coe_simpleProcess_sum {ι' : Type*} (hBmeas : ∀ t, Measurable (B t))
    (s : Finset ι') (W : ι' → SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas))
    (t : ℝ≥0) (ω : Ω) : ⇑(∑ i ∈ s, W i) t ω = ∑ i ∈ s, ⇑(W i) t ω := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, SimpleProcess.coe_add]
      simp [ih]

/-- A single step evaluates to the indicator of its rectangle. -/
private lemma coe_stepSP {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t)) {a' b : ℝ≥0}
    (hab : a' ≤ b) (hbT : b ≤ T) {ψ : Ω → ℝ}
    (hψm : Measurable[ItoIntegralL2.natFiltration hBmeas a'] ψ) {M : ℝ} (hψM : ∀ ω, |ψ ω| ≤ M)
    (t : ℝ≥0) (ω : Ω) :
    ⇑(ItoIntegralBrownian.stepSP hBmeas hab hbT hψm hψM : TBoundedSP T hBmeas).val t ω
      = (Set.Ioc a' b).indicator (fun _ ↦ ψ ω) t := by
  rw [SimpleProcess.apply_eq]
  have hbot : ({(⊥ : ℝ≥0)} : Set ℝ≥0).indicator
      (fun _ ↦ (ItoIntegralBrownian.stepSP hBmeas hab hbT hψm hψM :
        TBoundedSP T hBmeas).val.valueBot ω) t = 0 := by
    simp [ItoIntegralBrownian.stepSP]
  rw [hbot, zero_add]
  show (Finsupp.single (a', b) ψ).sum
      (fun p v ↦ (Set.Ioc p.1 p.2).indicator (fun _ ↦ v ω) t) = _
  rw [Finsupp.sum_single_index (by simp)]

/-- **`V` restarted at `a`, scaled by `Z`.** Each rectangle `(p.1, p.2]` of `V` is
cut down to `(a ⊔ p.1, p.2]` (empty, and dropped, when that is degenerate) and its
coefficient is multiplied by `Z`. The result is again a `T`-bounded simple process:
the new coefficient `Z·V(p)` is `𝓕_{a ⊔ p.1}`-measurable because `Z` is
`𝓕_a`-measurable and `V(p)` is `𝓕_{p.1}`-measurable — this is the one place where
`a ≤ a ⊔ p.1` earns the support hypothesis its keep. -/
noncomputable def afterStepSP (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ItoIntegralL2.natFiltration hBmeas a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (V : TBoundedSP T hBmeas) : TBoundedSP T hBmeas :=
  ∑ p ∈ V.val.value.support.attach,
    if h : a ⊔ p.val.1 ≤ p.val.2 then
      ItoIntegralBrownian.stepSP hBmeas h (V.property p.val p.property)
        (φ := fun ω ↦ Z ω * V.val.value p.val ω)
        ((hZm.mono ((ItoIntegralL2.natFiltration hBmeas).mono le_sup_left) le_rfl).mul
          ((V.val.measurable_value p.val).mono
            ((ItoIntegralL2.natFiltration hBmeas).mono le_sup_right) le_rfl))
        (M := C * V.val.valueBound)
        (fun ω ↦ by
          rw [abs_mul]
          exact mul_le_mul (hZb ω)
            (by rw [← Real.norm_eq_abs]; exact V.val.value_le_valueBound p.val ω)
            (abs_nonneg _) ((abs_nonneg (Z ω)).trans (hZb ω)))
    else 0

/-- **The defining pointwise identity of `afterStepSP`**: off the time origin it is
`𝟙_{a < t}·Z·V`. -/
private lemma coe_afterStepSP (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ItoIntegralL2.natFiltration hBmeas a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (V : TBoundedSP T hBmeas) {t : ℝ≥0} (ht : t ≠ 0) (ω : Ω) :
    ⇑(afterStepSP T a hBmeas Z hZm C hZb V).val t ω
      = afterFactor a Z (t, ω) * ⇑V.val t ω := by
  have htbot : t ∉ ({(⊥ : ℝ≥0)} : Set ℝ≥0) := by
    simp only [Set.mem_singleton_iff, NNReal.bot_eq_zero]
    exact ht
  have hV : ⇑V.val t ω
      = ∑ p ∈ V.val.value.support,
          (Set.Ioc p.1 p.2).indicator (fun _ ↦ V.val.value p ω) t := by
    rw [SimpleProcess.apply_eq, Set.indicator_of_notMem htbot, zero_add, Finsupp.sum]
  rw [afterStepSP, AddSubmonoidClass.coe_finsetSum, coe_simpleProcess_sum, hV, Finset.mul_sum,
    ← Finset.sum_attach V.val.value.support
      (fun q ↦ afterFactor a Z (t, ω) * (Set.Ioc q.1 q.2).indicator
        (fun _ ↦ V.val.value q ω) t)]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  by_cases hle : a ⊔ p.val.1 ≤ p.val.2
  · rw [dif_pos hle, coe_stepSP]
    simp only [afterFactor]
    by_cases hat : a < t
    · have hmem : t ∈ Set.Ioc (a ⊔ p.val.1) p.val.2 ↔ t ∈ Set.Ioc p.val.1 p.val.2 := by
        simp only [Set.mem_Ioc, sup_lt_iff]
        exact ⟨fun h ↦ ⟨h.1.2, h.2⟩, fun h ↦ ⟨⟨hat, h.1⟩, h.2⟩⟩
      by_cases hin : t ∈ Set.Ioc p.val.1 p.val.2
      · rw [Set.indicator_of_mem (hmem.mpr hin), Set.indicator_of_mem hin, if_pos hat]
      · rw [Set.indicator_of_notMem (fun hc ↦ hin (hmem.mp hc)), Set.indicator_of_notMem hin,
          mul_zero]
    · rw [if_neg hat, zero_mul]
      exact Set.indicator_of_notMem (fun hc ↦ hat (lt_of_le_of_lt le_sup_left hc.1)) _
  · rw [dif_neg hle]
    have hzero : ⇑((0 : TBoundedSP T hBmeas).val) t ω = 0 := by simp
    rw [hzero, eq_comm]
    simp only [afterFactor]
    by_cases hat : a < t
    · rw [Set.indicator_of_notMem (fun hc ↦ hle (sup_le (hat.le.trans hc.2) (hc.1.le.trans hc.2))),
        mul_zero]
    · rw [if_neg hat, zero_mul]

/-- **The simple-process bridge.** Embedding the restarted process is the same as
scaling the embedding. -/
private lemma simpleAssembly_T_afterStepSP (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ItoIntegralL2.natFiltration hBmeas a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (V : TBoundedSP T hBmeas) :
    simpleAssembly_T (μ := μ) T hBmeas (afterStepSP T a hBmeas Z hZm C hZb V)
      = smulAdaptedCLM T a hBmeas Z hZm C hZb (simpleAssembly_T (μ := μ) T hBmeas V) := by
  refine Lp.ext ?_
  filter_upwards [(memLp_uncurry_trim_T (μ := μ) T hBmeas
      (afterStepSP T a hBmeas Z hZm C hZb V).val).coeFn_toLp,
    coeFn_smulAdaptedCLM T a hBmeas Z hZm C hZb (simpleAssembly_T (μ := μ) T hBmeas V),
    (memLp_uncurry_trim_T (μ := μ) T hBmeas V.val).coeFn_toLp,
    ae_fst_ne_zero (μ := μ) T hBmeas] with p e1 e2 e3 hp
  rw [show (simpleAssembly_T (μ := μ) T hBmeas (afterStepSP T a hBmeas Z hZm C hZb V) :
        ℝ≥0 × Ω → ℝ) p
      = Function.uncurry ⇑(afterStepSP T a hBmeas Z hZm C hZb V).val p from e1, e2,
    show (simpleAssembly_T (μ := μ) T hBmeas V : ℝ≥0 × Ω → ℝ) p
      = Function.uncurry ⇑V.val p from e3]
  obtain ⟨t, ω⟩ := p
  exact coe_afterStepSP T a hBmeas Z hZm C hZb V hp ω

/-- The elementary integral of the restarted process, term by term. -/
private lemma itoSimple_afterStepSP_eq (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ItoIntegralL2.natFiltration hBmeas a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (V : TBoundedSP T hBmeas) (ω : Ω) :
    ItoIntegralL2.itoSimple hBmeas (afterStepSP T a hBmeas Z hZm C hZb V).val ω
      = ∑ p ∈ V.val.value.support.attach,
          if _h : a ⊔ p.val.1 ≤ p.val.2 then
            Z ω * V.val.value p.val ω * (B p.val.2 ω - B (a ⊔ p.val.1) ω) else 0 := by
  rw [afterStepSP, AddSubmonoidClass.coe_finsetSum, ItoIntegralBrownian.itoSimple_sum,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  by_cases hle : a ⊔ p.val.1 ≤ p.val.2
  · rw [dif_pos hle, dif_pos hle, ItoIntegralBrownian.itoSimple_stepSP]
  · rw [dif_neg hle, dif_neg hle]
    simp [ItoIntegralL2.itoSimple]

/-- **The scaling passes through the elementary integral**: `Z` factors out of the
finite increment sum. -/
private lemma itoSimple_afterStepSP_smul (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ItoIntegralL2.natFiltration hBmeas a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (V : TBoundedSP T hBmeas) (ω : Ω) :
    ItoIntegralL2.itoSimple hBmeas (afterStepSP T a hBmeas Z hZm C hZb V).val ω
      = Z ω * ItoIntegralL2.itoSimple hBmeas
          (afterStepSP T a hBmeas (fun _ ↦ (1 : ℝ)) measurable_const 1
            (fun _ ↦ abs_one.le) V).val ω := by
  rw [itoSimple_afterStepSP_eq, itoSimple_afterStepSP_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  by_cases hle : a ⊔ p.val.1 ≤ p.val.2
  · rw [dif_pos hle, dif_pos hle]; ring
  · rw [dif_neg hle, dif_neg hle, mul_zero]

/-! ### `𝓕_a`-linearity -/

/-- **`𝓕_a`-linearity of the Itô integral.** A bounded `𝓕_a`-measurable factor
passes through the stochastic integral of an integrand supported on `(a, T]`. -/
theorem itoIntegralCLM_T_smulAdapted (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ItoIntegralL2.natFiltration hBmeas a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (hφ : ∀ᵐ p ∂(trimMeasure_T (μ := μ) T hBmeas), p.1 ≤ a → φ p = 0) :
    ⇑(itoIntegralCLM_T hB T hBmeas (smulAdapted T a hBmeas Z hZm C hZb φ))
      =ᵐ[μ] fun ω ↦ Z ω * itoIntegralCLM_T hB T hBmeas φ ω := by
  -- multiplication by `Z` on the sample side
  have hZmΩ : Measurable Z := hZm.mono ((ItoIntegralL2.natFiltration hBmeas).le a) le_rfl
  -- the two continuous maps agree on the dense simple embeddings, hence everywhere
  have hEq : (itoIntegralCLM_T hB T hBmeas).comp (smulAdaptedCLM T a hBmeas Z hZm C hZb)
      = (mulBddCLM μ hZmΩ hZb).comp
          ((itoIntegralCLM_T hB T hBmeas).comp (restrictAfterCLM T a hBmeas)) := by
    refine ContinuousLinearMap.ext fun ψ ↦ ?_
    refine congrFun (DenseRange.equalizer (simpleAssembly_T_denseRange (μ := μ) T hBmeas)
      (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
      (funext fun V ↦ ?_)) ψ
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
    rw [← simpleAssembly_T_afterStepSP T a hBmeas Z hZm C hZb V,
      show restrictAfterCLM T a hBmeas (simpleAssembly_T (μ := μ) T hBmeas V)
          = simpleAssembly_T (μ := μ) T hBmeas
              (afterStepSP T a hBmeas (fun _ ↦ (1 : ℝ)) measurable_const 1
                (fun _ ↦ abs_one.le) V) from
        (simpleAssembly_T_afterStepSP T a hBmeas (fun _ ↦ (1 : ℝ)) measurable_const 1
          (fun _ ↦ abs_one.le) V).symm,
      itoIntegralCLM_T_simpleAssembly_T, itoIntegralCLM_T_simpleAssembly_T]
    refine Lp.ext ?_
    filter_upwards [(ItoIntegralL2.memLp_itoSimple hB hBmeas
        (afterStepSP T a hBmeas Z hZm C hZb V).val).coeFn_toLp,
      coeFn_mulBddCLM μ hZmΩ hZb (ItoIntegralL2.itoSimpleLp hB hBmeas
        (afterStepSP T a hBmeas (fun _ ↦ (1 : ℝ)) measurable_const 1
          (fun _ ↦ abs_one.le) V).val),
      (ItoIntegralL2.memLp_itoSimple hB hBmeas
        (afterStepSP T a hBmeas (fun _ ↦ (1 : ℝ)) measurable_const 1
          (fun _ ↦ abs_one.le) V).val).coeFn_toLp] with ω f1 f2 f3
    rw [show (ItoIntegralL2.itoSimpleLp hB hBmeas
          (afterStepSP T a hBmeas Z hZm C hZb V).val : Ω → ℝ) ω
        = ItoIntegralL2.itoSimple hBmeas (afterStepSP T a hBmeas Z hZm C hZb V).val ω from f1,
      f2, show (ItoIntegralL2.itoSimpleLp hB hBmeas
          (afterStepSP T a hBmeas (fun _ ↦ (1 : ℝ)) measurable_const 1
            (fun _ ↦ abs_one.le) V).val : Ω → ℝ) ω
        = ItoIntegralL2.itoSimple hBmeas
            (afterStepSP T a hBmeas (fun _ ↦ (1 : ℝ)) measurable_const 1
              (fun _ ↦ abs_one.le) V).val ω from f3]
    exact itoSimple_afterStepSP_smul T a hBmeas Z hZm C hZb V ω
  have h1 := DFunLike.congr_fun hEq φ
  simp only [ContinuousLinearMap.comp_apply, restrictAfterCLM_eq T a hBmeas φ hφ] at h1
  rw [show smulAdapted T a hBmeas Z hZm C hZb φ
      = smulAdaptedCLM T a hBmeas Z hZm C hZb φ from rfl, h1]
  exact coeFn_mulBddCLM μ hZmΩ hZb _

/-- **Unbounded `Z`.** The hypothesis is exactly that the *product* `Z·φ` is a
legitimate `L²` integrand; nothing is assumed about the moments of `Z` alone.
Localise on the `𝓕_a`-sets `{|Z| ≤ M}`: on each of them the bounded theorem
applies twice — with factor `𝟙_{|Z|≤M}` against the integrand `Z·φ`, and with
factor `𝟙_{|Z|≤M}·Z` against `φ` — and the two scaled integrands coincide. The
sets exhaust `Ω`, so the a.e. identities glue. -/
theorem itoIntegralCLM_T_smulAdapted_of_memLp (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ItoIntegralL2.natFiltration hBmeas a] Z)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (hφ : ∀ᵐ p ∂(trimMeasure_T (μ := μ) T hBmeas), p.1 ≤ a → φ p = 0)
    (hZφ : MemLp (fun p : ℝ≥0 × Ω ↦ Z p.2 * φ p) 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ⇑(itoIntegralCLM_T hB T hBmeas (hZφ.toLp _))
      =ᵐ[μ] fun ω ↦ Z ω * itoIntegralCLM_T hB T hBmeas φ ω := by
  set ψ := hZφ.toLp (fun p : ℝ≥0 × Ω ↦ Z p.2 * φ p)
  have hψ : ∀ᵐ p ∂(trimMeasure_T (μ := μ) T hBmeas), p.1 ≤ a → ψ p = 0 := by
    filter_upwards [hZφ.coeFn_toLp, hφ] with p e1 e2 h
    rw [show (ψ : ℝ≥0 × Ω → ℝ) p = Z p.2 * (φ : ℝ≥0 × Ω → ℝ) p from e1, e2 h, mul_zero]
  have key : ∀ M : ℕ, ∀ᵐ ω ∂μ, |Z ω| ≤ (M : ℝ) →
      (itoIntegralCLM_T hB T hBmeas ψ) ω = Z ω * (itoIntegralCLM_T hB T hBmeas φ) ω := by
    intro M
    have hAm : MeasurableSet[ItoIntegralL2.natFiltration hBmeas a] {ω | |Z ω| ≤ (M : ℝ)} := by
      rw [show {ω | |Z ω| ≤ (M : ℝ)} = Z ⁻¹' (Set.Icc (-(M : ℝ)) (M : ℝ)) from by
        ext ω; simp [abs_le]]
      exact hZm measurableSet_Icc
    have hg1m : Measurable[ItoIntegralL2.natFiltration hBmeas a]
        (Set.indicator {ω | |Z ω| ≤ (M : ℝ)} (fun _ ↦ (1 : ℝ))) := measurable_const.indicator hAm
    have hg1b : ∀ ω, |Set.indicator {ω | |Z ω| ≤ (M : ℝ)} (fun _ ↦ (1 : ℝ)) ω| ≤ 1 := by
      intro ω
      by_cases hm : ω ∈ {ω | |Z ω| ≤ (M : ℝ)}
      · simp [Set.indicator_of_mem hm]
      · simp [Set.indicator_of_notMem hm]
    have hgZm : Measurable[ItoIntegralL2.natFiltration hBmeas a]
        (Set.indicator {ω | |Z ω| ≤ (M : ℝ)} Z) := hZm.indicator hAm
    have hgZb : ∀ ω, |Set.indicator {ω | |Z ω| ≤ (M : ℝ)} Z ω| ≤ (M : ℝ) := by
      intro ω
      by_cases hm : ω ∈ {ω | |Z ω| ≤ (M : ℝ)}
      · rw [Set.indicator_of_mem hm]; exact hm
      · simp [Set.indicator_of_notMem hm]
    have E1 := itoIntegralCLM_T_smulAdapted hB T a hBmeas _ hg1m 1 hg1b ψ hψ
    have E2 := itoIntegralCLM_T_smulAdapted hB T a hBmeas _ hgZm (M : ℝ) hgZb φ hφ
    have hsame : smulAdapted T a hBmeas _ hg1m 1 hg1b ψ
        = smulAdapted T a hBmeas _ hgZm (M : ℝ) hgZb φ := by
      refine Lp.ext ?_
      filter_upwards [coeFn_smulAdapted_afterFactor T a hBmeas _ hg1m 1 hg1b ψ,
        coeFn_smulAdapted_afterFactor T a hBmeas _ hgZm (M : ℝ) hgZb φ,
        hZφ.coeFn_toLp] with p f1 f2 f3
      rw [f1, f2, show (ψ : ℝ≥0 × Ω → ℝ) p = Z p.2 * (φ : ℝ≥0 × Ω → ℝ) p from f3]
      simp only [afterFactor]
      split_ifs with h
      · by_cases hm : p.2 ∈ {ω | |Z ω| ≤ (M : ℝ)}
        · simp [Set.indicator_of_mem hm]
        · simp [Set.indicator_of_notMem hm]
      · rw [zero_mul, zero_mul]
    rw [hsame] at E1
    filter_upwards [E1, E2] with ω h1 h2 hω
    have hmem : ω ∈ {ω | |Z ω| ≤ (M : ℝ)} := hω
    have h3 := h1.symm.trans h2
    rwa [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, one_mul] at h3
  filter_upwards [ae_all_iff.mpr key] with ω hω
  obtain ⟨M, hM⟩ := exists_nat_ge |Z ω|
  exact hω M hM

/-- **Unbounded `Z`, existential form** — the shape the step-integrand Doléans
induction consumes: `Z·∫φ dB` is itself an Itô integral. -/
theorem itoIntegralCLM_T_smulAdapted_mem_range (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ItoIntegralL2.natFiltration hBmeas a] Z)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (hφ : ∀ᵐ p ∂(trimMeasure_T (μ := μ) T hBmeas), p.1 ≤ a → φ p = 0)
    (hZφ : MemLp (fun p : ℝ≥0 × Ω ↦ Z p.2 * φ p) 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ∃ χ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      ⇑(itoIntegralCLM_T hB T hBmeas χ)
        =ᵐ[μ] fun ω ↦ Z ω * itoIntegralCLM_T hB T hBmeas φ ω :=
  ⟨hZφ.toLp _, itoIntegralCLM_T_smulAdapted_of_memLp hB T a hBmeas Z hZm φ hφ hZφ⟩

end MathFin
