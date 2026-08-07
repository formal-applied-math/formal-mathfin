/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralCovariation
public import MathFin.Foundations.WienerExponentialTotality

/-!
# The martingale representation theorem on the Brownian filtration

The Itô integral `φ ↦ ∫₀ᵀ φ dB` is an isometry of the predictable `L²` integrands into
`L²(μ)` (`ItoIntegralCovariation.itoIsometry_T`). This file identifies its image exactly: the
**centered `𝓕ᴮ_T`-measurable** part of `L²(μ)`. Equivalently, every square-integrable claim
measurable for the Brownian σ-algebra is its own mean plus an Itô integral, uniquely — and
every square-integrable martingale on that filtration is its initial value plus an Itô
integral process. In the language of the pricing tower this is market completeness: the
theorem that turns a European claim into a hedging strategy.

## The argument

Surjectivity of an isometry onto a closed subspace is a *totality* statement about its range,
and the two halves come from the preceding modules:

* `DoleansStepRepresentation.stepDoleans_sub_one_mem_range` puts every step-integrand Doléans
  exponential, minus one, inside the range;
* `WienerExponentialTotality.eq_zero_of_orthogonal_stepDoleans` says an `L²(𝓕ᴮ_T)` variable
  orthogonal to all of them is zero.

They meet through an orthogonal decomposition. The range is complete — the image of a complete
space under an isometry — hence orthogonally complemented, so a centered `𝓕ᴮ_T`-measurable `F`
splits as `y + z` with `y` in the range and `z ⊥ range`. Then `z` inherits `𝓕ᴮ_T`-measurability
and centering from `F`, and `∫ z·D = ∫ z·(D − 1) + ∫ z = 0` for every step Doléans `D` — the
first term because `D − 1` is in the range, the second by centering. Totality kills `z`.

The decomposition runs in the ambient `L²(μ)`, not inside `↥(lpMeas …)`. That is deliberate:
the constants and the range both sit inside `lpMeas ℝ ℝ 𝓕ᴮ_T 2 μ`, so the remainder `z = F − y`
does too, and no `comap` transport is needed. The `Kᗮ = ⊥ ↔ K = ⊤` route would have needed it,
`Submodule.orthogonal_eq_bot_iff` being ambient-relative.

The centering fact `𝔼[∫₀ᵀ φ dB] = 0` is proved, not assumed — one floor down, as
`ItoIntegralProcessGeneral.integral_itoIntegralCLM_T`: the integral *process* is a martingale
(`itoIntegralProcessGen_isMartingale`) started at `0` (`itoProcessCLM_zero_time`, by density
from `itoSimpleProcess_zero_time`), and conditioning preserves the mean.

## Result

* `inner_eq_integral_mul` — the real `L²` inner product as an integral of a product.
* `itoIntegralCLM_T_mem_lpMeas` — the terminal Itô integral is `𝓕ᴮ_T`-measurable.
* `mem_range_itoIntegralCLM_T_of_centered` — kernel form: a centered `𝓕ᴮ_T`-measurable `L²`
  variable *is* an Itô integral.
* `exists_itoIntegral_representation` — terminal form: `F =ᵐ 𝔼[F] + ∫₀ᵀ φ dB` for a unique `φ`.
* `itoIntegralCLM_T_surjective_onto_centered` — submodule form: the Itô integrals together
  with the constants exhaust `lpMeas ℝ ℝ 𝓕ᴮ_T 2 μ`.
* `centeredBrownianL2`, `mem_centeredBrownianL2` — the centered `𝓕ᴮ_T`-measurable subspace.
* `itoIsometryCentered`, `coe_itoIsometryCentered`, `itoIsometryCentered_surjective` —
  the Itô isometry corestricted to that subspace, and its surjectivity.
* `itoIsometryEquiv` — those two bundled: `φ ↦ ∫₀ᵀ φ dB` as a linear isometric
  equivalence onto `centeredBrownianL2`.
* `martingale_representation` — process form (corpus entry `gir-thm-9.3.4`).
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter Topology
open ItoIntegralCLM ItoIntegralL2 ItoIntegralProcess ItoIntegralProcessGeneral
open ItoIntegralCovariation
open scoped NNReal ENNReal InnerProductSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

/-! ### The constants, and recentring -/

omit [IsProbabilityMeasure μ] in
/-- The real `L²` inner product as an integral of a product. -/
lemma inner_eq_integral_mul (f g : Lp ℝ 2 μ) :
    ⟪f, g⟫_ℝ = ∫ ω, f ω * g ω ∂μ := by
  rw [L2.inner_def]
  simp [RCLike.inner_apply, mul_comm]

/-- A constant `Lp` element is a.e. that constant. -/
private lemma coeFn_smul_const (c : ℝ) :
    (⇑(c • Lp.const 2 μ (1 : ℝ)) : Ω → ℝ) =ᵐ[μ] fun _ ↦ c := by
  filter_upwards [Lp.coeFn_smul c (Lp.const 2 μ (1 : ℝ))] with ω h1
  simp [h1]

/-- Pairing against the constant `1` is the mean. -/
private lemma inner_const_left (F : Lp ℝ 2 μ) :
    ⟪Lp.const 2 μ (1 : ℝ), F⟫_ℝ = ∫ ω, F ω ∂μ := by
  rw [inner_eq_integral_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_const 2 μ (1 : ℝ)] with ω hω
  rw [hω]
  simp

/-- Constants are measurable for every σ-algebra, so they sit in every `lpMeas`. -/
private lemma const_mem_lpMeas (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    Lp.const 2 μ (1 : ℝ) ∈ lpMeas ℝ ℝ (ItoIntegralL2.natFiltration hBmeas T) 2 μ :=
  ⟨Function.const Ω (1 : ℝ), stronglyMeasurable_const, Lp.coeFn_const 2 μ (1 : ℝ)⟩

/-- Subtracting the mean, pointwise. -/
private lemma coeFn_sub_mean (F : Lp ℝ 2 μ) :
    (⇑(F - (∫ x, F x ∂μ) • Lp.const 2 μ (1 : ℝ)) : Ω → ℝ)
      =ᵐ[μ] fun ω ↦ F ω - ∫ x, F x ∂μ := by
  filter_upwards [Lp.coeFn_sub F ((∫ x, F x ∂μ) • Lp.const 2 μ (1 : ℝ)),
    coeFn_smul_const (μ := μ) (∫ x, F x ∂μ)] with ω h1 h2
  rw [h1, Pi.sub_apply, h2]

/-- Subtracting the mean centers. -/
private lemma integral_sub_mean (F : Lp ℝ 2 μ) :
    ∫ ω, (F - (∫ x, F x ∂μ) • Lp.const 2 μ (1 : ℝ)) ω ∂μ = 0 := by
  rw [integral_congr_ae (coeFn_sub_mean F),
    integral_sub ((Lp.memLp F).integrable one_le_two) (integrable_const _),
    integral_const, probReal_univ, one_smul, sub_self]

/-! ### The Itô integral is `𝓕ᴮ_T`-measurable -/

/-- The terminal Itô integral is `𝓕ᴮ_T`-measurable: at the horizon the integral *process*
is the terminal integral, and the process is adapted. -/
lemma itoIntegralCLM_T_mem_lpMeas (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    itoIntegralCLM_T hB T hBmeas φ ∈ lpMeas ℝ ℝ (ItoIntegralL2.natFiltration hBmeas T) 2 μ := by
  rw [← itoProcessCLM_terminal_eq hB T hBmeas φ]
  exact itoProcessCLM_aeStronglyMeasurable hB T T hBmeas φ

/-! ### Surjectivity onto the centered subspace -/

/-- **Orthogonality to the Wiener exponentials.** A centered `L²` variable orthogonal to
every Itô integral is orthogonal to every step Doléans exponential: `stepDoleansExp − 1` is
an Itô integral, and the leftover `1` is killed by centering. -/
private lemma integral_mul_stepDoleansExp_eq_zero (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) (T : ℝ≥0) (z : Lp ℝ 2 μ)
    (hz : z ∈ (LinearMap.range (itoIntegralCLM_T hB T hBmeas).toLinearMap)ᗮ)
    (hz0 : ∫ ω, z ω ∂μ = 0) (s : ℕ → ℝ≥0) (hs : Monotone s) (h : ℕ → ℝ) (N : ℕ)
    (hsN : s N = T) :
    ∫ ω, z ω * stepDoleansExp B s h N ω ∂μ = 0 := by
  obtain ⟨χ, hχ⟩ := stepDoleans_sub_one_mem_range hB hBmeas hBcont T s hs h N hsN
  have hmul : Integrable (fun ω ↦ (itoIntegralCLM_T hB T hBmeas χ) ω * z ω) μ :=
    MemLp.integrable_mul (Lp.memLp (itoIntegralCLM_T hB T hBmeas χ)) (Lp.memLp z)
  have hXz : ∫ ω, (itoIntegralCLM_T hB T hBmeas χ) ω * z ω ∂μ = 0 := by
    rw [← inner_eq_integral_mul]
    exact (Submodule.mem_orthogonal _ z).mp hz _ (LinearMap.mem_range_self _ χ)
  rw [integral_congr_ae (show (fun ω ↦ z ω * stepDoleansExp B s h N ω)
      =ᵐ[μ] fun ω ↦ (itoIntegralCLM_T hB T hBmeas χ) ω * z ω + z ω by
    filter_upwards [hχ] with ω hω
    rw [sub_eq_iff_eq_add.mp hω]
    ring), integral_add hmul ((Lp.memLp z).integrable one_le_two), hXz, hz0, add_zero]

/-- **Martingale representation, kernel form.** A centered `𝓕ᴮ_T`-measurable `L²` variable
*is* an Itô integral. Split `F = y + z` against the range — closed, being the image of a
complete space under an isometry, hence orthogonally complemented. The remainder `z` inherits
both `𝓕ᴮ_T`-measurability and centering from `F`, so the totality theorem forces `z = 0`. -/
theorem mem_range_itoIntegralCLM_T_of_centered (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (T : ℝ≥0) (F : Lp ℝ 2 μ)
    (hFmeas : AEStronglyMeasurable[ItoIntegralL2.natFiltration hBmeas T] (⇑F) μ)
    (hF0 : ∫ ω, F ω ∂μ = 0) :
    F ∈ LinearMap.range (itoIntegralCLM_T hB T hBmeas).toLinearMap := by
  haveI : CompleteSpace ↥(LinearMap.range (itoIntegralCLM_T hB T hBmeas).toLinearMap) :=
    ((itoIsometry_T hB T hBmeas).isometry.isClosedEmbedding.isClosed_range).completeSpace_coe
  obtain ⟨y, hy, z, hz, hFyz⟩ :=
    (LinearMap.range (itoIntegralCLM_T hB T hBmeas).toLinearMap).exists_add_mem_mem_orthogonal F
  -- `id` destructures a copy: a bare `obtain` would clear `hy`, which is needed again below.
  obtain ⟨ψ, hψ⟩ := id hy
  have hymem : y ∈ lpMeas ℝ ℝ (ItoIntegralL2.natFiltration hBmeas T) 2 μ := by
    rw [← hψ]
    exact itoIntegralCLM_T_mem_lpMeas hB T hBmeas ψ
  have hy0 : ∫ ω, y ω ∂μ = 0 := by
    rw [← hψ]
    exact integral_itoIntegralCLM_T hB T hBmeas ψ
  have hz0 : ∫ ω, z ω ∂μ = 0 := by
    have h := integral_congr_ae (show (⇑F : Ω → ℝ) =ᵐ[μ] fun ω ↦ y ω + z ω by
      rw [hFyz]; exact Lp.coeFn_add y z)
    rw [integral_add ((Lp.memLp y).integrable one_le_two)
      ((Lp.memLp z).integrable one_le_two), hy0, hF0, zero_add] at h
    exact h.symm
  have hzmem : z ∈ lpMeas ℝ ℝ (ItoIntegralL2.natFiltration hBmeas T) 2 μ := by
    rw [eq_sub_of_add_eq' hFyz.symm]
    exact sub_mem hFmeas hymem
  rw [hFyz, eq_zero_of_orthogonal_stepDoleans hB hBmeas hBcont T z
    (mem_lpMeas_iff_aestronglyMeasurable.mp hzmem)
    -- the totality theorem still asks for `s 0 = 0`; the representation no longer needs it.
    (fun s hs h N _ hsN ↦
      integral_mul_stepDoleansExp_eq_zero hB hBmeas hBcont T z hz hz0 s hs h N hsN), add_zero]
  exact hy

/-! ### The headline forms -/

/-- **Martingale representation, terminal form.** Every square-integrable `𝓕ᴮ_T`-measurable
variable is its mean plus an Itô integral, and the integrand is unique. Existence is the
kernel form applied to `F − 𝔼[F]·1`; uniqueness is injectivity of an isometry. -/
theorem exists_itoIntegral_representation (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (T : ℝ≥0)
    (F : Lp ℝ 2 μ)
    (hFmeas : AEStronglyMeasurable[ItoIntegralL2.natFiltration hBmeas T] (⇑F) μ) :
    ∃! φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (⇑F) =ᵐ[μ] fun ω ↦ (∫ x, F x ∂μ) + itoIntegralCLM_T hB T hBmeas φ ω := by
  obtain ⟨φ, hφ⟩ := mem_range_itoIntegralCLM_T_of_centered hB hBmeas hBcont T
    (F - (∫ x, F x ∂μ) • Lp.const 2 μ (1 : ℝ))
    (sub_mem hFmeas (Submodule.smul_mem _ _ (const_mem_lpMeas T hBmeas)))
    (integral_sub_mean F)
  have hval : (⇑F : Ω → ℝ)
      =ᵐ[μ] fun ω ↦ (∫ x, F x ∂μ) + itoIntegralCLM_T hB T hBmeas φ ω := by
    have h1 : (⇑(itoIntegralCLM_T hB T hBmeas φ) : Ω → ℝ)
        =ᵐ[μ] fun ω ↦ F ω - ∫ x, F x ∂μ := by
      rw [show itoIntegralCLM_T hB T hBmeas φ
        = F - (∫ x, F x ∂μ) • Lp.const 2 μ (1 : ℝ) from hφ]
      exact coeFn_sub_mean F
    filter_upwards [h1] with ω hω
    rw [hω]
    ring
  refine ⟨φ, hval, fun ψ hψ ↦ ?_⟩
  have heq : itoIntegralCLM_T hB T hBmeas ψ = itoIntegralCLM_T hB T hBmeas φ := by
    refine Lp.ext ?_
    filter_upwards [hψ, hval] with ω h1 h2
    exact add_left_cancel (h1.symm.trans h2)
  exact (itoIsometry_T hB T hBmeas).injective heq

/-- **Martingale representation, submodule form.** The Itô integrals against `B` on `[0,T]`
together with the constants exhaust the `𝓕ᴮ_T`-measurable part of `L²(μ)`. -/
theorem itoIntegralCLM_T_surjective_onto_centered (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (T : ℝ≥0) :
    LinearMap.range (itoIntegralCLM_T hB T hBmeas).toLinearMap
        ⊔ (ℝ ∙ (Lp.const 2 μ (1 : ℝ)))
      = lpMeas ℝ ℝ (ItoIntegralL2.natFiltration hBmeas T) 2 μ := by
  refine le_antisymm (sup_le ?_ ?_) fun F hF ↦ ?_
  · rintro _ ⟨φ, rfl⟩
    exact itoIntegralCLM_T_mem_lpMeas hB T hBmeas φ
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact const_mem_lpMeas T hBmeas
  · obtain ⟨φ, hφ, -⟩ := exists_itoIntegral_representation hB hBmeas hBcont T F hF
    rw [show F = itoIntegralCLM_T hB T hBmeas φ + (∫ x, F x ∂μ) • Lp.const 2 μ (1 : ℝ) from
      Lp.ext (by
        filter_upwards [hφ, Lp.coeFn_add (itoIntegralCLM_T hB T hBmeas φ)
          ((∫ x, F x ∂μ) • Lp.const 2 μ (1 : ℝ)), coeFn_smul_const (μ := μ) (∫ x, F x ∂μ)]
          with ω h1 h2 h3
        rw [h1, h2, Pi.add_apply, h3, add_comm])]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ φ)
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

/-! ### The isometry onto the centered subspace -/

/-- The centered `𝓕ᴮ_T`-measurable subspace of `L²(μ)` — the Itô isometry's true target.
"Centered" is spelled as orthogonality to the constants, which for a probability measure
is `∫F = 0`. -/
noncomputable def centeredBrownianL2 (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    Submodule ℝ (Lp ℝ 2 μ) :=
  lpMeas ℝ ℝ (ItoIntegralL2.natFiltration hBmeas T) 2 μ
    ⊓ (ℝ ∙ (Lp.const 2 μ (1 : ℝ)))ᗮ

/-- Membership in `centeredBrownianL2` unfolded: `𝓕ᴮ_T`-measurable and mean zero. -/
lemma mem_centeredBrownianL2 (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) (F : Lp ℝ 2 μ) :
    F ∈ centeredBrownianL2 (μ := μ) T hBmeas ↔
      AEStronglyMeasurable[ItoIntegralL2.natFiltration hBmeas T] (⇑F) μ
        ∧ ∫ ω, F ω ∂μ = 0 := by
  rw [centeredBrownianL2, Submodule.mem_inf]
  refine and_congr Iff.rfl ⟨fun hF ↦ ?_, fun hF ↦ ?_⟩
  · rw [← inner_const_left]
    exact (Submodule.mem_orthogonal _ F).mp hF _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [real_inner_smul_left, inner_const_left, hF, mul_zero]

/-- The `[0,T]` Itô integral corestricted to its true target, the centered
`𝓕ᴮ_T`-measurable subspace: `ItoIntegralCovariation.itoIsometry_T` with a sharper codomain. -/
noncomputable def itoIsometryCentered (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) →ₗᵢ[ℝ] centeredBrownianL2 (μ := μ) T hBmeas where
  toLinearMap := LinearMap.codRestrict (centeredBrownianL2 (μ := μ) T hBmeas)
    (itoIntegralCLM_T hB T hBmeas).toLinearMap fun φ ↦
      (mem_centeredBrownianL2 T hBmeas _).mpr
        ⟨itoIntegralCLM_T_mem_lpMeas hB T hBmeas φ, integral_itoIntegralCLM_T hB T hBmeas φ⟩
  norm_map' φ := itoIntegralCLM_T_norm hB T hBmeas φ

/-- The corestriction changes nothing but the codomain. -/
@[simp] lemma coe_itoIsometryCentered (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    (itoIsometryCentered hB T hBmeas φ : Lp ℝ 2 μ) = itoIntegralCLM_T hB T hBmeas φ := rfl

/-- **The Itô isometry is onto the centered subspace.** Every centered `𝓕ᴮ_T`-measurable `L²`
variable is hit, by the kernel form. -/
theorem itoIsometryCentered_surjective (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (T : ℝ≥0) :
    Function.Surjective (itoIsometryCentered hB T hBmeas) := fun y ↦
  let ⟨hy1, hy2⟩ := (mem_centeredBrownianL2 T hBmeas _).mp y.2
  let ⟨ψ, hψ⟩ := mem_range_itoIntegralCLM_T_of_centered hB hBmeas hBcont T y hy1 hy2
  ⟨ψ, Subtype.ext ((coe_itoIsometryCentered hB T hBmeas ψ).trans hψ)⟩

/-- **The Itô isometry as an equivalence.** `φ ↦ ∫₀ᵀ φ dB` is a linear isometric equivalence
from the predictable `L²` integrands onto the centered `𝓕ᴮ_T`-measurable part of `L²(μ)`:
the corestriction is injective because it is an isometry, and surjective by
`itoIsometryCentered_surjective`. -/
noncomputable def itoIsometryEquiv (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) ≃ₗᵢ[ℝ]
      centeredBrownianL2 (μ := μ) T hBmeas :=
  LinearIsometryEquiv.ofSurjective (itoIsometryCentered hB T hBmeas)
    (itoIsometryCentered_surjective hB hBmeas hBcont T)

/-- **Martingale representation, process form.** Corpus entry `gir-thm-9.3.4`: every
square-integrable martingale on the Brownian filtration is its initial value plus an Itô
integral process. The terminal form supplies the integrand; the martingale property spreads
it over every `t ≤ T`, because `(φ●B)_t` is exactly the `𝓕_t`-conditional expectation of
`∫₀ᵀ φ dB` (`itoProcessCLM_eq_condExpL2`). That `M 0` is a.e. constant is not assumed — it is
the representation read at `t = 0`, where the integral process vanishes. -/
theorem martingale_representation (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (T : ℝ≥0)
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M (ItoIntegralL2.natFiltration hBmeas) μ)
    (hMT : MemLp (M T) 2 μ) :
    ∃ φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      ∀ t ≤ T, M t =ᵐ[μ] fun ω ↦ M 0 ω + itoProcessCLM hB T t hBmeas φ ω := by
  obtain ⟨φ, hφ, -⟩ := exists_itoIntegral_representation hB hBmeas hBcont T (hMT.toLp (M T))
    ((hM.1 T).aestronglyMeasurable.congr hMT.coeFn_toLp.symm)
  have key (t : ℝ≥0) (ht : t ≤ T) : M t =ᵐ[μ]
      fun ω ↦ (∫ x, (hMT.toLp (M T)) x ∂μ) + itoProcessCLM hB T t hBmeas φ ω := by
    have hproc : μ[(⇑(itoIntegralCLM_T hB T hBmeas φ) : Ω → ℝ) |
          ItoIntegralL2.natFiltration hBmeas t]
        =ᵐ[μ] ⇑(itoProcessCLM hB T t hBmeas φ) := by
      have h := (Lp.memLp (itoIntegralCLM_T hB T hBmeas φ)).condExpL2_ae_eq_condExp
        (𝕜 := ℝ) ((ItoIntegralL2.natFiltration hBmeas).le t)
      rw [Lp.toLp_coeFn] at h
      rw [itoProcessCLM_eq_condExpL2 hB T t hBmeas φ]
      exact h.symm
    have hrep : μ[(⇑(hMT.toLp (M T)) : Ω → ℝ) | ItoIntegralL2.natFiltration hBmeas t]
        =ᵐ[μ] μ[((fun _ ↦ ∫ x, (hMT.toLp (M T)) x ∂μ)
            + ⇑(itoIntegralCLM_T hB T hBmeas φ) : Ω → ℝ) |
          ItoIntegralL2.natFiltration hBmeas t] := condExp_congr_ae hφ
    exact ((hM.2 t T ht).symm.trans (condExp_congr_ae hMT.coeFn_toLp.symm)).trans
      (hrep.trans ((condExp_add (integrable_const _)
        ((Lp.memLp (itoIntegralCLM_T hB T hBmeas φ)).integrable one_le_two)
        (ItoIntegralL2.natFiltration hBmeas t)).trans
        ((condExp_const ((ItoIntegralL2.natFiltration hBmeas).le t)
          (∫ x, (hMT.toLp (M T)) x ∂μ)).eventuallyEq.add hproc)))
  have hzero : ∀ᵐ ω ∂μ, (itoProcessCLM hB T 0 hBmeas φ) ω = 0 := by
    rw [itoProcessCLM_zero_time hB T hBmeas φ]
    exact Lp.coeFn_zero ℝ 2 μ
  refine ⟨φ, fun t ht ↦ ?_⟩
  filter_upwards [key t ht, key 0 zero_le, hzero] with ω h1 h2 h3
  rw [h1, h2, h3, add_zero]

end MathFin
