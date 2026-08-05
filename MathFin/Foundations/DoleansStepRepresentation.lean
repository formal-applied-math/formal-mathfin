/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoFormulaGBM
public import MathFin.Foundations.ItoIntegralLocality
public import MathFin.Foundations.ItoIntegralProcessIsometry

/-!
# The Doléans exponential of a deterministic step integrand is an Itô integral

The Wiener exponentials `∏ₖ exp(hₖ(B_{sₖ₊₁} − B_{sₖ}) − ½hₖ²(sₖ₊₁ − sₖ))` are the test
family for the martingale representation theorem: they are total in `L²(𝓕_T)`, so an
`F ⊥ range(∫·dB)` orthogonal to all of them is zero. To run that argument each of them
must first be shown to *lie* in the range. This file does that.

The telescoping is the whole idea. With `Dₙ` the exponential over the first `n` cells,

  `Dₙ₊₁ − Dₙ = Eₙ·(M_{sₙ₊₁} − M_{sₙ})`,  `Eₙ = Dₙ/M_{sₙ}` `𝓕_{sₙ}`-measurable,

where `M_t = exp(h_n B_t − ½h_n²t)` is the *constant*-integrand Doléans exponential —
already an Itô integral, since it is `discountedGBM_eq_itoIntegral` at `S₀ = 1`. So each
increment is `𝓕_{sₙ}`-scalar times an Itô integral, which `ItoIntegralLocality`'s
`𝓕_a`-linearity turns back into an Itô integral, and the range is a submodule.

Two things have to be built to make that sentence true.

## Time locality: cutting an integrand at `u` cuts the integral at `u`

The Itô formula hands us `∫₀ᵀ φ dB = M_T − 1` at the *horizon* only, whereas the
telescoping needs the increment `M_b − M_a` over an inner band. The bridge is a pair of
facts about an integrand supported on one side of a time `u`, both read off the
time-indexed Itô isometry `‖(φ●B)_u‖² = ∫_{(0,u]} φ²`:

* switched on only after `u` ⟹ `(φ●B)_u = 0` (`itoProcessCLM_eq_zero_of_vanishes_before`);
* switched off after `u` ⟹ `∫₀ᵀ φ dB = (φ●B)_u`, hence `𝓕_u`-measurable
  (`itoIntegralCLM_T_eq_itoProcessCLM_of_vanishes_after`) — because then the
  `𝓕_u`-projection of `∫₀ᵀ φ dB` has *full norm*, and a norm-preserving orthogonal
  projection is the identity on that vector.

Together: `∫₀ᵀ 𝟙_{(u,T]}·φ dB = ∫₀ᵀ φ dB − (φ●B)_u`. Since the Itô-integral process is
the conditional expectation of its terminal value, and `M` is Wald's martingale, the
subtracted term is exactly `M_u − 1`, and the band integrand delivers `M_b − M_a`.

## Unbounded scaling: `Z·∫φ dB ∈ L²` is the same requirement as `Z·φ ∈ L²`

`ItoIntegralLocality`'s unbounded-`Z` corollary asks for the *integrand* product
`Z·φ ∈ L²(trim)`. What a Doléans induction can supply is the *sample-side*
`Z·∫φ dB ∈ L²(μ)` — a product of lognormals, whose moments are elementary. The Itô
isometry says these are the same requirement, and `itoIntegralCLM_T_smul_of_memLp`
performs the transfer: truncating `Z` at level `M` gives genuine integrands whose
energies are the (uniformly bounded) sample-side energies, and Fatou passes the bound
to the limit `Z·φ`.

This is also why the constant case is stated existentially here. The plan called for a
version *naming* the integrand as `s ↦ σ·exp(σB_s − ½σ²s)`, to feed that `L²(trim)`
hypothesis; but the exponential Itô formula is reached through
`ito_formula_td_localized`, whose cut-off limit does not identify its integrand (only
the bounded-derivative `ito_formula_td_L2_bddDeriv_explicit` does), so no such naming is
available from the tower. The transfer above removes the need for it.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter ItoIntegralCLM ItoIntegralL2
open ItoIntegralProcessGeneral
open scoped NNReal ENNReal Topology

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

/-! ### Time locality of the Itô integral -/

omit hB in
/-- The predictable trim measure lives on the band `(0,T] × Ω`. -/
private lemma ae_fst_mem_Ioc (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas), z.1 ∈ Set.Ioc 0 T := by
  rw [trimMeasure_T_eq_restrict]
  exact ae_restrict_of_forall_mem
    (MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := natFiltration hBmeas) 0 T
      MeasurableSet.univ) (fun z hz ↦ hz.1)

omit hB in
/-- `(0,u] × Ω` is predictable — the band the time-indexed isometry integrates over. -/
private lemma measurableSet_band (u : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    MeasurableSet[(natFiltration (mΩ := mΩ) hBmeas).predictable]
      (Set.Ioc 0 u ×ˢ (Set.univ : Set Ω)) :=
  MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := natFiltration hBmeas) 0 u
    MeasurableSet.univ

include hB

/-- **An integrand switched on only after `u` has not yet moved at `u`.** By the
time-indexed Itô isometry the energy of `(φ●B)_u` is `∫_{(0,u]} φ²`, which vanishes
when `φ` does. -/
theorem itoProcessCLM_eq_zero_of_vanishes_before (T u : ℝ≥0) (huT : u ≤ T)
    (hBmeas : ∀ t, Measurable (B t)) (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (hφ : ∀ᵐ p ∂(trimMeasure_T (μ := μ) T hBmeas), p.1 ≤ u → φ p = 0) :
    itoProcessCLM hB T u hBmeas φ = 0 := by
  have hzero : ∫ z in (Set.Ioc 0 u ×ˢ (Set.univ : Set Ω)), (φ z) ^ 2
      ∂(trimMeasure_T (μ := μ) T hBmeas) = 0 := by
    have hae : ∀ᵐ z ∂((trimMeasure_T (μ := μ) T hBmeas).restrict
        (Set.Ioc 0 u ×ˢ (Set.univ : Set Ω))), (φ z) ^ 2 = 0 := by
      rw [ae_restrict_iff' (measurableSet_band u hBmeas)]
      filter_upwards [hφ] with z hz hzmem
      rw [hz hzmem.1.2]
      ring
    rw [integral_congr_ae hae, integral_zero]
  refine norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp ?_)
  rw [itoProcessCLM_norm_sq hB huT hBmeas φ, hzero]

/-- **An integrand switched off after `u` has already finished at `u`**: its Itô
integral over `[0,T]` is the Itô-integral *process* at time `u`, hence
`𝓕_u`-measurable. The energy of `(φ●B)_u` is `∫_{(0,u]} φ² = ‖φ‖² = ‖∫₀ᵀ φ dB‖²`, so
the `𝓕_u`-projection of `∫₀ᵀ φ dB` has full norm — and an orthogonal projection that
preserves the norm is the identity on that vector. -/
theorem itoIntegralCLM_T_eq_itoProcessCLM_of_vanishes_after (T u : ℝ≥0) (huT : u ≤ T)
    (hBmeas : ∀ t, Measurable (B t)) (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (hφ : ∀ᵐ p ∂(trimMeasure_T (μ := μ) T hBmeas), u < p.1 → φ p = 0) :
    itoIntegralCLM_T hB T hBmeas φ = itoProcessCLM hB T u hBmeas φ := by
  haveI : Fact ((natFiltration hBmeas u : MeasurableSpace Ω) ≤ mΩ) := ⟨(natFiltration hBmeas).le u⟩
  set X := itoIntegralCLM_T hB T hBmeas φ with hX
  -- the band energy is the whole energy: `φ` is carried by `(0,u]`
  have hband : ∫ z in (Set.Ioc 0 u ×ˢ (Set.univ : Set Ω)), (φ z) ^ 2
      ∂(trimMeasure_T (μ := μ) T hBmeas)
      = ∫ z, (φ z) ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas) := by
    refine setIntegral_eq_integral_of_ae_compl_eq_zero ?_
    filter_upwards [hφ, ae_fst_mem_Ioc T hBmeas] with z hz hzT hznot
    rw [hz (by by_contra hc; exact hznot ⟨⟨hzT.1, not_lt.mp hc⟩, Set.mem_univ _⟩)]
    ring
  have hnorm : ‖(condExpL2 ℝ ℝ ((natFiltration hBmeas).le u) X : Lp ℝ 2 μ)‖ = ‖X‖ := by
    have hsq : ‖itoProcessCLM hB T u hBmeas φ‖ ^ 2 = ‖X‖ ^ 2 := by
      rw [itoProcessCLM_norm_sq hB huT hBmeas φ, hband, hX, itoIntegralCLM_T_norm hB T hBmeas φ,
        lp_two_norm_sq φ]
    rw [← itoProcessCLM_eq_condExpL2 hB T u hBmeas φ]
    have hs := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hs
  rw [itoProcessCLM_eq_condExpL2 hB T u hBmeas φ]
  have hcoe : ((condExpL2 ℝ ℝ ((natFiltration hBmeas).le u) X : Lp ℝ 2 μ))
      = (lpMeas ℝ ℝ (natFiltration hBmeas u) 2 μ).starProjection X := rfl
  rw [hcoe] at hnorm ⊢
  exact (Submodule.starProjection_eq_self_iff.mpr
    ((Submodule.mem_iff_norm_starProjection _ X).mpr hnorm)).symm

omit [IsProbabilityMeasure μ] hB in
/-- `restrictAfterCLM` unfolded: the integrand switched on strictly after `a`. -/
private lemma coeFn_restrictAfterCLM (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ⇑(restrictAfterCLM T a hBmeas φ) =ᵐ[trimMeasure_T (μ := μ) T hBmeas]
      fun p ↦ if a < p.1 then φ p else 0 := by
  filter_upwards [coeFn_smulAdaptedCLM T a hBmeas (fun _ ↦ (1 : ℝ)) measurable_const 1
    (fun _ ↦ abs_one.le) φ] with p hp
  rw [show ⇑(restrictAfterCLM T a hBmeas φ) p
      = afterFactor a (fun _ ↦ (1 : ℝ)) p * (φ : ℝ≥0 × Ω → ℝ) p from hp]
  simp only [afterFactor]
  split_ifs <;> simp

/-- **Restricting an integrand to `(u,T]` removes exactly the past of the integral.**
`∫₀ᵀ 𝟙_{(u,T]}·φ dB = ∫₀ᵀ φ dB − (φ●B)_u`: the complementary piece `𝟙_{(0,u]}·φ` is
switched off after `u`, so its integral is the process value at `u`
(`itoIntegralCLM_T_eq_itoProcessCLM_of_vanishes_after`), and the restriction itself
contributes nothing at `u` (`itoProcessCLM_eq_zero_of_vanishes_before`). -/
theorem itoIntegralCLM_T_restrictAfterCLM (T u : ℝ≥0) (huT : u ≤ T)
    (hBmeas : ∀ t, Measurable (B t)) (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    itoIntegralCLM_T hB T hBmeas (restrictAfterCLM T u hBmeas φ)
      = itoIntegralCLM_T hB T hBmeas φ - itoProcessCLM hB T u hBmeas φ := by
  set R := restrictAfterCLM T u hBmeas φ with hR
  have hafter : ∀ᵐ p ∂(trimMeasure_T (μ := μ) T hBmeas), p.1 ≤ u → R p = 0 := by
    filter_upwards [coeFn_restrictAfterCLM T u hBmeas φ] with p hp hpu
    rw [hp, if_neg (not_lt.mpr hpu)]
  have hbefore : ∀ᵐ p ∂(trimMeasure_T (μ := μ) T hBmeas), u < p.1 → (φ - R) p = 0 := by
    filter_upwards [coeFn_restrictAfterCLM T u hBmeas φ, Lp.coeFn_sub φ R] with p hp hsub hpu
    rw [hsub, Pi.sub_apply, hp, if_pos hpu, sub_self]
  have hkey : itoIntegralCLM_T hB T hBmeas (φ - R) = itoProcessCLM hB T u hBmeas φ := by
    rw [itoIntegralCLM_T_eq_itoProcessCLM_of_vanishes_after hB T u huT hBmeas (φ - R) hbefore,
      map_sub, itoProcessCLM_eq_zero_of_vanishes_before hB T u huT hBmeas R hafter, sub_zero]
  rw [← hkey, map_sub]
  abel

/-! ### The Doléans exponential of a constant integrand over a band -/

/-- **Constant-`σ` Doléans exponential as an Itô integral.** `discountedGBM_eq_itoIntegral`
at `S₀ = 1`, with `B 0 =ᵐ 0`: `exp(σB_T − σ²T/2) − 1 = ∫₀ᵀ σ·exp(σB_s − σ²s/2) dB_s`. -/
theorem constDoleans_sub_one_mem_range (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (T : ℝ≥0) (σ : ℝ) :
    ∃ φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (fun ω ↦ Real.exp (σ * B T ω - σ ^ 2 * (T : ℝ) / 2) - 1)
        =ᵐ[μ] ⇑(itoIntegralCLM_T hB T hBmeas φ) := by
  obtain ⟨gfx, hgfx⟩ := discountedGBM_eq_itoIntegral hB hBmeas hBcont T 1 σ
  refine ⟨gfx, ?_⟩
  filter_upwards [hgfx, ItoIntegralBrownian.eval_zero_ae hB hBmeas] with ω hω h0
  rw [← hω, h0]
  simp only [Pi.zero_apply, mul_zero, Real.exp_zero, one_mul, mul_one]
  ring_nf

/-- **The Doléans exponential of `σ·𝟙_{(a,b]}`, as an Itô integral over `[0,T]`.**
The integrand is `σ·exp(σB_s − σ²s/2)` cut down to the band `(a,b]`; its integral is the
increment `M_b − M_a` of the Wald exponential, because the Itô-integral process of the
uncut integrand is `M_· − 1` (Wald's martingale property read through
`itoProcessCLM_eq_condExpL2`). The two support clauses are what the caller needs: the
first is the hypothesis of `𝓕_a`-linearity, the second keeps the induction's running
integrand switched off past `b`. -/
theorem constDoleans_band_mem_range (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (a b T : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (σ : ℝ) :
    ∃ φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (∀ᵐ p ∂(trimMeasure_T (μ := μ) T hBmeas), p.1 ≤ a → φ p = 0) ∧
      (∀ᵐ p ∂(trimMeasure_T (μ := μ) T hBmeas), b < p.1 → φ p = 0) ∧
      (fun ω ↦ Real.exp (σ * B b ω - σ ^ 2 * (b : ℝ) / 2)
          - Real.exp (σ * B a ω - σ ^ 2 * (a : ℝ) / 2))
        =ᵐ[μ] ⇑(itoIntegralCLM_T hB T hBmeas φ) := by
  haveI : IsFilteredPreBrownian B (natFiltration hBmeas) μ := hB.isFilteredPreBrownian hBmeas
  obtain ⟨ψ, hψ⟩ := constDoleans_sub_one_mem_range hB hBmeas hBcont T σ
  have haT : a ≤ T := hab.trans hbT
  -- the Itô-integral process of `ψ` is the Wald exponential minus one
  have hproc : ∀ u : ℝ≥0, u ≤ T →
      ⇑(itoProcessCLM hB T u hBmeas ψ)
        =ᵐ[μ] fun ω ↦ Real.exp (σ * B u ω - σ ^ 2 * (u : ℝ) / 2) - 1 := by
    intro u huT
    have hcondExpL2 : ⇑(itoProcessCLM hB T u hBmeas ψ)
        =ᵐ[μ] μ[⇑(itoIntegralCLM_T hB T hBmeas ψ) | natFiltration hBmeas u] := by
      rw [itoProcessCLM_eq_condExpL2 hB T u hBmeas ψ]
      have h := (Lp.memLp (itoIntegralCLM_T hB T hBmeas ψ)).condExpL2_ae_eq_condExp
        (𝕜 := ℝ) ((natFiltration hBmeas).le u)
      rwa [Lp.toLp_coeFn] at h
    refine hcondExpL2.trans ((condExp_congr_ae hψ.symm).trans ?_)
    exact ((IsFilteredPreBrownian.waldExponential_isMartingale σ).sub
      (martingale_const _ _ 1)).2 u T huT
  refine ⟨restrictAfterCLM T a hBmeas ψ - restrictAfterCLM T b hBmeas ψ, ?_, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_sub (restrictAfterCLM T a hBmeas ψ) (restrictAfterCLM T b hBmeas ψ),
      coeFn_restrictAfterCLM T a hBmeas ψ, coeFn_restrictAfterCLM T b hBmeas ψ] with p h1 h2 h3 hpa
    rw [h1, Pi.sub_apply, h2, h3, if_neg (not_lt.mpr hpa), if_neg (not_lt.mpr (hpa.trans hab)),
      sub_self]
  · filter_upwards [Lp.coeFn_sub (restrictAfterCLM T a hBmeas ψ) (restrictAfterCLM T b hBmeas ψ),
      coeFn_restrictAfterCLM T a hBmeas ψ, coeFn_restrictAfterCLM T b hBmeas ψ] with p h1 h2 h3 hpb
    rw [h1, Pi.sub_apply, h2, h3, if_pos (lt_of_le_of_lt hab hpb), if_pos hpb, sub_self]
  · rw [map_sub, itoIntegralCLM_T_restrictAfterCLM hB T a haT hBmeas ψ,
      itoIntegralCLM_T_restrictAfterCLM hB T b hbT hBmeas ψ]
    filter_upwards [Lp.coeFn_sub (itoIntegralCLM_T hB T hBmeas ψ - itoProcessCLM hB T a hBmeas ψ)
        (itoIntegralCLM_T hB T hBmeas ψ - itoProcessCLM hB T b hBmeas ψ),
      Lp.coeFn_sub (itoIntegralCLM_T hB T hBmeas ψ) (itoProcessCLM hB T a hBmeas ψ),
      Lp.coeFn_sub (itoIntegralCLM_T hB T hBmeas ψ) (itoProcessCLM hB T b hBmeas ψ),
      hproc a haT, hproc b hbT] with ω h1 h2 h3 ha hb
    rw [h1, Pi.sub_apply, h2, h3, Pi.sub_apply, Pi.sub_apply, ha, hb]
    ring

/-! ### Scaling by an unbounded `𝓕_a`-measurable factor -/

/-- **`𝓕_a`-linearity for a factor with no moment assumption of its own.** Task 2's
unbounded corollary asks for `Z·φ ∈ L²` of the *integrand*; what a Doléans induction
can supply is `Z·∫φ dB ∈ L²` on the *sample* side. The two are the same requirement,
and this is the transfer: truncating `Z` at level `M` gives genuine integrands
`𝟙_{|Z|≤M}·Z·φ` whose energies are, by the Itô isometry, the sample-side energies
`‖𝟙_{|Z|≤M}·Z·∫φ dB‖ ≤ ‖Z·∫φ dB‖` — uniformly bounded. They converge pointwise to
`Z·φ`, so Fatou bounds its energy too, and Task 2's corollary applies. -/
theorem itoIntegralCLM_T_smul_of_memLp (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[natFiltration hBmeas a] Z)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (hφ : ∀ᵐ p ∂(trimMeasure_T (μ := μ) T hBmeas), p.1 ≤ a → φ p = 0)
    (hZI : MemLp (fun ω ↦ Z ω * itoIntegralCLM_T hB T hBmeas φ ω) 2 μ) :
    ∃ ψ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (⇑ψ =ᵐ[trimMeasure_T (μ := μ) T hBmeas] fun p ↦ Z p.2 * φ p) ∧
      ⇑(itoIntegralCLM_T hB T hBmeas ψ)
        =ᵐ[μ] fun ω ↦ Z ω * itoIntegralCLM_T hB T hBmeas φ ω := by
  -- the truncations `Z_M = 𝟙_{|Z| ≤ M}·Z`, bounded and `𝓕_a`-measurable
  have hAm : ∀ M : ℕ, MeasurableSet[natFiltration hBmeas a] {ω | |Z ω| ≤ (M : ℝ)} := by
    intro M
    rw [show {ω | |Z ω| ≤ (M : ℝ)} = Z ⁻¹' (Set.Icc (-(M : ℝ)) (M : ℝ)) from by
      ext ω; simp [abs_le]]
    exact hZm measurableSet_Icc
  have hZMm : ∀ M : ℕ, Measurable[natFiltration hBmeas a]
      (Set.indicator {ω | |Z ω| ≤ (M : ℝ)} Z) := fun M ↦ hZm.indicator (hAm M)
  have hZMb : ∀ (M : ℕ) (ω : Ω),
      |Set.indicator {ω | |Z ω| ≤ (M : ℝ)} Z ω| ≤ (M : ℝ) := by
    intro M ω
    by_cases hm : ω ∈ {ω | |Z ω| ≤ (M : ℝ)}
    · rw [Set.indicator_of_mem hm]; exact hm
    · simp [Set.indicator_of_notMem hm]
  -- their energies are bounded by the sample-side one, through the Itô isometry
  have hbound : ∀ M : ℕ,
      ‖smulAdapted T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ‖ ≤ ‖hZI.toLp _‖ := by
    intro M
    rw [← itoIntegralCLM_T_norm hB T hBmeas (smulAdapted T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ)]
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [itoIntegralCLM_T_smulAdapted hB T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ hφ,
      hZI.coeFn_toLp] with ω h1 h2
    rw [h1, h2, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    by_cases hm : ω ∈ {ω | |Z ω| ≤ (M : ℝ)}
    · rw [Set.indicator_of_mem hm]
    · rw [Set.indicator_of_notMem hm, abs_zero]; exact abs_nonneg _
  -- Fatou: the limit integrand `Z·φ` inherits the bound
  have hZφ : MemLp (fun p : ℝ≥0 × Ω ↦ Z p.2 * φ p) 2 (trimMeasure_T (μ := μ) T hBmeas) := by
    have hmeas : AEStronglyMeasurable[(natFiltration (mΩ := mΩ) hBmeas).predictable]
        (fun p : ℝ≥0 × Ω ↦ Z p.2 * φ p) (trimMeasure_T (μ := μ) T hBmeas) := by
      refine AEStronglyMeasurable.congr
        ((measurable_afterFactor hBmeas hZm).stronglyMeasurable.aestronglyMeasurable.mul
          (Lp.aestronglyMeasurable φ)) ?_
      filter_upwards [hφ] with p hp
      simp only [Pi.mul_apply, afterFactor]
      split_ifs with hc
      · rfl
      · rw [hp (not_lt.mp hc), mul_zero, mul_zero]
    have hlim : ∀ᵐ p ∂(trimMeasure_T (μ := μ) T hBmeas),
        Tendsto (fun M : ℕ ↦
            (smulAdapted T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ : ℝ≥0 × Ω → ℝ) p)
          atTop (𝓝 (Z p.2 * φ p)) := by
      filter_upwards [ae_all_iff.mpr (fun M : ℕ ↦
        coeFn_smulAdapted_afterFactor T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ), hφ] with p hall hp
      rcases le_or_gt p.1 a with hle | hlt
      · have hz : ∀ M : ℕ,
            (smulAdapted T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ : ℝ≥0 × Ω → ℝ) p = 0 := by
          intro M
          rw [hall M]
          simp only [afterFactor, if_neg (not_lt.mpr hle), zero_mul]
        simp only [hz, hp hle, mul_zero]
        exact tendsto_const_nhds
      · refine Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [eventually_ge_atTop ⌈|Z p.2|⌉₊] with M hM
        have hmem : p.2 ∈ {ω | |Z ω| ≤ (M : ℝ)} :=
          (Nat.le_ceil |Z p.2|).trans (by exact_mod_cast hM : ((⌈|Z p.2|⌉₊ : ℕ) : ℝ) ≤ (M : ℝ))
        rw [hall M]
        simp only [afterFactor, if_pos hlt, Set.indicator_of_mem hmem]
    have hle : atTop.liminf (fun M : ℕ ↦ eLpNorm
        (⇑(smulAdapted T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ)) 2
          (trimMeasure_T (μ := μ) T hBmeas))
        ≤ ENNReal.ofReal ‖hZI.toLp (fun ω ↦ Z ω * itoIntegralCLM_T hB T hBmeas φ ω)‖ := by
      refine liminf_le_of_frequently_le' (Filter.Frequently.of_forall fun M ↦ ?_)
      rw [show eLpNorm (⇑(smulAdapted T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ)) 2
            (trimMeasure_T (μ := μ) T hBmeas)
          = ENNReal.ofReal ‖smulAdapted T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ‖ from by
        rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]]
      exact ENNReal.ofReal_le_ofReal (hbound M)
    exact ⟨hmeas, lt_of_le_of_lt ((MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun M : ℕ ↦ Lp.aestronglyMeasurable
        (smulAdapted T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ)) _ hlim).trans hle)
      ENNReal.ofReal_lt_top⟩
  exact ⟨hZφ.toLp _, hZφ.coeFn_toLp,
    itoIntegralCLM_T_smulAdapted_of_memLp hB T a hBmeas Z hZm φ hφ hZφ⟩

omit [IsProbabilityMeasure μ] in
/-- A lognormal increment has a second moment: `exp(c(B_v − B_u)) ∈ L²(μ)`, by the
`xy ≤ ½(x² + y²)` split into two Brownian marginals. -/
private lemma memLp_exp_incr (hBmeas : ∀ t, Measurable (B t)) (u v : ℝ≥0) (c : ℝ) :
    MemLp (fun ω ↦ Real.exp (c * (B v ω - B u ω))) 2 μ := by
  have hmeas : AEStronglyMeasurable (fun ω ↦ Real.exp (c * (B v ω - B u ω))) μ :=
    (Real.measurable_exp.comp (((hBmeas v).sub (hBmeas u)).const_mul c)).aestronglyMeasurable
  have key : ∀ ω : Ω, Real.exp (c * (B v ω - B u ω))
      ≤ 1 / 2 * (Real.exp (2 * c * B v ω) + Real.exp (-(2 * c) * B u ω)) := by
    intro ω
    have h1 : Real.exp (c * (B v ω - B u ω))
        = Real.exp (c * B v ω) * Real.exp (-(c * B u ω)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (2 * c * B v ω) = Real.exp (c * B v ω) ^ 2 := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    have h3 : Real.exp (-(2 * c) * B u ω) = Real.exp (-(c * B u ω)) ^ 2 := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [h1, h2, h3]
    nlinarith [sq_nonneg (Real.exp (c * B v ω) - Real.exp (-(c * B u ω)))]
  refine MemLp.mono (((memLp_exp_mul_eval hB v (2 * c)).add
    (memLp_exp_mul_eval hB u (-(2 * c)))).const_mul (1 / 2)) hmeas (ae_of_all _ fun ω ↦ ?_)
  have hpos : (0 : ℝ) ≤ 1 / 2 * (Real.exp (2 * c * B v ω) + Real.exp (-(2 * c) * B u ω)) := by
    positivity
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_nonneg hpos]
  exact key ω

/-- **Shifted constant case.** The Doléans exponential of `σ·𝟙_{(a,T]}` — the band
integrand of `constDoleans_band_mem_range` renormalised by the `𝓕_a`-measurable
factor `1/M_a = exp(−σB_a + σ²a/2)`, which is exactly what turns the increment
`M_T − M_a` into `M_T/M_a − 1`. -/
theorem constDoleans_shift_sub_one_mem_range (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) (a T : ℝ≥0) (haT : a ≤ T) (σ : ℝ) :
    ∃ φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (∀ᵐ p ∂(trimMeasure_T (μ := μ) T hBmeas), p.1 ≤ a → φ p = 0) ∧
      (fun ω ↦ Real.exp (σ * (B T ω - B a ω) - σ ^ 2 * ((T : ℝ) - (a : ℝ)) / 2) - 1)
        =ᵐ[μ] ⇑(itoIntegralCLM_T hB T hBmeas φ) := by
  obtain ⟨χ, hχ0, -, hχval⟩ :=
    constDoleans_band_mem_range hB hBmeas hBcont a T T haT le_rfl σ
  have halg : ∀ ω : Ω, Real.exp (-(σ * B a ω) + σ ^ 2 * (a : ℝ) / 2) *
      (Real.exp (σ * B T ω - σ ^ 2 * (T : ℝ) / 2) - Real.exp (σ * B a ω - σ ^ 2 * (a : ℝ) / 2))
      = Real.exp (σ * (B T ω - B a ω) - σ ^ 2 * ((T : ℝ) - (a : ℝ)) / 2) - 1 := by
    intro ω
    rw [mul_sub, ← Real.exp_add, ← Real.exp_add,
      show -(σ * B a ω) + σ ^ 2 * (a : ℝ) / 2 + (σ * B a ω - σ ^ 2 * (a : ℝ) / 2) = 0 by ring,
      Real.exp_zero,
      show -(σ * B a ω) + σ ^ 2 * (a : ℝ) / 2 + (σ * B T ω - σ ^ 2 * (T : ℝ) / 2)
        = σ * (B T ω - B a ω) - σ ^ 2 * ((T : ℝ) - (a : ℝ)) / 2 by ring]
  have hZm : Measurable[natFiltration hBmeas a]
      (fun ω ↦ Real.exp (-(σ * B a ω) + σ ^ 2 * (a : ℝ) / 2)) := by
    have hBa : Measurable[natFiltration hBmeas a] (B a) := by
      have hle : MeasurableSpace.comap (B a) (inferInstance : MeasurableSpace ℝ)
          ≤ natFiltration hBmeas a := le_iSup₂_of_le a le_rfl le_rfl
      exact (measurable_iff_comap_le.mpr le_rfl).mono hle le_rfl
    exact Real.measurable_exp.comp (((hBa.const_mul σ).neg).add_const _)
  have hZI : MemLp (fun ω ↦ Real.exp (-(σ * B a ω) + σ ^ 2 * (a : ℝ) / 2) *
      itoIntegralCLM_T hB T hBmeas χ ω) 2 μ := by
    have hsrc : MemLp (fun ω ↦ Real.exp (σ * (B T ω - B a ω)
        - σ ^ 2 * ((T : ℝ) - (a : ℝ)) / 2) - 1) 2 μ := by
      refine (memLp_congr_ae ?_).mp
        (((memLp_exp_incr hB hBmeas a T σ).const_mul
          (Real.exp (-(σ ^ 2 * ((T : ℝ) - (a : ℝ)) / 2)))).sub (memLp_const (1 : ℝ)))
      filter_upwards with ω
      simp only [Pi.sub_apply]
      rw [← Real.exp_add, show -(σ ^ 2 * ((T : ℝ) - (a : ℝ)) / 2) + σ * (B T ω - B a ω)
        = σ * (B T ω - B a ω) - σ ^ 2 * ((T : ℝ) - (a : ℝ)) / 2 from by ring]
    refine (memLp_congr_ae ?_).mp hsrc
    filter_upwards [hχval] with ω hω
    rw [← hω]
    exact (halg ω).symm
  obtain ⟨ψ, hψcoe, hψval⟩ := itoIntegralCLM_T_smul_of_memLp hB T a hBmeas _ hZm χ hχ0 hZI
  refine ⟨ψ, ?_, ?_⟩
  · filter_upwards [hψcoe, hχ0] with p hp h0 hpa
    rw [hp, h0 hpa, mul_zero]
  · filter_upwards [hψval, hχval] with ω h1 h2
    rw [h1, ← h2, halg ω]

/-! ### The step Doléans exponential -/

/-- The Doléans exponential of a deterministic step integrand
`h = Σ hₖ·1_{(sₖ, sₖ₊₁]}` over a monotone partition, evaluated at the horizon.
The arithmetic shape of each cell matches `SimpleDoleansExponential.cellExp`
(`c·ΔX − c²·Δt/2`). `B` is explicit: Task 4 instantiates it at a `B` that the
statement of the orthogonality hypothesis does not otherwise pin down. -/
noncomputable def stepDoleansExp (B : ℝ≥0 → Ω → ℝ) (s : ℕ → ℝ≥0) (h : ℕ → ℝ)
    (N : ℕ) (ω : Ω) : ℝ :=
  ∏ k ∈ Finset.range N,
    Real.exp (h k * (B (s (k + 1)) ω - B (s k) ω)
      - h k ^ 2 * ((s (k + 1) : ℝ) - (s k : ℝ)) / 2)

/-- Every moment of a step Doléans exponential exists — the induction's integrability
feed. Stated for the exponential of the *increment sum* with an arbitrary scale `c`,
which is what makes the induction step go through: the square of the `(n+1)`-fold
exponential is the `n`-fold one at scale `2c` times a single lognormal factor, and
Cauchy–Schwarz (`MemLp.integrable_mul`) multiplies them. -/
private lemma memLp_exp_stepSum (hBmeas : ∀ t, Measurable (B t)) (s : ℕ → ℝ≥0) (h : ℕ → ℝ) :
    ∀ (m : ℕ) (c : ℝ), MemLp (fun ω ↦ Real.exp (c *
      ∑ k ∈ Finset.range m, h k * (B (s (k + 1)) ω - B (s k) ω))) 2 μ := by
  have hmeas : ∀ (m : ℕ) (c : ℝ), AEStronglyMeasurable (fun ω ↦ Real.exp (c *
      ∑ k ∈ Finset.range m, h k * (B (s (k + 1)) ω - B (s k) ω))) μ := fun m c ↦
    (Real.measurable_exp.comp ((Finset.measurable_sum _ fun k _ ↦
      ((hBmeas (s (k + 1))).sub (hBmeas (s k))).const_mul (h k)).const_mul c)).aestronglyMeasurable
  intro m
  induction m with
  | zero => intro c; simpa using memLp_const (1 : ℝ)
  | succ n ih =>
    intro c
    rw [memLp_two_iff_integrable_sq (hmeas (n + 1) c)]
    have hsq : (fun ω ↦ (Real.exp (c *
          ∑ k ∈ Finset.range (n + 1), h k * (B (s (k + 1)) ω - B (s k) ω))) ^ 2)
        = fun ω ↦ Real.exp (2 * c * ∑ k ∈ Finset.range n, h k * (B (s (k + 1)) ω - B (s k) ω))
            * Real.exp (2 * c * h n * (B (s (n + 1)) ω - B (s n) ω)) := by
      funext ω
      rw [Finset.sum_range_succ, sq, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [hsq]
    exact MemLp.integrable_mul (ih (2 * c))
      (memLp_exp_incr hB hBmeas (s n) (s (n + 1)) (2 * c * h n))

private lemma memLp_stepDoleansExp (hBmeas : ∀ t, Measurable (B t)) (s : ℕ → ℝ≥0) (h : ℕ → ℝ)
    (m : ℕ) : MemLp (stepDoleansExp B s h m) 2 μ := by
  have hrw : stepDoleansExp B s h m = fun ω ↦
      Real.exp (-∑ k ∈ Finset.range m, h k ^ 2 * ((s (k + 1) : ℝ) - (s k : ℝ)) / 2) *
        Real.exp (1 * ∑ k ∈ Finset.range m, h k * (B (s (k + 1)) ω - B (s k) ω)) := by
    funext ω
    simp only [stepDoleansExp]
    rw [← Real.exp_sum, Finset.sum_sub_distrib, one_mul, ← Real.exp_add]
    congr 1
    ring
  rw [hrw]
  exact (memLp_exp_stepSum hB hBmeas s h m 1).const_mul _

omit hB in
/-- The step Doléans exponential at stage `m` is `𝓕_{s m}`-measurable: every increment
it multiplies has both endpoints at or before `s m`. -/
private lemma measurable_stepDoleansExp (hBmeas : ∀ t, Measurable (B t)) {s : ℕ → ℝ≥0}
    (hs : Monotone s) (h : ℕ → ℝ) (m : ℕ) :
    Measurable[natFiltration hBmeas (s m)] (stepDoleansExp B s h m) := by
  have hBm : ∀ {v : ℝ≥0}, v ≤ s m → Measurable[natFiltration hBmeas (s m)] (B v) := by
    intro v hv
    have hle : MeasurableSpace.comap (B v) (inferInstance : MeasurableSpace ℝ)
        ≤ natFiltration hBmeas (s m) := le_iSup₂_of_le v hv le_rfl
    exact (measurable_iff_comap_le.mpr le_rfl).mono hle le_rfl
  refine Finset.measurable_prod _ fun k hk ↦ ?_
  have hk1 : k + 1 ≤ m := Finset.mem_range.mp hk
  exact Real.measurable_exp.comp
    ((((hBm (hs hk1)).sub (hBm (hs (Nat.le_of_succ_le hk1)))).const_mul (h k)).sub
      measurable_const)

/-- **The induction.** `Dₙ₊₁ − Dₙ = Eₙ·(M_{sₙ₊₁} − M_{sₙ})` with `Eₙ = Dₙ/M_{sₙ}`
`𝓕_{sₙ}`-measurable: the band integrand of `constDoleans_band_mem_range` supplies the
increment, `itoIntegralCLM_T_smul_of_memLp` pulls `Eₙ` inside, and the running
integrand stays switched off past `sₙ₊₁` so the next step's `𝓕`-linearity applies. -/
private theorem stepDoleans_aux (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) (T : ℝ≥0) {s : ℕ → ℝ≥0} (hs : Monotone s)
    (h : ℕ → ℝ) : ∀ n : ℕ, s n ≤ T →
      ∃ φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
        (∀ᵐ p ∂(trimMeasure_T (μ := μ) T hBmeas), s n < p.1 → φ p = 0) ∧
        (fun ω ↦ stepDoleansExp B s h n ω - 1) =ᵐ[μ] ⇑(itoIntegralCLM_T hB T hBmeas φ) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨0, ?_, ?_⟩
    · filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2)
        (μ := trimMeasure_T (μ := μ) T hBmeas)] with p hp _
      simpa using hp
    · have h0 : (fun ω : Ω ↦ stepDoleansExp B s h 0 ω - 1) = fun _ ↦ (0 : ℝ) := by
        funext ω
        simp [stepDoleansExp]
      rw [map_zero, h0]
      exact (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)).symm
  | succ n ih =>
    intro hsn1
    have hstep : s n ≤ s (n + 1) := hs (Nat.le_succ n)
    obtain ⟨φ, hφsupp, hφval⟩ := ih (hstep.trans hsn1)
    obtain ⟨χ, hχ0, hχ1, hχval⟩ :=
      constDoleans_band_mem_range hB hBmeas hBcont (s n) (s (n + 1)) T hstep hsn1 (h n)
    have halg : ∀ ω : Ω, (stepDoleansExp B s h n ω *
          Real.exp (-(h n * B (s n) ω) + h n ^ 2 * (s n : ℝ) / 2)) *
        (Real.exp (h n * B (s (n + 1)) ω - h n ^ 2 * ((s (n + 1) : ℝ)) / 2)
          - Real.exp (h n * B (s n) ω - h n ^ 2 * (s n : ℝ) / 2))
        = stepDoleansExp B s h (n + 1) ω - stepDoleansExp B s h n ω := by
      intro ω
      have hprod : stepDoleansExp B s h (n + 1) ω
          = stepDoleansExp B s h n ω * Real.exp (h n * (B (s (n + 1)) ω - B (s n) ω)
              - h n ^ 2 * ((s (n + 1) : ℝ) - (s n : ℝ)) / 2) := by
        simp only [stepDoleansExp, Finset.prod_range_succ]
      have e1 : Real.exp (-(h n * B (s n) ω) + h n ^ 2 * (s n : ℝ) / 2) *
          Real.exp (h n * B (s (n + 1)) ω - h n ^ 2 * ((s (n + 1) : ℝ)) / 2)
          = Real.exp (h n * (B (s (n + 1)) ω - B (s n) ω)
              - h n ^ 2 * ((s (n + 1) : ℝ) - (s n : ℝ)) / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have e2 : Real.exp (-(h n * B (s n) ω) + h n ^ 2 * (s n : ℝ) / 2) *
          Real.exp (h n * B (s n) ω - h n ^ 2 * (s n : ℝ) / 2) = 1 := by
        rw [← Real.exp_add,
          show -(h n * B (s n) ω) + h n ^ 2 * (s n : ℝ) / 2
            + (h n * B (s n) ω - h n ^ 2 * (s n : ℝ) / 2) = 0 by ring, Real.exp_zero]
      rw [hprod, mul_assoc, mul_sub, e1, e2]
      ring
    have hZm : Measurable[natFiltration hBmeas (s n)] (fun ω ↦ stepDoleansExp B s h n ω *
        Real.exp (-(h n * B (s n) ω) + h n ^ 2 * (s n : ℝ) / 2)) := by
      have hBsn : Measurable[natFiltration hBmeas (s n)] (B (s n)) := by
        have hle : MeasurableSpace.comap (B (s n)) (inferInstance : MeasurableSpace ℝ)
            ≤ natFiltration hBmeas (s n) := le_iSup₂_of_le (s n) le_rfl le_rfl
        exact (measurable_iff_comap_le.mpr le_rfl).mono hle le_rfl
      exact (measurable_stepDoleansExp hBmeas hs h n).mul
        (Real.measurable_exp.comp (((hBsn.const_mul (h n)).neg).add_const _))
    have hZI : MemLp (fun ω ↦ (stepDoleansExp B s h n ω *
        Real.exp (-(h n * B (s n) ω) + h n ^ 2 * (s n : ℝ) / 2)) *
        itoIntegralCLM_T hB T hBmeas χ ω) 2 μ := by
      refine (memLp_congr_ae ?_).mp ((memLp_stepDoleansExp hB hBmeas s h (n + 1)).sub
        (memLp_stepDoleansExp hB hBmeas s h n))
      filter_upwards [hχval] with ω hω
      rw [Pi.sub_apply, ← hω, halg ω]
    obtain ⟨ψ, hψcoe, hψval⟩ := itoIntegralCLM_T_smul_of_memLp hB T (s n) hBmeas _ hZm χ hχ0 hZI
    refine ⟨φ + ψ, ?_, ?_⟩
    · filter_upwards [Lp.coeFn_add φ ψ, hφsupp, hψcoe, hχ1] with p hadd hf hg hc hpb
      rw [hadd, Pi.add_apply, hf (lt_of_le_of_lt hstep hpb), hg, hc hpb, mul_zero, add_zero]
    · rw [map_add]
      filter_upwards [Lp.coeFn_add (itoIntegralCLM_T hB T hBmeas φ)
          (itoIntegralCLM_T hB T hBmeas ψ), hφval, hψval, hχval] with ω hadd hf hg hc
      rw [hadd, Pi.add_apply, ← hf, hg, ← hc, halg ω]
      ring

/-- **The step-integrand Doléans exponential is an Itô integral.** For a monotone
partition `0 = s₀ ≤ … ≤ s_N = T` and deterministic heights `h`, the Doléans
exponential `∏ₖ exp(hₖΔBₖ − ½hₖ²Δsₖ)`, minus one, lies in the range of `∫₀ᵀ · dB`. -/
theorem stepDoleans_sub_one_mem_range (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) (T : ℝ≥0)
    (s : ℕ → ℝ≥0) (hs : Monotone s) (h : ℕ → ℝ) (N : ℕ)
    (hs0 : s 0 = 0) (hsN : s N = T) :
    ∃ φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (fun ω ↦ stepDoleansExp B s h N ω - 1)
        =ᵐ[μ] ⇑(itoIntegralCLM_T hB T hBmeas φ) :=
  let ⟨φ, _, hval⟩ := stepDoleans_aux hB hBmeas hBcont T hs h N hsN.le
  ⟨φ, hval⟩

end MathFin
