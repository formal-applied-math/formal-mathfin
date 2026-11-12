/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Brownian.MartingaleRepresentation
public import MathFin.Probability.Brownian.Girsanov.GirsanovPredictableTheta
public import MathFin.Probability.Brownian.Ito.ItoIntegralLocality

/-!
# Uniqueness of the martingale measure on the Brownian filtration

Let `X` be a `μ`-martingale of the Brownian filtration whose increment is an Itô integral,
`X_T − X_0 = ∫₀ᵀ ψ dB`, with an integrand `ψ` that never vanishes (the discounted geometric
Brownian motion: `ψ = σX`). A second measure `Q = D·μ` with a square-integrable density that
makes `X` a martingale agrees with `μ` on `𝓕_T`. This is the uniqueness half of market
completeness, in the direction that needs the density in `L²(μ)`.

## The argument

By martingale representation the conditional density `F = 𝔼_μ[D | 𝓕_T]` is `1 + ∫₀ᵀ φ dB`.
The martingale property of `X` under `Q` says `𝔼_μ[F·1_A·(X_u − X_s)] = 0` for `A ∈ 𝓕_s`,
`s ≤ u ≤ T`, and the martingale property under `μ` gives `𝔼_μ[1_A·(X_u − X_s)] = 0`. Hence
`𝔼_μ[(∫φ dB)·1_A·(X_u − X_s)] = 0`. The increment `1_A·(X_u − X_s)` is the Itô integral of the
predictable rectangle integrand `1_{(s,u]×A}·ψ` (`exists_rectIntegrand`, by the locality of the
integral in the sample space and in time), so by the isometry `∫ φψ·1_R d(trim) = 0` for every
basic predictable rectangle `R`. The π-λ theorem
(`ItoIntegralCLM.setIntegral_eq_zero_of_orthogonal_pred`) extends this to every predictable set,
so `φψ = 0`, hence `φ = 0` since `ψ ≠ 0`, and `F = 1`.

## Main results

* `MathFin.exists_rectIntegrand`: the Itô integral of `1_{(s,u]×A}·ψ` is `1_A (X_u − X_s)`.
* `MathFin.ae_mul_eq_zero_of_orthogonal_increments`: an integrand `φ` whose integral is
  orthogonal to every increment `1_A (X_u − X_s)` satisfies `φψ = 0`.
* `MathFin.trim_eq_of_martingale_withDensity`: a probability measure with an `L²(μ)` density that
  makes `X` a martingale equals `μ` on `𝓕_T`.

## References

* [I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991], 3.4
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], 5.4

## Tags

martingale measure, uniqueness of the risk-neutral measure, martingale representation theorem,
Itô integral, market completeness, MSC 60H05, MSC 60G44, MSC 91G20
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter Topology
open ItoIntegralCLM ItoIntegralL2 ItoIntegralProcess ItoIntegralProcessGeneral
open ItoIntegralCovariation
open scoped NNReal ENNReal InnerProductSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
  {X : ℝ≥0 → Ω → ℝ}

/-- **The integral process of a martingale increment is the martingale.** If the terminal integral
of `ψ` is `X_T − X_0` for a martingale `X` of the Brownian filtration, the integral process is
`(ψ●B)_t = X_t − X_0` for `t ≤ T`. -/
lemma itoProcessCLM_ae_eq_of_martingale (T : ℝ≥0) (hX : Martingale X (natFiltration hBmeas) μ)
    (ψ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hψ : (fun ω ↦ X T ω - X 0 ω) =ᵐ[μ] itoIntegralCLM hB T hBmeas ψ) {t : ℝ≥0} (ht : t ≤ T) :
    itoProcessCLM hB T t hBmeas ψ =ᵐ[μ] fun ω ↦ X t ω - X 0 ω := by
  have h := (Lp.memLp (itoIntegralCLM hB T hBmeas ψ)).condExpL2_ae_eq_condExp
    (𝕜 := ℝ) ((natFiltration hBmeas).le t)
  rw [Lp.toLp_coeFn] at h
  rw [itoProcessCLM_eq_condExpL2 hB T t hBmeas ψ]
  refine h.trans ((condExp_congr_ae hψ.symm).trans ?_)
  refine (condExp_sub (hX.integrable T) (hX.integrable 0) _).trans ?_
  rw [condExp_of_stronglyMeasurable ((natFiltration hBmeas).le t)
    ((hX.stronglyAdapted 0).mono ((natFiltration hBmeas).mono zero_le)) (hX.integrable 0)]
  filter_upwards [hX.condExp_ae_eq ht] with ω hω
  rw [Pi.sub_apply, hω]

/-- **The rectangle integrand.** For a martingale `X` of the Brownian filtration with
`X_T − X_0 = ∫₀ᵀ ψ dB`, `s ≤ u ≤ T` and `A ∈ 𝓕_s`, the predictable integrand
`1_{(s,u]×A}·ψ` has Itô integral `1_A (X_u − X_s)`. The integrand is the restriction of `ψ` to
`(s,u]` (`restrictAfterCLM` at `s` minus at `u`, whose integrals are `∫ψ − (ψ●B)_s` and
`∫ψ − (ψ●B)_u`) scaled by the `𝓕_s`-measurable `1_A` (`itoIntegralCLM_smulAdapted`). -/
theorem exists_rectIntegrand (T : ℝ≥0) (hX : Martingale X (natFiltration hBmeas) μ)
    (ψ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hψ : (fun ω ↦ X T ω - X 0 ω) =ᵐ[μ] itoIntegralCLM hB T hBmeas ψ) {s u : ℝ≥0} (hsu : s ≤ u)
    (huT : u ≤ T) {A : Set Ω} (hA : MeasurableSet[natFiltration hBmeas s] A) :
    ∃ χ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas),
      ⇑χ =ᵐ[trimMeasure (μ := μ) T hBmeas] (Set.Ioc s u ×ˢ A).indicator ⇑ψ ∧
      ⇑(itoIntegralCLM hB T hBmeas χ) =ᵐ[μ] A.indicator fun ω ↦ X u ω - X s ω := by
  set ρ := restrictAfterCLM T s hBmeas ψ - restrictAfterCLM T u hBmeas ψ with hρ
  have hρ0 : ∀ᵐ p ∂(trimMeasure (μ := μ) T hBmeas), p.1 ≤ s → ρ p = 0 := by
    filter_upwards [Lp.coeFn_sub (restrictAfterCLM T s hBmeas ψ) (restrictAfterCLM T u hBmeas ψ),
      coeFn_restrictAfterCLM T s hBmeas ψ, coeFn_restrictAfterCLM T u hBmeas ψ]
      with p h1 h2 h3 hp
    rw [hρ, h1, Pi.sub_apply, h2, h3]
    simp [not_lt.2 hp, not_lt.2 (hp.trans hsu)]
  have hIρ : itoIntegralCLM hB T hBmeas ρ
      = itoProcessCLM hB T u hBmeas ψ - itoProcessCLM hB T s hBmeas ψ := by
    rw [hρ, map_sub, itoIntegralCLM_restrictAfterCLM hB T s (hsu.trans huT) hBmeas ψ,
      itoIntegralCLM_restrictAfterCLM hB T u huT hBmeas ψ]
    abel
  have hZm : Measurable[natFiltration hBmeas s] (A.indicator fun _ ↦ (1 : ℝ)) :=
    measurable_const.indicator hA
  have hZb : ∀ ω, |A.indicator (fun _ ↦ (1 : ℝ)) ω| ≤ 1 := fun ω ↦ by
    by_cases h : ω ∈ A <;> simp [h]
  refine ⟨smulAdapted T s hBmeas _ hZm 1 hZb ρ, ?_, ?_⟩
  · filter_upwards [coeFn_smulAdapted T s hBmeas _ hZm 1 hZb ρ hρ0,
      Lp.coeFn_sub (restrictAfterCLM T s hBmeas ψ) (restrictAfterCLM T u hBmeas ψ),
      coeFn_restrictAfterCLM T s hBmeas ψ, coeFn_restrictAfterCLM T u hBmeas ψ]
      with p h1 h2 h3 h4
    rw [h1, hρ, h2, Pi.sub_apply, h3, h4]
    by_cases hA' : p.2 ∈ A <;> by_cases hs : s < p.1 <;> by_cases hu : u < p.1 <;>
      first
        | exact absurd (hsu.trans_lt hu) hs
        | simp [Set.indicator, hA', hs, hu, Set.mem_prod, Set.mem_Ioc]
  · have hmul := itoIntegralCLM_smulAdapted hB T s hBmeas _ hZm 1 hZb ρ hρ0
    filter_upwards [hmul, itoProcessCLM_ae_eq_of_martingale hB hBmeas T hX ψ hψ huT,
      itoProcessCLM_ae_eq_of_martingale hB hBmeas T hX ψ hψ (hsu.trans huT),
      Lp.coeFn_sub (itoProcessCLM hB T u hBmeas ψ) (itoProcessCLM hB T s hBmeas ψ)]
      with ω h1 h2 h3 h4
    rw [h1, hIρ, h4, Pi.sub_apply, h2, h3]
    by_cases hω : ω ∈ A <;> simp [Set.indicator, hω]

/-- **The Itô integrand orthogonal to a martingale's increments.** Let `X` be a martingale of the
Brownian filtration with `X_T − X_0 = ∫₀ᵀ ψ dB`. If `∫₀ᵀ φ dB` is orthogonal to every increment
`1_A (X_u − X_s)` (`s ≤ u ≤ T`, `A ∈ 𝓕_s`), then `φ·ψ = 0` almost everywhere for the
predictable trim: the pairings `⟪φ, 1_R ψ⟫` over the basic predictable rectangles `R = (s,u]×A`
vanish by the isometry (`exists_rectIntegrand`), and the π-λ theorem passes to every predictable
set. -/
theorem ae_mul_eq_zero_of_orthogonal_increments (T : ℝ≥0)
    (hX : Martingale X (natFiltration hBmeas) μ) (ψ φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hψ : (fun ω ↦ X T ω - X 0 ω) =ᵐ[μ] itoIntegralCLM hB T hBmeas ψ)
    (hφ : ∀ {s u : ℝ≥0}, s ≤ u → u ≤ T → ∀ {A : Set Ω},
      MeasurableSet[natFiltration hBmeas s] A →
        ∫ ω in A, itoIntegralCLM hB T hBmeas φ ω * (X u ω - X s ω) ∂μ = 0) :
    (fun z ↦ φ z * ψ z) =ᵐ[trimMeasure (μ := μ) T hBmeas] 0 := by
  set 𝓕 := natFiltration hBmeas
  let : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  have hh_int : Integrable (fun z ↦ φ z * ψ z) (trimMeasure (μ := μ) T hBmeas) :=
    (Lp.memLp φ).integrable_mul (Lp.memLp ψ)
  have hrect : ∀ {s u : ℝ≥0}, s ≤ u → u ≤ T → ∀ {A : Set Ω}, MeasurableSet[𝓕 s] A →
      ∫ z in Set.Ioc s u ×ˢ A, φ z * ψ z ∂(trimMeasure (μ := μ) T hBmeas) = 0 := by
    intro s u hsu huT A hA
    obtain ⟨χ, hχ, hIχ⟩ := exists_rectIntegrand hB hBmeas T hX ψ hψ hsu huT hA
    have hRpred : MeasurableSet[𝓕.predictable] (Set.Ioc s u ×ˢ A) :=
      MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓕) s u hA
    have hAm : MeasurableSet A := 𝓕.le s A hA
    calc ∫ z in Set.Ioc s u ×ˢ A, φ z * ψ z ∂(trimMeasure (μ := μ) T hBmeas)
        = ∫ z, φ z * χ z ∂(trimMeasure (μ := μ) T hBmeas) := by
          rw [← integral_indicator hRpred]
          refine integral_congr_ae ?_
          filter_upwards [hχ] with z hz
          rw [hz]
          by_cases hzR : z ∈ Set.Ioc s u ×ˢ A <;> simp [Set.indicator, hzR]
      _ = ⟪φ, χ⟫_ℝ := (inner_eq_integral_mul φ χ).symm
      _ = ⟪itoIntegralCLM hB T hBmeas φ, itoIntegralCLM hB T hBmeas χ⟫_ℝ :=
          (inner_itoIntegralCLM hB T hBmeas φ χ).symm
      _ = ∫ ω, itoIntegralCLM hB T hBmeas φ ω * itoIntegralCLM hB T hBmeas χ ω ∂μ :=
          inner_eq_integral_mul _ _
      _ = ∫ ω in A, itoIntegralCLM hB T hBmeas φ ω * (X u ω - X s ω) ∂μ := by
          rw [← integral_indicator hAm]
          refine integral_congr_ae ?_
          filter_upwards [hIχ] with ω hω
          rw [hω]
          by_cases hωA : ω ∈ A <;> simp [Set.indicator, hωA]
      _ = 0 := hφ hsu huT hA
  have h_orth : ∀ R ∈ predictableRect (mΩ := mΩ) hBmeas,
      ∫ z in R, φ z * ψ z ∂(trimMeasure (μ := μ) T hBmeas) = 0 := by
    intro R hR
    rcases hR with ⟨F₀, hF₀, rfl⟩ | ⟨a, b, _hab, F, hF, rfl⟩
    · have h_R_pred : MeasurableSet[𝓕.predictable] ({(⊥ : ℝ≥0)} ×ˢ F₀) :=
        MeasureTheory.measurableSet_predictable_singleton_bot_prod (𝓕 := 𝓕) hF₀
      rw [setIntegral_eq_setIntegral_inter_supp hBmeas _ _ h_R_pred]
      have h_empty : ({(⊥ : ℝ≥0)} ×ˢ F₀) ∩ Set.Ioc 0 T ×ˢ (Set.univ : Set Ω) = ∅ := by
        rw [Set.prod_inter_prod,
          show ({(⊥ : ℝ≥0)} ∩ Set.Ioc 0 T : Set ℝ≥0) = ∅ by ext x; simp, Set.empty_prod]
      rw [h_empty, setIntegral_empty]
    · have h_R_pred : MeasurableSet[𝓕.predictable] (Set.Ioc a b ×ˢ F) :=
        MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := 𝓕) a b hF
      rw [setIntegral_eq_setIntegral_inter_supp hBmeas _ _ h_R_pred]
      have h_inter : (Set.Ioc a b ×ˢ F) ∩ (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω))
          = Set.Ioc a (min b T) ×ˢ F := by
        ext ⟨t, ω⟩
        simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true,
          le_min_iff]
        constructor
        · rintro ⟨⟨⟨h1, h2⟩, hω⟩, ⟨_, h4⟩⟩
          exact ⟨⟨h1, h2, h4⟩, hω⟩
        · rintro ⟨⟨h1, h2, h4⟩, hω⟩
          exact ⟨⟨⟨h1, h2⟩, hω⟩, ⟨(bot_le : (0 : ℝ≥0) ≤ a).trans_lt h1, h4⟩⟩
      rw [h_inter]
      by_cases hab' : a ≤ min b T
      · exact hrect hab' (min_le_right _ _) hF
      · push Not at hab'
        rw [Set.Ioc_eq_empty (not_lt.mpr hab'.le), Set.empty_prod, setIntegral_empty]
  exact hh_int.ae_eq_zero_of_forall_setIntegral_eq_zero fun s hs _ ↦
    setIntegral_eq_zero_of_orthogonal_pred T hBmeas hh_int h_orth s hs

/-- **The martingale and its Itô integrand are square-integrable.** Given `X 0 ∈ L²`, every
`X t`, `t ≤ T`, is square-integrable: `X t − X 0` is the integral process. -/
lemma memLp_of_martingale_increment (T : ℝ≥0) (hX : Martingale X (natFiltration hBmeas) μ)
    (ψ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hψ : (fun ω ↦ X T ω - X 0 ω) =ᵐ[μ] itoIntegralCLM hB T hBmeas ψ) (hX0 : MemLp (X 0) 2 μ)
    {t : ℝ≥0} (ht : t ≤ T) : MemLp (X t) 2 μ := by
  have h := ((Lp.memLp (itoProcessCLM hB T t hBmeas ψ)).ae_eq
    (itoProcessCLM_ae_eq_of_martingale hB hBmeas T hX ψ hψ ht)).add hX0
  exact h.ae_eq (.of_forall fun ω ↦ sub_add_cancel (X t ω) (X 0 ω))

/-- **Uniqueness of the martingale measure with a square-integrable density.** Let `X` be a
martingale of the Brownian filtration with `X_T − X_0 = ∫₀ᵀ ψ dB`, `ψ ≠ 0` almost everywhere,
and `X_0` square-integrable. A probability measure `Q = D·μ` with `D ∈ L²(μ)` nonnegative under
which `X`, frozen at `T`, is a martingale of the Brownian filtration agrees with `μ` on `𝓕_T`.
The conditional density `𝔼_μ[D | 𝓕_T]` is `1 + ∫₀ᵀ φ dB` (martingale representation), and the
martingale property under `Q` and under `μ` makes `∫₀ᵀ φ dB` orthogonal to every increment
`1_A (X_u − X_s)`, so `φψ = 0` (`ae_mul_eq_zero_of_orthogonal_increments`), `φ = 0`. -/
theorem trim_eq_of_martingale_withDensity (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω)
    (T : ℝ≥0) (hX : Martingale X (natFiltration hBmeas) μ)
    (ψ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hψ : (fun ω ↦ X T ω - X 0 ω) =ᵐ[μ] itoIntegralCLM hB T hBmeas ψ)
    (hψ0 : ∀ᵐ z ∂(trimMeasure (μ := μ) T hBmeas), ψ z ≠ 0) (hX0 : MemLp (X 0) 2 μ)
    (D : Lp ℝ 2 μ) (hD0 : ∀ᵐ ω ∂μ, 0 ≤ D ω) {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hQD : Q = μ.withDensity fun ω ↦ ENNReal.ofReal (D ω))
    (hQ : Martingale (fun t ↦ X (min t T)) (natFiltration hBmeas) Q) :
    Q.trim ((natFiltration hBmeas).le T) = μ.trim ((natFiltration hBmeas).le T) := by
  set 𝓕 := natFiltration hBmeas
  have hD1 : Integrable D μ := (Lp.memLp D).integrable one_le_two
  have hDp : ∀ ω, 0 ≤ max (D ω) 0 := fun ω ↦ le_max_right _ _
  have hDpD : (fun ω ↦ max (D ω) 0) =ᵐ[μ] D := by
    filter_upwards [hD0] with ω hω using max_eq_left hω
  have hQp : Q = μ.withDensity fun ω ↦ ENNReal.ofReal (max (D ω) 0) := by
    rw [hQD]
    congr 1
    funext ω
    rw [ENNReal.ofReal_max, ENNReal.ofReal_zero]
    simp
  have hD : ∫ ω, D ω ∂μ = 1 := by
    have h1 : ENNReal.ofReal (∫ ω, D ω ∂μ) = 1 := by
      rw [ofReal_integral_eq_lintegral_ofReal hD1 hD0, ← setLIntegral_univ, ← withDensity_apply _
        MeasurableSet.univ, ← hQD, measure_univ]
    exact (ENNReal.ofReal_eq_one.1 h1)
  -- the conditional density and its representation
  set F : Ω → ℝ := μ[D | 𝓕 T] with hFdef
  have hF2 : MemLp F 2 μ := (Lp.memLp D).condExp one_le_two
  have hFae : ⇑(hF2.toLp F) =ᵐ[μ] F := hF2.coeFn_toLp
  obtain ⟨φ, hφ, -⟩ := exists_itoIntegral_representation hB hBmeas hBcont T (hF2.toLp F)
    (stronglyMeasurable_condExp.aestronglyMeasurable.congr hFae.symm)
  have hint : ∫ x, (hF2.toLp F) x ∂μ = 1 := by
    rw [integral_congr_ae hFae, hFdef, integral_condExp (𝓕.le T), hD]
  -- the pairings against the increments
  have hφ0 : ∀ {s u : ℝ≥0}, s ≤ u → u ≤ T → ∀ {A : Set Ω}, MeasurableSet[𝓕 s] A →
      ∫ ω in A, itoIntegralCLM hB T hBmeas φ ω * (X u ω - X s ω) ∂μ = 0 := by
    intro s u hsu huT A hA
    have hsT : s ≤ T := hsu.trans huT
    have hAm : MeasurableSet A := 𝓕.le s A hA
    have hAT : MeasurableSet[𝓕 T] A := 𝓕.mono hsT _ hA
    have hXu := memLp_of_martingale_increment hB hBmeas T hX ψ hψ hX0 huT
    have hXs := memLp_of_martingale_increment hB hBmeas T hX ψ hψ hX0 hsT
    have hg2 : MemLp (fun ω ↦ X u ω - X s ω) 2 μ := hXu.sub hXs
    have hgint : Integrable (fun ω ↦ X u ω - X s ω) μ := hg2.integrable one_le_two
    -- `∫_A g dμ = 0`
    have hμg : ∫ ω in A, (X u ω - X s ω) ∂μ = 0 := by
      rw [integral_sub (hX.integrable u).integrableOn (hX.integrable s).integrableOn,
        hX.setIntegral_eq hsu hA, sub_self]
    -- `∫_A g dQ = 0`
    have hQg : ∫ ω in A, (X u ω - X s ω) ∂Q = 0 := by
      have h := hQ.setIntegral_eq hsu hA
      simp only [min_eq_left hsT, min_eq_left huT] at h
      have hiu : Integrable (X u) Q := by simpa [min_eq_left huT] using hQ.integrable u
      have his : Integrable (X s) Q := by simpa [min_eq_left hsT] using hQ.integrable s
      rw [integral_sub hiu.integrableOn his.integrableOn, h, sub_self]
    -- `∫_A g dQ = ∫_A D g dμ`
    have hQg' : ∫ ω in A, (X u ω - X s ω) ∂Q = ∫ ω in A, (X u ω - X s ω) * D ω ∂μ := by
      rw [hQp, setIntegral_withDensity_ofReal
        (((Lp.memLp D).aestronglyMeasurable.aemeasurable.max aemeasurable_const).aestronglyMeasurable)
        hDp _ hAm]
      exact setIntegral_congr_ae hAm (hDpD.mono fun ω h _ ↦ by rw [show max (D ω) 0 = D ω from h])
    -- `∫_A D g dμ = ∫_A F g dμ`: pull the `𝓕_T`-measurable `1_A g` out of `μ[· | 𝓕_T]`
    have hFg : ∫ ω in A, (X u ω - X s ω) * D ω ∂μ = ∫ ω in A, F ω * (X u ω - X s ω) ∂μ := by
      set h : Ω → ℝ := A.indicator fun ω ↦ X u ω - X s ω with hh
      have hhsm : StronglyMeasurable[𝓕 T] h :=
        (((hX.stronglyAdapted u).mono (𝓕.mono huT)).sub
          ((hX.stronglyAdapted s).mono (𝓕.mono hsT))).indicator hAT
      have hhD : Integrable (h * ⇑D) μ :=
        (hg2.indicator hAm.nullMeasurableSet).integrable_mul (Lp.memLp D)
      calc ∫ ω in A, (X u ω - X s ω) * D ω ∂μ = ∫ ω, (h * ⇑D) ω ∂μ := by
            rw [← integral_indicator hAm]
            refine integral_congr_ae (.of_forall fun ω ↦ ?_)
            by_cases hω : ω ∈ A <;> simp [hh, Set.indicator, hω]
        _ = ∫ ω, (μ[h * ⇑D | 𝓕 T]) ω ∂μ := (integral_condExp (𝓕.le T)).symm
        _ = ∫ ω, (h * F) ω ∂μ :=
            integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hhsm hhD hD1)
        _ = ∫ ω in A, F ω * (X u ω - X s ω) ∂μ := by
            rw [← integral_indicator hAm]
            refine integral_congr_ae (.of_forall fun ω ↦ ?_)
            by_cases hω : ω ∈ A <;> simp [hh, Set.indicator, hω, mul_comm]
    have hIφ : ∀ᵐ ω ∂μ, itoIntegralCLM hB T hBmeas φ ω = F ω - 1 := by
      filter_upwards [hφ, hFae] with ω h1 h2
      rw [← h2, h1, hint]
      ring
    have hFgint : Integrable (fun ω ↦ F ω * (X u ω - X s ω)) μ := hF2.integrable_mul hg2
    calc ∫ ω in A, itoIntegralCLM hB T hBmeas φ ω * (X u ω - X s ω) ∂μ
        = ∫ ω in A, (F ω * (X u ω - X s ω) - (X u ω - X s ω)) ∂μ :=
          setIntegral_congr_ae hAm (hIφ.mono fun ω h _ ↦ by rw [h]; ring)
      _ = 0 := by
          rw [integral_sub hFgint.integrableOn hgint.integrableOn, ← hFg, ← hQg', hQg, hμg,
            sub_zero]
  have hφψ := ae_mul_eq_zero_of_orthogonal_increments hB hBmeas T hX ψ φ hψ hφ0
  have hφz : φ = 0 := by
    refine Lp.eq_zero_iff_ae_eq_zero.2 ?_
    filter_upwards [hφψ, hψ0] with z h1 h2
    simpa [h2] using h1
  have hF1 : F =ᵐ[μ] fun _ ↦ 1 := by
    filter_upwards [hφ, hFae] with ω h1 h2
    rw [← h2, h1, hint, hφz, map_zero]
    simp
  refine @Measure.ext Ω (𝓕 T) _ _ fun A hA ↦ ?_
  rw [trim_measurableSet_eq _ hA, trim_measurableSet_eq _ hA]
  have hAm := 𝓕.le T A hA
  rw [hQD, withDensity_apply _ hAm, ← ofReal_integral_eq_lintegral_ofReal hD1.integrableOn
    (ae_restrict_of_ae hD0), ← setIntegral_condExp (𝓕.le T) hD1 hA,
    setIntegral_congr_ae hAm (hF1.mono fun ω h _ ↦ h)]
  simp

end MathFin
