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

Two general facts about the Itô integral are what make that sentence true, and both
live one floor down, in `ItoIntegralLocality`.

*Locality in time* is what converts the Itô formula's *terminal* identity
`∫₀ᵀ φ dB = M_T − 1` into one for the inner increment `M_b − M_a` the telescoping needs:
`itoIntegralCLM_T_restrictAfterCLM` says that restricting an integrand to `(u,T]`
subtracts exactly `(φ●B)_u` from its integral, and `(φ●B)_u` is the `𝓕_u`-conditional
expectation of `∫₀ᵀ φ dB` — which, `M` being Wald's martingale, is `M_u − 1`. Cutting
the integrand at `a` and at `b` and subtracting gives the band integrand of
`constDoleans_band_mem_range`.

*The sample-side form of the integrand hypothesis* is what lets `Eₙ` — unbounded — be
pulled inside. `itoIntegralCLM_T_smul_of_memLp` accepts `Eₙ·∫φ dB ∈ L²(μ)` in place of
`Eₙ·φ ∈ L²(trim)`, and after rewriting along the band identity that requirement is
exactly `Dₙ₊₁ − Dₙ ∈ L²(μ)`. So the only moment fact this file needs is that every step
Doléans exponential has a second moment (`memLp_stepDoleansExp`) — proved by writing it
as `exp(−c)·exp(∑ hₖΔBₖ)` and inducting on the *scale*, since the square of an
`(n+1)`-fold exponential is the `n`-fold one at twice the scale times one lognormal
factor, which Cauchy–Schwarz multiplies.

That is also why the constant case is stated existentially here. The plan called for a
version *naming* the integrand as `s ↦ σ·exp(σB_s − ½σ²s)`, to feed the `L²(trim)`
hypothesis directly, and at the time that was not derivable from the tower's exported
API: every link of the chain

  `cutoff_bddDeriv → ito_formula_td_localized → ito_formula_itoProcess →
   ito_formula_gbm → discountedGBM_eq_itoIntegral`

was a bare existential. The chain now carries the naming conjunct throughout, so the named
form is one `obtain` away should a consumer want it. This file still does not: the
sample-side transfer never needed the integrand's identity, only its integral's second
moment, and stating what a proof does not use is what the `∃` here honestly records.

## Result

* `constDoleans_sub_one_mem_range` — the constant-`σ` Doléans exponential, minus one, is an
  Itô integral over `[0,T]`.
* `constDoleans_band_mem_range` — the band form: the increment `M_b − M_a` is the integral of
  an integrand supported on `(a,b]`, and the two support clauses come with it.
* `constDoleans_shift_sub_one_mem_range` — that band renormalised by the `𝓕_a`-measurable
  `1/M_a`, giving `M_T/M_a − 1`.
* `stepDoleansExp` — the Doléans exponential of a deterministic step integrand.
* `stepDoleans_sub_one_mem_range` — **the theorem**: that exponential, minus one, lies in the
  range of `∫₀ᵀ · dB`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter ItoIntegralCLM ItoIntegralL2
open ItoIntegralProcessGeneral
open scoped NNReal ENNReal Topology

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

include hB

/-! ### The Doléans exponential of a constant integrand over a band -/

/-- **Constant-`σ` Doléans exponential as an Itô integral.** `discountedGBM_eq_itoIntegral`
at `S₀ = 1`, with `B 0 =ᵐ 0`: `exp(σB_T − σ²T/2) − 1 = ∫₀ᵀ σ·exp(σB_s − σ²s/2) dB_s`. -/
theorem constDoleans_sub_one_mem_range (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (T : ℝ≥0) (σ : ℝ) :
    ∃ φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (fun ω ↦ Real.exp (σ * B T ω - σ ^ 2 * (T : ℝ) / 2) - 1)
        =ᵐ[μ] ⇑(itoIntegralCLM_T hB T hBmeas φ) := by
  obtain ⟨gfx, -, hgfx⟩ := discountedGBM_eq_itoIntegral hB hBmeas hBcont T 1 σ
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
  have hproc (u : ℝ≥0) (huT : u ≤ T) :
      ⇑(itoProcessCLM hB T u hBmeas ψ)
        =ᵐ[μ] fun ω ↦ Real.exp (σ * B u ω - σ ^ 2 * (u : ℝ) / 2) - 1 := by
    have hcondExpL2 : ⇑(itoProcessCLM hB T u hBmeas ψ)
        =ᵐ[μ] μ[⇑(itoIntegralCLM_T hB T hBmeas ψ) | natFiltration hBmeas u] := by
      rw [itoProcessCLM_eq_condExpL2 hB T u hBmeas ψ]
      have h := (Lp.memLp (itoIntegralCLM_T hB T hBmeas ψ)).condExpL2_ae_eq_condExp
        (𝕜 := ℝ) ((natFiltration hBmeas).le u)
      rwa [Lp.toLp_coeFn] at h
    refine hcondExpL2.trans ((condExp_congr_ae hψ.symm).trans ?_)
    exact ((IsFilteredPreBrownian.waldExponential_isMartingale σ).sub
      (martingale_const _ _ 1)).2 u T huT
  have hcut := Lp.coeFn_sub (restrictAfterCLM T a hBmeas ψ) (restrictAfterCLM T b hBmeas ψ)
  have hcuta := coeFn_restrictAfterCLM T a hBmeas ψ
  have hcutb := coeFn_restrictAfterCLM T b hBmeas ψ
  refine ⟨restrictAfterCLM T a hBmeas ψ - restrictAfterCLM T b hBmeas ψ, ?_, ?_, ?_⟩
  · filter_upwards [hcut, hcuta, hcutb] with p h1 h2 h3 hpa
    rw [h1, Pi.sub_apply, h2, h3, if_neg (not_lt.mpr hpa), if_neg (not_lt.mpr (hpa.trans hab)),
      sub_self]
  · filter_upwards [hcut, hcuta, hcutb] with p h1 h2 h3 hpb
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
  have halg (ω : Ω) : Real.exp (-(σ * B a ω) + σ ^ 2 * (a : ℝ) / 2) *
      (Real.exp (σ * B T ω - σ ^ 2 * (T : ℝ) / 2) - Real.exp (σ * B a ω - σ ^ 2 * (a : ℝ) / 2))
      = Real.exp (σ * (B T ω - B a ω) - σ ^ 2 * ((T : ℝ) - (a : ℝ)) / 2) - 1 := by
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
        (((memLp_exp_incr hB a T σ).const_mul
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
  have hmeas (m : ℕ) (c : ℝ) : AEStronglyMeasurable (fun ω ↦ Real.exp (c *
      ∑ k ∈ Finset.range m, h k * (B (s (k + 1)) ω - B (s k) ω))) μ :=
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
      (memLp_exp_incr hB (s n) (s (n + 1)) (2 * c * h n))

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
  have hBm {v : ℝ≥0} (hv : v ≤ s m) : Measurable[natFiltration hBmeas (s m)] (B v) := by
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
    have halg (ω : Ω) : (stepDoleansExp B s h n ω *
          Real.exp (-(h n * B (s n) ω) + h n ^ 2 * (s n : ℝ) / 2)) *
        (Real.exp (h n * B (s (n + 1)) ω - h n ^ 2 * ((s (n + 1) : ℝ)) / 2)
          - Real.exp (h n * B (s n) ω - h n ^ 2 * (s n : ℝ) / 2))
        = stepDoleansExp B s h (n + 1) ω - stepDoleansExp B s h n ω := by
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
partition `s₀ ≤ … ≤ s_N = T` and deterministic heights `h`, the Doléans
exponential `∏ₖ exp(hₖΔBₖ − ½hₖ²Δsₖ)`, minus one, lies in the range of `∫₀ᵀ · dB`.
The partition need not start at `0`: the induction bottoms out at the empty product
`D₀ = 1`, which is the zero integrand's integral whatever `s 0` is. -/
theorem stepDoleans_sub_one_mem_range (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) (T : ℝ≥0)
    (s : ℕ → ℝ≥0) (hs : Monotone s) (h : ℕ → ℝ) (N : ℕ)
    (hsN : s N = T) :
    ∃ φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (fun ω ↦ stepDoleansExp B s h N ω - 1)
        =ᵐ[μ] ⇑(itoIntegralCLM_T hB T hBmeas φ) :=
  let ⟨φ, _, hval⟩ := stepDoleans_aux hB hBmeas hBcont T hs h N hsN.le
  ⟨φ, hval⟩

end MathFin
