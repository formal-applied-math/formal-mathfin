/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.FiniteBellman
public import MathFin.Foundations.DoobDecomposition
public import MathFin.Foundations.OptionalSamplingInequality

/-!
# Bridge: Doob decomposition and optional sampling of the finite-horizon Snell envelope

`finiteBellman P 𝓕 Z N` (`BlackScholes/AmericanPut/Stopping/FiniteBellman.lean`) is the backward
Bellman recursion `U_i = max(Z_i, 𝔼[U_{i+1} | 𝓕_i])` for an adapted integrable reward `Z` on an
arbitrary filtered probability space, frozen at `Z_N` after the horizon `N`: the discrete Snell
envelope of `Z`. It is a supermartingale (`finiteBellman_supermartingale`). This file applies two
results of `Foundations/` to it.

* **Doob decomposition** (`Foundations/DoobDecomposition`). `U = M + A` with `M` a martingale and
  `A` predictable with `A₀ = 0`, unique up to a.e. equality at every time
  (`doob_decomposition_unique`). For the Snell envelope the compensator `A` is a.e.
  nonincreasing, and it does not move on the continuation region: at a step `i < N` where
  `Z_i < U_i`, `A_{i+1} = A_i` almost surely, because there `U_i = 𝔼[U_{i+1} | 𝓕_i]`.
* **Optional sampling** (`Foundations/OptionalSamplingInequality`). For stopping times
  `σ ≤ τ ≤ N`, `𝔼[Z_τ | 𝓕_σ] ≤ U_σ` almost surely: at any stopping time the envelope dominates
  the conditional expected reward of every later bounded stopping rule. At `σ = 0` and in
  expectation this is `expected_discrete_payoff_le_bellman`.

## Main results

* `finiteBellman_doob_decomposition`
* `condExp_stoppedValue_le_finiteBellman`
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›} {Z : ℕ → Ω → ℝ}

/-- **Doob decomposition of the finite-horizon Snell envelope.** For an adapted integrable reward
`Z` and a horizon `N`, the Bellman value `U = finiteBellman P 𝓕 Z N` is `M + A` with `M` a
martingale and `A` predictable (`A (n + 1)` is `𝓕 n`-measurable) with `A 0 = 0`, and:

* `A` is a.e. nonincreasing (`U` is a supermartingale);
* `A` is constant across every step `i < N` taken in the continuation region `Z_i < U_i`;
* the pair `(M, A)` is unique up to a.e. equality at every time
  (`doob_decomposition_unique`). -/
theorem finiteBellman_doob_decomposition (ha : Adapted 𝓕 Z) (hi : ∀ i, Integrable (Z i) P)
    (N : ℕ) :
    ∃ M A : ℕ → Ω → ℝ,
      (Martingale M 𝓕 P ∧ (StronglyAdapted 𝓕 fun n ↦ A (n + 1)) ∧ A 0 = 0 ∧
        M + A = finiteBellman P 𝓕 Z N) ∧
      (∀ᵐ ω ∂P, Antitone fun n ↦ A n ω) ∧
      (∀ i < N, ∀ᵐ ω ∂P, Z i ω < finiteBellman P 𝓕 Z N i ω → A (i + 1) ω = A i ω) ∧
      ∀ M' A' : ℕ → Ω → ℝ, Martingale M' 𝓕 P → (StronglyAdapted 𝓕 fun n ↦ A' (n + 1)) →
        A' 0 = 0 → (∀ n, Integrable (A' n) P) → M' + A' = finiteBellman P 𝓕 Z N →
        ∀ n, M' n =ᵐ[P] M n ∧ A' n =ᵐ[P] A n := by
  set U := finiteBellman P 𝓕 Z N
  have hUa : StronglyAdapted 𝓕 U := finiteBellman_stronglyAdapted ha N
  have hUi : ∀ i, Integrable (U i) P := finiteBellman_integrable hi N
  have hU : Supermartingale U 𝓕 P := finiteBellman_supermartingale ha hi N
  -- the one-step conditional increments of a supermartingale are a.e. nonpositive
  have hinc (n : ℕ) : P[U (n + 1) - U n | 𝓕 n] ≤ᵐ[P] 0 := by
    have hneg := hU.neg.condExp_sub_nonneg (Nat.le_add_right n 1)
    have heq : (-U) (n + 1) - (-U) n = -(U (n + 1) - U n) := by
      funext ω
      simp only [Pi.sub_apply, Pi.neg_apply]
      ring
    rw [heq] at hneg
    filter_upwards [hneg, condExp_neg (U (n + 1) - U n) (𝓕 n)] with ω h1 h2
    simp only [Pi.zero_apply, Pi.neg_apply] at h1 h2 ⊢
    linarith
  refine ⟨martingalePart U 𝓕 P, predictablePart U 𝓕 P,
    ⟨martingale_martingalePart hUa hUi, stronglyAdapted_predictablePart, predictablePart_zero,
      martingalePart_add_predictablePart 𝓕 P U⟩, ?_, fun i hiN ↦ ?_,
    fun M' A' hM' hA' hA'0 hA'i hM'A' n ↦ doob_decomposition_unique hM' hA' hA'0 hA'i hM'A' n⟩
  · filter_upwards [ae_all_iff.2 hinc] with ω h
    refine antitone_nat_of_succ_le fun n ↦ ?_
    have hn := h n
    simp only [Pi.zero_apply] at hn
    rw [predictablePart_add_one, Pi.add_apply]
    linarith
  · have hrec : U i = fun ω ↦ max (Z i ω) (P[U (i + 1) | 𝓕 i] ω) := finiteBellman_recursion hiN
    have hself : P[U i | 𝓕 i] = U i := condExp_of_stronglyMeasurable (𝓕.le i) (hUa i) (hUi i)
    filter_upwards [condExp_sub (hUi (i + 1)) (hUi i) (𝓕 i)] with ω hω hlt
    have hUω : U i ω = max (Z i ω) (P[U (i + 1) | 𝓕 i] ω) := congrFun hrec ω
    rw [hUω] at hlt
    have hstay : U i ω = P[U (i + 1) | 𝓕 i] ω := by
      rw [hUω, max_eq_right ((lt_max_iff.mp hlt).resolve_left (lt_irrefl _)).le]
    rw [predictablePart_add_one, Pi.add_apply, hω, Pi.sub_apply, hself, ← hstay, sub_self,
      add_zero]

/-- **Optional sampling for the Snell envelope.** For an adapted integrable reward `Z`, a
horizon `N` and stopping times `σ ≤ τ` with `τ ≤ N`, the conditional expected reward at `τ`
given `𝓕_σ` is at most the Bellman value at `σ`:

  `𝔼[Z_τ | 𝓕_σ] ≤ U_σ`  almost surely, `U = finiteBellman P 𝓕 Z N`.

The optional sampling inequality `submartingale_optional_sampling` for the submartingale `−U`
gives `𝔼[U_τ | 𝓕_σ] ≤ U_σ`, and `Z_τ ≤ U_τ` pathwise (`finiteBellman_dominates`, `τ ≤ N`). -/
theorem condExp_stoppedValue_le_finiteBellman (ha : Adapted 𝓕 Z) (hi : ∀ i, Integrable (Z i) P)
    {N : ℕ} {σ τ : Ω → ℕ∞} (hσ : IsStoppingTime 𝓕 σ) (hτ : IsStoppingTime 𝓕 τ) (hστ : σ ≤ τ)
    (hτN : ∀ ω, τ ω ≤ N) :
    P[stoppedValue Z τ | hσ.measurableSpace]
      ≤ᵐ[P] stoppedValue (finiteBellman P 𝓕 Z N) σ := by
  have hτk (ω : Ω) : (τ ω).untopA ≤ N := by
    have h := hτN ω
    have hne : τ ω ≠ ⊤ := fun htop ↦ by simp [htop] at h
    obtain ⟨a, ha'⟩ := WithTop.ne_top_iff_exists.1 hne
    rw [← ha'] at h ⊢
    simpa only [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe] using
      WithTop.coe_le_coe.1 h
  have hdom : stoppedValue Z τ ≤ᵐ[P] stoppedValue (finiteBellman P 𝓕 Z N) τ :=
    ae_of_all _ fun ω ↦ by
      have h := finiteBellman_dominates (P := P) (𝓕 := 𝓕) (Z := Z) N (τ ω).untopA ω
      rw [min_eq_left (hτk ω)] at h
      exact h
  have hos := submartingale_optional_sampling (finiteBellman_supermartingale ha hi N).neg
    hτ hσ hστ hτN
  have hneg (ρ : Ω → ℕ∞) : stoppedValue (-finiteBellman P 𝓕 Z N) ρ
      = -stoppedValue (finiteBellman P 𝓕 Z N) ρ := rfl
  rw [hneg, hneg] at hos
  filter_upwards [condExp_mono (m := hσ.measurableSpace) (integrable_stoppedValue ℕ hτ hi hτN)
      (integrable_stoppedValue ℕ hτ (finiteBellman_integrable hi N) hτN) hdom, hos,
    condExp_neg (stoppedValue (finiteBellman P 𝓕 Z N) τ) hσ.measurableSpace] with ω h1 h2 h3
  simp only [Pi.neg_apply] at h2 h3
  rw [h3] at h2
  linarith

end MathFin.BlackScholes.AmericanPut.Stopping
