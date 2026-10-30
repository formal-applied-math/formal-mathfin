/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.FTAPTwoState
public import MathFin.Foundations.ConvexSeparation
public import MathFin.Foundations.FTAPOnePeriodVector
public import MathFin.Foundations.StatePrices

/-!
# Multi-state FTAP (both directions)

`Foundations/FTAPTwoState.lean` treats the **one-period, one-asset,
two-state** market. This file proves the Fundamental Theorem of Asset Pricing for
**arbitrary finite-state markets with multiple assets**, in **both directions**: the
forward direction (EMM ⟹ no arbitrage) and the backward direction
(no arbitrage ⟹ EMM) — the latter constructs the EMM by
finite-dimensional geometric Hahn–Banach separation of the
attainable-payoff span from the standard simplex
(`exists_pos_dual_of_disjoint_stdSimplex`, `Foundations/ConvexSeparation.lean`).
The two-state market is the case `N = 2`, `M = 1`, and the finite-state market is the
one-period market of `Foundations/FTAPOnePeriodVector.lean` on the state space `Fin N`
(see "Relation to the other EMM notions" below).

## Setup

* `s : Fin N` — states of the world.
* `m : Fin M` — assets (excess-return vectors).
* `z : Fin M → Fin N → ℝ` — excess-return matrix; `z k i` is the
  excess return of asset `k` in state `i`.
* Portfolio: `θ : Fin M → ℝ` — exposure to each asset.
* Portfolio payoff in state `i`: `(Σ_k θ_k · z k i)`.

## Forward FTAP (proved)

`noArbitrage_of_emm_multi`: if there exists `q : Fin N → ℝ` with
`q_i > 0`, `Σ q_i = 1`, and `Σ q_i · z k i = 0` for every asset `k`,
then no portfolio yields a non-negative payoff with at least one
strictly positive state (no arbitrage). Standard linearity argument:
under EMM, every portfolio's `q`-weighted excess return is zero, but
non-negative components with one strictly positive ⟹ strictly positive
weighted sum, contradiction.

## Backward FTAP (proved)

`hasEMM_multi_of_not_hasArbitrage`: no arbitrage ⟹ an EMM exists. The
attainable-payoff subspace `span {z k}` misses the standard simplex (that is
exactly no arbitrage), so the separating-dual kernel
`exists_pos_dual_of_disjoint_stdSimplex` (`Foundations/ConvexSeparation.lean`,
finite-dimensional geometric Hahn–Banach) produces a strictly-positive `q`
annihilating every asset's excess return; normalising `q` to a probability is
the EMM. Together with the forward direction this is the biconditional
`hasEMM_multi_iff_not_hasArbitrage`.

## Relation to the other EMM notions

`HasEMM_multi_state` is the library's EMM notion for finite-state one-period markets.

* **Two states.** `HasEMM_two_state` and `HasArbitrage_two_state` are the `N = 2`, `M = 1`
  cases (`hasEMM_two_state_iff_multi`, `hasArbitrage_two_state_iff_multi`), so the
  two-state FTAP biconditional (`hasEMM_two_state_iff_not_hasArbitrage`) and Nagy's
  opposite-signs lemma (`signs_opposite_of_not_hasArbitrage_two_state`) are instances of
  the multi-state theorem.
* **Measure form.** On `Ω = Fin N` with any full-support probability `P`, the return matrix
  is an `ℝᴹ`-valued random vector `multiStateReturn z`. An arbitrage in the matrix sense is
  exactly a failure of `OnePeriodVector.NoArbitrage`
  (`hasArbitrage_multi_state_iff_not_noArbitrage`), and an EMM vector `q` exists iff there
  is a measure `Q ~ P` with `OnePeriodVector.IsEMM` (`hasEMM_multi_state_iff_exists_isEMM`).
  The latter is derived from the two FTAPs (this file's separation proof and the
  general-Ω softplus proof), so the two independent proofs are shown to agree.
* **Martingale probability vectors.** The EMMs are the strictly positive members of
  `martingaleProbVectors z` (`Foundations/SuperhedgingDuality.lean`).

## Results

* `HasEMM_multi_state`: EMM existence for an N-state market with M assets.
* `HasArbitrage_multi_state`: arbitrage definition.
* `noArbitrage_of_emm_multi`: forward FTAP (EMM ⟹ no arbitrage).
* `hasEMM_multi_of_pos_dual`: a strictly positive pricing vector normalises to an EMM.
* `hasEMM_multi_of_not_hasArbitrage`: backward FTAP (no arbitrage ⟹ EMM).
* `hasEMM_multi_iff_not_hasArbitrage`: the multi-state FTAP biconditional.
* `hasEMM_two_state_iff_not_hasArbitrage`: the two-state FTAP biconditional.
* `hasEMM_multi_state_iff_exists_isEMM`: the measure form of the finite-state EMM.
* `exists_statePrices_of_hasEMM`: an EMM for the excess return `S − S₀/DF` is the state-price
  vector `DF · q` of the no-arbitrage derivations (`Foundations/NoArbitrageDerivations.lean`).
-/

@[expose] public section

namespace MathFin

open Finset

/-- **EMM existence in a multi-state market** (`N` states, `M` assets):
there exists a strictly positive probability `q : Fin N → ℝ` with `Σ q
= 1` and `q`-weighted excess return zero for every asset. Equivalently, an
`OnePeriodVector.IsEMM` measure exists on `Fin N` (`hasEMM_multi_state_iff_exists_isEMM`). -/
def HasEMM_multi_state {N M : ℕ} (z : Fin M → Fin N → ℝ) : Prop :=
  ∃ q : Fin N → ℝ,
    (∀ i, 0 < q i) ∧
    (∑ i, q i) = 1 ∧
    ∀ k, (∑ i, q i * z k i) = 0

/-- **Arbitrage in a multi-state market**: a portfolio `θ : Fin M → ℝ`
with `θ`-weighted excess return non-negative in every state and
strictly positive in at least one state. -/
def HasArbitrage_multi_state {N M : ℕ} (z : Fin M → Fin N → ℝ) : Prop :=
  ∃ θ : Fin M → ℝ,
    (∀ i, 0 ≤ ∑ k, θ k * z k i) ∧
    (∃ i₀, 0 < ∑ k, θ k * z k i₀)

/-- **Forward FTAP, multi-state**: EMM ⟹ no arbitrage. Standard
linearity proof: under EMM, every portfolio's `q`-weighted excess
return is `Σ_i q_i · (Σ_k θ_k · z k i) = Σ_k θ_k · (Σ_i q_i · z k i) =
Σ_k θ_k · 0 = 0`. If the portfolio's payoff is non-negative in every
state and strictly positive in at least one, the `q`-weighted sum is
strictly positive (positive `q_i` times positive payoff at `i₀`),
contradiction. -/
theorem noArbitrage_of_emm_multi {N M : ℕ} (z : Fin M → Fin N → ℝ)
    (h_emm : HasEMM_multi_state z) :
    ¬ HasArbitrage_multi_state z := by
  obtain ⟨q, hq_pos, _hq_sum, h_q_z⟩ := h_emm
  rintro ⟨θ, h_nn, i₀, h_pos⟩
  -- Compute the q-weighted portfolio payoff and show it equals 0.
  have h_swap : ∑ i, q i * (∑ k, θ k * z k i) = ∑ k, θ k * (∑ i, q i * z k i) := by
    -- Distribute q i over inner ∑ k on LHS, θ k over inner ∑ i on RHS,
    -- then both sides are ∑ ∑ over indexes that swap via Finset.sum_comm.
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  have h_zero : ∑ i, q i * (∑ k, θ k * z k i) = 0 := by
    rw [h_swap]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    rw [h_q_z k, mul_zero]
  -- But each term ≥ 0 and the i₀-term is > 0, so the sum is > 0. Contradiction.
  have h_term_nn : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      0 ≤ q i * (∑ k, θ k * z k i) :=
    fun i _ ↦ mul_nonneg (hq_pos i).le (h_nn i)
  have h_term_pos : 0 < q i₀ * (∑ k, θ k * z k i₀) :=
    mul_pos (hq_pos i₀) h_pos
  have h_sum_pos : 0 < ∑ i, q i * (∑ k, θ k * z k i) :=
    Finset.sum_pos' h_term_nn ⟨i₀, Finset.mem_univ _, h_term_pos⟩
  exact h_sum_pos.ne' h_zero

/-- **Normalising a positive pricing vector.** A strictly positive `q` under which every
asset's excess return is fair, divided by its total mass, is an EMM. -/
theorem hasEMM_multi_of_pos_dual {N M : ℕ} [NeZero N] {z : Fin M → Fin N → ℝ}
    {q : Fin N → ℝ} (hq_pos : ∀ i, 0 < q i) (hq_fair : ∀ k, ∑ i, q i * z k i = 0) :
    HasEMM_multi_state z := by
  set Z : ℝ := ∑ i, q i with hZdef
  have hZ_pos : 0 < Z := Finset.sum_pos (fun i _ ↦ hq_pos i) Finset.univ_nonempty
  refine ⟨fun i ↦ q i / Z, fun i ↦ div_pos (hq_pos i) hZ_pos, ?_, fun k ↦ ?_⟩
  · rw [← Finset.sum_div, ← hZdef, div_self hZ_pos.ne']
  · have hcongr : ∀ i, (q i / Z) * z k i = (q i * z k i) / Z := fun i ↦ by ring
    rw [Finset.sum_congr rfl (fun i _ ↦ hcongr i), ← Finset.sum_div, hq_fair k, zero_div]

/-- **Backward FTAP, multi-state**: no arbitrage ⟹ an EMM exists. The
attainable-payoff subspace `span {z k}` is disjoint from the standard simplex
(no arbitrage), so `exists_pos_dual_of_disjoint_stdSimplex` yields a
strictly-positive dual `q` with `∑ i, q i · z k i = 0` for every asset `k`;
normalising `q` to a probability is the equivalent martingale measure. -/
theorem hasEMM_multi_of_not_hasArbitrage {N M : ℕ} [NeZero N]
    (z : Fin M → Fin N → ℝ) (h : ¬ HasArbitrage_multi_state z) :
    HasEMM_multi_state z := by
  -- The attainable-payoff subspace.
  set V : Submodule ℝ (Fin N → ℝ) := Submodule.span ℝ (Set.range z) with hVdef
  -- No arbitrage ⇒ `V` misses the standard simplex.
  have hdisj : ∀ v ∈ V, v ∉ stdSimplex ℝ (Fin N) := by
    intro v hv hsimplex
    rw [hVdef, Submodule.mem_span_range_iff_exists_fun] at hv
    obtain ⟨c, hc⟩ := hv
    have hpayoff : ∀ i, (∑ k, c k * z k i) = v i := by
      intro i
      have h1 : (∑ k, c k • z k) i = v i := by rw [hc]
      rw [Finset.sum_apply] at h1
      simpa only [Pi.smul_apply, smul_eq_mul] using h1
    refine absurd ⟨c, fun i ↦ ?_, ?_⟩ h
    · rw [hpayoff i]; exact hsimplex.1 i
    · obtain ⟨i₀, hi₀⟩ : ∃ i₀, 0 < v i₀ := by
        by_contra hcon
        simp only [not_exists, not_lt] at hcon
        have hle : ∑ i, v i ≤ 0 := Finset.sum_nonpos fun i _ ↦ hcon i
        rw [hsimplex.2] at hle; linarith
      exact ⟨i₀, by rw [hpayoff i₀]; exact hi₀⟩
  obtain ⟨q, hq_pos, hq_dual⟩ := exists_pos_dual_of_disjoint_stdSimplex V hdisj
  exact hasEMM_multi_of_pos_dual hq_pos fun k ↦ hq_dual (z k) (Submodule.subset_span ⟨k, rfl⟩)

/-- **Multi-state FTAP biconditional**: an EMM exists iff there is no
arbitrage. -/
theorem hasEMM_multi_iff_not_hasArbitrage {N M : ℕ} [NeZero N]
    (z : Fin M → Fin N → ℝ) :
    HasEMM_multi_state z ↔ ¬ HasArbitrage_multi_state z :=
  ⟨noArbitrage_of_emm_multi z, hasEMM_multi_of_not_hasArbitrage z⟩

/-! ### The two-state market is the `N = 2`, `M = 1` multi-state market -/

/-- **The two-state EMM is the multi-state EMM** of the one-asset, two-state matrix
`(z_up, z_down)`. -/
theorem hasEMM_two_state_iff_multi (z_up z_down : ℝ) :
    HasEMM_two_state z_up z_down ↔ HasEMM_multi_state (fun _ : Fin 1 ↦ ![z_up, z_down]) := by
  constructor
  · rintro ⟨a, b, ha, hb, hsum, hfair⟩
    refine ⟨![a, b], fun i ↦ ?_, by simpa [Fin.sum_univ_two] using hsum,
      fun _ ↦ by simpa [Fin.sum_univ_two] using hfair⟩
    fin_cases i <;> simp [ha, hb]
  · rintro ⟨q, hq, hsum, hfair⟩
    exact ⟨q 0, q 1, hq 0, hq 1, by simpa [Fin.sum_univ_two] using hsum,
      by simpa [Fin.sum_univ_two] using hfair 0⟩

/-- **Two-state arbitrage is multi-state arbitrage** for the one-asset, two-state matrix
`(z_up, z_down)`: a position `θ` in the single asset is a portfolio `Fin 1 → ℝ`. -/
theorem hasArbitrage_two_state_iff_multi (z_up z_down : ℝ) :
    HasArbitrage_two_state z_up z_down ↔
      HasArbitrage_multi_state (fun _ : Fin 1 ↦ ![z_up, z_down]) := by
  constructor
  · rintro ⟨θ, hup, hdown, hpos⟩
    refine ⟨fun _ ↦ θ, fun i ↦ ?_, ?_⟩
    · fin_cases i
      · simpa using hup
      · simpa using hdown
    · rcases hpos with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
  · rintro ⟨θ, hnn, i₀, hi₀⟩
    refine ⟨θ 0, by simpa using hnn 0, by simpa using hnn 1, ?_⟩
    fin_cases i₀
    · exact Or.inl (by simpa using hi₀)
    · exact Or.inr (by simpa using hi₀)

/-- **Two-state FTAP biconditional**: in the one-period, one-asset, two-state market an
EMM exists iff there is no arbitrage. The `N = 2`, `M = 1` case of
`hasEMM_multi_iff_not_hasArbitrage`. -/
theorem hasEMM_two_state_iff_not_hasArbitrage (z_up z_down : ℝ) :
    HasEMM_two_state z_up z_down ↔ ¬ HasArbitrage_two_state z_up z_down := by
  rw [hasEMM_two_state_iff_multi, hasArbitrage_two_state_iff_multi]
  exact hasEMM_multi_iff_not_hasArbitrage _

/-- **Opposite signs under no arbitrage** (Nagy 2026, Theorem 7.2): in an arbitrage-free
two-state market whose excess returns are not both zero, one is strictly positive and the
other strictly negative. The EMM `q_up z_up + q_down z_down = 0` with `q_up, q_down > 0`
forces it. -/
theorem signs_opposite_of_not_hasArbitrage_two_state {z_up z_down : ℝ}
    (h : ¬ HasArbitrage_two_state z_up z_down) (hz : z_up ≠ 0 ∨ z_down ≠ 0) :
    (0 < z_up ∧ z_down < 0) ∨ (z_up < 0 ∧ 0 < z_down) := by
  obtain ⟨a, b, ha, hb, -, hfair⟩ := (hasEMM_two_state_iff_not_hasArbitrage z_up z_down).mpr h
  rcases lt_trichotomy z_up 0 with hu | hu | hu
  · exact Or.inr ⟨hu, by nlinarith [mul_pos ha (neg_pos.mpr hu)]⟩
  · subst hu
    have hd : z_down = 0 := (mul_eq_zero.mp (by linarith : b * z_down = 0)).resolve_left hb.ne'
    simp [hd] at hz
  · exact Or.inl ⟨hu, by nlinarith [mul_pos ha hu]⟩

/-! ### The finite-state market as a one-period market on `Ω = Fin N`

On the state space `Fin N` (discrete σ-algebra) with a full-support probability `P`, the
return matrix `z` is the `ℝᴹ`-valued random vector `multiStateReturn z`, a portfolio
`θ : Fin M → ℝ` is a vector of `ℝᴹ`, and its payoff `∑ₖ θₖ z k i` is the inner product
`⟪θ, multiStateReturn z i⟫`. `P`-a.e. statements are statements about every state. -/

section MeasureForm

open MeasureTheory

/-- The excess-return matrix read as a random vector on the state space: in state `i`, the
`M` assets' excess returns as a point of `ℝᴹ = EuclideanSpace ℝ (Fin M)`. -/
def multiStateReturn {N M : ℕ} (z : Fin M → Fin N → ℝ) (i : Fin N) :
    EuclideanSpace ℝ (Fin M) :=
  WithLp.toLp 2 fun k ↦ z k i

/-- A portfolio's payoff in state `i` is its inner product with the return vector. -/
lemma inner_multiStateReturn {N M : ℕ} (z : Fin M → Fin N → ℝ)
    (θ : EuclideanSpace ℝ (Fin M)) (i : Fin N) :
    inner ℝ θ (multiStateReturn z i) = ∑ k, θ k * z k i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [multiStateReturn, WithLp.ofLp_toLp, dotProduct, Pi.star_apply, star_trivial]
  exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _

/-- **Matrix arbitrage is measure-theoretic arbitrage.** For any measure `P` on the states
charging every state, a portfolio with non-negative payoff in every state and a
positive payoff in some state exists iff `OnePeriodVector.NoArbitrage` fails for the return
vector `multiStateReturn z`. -/
theorem hasArbitrage_multi_state_iff_not_noArbitrage {N M : ℕ} (z : Fin M → Fin N → ℝ)
    (P : Measure (Fin N)) (hP : ∀ i, P {i} ≠ 0) :
    HasArbitrage_multi_state z ↔ ¬ OnePeriodVector.NoArbitrage P (multiStateReturn z) := by
  have hae (p : Fin N → Prop) : (∀ᵐ i ∂P, p i) ↔ ∀ i, p i := by
    rw [ae_iff_of_countable]
    exact forall_congr' fun i ↦ ⟨fun h ↦ h (hP i), fun h _ ↦ h⟩
  simp only [OnePeriodVector.NoArbitrage, Filter.EventuallyLE, Filter.EventuallyEq, hae,
    inner_multiStateReturn, Pi.zero_apply, not_forall]
  constructor
  · rintro ⟨θ, hnn, i₀, hpos⟩
    exact ⟨WithLp.toLp 2 θ, hnn, i₀, hpos.ne'⟩
  · rintro ⟨θ, hnn, i₀, hne⟩
    exact ⟨WithLp.ofLp θ, hnn, i₀, lt_of_le_of_ne (hnn i₀) (Ne.symm hne)⟩

/-- **The finite-state EMM is the one-period EMM on `Fin N`.** For any probability `P` on
the states charging every state, an EMM vector `q` (strictly positive, summing to `1`,
pricing every asset's excess return at zero) exists iff some `Q ~ P` makes the return vector
`multiStateReturn z` integrable with `E_Q[multiStateReturn z] = 0`. Derived by composing the
multi-state FTAP (`hasEMM_multi_iff_not_hasArbitrage`, separation), the arbitrage bridge
above, and the general-Ω vector FTAP (`OnePeriodVector.ftap_one_period_vector`, softplus
potential). -/
theorem hasEMM_multi_state_iff_exists_isEMM {N M : ℕ} [NeZero N] (z : Fin M → Fin N → ℝ)
    (P : Measure (Fin N)) [IsProbabilityMeasure P] (hP : ∀ i, P {i} ≠ 0) :
    HasEMM_multi_state z ↔ ∃ Q, OnePeriodVector.IsEMM P (multiStateReturn z) Q := by
  rw [hasEMM_multi_iff_not_hasArbitrage, hasArbitrage_multi_state_iff_not_noArbitrage z P hP,
    not_not]
  exact OnePeriodVector.ftap_one_period_vector P _ (measurable_of_finite _)

end MeasureForm

/-- **State prices from an EMM.** If the one-asset market with terminal values `S` and the
excess return `S i − S₀/DF` (the asset's value against its forward `S₀/DF`) has an EMM `p`,
then `q = DF · p` is a strictly positive state-price vector that prices the unit bond at `DF`
and the asset at `S₀` — exactly the bond and stock constraints of
`putCall_parity_from_no_arbitrage` and `forward_price_from_no_arbitrage`. -/
theorem exists_statePrices_of_hasEMM {N : ℕ} (S : Fin N → ℝ) {DF : ℝ} (S₀ : ℝ) (hDF : 0 < DF)
    (h : HasEMM_multi_state (M := 1) fun _ i ↦ S i - S₀ / DF) :
    ∃ q : Fin N → ℝ, (∀ i, 0 < q i) ∧ ∑ i, q i = DF ∧
      statePricePricing Finset.univ q S = S₀ := by
  obtain ⟨p, hp, hsum, hz⟩ := h
  have hmean : ∑ i, p i * S i = S₀ / DF := by
    have h0 := hz 0
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul] at h0
    linarith
  refine ⟨fun i ↦ DF * p i, fun i ↦ mul_pos hDF (hp i), ?_, ?_⟩
  · rw [← Finset.mul_sum, hsum, mul_one]
  · simp only [statePricePricing, mul_assoc, ← Finset.mul_sum, hmean]
    field_simp

end MathFin
