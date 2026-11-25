/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Pricing.Market
public import MathFin.Pricing.SuperhedgingDuality
public import MathFin.Risk.AcceptanceSet
public import MathFin.Risk.Coherent

/-!
# The superhedging price is a coherent risk measure

In the one-period finite-state market with excess-return matrix `z : Fin M → Fin N → ℝ`
(`Pricing/SuperhedgingDuality.lean`), the **superhedging price** of a claim `Y` (a liability
paying `Yₙ` in state `n`) is the least initial capital `x` for which some portfolio `θ` makes the
terminal wealth `x + ∑ₘ θₘ zₘₙ` dominate `Y` in every state. Read as a *loss*, `Y` is charged the
capital that makes it acceptable, which is the library's convention for a coherent risk measure
(`IsCoherentRiskMeasure`: a larger loss is worse, `ρ (Y + m) = ρ Y + m`).

A superreplicating capital always exists (the claim's absolute value summed over states, with no
portfolio), and a martingale probability vector `q` bounds every such capital below by `∑ qₙ Yₙ`
(`emm_le_superReplication`), so with such a vector the infimum is a genuine real greatest lower
bound. That hypothesis, `(martingaleProbVectors z).Nonempty`, is weaker than
no arbitrage (`martingaleProbVectors_nonempty_of_not_hasArbitrage`), because a martingale
probability vector may vanish on a state.

Superhedging is a pointwise-in-states notion, so it is monotone for the pointwise order only. The
axioms of `IsCoherentRiskMeasure` ask monotonicity almost surely; for them to hold the reference
measure `P` on the states must charge every state (`hP : ∀ n, P {n} ≠ 0`).

The **duality** needs no Minkowski–Weyl theorem. The superhedging price is a coherent risk
measure, so the finite-state representation theorem of Artzner, Delbaen, Eber and Heath
(`coherentRisk_isLUB`) expresses it as the supremum of `∑ qₙ Yₙ` over its representing set, and
that set is exactly `martingaleProbVectors z` (`representingSet_superhedgingPrice`): a
martingale probability vector prices every claim of nonpositive superhedging price at most `0`, and
conversely a representing vector prices the gain of every portfolio, a claim superreplicated at
capital `0` by that portfolio and its negative, at both `≤ 0` and `≥ 0`.
`superhedgingPrice_isLUB` is the duality: the superhedging price is the least upper bound of the
prices under the martingale probability vectors.

## Main definitions

* `superhedgingPrice`: the least capital that superreplicates a claim,
  `sInf {x | ∃ θ, SuperReplicates z Y x θ}`.

## Main results

* `MathFin.isCoherentRiskMeasure_superhedgingPrice`: the superhedging price is a coherent risk
  measure of the claim, viewed as a loss.
* `MathFin.representingSet_superhedgingPrice`: the representing set of the superhedging price is
  `martingaleProbVectors z`.
* `MathFin.superhedgingPrice_isLUB`: **superhedging duality**, the superhedging price is the least
  upper bound of the prices `∑ qₙ Yₙ` over the martingale probability vectors `q`.
* `MathFin.le_superhedgingPrice`: the price under every martingale probability vector is a lower
  bound of the superhedging price.
* `MathFin.Market.IsPricingMeasure.price_pay_le_superhedgingPrice`: the joint with `Market`: the
  price of a payment under a pricing measure of a finite-state market is at most the superhedging
  price of its deflated payoff, in the deflated excess returns `Market.excessReturn`
  (`Market.IsPricingMeasure.mem_martingaleProbVectors`).
* `MathFin.martingaleProbVectors_nonempty_of_not_hasArbitrage`: no arbitrage supplies the
  hypothesis.

## References

* [H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete Time*][FollmerSchied],
  §1.3 and §7.1
* [P. Artzner et al., *Coherent measures of risk*][ArtznerDelbaenEberHeath1999]

## Tags

superhedging, super-replication, superhedging price, coherent risk measure, martingale
probability vector, capital requirement, MSC 91G20, MSC 91G70, JEL G13, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory
open scoped NNReal

variable {M N : ℕ} {z : Fin M → Fin N → ℝ} {Y Y' : Fin N → ℝ} {x x' : ℝ} {θ θ' : Fin M → ℝ}

/-- The **superhedging price** of a claim `Y` in the market `z`: the least initial capital `x` for
which some portfolio `θ` superreplicates `Y` (`SuperReplicates z Y x θ`). It is the infimum of the
superreplicating capitals. The set of capitals is always nonempty; a martingale probability
vector bounds it below (`le_superhedgingPrice`), and without a lower bound the real `sInf` would
return the junk value `0`. -/
noncomputable def superhedgingPrice (z : Fin M → Fin N → ℝ) (Y : Fin N → ℝ) : ℝ :=
  sInf {x | ∃ θ, SuperReplicates z Y x θ}

namespace SuperReplicates

/-- A superreplicating portfolio of a larger claim superreplicates the smaller one. -/
lemma mono (hY : Y ≤ Y') (h : SuperReplicates z Y' x θ) : SuperReplicates z Y x θ :=
  fun n ↦ (hY n).trans (h n)

/-- Adding the constant `m` to a claim adds `m` to its superreplicating capital. -/
lemma add_const (h : SuperReplicates z Y x θ) (m : ℝ) :
    SuperReplicates z (fun n ↦ Y n + m) (x + m) θ :=
  fun n ↦ by linarith [h n]

/-- Subtracting the constant `m` from a claim's superreplicating capital: the converse of
`add_const`. -/
lemma sub_const {m : ℝ} (h : SuperReplicates z (fun n ↦ Y n + m) x θ) :
    SuperReplicates z Y (x - m) θ :=
  fun n ↦ by linarith [h n]

/-- Scaling a claim by `c ≥ 0` scales its superreplicating capital and portfolio by `c`. -/
lemma smul (h : SuperReplicates z Y x θ) {c : ℝ} (hc : 0 ≤ c) :
    SuperReplicates z (fun n ↦ c * Y n) (c * x) (c • θ) := fun n ↦ by
  refine (mul_le_mul_of_nonneg_left (h n) hc).trans_eq ?_
  simp only [Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum, mul_assoc]

/-- Superreplicating two claims superreplicates their sum, at the sum of the capitals. -/
lemma add (h : SuperReplicates z Y x θ) (h' : SuperReplicates z Y' x' θ') :
    SuperReplicates z (fun n ↦ Y n + Y' n) (x + x') (θ + θ') := fun n ↦ by
  have e : ∑ m, (θ + θ') m * z m n = ∑ m, θ m * z m n + ∑ m, θ' m * z m n := by
    simp [add_mul, Finset.sum_add_distrib]
  linarith [h n, h' n]

end SuperReplicates

variable (z Y) in
/-- Every claim is superreplicated by some capital: the sum of its absolute values, with no
portfolio. -/
lemma exists_superReplicates : ∃ x θ, SuperReplicates z Y x θ :=
  ⟨∑ n, |Y n|, 0, fun n ↦ by
    have := Finset.single_le_sum (f := fun n ↦ |Y n|) (fun i _ ↦ abs_nonneg (Y i))
      (Finset.mem_univ n)
    simpa using (le_abs_self (Y n)).trans this⟩

/-- A lower bound of every superreplicating capital is a lower bound of the superhedging price. -/
lemma le_superhedgingPrice_of_forall {a : ℝ}
    (h : ∀ x θ, SuperReplicates z Y x θ → a ≤ x) : a ≤ superhedgingPrice z Y := by
  obtain ⟨x, θ, hs⟩ := exists_superReplicates z Y
  exact le_csInf ⟨x, θ, hs⟩ fun _ ⟨θ, hθ⟩ ↦ h _ θ hθ

/-- **The price under a martingale probability vector bounds the superhedging price from below**:
`∑ qₙ Yₙ ≤ superhedgingPrice z Y` for every `q` in `martingaleProbVectors z`, so in particular for
every equivalent martingale measure. This is `emm_le_superReplication` passed to the infimum of
the superreplicating capitals. -/
theorem le_superhedgingPrice {q : Fin N → ℝ} (hq : q ∈ martingaleProbVectors z)
    (Y : Fin N → ℝ) : ∑ n, q n * Y n ≤ superhedgingPrice z Y :=
  le_superhedgingPrice_of_forall fun _ _ h ↦ emm_le_superReplication z Y hq h

/-- The superhedging price is at most every superreplicating capital, when a martingale
probability vector bounds the capitals below. -/
theorem superhedgingPrice_le (hz : (martingaleProbVectors z).Nonempty)
    (h : SuperReplicates z Y x θ) : superhedgingPrice z Y ≤ x := by
  obtain ⟨q, hq⟩ := hz
  exact csInf_le ⟨∑ n, q n * Y n, fun _ ⟨_, hθ⟩ ↦ emm_le_superReplication z Y hq hθ⟩ ⟨θ, h⟩

/-- No arbitrage supplies a martingale probability vector (the multi-state FTAP). -/
theorem martingaleProbVectors_nonempty_of_not_hasArbitrage [NeZero N]
    (hNA : ¬ HasArbitrageMultiState z) : (martingaleProbVectors z).Nonempty :=
  let ⟨q, hq, _⟩ :=
    (hasEMMMultiState_iff_exists_pos_mem z).mp (hasEMM_multi_of_not_hasArbitrage z hNA)
  ⟨q, hq⟩

/-- **Monotonicity**: a pointwise larger claim has the larger superhedging price. -/
theorem superhedgingPrice_mono (hz : (martingaleProbVectors z).Nonempty) (h : Y ≤ Y') :
    superhedgingPrice z Y ≤ superhedgingPrice z Y' :=
  le_superhedgingPrice_of_forall fun _ _ hs ↦ superhedgingPrice_le hz (hs.mono h)

/-- **Cash invariance**: adding `m` to the claim adds `m` to its superhedging price. -/
theorem superhedgingPrice_add_const (hz : (martingaleProbVectors z).Nonempty) (Y : Fin N → ℝ)
    (m : ℝ) : superhedgingPrice z (fun n ↦ Y n + m) = superhedgingPrice z Y + m := by
  refine le_antisymm ?_ ?_
  · have : superhedgingPrice z (fun n ↦ Y n + m) - m ≤ superhedgingPrice z Y :=
      le_superhedgingPrice_of_forall fun x θ hs ↦ by
        linarith [superhedgingPrice_le hz (hs.add_const m)]
    linarith
  · exact le_superhedgingPrice_of_forall fun x θ hs ↦ by
      linarith [superhedgingPrice_le hz hs.sub_const]

/-- **Positive homogeneity**: `superhedgingPrice (c Y) = c · superhedgingPrice Y` for `c ≥ 0`. -/
theorem superhedgingPrice_smul (hz : (martingaleProbVectors z).Nonempty) (Y : Fin N → ℝ)
    {c : ℝ} (hc : 0 ≤ c) :
    superhedgingPrice z (fun n ↦ c * Y n) = c * superhedgingPrice z Y := by
  rcases hc.eq_or_lt with rfl | hc
  · obtain ⟨q, hq⟩ := hz
    have h0 : (fun n ↦ (0 : ℝ) * Y n) = 0 := funext fun n ↦ zero_mul _
    rw [h0, zero_mul]
    exact le_antisymm (superhedgingPrice_le ⟨q, hq⟩ (x := 0) (θ := 0) fun n ↦ by simp)
      (by simpa using le_superhedgingPrice hq 0)
  · refine le_antisymm ?_ ?_
    · have : superhedgingPrice z (fun n ↦ c * Y n) / c ≤ superhedgingPrice z Y :=
        le_superhedgingPrice_of_forall fun x θ hs ↦ by
          rw [div_le_iff₀ hc]
          linarith [superhedgingPrice_le hz (hs.smul hc.le)]
      linarith [(div_le_iff₀ hc).1 this]
    · refine le_superhedgingPrice_of_forall fun x θ hs ↦ ?_
      have hs' := hs.smul (inv_nonneg.2 hc.le)
      simp only [inv_mul_cancel_left₀ hc.ne'] at hs'
      calc c * superhedgingPrice z Y ≤ c * (c⁻¹ * x) :=
            mul_le_mul_of_nonneg_left (superhedgingPrice_le hz hs') hc.le
        _ = x := mul_inv_cancel_left₀ hc.ne' x

/-- **Subadditivity**: the superhedging price of a sum is at most the sum of the prices. -/
theorem superhedgingPrice_add_le (hz : (martingaleProbVectors z).Nonempty) (Y Y' : Fin N → ℝ) :
    superhedgingPrice z (fun n ↦ Y n + Y' n) ≤ superhedgingPrice z Y + superhedgingPrice z Y' := by
  have : superhedgingPrice z (fun n ↦ Y n + Y' n) - superhedgingPrice z Y' ≤
      superhedgingPrice z Y :=
    le_superhedgingPrice_of_forall fun x θ hs ↦ by
      have : superhedgingPrice z (fun n ↦ Y n + Y' n) - x ≤ superhedgingPrice z Y' :=
        le_superhedgingPrice_of_forall fun x' θ' hs' ↦ by
          linarith [superhedgingPrice_le hz (hs.add hs')]
      linarith
  linarith

/-- **The superhedging price is a coherent risk measure.** On the one-period finite-state market
`z` with a martingale probability vector, and a reference measure `P` charging every state,
the superhedging price of a claim, read as a loss, is monotone, cash-invariant, positively
homogeneous and subadditive (`IsCoherentRiskMeasure`). -/
theorem isCoherentRiskMeasure_superhedgingPrice (hz : (martingaleProbVectors z).Nonempty)
    {P : Measure (Fin N)} (hP : ∀ n, P {n} ≠ 0) :
    IsCoherentRiskMeasure P (superhedgingPrice z) where
  mono Y Y' _ _ hae := superhedgingPrice_mono hz
    ((ae_iff_forall_of_singleton_ne_zero (p := fun n ↦ Y n ≤ Y' n) hP).1 hae)
  add_const _ _ m := superhedgingPrice_add_const hz _ m
  const_mul _ _ _ hc := superhedgingPrice_smul hz _ hc
  add_le _ _ _ _ := superhedgingPrice_add_le hz _ _

/-- **The representing set of the superhedging price is the set of martingale probability
vectors.** A vector pricing every claim of nonpositive superhedging price at most `0` is a
martingale vector: the gain `∑ₘ θₘ zₘ·` of a portfolio `θ` is superreplicated at capital `0` by
`θ`, so `q` prices it at most `0`, and applying this to `±` a basis vector gives
`∑ₙ qₙ zₘₙ = 0`. Conversely a martingale vector prices a claim at most its superhedging price
(`le_superhedgingPrice`). -/
theorem representingSet_superhedgingPrice (hz : (martingaleProbVectors z).Nonempty) :
    representingSet (superhedgingPrice z) = martingaleProbVectors z := by
  ext q
  refine ⟨fun ⟨hq0, hq1, hq⟩ ↦ ⟨hq0, hq1, fun m ↦ ?_⟩, fun hq ↦ ⟨hq.1, hq.2.1, fun Z hZ ↦ ?_⟩⟩
  · have key (θ : Fin M → ℝ) : ∑ n, q n * ∑ m, θ m * z m n ≤ 0 :=
      hq (fun n ↦ ∑ m, θ m * z m n) (superhedgingPrice_le hz (x := 0) (θ := θ) fun n ↦ by simp)
    have hsingle (c : ℝ) : ∑ n, q n * ∑ m', (Pi.single m c : Fin M → ℝ) m' * z m' n =
        c * ∑ n, q n * z m n := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ ↦ ?_
      rw [Finset.sum_eq_single m (fun b _ hb ↦ by rw [Pi.single_eq_of_ne hb, zero_mul])
        fun h ↦ absurd (Finset.mem_univ m) h, Pi.single_eq_same]
      ring
    have h1 := key (Pi.single m 1)
    have h2 := key (Pi.single m (-1))
    rw [hsingle] at h1 h2
    linarith
  · exact (le_superhedgingPrice hq Z).trans hZ

/-- **Superhedging duality.** With a martingale probability vector, the superhedging price of a
claim is the least upper bound of its prices `∑ qₙ Yₙ` under the martingale probability vectors:
the representation `coherentRisk_isLUB` of the coherent risk measure `superhedgingPrice z`,
over its representing set `representingSet_superhedgingPrice`. -/
theorem superhedgingPrice_isLUB (hz : (martingaleProbVectors z).Nonempty) (Y : Fin N → ℝ) :
    IsLUB ((fun q ↦ ∑ n, q n * Y n) '' martingaleProbVectors z) (superhedgingPrice z Y) := by
  have hP : ∀ n, (Measure.count : Measure (Fin N)) {n} ≠ 0 := fun n ↦ by simp
  simpa only [representingSet_superhedgingPrice hz] using
    coherentRisk_isLUB (isCoherentRiskMeasure_superhedgingPrice hz hP) Y

/-! ### The joint with `Market`: a pricing measure prices below the superhedging price -/

section MarketBridge

open MathFin.Contracts

variable {K L : ℕ}

/-- The **deflated excess returns** of a market on `L` states up to `T`, the excess-return matrix
`z` of the superhedging theory: `z k ω = (N 0 / N T)(ω) · S_k(T)(ω) − pr k`, the deflated terminal
price of asset `k` less its initial price `pr k`. -/
noncomputable def Market.excessReturn (mk : Market (Fin K) (Fin L)) (T : ℝ≥0)
    (pr : Fin K → ℝ) : Fin K → Fin L → ℝ :=
  fun k ω ↦ mk.deflator T ω * mk.asset k T ω - pr k

/-- **A pricing measure is a martingale probability vector of the deflated excess returns.** If
`Q` prices the market up to `T` and the numéraire and the asset prices at `0` are deterministic
(`n₀` and `pr`), the masses `Q {ω}` are a member of `martingaleProbVectors` of
`Market.excessReturn`: they are nonnegative and sum to `1`, and `𝔼_Q[(N 0 / N T) S_k(T)] = pr k`
because the deflated asset is a `Q`-martingale. -/
theorem Market.IsPricingMeasure.mem_martingaleProbVectors {mk : Market (Fin K) (Fin L)}
    {T : ℝ≥0} {Q : Measure (Fin L)} (hQ : mk.IsPricingMeasure T Q) {n₀ : ℝ}
    (hN₀ : ∀ ω, mk.numeraire 0 ω = n₀) {pr : Fin K → ℝ} (hpr : ∀ k ω, mk.asset k 0 ω = pr k) :
    (fun ω ↦ Q.real {ω}) ∈ martingaleProbVectors (mk.excessReturn T pr) := by
  have := hQ.isProb
  have hsum : ∑ ω, Q.real {ω} = 1 := by
    have h := integral_fintype (f := fun _ : Fin L ↦ (1 : ℝ)) (μ := Q) Integrable.of_finite
    simpa using h.symm
  refine ⟨fun ω ↦ measureReal_nonneg, hsum, fun k ↦ ?_⟩
  have h : ∫ ω, mk.deflator T ω * mk.asset k T ω ∂Q = ∫ ω, mk.asset k 0 ω ∂Q := by
    rw [← hQ.price_pay_obs hN₀ k le_rfl, Market.price, Contract.value_pay]
    simp [Payoff.eval, scenarioAt]
  have h0 : ∫ ω, mk.asset k 0 ω ∂Q = pr k := by simp [hpr k]
  have h1 := integral_fintype (μ := Q) (f := fun ω ↦ mk.deflator T ω * mk.asset k T ω)
    Integrable.of_finite
  simp only [smul_eq_mul] at h1
  have e : ∑ ω, Q.real {ω} * Market.excessReturn mk T pr k ω =
      (∑ ω, Q.real {ω} * (mk.deflator T ω * mk.asset k T ω)) - pr k * ∑ ω, Q.real {ω} := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ω _ ↦ by simp only [Market.excessReturn]; ring
  rw [e, hsum]
  linarith

/-- **The state-price value of a claim is at most its superhedging price.** In a market on finitely
many states with a pricing measure `Q` up to `T` and deterministic initial numéraire and prices,
the price of the payment `Y` at `T`, `∑ ω, (N 0 / N T)(ω) Q {ω} Y ω` (`Market.statePrice`), is at
most the superhedging price of the deflated claim `(N 0 / N T) Y` in the deflated excess returns:
no portfolio superreplicates it more cheaply. -/
theorem Market.IsPricingMeasure.statePricePricing_le_superhedgingPrice
    {mk : Market (Fin K) (Fin L)} {T : ℝ≥0} {Q : Measure (Fin L)}
    (hQ : mk.IsPricingMeasure T Q) {n₀ : ℝ} (hN₀ : ∀ ω, mk.numeraire 0 ω = n₀) {pr : Fin K → ℝ}
    (hpr : ∀ k ω, mk.asset k 0 ω = pr k) (Y : Fin L → ℝ) :
    statePricePricing Finset.univ (mk.statePrice Q T) Y ≤
      superhedgingPrice (mk.excessReturn T pr) fun ω ↦ mk.deflator T ω * Y ω := by
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun ω _ ↦ ?_))
    (le_superhedgingPrice (hQ.mem_martingaleProbVectors hN₀ hpr) fun ω ↦ mk.deflator T ω * Y ω)
  simp only [Market.statePrice]
  ring

/-- **A contract's market price is at most the superhedging price of its payoff**: for a payment of
`a` at `T`, `mk.price Q (.pay T a)` is at most the superhedging price, in the deflated excess
returns, of the deflated payoff `(N 0 / N T) a`. The market price under any pricing measure `Q`
is a lower bound of the cost of every superreplication, which is the one-sided half of the duality
`superhedgingPrice_isLUB`. -/
theorem Market.IsPricingMeasure.price_pay_le_superhedgingPrice
    {mk : Market (Fin K) (Fin L)} {T : ℝ≥0} {Q : Measure (Fin L)}
    (hQ : mk.IsPricingMeasure T Q) {n₀ : ℝ} (hN₀ : ∀ ω, mk.numeraire 0 ω = n₀) {pr : Fin K → ℝ}
    (hpr : ∀ k ω, mk.asset k 0 ω = pr k) (a : Payoff (Fin K)) :
    mk.price Q (.pay T a) ≤ superhedgingPrice (mk.excessReturn T pr)
      fun ω ↦ mk.deflator T ω * a.eval (scenarioAt mk.asset ω) := by
  haveI := hQ.isProb
  rw [Market.price_pay_eq_statePricePricing]
  exact hQ.statePricePricing_le_superhedgingPrice hN₀ hpr _

end MarketBridge

end MathFin
