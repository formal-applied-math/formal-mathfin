/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Pricing.MarketCompletenessInPrice
public import MathFin.Pricing.Market

/-!
# The hedge rung: a contract's value is the cost of its hedge

`Contract.value` prices a contract as an expectation of its discounted cash flows
(`Pricing/Value.lean`). `Pricing/MarketCompletenessInPrice.lean` shows that in the Brownian market
every square-integrable claim known at `T` is the terminal wealth `𝔼[H] + ∫₀ᵀ ψ dS` of a unique
holding `ψ` in the discounted price `S = S₀ + (σ●B)`. This file joins the two: the claim is the
deflated present value `c.pathPV` of a contract `c`, and the initial wealth `𝔼[H]` is, by
definition of `value`, `c.value`.

The only new work is that a contract's cash flows *are* such a claim:

* they are known at `T`, because every date the contract observes or pays on is `≤ T` and the
  model and the deflator are adapted to the Brownian filtration
  (`Contract.measurable_pathPV_of_le`);
* they are square-integrable, which is a hypothesis (`hL2`), discharged for a bounded model and a
  deterministic discount factor by `Contract.exists_bound_pathPV`.

No notion of replication is introduced: `ψ` is the holding of
`exists_replicating_strategy_in_price`, and the wealth is its `∫ ψ dS`.

## Scope

The wealth is stated in **discounted units**: the identity is
`pathPV = value + ∫₀ᵀ ψ dS` almost surely, the total discounted cash flow of the contract against
the initial capital plus the discounted trading gains. For a deterministic discount factor that is
the cash flows rolled to `T` at the bank account and discounted back; a cash flow paid before `T`
is read as held in the numéraire until `T`, which this file does not model as a strategy. The
identity holds for every contract of the language that pays at fixed dates, with one price
`S = S₀ + (σ●B)` for all of them.

The contract's model `X` is any process adapted to the Brownian filtration; it is **not** required
to be a function of the price `S`, and nothing here identifies `S` with a traded asset of `X`. A
market whose asset is the contract's underlying needs the identification of that asset's discounted
price with `S₀ + (σ●B)` (the Itô integral of its volatility), which is not proved here. So this
file proves that the value of a contract is the initial capital of *a* replicating holding in a
complete Brownian price, not that it is the cost of hedging the contract's own underlying.

## Main results

* `Contract.exists_unique_hedge_in_price` — a fixed-dated contract whose observations and payment
  dates lie in `[0, T]`, on a Brownian-adapted model and deflator, with square-integrable
  discounted cash flows, is replicated by a unique holding in the price, with initial wealth
  `Contract.value`.
* `Contract.exists_unique_hedge_in_price_of_bounded` — the same for a bounded model and a
  deterministic discount factor, with no integrability hypothesis.
* `Market.exists_unique_hedge_in_price` — the same for a `Market` whose filtration is the Brownian
  one: the initial wealth is `Market.price`.

## References

* [I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991], 1.6
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], 5.4
* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]

## Tags

replication, hedging strategy, contract value, complete market, martingale representation,
stochastic integral against price, MSC 91G20, MSC 60H05, JEL G13
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathFin ItoIntegralCLM ItoIntegralAgainstMartingale ItoIntegralL2
open scoped NNReal

namespace MathFin.Contracts

variable {ι Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- **A contract's value is the initial capital of its hedge in the price.** Let `B` be a Brownian
motion with continuous paths, `S = S₀ + (σ●B)` the discounted price with volatility `σ ≠ 0` a.e.,
and `c` a contract that pays at fixed dates, observing and paying only at dates `≤ T`, on a model
`X` and deflator `D` adapted to the Brownian filtration. If its discounted cash flows
`c.pathPV` are square-integrable, there is a **unique** holding `ψ` in the price with

  `c.pathPV = c.value + ∫₀ᵀ ψ dS`  almost surely,

so the contract's total discounted cash flow is the terminal discounted wealth of a strategy started
from `c.value`. The claim is `Contract.pathPV` itself, not a model-specific closed form: every term
of the contract language that pays at fixed dates is covered. -/
theorem Contract.exists_unique_hedge_in_price (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (T : ℝ≥0)
    (σ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hσ : ∀ᵐ z ∂(trimMeasure (μ := μ) T hBmeas), (σ : ℝ≥0 × Ω → ℝ) z ≠ 0)
    {c : Contract ι} (hc : c.FixedDated) {D : ℝ≥0 → Ω → ℝ} {X : ι → ℝ≥0 → Ω → ℝ}
    (hD : ∀ t, Measurable[natFiltration hBmeas t] (D t))
    (hX : ∀ i t, Measurable[natFiltration hBmeas t] (X i t))
    (hobs : ∀ p ∈ c.obsList, p.2 ≤ T) (hdates : ∀ t ∈ c.dates, t ≤ T)
    (hL2 : MemLp (fun ω ↦ c.pathPV (fun t ↦ D t ω) (scenarioAt X ω)) 2 μ) :
    ∃! ψ : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas σ),
      (fun ω ↦ c.pathPV (fun t ↦ D t ω) (scenarioAt X ω)) =ᵐ[μ]
        fun ω ↦ c.value μ D X + (itoIntegralAgainstCLM hB T hBmeas σ ψ : Ω → ℝ) ω := by
  have hmeas : Measurable[natFiltration hBmeas T]
      fun ω ↦ c.pathPV (fun t ↦ D t ω) (scenarioAt X ω) :=
    Contract.measurable_pathPV_of_le (𝓕 := natFiltration hBmeas) hc hD hX hobs hdates
  obtain ⟨H, hae⟩ : ∃ H : Lp ℝ 2 μ,
      ⇑H =ᵐ[μ] fun ω ↦ c.pathPV (fun t ↦ D t ω) (scenarioAt X ω) :=
    ⟨hL2.toLp _, hL2.coeFn_toLp⟩
  have hHmeas : AEStronglyMeasurable[natFiltration hBmeas T] (⇑H) μ :=
    hmeas.stronglyMeasurable.aestronglyMeasurable.congr hae.symm
  obtain ⟨ψ, hψ, huniq⟩ := MarketCompletenessInPrice.exists_replicating_strategy_in_price
    (hB := hB) hBmeas hBcont T σ hσ H hHmeas
  have hint : ∫ ω, H ω ∂μ = c.value μ D X := integral_congr_ae hae
  have key (ψ' : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas σ)) :
      ((fun ω ↦ c.pathPV (fun t ↦ D t ω) (scenarioAt X ω)) =ᵐ[μ]
        fun ω ↦ c.value μ D X + (itoIntegralAgainstCLM hB T hBmeas σ ψ' : Ω → ℝ) ω) ↔
      (⇑H =ᵐ[μ] fun ω ↦
        (∫ ω, H ω ∂μ) + (itoIntegralAgainstCLM hB T hBmeas σ ψ' : Ω → ℝ) ω) := by
    rw [hint]
    exact ⟨fun h ↦ hae.trans h, fun h ↦ hae.symm.trans h⟩
  exact ⟨ψ, (key ψ).2 hψ, fun ψ' h ↦ huniq ψ' ((key ψ').1 h)⟩

/-- **The hedge rung with no integrability hypothesis.** On a model whose every coordinate is
bounded and adapted to the Brownian filtration, with a deterministic discount factor `D`, the
discounted cash flows of a fixed-dated contract observing and paying at dates `≤ T` are bounded,
hence square-integrable, and `Contract.exists_unique_hedge_in_price` applies. -/
theorem Contract.exists_unique_hedge_in_price_of_bounded (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (T : ℝ≥0)
    (σ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hσ : ∀ᵐ z ∂(trimMeasure (μ := μ) T hBmeas), (σ : ℝ≥0 × Ω → ℝ) z ≠ 0)
    {c : Contract ι} (hc : c.FixedDated) (D : ℝ≥0 → ℝ) {X : ι → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i t, Measurable[natFiltration hBmeas t] (X i t))
    (hXb : ∀ i t, ∃ C, ∀ ω, |X i t ω| ≤ C)
    (hobs : ∀ p ∈ c.obsList, p.2 ≤ T) (hdates : ∀ t ∈ c.dates, t ≤ T) :
    ∃! ψ : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas σ),
      (fun ω ↦ c.pathPV D (scenarioAt X ω)) =ᵐ[μ]
        fun ω ↦ c.value μ (fun t _ ↦ D t) X
          + (itoIntegralAgainstCLM hB T hBmeas σ ψ : Ω → ℝ) ω := by
  obtain ⟨C, hC⟩ := Contract.exists_bound_pathPV D hXb hc
  have hXamb (i : ι) (t : ℝ≥0) : Measurable (X i t) :=
    (hX i t).mono ((natFiltration hBmeas).le t) le_rfl
  have hmeas := Contract.measurable_pathPV hc (D := fun t _ ↦ D t) (fun t ↦ measurable_const)
    hXamb
  refine Contract.exists_unique_hedge_in_price hB hBmeas hBcont T σ hσ hc
    (D := fun t _ ↦ D t) (fun t ↦ measurable_const) hX hobs hdates ?_
  exact MemLp.of_bound hmeas.aestronglyMeasurable C
    (.of_forall fun ω ↦ (Real.norm_eq_abs _).trans_le (hC ω))

end MathFin.Contracts

namespace MathFin

variable {ι Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- **The price of a contract in a Brownian market is the initial capital of its hedge in the
price.** For a `Market` `M` whose information is the Brownian filtration, a fixed-dated contract
observing and paying at dates `≤ T`, with square-integrable cash flows deflated by `M.deflator`, is
replicated by a unique holding `ψ` in the price `S = S₀ + (σ●B)`, with initial wealth `M.price μ c`.
The price `S` is the Itô price of `exists_replicating_strategy_in_price`: nothing here asserts it is
`M`'s own deflated asset. -/
theorem Market.exists_unique_hedge_in_price {M : Market ι Ω}
    (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (hF : M.𝓕 = natFiltration hBmeas)
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (T : ℝ≥0)
    (σ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hσ : ∀ᵐ z ∂(trimMeasure (μ := μ) T hBmeas), (σ : ℝ≥0 × Ω → ℝ) z ≠ 0)
    {c : Contracts.Contract ι} (hc : c.FixedDated)
    (hobs : ∀ p ∈ c.obsList, p.2 ≤ T) (hdates : ∀ t ∈ c.dates, t ≤ T)
    (hL2 : MemLp (fun ω ↦ c.pathPV (fun t ↦ M.deflator t ω) (Contracts.scenarioAt M.asset ω))
      2 μ) :
    ∃! ψ : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas σ),
      (fun ω ↦ c.pathPV (fun t ↦ M.deflator t ω) (Contracts.scenarioAt M.asset ω)) =ᵐ[μ]
        fun ω ↦ M.price μ c + (itoIntegralAgainstCLM hB T hBmeas σ ψ : Ω → ℝ) ω := by
  have hFt (t : ℝ≥0) : M.𝓕 t = natFiltration hBmeas t := by rw [hF]
  have hD (t : ℝ≥0) : Measurable[natFiltration hBmeas t] (M.deflator t) := by
    rw [← hFt t]
    exact (M.stronglyMeasurable_deflator t).measurable
  have hX (i : ι) (t : ℝ≥0) : Measurable[natFiltration hBmeas t] (M.asset i t) := by
    rw [← hFt t]
    exact (M.asset_adapted i t).measurable
  exact Contracts.Contract.exists_unique_hedge_in_price hB hBmeas hBcont T σ hσ hc hD hX hobs
    hdates hL2

end MathFin
