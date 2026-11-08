/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Models.Binomial.Binomial
public import MathFin.Pricing.Market
public import MathFin.Probability.Martingales.TimeChange

/-!
# The binomial tree as a market

The binomial model of `Models/Binomial/Binomial.lean` as a `Market` (`Binomial.market`): coin-flip
paths `ω : ℕ → Bool` under a physical law `P`, the information of the flips made by `t`
(`flipFiltration` along the step count `t ↦ ⌊t / h⌋₊`, `Filtration.comp`), the spot after those
flips as the traded asset, and the money market `e^{ρ n}` after `n` steps as numéraire.

* **The risk-neutral law prices it.** Under no-arbitrage, i.i.d. flips that go up with the
  probability `crrUpProb u d ρ` are a pricing measure of the market at every horizon, for a physical
  law they are equivalent to (`isPricingMeasure_coinFlipMeasure`): the deflated spot is the
  discounted spot after the steps made (`deflated_market`), a martingale for the flip filtration
  (`martingale_discountedSpot`) and so along the step count (`Martingale.comp`).
* **Its price is the binomial value.** On contracts paying at whole numbers of steps the
  deflator `e^{−ρ ⌊t/h⌋}` is the binomial discount `e^{−ρ t/h}`, so the market's price is the
  `Contract.value` of `Binomial.lean` (`price_market`), and a European payoff is priced at its
  backward-induction tree price (`price_market_pay_eq_binomialPrice`).

`IsPricingMeasure` asks for a measure equivalent to `P` on the whole path space, so the physical
law is a hypothesis of `isPricingMeasure_coinFlipMeasure`, discharged by the risk-neutral law
itself.

## Main definitions

* `Binomial.market`: the binomial tree with step `h` as a `Market`.

## Main results

* `Binomial.isPricingMeasure_coinFlipMeasure`: the risk-neutral law of the flips is a pricing
  measure.
* `Binomial.price_market`: on grid dates the market's price is the binomial value.
* `Binomial.price_market_pay_eq_binomialPrice`: the price of a European payoff is its tree price.

## References

* [J. C. Cox, S. A. Ross and M. Rubinstein, *Option pricing: a simplified
  approach*][CoxRossRubinstein1979]
* [S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset Pricing Model*][ShreveSCFI],
  ch. 2

## Tags

binomial tree, Cox–Ross–Rubinstein, market, numéraire, pricing measure, risk-neutral probability,
money market, MSC 91G20, MSC 60G42, JEL G13
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MathFin.Contracts.Binomial

variable {u d ρ h : ℝ}

/-- The step count `t ↦ ⌊t / h⌋₊` is monotone for a step `h ≥ 0`. -/
theorem monotone_floor_div (hh : 0 ≤ h) : Monotone fun t : ℝ≥0 ↦ ⌊(t : ℝ) / h⌋₊ :=
  fun _ _ hst ↦ Nat.floor_mono (div_le_div_of_nonneg_right (NNReal.coe_le_coe.2 hst) hh)

/-- **The binomial market** with step `h ≥ 0`, under a physical law `P` of the flips: the
information of the flips made by `t`, the spot after them, and the money market `e^{ρ n}` after
`n` steps as numéraire. -/
noncomputable def market (P : Measure (ℕ → Bool)) (S₀ u d ρ : ℝ) (hh : 0 ≤ h) :
    Market Unit (ℕ → Bool) where
  P := P
  𝓕 := flipFiltration.comp (monotone_floor_div hh)
  asset := assets S₀ u d h
  numeraire t _ := Real.exp (ρ * ⌊(t : ℝ) / h⌋₊)
  numeraire_pos _ _ := Real.exp_pos _
  asset_adapted _ t := (stronglyMeasurable_flipFiltration_iff (n := ⌊(t : ℝ) / h⌋₊)).2
    (pathAdaptedAt_spotPath S₀ u d _)
  numeraire_adapted _ := stronglyMeasurable_const

/-- The deflated spot of the binomial market is the discounted spot after the steps made. -/
theorem deflated_market (P : Measure (ℕ → Bool)) (S₀ : ℝ) (hh : 0 ≤ h) (t : ℝ≥0) :
    (market P S₀ u d ρ hh).deflated () t = discountedSpot S₀ u d ρ ⌊(t : ℝ) / h⌋₊ := by
  funext ω
  simp only [Market.deflated, market, assets, discountedSpot, Real.exp_neg, div_eq_inv_mul]

variable {q : ℝ≥0} (hq : q ≤ 1)

/-- **The risk-neutral law of the flips prices the binomial market.** Under no-arbitrage, i.i.d.
flips that go up with the probability `crrUpProb u d ρ` are a pricing measure at every horizon, for
a physical law `P` they are equivalent to: the deflated spot is the discounted spot after the steps
made, a martingale for the flip filtration (`martingale_discountedSpot`), and so for its time
change along the step count. -/
theorem isPricingMeasure_coinFlipMeasure (hna : BinomialNoArb u d ρ)
    (hqcrr : crrUpProb u d ρ = q) (S₀ : ℝ) (hh : 0 ≤ h) {P : Measure (ℕ → Bool)}
    (hP : IsEquivProbMeasure P (coinFlipMeasure q hq)) (T : ℝ≥0) :
    (market P S₀ u d ρ hh).IsPricingMeasure T (coinFlipMeasure q hq) := by
  have hM : Martingale (fun t ↦ (market P S₀ u d ρ hh).deflated () t)
      (market P S₀ u d ρ hh).𝓕 (coinFlipMeasure q hq) := by
    simp only [deflated_market]
    exact (martingale_discountedSpot hna S₀ hq hqcrr).comp (monotone_floor_div hh)
  exact ⟨hP, fun ⟨⟩ ↦ (IsEMM.of_martingale hM hP.ac hP.ac' T).martingale⟩

/-- **On grid dates the binomial market's price is the binomial value**: for a fixed-dated
contract paying only at whole numbers of steps, the deflator `e^{−ρ ⌊t/h⌋}` is the discount
`e^{−ρ t/h}` of `Binomial.lean`, under any measure `Q`. -/
theorem price_market (P Q : Measure (ℕ → Bool)) (S₀ : ℝ) (hh : 0 ≤ h) {c : Contract Unit}
    (hc : c.FixedDated) (hgrid : ∀ t ∈ c.dates, ∃ n : ℕ, (t : ℝ) / h = n) :
    (market P S₀ u d ρ hh).price Q c
      = c.value Q (fun t _ ↦ discount ρ h t) (assets S₀ u d h) := by
  simp only [Market.price, Contract.value]
  refine integral_congr_ae (.of_forall fun ω ↦ c.pathPV_congr hc (fun t ht ↦ ?_) fun _ _ ↦ rfl)
  obtain ⟨n, hn⟩ := hgrid t ht
  simp [Market.deflator, market, discount, hn, Real.exp_neg]

/-- **The price of a European payoff in the binomial market is its tree price.** Under the
risk-neutral law, a cash flow at `T`, on step `N`, paying `g` of the spot at `T`, is priced at the
backward-induction price `binomialPrice u d ρ g N S₀`. -/
theorem price_market_pay_eq_binomialPrice (hqcrr : crrUpProb u d ρ = q) (P : Measure (ℕ → Bool))
    (S₀ : ℝ) (hh : 0 ≤ h) {T : ℝ≥0} {N : ℕ} (hTN : (T : ℝ) / h = N) {a : Payoff Unit}
    {g : ℝ → ℝ} (hg : ∀ s : Scenario Unit, a.eval s = g (s () T)) :
    (market P S₀ u d ρ hh).price (coinFlipMeasure q hq) (.pay T a)
      = binomialPrice u d ρ g N S₀ := by
  rw [price_market P _ S₀ hh (c := .pay T a) trivial fun t ht ↦
    ⟨N, by rw [show t = T by simpa [Contract.dates] using ht]; exact hTN⟩]
  exact value_pay_eq_binomialPrice hq hqcrr S₀ hTN hg

end MathFin.Contracts.Binomial
