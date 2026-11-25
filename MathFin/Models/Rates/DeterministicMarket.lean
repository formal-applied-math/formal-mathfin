/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Pricing.Market
public import MathFin.Pricing.BondPrice
public import MathFin.Models.Rates.DeterministicCurve
public import MathFin.Models.Rates.Immunization
public import MathFin.Models.Rates.KeyRateDuration

/-!
# The deterministic-rates bond market

The simplest term-structure model as a `Market`: a deterministic bank account `N`
(`N t = e^{rt}` for a flat rate) as numéraire, and zero-coupon bonds `P(t, τᵢ) = N t / N τᵢ` as
the traded assets (`deterministicMarket`). After its maturity a bond is worth what its proceeds
earn in the bank account, so the formula holds at every date and the bond is a self-financing
position. Nothing is random, so every probability measure is a pricing measure
(`isPricingMeasure_deterministicMarket`): the deflated bond `P(t, τᵢ) / N t = 1 / N τᵢ` is
constant.

In any market with a deterministic numéraire a schedule of fixed cash flows is worth its flows
discounted by `N 0 / N` (`price_fixedFlows_deterministicMarket`), and the price of a unit payment
at `τᵢ` is the bond's price (`price_pay_deterministicMarket`). The first-order immunization and
the key-rate durations of `Models/Rates/` differentiate such a flat-rate value, and the value
of a zero-coupon portfolio is the price of its schedule when the numéraire is `e^{rt}`, and the
price of a coupon bond at an annually compounded yield `y` is the price of its schedule when the
numéraire is `(1 + y)^⌊t⌋` (`bondPortfolioValue_eq_price`).

The library's canonical bond price is `Contracts.bondPrice` (`P(t, T) = 𝔼_Q[D T ∣ 𝓕 t] / D t`,
`Pricing/BondPrice.lean`), and three deterministic bond formulas are tied to it. The flat-rate bond
`zcb r t T` is `P(t, T)` at the curve `D s = e^{−rs}` (`bondPrice_exp_eq_zcb`), and it is the
market's price at `t` of one unit paid at `T` whenever the numéraire is `e^{rt}`
(`priceAt_pay_eq_zcb`). The key-rate price is `∑ cᵢ P(0, tᵢ)` with one curve per cash flow, and the
coupon bond at an annually compounded yield is its flat case
(`bondPriceKeyRate_eq_sum_bondPrice`, `bondPriceDisc_eq_sum_bondPrice`).

The stochastic short-rate models (`Models/Rates/ShortRate.lean`) price the same schedules through
their zero curve; that their bonds are martingales after deflation by the bank account is not
proved here.

## Main definitions

* `MathFin.Rates.deterministicMarket`: the market of a deterministic numéraire with zero-coupon
  bonds of given maturities.

## Main results

* `MathFin.Rates.isPricingMeasure_deterministicMarket`: every probability measure prices the
  deterministic bond market, at every horizon.
* `MathFin.Rates.price_pay_deterministicMarket`: the price of a unit payment at `τᵢ` is the
  bond's market price `N 0 / N τᵢ`.
* `MathFin.Rates.price_fixedFlows_deterministicMarket`: a schedule of fixed cash flows is worth
  its flows discounted by the numéraire.
* `MathFin.Rates.bondPortfolioValue_eq_price_exp`, `bondPriceDisc_eq_price`: the flat-rate value of
  a zero-coupon portfolio (numéraire `e^{rt}`) and the annually compounded price of a coupon bond
  (numéraire `(1 + y)^⌊t⌋`) are market prices.
* `MathFin.Rates.bondPortfolioValue_eq_price`: the two in one conjunction.
* `MathFin.Rates.bondPrice_exp_eq_zcb`, `MathFin.Rates.priceAt_pay_eq_zcb`: at the discount curve
  `e^{−rs}` the bond price `P(t, T)` is `zcb r t T`, and so is the market price at `t` of one unit
  paid at `T` when the numéraire is `e^{rt}`.
* `MathFin.Rates.bondPriceKeyRate_eq_sum_bondPrice`, `MathFin.Rates.bondPriceDisc_eq_sum_bondPrice`:
  the key-rate price is `∑ cᵢ P(0, tᵢ)`, each cash flow at its own curve `(1 + kᵢ)^{−⌊u⌋}`, and the
  coupon bond at a yield is the flat case.
* `MathFin.Rates.bondPriceKeyRate_eq_price_deterministicMarket`: for distinct tenors the key-rate
  price is the price of the schedule in the deterministic bond market of one discount curve.
* `MathFin.Rates.price_immunization_first_order`: first-order immunization stated for the market
  prices of the asset and liability schedules, in a family of markets with numéraires `e^{rt}`.
* `MathFin.Rates.sum_deriv_keyRate_eq_deriv_price`: the key-rate partials of a coupon bond sum to
  the derivative in `y` of the market price of its cash flows, in a family of markets with
  numéraires `(1 + y)^⌊t⌋`.

## References

* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  Section 1.5
* [Fabozzi, *Fixed Income Mathematics*][FabozziFIM], Ch 5
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], ch. 4
* [Redington (1952)][Redington1952]

## Tags

term structure, zero-coupon bond, bank account, pricing measure, deterministic interest rates,
bond immunization, MSC 91G30, JEL E43, JEL G12
-/

@[expose] public section

open MeasureTheory MathFin.Contracts
open scoped NNReal

namespace MathFin.Rates

variable {ι Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **The deterministic-rates bond market**: the physical measure `P`, the trivial filtration,
the deterministic numéraire `N` (the bank account), and for each `i` the zero-coupon bond of
maturity `τ i`, worth `N t / N (τ i)` at `t`. -/
noncomputable def deterministicMarket (P : Measure Ω) (N : ℝ≥0 → ℝ) (hN : ∀ t, 0 < N t)
    (τ : ι → ℝ≥0) : Market ι Ω where
  P := P
  𝓕 := Filtration.const ℝ≥0 ⊥ bot_le
  asset i t _ := N t / N (τ i)
  numeraire t _ := N t
  numeraire_pos t _ := hN t
  asset_adapted _ _ := stronglyMeasurable_const
  numeraire_adapted _ := stronglyMeasurable_const

/-- **Every probability measure prices the deterministic bond market.** The deflated bond
`(N t / N τᵢ) / N t = 1 / N τᵢ` is constant in time and in the outcome, hence a martingale. -/
theorem isPricingMeasure_deterministicMarket (P : Measure Ω) [IsProbabilityMeasure P]
    (N : ℝ≥0 → ℝ) (hN : ∀ t, 0 < N t) (τ : ι → ℝ≥0) (T : ℝ≥0) :
    (deterministicMarket P N hN τ).IsPricingMeasure T P :=
  ⟨inferInstance, Measure.AbsolutelyContinuous.refl _, Measure.AbsolutelyContinuous.refl _,
    fun i ↦ by
      have h : (fun t (ω : Ω) ↦ (deterministicMarket P N hN τ).deflated i (min t T) ω)
          = fun _ _ ↦ 1 / N (τ i) := by
        funext t ω
        have := (hN (min t T)).ne'
        simp only [Market.deflated, deterministicMarket]
        field_simp
      rw [h]
      exact martingale_const _ _ _⟩

/-- **The price of a unit payment at `τᵢ` is the bond's price.** In the deterministic bond market
the unit payment at `τ i` is worth the bond's price `N 0 / N (τ i)` today, under any probability
measure. -/
theorem price_pay_deterministicMarket (P : Measure Ω) (N : ℝ≥0 → ℝ) (hN : ∀ t, 0 < N t)
    (τ : ι → ℝ≥0) (Q : Measure Ω) [IsProbabilityMeasure Q] (i : ι) (ω : Ω) :
    (deterministicMarket P N hN τ).price Q (.pay (τ i) (.const 1))
      = (deterministicMarket P N hN τ).asset i 0 ω := by
  rw [Market.price, Contract.value_pay]
  simp [Payoff.eval, Market.deflator, deterministicMarket]

/-- **A schedule of fixed cash flows is worth its flows discounted by the numéraire**: in the
deterministic bond market, `∑ cᵢ N 0 / N (tᵢ)`, under any probability measure. -/
theorem price_fixedFlows_deterministicMarket (P : Measure Ω) (N : ℝ≥0 → ℝ)
    (hN : ∀ t, 0 < N t) (τ : ι → ℝ≥0) (Q : Measure Ω) [IsProbabilityMeasure Q]
    (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ) :
    (deterministicMarket P N hN τ).price Q (fixedFlows t c n)
      = ∑ i ∈ Finset.range n, N 0 / N (t i) * c i :=
  value_fixedFlows_deterministic (fun s ↦ N 0 / N s) _ t c n

/-- **The flat-rate value of a bond portfolio is a market price.** In any market with the money
market `e^{rt}` as numéraire, under any probability measure `Q`, the portfolio of zero-coupon
bonds of face `w i` and maturity `T i ≥ 0` (`bondPortfolioValue` at time `0`) is the price of the
schedule `fixedFlows`. -/
theorem bondPortfolioValue_eq_price_exp (Q : Measure Ω) [IsProbabilityMeasure Q] (n : ℕ)
    (w T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) (M : Market ι Ω) (r : ℝ)
    (hM : ∀ t ω, M.numeraire t ω = Real.exp (r * t)) :
    MathFin.bondPortfolioValue (Finset.range n) w T 0 r =
      M.price Q (fixedFlows (fun i ↦ (T i).toNNReal) w n) := by
  have hD : M.deflator = fun (s : ℝ≥0) _ ↦ Real.exp (-(r * s)) := by
    funext s ω
    simp only [Market.deflator_of_numeraire_exp hM, neg_mul]
  rw [Market.price, hD, value_fixedFlows_deterministic, MathFin.bondPortfolioValue]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Real.coe_toNNReal _ (hT i), sub_zero]
  ring

/-- **The annually compounded price of a coupon bond is a market price.** In any market with the
numéraire `(1 + y)^⌊t⌋`, under any probability measure `Q`, the coupon bond at the annually
compounded yield `y` (`bondPriceDisc`) is the price of its cash flows. -/
theorem bondPriceDisc_eq_price (Q : Measure Ω) [IsProbabilityMeasure Q] (n : ℕ)
    (w : ℕ → ℝ) (M : Market ι Ω) (y : ℝ) (t : ℕ → ℕ)
    (hM : ∀ s ω, M.numeraire s ω = (1 + y) ^ ⌊s⌋₊) :
    MathFin.bondPriceDisc (Finset.range n) t w y =
      M.price Q (fixedFlows (fun i ↦ ((t i : ℕ) : ℝ≥0)) w n) := by
  have hD : M.deflator = fun (s : ℝ≥0) _ ↦ ((1 + y) ^ ⌊s⌋₊)⁻¹ := by
    funext s ω
    simp only [Market.deflator_of_numeraire hM, Nat.floor_zero, pow_zero, one_div]
  rw [Market.price, hD, value_fixedFlows_deterministic, MathFin.bondPriceDisc]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Nat.floor_natCast]
  ring

/-- **The flat-rate value of a bond portfolio and the discrete price of a coupon bond are market
prices** (`bondPortfolioValue_eq_price_exp`, `bondPriceDisc_eq_price`): the two facts in one
statement, one per numéraire, `e^{rt}` and `(1 + y)^⌊t⌋`. -/
theorem bondPortfolioValue_eq_price (Q : Measure Ω) [IsProbabilityMeasure Q] (n : ℕ)
    (w T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) :
    (∀ (M : Market ι Ω) (r : ℝ), (∀ t ω, M.numeraire t ω = Real.exp (r * t)) →
      MathFin.bondPortfolioValue (Finset.range n) w T 0 r =
        M.price Q (fixedFlows (fun i ↦ (T i).toNNReal) w n)) ∧
    (∀ (M : Market ι Ω) (y : ℝ) (t : ℕ → ℕ),
      (∀ s ω, M.numeraire s ω = (1 + y) ^ ⌊s⌋₊) →
      MathFin.bondPriceDisc (Finset.range n) t w y =
        M.price Q (fixedFlows (fun i ↦ ((t i : ℕ) : ℝ≥0)) w n)) :=
  ⟨fun M r hM ↦ bondPortfolioValue_eq_price_exp Q n w T hT M r hM,
    fun M y t hM ↦ bondPriceDisc_eq_price Q n w M y t hM⟩

/-! ### The deterministic bond formulas and the bond price

`zcb` is the bond price `Contracts.bondPrice` at the curve `e^{−rs}`; `bondPriceKeyRate` and
`bondPriceDisc` are sums of cash flows times it (`bondPrice_deterministic`). -/

/-- **Under a constant short rate the bond price is `zcb`**: at the money-market discount factor
`D s = e^{−rs}`, under any finite measure and any information, the price at `t` of one unit paid
at `T` is `zcb r t T = e^{−r(T−t)}`, on either side of maturity. -/
theorem bondPrice_exp_eq_zcb (Q : Measure Ω) [IsFiniteMeasure Q] (𝓕 : Filtration ℝ≥0 mΩ)
    (r : ℝ) (t T : ℝ≥0) :
    bondPrice Q 𝓕 (fun s _ ↦ Real.exp (-(r * s))) t T = fun _ ↦ MathFin.zcb r t T := by
  rw [bondPrice_deterministic]
  funext ω
  rw [MathFin.zcb, ← Real.exp_sub]
  congr 1
  ring

/-- **`zcb` is the market price of the zero-coupon bond**: in any market whose numéraire is the
money market `e^{rt}`, under any finite measure, the price at `t` of one unit paid at `T` is
`zcb r t T` (`Market.priceAt_pay_one_of_numeraire`). -/
theorem priceAt_pay_eq_zcb (M : Market ι Ω) (Q : Measure Ω) [IsFiniteMeasure Q] {r : ℝ}
    (hN : ∀ t ω, M.numeraire t ω = Real.exp (r * t)) (t T : ℝ≥0) :
    M.priceAt Q t (.pay T (.const 1)) = fun _ ↦ MathFin.zcb r t T := by
  rw [Market.priceAt_pay_one_of_numeraire (f := fun s ↦ Real.exp (r * s)) hN]
  funext ω
  rw [MathFin.zcb, ← Real.exp_sub]
  congr 1
  ring

/-- **The key-rate price is a sum of bond prices, one curve per cash flow**: the key-rate price
`bondPriceKeyRate` of the cash flows `c i` at the integer dates `t i` is `∑ c i · P(0, t i)`, where
`P` is the bond price at the cash flow's own curve `D u = (1 + k i)^{−⌊u⌋}`, under any finite
measure and any information. The identity holds for every `k`; the curve is a discount curve, so
that `P(0, t i)` is a bond price, when `k i > −1`. -/
theorem bondPriceKeyRate_eq_sum_bondPrice {κ : Type*} (Q : Measure Ω) [IsFiniteMeasure Q]
    (𝓕 : Filtration ℝ≥0 mΩ) (s : Finset κ) (t : κ → ℕ) (c k : κ → ℝ) (ω : Ω) :
    MathFin.bondPriceKeyRate s t c k =
      ∑ i ∈ s, c i * bondPrice Q 𝓕 (fun u _ ↦ ((1 + k i) ^ ⌊u⌋₊)⁻¹) 0 (t i) ω := by
  simp [bondPrice_deterministic, MathFin.bondPriceKeyRate, div_eq_mul_inv]

/-- **The key-rate price is a market price on one discount curve.** If the tenors `t i`, `i < n`,
are distinct (`Set.InjOn t`) and each node rate has `1 + k i > 0`, there is a single deterministic
numéraire `N` with `N 0 = 1` and `N (t i) = (1 + k i)^{t i}`, and the key-rate price
`bondPriceKeyRate` of the cash flows `c i` is the price of their schedule in the deterministic bond
market of `N`, under any probability measure. Distinct tenors are what let one curve carry every
node: a repeated tenor with two different rates has no single discount factor. -/
theorem bondPriceKeyRate_eq_price_deterministicMarket (P Q : Measure Ω) [IsProbabilityMeasure Q]
    (τ : ι → ℝ≥0) (n : ℕ) (t : ℕ → ℕ) (c k : ℕ → ℝ) (hk : ∀ i < n, 0 < 1 + k i)
    (hinj : Set.InjOn t (Finset.range n)) :
    ∃ (N : ℝ≥0 → ℝ) (hN : ∀ s, 0 < N s), N 0 = 1 ∧
      MathFin.bondPriceKeyRate (Finset.range n) t c k =
        (deterministicMarket P N hN τ).price Q (fixedFlows (fun i ↦ ((t i : ℕ) : ℝ≥0)) c n) := by
  classical
  let N : ℝ≥0 → ℝ := fun u ↦
    if h : ∃ i < n, ((t i : ℕ) : ℝ≥0) = u then (1 + k h.choose) ^ t h.choose else 1
  have hNt (i : ℕ) (hi : i < n) : N (t i) = (1 + k i) ^ t i := by
    have h : ∃ j < n, ((t j : ℕ) : ℝ≥0) = t i := ⟨i, hi, rfl⟩
    have hj : h.choose = i := hinj (by simpa using h.choose_spec.1) (by simpa using hi)
      (Nat.cast_injective h.choose_spec.2)
    simp only [N, dif_pos h, hj]
  have hN : ∀ u, 0 < N u := fun u ↦ by
    by_cases h : ∃ i < n, ((t i : ℕ) : ℝ≥0) = u
    · simpa only [N, dif_pos h] using pow_pos (hk _ h.choose_spec.1) _
    · simp only [N, dif_neg h, zero_lt_one]
  have hN0 : N 0 = 1 := by
    by_cases h : ∃ i < n, ((t i : ℕ) : ℝ≥0) = 0
    · obtain ⟨i, hi, hi0⟩ := h
      rw [← hi0, hNt i hi, Nat.cast_eq_zero.1 hi0, pow_zero]
    · simp only [N, dif_neg h]
  refine ⟨N, hN, hN0, ?_⟩
  rw [price_fixedFlows_deterministicMarket, MathFin.bondPriceKeyRate]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [hN0, hNt i (Finset.mem_range.1 hi)]
  ring

/-- **A coupon bond is a sum of its zero-coupon bond prices**: at the annually compounded yield
`y`, the price `bondPriceDisc` of the cash flows `c i` at the integer dates `t i` is
`∑ c i · P(0, t i)` at the curve `D u = (1 + y)^{−⌊u⌋}`, the key-rate identity at the flat curve
(`bondPriceKeyRate_const`). It holds for every `y`; the curve is a discount curve, so that
`P(0, t i)` is a bond price, when `y > −1`. -/
theorem bondPriceDisc_eq_sum_bondPrice {κ : Type*} (Q : Measure Ω) [IsFiniteMeasure Q]
    (𝓕 : Filtration ℝ≥0 mΩ) (s : Finset κ) (t : κ → ℕ) (c : κ → ℝ) (y : ℝ) (ω : Ω) :
    MathFin.bondPriceDisc s t c y =
      ∑ i ∈ s, c i * bondPrice Q 𝓕 (fun u _ ↦ ((1 + y) ^ ⌊u⌋₊)⁻¹) 0 (t i) ω :=
  bondPriceKeyRate_eq_sum_bondPrice Q 𝓕 s t c (fun _ ↦ y) ω

/-- **First-order immunization, for market prices.** Let `M r` be markets with the money market
`e^{rt}` as numéraire, and let two zero-coupon portfolios (faces `wA`, `wL`, maturities `TA`,
`TL ≥ 0`) have equal duration-weighted values at the rate `r`. Then the derivative in `r` of the
difference of the market prices of their cash-flow schedules is zero at `r`
(`bondPortfolio_immunization_first_order`, through `bondPortfolioValue_eq_price`). -/
theorem price_immunization_first_order (Q : Measure Ω) [IsProbabilityMeasure Q] (n m : ℕ)
    (wA TA wL TL : ℕ → ℝ) (hTA : ∀ i, 0 ≤ TA i) (hTL : ∀ i, 0 ≤ TL i)
    (M : ℝ → Market ι Ω) (hM : ∀ r t ω, (M r).numeraire t ω = Real.exp (r * t)) (r : ℝ)
    (h_match : MathFin.bondPortfolioDur (Finset.range n) wA TA 0 r =
      MathFin.bondPortfolioDur (Finset.range m) wL TL 0 r) :
    HasDerivAt (fun r' ↦ (M r').price Q (fixedFlows (fun i ↦ (TA i).toNNReal) wA n) -
        (M r').price Q (fixedFlows (fun i ↦ (TL i).toNNReal) wL m)) 0 r := by
  have e : (fun r' ↦ (M r').price Q (fixedFlows (fun i ↦ (TA i).toNNReal) wA n) -
        (M r').price Q (fixedFlows (fun i ↦ (TL i).toNNReal) wL m)) =
      fun r' ↦ MathFin.bondPortfolioValue (Finset.range n) wA TA 0 r' -
        MathFin.bondPortfolioValue (Finset.range m) wL TL 0 r' :=
    funext fun r' ↦ by
      rw [(bondPortfolioValue_eq_price Q n wA TA hTA).1 (M r') r' (hM r'),
        (bondPortfolioValue_eq_price Q m wL TL hTL).1 (M r') r' (hM r')]
  rw [e]
  exact MathFin.bondPortfolio_immunization_first_order _ _ _ _ _ _ 0 r h_match

/-- **Key-rate durations, for market prices.** Let `M y` be markets with the numéraire
`(1 + y)^⌊t⌋`. At a flat curve `y` with `1 + y ≠ 0`, the key-rate partial derivatives of the
coupon bond with cash flows `c` at the integer dates `t` sum to the derivative in `y` of the
market price of its cash-flow schedule
(`sum_deriv_keyRate_eq_deriv_bondPriceDisc`, through `bondPortfolioValue_eq_price`). -/
theorem sum_deriv_keyRate_eq_deriv_price (Q : Measure Ω) [IsProbabilityMeasure Q] (n : ℕ)
    (t : ℕ → ℕ) (c : ℕ → ℝ) (M : ℝ → Market ι Ω)
    (hM : ∀ y s ω, (M y).numeraire s ω = (1 + y) ^ ⌊s⌋₊) {y : ℝ} (hy : 1 + y ≠ 0) :
    ∑ j ∈ Finset.range n, deriv (fun x ↦ MathFin.bondPriceKeyRate (Finset.range n) t c
        (Function.update (fun _ ↦ y) j x)) y =
      deriv (fun y' ↦ (M y').price Q (fixedFlows (fun i ↦ ((t i : ℕ) : ℝ≥0)) c n)) y := by
  have e : (fun y' ↦ (M y').price Q (fixedFlows (fun i ↦ ((t i : ℕ) : ℝ≥0)) c n)) =
      MathFin.bondPriceDisc (Finset.range n) t c :=
    funext fun y' ↦ ((bondPortfolioValue_eq_price Q n c (fun _ ↦ 0) fun _ ↦ le_rfl).2 (M y') y' t
      (hM y')).symm
  rw [e]
  exact MathFin.sum_deriv_keyRate_eq_deriv_bondPriceDisc _ t c hy

end MathFin.Rates
