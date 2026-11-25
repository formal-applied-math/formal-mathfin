/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Choice.Performance.Ratios
public import MathFin.Choice.Utility.MarketMarginalUtility
public import MathFin.Choice.Utility.StatePriceDensity
public import MathFin.Pricing.OneDateMarket

/-!
# The Kelly (growth-optimal) portfolio as numéraire ⟹ the risk-neutral measure

The growth-optimal (log-optimal) portfolio is the **numéraire portfolio**: deflating
the physical measure by the growth-optimal wealth turns it into the equivalent
martingale measure (Long 1990 / Platen's benchmark approach). This file realizes that
identity in the two-outcome Kelly market, the discrete, fully elementary shadow of the
continuous statement, which is not proved here. Its state-price form is `kelly_statePrices`
below, an instance of the first-order condition of `Choice/Utility/StatePriceDensity`.

Setup (`Choice/Performance/Ratios`): a binary bet at fraction `f` pays odds `b` (wealth
multiplier `1 + f·b`) with physical probability `p`, or loses the stake (multiplier
`1 - f`) with probability `1 - p`. The **Kelly fraction** `f* = kellyFraction p b`
maximizes the expected log-growth `kellyGrowth p b` — its first-order optimality is
`kellyGrowth_deriv_at_kelly`. The growth-optimal terminal wealths are

  `W*₊ = 1 + f*·b`   (winning state),   `W*₋ = 1 - f*`   (losing state).

**Deflating the physical measure by `W*`** (dividing each state's physical probability
by the growth-optimal wealth there) gives `q₊ = p/W*₊`, `q₋ = (1-p)/W*₋`. The punchline:

  `q₊ = 1/(b+1)`,   `q₋ = b/(b+1)`   — **independent of the physical `p`** —

the *fair-odds* (risk-neutral) probabilities for a bet paying `b`-to-`1`. They sum
to `1` (a probability measure) and price the bet as a martingale
(`q₊·b + q₋·(−1) = 0`, zero expected excess return): the GOP-deflated measure **is** the
EMM. The `p`-independence is exactly the content of the Kelly first-order condition —
`1 + f*·b = p·(b+1)`, so the physical `p` cancels in the deflation. Change the numéraire
to the growth-optimal portfolio and the physical measure becomes risk-neutral.

The same identities hold in the library's own market structure. `kellyMarket` is the `Market` of
a bond and the bet (the one-date market `Market.oneDate` of the payoff `(b, -1)`, plus a unit
bond), `kellyFairLaw` is a pricing measure of it, and the Kelly portfolio is stationary for the
expected log-wealth (`kelly_foc`, from `kellyGrowth_deriv_at_kelly`). So the market theorems
`sdf_eq_div_of_logOptimal` and `integral_div_logOptimal_mul` apply: the Kelly wealth `W` has
`sdf = 1 / W`, and `E_P[S_k(1) / W] = S_k(0)` (`kellyMarket_numeraire_portfolio`). First order only:
that the Kelly portfolio maximises the expected log-wealth is not proved.

## Main definitions

* `kellyPayoff`, `kellyPrice` — the Kelly market as a payoff matrix and a price vector: the unit
  bond and the bet, which costs nothing.
* `kellyLaw`, `kellyFairLaw`, `kellyMarket` — the physical law, the fair-odds law and the Kelly
  market as a `Market (Fin 2) (Fin 2)`.

## Main results

* `kellyGOPWealth_win`, `kellyGOPWealth_lose` — the growth-optimal terminal wealths
  `W*₊ = p(b+1)` and `W*₋ = (1-p)(b+1)/b` (the Kelly first-order condition made explicit).
* `kellyDeflatedProb_win`, `kellyDeflatedProb_lose` — the GOP-deflated probabilities
  `q₊ = 1/(b+1)`, `q₋ = b/(b+1)`.
* `kellyDeflatedProb_sum_one` — `q₊ + q₋ = 1` (a probability measure).
* `kellyNumeraire_isRiskNeutral` — `q₊·b + q₋·(−1) = 0`: under the GOP-deflated probabilities
  the one-period bet has zero mean, the numéraire-portfolio ⟹ EMM identity in one period.
* `kelly_statePrices` — the GOP-deflated probabilities `q₊, q₋` are a state-price vector of the
  Kelly market, pricing the bond (`q₊ + q₋ = 1`) and the bet (`q₊·b − q₋ = 0`): the logarithmic
  instance of `logUtility_statePrices_of_stationary` (`Choice/Utility/StatePriceDensity`), whose
  stationarity hypothesis is the Kelly first-order condition, which is
  `kellyNumeraire_isRiskNeutral`.

* `kelly_foc` — the Kelly portfolio is stationary for the expected log-wealth on the budget set.
* `kellyFairLaw_isPricingMeasure` — the fair-odds law is a pricing measure of `kellyMarket`.
* `kellyMarket_numeraire_portfolio` — in `kellyMarket`, `sdf = 1 / W` under `kellyFairLaw` and
  `E_P[S_k(1) / W] = S_k(0)` for the Kelly wealth `W`.

## References

* [Long (1990)][Long1990]
* [J. L. Kelly, *A new interpretation of information rate*][Kelly1956]

## Tags

numéraire portfolio, growth-optimal portfolio, benchmark approach, risk-neutral probabilities,
Kelly criterion, fair odds, MSC 91G10, MSC 91G20, JEL G12
-/

@[expose] public section

namespace MathFin

open Real

variable {p b : ℝ}

/-- **Growth-optimal winning wealth** `W*₊ = 1 + f*·b = p·(b+1)`. This is the Kelly
first-order condition (`kellyGrowth_deriv_at_kelly`) made explicit: the physical `p`
appears as the whole factor, which is what lets it cancel in the deflation below. -/
lemma kellyGOPWealth_win (hb : b ≠ 0) :
    1 + kellyFraction p b * b = p * (b + 1) := by
  unfold kellyFraction; field_simp; ring

/-- **Growth-optimal losing wealth** `W*₋ = 1 - f* = (1-p)·(b+1)/b`. -/
lemma kellyGOPWealth_lose (hb : b ≠ 0) :
    1 - kellyFraction p b = (1 - p) * (b + 1) / b := by
  unfold kellyFraction; field_simp; ring

/-- **GOP-deflated winning probability** `q₊ = p / W*₊ = 1/(b+1)`: the physical `p`,
deflated by the growth-optimal wealth, is the fair-odds risk-neutral probability —
independent of `p`. -/
lemma kellyDeflatedProb_win (hp : 0 < p) (hb : 0 < b) :
    p / (1 + kellyFraction p b * b) = 1 / (b + 1) := by
  rw [kellyGOPWealth_win hb.ne']
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- **GOP-deflated losing probability** `q₋ = (1-p) / W*₋ = b/(b+1)`. -/
lemma kellyDeflatedProb_lose (hp1 : p < 1) (hb : 0 < b) :
    (1 - p) / (1 - kellyFraction p b) = b / (b + 1) := by
  have hq : 0 < 1 - p := by linarith
  rw [kellyGOPWealth_lose hb.ne']
  rw [div_div_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- **The GOP-deflated probabilities form a probability measure**: `q₊ + q₋ = 1`. -/
theorem kellyDeflatedProb_sum_one (hp : 0 < p) (hp1 : p < 1) (hb : 0 < b) :
    p / (1 + kellyFraction p b * b) + (1 - p) / (1 - kellyFraction p b) = 1 := by
  rw [kellyDeflatedProb_win hp hb, kellyDeflatedProb_lose hp1 hb]
  have : (b : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- **The Kelly numéraire portfolio induces the risk-neutral measure.** Under the
GOP-deflated measure `q₊ = p/W*₊`, `q₋ = (1-p)/W*₋`, the bet's excess return has zero
mean:

  `q₊·b + q₋·(−1) = 0`,

i.e. the discounted asset is a `q`-martingale — `q` is the equivalent martingale
measure. This is the (discrete, two-outcome) **numéraire-portfolio ⟹ EMM** identity: the
growth-optimal portfolio is the numéraire whose deflator turns the physical measure into
the EMM, the risk-neutrality being exactly the vanishing of the Kelly first-order
condition (`kellyGrowth_deriv_at_kelly`). -/
theorem kellyNumeraire_isRiskNeutral (hp : 0 < p) (hp1 : p < 1) (hb : 0 < b) :
    p / (1 + kellyFraction p b * b) * b
      + (1 - p) / (1 - kellyFraction p b) * (-1) = 0 := by
  rw [kellyDeflatedProb_win hp hb, kellyDeflatedProb_lose hp1 hb]
  ring

/-- The **Kelly market** on the states `0` (win) and `1` (lose), as a payoff matrix: asset `0` is
the unit bond, asset `1` the bet, paying `b` or `-1`. A portfolio `θ` pays `θ 0 + θ 1 * b` when
the bet wins and `θ 0 - θ 1` when it loses. -/
def kellyPayoff (b : ℝ) : Fin 2 → Fin 2 → ℝ := ![![1, 1], ![b, -1]]

/-- The prices of the Kelly market: the bond costs `1`, the bet nothing. -/
def kellyPrice : Fin 2 → ℝ := ![1, 0]

lemma kellyPayoff_win (θ : Fin 2 → ℝ) :
    portfolioPayoff (kellyPayoff b) θ 0 = θ 0 + θ 1 * b := by
  simp [portfolioPayoff, Matrix.vecMul, dotProduct, kellyPayoff, Fin.sum_univ_two]

lemma kellyPayoff_lose (θ : Fin 2 → ℝ) :
    portfolioPayoff (kellyPayoff b) θ 1 = θ 0 - θ 1 := by
  simp [portfolioPayoff, Matrix.vecMul, dotProduct, kellyPayoff, Fin.sum_univ_two]
  ring

lemma kellyCost (θ : Fin 2 → ℝ) : portfolioCost kellyPrice θ = θ 0 := by
  simp [portfolioCost, dotProduct, kellyPrice, Fin.sum_univ_two]

/-- The Kelly winning wealth `1 + f*·b` is positive. -/
lemma kellyWealth_win_pos (hp : 0 < p) (hb : 0 < b) : 0 < 1 + kellyFraction p b * b := by
  rw [kellyGOPWealth_win hb.ne']
  positivity

/-- The Kelly losing wealth `1 - f*` is positive. -/
lemma kellyWealth_lose_pos (hp1 : p < 1) (hb : 0 < b) : 0 < 1 - kellyFraction p b := by
  rw [kellyGOPWealth_lose hb.ne']
  exact div_pos (mul_pos (sub_pos.mpr hp1) (by linarith)) hb

/-- **The Kelly portfolio is stationary for the expected log-wealth.** The portfolio of the
Kelly market with one unit in the bond and the fraction `f*` on the bet has the first-order
condition of `u = log` on the budget set: `∑ ω, P ω * W⁻¹ * (payoff of d) = 0` for every
budget-neutral `d` (`d 0 = 0`, the bet costs nothing). This is the Kelly first-order condition
`kellyGrowth_deriv_at_kelly`, `g'(f*) = 0`, read along the direction `d = (0, 1)`: the derivative
of `g` at `f*` is computed independently and equated to the zero of that lemma. -/
theorem kelly_foc (hp : 0 < p) (hp1 : p < 1) (hb : 0 < b) (d : Fin 2 → ℝ) (hd : d 0 = 0) :
    ∑ ω, ![p, 1 - p] ω * (portfolioPayoff (kellyPayoff b) ![1, kellyFraction p b] ω)⁻¹ *
      portfolioPayoff (kellyPayoff b) d ω = 0 := by
  have h1 := kellyWealth_win_pos hp hb
  have h2 := kellyWealth_lose_pos hp1 hb
  have ha : HasDerivAt (fun f : ℝ ↦ Real.log (1 + f * b)) (1 * b / (1 + kellyFraction p b * b))
      (kellyFraction p b) := (((hasDerivAt_id' _).mul_const b).const_add 1).log h1.ne'
  have hc : HasDerivAt (fun f : ℝ ↦ Real.log (1 - f)) ((-1) / (1 - kellyFraction p b))
      (kellyFraction p b) := ((hasDerivAt_id' _).const_sub 1).log h2.ne'
  have hg : HasDerivAt (kellyGrowth p b)
      (p * (1 * b / (1 + kellyFraction p b * b)) +
        (1 - p) * ((-1) / (1 - kellyFraction p b))) (kellyFraction p b) := by
    convert (ha.const_mul p).add (hc.const_mul (1 - p)) using 1
    ext x
    simp [kellyGrowth]
  have h0 := (kellyGrowth_deriv_at_kelly hp hp1 hb).unique hg
  rw [Fin.sum_univ_two]
  simp only [kellyPayoff_win, kellyPayoff_lose, hd, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (-d 1) * h0

/-- **The GOP-deflated probabilities are the state prices of the Kelly market.** The Kelly
portfolio (one unit in the bond, the fraction `f*` on the bet) has the marginal-utility density
`p / W*` of the logarithmic utility, and this density, which is `q₊, q₋`, prices both assets of the
Kelly market: the bond at `1` (`q₊ + q₋ = 1`) and the bet at `0`
(`q₊·b − q₋ = 0`, `kellyNumeraire_isRiskNeutral`). -/
theorem kelly_statePrices (hp : 0 < p) (hp1 : p < 1) (hb : 0 < b) (k : Fin 2) :
    statePricePricing Finset.univ
      ![p / (1 + kellyFraction p b * b), (1 - p) / (1 - kellyFraction p b)]
      (kellyPayoff b k) = kellyPrice k := by
  have hW : portfolioPayoff (kellyPayoff b) ![1, kellyFraction p b] =
      ![1 + kellyFraction p b * b, 1 - kellyFraction p b] := by
    funext ω
    fin_cases ω
    · simp [kellyPayoff_win]
    · simp [kellyPayoff_lose]
  have hq : (fun ω : Fin 2 ↦ 1 * ![p, 1 - p] ω /
      portfolioPayoff (kellyPayoff b) ![1, kellyFraction p b] ω) =
      ![p / (1 + kellyFraction p b * b), (1 - p) / (1 - kellyFraction p b)] := by
    funext ω
    fin_cases ω
    · simp [hW]
    · simp [hW]
  have hpos : ∀ ω, 0 < ![p, 1 - p] ω := by
    intro ω
    fin_cases ω
    · simpa using hp
    · simpa using hp1
  have hWpos : ∀ ω, 0 < portfolioPayoff (kellyPayoff b) ![1, kellyFraction p b] ω := by
    intro ω
    rw [hW]
    fin_cases ω
    · simpa using kellyWealth_win_pos hp hb
    · simpa using kellyWealth_lose_pos hp1 hb
  have hfoc : ∀ d, portfolioCost kellyPrice d = 0 →
      ∑ ω, ![p, 1 - p] ω * (portfolioPayoff (kellyPayoff b) ![1, kellyFraction p b] ω)⁻¹ *
        portfolioPayoff (kellyPayoff b) d ω = 0 := fun d hd ↦
    kelly_foc hp hp1 hb d (by rwa [kellyCost] at hd)
  obtain ⟨-, hprice⟩ := logUtility_statePrices_of_stationary (p := ![p, 1 - p])
    (A := kellyPayoff b) (pr := kellyPrice) (θ := ![1, kellyFraction p b]) (w₀ := 1)
    (by rw [kellyCost]; simp) one_pos hpos (by simp [Fin.sum_univ_two]) hWpos hfoc
  exact (congrArg (fun q ↦ statePricePricing Finset.univ q (kellyPayoff b k)) hq).symm.trans
    (hprice k)

/-! ### The Kelly market as a `Market`

The bet is the one-date market of the payoff `![b, -1]` (quoted at `0`, no discounting, date `1`);
the bond is a second asset worth `1` throughout. The numéraire is the money market `e^{0·t} = 1`. -/

open MeasureTheory MathFin.Contracts

/-- The physical law of the bet: the winning state `0` has probability `p`, the losing state `1`
probability `1 - p`. -/
noncomputable def kellyLaw (p : ℝ) : Measure (Fin 2) :=
  Measure.ofWeights Finset.univ ![p, 1 - p]

/-- The fair-odds law `q₊ = 1/(b+1)`, `q₋ = b/(b+1)`. -/
noncomputable def kellyFairLaw (b : ℝ) : Measure (Fin 2) :=
  Measure.ofWeights Finset.univ ![1 / (b + 1), b / (b + 1)]

/-- The bet alone: the one-date market (`Market.oneDate`) whose asset is quoted at `0` before the
date `1` and pays `![b, -1]` from then on, at zero rate, under the law `kellyLaw p`. -/
noncomputable def kellyBetMarket (p b : ℝ) : Market Unit (Fin 2) :=
  Market.oneDate (kellyLaw p) (measurable_of_finite ![b, -1]) 0 0 1

/-- **The Kelly market** on the two states: asset `0` is the bond (price `1` at every date), asset
`1` the bet of `kellyBetMarket`, with the money market `1` as numéraire. -/
noncomputable def kellyMarket (p b : ℝ) : Market (Fin 2) (Fin 2) where
  P := (kellyBetMarket p b).P
  𝓕 := (kellyBetMarket p b).𝓕
  asset i t ω := if i = 0 then 1 else (kellyBetMarket p b).asset () t ω
  numeraire := (kellyBetMarket p b).numeraire
  numeraire_pos := (kellyBetMarket p b).numeraire_pos
  asset_adapted i t := by
    by_cases hi : i = 0
    · simp only [hi, ↓reduceIte]
      exact stronglyMeasurable_const
    · simp only [hi, ↓reduceIte]
      exact (kellyBetMarket p b).asset_adapted () t
  numeraire_adapted := (kellyBetMarket p b).numeraire_adapted

lemma isProbabilityMeasure_kellyLaw (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (kellyLaw p) :=
  Measure.isProbabilityMeasure_ofWeights (fun i _ ↦ by
    fin_cases i
    · simpa using hp
    · simpa using hp1) (by simp [Fin.sum_univ_two])

lemma kellyLaw_real_singleton (ω : Fin 2) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (kellyLaw p).real {ω} = ![p, 1 - p] ω := by
  fin_cases ω <;> simp [kellyLaw, Measure.real, Measure.ofWeights, Fin.sum_univ_two,
    Measure.dirac_apply', ENNReal.toReal_ofReal, hp, sub_nonneg.mpr hp1]

/-- The terminal asset payoffs of the Kelly market are the columns of `kellyPayoff`. -/
lemma kellyMarket_asset_one (k ω : Fin 2) : (kellyMarket p b).asset k 1 ω = kellyPayoff b k ω := by
  fin_cases k <;> fin_cases ω <;>
    simp [kellyMarket, kellyBetMarket, Market.oneDate, kellyPayoff]

/-- The initial prices of the Kelly market are `kellyPrice`. -/
lemma kellyMarket_asset_zero (k ω : Fin 2) : (kellyMarket p b).asset k 0 ω = kellyPrice k := by
  fin_cases k <;> simp [kellyMarket, kellyBetMarket, Market.oneDate, kellyPrice]

/-- **The fair-odds law prices the Kelly market.** For `p ∈ (0, 1)` and `b > 0` the law
`q₊ = 1/(b+1)`, `q₋ = b/(b+1)` is equivalent to the physical law and makes the deflated bond and
bet martingales up to the date `1`. -/
theorem kellyFairLaw_isPricingMeasure (hp : 0 < p) (hp1 : p < 1) (hb : 0 < b) :
    (kellyMarket p b).IsPricingMeasure 1 (kellyFairLaw b) := by
  have hpos : ∀ i, 0 < ![p, 1 - p] i := fun i ↦ by
    fin_cases i
    · simpa using hp
    · simpa using sub_pos.mpr hp1
  have hqpos : ∀ i, 0 < ![1 / (b + 1), b / (b + 1)] i := fun i ↦ by
    fin_cases i
    · simpa using by positivity
    · simpa using by positivity
  have hprob : IsProbabilityMeasure (kellyFairLaw b) :=
    Measure.isProbabilityMeasure_ofWeights (fun i _ ↦ (hqpos i).le) (by
      simp [Fin.sum_univ_two]
      field_simp
      ring)
  have hQ : (kellyBetMarket p b).IsPricingMeasure 1 (kellyFairLaw b) :=
    Market.isPricingMeasure_oneDate (Measure.ofWeights_absolutelyContinuous_of_pos hpos)
      (Measure.ofWeights_absolutelyContinuous_of_pos hqpos) .of_finite (by
        rw [kellyFairLaw, Measure.integral_ofWeights _ fun i _ ↦ (hqpos i).le]
        simp [Fin.sum_univ_two]
        field_simp
        ring)
  refine Market.IsPricingMeasure.of_isEquivProbMeasure ⟨hprob,
    Measure.ofWeights_absolutelyContinuous_of_pos hpos,
    Measure.ofWeights_absolutelyContinuous_of_pos hqpos⟩ fun i ↦ ?_
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · have e : (fun t ↦ (kellyMarket p b).deflated 0 (min t 1)) = fun _ _ ↦ 1 := by
      funext t ω
      simp [Market.deflated, kellyMarket, kellyBetMarket, Market.oneDate]
    rw [e]
    exact martingale_const _ _ _
  · exact hQ.martingale ()

/-- **The Kelly wealth is the numéraire portfolio of the betting market.** In the Kelly market
(`kellyMarket`, a bond and a bet paying odds `b` with win probability `p ∈ (0, 1)`, `b > 0`), let
`W` be the terminal wealth of the portfolio with one unit in the bond and the Kelly fraction
`f* = kellyFraction p b` on the bet. Under the fair-odds pricing measure `kellyFairLaw b`, the
stochastic discount factor is `1 / W` in every state, and the prices deflated by `W` are
`P`-martingales over the period: `E_P[S_k(1) / W] = S_k(0)` for the bond (`k = 0`, `E_P[1 / W] = 1`)
and the bet (`k = 1`, `E_P[payoff / W] = 0`, its price). The stationarity of the Kelly portfolio is
`kelly_foc`, a consequence of `kellyGrowth_deriv_at_kelly`; the identities are
`IsPricingMeasure.sdf_eq_div_of_logOptimal` and `IsPricingMeasure.integral_div_logOptimal_mul`
for the market. -/
theorem kellyMarket_numeraire_portfolio (hp : 0 < p) (hp1 : p < 1) (hb : 0 < b) :
    (∀ ω, (kellyMarket p b).sdf (kellyFairLaw b) 1 ω =
        1 / portfolioPayoff (kellyPayoff b) ![1, kellyFraction p b] ω) ∧
      ∀ k, ∫ ω, kellyPayoff b k ω / portfolioPayoff (kellyPayoff b) ![1, kellyFraction p b] ω
        ∂(kellyLaw p) = kellyPrice k := by
  have hP : IsProbabilityMeasure (kellyMarket p b).P := isProbabilityMeasure_kellyLaw hp.le hp1.le
  have hA : (fun j ↦ (kellyMarket p b).asset j 1) = kellyPayoff b :=
    funext fun j ↦ funext (kellyMarket_asset_one j)
  have hPr : ∀ ω, 0 < (kellyMarket p b).P.real {ω} := fun ω ↦ by
    rw [show (kellyMarket p b).P = kellyLaw p from rfl, kellyLaw_real_singleton ω hp.le hp1.le]
    fin_cases ω
    · simpa using hp
    · simpa using sub_pos.mpr hp1
  have hQ := kellyFairLaw_isPricingMeasure hp hp1 hb
  have hθ : portfolioCost kellyPrice ![1, kellyFraction p b] = 1 := by
    rw [kellyCost]; simp
  have hW (ω : Fin 2) : 0 < portfolioPayoff (kellyPayoff b) ![1, kellyFraction p b] ω := by
    fin_cases ω
    · simpa [kellyPayoff_win] using kellyWealth_win_pos hp hb
    · simpa [kellyPayoff_lose] using kellyWealth_lose_pos hp1 hb
  have hfoc : ∀ d, portfolioCost kellyPrice d = 0 →
      ∑ ω, (kellyMarket p b).P.real {ω} *
        (portfolioPayoff (kellyPayoff b) ![1, kellyFraction p b] ω)⁻¹ *
        portfolioPayoff (kellyPayoff b) d ω = 0 := fun d hd ↦ by
    simp only [show (kellyMarket p b).P = kellyLaw p from rfl,
      kellyLaw_real_singleton _ hp.le hp1.le]
    exact kelly_foc hp hp1 hb d (by rwa [kellyCost] at hd)
  have hcomplete : ∀ x : Fin 2 → ℝ, (∀ k, ∑ ω, x ω * (kellyMarket p b).asset k 1 ω = 0) →
      x = 0 := fun x hx ↦ by
    have h0 := hx 0
    have h1 := hx 1
    simp only [kellyMarket_asset_one, Fin.sum_univ_two, kellyPayoff] at h0 h1
    simp at h0 h1
    have : (b + 1) * x 0 = 0 := by linarith
    have hx0 : x 0 = 0 := (mul_eq_zero.mp this).resolve_left (by positivity)
    funext ω
    fin_cases ω
    · simpa using hx0
    · simpa [hx0] using h0
  have hN₀ : ∀ ω, (kellyMarket p b).numeraire 0 ω = 1 := fun ω ↦ by
    simp [kellyMarket, kellyBetMarket, Market.oneDate]
  have h1 := hQ.sdf_eq_div_of_logOptimal (w₀ := 1) (θ := ![1, kellyFraction p b]) hPr hN₀
    kellyMarket_asset_zero hcomplete hθ one_pos (by rw [hA]; exact hW) (by rw [hA]; exact hfoc)
  have h2 := hQ.integral_div_logOptimal_mul (w₀ := 1) (θ := ![1, kellyFraction p b]) hPr hN₀
    kellyMarket_asset_zero hcomplete hθ one_pos (by rw [hA]; exact hW) (by rw [hA]; exact hfoc)
  rw [hA] at h1 h2
  refine ⟨fun ω ↦ h1 ω, fun k ↦ ?_⟩
  have h3 := h2 k
  simp only [kellyMarket_asset_one, div_one] at h3
  exact h3

end MathFin
