/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Choice.Performance.Ratios
public import MathFin.Choice.Utility.StatePriceDensity

/-!
# The Kelly (growth-optimal) portfolio as numéraire ⟹ the risk-neutral measure

The growth-optimal (log-optimal) portfolio is the **numéraire portfolio**: deflating
the physical measure by the growth-optimal wealth turns it into the equivalent
martingale measure (Long 1990 / Platen's benchmark approach). This file realizes that
identity in the two-outcome Kelly market — the discrete, fully elementary shadow of the
continuous statement (which needs a state-price-density / market model absent from the
Itô tower).

Setup (`Choice/Performance/Ratios`): a binary bet at fraction `f` pays odds `b` (wealth
multiplier `1 + f·b`) with physical probability `p`, or loses the stake (multiplier
`1 - f`) with probability `1 - p`. The **Kelly fraction** `f* = kellyFraction p b`
maximizes the expected log-growth `kellyGrowth p b` — its first-order optimality is
`kellyGrowth_deriv_at_kelly`. The growth-optimal terminal wealths are

  `W*₊ = 1 + f*·b`   (winning state),   `W*₋ = 1 - f*`   (losing state).

**Deflating the physical measure by `W*`** (dividing each state's physical probability
by the growth-optimal wealth there) gives `q₊ = p/W*₊`, `q₋ = (1-p)/W*₋`. The punchline:

  `q₊ = 1/(b+1)`,   `q₋ = b/(b+1)`   — **independent of the physical `p`** —

the unique *fair-odds* (risk-neutral) probabilities for a bet paying `b`-to-`1`. They sum
to `1` (a probability measure) and price the bet as a martingale
(`q₊·b + q₋·(−1) = 0`, zero expected excess return): the GOP-deflated measure **is** the
EMM. The `p`-independence is exactly the content of the Kelly first-order condition —
`1 + f*·b = p·(b+1)`, so the physical `p` cancels in the deflation. Change the numéraire
to the growth-optimal portfolio and the physical measure becomes risk-neutral.

## Main results

* `kellyGOPWealth_win`, `kellyGOPWealth_lose` — the growth-optimal terminal wealths
  `W*₊ = p(b+1)` and `W*₋ = (1-p)(b+1)/b` (the Kelly first-order condition made explicit).
* `kellyDeflatedProb_win`, `kellyDeflatedProb_lose` — the GOP-deflated probabilities
  `q₊ = 1/(b+1)`, `q₋ = b/(b+1)`.
* `kellyDeflatedProb_sum_one` — `q₊ + q₋ = 1` (a probability measure).
* `kellyNumeraire_isRiskNeutral` — `q₊·b + q₋·(−1) = 0`: under the GOP-deflated probabilities
  the one-period bet has zero mean, the numéraire-portfolio ⟹ EMM identity in one period.
* `kellyPayoff`, `kellyPrice` — the Kelly market as a payoff matrix and a price vector: the unit
  bond and the bet, which costs nothing.
* `kelly_statePrices` — the GOP-deflated probabilities `q₊, q₋` are a state-price vector of the
  Kelly market, pricing the bond (`q₊ + q₋ = 1`) and the bet (`q₊·b − q₋ = 0`): the logarithmic
  instance of `logUtility_statePrices_of_stationary` (`Choice/Utility/StatePriceDensity`), whose
  stationarity hypothesis is the Kelly first-order condition, which is
  `kellyNumeraire_isRiskNeutral`.

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
  simp [portfolioPayoff, kellyPayoff, Fin.sum_univ_two] <;> ring

lemma kellyPayoff_lose (θ : Fin 2 → ℝ) :
    portfolioPayoff (kellyPayoff b) θ 1 = θ 0 - θ 1 := by
  simp [portfolioPayoff, kellyPayoff, Fin.sum_univ_two] <;> ring

lemma kellyCost (θ : Fin 2 → ℝ) : portfolioCost kellyPrice θ = θ 0 := by
  simp [portfolioCost, kellyPrice, Fin.sum_univ_two]

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
  have h1 : 0 < 1 + kellyFraction p b * b := by
    rw [kellyGOPWealth_win hb.ne']
    positivity
  have h2 : 0 < 1 - kellyFraction p b := by
    rw [kellyGOPWealth_lose hb.ne']
    exact div_pos (mul_pos (sub_pos.mpr hp1) (by linarith)) hb
  have hWpos : ∀ ω, 0 < portfolioPayoff (kellyPayoff b) ![1, kellyFraction p b] ω := by
    intro ω
    rw [hW]
    fin_cases ω
    · simpa using h1
    · simpa using h2
  have hfoc : ∀ d, portfolioCost kellyPrice d = 0 →
      ∑ ω, ![p, 1 - p] ω * (portfolioPayoff (kellyPayoff b) ![1, kellyFraction p b] ω)⁻¹ *
        portfolioPayoff (kellyPayoff b) d ω = 0 := by
    intro d hd
    have hd0 : d 0 = 0 := by rwa [kellyCost] at hd
    rw [Fin.sum_univ_two]
    simp only [kellyPayoff_win, kellyPayoff_lose, hd0, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination d 1 * kellyNumeraire_isRiskNeutral hp hp1 hb
  obtain ⟨-, hprice⟩ := logUtility_statePrices_of_stationary (p := ![p, 1 - p])
    (A := kellyPayoff b) (pr := kellyPrice) (θ := ![1, kellyFraction p b]) (w₀ := 1)
    (by rw [kellyCost]; simp) one_pos hpos (by simp [Fin.sum_univ_two]) hWpos hfoc
  exact (congrArg (fun q ↦ statePricePricing Finset.univ q (kellyPayoff b k)) hq).symm.trans
    (hprice k)

end MathFin
