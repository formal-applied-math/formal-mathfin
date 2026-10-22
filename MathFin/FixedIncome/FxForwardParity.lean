/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.BlackScholes.Forward
public import MathFin.Foundations.NoArbitrageDerivations

/-!
# FX forward via covered interest parity, and the implied forward curve

**Covered interest parity (CIP)**: with continuously-compounded domestic and
foreign rates `r_d`, `r_f` and spot `S` (domestic per unit of foreign), the
no-arbitrage forward rate for maturity `T` is

  `F(0, T) = S · exp((r_d - r_f) · T)`.

It is derived from `forward_price_from_no_arbitrage`: in a finite-state market
the forward contract paying `S_T - F` is priced by the same state prices as the
domestic zero-coupon bond (price `e^{-r_d T}`) and the foreign zero-coupon bond
held in domestic currency (price `S·e^{-r_f T}`: buy `e^{-r_f T}` units of
foreign currency at spot and invest them at `r_f`), and it is worth zero
exactly at `F = S·e^{-r_f T}/e^{-r_d T}` (`covered_interest_parity`). The
one-period discrete form is `F = S·(1 + r_d)/(1 + r_f)`.

**Uncovered interest parity**, in its risk-neutral form: under the domestic
risk-neutral measure of the Garman–Kohlhagen model (the lognormal hypothesis
`BSCallHyp` with drift `r_d - r_f`, as in `garman_kohlhagen_call_formula`),
the expected terminal spot is the same `S·e^{(r_d - r_f)T}`
(`uncovered_interest_parity`, from `expected_terminal_eq_forward`). This is a
statement about the pricing measure; the economists' UIP, the same equation
under the physical measure, is an empirical hypothesis and is not claimed
here. The two parities agree (`covered_eq_uncovered_interest_parity`): the
forward a static market prices to zero is the model's expected spot.

**Implied forward curve**: chaining CIP across two maturities gives the
**forward-forward factor** — the ratio `F(0,T₂)/F(0,T₁)`, i.e. the implied
carry between `T₁` and `T₂` (the FX-swap points over that leg, quoted as the
additive `F(0,T₂) - F(0,T₁) = F(0,T₁)·(factor - 1)`, follow from it) — purely
from the two spot-dated forwards, with the spot rate canceling. This is *not itself* an exchange rate: the actual
`T₁`-struck forward for delivery at `T₂` is the random
`S_{T₁} · exp((r_d - r_f)·(T₂ - T₁))`, since the future spot `S_{T₁}` is
unknown today. What the factor gives is the deterministic multiplier by
which that future forward quote relates to today's two spot-dated quotes —
the curve is internally consistent, with no re-anchoring to `S` needed once
`F(0,T₁)` and `F(0,T₂)` are known:

  `F(0, T₂) / F(0, T₁) = exp((r_d - r_f) · (T₂ - T₁))`.

## Result

* `fxForward`: the CIP forward rate `S · exp((r_d - r_f) · T)`.
* `covered_interest_parity`: the zero-value forward is `fxForward`, derived
  from `forward_price_from_no_arbitrage`;
  `covered_interest_parity_discrete`: the one-period form
  `S·(1 + r_d)/(1 + r_f)`.
* `uncovered_interest_parity`: `E_Q[S_T] = fxForward` under the
  Garman–Kohlhagen risk-neutral hypothesis.
* `covered_eq_uncovered_interest_parity`: the CIP forward equals the
  risk-neutral expected spot.
* `fxForward_at_zero`: `F(0, 0) = S` (the forward collapses to spot at
  immediate maturity).
* `fxForward_pos`: every CIP forward is positive whenever spot is.
* `forwardForwardFactor`: the ratio `F(0,T₂)/F(0,T₁)` — the forward-forward
  factor, independent of `S`.
* `forwardForwardFactor_eq_exp_diff`: that ratio equals
  `exp((r_d - r_f)·(T₂ - T₁))` — the curve is multiplicatively consistent.
-/

@[expose] public section

namespace MathFin

open MeasureTheory

/-- Covered-interest-parity FX forward rate for maturity `T`, continuous
compounding: `F(0, T) = S · exp((r_d - r_f) · T)`. -/
noncomputable def fxForward (S r_d r_f T : ℝ) : ℝ := S * Real.exp ((r_d - r_f) * T)

/-- **Covered interest parity from no-arbitrage.** A finite-state market with
state prices `q` and terminal spot `S_T`, pricing the domestic zero-coupon bond
at `e^{-r_d T}` and the foreign zero-coupon bond, held in domestic currency, at
`S·e^{-r_f T}`. The forward contract paying `S_T - F` is worth zero iff
`F = S·e^{(r_d - r_f)T}`: `forward_price_from_no_arbitrage` with the foreign
bond as the asset. -/
theorem covered_interest_parity {ι : Type*} (s : Finset ι) (q S_T : ι → ℝ)
    (S r_d r_f T F : ℝ)
    (h_dom : ∑ i ∈ s, q i = Real.exp (-(r_d * T)))
    (h_for : ∑ i ∈ s, q i * S_T i = S * Real.exp (-(r_f * T))) :
    ∑ i ∈ s, q i * (S_T i - F) = 0 ↔ F = fxForward S r_d r_f T := by
  rw [forward_price_from_no_arbitrage s q S_T _ _ F (Real.exp_pos _).ne' h_dom h_for, fxForward,
    mul_div_assoc, ← Real.exp_sub, neg_sub_neg, ← sub_mul]

/-- **Covered interest parity, one period, discrete compounding**: with the
domestic bond priced at `1/(1 + r_d)` and the foreign bond, in domestic
currency, at `S/(1 + r_f)`, the zero-value forward is `S·(1 + r_d)/(1 + r_f)`. -/
theorem covered_interest_parity_discrete {ι : Type*} (s : Finset ι) (q S_T : ι → ℝ)
    (S r_d r_f F : ℝ) (hd : 1 + r_d ≠ 0)
    (h_dom : ∑ i ∈ s, q i = 1 / (1 + r_d))
    (h_for : ∑ i ∈ s, q i * S_T i = S / (1 + r_f)) :
    ∑ i ∈ s, q i * (S_T i - F) = 0 ↔ F = S * (1 + r_d) / (1 + r_f) := by
  rw [forward_price_from_no_arbitrage s q S_T _ _ F (one_div_ne_zero hd) h_dom h_for,
    div_div_eq_mul_div, div_one, div_mul_eq_mul_div]

/-- **Uncovered interest parity, risk-neutral form.** Under the Garman–Kohlhagen
hypothesis (lognormal terminal spot with domestic risk-neutral drift
`r_d - r_f`), the expected terminal spot is the CIP forward:
`E_Q[S_T] = S·e^{(r_d - r_f)T}`. This is `expected_terminal_eq_forward` at the
drift `r_d - r_f`; it is a statement about the pricing measure `Q`, not about
the physical one. -/
theorem uncovered_interest_parity {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q] {S K r_d r_f σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S K (r_d - r_f) σ T Z) :
    ∫ ω, bsTerminal S (r_d - r_f) σ T (Z ω) ∂Q = fxForward S r_d r_f T :=
  expected_terminal_eq_forward h

/-- **Covered and uncovered parity agree.** The forward that a finite-state
market prices to zero (`covered_interest_parity`) is the expected terminal spot
under the Garman–Kohlhagen risk-neutral measure with the same spot and rates
(`uncovered_interest_parity`). -/
theorem covered_eq_uncovered_interest_parity {ι : Type*} (s : Finset ι) (q S_T : ι → ℝ)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S K r_d r_f σ T F : ℝ} {Z : Ω → ℝ}
    (h_dom : ∑ i ∈ s, q i = Real.exp (-(r_d * T)))
    (h_for : ∑ i ∈ s, q i * S_T i = S * Real.exp (-(r_f * T)))
    (hF : ∑ i ∈ s, q i * (S_T i - F) = 0) (h : BSCallHyp Q S K (r_d - r_f) σ T Z) :
    F = ∫ ω, bsTerminal S (r_d - r_f) σ T (Z ω) ∂Q := by
  rw [uncovered_interest_parity h]
  exact (covered_interest_parity s q S_T S r_d r_f T F h_dom h_for).mp hF

/-- At zero maturity the forward collapses to the spot rate. -/
theorem fxForward_at_zero (S r_d r_f : ℝ) : fxForward S r_d r_f 0 = S := by
  unfold fxForward; simp

/-- Every CIP forward is positive whenever the spot rate is. -/
theorem fxForward_pos {S : ℝ} (hS : 0 < S) (r_d r_f T : ℝ) : 0 < fxForward S r_d r_f T :=
  mul_pos hS (Real.exp_pos _)

/-- The **forward-forward factor** between `T₁` and `T₂`: the ratio of the
two spot-dated CIP forwards. The spot rate `S` cancels, so this is exactly
the deterministic forward-forward carry factor a forward curve built from
market-quoted forwards would use, with no need to re-observe spot. It is a
unitless ratio, not an exchange rate — see the module docstring. -/
noncomputable def forwardForwardFactor (S r_d r_f T1 T2 : ℝ) : ℝ :=
  fxForward S r_d r_f T2 / fxForward S r_d r_f T1

/-- The forward-forward factor equals `exp((r_d - r_f)·(T₂ - T₁))`, with no
dependence on `S` left. This is the forward curve's self-consistency:
chaining two spot-dated forwards agrees with the direct CIP exponential over
the maturity gap. -/
theorem forwardForwardFactor_eq_exp_diff {S : ℝ} (hS : S ≠ 0) (r_d r_f T1 T2 : ℝ) :
    forwardForwardFactor S r_d r_f T1 T2 = Real.exp ((r_d - r_f) * (T2 - T1)) := by
  unfold forwardForwardFactor fxForward
  rw [mul_div_mul_left _ _ hS, ← Real.exp_sub]
  congr 1
  ring

end MathFin
