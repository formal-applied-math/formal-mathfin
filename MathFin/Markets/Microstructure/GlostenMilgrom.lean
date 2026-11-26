/-
Copyright (c) 2026 Alfredo Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfredo Garcia
-/
module

public import MathFin.Init
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Glosten-Milgrom adverse-selection bid-ask spread

Glosten and Milgrom (1985) derive the bid-ask spread from adverse selection
alone. A fraction `p` of arriving traders know a binary asset value
`V ∈ {V_L, V_H}`; the rest trade at random. A competitive market maker quotes

  `ask = E[V | buy]`,   `bid = E[V | sell]`,

updating by Bayes on the direction of the order. The spread is what is left.

Two modelling conventions, both visible in the statements. The sell event is
`Bᶜ`: every arriving trader either buys or sells, so there is no no-trade
outcome, and `bid = E[V | Bᶜ]`. And the quotes are *posited* to be those
conditional expectations — Glosten-Milgrom's derivation of them from a
competitive market maker's zero expected profit is not formalized here.

The four stages below are marked by section headers. The fourth is what makes
the other three a single theorem rather than three separate ones:
`cond_real_eq` is Bayes in `ℝ`, and that is what identifies the model's posterior
`(μ[|B]).real H` with the real function `postBuy` stage 3 reasons about.

Every probability is `μ.real`, Mathlib's `Measure.real`, so no stage converts between `ℝ≥0∞`
and `ℝ`. Conditioning on a null event gives the zero measure, hence the junk value `x/0 = 0`;
each lemma carries the non-nullity hypothesis it needs.

## The hypothesis `0 < θ < 1`

The usual statement of the result omits it. It is not a technical convenience,
and the two endpoints fail for different reasons.

With `p < 1` a degenerate prior leaves nothing to be adversely selected: both
posteriors coincide, the spread is exactly `0`, and `ask - bid > 0` is false.

A degenerate prior with `p = 1` is worse, in two ways both machine-checked here.
One of the two trade events becomes null, and `quote_eq_zero_of_null` shows what
`cond` then returns: not a bad price but the zero measure, whose integral is `0`.
And `spread_junk_at_corner` evaluates the closed form at `θ = 1, p = 1` — it
returns the *entire* `V_H - V_L`, the largest spread there could be, at the one
point where the true spread is `0`, because `0/0 = 0`. Nothing errors in either
case. Excluding the endpoints excludes both at once.

The derivation demands the hypothesis independently: `cond_buy_high`
needs `μ.real H ≠ 0` and `cond_buy_low` needs `μ.real Hᶜ ≠ 0`, so their
hypotheses cannot be jointly satisfied without `0 < θ < 1`.

A model satisfying all of them — so the theorem is not vacuous — is in
`MathFin.Markets.Microstructure.GlostenMilgromModel`.

## Main definitions

* `payoff`: the two-valued asset, `VL + indicator H (VH - VL)`, equal to `VH` on the high event
  `H` and `VL` off it.
* `postBuy`, `postSell`: the posterior probability that the value is high after a buy,
  `(1 + p) θ / (1 + p (2θ - 1))`, and after a sell, `(1 - p) θ / (1 - p (2θ - 1))`.

## Main results

* `cond_buy_high`, `cond_buy_low`: the trade probabilities `(1 ± p)/2`, derived from the trader
  mix (`two_mul_inter_high_buy`, `two_mul_inter_low_buy` are their joint form).
* `cond_real_apply`, `cond_real_mul_eq_inter`: conditioning in `ℝ`.
* `payoff`, `spread_eq`: the quotes as integrals, and the payoff cancelling.
* `postBuy`, `postSell`, `post_sub_post`: the posteriors and the closed form
  `4pθ(1-θ) / (1 - p²(2θ-1)²)`.
* `cond_real_eq`: Bayes in `ℝ` — the seam.
* `postBuy_eq`, `postSell_eq`: the model's posteriors *are* `postBuy`/`postSell`.
* `spread_pos_of_model`: `∫ V ∂μ[|buy] > ∫ V ∂μ[|sell]`, from the model's own
  primitives.
* `quote_eq_zero_of_null`, `spread_junk_at_corner`: what the excluded endpoints
  actually do — a quote that is not a quote, and a closed form returning the
  whole value range.

## References

* [L. R. Glosten and P. R. Milgrom, *Bid, ask and transaction prices in a
  specialist market with heterogeneously informed traders*][GlostenMilgrom1985].

## Tags

Glosten–Milgrom model, bid–ask spread, adverse selection, market maker, informed trader,
market microstructure, Bayesian updating, MSC 91B26, JEL D82, JEL G14
-/

@[expose] public section

namespace MathFin.Execution

open MeasureTheory ProbabilityTheory

variable {Ω : Type*}

/-! ## Stage 1 — the trade probabilities, derived from the trader mix -/

/-- **The informed half.** On the high-value event, every informed trader buys,
so the buy-and-informed mass is exactly the informed mass. -/
theorem inter_informed (H B I : Set Ω) (hbuy : B ∩ I = H ∩ I) :
    H ∩ B ∩ I = H ∩ I := by
  rw [Set.inter_assoc, hbuy, ← Set.inter_assoc, Set.inter_self]

/-- **The informed half, low value.** An informed trader facing a low value sells,
so the buy-and-informed mass on `Hᶜ` is empty. Derived from the same primitive —
no extra hypothesis. -/
theorem inter_informed_low (H B I : Set Ω) (hbuy : B ∩ I = H ∩ I) :
    Hᶜ ∩ B ∩ I = ∅ := by
  rw [Set.inter_assoc, hbuy, ← Set.inter_assoc, Set.compl_inter_self, Set.empty_inter]

variable [MeasurableSpace Ω] (μ : Measure Ω)

/-- **Conditioning, in `ℝ`.** `P(T | E) = P(E ∩ T) / P(E)`, with `x/0 = 0` the junk value of a
null conditioning event (there `μ[|E]` is the zero measure). -/
theorem cond_real_apply {E : Set Ω} (hE : MeasurableSet E) (T : Set Ω) :
    (μ[|E]).real T = (μ.real E)⁻¹ * μ.real (E ∩ T) := by
  simp only [measureReal_def, cond_apply hE, ENNReal.toReal_mul, ENNReal.toReal_inv]

/-- **The multiplication rule, in `ℝ`.** `P(T | E) · P(E) = P(E ∩ T)`, with no non-nullity
hypothesis: on a null `E` both sides are `0`. -/
theorem cond_real_mul_eq_inter [IsFiniteMeasure μ] {E : Set Ω} (hE : MeasurableSet E)
    (T : Set Ω) : (μ[|E]).real T * μ.real E = μ.real (E ∩ T) := by
  simp only [measureReal_def, ← ENNReal.toReal_mul, cond_mul_eq_inter hE T μ]

/-- **The trade probability, derived.** Doubling clears the uninformed `1/2`:
`2·μ(H ∩ B) = (1 + p)·θ`. -/
theorem two_mul_inter_high_buy [IsFiniteMeasure μ] (H B I : Set Ω) (hI : MeasurableSet I)
    {θ p : ℝ} (hbuy : B ∩ I = H ∩ I) (hindep : μ.real (H ∩ I) = p * θ) (hH : μ.real H = θ)
    (huninf : 2 * μ.real ((H ∩ B) \ I) = μ.real (H \ I)) :
    2 * μ.real (H ∩ B) = (1 + p) * θ := by
  have hsplitB := measureReal_inter_add_sdiff (μ := μ) (s := H ∩ B) hI
  have hsplitH := measureReal_inter_add_sdiff (μ := μ) (s := H) hI
  rw [inter_informed H B I hbuy] at hsplitB
  linarith

/-- **The trade probability on the low event, derived.** An informed trader facing a low value
sells, so only the uninformed buy there: `2·μ(Hᶜ ∩ B) = (1 - p)·θ'`, where `θ' = μ(Hᶜ)`. -/
theorem two_mul_inter_low_buy [IsFiniteMeasure μ] (H B I : Set Ω) (hI : MeasurableSet I)
    {θ' p : ℝ} (hbuy : B ∩ I = H ∩ I) (hindep : μ.real (Hᶜ ∩ I) = p * θ')
    (hHc : μ.real Hᶜ = θ') (huninf : 2 * μ.real ((Hᶜ ∩ B) \ I) = μ.real (Hᶜ \ I)) :
    2 * μ.real (Hᶜ ∩ B) = (1 - p) * θ' := by
  have hsplitB := measureReal_inter_add_sdiff (μ := μ) (s := Hᶜ ∩ B) hI
  have hsplitH := measureReal_inter_add_sdiff (μ := μ) (s := Hᶜ) hI
  rw [inter_informed_low H B I hbuy, measureReal_empty] at hsplitB
  linarith

/-- **`P(buy | V_H) = (1 + p)/2`.** -/
theorem cond_buy_high [IsFiniteMeasure μ] (H B I : Set Ω) (hH' : MeasurableSet H)
    (hI : MeasurableSet I) {θ p : ℝ} (hθ0 : θ ≠ 0) (hbuy : B ∩ I = H ∩ I)
    (hindep : μ.real (H ∩ I) = p * θ) (hH : μ.real H = θ)
    (huninf : 2 * μ.real ((H ∩ B) \ I) = μ.real (H \ I)) :
    (μ[|H]).real B = (1 + p) / 2 := by
  have h2 := two_mul_inter_high_buy μ H B I hI hbuy hindep hH huninf
  rw [cond_real_apply μ hH', hH, inv_mul_eq_div, div_eq_iff hθ0]
  linarith

/-- **`P(buy | V_L) = (1 − p)/2`.**

And note which hypothesis the proof demands: `μ Hᶜ ≠ 0`, i.e. `θ ≠ 1`. Together
with `θ ≠ 0` from the high-value case, **the model itself forces `0 < θ < 1`** —
exactly the hypothesis the issue is missing. It is not an extra condition imposed
on the theorem; it is what the derivation needs in order to exist. -/
theorem cond_buy_low [IsFiniteMeasure μ] (H B I : Set Ω) (hHc : MeasurableSet Hᶜ)
    (hI : MeasurableSet I) {θ' p : ℝ} (hθ0 : θ' ≠ 0) (hbuy : B ∩ I = H ∩ I)
    (hindep : μ.real (Hᶜ ∩ I) = p * θ') (hHc' : μ.real Hᶜ = θ')
    (huninf : 2 * μ.real ((Hᶜ ∩ B) \ I) = μ.real (Hᶜ \ I)) :
    (μ[|Hᶜ]).real B = (1 - p) / 2 := by
  have h2 := two_mul_inter_low_buy μ H B I hI hbuy hindep hHc' huninf
  rw [cond_real_apply μ hHc, hHc', inv_mul_eq_div, div_eq_iff hθ0]
  linarith


/-! ## Stage 2 — the quotes as Bochner integrals -/

/-- The two-valued asset: `V_H` on the high event `H`, `V_L` off it. Written as
a constant plus an indicator, which is what makes it integrable for free. -/
noncomputable def payoff (H : Set Ω) (VL VH : ℝ) : Ω → ℝ :=
  fun ω => VL + Set.indicator H (fun _ => VH - VL) ω

/-- **The expectation of a two-valued payoff.** Against any probability measure,
`E[V] = V_L + P(H)·(V_H − V_L)`. -/
theorem integral_payoff (ν : Measure Ω) [IsProbabilityMeasure ν] (H : Set Ω)
    (hH : MeasurableSet H) (VL VH : ℝ) :
    ∫ ω, payoff H VL VH ω ∂ν = VL + ν.real H * (VH - VL) := by
  unfold payoff
  rw [integral_add (integrable_const VL) ((integrable_const (VH - VL)).indicator hH),
    integral_const, integral_indicator_const _ hH]
  simp [measureReal_def]

/-- **The quote.** `E[V | E]` for a conditioning event of positive probability —
this is `ask` when `E` is a buy and `bid` when `E` is a sell. -/
theorem integral_payoff_cond [IsFiniteMeasure μ] (E H : Set Ω) (hH : MeasurableSet H)
    (hE0 : μ.real E ≠ 0) (VL VH : ℝ) :
    ∫ ω, payoff H VL VH ω ∂(μ[|E]) = VL + (μ[|E]).real H * (VH - VL) := by
  have : IsProbabilityMeasure (μ[|E]) :=
    cond_isProbabilityMeasure ((measureReal_ne_zero_iff (measure_ne_top μ _)).1 hE0)
  exact integral_payoff (μ[|E]) H hH VL VH

/-- **The spread, reduced to the posteriors.** Every trace of the payoff cancels
except the scale `V_H − V_L`; what is left is exactly how much a buy moves the
belief relative to a sell. Adverse selection, and nothing else, sets the spread. -/
theorem spread_eq [IsFiniteMeasure μ] (B S H : Set Ω) (hH : MeasurableSet H)
    (hB0 : μ.real B ≠ 0) (hS0 : μ.real S ≠ 0) (VL VH : ℝ) :
    (∫ ω, payoff H VL VH ω ∂(μ[|B])) - (∫ ω, payoff H VL VH ω ∂(μ[|S]))
      = (VH - VL) * ((μ[|B]).real H - (μ[|S]).real H) := by
  rw [integral_payoff_cond μ B H hH hB0 VL VH, integral_payoff_cond μ S H hH hS0 VL VH]
  ring

/-- **A null trade event does not give a bad quote — it gives no quote.**
`cond` on a null set is the *zero measure*, so the "price" integrates to `0`
whatever the asset is worth. This is what a degenerate prior can do to a quote:
at `θ = 1, p = 1` every arriving trader buys, so `Bᶜ` is null and the "bid" is
not a bad price but no price at all. `p = 1` alone is harmless and is *not*
excluded — `spread_pos_of_model` derives `p ≤ 1` rather than assuming it, and at
`p = 1` with `0 < θ < 1` both trade events still carry positive mass. It is the
prior's endpoints that have to go. -/
theorem quote_eq_zero_of_null [IsFiniteMeasure μ] (H B : Set Ω) (VL VH : ℝ) (hB : μ.real B = 0) :
    ∫ ω, payoff H VL VH ω ∂(μ[|B]) = 0 := by
  rw [cond_eq_zero_of_meas_eq_zero ((measureReal_eq_zero_iff (measure_ne_top μ _)).1 hB)]; simp

/-! ## Stage 3 — the closed form and strict positivity, in `ℝ` -/

/-- Posterior that the value is high, after a buy: `θ(1+p) / (1 + p(2θ−1))`. -/
noncomputable def postBuy (θ p : ℝ) : ℝ := (1 + p) * θ / (1 + p * (2 * θ - 1))

/-- Posterior that the value is high, after a sell: `θ(1−p) / (1 − p(2θ−1))`. -/
noncomputable def postSell (θ p : ℝ) : ℝ := (1 - p) * θ / (1 - p * (2 * θ - 1))

/-- The buy denominator is positive. Note `1 + p(2θ−1)` is *twice* `P(buy)`
(see `hBreal` in `spread_pos_of_model`), not `P(buy)` itself. Positivity holds
because it equals `(1−p) + 2pθ`, two non-negative terms with the second strictly
positive — which is the hint `nlinarith` is given, so no case split on the sign
of `2θ−1` is needed. -/
theorem buy_denom_pos {θ p : ℝ} (hθ0 : 0 < θ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 < 1 + p * (2 * θ - 1) := by
  rcases hp1.lt_or_eq with h | h
  · nlinarith [mul_nonneg hp0 hθ0.le]
  · subst h; linarith

/-- The sell denominator is positive — likewise *twice* `P(sell)` — by the mirror
identity `1 − p(2θ−1) = (1−p) + 2p(1−θ)`. -/
theorem sell_denom_pos {θ p : ℝ} (hθ1 : θ < 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 < 1 - p * (2 * θ - 1) := by
  rcases hp1.lt_or_eq with h | h
  · nlinarith [mul_nonneg hp0 (sub_pos.mpr hθ1).le]
  · subst h; linarith

/-- **The closed form of the spread's belief term** — the formula the issue's
`## Task` states, now derived:
`postBuy − postSell = 4pθ(1−θ) / (1 − p²(2θ−1)²)`.

The `θ(1−θ)` in the numerator is the whole point: it is what the acceptance
criterion forgets, and it vanishes exactly at `θ ∈ {0,1}`. -/
theorem post_sub_post {θ p : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hp0 : 0 < p)
    (hp1 : p ≤ 1) :
    postBuy θ p - postSell θ p
      = 4 * p * θ * (1 - θ) / (1 - p ^ 2 * (2 * θ - 1) ^ 2) := by
  have h1 := (buy_denom_pos hθ0 hp0.le hp1).ne'
  have h2 := (sell_denom_pos hθ1 hp0.le hp1).ne'
  have h3 : (1 : ℝ) - p ^ 2 * (2 * θ - 1) ^ 2
      = (1 + p * (2 * θ - 1)) * (1 - p * (2 * θ - 1)) := by ring
  have hD : (1 : ℝ) - p ^ 2 * (2 * θ - 1) ^ 2 ≠ 0 := by rw [h3]; exact mul_ne_zero h1 h2
  unfold postBuy postSell
  rw [div_sub_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) hD]
  ring

/-- **A buy moves the belief strictly more than a sell does.** This is the whole
economic content: the order's direction is informative, so the two quotes cannot
coincide. -/
theorem postSell_lt_postBuy {θ p : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hp0 : 0 < p)
    (hp1 : p ≤ 1) : postSell θ p < postBuy θ p := by
  have h1 := buy_denom_pos hθ0 hp0.le hp1
  have h2 := sell_denom_pos hθ1 hp0.le hp1
  have hdiff : 0 < postBuy θ p - postSell θ p := by
    rw [post_sub_post hθ0 hθ1 hp0 hp1]
    apply div_pos
    · nlinarith [mul_pos (mul_pos hp0 hθ0) (sub_pos.mpr hθ1)]
    · nlinarith
  linarith

/-- **The theorem the issue asks for**, with the hypotheses it is missing:
`ask − bid > 0` whenever `V_L < V_H`, `0 < p ≤ 1` **and `0 < θ < 1`** — where
`ask − bid = (V_H − V_L)·(postBuy − postSell)` is exactly Stage 2's `spread_eq`. -/
theorem spread_pos {θ p VL VH : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hp0 : 0 < p)
    (hp1 : p ≤ 1) (hV : VL < VH) :
    0 < (VH - VL) * (postBuy θ p - postSell θ p) :=
  mul_pos (sub_pos.mpr hV) (sub_pos.mpr (postSell_lt_postBuy hθ0 hθ1 hp0 hp1))

/-- `postSell 1 1 = 0/0`, which Lean evaluates to `0` rather than rejecting. -/
theorem postSell_one_one : postSell 1 1 = 0 := by unfold postSell; norm_num

/-- `postBuy 1 1 = 1`: after a buy the value is certainly high — which is true,
and is exactly why the *difference* below is the whole value range. -/
theorem postBuy_one_one : postBuy 1 1 = 1 := by unfold postBuy; norm_num

/-- **The punchline.** At `θ = 1, p = 1` the closed form hands back the *entire
value range* as the spread — the largest it could conceivably be — at exactly the
point where the value is common knowledge and the true spread is `0`. Nothing
errors, nothing is flagged; `0/0 = 0` does it all. A `full` entry quantified over
`p ≤ 1` and unconstrained `θ` would carry this inside it. -/
theorem spread_junk_at_corner (VL VH : ℝ) :
    (VH - VL) * (postBuy 1 1 - postSell 1 1) = VH - VL := by
  rw [postSell_one_one, postBuy_one_one]; ring

/-! ## Stage 4 — the seam -/

/-- **The unconditional probability of `E`, in `ℝ`.** The law of total
probability, converted once. -/
theorem measureReal_of_likelihoods [IsProbabilityMeasure μ] (E H : Set Ω) (hH : MeasurableSet H)
    {a c t : ℝ} (ha : (μ[|H]).real E = a) (hc : (μ[|Hᶜ]).real E = c) (ht : μ.real H = t) :
    μ.real E = a * t + c * (1 - t) := by
  have h1 := cond_real_mul_eq_inter μ hH E
  have h2 := cond_real_mul_eq_inter μ hH.compl E
  have h3 := measureReal_inter_add_sdiff (μ := μ) (s := E) hH
  rw [ha, ht, Set.inter_comm] at h1
  rw [hc, probReal_compl_eq_one_sub hH, ht, Set.inter_comm] at h2
  rw [Set.diff_eq] at h3
  linarith

/-- **THE SEAM.** Bayes' theorem in `ℝ`: the posterior on `H` after observing `E` is the Bayes
ratio of the two likelihoods against the prior.

This is what makes the stages one argument rather than three. Stage 2 hands back
`(μ[|E]).real H`; Stage 3 reasons about a ratio of real numbers; this says they
are the same number. No hypothesis that the denominator is nonzero is needed —
in the degenerate case both sides are `0`, which is precisely the behaviour the
issue's statement must not be allowed to hide. -/
theorem cond_real_eq [IsProbabilityMeasure μ] (E H : Set Ω) (hE : MeasurableSet E)
    (hH : MeasurableSet H)
    {a c t : ℝ} (ha : (μ[|H]).real E = a) (hc : (μ[|Hᶜ]).real E = c) (ht : μ.real H = t) :
    (μ[|E]).real H = a * t / (a * t + c * (1 - t)) := by
  have h1 := cond_real_mul_eq_inter μ hH E
  rw [cond_real_apply μ hE, measureReal_of_likelihoods μ E H hH ha hc ht, Set.inter_comm, ← h1,
    ha, ht, inv_mul_eq_div]

/-- **The complementary likelihood.** `P(Eᶜ | F) = 1 − P(E | F)`, in `ℝ`, given
that `F` is not null — the hypothesis the model already forces. -/
theorem cond_compl_real [IsFiniteMeasure μ] (E F : Set Ω) (hE : MeasurableSet E)
    (hF0 : μ.real F ≠ 0) : (μ[|F]).real Eᶜ = 1 - (μ[|F]).real E := by
  have : IsProbabilityMeasure (μ[|F]) :=
    cond_isProbabilityMeasure ((measureReal_ne_zero_iff (measure_ne_top μ _)).1 hF0)
  exact probReal_compl_eq_one_sub hE

/-- **The posterior after a buy is exactly `postBuy`.** Stage 3's `postBuy` was a
real function of two real numbers with no measure in sight; this is the theorem
that makes it the model's posterior. -/
theorem postBuy_eq [IsProbabilityMeasure μ] (H B : Set Ω) (hB : MeasurableSet B)
    (hH : MeasurableSet H) {θ p : ℝ} (ht : μ.real H = θ)
    (hhigh : (μ[|H]).real B = (1 + p) / 2) (hlow : (μ[|Hᶜ]).real B = (1 - p) / 2) :
    (μ[|B]).real H = postBuy θ p := by
  rw [cond_real_eq μ B H hB hH hhigh hlow ht, postBuy,
    show (1 + p) / 2 * θ + (1 - p) / 2 * (1 - θ) = (1 + p * (2 * θ - 1)) / 2 by ring,
    show (1 + p) / 2 * θ = (1 + p) * θ / 2 by ring]
  exact div_div_div_cancel_right₀ two_ne_zero _ _

/-- **The posterior after a sell is exactly `postSell`.** The sell event is
`Bᶜ` — every arriving trader either buys or sells — so the likelihoods are the
buy ones swapped, and the same seam lemma does the work.

Only `μ Hᶜ ≠ 0` (that is, `θ ≠ 1`) is taken as a hypothesis. Its mirror
`μ H ≠ 0` is *derived*: at a degenerate prior `cond` collapses to the zero
measure, so `hhigh` would read `0 = (1 + p)/2`. -/
theorem postSell_eq [IsProbabilityMeasure μ] (H B : Set Ω) (hB : MeasurableSet B)
    (hH : MeasurableSet H) {θ p : ℝ} (hp0 : 0 ≤ p) (ht : μ.real H = θ) (hHc0 : μ.real Hᶜ ≠ 0)
    (hhigh : (μ[|H]).real B = (1 + p) / 2) (hlow : (μ[|Hᶜ]).real B = (1 - p) / 2) :
    (μ[|Bᶜ]).real H = postSell θ p := by
  have hH0 : μ.real H ≠ 0 := by
    intro h
    have hz : (μ[|H]).real B = 0 := by
      rw [cond_eq_zero_of_meas_eq_zero ((measureReal_eq_zero_iff (measure_ne_top μ _)).1 h)]
      simp [measureReal_def]
    linarith
  have hsa : (μ[|H]).real Bᶜ = (1 - p) / 2 := by
    rw [cond_compl_real μ B H hB hH0, hhigh]; ring
  have hsc : (μ[|Hᶜ]).real Bᶜ = (1 + p) / 2 := by
    rw [cond_compl_real μ B Hᶜ hB hHc0, hlow]; ring
  rw [cond_real_eq μ Bᶜ H hB.compl hH hsa hsc ht, postSell,
    show (1 - p) / 2 * θ + (1 + p) / 2 * (1 - θ) = (1 - p * (2 * θ - 1)) / 2 by ring,
    show (1 - p) / 2 * θ = (1 - p) * θ / 2 by ring]
  exact div_div_div_cancel_right₀ two_ne_zero _ _

/-- **Glosten–Milgrom: the spread is strictly positive.** The market maker's ask
and bid are `∫ V ∂μ[|buy]` and `∫ V ∂μ[|sell]`, and the first strictly exceeds
the second whenever `V_L < V_H`, `0 < p ≤ 1` **and `0 < θ < 1`**.

This is the issue's `## Acceptance criteria`, with the hypothesis it omits. The
chain is: Stage 1 derives the trade probabilities from the trader mix; Stage 4
applies Bayes to get the posteriors; Stage 2 turns the quotes
into those posteriors; Stage 3 supplies the strict inequality. -/
theorem spread_pos_of_model [IsProbabilityMeasure μ] (H B I : Set Ω)
    (hH : MeasurableSet H) (hB : MeasurableSet B) (hI : MeasurableSet I)
    {θ p VL VH : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hp0 : 0 < p) (hV : VL < VH)
    (hprior : μ.real H = θ)
    (hbuy : B ∩ I = H ∩ I)
    (hindepH : μ.real (H ∩ I) = p * θ)
    (hindepHc : μ.real (Hᶜ ∩ I) = p * (1 - θ))
    (huninfH : 2 * μ.real ((H ∩ B) \ I) = μ.real (H \ I))
    (huninfHc : 2 * μ.real ((Hᶜ ∩ B) \ I) = μ.real (Hᶜ \ I)) :
    0 < (∫ ω, payoff H VL VH ω ∂(μ[|B])) - (∫ ω, payoff H VL VH ω ∂(μ[|Bᶜ])) := by
  -- `p ≤ 1` is not a hypothesis: the informed mass cannot exceed the prior.
  have hp1 : p ≤ 1 := by
    have h := measureReal_mono (μ := μ) (Set.inter_subset_left (s := H) (t := I))
    rw [hindepH, hprior] at h
    nlinarith
  have hpriorc : μ.real Hᶜ = 1 - θ := by rw [probReal_compl_eq_one_sub hH, hprior]
  have hH0 : μ.real H ≠ 0 := by rw [hprior]; exact hθ0.ne'
  have hHc0 : μ.real Hᶜ ≠ 0 := by rw [hpriorc]; exact (sub_pos.2 hθ1).ne'
  -- Stage 1: the trade probabilities, derived from the trader mix
  have hhigh := cond_buy_high μ H B I hH hI hθ0.ne' hbuy hindepH hprior huninfH
  have hlow := cond_buy_low μ H B I hH.compl hI (sub_pos.2 hθ1).ne' hbuy hindepHc hpriorc huninfHc
  -- both trade events have positive probability, so neither conditioning is vacuous
  have hsa : (μ[|H]).real Bᶜ = (1 - p) / 2 := by
    rw [cond_compl_real μ B H hB hH0, hhigh]; ring
  have hsc : (μ[|Hᶜ]).real Bᶜ = (1 + p) / 2 := by
    rw [cond_compl_real μ B Hᶜ hB hHc0, hlow]; ring
  have hBreal : μ.real B = (1 + p * (2 * θ - 1)) / 2 := by
    rw [measureReal_of_likelihoods μ B H hH hhigh hlow hprior]; ring
  have hBcreal : μ.real Bᶜ = (1 - p * (2 * θ - 1)) / 2 := by
    rw [measureReal_of_likelihoods μ Bᶜ H hH hsa hsc hprior]; ring
  have hB0 : μ.real B ≠ 0 := by
    rw [hBreal]; exact (div_pos (buy_denom_pos hθ0 hp0.le hp1) two_pos).ne'
  have hBc0 : μ.real Bᶜ ≠ 0 := by
    rw [hBcreal]; exact (div_pos (sell_denom_pos hθ1 hp0.le hp1) two_pos).ne'
  -- Stage 2 reduces the quotes to the posteriors; Stage 4 names them; Stage 3 closes
  rw [spread_eq μ B Bᶜ H hH hB0 hBc0 VL VH, postBuy_eq μ H B hB hH hprior hhigh hlow,
    postSell_eq μ H B hB hH hp0.le hprior hHc0 hhigh hlow]
  exact spread_pos hθ0 hθ1 hp0 hp1 hV

end MathFin.Execution
