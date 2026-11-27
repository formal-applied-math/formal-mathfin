/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Init
public import MathFin.Models.ModelFree.CarrMadanMarket

/-!
# Gamma swap replication and fair strike

A **gamma swap** is a variance swap whose floating leg weights the squared return by the
price level: with notional `N` it pays `N·(T⁻¹∫₀ᵀ σ_t²·(S_t/S₀) dt − K_Γ)` (Jacquier–Slaoui,
§2). Its static replication runs through the entropy-anchored payoff
`φ(x) = x·log(x/κ) − x + κ`, whose convexity is `φ″(K) = 1/K`: where the log payoff's
Carr–Madan weight is `−1/K²` (the variance swap's strip), the gamma swap's is `1/K`.

We prove the replication and the fair strike in the market form of
`Market.IsPricingMeasure.integral_eq_carrMadan` (compact strike range, unit numéraire).
The payoff `φ` vanishes with its first derivative at the reference level `κ`, so its
spanning identity has no cash or forward leg at all:

* `gammaSwapPayoff_eq_strip`: pathwise, `φ(S)` *is* the `1/K` strip — puts on `[L, κ]`
  plus calls on `[κ, U]`, each weighted by `1/K`.
* `Market.IsPricingMeasure.integral_eq_gammaSwap`: under a pricing measure, the expected
  payoff `𝔼_Q[φ(S_T)]` is the market price of that `1/K` strip.
* `Market.gammaSwapFairStrike`: the fair strike `K_Γ` as twice the strip's market price
  per `κ·T` — Jacquier–Slaoui's `K_Γ = (2e^{2rT}/(T S₀))[∫ P/K + ∫ C/K]` at the zero-rate,
  numéraire-discounted instance where the factor collapses to `2` (reference level `κ`
  in the `S₀` slot, compact range).
* `Market.IsPricingMeasure.gammaSwapFairStrike_eq_integral`: the fair strike is also
  twice the expected replication payoff per `κ·T`, `K_Γ = 2𝔼_Q[φ(S_T)]/(κT)` — the
  expectation-level reading of the floating leg.

The mark-to-market formula, the Greeks and the dispersion decomposition of the source
need the forward dynamics of `S` and a multi-asset index; they are not treated here. The
strike range is bounded and `S_T` is assumed to stay in it; the unbounded strip is not
assembled.

## Main definitions

* `gammaSwapPayoff κ x`: the replication payoff `x·log(x/κ) − x + κ`; it is the payoff
  meant by the strip identity at `x > 0` with `κ > 0` (outside that quadrant the
  logarithm is out of its domain and the value is junk).
* `Market.gammaSwapFairStrike M T Q κ L U`: twice the market price of the `1/K` strip
  per `κ·T`; it is the fair strike under `0 < κ`, `0 < T` and `0 < L ≤ κ ≤ U`. The
  division is junk at `κ ≤ 0` or `T = 0`; outside the ordering it is well defined but
  is not a fair strike.

## Main results

* `gammaSwapPayoff_eq_strip`: the payoff equals the `1/K`-weighted strip, pathwise on
  the strike range.
* `Market.IsPricingMeasure.integral_eq_gammaSwap`: the expected payoff is the market
  price of the `1/K` strip.
* `Market.IsPricingMeasure.gammaSwapFairStrike_eq_integral`: the fair strike equals
  twice the expected payoff per `κ·T`.

## References

* [Jacquier and Slaoui, *Variance dispersion and correlation swaps*][JacquierSlaoui2010], §2
* [Carr and Madan (2001)][CarrMadan2001]
* [Demeterfi et al., *More than you ever wanted to know about volatility
  swaps*][DemeterfiDermanKamalZou1999]

## Tags

gamma swap, variance swap, static replication, strip of options, Carr–Madan formula,
fair strike, JEL G13, MSC 91G20
-/

@[expose] public section

namespace MathFin

open MeasureTheory Set MathFin.Contracts

/-- The gamma swap's replication payoff: `x·log(x/κ) − x + κ` (Jacquier–Slaoui, §2, the
function `φ = e^{−rT}f` with `f(F_t) = e^{rt}(F_t log(F_t/F₀) − F_t + F₀)`). Its convexity
is `x ↦ x⁻¹`, the `1/K` weight of the gamma swap's strip, and it vanishes with its first
derivative at `κ` — so its spanning identity has no cash or forward leg. The payoff and
the convexity are meant at `x > 0` with `κ > 0`; outside that quadrant the logarithm is
out of its domain and the value is junk (at `κ ≤ 0` with `x > 0` it reads `−x + κ`). -/
noncomputable def gammaSwapPayoff (κ x : ℝ) : ℝ := x * Real.log (x / κ) - x + κ

/-- The first two derivatives of the replication payoff: `φ′(x) = log(x/κ)` (whose value
at `κ` is `0`) and `φ″(x) = x⁻¹`, the `1/K` weight of the gamma swap's strip. -/
private theorem gammaSwapPayoff_derivs {κ x : ℝ} (hκ : 0 < κ) (hx : 0 < x) :
    HasDerivAt (gammaSwapPayoff κ) (Real.log (x / κ)) x
      ∧ HasDerivAt (fun y : ℝ ↦ Real.log (y / κ)) x⁻¹ x := by
  have hdiv : HasDerivAt (fun y : ℝ ↦ y / κ) (1 / κ) x := (hasDerivAt_id' x).div_const κ
  have hlog : HasDerivAt (fun y : ℝ ↦ Real.log (y / κ)) x⁻¹ x := by
    have h : HasDerivAt (Real.log ∘ fun y : ℝ ↦ y / κ) ((x / κ)⁻¹ * (1 / κ)) x :=
      (Real.hasDerivAt_log (show x / κ ≠ 0 by positivity)).comp x hdiv
    convert h using 1
    · simp [Function.comp_def]
    · field_simp
  refine ⟨?_, hlog⟩
  have h1 : HasDerivAt (fun y : ℝ ↦ y * Real.log (y / κ))
      (Real.log (x / κ) + x * x⁻¹) x := by
    convert (hasDerivAt_id' x).mul hlog using 1
    · simp
  convert ((h1.sub (hasDerivAt_id' x)).add_const κ) using 1
  · rfl
  · simp [mul_inv_cancel₀ hx.ne']

/-- **Gamma swap replication (pathwise).** On a positive strike range `0 < L ≤ κ ≤ U`, the
replication payoff is exactly its `1/K` strip — the payoff *is* the static book of puts on
`[L, κ]` and calls on `[κ, U]`, each weighted by `1/K`:

  `x·log(x/κ) − x + κ = ∫_L^κ K⁻¹·(K − S)⁺ dK + ∫_κ^U K⁻¹·(S − K)⁺ dK`.

Specialises `carrMadan_spanning` to the entropy-anchored payoff; the cash and forward
legs vanish because `φ(κ) = φ′(κ) = 0`. -/
theorem gammaSwapPayoff_eq_strip {L U κ S : ℝ} (hL : 0 < L) (hLκ : L ≤ κ) (hκU : κ ≤ U)
    (hS : S ∈ Set.Icc L U) :
    gammaSwapPayoff κ S
      = (∫ K in L..κ, K⁻¹ * max (K - S) 0) + (∫ K in κ..U, K⁻¹ * max (S - K) 0) := by
  have hpos : ∀ t ∈ Set.Icc L U, 0 < t := fun t ht ↦ lt_of_lt_of_le hL ht.1
  have hκpos : 0 < κ := hpos κ ⟨hLκ, hκU⟩
  have hκ : κ ≠ 0 := hκpos.ne'
  have h := carrMadan_spanning (f := gammaSwapPayoff κ) (f' := fun t ↦ Real.log (t / κ))
    (f'' := fun K ↦ K⁻¹) hLκ hκU hS
    (fun t ht ↦ (gammaSwapPayoff_derivs hκpos (hpos t ht)).1)
    (fun t ht ↦ (gammaSwapPayoff_derivs hκpos (hpos t ht)).2)
    (continuousOn_id.inv₀ fun K hK ↦ (hpos K hK).ne')
  have hzero : gammaSwapPayoff κ κ = 0 := by simp [gammaSwapPayoff, div_self hκ]
  have hlogzero : Real.log (κ / κ) = 0 := by rw [div_self hκ, Real.log_one]
  rw [hzero, hlogzero, zero_mul, add_zero, zero_add] at h
  exact h

end MathFin

namespace MathFin.Market

open MeasureTheory Set MathFin.Contracts
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Gamma swap replication in a market.** In a market with unit numéraire, let `Q` be a
pricing measure up to `T` under which `S_T ∈ [L, U]` almost surely, with `0 < L ≤ κ ≤ U`.
The expected replication payoff is the market price of the gamma swap's `1/K` strip:

  `𝔼_Q[φ(S_T)] = ∫_L^κ K⁻¹·P(K) dK + ∫_κ^U K⁻¹·C(K) dK`,

with `P(K)`, `C(K)` the market's prices of the European put and call at strike `K` and
maturity `T`. Instantiates `IsPricingMeasure.integral_eq_carrMadan` at the entropy-anchored
payoff; its cash and forward legs vanish since `φ(κ) = φ′(κ) = 0`. -/
theorem IsPricingMeasure.integral_eq_gammaSwap {M : Market Unit Ω} {T : ℝ≥0}
    {Q : Measure Ω} (hQ : M.IsPricingMeasure T Q) (hN : ∀ t x, M.numeraire t x = 1)
    {L U κ : ℝ} (hL : 0 < L) (hLκ : L ≤ κ) (hκU : κ ≤ U)
    (hS : ∀ᵐ x ∂Q, M.asset () T x ∈ Icc L U) :
    ∫ x, gammaSwapPayoff κ (M.asset () T x) ∂Q
      = (∫ K in L..κ, K⁻¹ * M.price Q (europeanPut K T))
        + ∫ K in κ..U, K⁻¹ * M.price Q (europeanCall K T) := by
  have hpos : ∀ t ∈ Icc L U, 0 < t := fun t ht ↦ lt_of_lt_of_le hL ht.1
  have hκpos : 0 < κ := hpos κ ⟨hLκ, hκU⟩
  have hκ : κ ≠ 0 := hκpos.ne'
  have h := hQ.integral_eq_carrMadan hN hLκ hκU hS
    (fun t ht ↦ (gammaSwapPayoff_derivs hκpos (hpos t ht)).1)
    (fun t ht ↦ (gammaSwapPayoff_derivs hκpos (hpos t ht)).2)
    (continuousOn_id.inv₀ fun K hK ↦ (hpos K hK).ne')
  have hzero : gammaSwapPayoff κ κ = 0 := by simp [gammaSwapPayoff, div_self hκ]
  have hlogzero : Real.log (κ / κ) = 0 := by rw [div_self hκ, Real.log_one]
  rw [hzero, hlogzero, zero_mul, add_zero, zero_add] at h
  exact h

/-- The gamma swap's fair strike: twice the market price of its `1/K` strip per `κ·T`,
with `P(K)` and `C(K)` the market's prices of the European put and call at strike `K` and
maturity `T`. This is Jacquier–Slaoui's `K_Γ^{0,T} = (2e^{2rT}/(T S₀))[∫₀^{F₀} P/K dK
+ ∫_{F₀}^∞ C/K dK]` at the substitutions the numéraire convention makes (`r = 0`, so the
factor is `2`; the reference level `κ` in the `S₀` slot, at the at-the-money forward
`κ = F₀`); the unbounded strip of the source is cut to the compact range. The value is
the fair strike under `0 < κ`, `0 < T` and `0 < L ≤ κ ≤ U`; the division is junk at
`κ ≤ 0` or `T = 0`, and outside the ordering it is well defined but is not a fair strike. -/
noncomputable def gammaSwapFairStrike (M : Market Unit Ω) (T : ℝ≥0) (Q : Measure Ω)
    (κ L U : ℝ) : ℝ :=
  2 / (κ * (T : ℝ)) *
    ((∫ K in L..κ, K⁻¹ * M.price Q (europeanPut K T))
      + ∫ K in κ..U, K⁻¹ * M.price Q (europeanCall K T))

/-- **Fair strike equals the expected replication payoff.** Under the hypotheses of
`IsPricingMeasure.integral_eq_gammaSwap`, twice the expected replication payoff per `κ·T`
is the fair strike: `K_Γ = 2𝔼_Q[φ(S_T)]/(κT)`. Under the Itô dynamics of the source's §2
this is the level its floating leg `T⁻¹𝔼[∫₀ᵀ σ_t²·(S_t/κ) dt]` reads at; the dynamics step
is the source's, not proved here (this module has no process). -/
theorem IsPricingMeasure.gammaSwapFairStrike_eq_integral {M : Market Unit Ω} {T : ℝ≥0}
    {Q : Measure Ω} (hQ : M.IsPricingMeasure T Q) (hN : ∀ t x, M.numeraire t x = 1)
    {L U κ : ℝ} (hL : 0 < L) (hLκ : L ≤ κ) (hκU : κ ≤ U)
    (hS : ∀ᵐ x ∂Q, M.asset () T x ∈ Icc L U) :
    2 / (κ * (T : ℝ)) * ∫ x, gammaSwapPayoff κ (M.asset () T x) ∂Q
      = M.gammaSwapFairStrike T Q κ L U := by
  rw [gammaSwapFairStrike, hQ.integral_eq_gammaSwap hN hL hLκ hκU hS]

end MathFin.Market
