/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Models.LocalVol.Dupire
public import MathFin.Models.ModelFree.RoperConverse

/-!
# The call surface of a market

`Dupire.callSurface μ X s K = 𝔼_μ[(X_{s⁺} − K)⁺]` is defined for any process and any measure. Here
it is tied to the pricing functional: in a market with unit numéraire, the price of the European
call at `K` and `T` under `Q` is the call surface of the asset under `Q` at `(T, K)`. Two things
follow.

* The Breeden–Litzenberger statements of `Dupire.lean` read as statements about the market's
  prices: under a pricing measure, the strike derivative of the call prices is the digital price
  `−Q(S_T > K)` and, weakly, the second strike derivative is the law of `S_T`.
* Roper's converse (`exists_market_of_isNormalizedCallPrice`) makes every normalised call price
  function the call surface of a market under a pricing measure.

Dupire's equation (`Dupire.dupire_pointwise`) needs the asset to be an Itô process with bounded
continuous diffusion coefficient. A `Market` carries no such structure, so
`Market.dupire_price_europeanCall` takes it as a hypothesis on the asset and states Dupire's
formula for the market's own call prices.

## Main results

* `Market.price_europeanCall_eq_callSurface`: with unit numéraire, the call price is the call
  surface of the asset.
* `exists_market_callSurface_eq`: a normalised call price function is, at strikes `K > 0`, the call
  surface at time `1` of a market under a pricing measure.
* `Market.IsPricingMeasure.hasDerivAt_price_europeanCall`: where the call price has a strike
  derivative, it is `−Q(S_T > K)`.
* `Market.IsPricingMeasure.integral_deriv_deriv_mul_price_europeanCall`: the weak
  Breeden–Litzenberger identity `∫ ψ''(K) · price(call K) dK = 𝔼_Q[ψ(S_T)]` for the market's call
  prices.
* `Market.dupire_price_europeanCall`: Dupire's formula `σloc(K)² = 2 C_T / (K² C_KK)` for the
  market's call prices, when the asset is an Itô process under `Q`.

## References

* [Breeden and Litzenberger, *Prices of state-contingent claims implicit in option
  prices*][BreedenLitzenberger1978]
* [Dupire, *Pricing with a smile*][Dupire1994]
* [Roper, *Arbitrage free implied volatility surfaces*][Roper2010], Theorem 2.1

## Tags

call surface, pricing measure, Breeden-Litzenberger, Dupire, risk-neutral density,
MSC 91G20, JEL G13
-/

@[expose] public section

open MeasureTheory Set MathFin.Contracts
open scoped NNReal ContDiff

namespace MathFin

namespace Market

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {M : Market Unit Ω} {T : ℝ≥0} {Q : Measure Ω}

/-- **The call price is the call surface.** With unit numéraire, the price under `Q` of the
European call at strike `K` and maturity `T` is `Dupire.callSurface Q (M.asset ()) T K`. -/
theorem price_europeanCall_eq_callSurface (hN : ∀ t x, M.numeraire t x = 1) (K : ℝ) :
    M.price Q (europeanCall K T) = Dupire.callSurface Q (M.asset ()) T K := by
  simp [price_europeanCall_of_numeraire_eq_one hN, Dupire.callSurface]

/-- **The call prices have strike derivative minus the digital.** In a market with unit numéraire,
where the strike map `K ↦ price (call K T)` has a derivative `d` at `K`, under a pricing measure
`d = −Q(S_T > K)`. -/
theorem IsPricingMeasure.hasDerivAt_price_europeanCall (hQ : M.IsPricingMeasure T Q)
    (hN : ∀ t x, M.numeraire t x = 1) {K d : ℝ}
    (hd : HasDerivAt (fun K ↦ M.price Q (europeanCall K T)) d K) :
    d = -Q.real {x | K < M.asset () T x} := by
  have := hQ.isProb
  have hfun : (fun K ↦ M.price Q (europeanCall K T)) = Dupire.callSurface Q (M.asset ()) T :=
    funext (price_europeanCall_eq_callSurface hN)
  simpa using Dupire.strikeDeriv_callSurface_eq_neg_tail (s := T)
    (by simpa using M.measurable_asset () T) (by simpa using hQ.integrable_asset hN) (hfun ▸ hd)

/-- **Breeden–Litzenberger for the market's call prices (weak form).** In a market with unit
numéraire under a pricing measure `Q`, for every smooth compactly supported `ψ`,
`∫ ψ''(K) · price(call K, T) dK = 𝔼_Q[ψ(S_T)]`: the second strike derivative of the call prices
is the `Q`-law of `S_T` as a distribution. -/
theorem IsPricingMeasure.integral_deriv_deriv_mul_price_europeanCall
    (hQ : M.IsPricingMeasure T Q) (hN : ∀ t x, M.numeraire t x = 1) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    ∫ K, deriv (deriv ψ) K * M.price Q (europeanCall K T) = ∫ x, ψ (M.asset () T x) ∂Q := by
  have := hQ.isProb
  simpa [price_europeanCall_eq_callSurface hN] using
    Dupire.breedenLitzenberger_weak (μ := Q) (X := M.asset ()) (s := T)
      (by simpa using hQ.integrable_asset hN) hψ hψc

section Dupire

open ProbabilityTheory MathFin.GyongyMimicry

/-- **Dupire's formula for the market's call prices (zero rates).** In a market with unit numéraire
whose asset is, under a probability measure `Q`, the Itô process `c + Y` driven by a Brownian
motion (`Dupire.dupire_pointwise`), let `σloc(K)² K²` be a continuous version of
`𝔼_Q[δ_t² | S_t = K]` on a window `(a, b) ⊆ [0, ∞)` of strikes. If the market's call prices
`C(s, K) = price(call K, s)` have strike derivatives `C_K`, `C_KK` and a maturity derivative `C_T`
on the window, then `σloc(K)² = 2 C_T(t, K) / (K² C_KK(t, K))` at every strike of the window with
`C_KK > 0`. The derivatives of the price surface are hypotheses. -/
theorem dupire_price_europeanCall [IsProbabilityMeasure Q] (hN : ∀ t x, M.numeraire t x = 1)
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B Q) (hBmeas : ∀ t, Measurable (B t))
    {H : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ} {Y : ℝ≥0 → Ω → ℝ}
    (hD : ItoDriftConditional.IsAdaptedItoDrift hB hBmeas H δ Dd Y) (c : ℝ)
    (hScont : ∀ ω, Continuous fun s : ℝ≥0 ↦ M.asset () s ω)
    (hSrel : ∀ t : ℝ≥0, M.asset () t = fun ω : Ω ↦ c + Y t ω)
    (t : ℝ) (ht : 0 < t) (htH : Real.toNNReal t < H)
    {a b ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) {CK CKK : ℝ → ℝ} {Ct : ℝ → ℝ → ℝ}
    (hCK : ∀ K ∈ Ioo a b,
      HasDerivAt (fun K ↦ M.price Q (europeanCall K (Real.toNNReal t))) (CK K) K)
    (hCKK : ∀ K ∈ Ioo a b, HasDerivAt CK (CKK K) K)
    (hCKKc : ContinuousOn CKK (Ioo a b))
    (hCt : ∀ s ∈ Ioo (t - ε) (t + ε), ∀ K ∈ Ioo a b,
      HasDerivAt (fun s' ↦ M.price Q (europeanCall K (Real.toNNReal s'))) (Ct s K) s)
    (hCtc : ContinuousOn (Function.uncurry Ct) (Ioo (t - ε) (t + ε) ×ˢ Ioo a b))
    {σloc : ℝ → ℝ} (hσc : ContinuousOn σloc (Ioo a b))
    (hσrep : ∀ᵐ ω ∂Q, M.asset () (Real.toNNReal t) ω ∈ Ioo a b →
      diffCoeffSq Q (reindexed (M.asset ())) (reindexed δ) t ω
        = σloc (M.asset () (Real.toNNReal t) ω) ^ 2 * M.asset () (Real.toNNReal t) ω ^ 2) :
    ∀ K ∈ Ioo a b, 0 < CKK K → σloc K ^ 2 = 2 * Ct t K / (K ^ 2 * CKK K) := by
  have hC (s K : ℝ) :
      M.price Q (europeanCall K (Real.toNNReal s)) = Dupire.callSurface Q (M.asset ()) s K := by
    simp only [price_europeanCall_of_numeraire_eq_one hN, Dupire.callSurface]
  exact Dupire.dupire_pointwise hB hBmeas hD c hScont hSrel t ht htH ha hε
    (by simpa only [hC] using hCK) hCKK hCKKc (by simpa only [hC] using hCt) hCtc hσc hσrep

end Dupire

end Market

/-- **Every normalised call price function is a market's call surface.** For a normalised call price
function `C` there are a market with unit numéraire, a nonnegative asset, and a pricing measure
`Q` up to time `1` under which `C K` is the call surface of the asset at time `1`, for every
strike `K > 0`. -/
theorem exists_market_callSurface_eq {C : ℝ → ℝ} (hC : IsNormalizedCallPrice C) :
    ∃ (M : Market Unit ℝ) (Q : Measure ℝ), (∀ t x, M.numeraire t x = 1) ∧
      (∀ x, 0 ≤ M.asset () 1 x) ∧ M.IsPricingMeasure 1 Q ∧
      ∀ K > 0, C K = Dupire.callSurface Q (M.asset ()) 1 K := by
  obtain ⟨M, Q, hN, hnn, hQ, -, hC'⟩ := exists_market_of_isNormalizedCallPrice hC
  exact ⟨M, Q, hN, hnn, hQ, fun K hK ↦
    (hC' K hK).symm.trans (by simpa using Market.price_europeanCall_eq_callSurface (T := 1) hN K)⟩

end MathFin
