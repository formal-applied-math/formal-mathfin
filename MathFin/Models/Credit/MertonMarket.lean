/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Models.BlackScholes.Market
public import MathFin.Models.BlackScholes.PricingFromBrownian
public import MathFin.Models.Credit.KMVMertonStructural

/-!
# Merton's structural model as a market

Merton's firm has assets `V` following the Black–Scholes market (`BlackScholes.market`: `V` is the
traded asset, the money market `e^{rt}` the numéraire) and zero-coupon debt of face `F` due at
`T`. At `T` the shareholders receive `(V_T − F)⁺`, a European call on the firm's assets
(`europeanCall F T`), and the creditors `min (V_T, F)` (`defaultableZCB F T`), the face value less
a put. The Girsanov measure of the constant market price of risk is a pricing measure of this
market (`BlackScholes.isPricingMeasure_constGirsanovMeasure`), and under it:

* the equity is worth the Black–Scholes call price;
* the debt is worth the firm's value less the equity, `V₀ − C₀`, which is the balance-sheet
  identity of the two claims (`price_defaultableZCB_add_price_europeanCall`);
* the probability that the firm is in default at `T`, `V_T ≤ F`, is `kmvPD`, the Merton–KMV
  default probability `Φ(−d₂)` (`merton_market`).

The market is the one-asset Black–Scholes market of the firm; default is observed at the maturity
of the debt only, so first-passage (Black–Cox) default and coupons are not covered.

## Main definitions

* `MathFin.Contracts.defaultableZCB`: a zero-coupon bond of face `F` on a firm of assets `V`,
  paying `min (V_T, F)` at `T`.

## Main results

* `MathFin.Contracts.Merton.price_defaultableZCB_add_price_europeanCall`: in any market, under a
  pricing measure, the debt and the equity of a firm with nonnegative assets sum to the price of
  its assets.
* `MathFin.Contracts.Merton.merton_market`: in the Black–Scholes market of the firm, the
  Girsanov measure of the market price of risk is a pricing measure; it prices the equity at the
  Black–Scholes call price and the debt at `V₀` less that; and the default probability is
  `kmvPD`. Its conjuncts are named: `price_defaultableZCB_constGirsanovMeasure` (the debt is
  worth `V₀` less the equity) and `real_default_constGirsanovMeasure` (the default probability),
  beside the pricing-measure and call-price theorems of `BlackScholes`.

## References

* [R. C. Merton, *On the pricing of corporate debt: the risk structure of interest
  rates*][Merton1974]
* [F. Black and M. Scholes, *The pricing of options and corporate liabilities*][BlackScholes1973]
* [D. Lando, *Credit Risk Modeling*][Lando2004], Section 2.2

## Tags

Merton model, structural credit model, equity as call option, defaultable bond, risk-neutral
default probability, pricing measure, MSC 91G40, MSC 91G20, JEL G12, JEL G33
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal
open MathFin MathFin.Contracts MathFin.Contracts.BlackScholes

namespace MathFin.Contracts

/-- The **defaultable zero-coupon bond** of face `F` due at `T` on a firm whose assets are the
underlying: it pays `min (V_T, F)`, the face value if the assets cover it and the assets
otherwise. -/
noncomputable def defaultableZCB (F : ℝ) (T : ℝ≥0) : Contract Unit :=
  .pay T (.min (.obs () T) (.const F))

namespace Merton

/-- **Debt and equity add up to the firm.** In a market with deterministic initial numéraire
`n₀`, under a pricing measure up to `T`, for a firm whose assets are nonnegative at `T` and a
face value `F ≥ 0`, the defaultable bond and the European call on the assets (the equity) together
are worth `𝔼_Q[V₀]`, the price of the assets: `min (V_T, F) + (V_T − F)⁺ = V_T`. -/
theorem price_defaultableZCB_add_price_europeanCall {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (M : Market Unit Ω) {T : ℝ≥0} {Q : Measure Ω} (hQ : M.IsPricingMeasure T Q) {n₀ : ℝ}
    (hN₀ : ∀ ω, M.numeraire 0 ω = n₀) (hS : ∀ ω, 0 ≤ M.asset () T ω) {F : ℝ} (hF : 0 ≤ F) :
    M.price Q (defaultableZCB F T) + M.price Q (europeanCall F T)
      = ∫ ω, M.asset () 0 ω ∂Q := by
  have := hQ.isProb
  rw [← hQ.price_pay_obs hN₀ () le_rfl]
  have hD (ω : Ω) : 0 ≤ M.deflator T ω := (M.deflator_pos T ω).le
  have hSint : Integrable (fun ω ↦ M.deflator T ω * M.asset () T ω) Q := by
    have h := (hQ.martingale ()).integrable T
    simp only [min_self] at h
    refine (h.const_mul n₀).congr (.of_forall fun ω ↦ ?_)
    simp only [Market.deflator, Market.deflated, hN₀]
    ring
  have hint (f : ℝ → ℝ) (hf : Measurable f) (h0 : ∀ x, 0 ≤ x → 0 ≤ f x)
      (h1 : ∀ x, 0 ≤ x → f x ≤ x) :
      Integrable (fun ω ↦ M.deflator T ω * f (M.asset () T ω)) Q :=
    hSint.mono'
      ((M.measurable_deflator T).mul (hf.comp (M.measurable_asset () T))).aestronglyMeasurable
      (.of_forall fun ω ↦ by
        rw [Real.norm_of_nonneg (mul_nonneg (hD ω) (h0 _ (hS ω)))]
        exact mul_le_mul_of_nonneg_left (h1 _ (hS ω)) (hD ω))
  have h1 : Integrable (fun ω ↦ M.deflator T ω * min (M.asset () T ω) F) Q :=
    hint (fun x ↦ min x F) (measurable_id.min measurable_const) (fun x hx ↦ le_min hx hF)
      fun x _ ↦ min_le_left _ _
  have h2 : Integrable (fun ω ↦ M.deflator T ω * max (M.asset () T ω - F) 0) Q :=
    hint (fun x ↦ max (x - F) 0) ((measurable_id.sub_const F).max measurable_const)
      (fun x _ ↦ le_max_right _ _) fun x hx ↦ max_le (sub_le_self _ hF) hx
  simp only [Market.price, defaultableZCB, europeanCall, europeanCallPayoff, Contract.value_pay,
    Payoff.eval, scenarioAt]
  rw [← integral_add h1 h2]
  refine integral_congr_ae (.of_forall fun ω ↦ ?_)
  beta_reduce
  rw [← mul_add]
  congr 1
  rcases le_total (M.asset () T ω) F with h | h
  · rw [min_eq_left h, max_eq_right (sub_nonpos.2 h), add_zero]
  · rw [min_eq_right h, max_eq_left (sub_nonneg.2 h)]
    ring

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {W : ℝ≥0 → Ω → ℝ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] (hW : IsPreBrownianReal W μ) (hWmeas : ∀ t, Measurable (W t))

include hW in
/-- **The defaultable bond of Merton's firm** is worth `V₀` less the equity: under the Girsanov
measure `Q` of the constant market price of risk `(m − r)/σ` at the horizon `H ≥ T`, in the
Black–Scholes market of the firm (spot `V₀ > 0`, drift `m`, rate `r`, volatility `σ > 0`), the
defaultable zero-coupon bond of face `F > 0` due at `T` is worth `V₀` less the Black–Scholes call
price. It is the balance-sheet identity (`price_defaultableZCB_add_price_europeanCall`) at the
pricing measure `Q`, with the equity priced by `price_europeanCall_constGirsanovMeasure`. -/
theorem price_defaultableZCB_constGirsanovMeasure {V₀ F m r σ : ℝ} {T H : ℝ≥0} (hTH : T ≤ H)
    (hV₀ : 0 < V₀) (hF : 0 < F) (hσ : 0 < σ) (hT : 0 < (T : ℝ)) :
    (market μ hWmeas V₀ m r σ).price (constGirsanovMeasure hW hWmeas ((m - r) / σ) H)
        (defaultableZCB F T)
      = V₀ - (V₀ * Phi (bsd1 V₀ F r σ T) - F * Real.exp (-r * T) * Phi (bsd2 V₀ F r σ T)) := by
  have hQp := constGirsanovMeasure_isProbabilityMeasure hW hWmeas ((m - r) / σ) H
  have hQ := isPricingMeasure_constGirsanovMeasure hW hWmeas (S_0 := V₀) (m := m) (r := r)
    hσ.ne' hTH
  have hcall := price_europeanCall_constGirsanovMeasure hW hWmeas (m := m) (r := r) (K := F)
    hTH hV₀ hF hσ hT
  have hac : constGirsanovMeasure hW hWmeas ((m - r) / σ) H ≪ μ :=
    withDensity_absolutelyContinuous _ _
  have h0 : ∀ᵐ ω ∂(constGirsanovMeasure hW hWmeas ((m - r) / σ) H),
      (market μ hWmeas V₀ m r σ).asset () 0 ω = V₀ :=
    hac.ae_le (hW.eval_zero_ae_eq_zero.mono fun ω h ↦ by simp [market, pathAssets, h])
  have hsum := price_defaultableZCB_add_price_europeanCall (market μ hWmeas V₀ m r σ) hQ
    (n₀ := 1) (fun ω ↦ by simp [market]) (F := F)
    (fun ω ↦ (mul_pos hV₀ (Real.exp_pos _)).le) hF.le
  rw [integral_congr_ae h0, integral_const, probReal_univ, one_smul, hcall] at hsum
  linarith

include hW in
/-- **The default probability of Merton's firm** under the Girsanov measure `Q` of the constant
market price of risk at the horizon `H ≥ T` is `kmvPD`, the Merton–KMV default probability
`Φ(−d₂)`: the event `V_T ≤ F` has `Q`-measure `kmvPD V₀ F r σ T`. Default is the event at the
maturity `T`, not a first passage. -/
theorem real_default_constGirsanovMeasure {V₀ F m r σ : ℝ} {T H : ℝ≥0} (hTH : T ≤ H)
    (hV₀ : 0 < V₀) (hF : 0 < F) (hσ : 0 < σ) (hT : 0 < (T : ℝ)) :
    (constGirsanovMeasure hW hWmeas ((m - r) / σ) H).real
        {ω | (market μ hWmeas V₀ m r σ).asset () T ω ≤ F}
      = kmvPD V₀ F r σ T := by
  have hQp := constGirsanovMeasure_isProbabilityMeasure hW hWmeas ((m - r) / σ) H
  have hB := isPreBrownianReal_constBtheta hW hWmeas ((m - r) / σ) H
  have hkmv := kmvPD_eq_one_sub_survival_probability_via_brownian
    (constGirsanovMeasure hW hWmeas ((m - r) / σ) H)
    (constBtheta (μ := μ) hWmeas ((m - r) / σ) H) hB hV₀ hF hσ hT (r := r)
  simp only [Real.toNNReal_coe] at hkmv
  have hae : ∀ᵐ ω ∂(constGirsanovMeasure hW hWmeas ((m - r) / σ) H),
      (market μ hWmeas V₀ m r σ).asset () T ω
        = bsTerminal V₀ r σ T (constBtheta (μ := μ) hWmeas ((m - r) / σ) H T ω / Real.sqrt T) := by
    filter_upwards [pathAssets_physical_ae_eq hW hWmeas (S_0 := V₀) (m := m) (r := r) hσ.ne' H
      hTH] with ω hω
    exact hω.trans (pathAssets_eq_bsTerminal _ hT V₀ r σ ω)
  have hA : MeasurableSet {ω | (market μ hWmeas V₀ m r σ).asset () T ω ≤ F} :=
    measurableSet_le ((market μ hWmeas V₀ m r σ).measurable_asset () T) measurable_const
  have hcompl : {ω | (market μ hWmeas V₀ m r σ).asset () T ω ≤ F}ᶜ
      =ᵐ[constGirsanovMeasure hW hWmeas ((m - r) / σ) H]
      {ω | bsTerminal V₀ r σ T
        (constBtheta (μ := μ) hWmeas ((m - r) / σ) H T ω / Real.sqrt T) > F} :=
    Filter.eventuallyEqSet_iff.2 (hae.mono fun ω h ↦ by simp [h])
  have := probReal_compl_eq_one_sub (μ := constGirsanovMeasure hW hWmeas ((m - r) / σ) H) hA
  rw [measureReal_congr hcompl] at this
  simp only [measureReal_def] at this
  rw [hkmv, measureReal_def]
  linarith

include hW in
/-- **Merton's structural model is a market with a pricing measure.** Let the firm's assets be
the Black–Scholes market of a pre-Brownian motion `W` (spot `V₀ > 0`, physical drift `m`, rate
`r`, volatility `σ > 0`), with debt of face `F > 0` due at `T ≤ H`. The Girsanov measure `Q` of the
constant market price of risk `(m − r)/σ` at the horizon `H` is a pricing measure of the market,
and under it

* the equity, the European call on the assets, is worth the Black–Scholes price
  `V₀ Φ(d₁) − F e^{−rT} Φ(d₂)` (for `0 < T`);
* the defaultable zero-coupon bond is worth `V₀` less the equity;
* the probability of default `V_T ≤ F` is the Merton–KMV default probability `kmvPD`.

Default is the event at the maturity `T`, not a first passage. The four conjuncts are
`isPricingMeasure_constGirsanovMeasure`, `price_europeanCall_constGirsanovMeasure`,
`price_defaultableZCB_constGirsanovMeasure` and `real_default_constGirsanovMeasure`. -/
theorem merton_market {V₀ F m r σ : ℝ} {T H : ℝ≥0} (hTH : T ≤ H) (hV₀ : 0 < V₀) (hF : 0 < F)
    (hσ : 0 < σ) (hT : 0 < (T : ℝ)) :
    (market μ hWmeas V₀ m r σ).IsPricingMeasure T
        (constGirsanovMeasure hW hWmeas ((m - r) / σ) H) ∧
      (market μ hWmeas V₀ m r σ).price (constGirsanovMeasure hW hWmeas ((m - r) / σ) H)
          (europeanCall F T)
        = V₀ * Phi (bsd1 V₀ F r σ T) - F * Real.exp (-r * T) * Phi (bsd2 V₀ F r σ T) ∧
      (market μ hWmeas V₀ m r σ).price (constGirsanovMeasure hW hWmeas ((m - r) / σ) H)
          (defaultableZCB F T)
        = V₀ - (V₀ * Phi (bsd1 V₀ F r σ T) - F * Real.exp (-r * T) * Phi (bsd2 V₀ F r σ T)) ∧
      (constGirsanovMeasure hW hWmeas ((m - r) / σ) H).real
          {ω | (market μ hWmeas V₀ m r σ).asset () T ω ≤ F}
        = kmvPD V₀ F r σ T :=
  ⟨isPricingMeasure_constGirsanovMeasure hW hWmeas (S_0 := V₀) (m := m) (r := r) hσ.ne' hTH,
    price_europeanCall_constGirsanovMeasure hW hWmeas (m := m) (r := r) (K := F) hTH hV₀ hF hσ hT,
    price_defaultableZCB_constGirsanovMeasure hW hWmeas hTH hV₀ hF hσ hT,
    real_default_constGirsanovMeasure hW hWmeas hTH hV₀ hF hσ hT⟩

end Merton

end MathFin.Contracts
