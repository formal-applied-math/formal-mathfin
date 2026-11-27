/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.BlackScholes.ImpliedVolatility
public import MathFin.Models.BlackScholes.Market
public import MathFin.Probability.Analysis.BisectionStraddle
public import Mathlib.Topology.Order.LeftRightNhds

/-!
# Implied volatility for every arbitrage-free price

`ImpliedVolatility.lean` proves uniqueness of the implied volatility and
existence above a reference volatility; its missing piece was the
`σ → 0⁺` behaviour. This file completes the picture. As `σ → 0⁺`, both
`d₁ = (log(S/K) + (r + σ²/2)T)/(σ√T)` and `d₂ = d₁ − σ√T` are driven by the
`1/σ` term of the forward offset `log(S/K) + rT`: the price tends to

  `(S − K·e^{−rT})⁺`,

whether the spot is above, at, or below the discounted strike (at equality the
`Φ(d₁)`, `Φ(d₂)` terms both tend to `1/2` and cancel against the vanishing
forward). So a call price `C` strictly inside the no-arbitrage range
`((S − K·e^{−rT})⁺, S)` straddles the price curve between small and large
volatilities, and `exists_impliedVol_gt_of_bsV_lt` applies: every arbitrage-free
price has a unique positive implied volatility (`exists_impliedVol_of_lt`),
packaged as the function `impliedVol` with its defining equation
(`impliedVol_defining_eq`) and its junk disclosure (`impliedVol_eq_zero_iff`).

The threshold bisection of `BisectionStraddle.lean` specializes to the
Black–Scholes price: at a threshold volatility inside the bracket, the
estimates converge to it and it prices the option (`bsV_bisect_threshold_root`).
`BisectionIV.lean`'s `impliedVol_bisection_converges` already converges the
estimates on a straddled bracket with `C < bsV K r σ_hi S T` through strict
monotonicity; the threshold form adds the endpoint case `σ = σ_hi` and the
equation `bsV K r σ S T = C` at the named threshold, which the plain threshold
theorem does not give.

## Main definitions

* `impliedVol`: the implied volatility of a call price; junk value `0` outside
  the no-arbitrage range.

## Main results

* `tendsto_bsV_sigma_zero`: the call price tends to `(S − K·e^{−rT})⁺` as
  `σ → 0⁺`.
* `bsV_lt_S`: the price sits strictly below the spot, for `K, S > 0` and any `σ, r, T`.
* `exists_impliedVol_of_lt`: every price in the no-arbitrage range has a unique
  positive implied volatility.
* `impliedVol_defining_eq`: the defining equation of `impliedVol`.
* `impliedVol_eq_zero_iff`: `impliedVol` vanishes exactly when no positive
  volatility both prices to `C` and is the only one.
* `bsV_bisect_threshold_root`: bisection on the Black–Scholes price converges
  to an interior threshold and the threshold prices the option.
* `tendsto_marketCallPrice_sigma_zero`, `impliedVol_eq_model_vol`,
  `marketCallPrice_bisect_threshold_root`: the same three facts for the price the
  Black–Scholes market's Girsanov measure assigns the call, through
  `price_europeanCall_constGirsanovMeasure`.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 19.10
* [J. Gatheral, *The Volatility Surface: A Practitioner's Guide*][Gatheral2006]
* [R. L. Burden and J. D. Faires, *Numerical Analysis*][BurdenFaires2011], §2.1
* [S. E. Shreve, *Stochastic Calculus for Finance II*][ShreveSCFII], 4.5

## Tags

implied volatility, no-arbitrage price range, volatility limit, bisection method,
root finding, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal Topology

/-! ### The forward offset's sign converts to a spot-versus-forward comparison -/

/-- The spot is above the discounted strike iff the forward offset `log(S/K) + rT` is
positive. -/
theorem lt_forward_iff_offset_pos {S K r T : ℝ} (hK : 0 < K) (hS : 0 < S) :
    K * Real.exp (-(r * T)) < S ↔ 0 < Real.log (S / K) + r * T := by
  have h1 : -(r * T) < Real.log (S / K) ↔ Real.exp (-(r * T)) < S / K :=
    Real.lt_log_iff_exp_lt (div_pos hS hK)
  have h2 : Real.exp (-(r * T)) < S / K ↔ K * Real.exp (-(r * T)) < S :=
    lt_div_iff₀' hK
  rw [show (0 < Real.log (S / K) + r * T ↔ -(r * T) < Real.log (S / K)) from by
      constructor <;> intro h <;> linarith, ← h2, ← h1]

/-- The spot is below the discounted strike iff the forward offset `log(S/K) + rT` is
negative. -/
theorem lt_forward_iff_offset_neg {S K r T : ℝ} (hK : 0 < K) (hS : 0 < S) :
    S < K * Real.exp (-(r * T)) ↔ Real.log (S / K) + r * T < 0 := by
  have h1 : Real.log (S / K) < -(r * T) ↔ S / K < Real.exp (-(r * T)) :=
    Real.log_lt_iff_lt_exp (div_pos hS hK)
  have h2 : S / K < Real.exp (-(r * T)) ↔ S < K * Real.exp (-(r * T)) := by
    rw [div_lt_iff₀ hK, mul_comm]
  rw [show (Real.log (S / K) + r * T < 0 ↔ Real.log (S / K) < -(r * T)) from by
      constructor <;> intro h <;> linarith, ← h2, ← h1]

/-! ### The limits of `d₁` and `d₂` as `σ → 0⁺` -/

/-- `d₁ → +∞` as `σ → 0⁺` when the forward offset is positive. -/
private lemma tendsto_bsd1_atTop_of_forward_pos (S K r : ℝ) {T : ℝ} (hT : 0 < T)
    (h : 0 < Real.log (S / K) + r * T) :
    Tendsto (fun σ ↦ bsd1 S K r σ T) (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun σ : ℝ ↦ (Real.log (S / K) + r * T) / Real.sqrt T * σ⁻¹)
      (𝓝[>] 0) atTop :=
    (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop
      (div_pos h (Real.sqrt_pos.2 hT))
  have h2 : Tendsto (fun σ : ℝ ↦ Real.sqrt T / 2 * σ) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun σ : ℝ ↦ Real.sqrt T / 2 * σ :=
      continuous_const.mul continuous_id
    simpa using hc.tendsto 0 |>.mono_left nhdsWithin_le_nhds
  refine h2.add_atTop h1 |>.congr' ?_
  filter_upwards [(self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)] with σ hσ
  rw [bsd1_eq_inv_add S K r hσ.ne' hT]
  linarith

/-- `d₂ → +∞` as `σ → 0⁺` when the forward offset is positive. -/
private lemma tendsto_bsd2_atTop_of_forward_pos (S K r : ℝ) {T : ℝ} (hT : 0 < T)
    (h : 0 < Real.log (S / K) + r * T) :
    Tendsto (fun σ ↦ bsd2 S K r σ T) (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun σ : ℝ ↦ (Real.log (S / K) + r * T) / Real.sqrt T * σ⁻¹)
      (𝓝[>] 0) atTop :=
    (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop
      (div_pos h (Real.sqrt_pos.2 hT))
  have h2 : Tendsto (fun σ : ℝ ↦ -(Real.sqrt T / 2 * σ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun σ : ℝ ↦ -(Real.sqrt T / 2 * σ) :=
      (continuous_const.mul continuous_id).neg
    simpa using hc.tendsto 0 |>.mono_left nhdsWithin_le_nhds
  refine h2.add_atTop h1 |>.congr' ?_
  filter_upwards [(self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)] with σ hσ
  rw [bsd2, bsd1_eq_inv_add S K r hσ.ne' hT]
  ring

/-- `d₁ → −∞` as `σ → 0⁺` when the forward offset is negative. -/
private lemma tendsto_bsd1_atBot_of_forward_neg (S K r : ℝ) {T : ℝ} (hT : 0 < T)
    (h : Real.log (S / K) + r * T < 0) :
    Tendsto (fun σ ↦ bsd1 S K r σ T) (𝓝[>] 0) atBot := by
  have h1 : Tendsto (fun σ : ℝ ↦ (Real.log (S / K) + r * T) / Real.sqrt T * σ⁻¹)
      (𝓝[>] 0) atBot :=
    (tendsto_const_mul_atBot_of_neg
      (div_neg_of_neg_of_pos h (Real.sqrt_pos.2 hT))).2 (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))
  have h2 : Tendsto (fun σ : ℝ ↦ Real.sqrt T / 2 * σ) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun σ : ℝ ↦ Real.sqrt T / 2 * σ :=
      continuous_const.mul continuous_id
    simpa using hc.tendsto 0 |>.mono_left nhdsWithin_le_nhds
  refine h2.add_atBot h1 |>.congr' ?_
  filter_upwards [(self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)] with σ hσ
  rw [bsd1_eq_inv_add S K r hσ.ne' hT]
  linarith

/-- `d₂ → −∞` as `σ → 0⁺` when the forward offset is negative. -/
private lemma tendsto_bsd2_atBot_of_forward_neg (S K r : ℝ) {T : ℝ} (hT : 0 < T)
    (h : Real.log (S / K) + r * T < 0) :
    Tendsto (fun σ ↦ bsd2 S K r σ T) (𝓝[>] 0) atBot := by
  have h1 : Tendsto (fun σ : ℝ ↦ (Real.log (S / K) + r * T) / Real.sqrt T * σ⁻¹)
      (𝓝[>] 0) atBot :=
    (tendsto_const_mul_atBot_of_neg
      (div_neg_of_neg_of_pos h (Real.sqrt_pos.2 hT))).2 (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))
  have h2 : Tendsto (fun σ : ℝ ↦ -(Real.sqrt T / 2 * σ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun σ : ℝ ↦ -(Real.sqrt T / 2 * σ) :=
      (continuous_const.mul continuous_id).neg
    simpa using hc.tendsto 0 |>.mono_left nhdsWithin_le_nhds
  refine h2.add_atBot h1 |>.congr' ?_
  filter_upwards [(self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)] with σ hσ
  rw [bsd2, bsd1_eq_inv_add S K r hσ.ne' hT]
  ring

/-- At a vanishing forward offset both `d₁` and `d₂` tend to `0` as `σ → 0⁺`. -/
private lemma tendsto_bsd1_bsd2_nhds_zero_of_forward_eq (S K r : ℝ) {T : ℝ} (hT : 0 < T)
    (h : Real.log (S / K) + r * T = 0) :
    Tendsto (fun σ ↦ bsd1 S K r σ T) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun σ ↦ bsd2 S K r σ T) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun σ : ℝ ↦ Real.sqrt T / 2 * σ) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun σ : ℝ ↦ Real.sqrt T / 2 * σ :=
      continuous_const.mul continuous_id
    simpa using hc.tendsto 0 |>.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun σ : ℝ ↦ -(Real.sqrt T / 2 * σ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun σ : ℝ ↦ -(Real.sqrt T / 2 * σ) :=
      (continuous_const.mul continuous_id).neg
    simpa using hc.tendsto 0 |>.mono_left nhdsWithin_le_nhds
  refine ⟨h1.congr' ?_, h2.congr' ?_⟩
  · filter_upwards [(self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)] with σ hσ
    rw [bsd1_eq_inv_add S K r hσ.ne' hT, h]
    ring
  · filter_upwards [(self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)] with σ hσ
    rw [bsd2, bsd1_eq_inv_add S K r hσ.ne' hT, h]
    ring

/-! ### The price at vanishing volatility -/

/-- **The Black–Scholes call price at vanishing volatility**: with `S, K > 0` and `T > 0`,
the price tends to the positive part `(S − K·e^{−rT})⁺` of the discounted intrinsic value
as `σ → 0⁺`. Above the forward the `Φ` terms tend to `1`; below it they tend to `0`; at
the forward both tend to `1/2` and the price vanishes together with the forward. -/
theorem tendsto_bsV_sigma_zero {S K r : ℝ} (hS : 0 < S) (hK : 0 < K) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun σ ↦ bsV K r σ S T) (𝓝[>] 0)
      (𝓝 (max (S - K * Real.exp (-(r * T))) 0)) := by
  rcases lt_trichotomy (K * Real.exp (-(r * T))) S with hF | heq | hF'
  · have hlog := (lt_forward_iff_offset_pos hK hS).mp hF
    have hp := ((tendsto_Phi_atTop.comp
        (tendsto_bsd1_atTop_of_forward_pos S K r hT hlog)).const_mul S).sub
      ((tendsto_Phi_atTop.comp
        (tendsto_bsd2_atTop_of_forward_pos S K r hT hlog)).const_mul
          (K * Real.exp (-(r * T))))
    have hL : S * 1 - K * Real.exp (-(r * T)) * 1 = S - K * Real.exp (-(r * T)) := by ring
    rw [hL] at hp
    rw [max_eq_left (by linarith : (0:ℝ) ≤ S - K * Real.exp (-(r * T)))]
    exact hp
  · have hSK : S / K = Real.exp (-(r * T)) := by rw [← heq]; field_simp
    have hlog : Real.log (S / K) + r * T = 0 := by rw [hSK, Real.log_exp]; ring
    obtain ⟨h1, h2⟩ := tendsto_bsd1_bsd2_nhds_zero_of_forward_eq S K r hT hlog
    have hp := ((Filter.Tendsto.comp (continuous_Phi.tendsto 0) h1).const_mul S).sub
      ((Filter.Tendsto.comp (continuous_Phi.tendsto 0) h2).const_mul
        (K * Real.exp (-(r * T))))
    rw [Phi_zero] at hp
    have hL : S * (1 / 2) - K * Real.exp (-(r * T)) * (1 / 2) = 0 := by
      rw [heq]
      ring
    rw [hL] at hp
    rw [max_eq_right (by rw [heq]; linarith : S - K * Real.exp (-(r * T)) ≤ 0)]
    exact hp
  · have hlog := (lt_forward_iff_offset_neg hK hS).mp hF'
    have hp := ((tendsto_Phi_atBot.comp
        (tendsto_bsd1_atBot_of_forward_neg S K r hT hlog)).const_mul S).sub
      ((tendsto_Phi_atBot.comp
        (tendsto_bsd2_atBot_of_forward_neg S K r hT hlog)).const_mul
          (K * Real.exp (-(r * T))))
    have hL : S * 0 - K * Real.exp (-(r * T)) * 0 = 0 := by ring
    rw [hL] at hp
    rw [max_eq_right (by linarith : S - K * Real.exp (-(r * T)) ≤ 0)]
    exact hp

/-- **The call price sits strictly below the spot**: the strict form of `bsV_le_S`,
through `Φ(d₂) > 0` and `Φ(d₁) < 1`. -/
theorem bsV_lt_S (K r σ S T : ℝ) (hK : 0 < K) (hS : 0 < S) :
    bsV K r σ S T < S := by
  have h1 : 0 < K * Real.exp (-(r * T)) * Phi (bsd2 S K r σ T) :=
    mul_pos (mul_pos hK (Real.exp_pos _)) (Phi_pos _)
  have h2 : Phi (bsd1 S K r σ T) < 1 := (Phi_mem_Ioo _).2
  have key : S * Phi (bsd1 S K r σ T) < S := by
    have := mul_lt_mul_of_pos_left h2 hS
    linarith
  unfold bsV
  linarith

/-! ### Existence on the whole no-arbitrage range -/

/-- **Implied volatility for every arbitrage-free price**: for `S, K, T > 0`, a call price
`C` in the no-arbitrage range `C ∈ ((S − K·e^{−rT})⁺, S)` has an implied volatility
`σ > 0` with `bsV K r σ S T = C`, and no other positive volatility prices to `C`. The
`σ → 0⁺` limit (`tendsto_bsV_sigma_zero`) supplies a volatility below which the price
sits under `C`; existence above it is `exists_impliedVol_gt_of_bsV_lt`. -/
theorem exists_impliedVol_of_lt {K r T S C : ℝ} (hK : 0 < K) (hT : 0 < T) (hS : 0 < S)
    (hC : C ∈ Ioo (max (S - K * Real.exp (-(r * T))) 0) S) :
    ∃ σ, 0 < σ ∧ bsV K r σ S T = C ∧ ∀ σ' > 0, bsV K r σ' S T = C → σ' = σ := by
  obtain ⟨hlo, hhi⟩ := hC
  have hlt : max (S - K * Real.exp (-(r * T))) 0 < C := hlo
  have hev : ∀ᶠ σ in 𝓝[>] 0, bsV K r σ S T ∈ Iio C :=
    (tendsto_bsV_sigma_zero hS hK hT).eventually (Iio_mem_nhds hlt)
  obtain ⟨δ, hδ, hball⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1 hev
  obtain ⟨σ₀, hσ₀big, hσ₀C, huniq⟩ :=
    exists_impliedVol_gt_of_bsV_lt hK hT hS (by linarith : 0 < δ / 2)
      (hball (show δ / 2 ∈ Ioo (0 : ℝ) δ by constructor <;> linarith)) hhi
  exact ⟨σ₀, lt_of_lt_of_le (by linarith : (0 : ℝ) < δ / 2) (le_of_lt hσ₀big), hσ₀C, huniq⟩

/-! ### The implied volatility function -/

open scoped Classical in
/-- The **implied volatility** of a call price `C` at spot `S`, strike `K`, rate `r` and
maturity `T`: a positive volatility whose Black–Scholes price is `C`, chosen when one
exists. On the no-arbitrage range `C ∈ ((S − K·e^{−rT})⁺, S)` it exists and is unique
(`impliedVol_defining_eq`); where no positive volatility prices to `C` the value is the
junk `0` (`impliedVol_eq_zero_iff`). -/
noncomputable def impliedVol (K r : ℝ) (S T C : ℝ) : ℝ :=
  if h : ∃ σ, 0 < σ ∧ bsV K r σ S T = C ∧ ∀ σ' > 0, bsV K r σ' S T = C → σ' = σ then
    h.choose
  else 0

/-- `impliedVol` is the junk `0` exactly where no positive volatility both prices to `C` and
is the only one: the iff quantifies over the function's whole domain, including degenerate
inputs (with a strike of `0` and a positive rate the price is non-injective in `σ`), so the
uniqueness clause is part of what is characterized. -/
lemma impliedVol_eq_zero_iff (K r : ℝ) (S T C : ℝ) :
    impliedVol K r S T C = 0 ↔
      ¬∃ σ, 0 < σ ∧ bsV K r σ S T = C ∧ ∀ σ' > 0, bsV K r σ' S T = C → σ' = σ := by
  by_cases h : ∃ σ, 0 < σ ∧ bsV K r σ S T = C ∧ ∀ σ' > 0, bsV K r σ' S T = C → σ' = σ
  · rw [impliedVol, dite_eq_left h]
    have h1 : 0 < h.choose := h.choose_spec.1
    exact ⟨fun hz ↦ absurd hz (ne_of_gt h1), fun hz ↦ absurd h hz⟩
  · rw [impliedVol, dite_eq_right h]
    exact ⟨fun _ ↦ h, fun _ ↦ rfl⟩

/-- **The defining equation of the implied volatility.** For `S, K, T > 0` and a price
`C` in the no-arbitrage range, `impliedVol K r S T C` is positive, prices the call, and
is the only positive volatility that does. -/
theorem impliedVol_defining_eq {K r T S C : ℝ} (hK : 0 < K) (hT : 0 < T) (hS : 0 < S)
    (hC : C ∈ Ioo (max (S - K * Real.exp (-(r * T))) 0) S) :
    0 < impliedVol K r S T C ∧ bsV K r (impliedVol K r S T C) S T = C ∧
      ∀ σ' > 0, bsV K r σ' S T = C → σ' = impliedVol K r S T C := by
  have hex := exists_impliedVol_of_lt hK hT hS hC
  rw [impliedVol, dite_eq_left hex]
  exact hex.choose_spec

/-! ### Bisection at a Black–Scholes threshold -/

/-- **Bisection on the Black–Scholes price at a threshold**: for `S, K, T > 0`, if some
`σ` with `σ_lo < σ ≤ σ_hi` is the threshold of the price against `C` on the bracket
(`bsV K r x S T < C ↔ x < σ` on `[σ_lo, σ_hi]` — via
`bsV_strictMonoOn_sigma`, in particular when the prices at the bracket ends
straddle `C`), then the bisection estimates converge to `σ` and `σ` prices
the option: `bsV K r σ S T = C`. Specializes `bisect_threshold_root` to
`bsV_continuousOn_sigma`. -/
theorem bsV_bisect_threshold_root {K r T S σ_lo σ_hi σ C : ℝ} (hK : 0 < K) (hT : 0 < T)
    (hS : 0 < S) (hσlo : 0 < σ_lo) (hloσ : σ_lo < σ) (hσhi : σ ≤ σ_hi)
    (hC : ∀ x ∈ Icc σ_lo σ_hi, bsV K r x S T < C ↔ x < σ) :
    bsV K r σ S T = C ∧ Tendsto (bisectMid (fun v ↦ bsV K r v S T) C σ_lo σ_hi) atTop (𝓝 σ) :=
  bisect_threshold_root hloσ hσhi hC
    ((bsV_continuousOn_sigma hK hT hS).mono fun _ hv ↦ hσlo.trans_le hv.1)

/-! ### The market's call price

Through `price_europeanCall_constGirsanovMeasure` the Girsanov pricing measure of the
Black–Scholes market prices the call at the formula value, so the three volatility facts
above price the market's own call. -/

/-- **The market's call price at vanishing model volatility**: as the Black–Scholes market's
volatility `σ → 0⁺`, the Girsanov price of the European call tends to the positive part of
the discounted intrinsic value, through `price_europeanCall_constGirsanovMeasure`. -/
theorem tendsto_marketCallPrice_sigma_zero {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {W : ℝ≥0 → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hW : IsPreBrownianReal W μ) (hWmeas : ∀ t, Measurable (W t)) (S_0 m r K : ℝ)
    {T H : ℝ≥0} (hTH : T ≤ H) (hS₀ : 0 < S_0) (hK : 0 < K) (hT : 0 < (T : ℝ)) :
    Tendsto (fun σ : ℝ ↦ (Contracts.BlackScholes.market μ hWmeas S_0 m r σ).price
        (Contracts.BlackScholes.constGirsanovMeasure hW hWmeas ((m - r) / σ) H)
        (Contracts.europeanCall K T))
      (𝓝[>] 0) (𝓝 (max (S_0 - K * Real.exp (-(r * (T : ℝ)))) 0)) := by
  refine (tendsto_bsV_sigma_zero hS₀ hK hT).congr' ?_
  filter_upwards [(self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)] with σ hσ
  have key := Contracts.BlackScholes.price_europeanCall_constGirsanovMeasure
    (S_0 := S_0) (m := m) (r := r) (σ := σ) (K := K) (T := T) (H := H)
    hW hWmeas hTH hS₀ hK hσ hT
  rw [← key.symm]
  unfold bsV
  simp only [neg_mul]

/-- **The implied volatility of the market's call price is the model's volatility.** The
Girsanov pricing measure prices the European call at the formula value
(`price_europeanCall_constGirsanovMeasure`), so if that price lies in the formula's
no-arbitrage range, the price's implied volatility is the model's own `σ`. -/
theorem impliedVol_eq_model_vol {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {W : ℝ≥0 → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hW : IsPreBrownianReal W μ) (hWmeas : ∀ t, Measurable (W t)) (S_0 m r σ K : ℝ)
    {T H : ℝ≥0} (hTH : T ≤ H) (hS₀ : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < (T : ℝ))
    {C : ℝ}
    (hCprice : (Contracts.BlackScholes.market μ hWmeas S_0 m r σ).price
        (Contracts.BlackScholes.constGirsanovMeasure hW hWmeas ((m - r) / σ) H)
        (Contracts.europeanCall K T) = C)
    (hC : C ∈ Ioo (max (S_0 - K * Real.exp (-(r * (T : ℝ)))) 0) S_0) :
    impliedVol K r S_0 (T : ℝ) C = σ := by
  have key := Contracts.BlackScholes.price_europeanCall_constGirsanovMeasure
    (S_0 := S_0) (m := m) (r := r) (σ := σ) (K := K) (T := T) (H := H)
    hW hWmeas hTH hS₀ hK hσ hT
  have hσC : bsV K r σ S_0 (T : ℝ) = C := by
    rw [← key.symm] at hCprice
    unfold bsV
    rw [← hCprice]
    simp only [neg_mul]
  exact ((impliedVol_defining_eq hK hT hS₀ hC).2.2 σ hσ hσC).symm

/-- **Bisection on the market's call price at a threshold**: at an interior threshold
volatility the estimates of the Girsanov price converge to it, and it prices the option.
The Girsanov price agrees with the formula on the bracket
(`price_europeanCall_constGirsanovMeasure`), so the threshold theorem transfers. -/
theorem marketCallPrice_bisect_threshold_root {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {W : ℝ≥0 → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hW : IsPreBrownianReal W μ) (hWmeas : ∀ t, Measurable (W t)) (S_0 m r K : ℝ)
    {T H : ℝ≥0} (hTH : T ≤ H) (hS₀ : 0 < S_0) (hK : 0 < K) (hT : 0 < (T : ℝ))
    {σ_lo σ_hi σ C : ℝ} (hσlo : 0 < σ_lo) (hloσ : σ_lo < σ) (hσhi : σ ≤ σ_hi)
    (hC : ∀ x ∈ Icc σ_lo σ_hi, (Contracts.BlackScholes.market μ hWmeas S_0 m r x).price
        (Contracts.BlackScholes.constGirsanovMeasure hW hWmeas ((m - r) / x) H)
        (Contracts.europeanCall K T) < C ↔ x < σ) :
    (Contracts.BlackScholes.market μ hWmeas S_0 m r σ).price
        (Contracts.BlackScholes.constGirsanovMeasure hW hWmeas ((m - r) / σ) H)
        (Contracts.europeanCall K T) = C ∧
      Tendsto (bisectMid (fun v : ℝ ↦ (Contracts.BlackScholes.market μ hWmeas S_0 m r v).price
          (Contracts.BlackScholes.constGirsanovMeasure hW hWmeas ((m - r) / v) H)
          (Contracts.europeanCall K T)) C σ_lo σ_hi) atTop (𝓝 σ) := by
  set mp : ℝ → ℝ := fun v : ℝ ↦ (Contracts.BlackScholes.market μ hWmeas S_0 m r v).price
      (Contracts.BlackScholes.constGirsanovMeasure hW hWmeas ((m - r) / v) H)
      (Contracts.europeanCall K T) with hmp
  have hkey : ∀ v ∈ Icc σ_lo σ_hi, mp v = bsV K r v S_0 (T : ℝ) := fun v hv ↦ by
    have hp := Contracts.BlackScholes.price_europeanCall_constGirsanovMeasure
      (S_0 := S_0) (m := m) (r := r) (σ := v) (K := K) (T := T) (H := H)
      hW hWmeas hTH hS₀ hK (hσlo.trans_le hv.1) hT
    simp only [neg_mul] at hp
    unfold bsV
    rw [← hp]
  have hmemσ : σ ∈ Icc σ_lo σ_hi := ⟨le_of_lt hloσ, hσhi⟩
  have hC' : ∀ x ∈ Icc σ_lo σ_hi, bsV K r x S_0 (T : ℝ) < C ↔ x < σ := fun x hx ↦ by
    rw [← hkey x hx]; exact hC x hx
  obtain ⟨heq, hconv⟩ := bsV_bisect_threshold_root hK hT hS₀ hσlo hloσ hσhi hC'
  refine ⟨(hkey σ hmemσ).trans heq, hconv.congr' ?_⟩
  have hstep : ∀ I : ℝ × ℝ, σ_lo ≤ I.1 → I.1 ≤ σ_hi → σ_lo ≤ I.2 → I.2 ≤ σ_hi → I.1 ≤ I.2 →
      bisectStep mp C I = bisectStep (fun v ↦ bsV K r v S_0 (T : ℝ)) C I := by
    intro I h1lo h1hi h2lo h2hi hle
    simp only [bisectStep]
    rw [hkey _ ⟨by linarith, by linarith⟩]
  have hag : ∀ n, bisect mp C σ_lo σ_hi n =
      bisect (fun v ↦ bsV K r v S_0 (T : ℝ)) C σ_lo σ_hi n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      obtain ⟨⟨h1lo, h1σ⟩, h2σ, h2hi⟩ := bisect_mem hC' hmemσ n
      rw [bisect_succ, bisect_succ, ih]
      exact hstep _ h1lo (le_trans (le_trans h1σ h2σ) h2hi)
        (le_trans h1lo (le_trans h1σ h2σ)) h2hi (le_trans h1σ h2σ)
  filter_upwards with n
  rw [bisectMid, bisectMid, hag n]

end MathFin
