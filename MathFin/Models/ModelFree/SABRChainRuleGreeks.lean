/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

public import MathFin.Models.BlackScholes.HigherGreeks
public import MathFin.Models.BlackScholes.Market
public import MathFin.Models.StochVol.SABRImpliedVol

/-!
# SABR chain-rule Greeks (at-the-money)

Hagan, Kumar, Lesniewski & Woodward, "Managing Smile Risk," *Wilmott Magazine*,
September 2002, pp. 84-108, §3.2 ("Managing smile risk"): since the SABR implied vol
`σ_B(K, f)` is itself a function of the forward `f` and of `α`, a European option
`V = BS(f, K, σ_B(K, f), t_ex)` (their eq. 3.5) has genuine price sensitivities that combine
the ordinary Black-Scholes sensitivity with the *vol smile's own movement*, via the chain
rule — their eq. 3.9 (the Δ risk) and eq. 3.6 (the vega risk, in `α`):

`Δ_SABR = Δ_BS + Λ_BS · ∂σ_B/∂f`,   `Λ_SABR^α = Λ_BS · ∂σ_B/∂α`

where `Δ_BS`, `Λ_BS` are the ordinary Black-Scholes delta/vega evaluated at `σ = σ_B(K, f)`.

**What is proved here, and what is not (read this before citing the theorems below).**
Eq. 3.9 needs `∂σ_B(K, f)/∂f` at a FIXED strike `K` as `f` varies — `sabrImpliedVol`'s
general formula (`SABRImpliedVol.lean` eq. 2.17a) differentiated in its *second* argument.
That is not attempted here. At `K = f` the formula's `z / x(z)` factor is `0/0`, which Lean
evaluates to `0`, so the literal `f ↦ sabrImpliedVol K f ⋯` is not even continuous at
`f = K` (`SABRImpliedVol.lean` resolves only the `K → f` *limit* there,
`tendsto_sabrImpliedVol_atm`, from `x'(0) = 1`); a fixed-strike Delta at `K = f` would
first need the ATM value redefined by that limit, and then `x''(0)` (the second
derivative of `sabrX` at `0`, not established in this repository). Away from `K = f`
(where `z ≠ 0`) no singularity arises, but the chain rule
through eq. 2.17a's `(f·K)^((1-β)/2)`, `log(f/K)` and `z / x(z)` factors is left as future
work.

What **is** proved here is the chain rule for the Black call with its strike held FIXED at
`K = f` and the spot `s` moving, priced at the *ATM-vol curve evaluated at the spot*,
`σ_ATM(s) = sabrATMVol s α β ρ ν tex` (eq. 2.18, the paper's own ATM closed form, read as a
function of the forward alone — the "backbone" of `SABRImpliedVol.lean` §"The backbone law",
generalized from its log-log slope to the plain derivative), via a genuine total-derivative
(`HasFDerivAt`-level) argument, not just formula-splicing. This is a well-defined, useful
risk quantity (the Delta under a "vol re-marks along the backbone" convention: the
strike-`K` option is re-marked at the ATM vol of the new forward), but it is **not** eq. 3.9
restricted to `K = f`: eq. 3.9 differentiates the fixed-strike smile `f ↦ σ_B(K, f)`,
whereas the theorem below differentiates the ATM curve `f ↦ σ_B(f, f)`; the two curves agree
at `f = K` but their slopes there differ by the smile's ATM strike-slope. Nor is it eq. 3.10
(the Δ with `σ_ATM` held fixed).

## Main results

* The general chain rules `hasDerivAt_bsV_S_chainRule` and `hasDerivAt_bsV_param_chainRule`
  (vol a function of the spot, resp. of a parameter) are in `BlackScholes/HigherGreeks.lean`;
  this file instantiates them at `sabrATMVol`.
* `hasDerivAt_sabrATMVol_F`, `hasDerivAt_sabrATMVol_alpha` — the real derivatives of the
  closed form `sabrATMVol` (eq. 2.18) in `f` and in `α` respectively.
* `sabrATMVol_bsV_delta_chainRule`, `sabrATMVol_bsV_vega_chainRule` — the two combined,
  with the vol's slope written `deriv`: the derivative at `s = f` of
  `s ↦ bsV f 0 (sabrATMVol s α β ρ ν tex) s tex` (strike fixed at `f`, spot `s` and the vol
  curve's argument moving) and of `a ↦ bsV f 0 (sabrATMVol f a
  β ρ ν tex) f tex` (spot/strike fixed at `f`, only `α` moving).

## References

* [P. S. Hagan, D. Kumar, A. S. Lesniewski and D. E. Woodward,
  *Managing smile risk*][HaganKumarLesniewskiWoodward2002], §3.2, eqs. 3.5, 3.6, 3.9

## Tags

SABR, chain rule, Greeks, delta, vega, at-the-money, Frechet derivative, implied volatility,
MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

/-! ### The ATM-vol curve's own sensitivities -/

/-- **`∂σ_ATM/∂f`**: the real derivative of the closed-form ATM vol `sabrATMVol`
(eq. 2.18) with respect to the forward, for `f > 0`. -/
theorem hasDerivAt_sabrATMVol_F {f α β ρ ν tex : ℝ} (hf : 0 < f) :
    HasDerivAt (fun x ↦ sabrATMVol x α β ρ ν tex)
      ((-(α * ((1 - β) * f ^ (1 - β - 1))) / (f ^ (1 - β)) ^ 2) *
          (1 + ((1 - β) ^ 2 / 24 * (α ^ 2 / f ^ (2 - 2 * β))
              + ρ * β * α * ν / 4 / f ^ (1 - β) + (2 - 3 * ρ ^ 2) / 24 * ν ^ 2) * tex)
        + (α / f ^ (1 - β)) *
          (((1 - β) ^ 2 / 24 * (-(α ^ 2 * ((2 - 2 * β) * f ^ (2 - 2 * β - 1)))
                / (f ^ (2 - 2 * β)) ^ 2)
              + (-(ρ * β * α * ν / 4 * ((1 - β) * f ^ (1 - β - 1))) / (f ^ (1 - β)) ^ 2))
            * tex))
      f := by
  have hpow1 : HasDerivAt (fun x : ℝ ↦ x ^ (1 - β)) ((1 - β) * f ^ (1 - β - 1)) f :=
    hasDerivAt_rpow_const (Or.inl hf.ne')
  have hpow2 : HasDerivAt (fun x : ℝ ↦ x ^ (2 - 2 * β)) ((2 - 2 * β) * f ^ (2 - 2 * β - 1)) f :=
    hasDerivAt_rpow_const (Or.inl hf.ne')
  have hp1ne : f ^ (1 - β) ≠ 0 := (Real.rpow_pos_of_pos hf _).ne'
  have hp2ne : f ^ (2 - 2 * β) ≠ 0 := (Real.rpow_pos_of_pos hf _).ne'
  have hBb := (hasDerivAt_const f α).div hpow1 hp1ne
  have hterm1 := (hasDerivAt_const f (α ^ 2)).div hpow2 hp2ne |>.const_mul ((1 - β) ^ 2 / 24)
  have hterm2 := (hasDerivAt_const f (ρ * β * α * ν / 4)).div hpow1 hp1ne
  have hbracket := (hterm1.add hterm2).add (hasDerivAt_const f ((2 - 3 * ρ ^ 2) / 24 * ν ^ 2))
  have hCf := (hbracket.mul_const tex).const_add (1 : ℝ)
  have hfinal := hBb.mul hCf
  unfold sabrATMVol sabrBackbone
  convert hfinal using 1
  simp only [Pi.div_apply, Pi.add_apply]
  ring

/-- **`∂σ_ATM/∂α`**: the real derivative of the closed-form ATM vol `sabrATMVol`
(eq. 2.18) with respect to `α`. Unlike the `f`-derivative, this holds unconditionally
(`sabrATMVol` is a genuine polynomial in `α`, with no `α`-dependent rpow base). -/
theorem hasDerivAt_sabrATMVol_alpha {f β ρ ν tex : ℝ} (α : ℝ) :
    HasDerivAt (fun a ↦ sabrATMVol f a β ρ ν tex)
      (1 / f ^ (1 - β) *
          (1 + ((1 - β) ^ 2 / 24 * (α ^ 2 / f ^ (2 - 2 * β))
              + ρ * β * α * ν / 4 / f ^ (1 - β) + (2 - 3 * ρ ^ 2) / 24 * ν ^ 2) * tex)
        + α / f ^ (1 - β) *
          (((1 - β) ^ 2 / 24 * (2 * α / f ^ (2 - 2 * β)) + ρ * β * ν / 4 / f ^ (1 - β)) * tex))
      α := by
  unfold sabrATMVol sabrBackbone
  have hBb : HasDerivAt (fun a : ℝ ↦ a / f ^ (1 - β)) (1 / f ^ (1 - β)) α := by
    have h := (hasDerivAt_id' α).div_const (f ^ (1 - β))
    convert h using 1
  have hbr : HasDerivAt (fun a : ℝ ↦ (1 - β) ^ 2 / 24 * (a ^ 2 / f ^ (2 - 2 * β))
      + ρ * β * a * ν / 4 / f ^ (1 - β) + (2 - 3 * ρ ^ 2) / 24 * ν ^ 2)
      ((1 - β) ^ 2 / 24 * (2 * α / f ^ (2 - 2 * β)) + ρ * β * ν / 4 / f ^ (1 - β)) α := by
    have h1 : HasDerivAt (fun a : ℝ ↦ (1 - β) ^ 2 / 24 * (a ^ 2 / f ^ (2 - 2 * β)))
        ((1 - β) ^ 2 / 24 * (2 * α / f ^ (2 - 2 * β))) α := by
      have h := ((hasDerivAt_pow 2 α).div_const (f ^ (2 - 2 * β))).const_mul ((1 - β) ^ 2 / 24)
      convert h using 1
      ring
    have h2 : HasDerivAt (fun a : ℝ ↦ ρ * β * a * ν / 4 / f ^ (1 - β))
        (ρ * β * ν / 4 / f ^ (1 - β)) α := by
      have h :=
        (((hasDerivAt_id' α).const_mul (ρ * β)).mul_const ν).div_const 4 |>.div_const (f ^ (1 - β))
      convert h using 1
      ring
    have h3 : HasDerivAt (fun _ : ℝ ↦ (2 - 3 * ρ ^ 2) / 24 * ν ^ 2) 0 α := hasDerivAt_const α _
    have hsum := (h1.add h2).add h3
    convert hsum using 1
    ring
  have hCf : HasDerivAt (fun a : ℝ ↦ 1 + ((1 - β) ^ 2 / 24 * (a ^ 2 / f ^ (2 - 2 * β))
      + ρ * β * a * ν / 4 / f ^ (1 - β) + (2 - 3 * ρ ^ 2) / 24 * ν ^ 2) * tex)
      ((((1 - β) ^ 2 / 24 * (2 * α / f ^ (2 - 2 * β)) + ρ * β * ν / 4 / f ^ (1 - β))) * tex) α
      := by
    have h := (hbr.mul_const tex).const_add (1 : ℝ)
    convert h using 1
  have hres := hBb.mul hCf
  convert hres using 1

/-! ### The combined chain-rule Greeks -/

/-- **The SABR ATM chain-rule Delta**: the derivative at spot `s = f` of the Black call
with strike held fixed at `K = f`, priced at spot `s` with the ATM vol curve evaluated at
that spot, `σ_ATM(s) = sabrATMVol s α β ρ ν tex` — spot and the vol's own forward-dependence
moving together, strike fixed — equals `Δ_BS + Λ_BS · ∂σ_ATM/∂f`. See the file docstring
for exactly what this is (and is not) relative to Hagan's eq. 3.9. `hσ` (vol positivity) is
a standing domain hypothesis, assumed rather than derived — as `BSCallHyp.σ_pos` is for
`sabrATMVol_black_futures_price` (`SABRImpliedVol.lean`; its `sabrATMVol_bsV_gt_backbone_bsV`
instead *derives* positivity from `0 < α` and a positive correction bracket). -/
theorem sabrATMVol_bsV_delta_chainRule {f α β ρ ν tex : ℝ} (hf : 0 < f)
    (hσ : 0 < sabrATMVol f α β ρ ν tex) (htex : 0 < tex) :
    HasDerivAt (fun s ↦ bsV f 0 (sabrATMVol s α β ρ ν tex) s tex)
      (Phi (bsd1 f f 0 (sabrATMVol f α β ρ ν tex) tex)
        + f * gaussianPDFReal 0 1 (bsd1 f f 0 (sabrATMVol f α β ρ ν tex) tex) * Real.sqrt tex *
          deriv (fun x ↦ sabrATMVol x α β ρ ν tex) f)
      f :=
  hasDerivAt_bsV_S_chainRule hf hf hσ htex
    (hasDerivAt_sabrATMVol_F hf).differentiableAt.hasDerivAt rfl

/-- **The SABR ATM chain-rule Vega**: the derivative, in `α`, of the Black call priced at
the ATM strike `K = f` (spot and strike both fixed at `f`, only `α` moving through the
vol) with vol `σ_ATM = sabrATMVol f α β ρ ν tex`, equals `Λ_BS · ∂σ_ATM/∂α`. This is
Hagan et al.'s eq. 3.6 at `K = f`. -/
theorem sabrATMVol_bsV_vega_chainRule {f α β ρ ν tex : ℝ} (hf : 0 < f)
    (hσ : 0 < sabrATMVol f α β ρ ν tex) (htex : 0 < tex) :
    HasDerivAt (fun a ↦ bsV f 0 (sabrATMVol f a β ρ ν tex) f tex)
      (f * gaussianPDFReal 0 1 (bsd1 f f 0 (sabrATMVol f α β ρ ν tex) tex) * Real.sqrt tex *
        deriv (fun a ↦ sabrATMVol f a β ρ ν tex) α)
      α :=
  hasDerivAt_bsV_param_chainRule hf hf hσ htex
    (hasDerivAt_sabrATMVol_alpha α).differentiableAt.hasDerivAt rfl

/-! ### The same Greeks as derivatives of the market price -/

section MarketPrice

open scoped NNReal
open Contracts Contracts.BlackScholes

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {W : ℝ≥0 → Ω → ℝ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] (hW : IsPreBrownianReal W μ) (hWmeas : ∀ t, Measurable (W t))

/-- The price of the European call in the Black-Scholes market at rate `0`, spot `S`, strike `K`
and volatility `σ`, under the Girsanov pricing measure of `θ = m / σ`, is `bsV K 0 σ S T`. -/
theorem price_europeanCall_eq_bsV {K S m σ : ℝ} {T H : ℝ≥0} (hTH : T ≤ H) (hS : 0 < S)
    (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < (T : ℝ)) :
    (market μ hWmeas S m 0 σ).price (constGirsanovMeasure hW hWmeas ((m - 0) / σ) H)
        (europeanCall K T) = bsV K 0 σ S T := by
  rw [price_europeanCall_constGirsanovMeasure hW hWmeas hTH hS hK hσ hT, bsV_eq_closedForm]
  simp

/-- **The SABR ATM chain-rule Delta is the derivative of the market price.** In the
Black-Scholes market with spot `s`, rate `0` and the SABR ATM vol `σ_ATM(s)` as its volatility,
the price of the European call struck at `f` under the Girsanov pricing measure of the constant
price of risk `m / σ_ATM(s)` (the measure moves with `s`) has, at `s = f`, the derivative
`Δ_BS + Λ_BS · ∂σ_ATM/∂f` of `sabrATMVol_bsV_delta_chainRule`. The price is undiscounted
(`r = 0`) and the horizon `H ≥ T` is the Girsanov horizon. -/
theorem sabrATMVol_marketPrice_delta_chainRule {f α β ρ ν m : ℝ} {T H : ℝ≥0} (hTH : T ≤ H)
    (hf : 0 < f) (hσ : 0 < sabrATMVol f α β ρ ν T) (hT : 0 < (T : ℝ)) :
    HasDerivAt (fun s ↦ (market μ hWmeas s m 0 (sabrATMVol s α β ρ ν T)).price
        (constGirsanovMeasure hW hWmeas ((m - 0) / sabrATMVol s α β ρ ν T) H) (europeanCall f T))
      (Phi (bsd1 f f 0 (sabrATMVol f α β ρ ν T) T)
        + f * gaussianPDFReal 0 1 (bsd1 f f 0 (sabrATMVol f α β ρ ν T) T) * Real.sqrt T *
          deriv (fun x ↦ sabrATMVol x α β ρ ν T) f)
      f := by
  refine (sabrATMVol_bsV_delta_chainRule hf hσ hT).congr_of_eventuallyEq ?_
  have hc : ContinuousAt (fun x ↦ sabrATMVol x α β ρ ν T) f :=
    (hasDerivAt_sabrATMVol_F hf).continuousAt
  filter_upwards [hc.eventually (lt_mem_nhds hσ), lt_mem_nhds hf] with s hs hsf
  exact price_europeanCall_eq_bsV hW hWmeas hTH (by linarith) hf hs hT

/-- **The SABR ATM chain-rule Vega is the derivative of the market price.** In the
Black-Scholes market with spot `f`, rate `0` and volatility `σ_ATM(a) = sabrATMVol f a ⋯`, the
price of the European call struck at `f` under the Girsanov pricing measure of the constant price
of risk `m / σ_ATM(a)` has, at `a = α`, the derivative `Λ_BS · ∂σ_ATM/∂α` of
`sabrATMVol_bsV_vega_chainRule`. The price is undiscounted (`r = 0`). -/
theorem sabrATMVol_marketPrice_vega_chainRule {f α β ρ ν m : ℝ} {T H : ℝ≥0} (hTH : T ≤ H)
    (hf : 0 < f) (hσ : 0 < sabrATMVol f α β ρ ν T) (hT : 0 < (T : ℝ)) :
    HasDerivAt (fun a ↦ (market μ hWmeas f m 0 (sabrATMVol f a β ρ ν T)).price
        (constGirsanovMeasure hW hWmeas ((m - 0) / sabrATMVol f a β ρ ν T) H) (europeanCall f T))
      (f * gaussianPDFReal 0 1 (bsd1 f f 0 (sabrATMVol f α β ρ ν T) T) * Real.sqrt T *
        deriv (fun a ↦ sabrATMVol f a β ρ ν T) α)
      α := by
  refine (sabrATMVol_bsV_vega_chainRule hf hσ hT).congr_of_eventuallyEq ?_
  have hc : ContinuousAt (fun a ↦ sabrATMVol f a β ρ ν T) α :=
    (hasDerivAt_sabrATMVol_alpha α).continuousAt
  filter_upwards [hc.eventually (lt_mem_nhds hσ)] with a ha
  exact price_europeanCall_eq_bsV hW hWmeas hTH hf hf ha hT

end MarketPrice

end MathFin
