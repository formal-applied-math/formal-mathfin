/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.BlackScholes.StrikeGreeks
public import MathFin.BlackScholes.StrikeConvexity
public import MathFin.BlackScholes.Call

/-!
# Breeden-Litzenberger: implied risk-neutral PDF from option prices

The Breeden-Litzenberger identity says the risk-neutral PDF of the terminal
asset price `S_T`, evaluated at strike `K`, equals `e^{rT}` times the second
strike-derivative of the European call price:

  `f_{S_T}(K) = e^{rT} · ∂²_K C(K)`.

Specialising to the BS model: `∂²_K bsV = e^{-rT} · ϕ(d_2)/(K σ √T)`
(`hasDerivAt_deriv_bsV_K` in `StrikeGreeks.lean`), so

  `f_{S_T}(K) = ϕ(d_2(K)) / (K σ √T)`,

which is the lognormal density at `K` (parameters
`log S_0 + (r − σ²/2)T, σ² T`). This file defines `lognormalTerminalPDF` as that
formula. It proves neither that `S_T` has it as its density nor, beyond the
differential identity at the end, that it integrates to 1.

## Structural connection: PDF positivity = strike-convexity of the price

The non-negativity `0 ≤ f_{S_T}(K)` is *not* an independent fact. It is the
infinitesimal manifestation of a convexity chain:

1. The call **payoff** is convex in `K` (`convexOn_call_payoff` in
   `StrikeConvexity.lean`).
2. Risk-neutral expectation preserves convexity: integration against a positive
   measure does (the finite-state form is `callPrice_finiteState_convexOn_K`).
3. So the call **price** `K ↦ bsV K r σ S T` is convex in `K`.
4. So `∂²_K bsV ≥ 0`.
5. By Breeden-Litzenberger, `∂²_K bsV = e^{-rT} · f_{S_T}(K)`, so
   `f_{S_T}(K) ≥ 0`.

Step 1 is formal. Step 2 is not formalized for the lognormal law, so step 3 is
proved instead by the second-derivative test (`bsV_strike_convexOn`), whose
input is the sign of the closed form in step 4. In this library the chain is
therefore a consistency loop, not an independent source of the sign. Steps
3 → 4 → 5 are formal: `lognormalTerminalPDF_nonneg_via_strike_convexity`
derives step 5 from step 3, and `lognormalTerminalPDF_nonneg` proves it
directly.

Results:

* `lognormalTerminalPDF`: definition.
* `breedenLitzenberger`: `∂²_K bsV(K) = e^{-rT} · lognormalTerminalPDF(K)`.
* `lognormalTerminalPDF_nonneg`: `0 ≤ lognormalTerminalPDF`, directly.
* `lognormalTerminalPDF_nonneg_via_strike_convexity`: the same, from the strike
  convexity of the price.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

/-- **Lognormal PDF of `S_T`** at strike `K`, expressed via the BS `d_2`
parameter: `f(K) = ϕ(d_2(K)) / (K · σ · √T)`. -/
noncomputable def lognormalTerminalPDF (S_0 r σ T K : ℝ) : ℝ :=
  gaussianPDFReal 0 1 (bsd2 S_0 K r σ T) / (K * σ * Real.sqrt T)

/-- **Breeden-Litzenberger formula** under the Black-Scholes model: the second
strike-derivative of the call price is the discounted lognormal density,
`∂²C/∂K² = e^{-rT} · lognormalTerminalPDF(K)`. This is `hasDerivAt_deriv_bsV_K` with the value
read as a density, since `lognormalTerminalPDF` unfolds to `ϕ(d₂) / (K σ √T)`. -/
theorem breedenLitzenberger {S_0 r σ : ℝ} (hS : 0 < S_0) (hσ : 0 < σ)
    {K T : ℝ} (hK : 0 < K) (hT : 0 < T) :
    HasDerivAt (deriv fun k ↦ bsV k r σ S_0 T)
      (Real.exp (-(r * T)) * lognormalTerminalPDF S_0 r σ T K) K :=
  (hasDerivAt_deriv_bsV_K hS hσ hK hT).congr_deriv (mul_div_assoc _ _ _)

/-- **Implied PDF non-negativity**, directly: `ϕ ≥ 0` and `K σ √T > 0`. The route through the
strike convexity of the price is `lognormalTerminalPDF_nonneg_via_strike_convexity`. That
`lognormalTerminalPDF` is a probability density is not proved here. -/
theorem lognormalTerminalPDF_nonneg
    {S_0 r σ T K : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    0 ≤ lognormalTerminalPDF S_0 r σ T K := by
  unfold lognormalTerminalPDF
  have h_pdf_nn : 0 ≤ gaussianPDFReal 0 1 (bsd2 S_0 K r σ T) :=
    gaussianPDFReal_nonneg _ _ _
  have h_den_pos : 0 < K * σ * Real.sqrt T :=
    mul_pos (mul_pos hK hσ) (Real.sqrt_pos.mpr hT)
  exact div_nonneg h_pdf_nn h_den_pos.le

/-! ## Three-scale loop closure: PDF non-negativity ⟸ strike convexity

The proof of `lognormalTerminalPDF_nonneg` above uses direct positivity of the
gaussian PDF (one-line). This section records the **structural derivation**
through `bsV_strike_convexOn`, exhibiting PDF non-negativity as the
infinitesimal face of the K-convexity principle: convexity makes
`0 ≤ ∂²_K bsV` (`deriv_deriv_nonneg_of_convexOn`), and Breeden-Litzenberger
identifies `∂²_K bsV` with `e^{-rT} · PDF(K)`. -/

/-- **PDF non-negativity as a corollary of strike convexity** (structural
derivation closing the three-scale loop).

The derivation chain made explicit:

1. `bsV_strike_convexOn`: the BS call *price* is convex in K on `(0, ∞)`.
2. `deriv_deriv_nonneg_of_convexOn`: so `0 ≤ ∂²_K bsV` there, since its strike
   derivative is monotone (`ConvexOn.monotoneOn_deriv`).
3. `breedenLitzenberger`: `∂²_K bsV = e^{-rT} · PDF`.
4. So `0 ≤ e^{-rT} · PDF`. Dividing by positive `e^{-rT}` gives the result.

The complementary `lognormalTerminalPDF_nonneg` proof above is shorter
(direct gaussian-PDF positivity); this proof takes the sign from
`bsV`-convexity alone. Since `bsV_strike_convexOn` is itself proved by the
second-derivative test, the two routes close a loop rather than giving
independent sources for the sign. -/
theorem lognormalTerminalPDF_nonneg_via_strike_convexity
    {S_0 r σ T K : ℝ} (hS₀ : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    0 ≤ lognormalTerminalPDF S_0 r σ T K := by
  have h := deriv_deriv_nonneg_of_convexOn (bsV_strike_convexOn (r := r) hS₀ hσ hT) isOpen_Ioi
    (fun _ hk ↦ (hasDerivAt_bsV_K hS₀ hσ hk hT).differentiableAt) (Set.mem_Ioi.mpr hK)
  rw [(breedenLitzenberger hS₀ hσ hK hT).deriv] at h
  exact (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp h

/-! ## Change of variables to standard normal (folded from `LognormalCOV.lean`)

The implied PDF and the standard-normal PDF are related by the substitution
`K ↦ z = −bsd2(K)`, whose Jacobian is `dz/dK = −1/(K σ √T)`. The
differential identity below packages this.

The integration-to-1 claim
`∫_0^∞ lognormalTerminalPDF dK = 1` follows from the gaussian PDF
integrating to 1 over `ℝ` plus Mathlib's change-of-variables formula; we
state only the differential. -/

/-- **Differential change-of-variables identity** between the lognormal PDF
of `S_T` and the standard-normal PDF:
`f(K) · K · σ · √T = ϕ(bsd2(K))`. -/
theorem lognormalTerminalPDF_change_of_variables
    {S_0 r σ T K : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    lognormalTerminalPDF S_0 r σ T K * (K * σ * Real.sqrt T) =
      gaussianPDFReal 0 1 (bsd2 S_0 K r σ T) := by
  unfold lognormalTerminalPDF
  have hsqrtT_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have h_den_ne : K * σ * Real.sqrt T ≠ 0 :=
    (mul_pos (mul_pos hK hσ) hsqrtT_pos).ne'
  field_simp

end MathFin
