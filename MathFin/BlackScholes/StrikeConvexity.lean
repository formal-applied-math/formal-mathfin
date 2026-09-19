/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.BlackScholes.StrikeGreeks
public import MathFin.BlackScholes.GreekSigns

/-!
# Strike-direction convexity at every scale

The European call satisfies *the same* convexity-in-`K` fact at three
different scales of resolution:

1. **Payoff level**, `K ↦ max(S − K, 0)`. Convex because the positive
   part of an affine function is convex (`ConvexOn.sup` on `(S − ·)` and
   `0`).
2. **Finite-state price level**, `K ↦ Σ q_i · max(S_i − K, 0)`. Convex
   because non-negative linear combinations of convex functions are convex
   (`ConvexPricingFunctional.callPrice_finiteState_convexOn_K`).
3. **Continuous BS price level**, `K ↦ bsV K r σ S τ`. Convex on `(0, ∞)`
   because its second `K`-derivative is non-negative
   (`hasDerivAt_deriv_bsV_K` + `convexOn_of_deriv2_nonneg'`).

The three scales are not three theorems; they are one principle realised at
three different levels of integration. This file packages all three so the
hierarchy is visible.

## Downstream consequences (one principle, many faces)

* **Bull spread** `V(K₁) ≥ V(K₂)` for `K₁ ≤ K₂` — `Antitone`-payoff after
  pricing-functional preservation of monotonicity.
* **Butterfly non-negativity at payoff** (`butterfly_payoff_nonneg`) —
  convex-payoff second-difference inequality.
* **Butterfly non-negativity at price** (`callPrice_finiteState_butterfly_nonneg`) —
  pricing functional preserves convexity, hence the same second-difference
  is non-negative at the price level.
* **Breeden-Litzenberger PDF positivity**
  (`lognormalTerminalPDF_nonneg_via_strike_convexity`) — the infinitesimal
  manifestation of price-level convexity, from `bsV_strike_convexOn` below via
  `deriv_deriv_nonneg_of_convexOn`. That convexity is itself proved from the sign,
  so this is a loop, not an independent derivation.

## Results

* `convexOn_sub_const_id`: `K ↦ a − K` is convex.
* `convexOn_call_payoff`: `K ↦ max(S − K, 0)` is convex in K (payoff level).
* `antitone_call_payoff`: `K ↦ max(S − K, 0)` is antitone in K.
* `bsV_strike_convexOn`: `K ↦ bsV K r σ S τ` is convex on `(0, ∞)`
  (continuous BS price level).
-/

@[expose] public section

namespace MathFin

open Set Real ProbabilityTheory

/-- The affine function `K ↦ a − K` is convex on `Set.univ`. Affine
functions are simultaneously convex and concave; the inequality holds
with equality. -/
lemma convexOn_sub_const_id (a : ℝ) :
    ConvexOn ℝ Set.univ (fun K : ℝ ↦ a - K) := by
  refine ⟨convex_univ, fun K₁ _ K₂ _ s t _ _ hst ↦ ?_⟩
  show a - (s • K₁ + t • K₂) ≤ s • (a - K₁) + t • (a - K₂)
  simp only [smul_eq_mul]
  -- Equality (affine functions are tight): `s·a + t·a = a` via `s + t = 1`.
  have h_sa_ta : s * a + t * a = a := by linear_combination a * hst
  linarith

/-- **Call payoff is convex in the strike**: `K ↦ max(S − K, 0)` is convex.

This is the structural spine of static option-price no-arbitrage relations.
Butterfly non-negativity and Breeden-Litzenberger PDF positivity are
discrete and infinitesimal consequences (respectively) of this single fact,
after passing through risk-neutral expectation. -/
lemma convexOn_call_payoff (S : ℝ) :
    ConvexOn ℝ Set.univ (fun K : ℝ ↦ max (S - K) 0) :=
  (convexOn_sub_const_id S).sup (convexOn_const (0 : ℝ) convex_univ)

/-- **Call payoff is antitone in the strike**: higher strikes pay less.

Equivalent to monotonicity of `max(·, 0)` composed with `K ↦ S − K` (which
is itself antitone). The single-line consequence of monotonicity of `max`. -/
lemma antitone_call_payoff (S : ℝ) :
    Antitone (fun K : ℝ ↦ max (S - K) 0) :=
  fun _ _ h ↦ max_le_max (by linarith) le_rfl

/-! ## The continuous-price face

Beyond the payoff (`convexOn_call_payoff`), the *price itself* is convex
in the strike. The proof is the second-derivative test:

* `hasDerivAt_bsV_K`: `∂_K bsV = −e^{-rτ} · Φ(d_2)` exists at every `K > 0`.
* `hasDerivAt_deriv_bsV_K`: `∂²_K bsV = e^{-rτ} · ϕ(d_2) / (K σ √τ)` exists at
  every `K > 0`, and it is non-negative (`bsV_partial_KK_nonneg`).

We feed these to Mathlib's `convexOn_of_deriv2_nonneg'`. -/

/-- **BS call price is convex in the strike on `(0, ∞)`** — the continuous-
price face of the K-convexity principle.

This is the second-derivative test applied to BS: at every `K > 0`,
`∂²_K bsV = e^{-rτ} · ϕ(d_2)/(K σ √τ) ≥ 0`. -/
theorem bsV_strike_convexOn {S r σ τ : ℝ} (hS : 0 < S) (hσ : 0 < σ) (hτ : 0 < τ) :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun K ↦ bsV K r σ S τ) :=
  convexOn_of_deriv2_nonneg' (convex_Ioi 0)
    (fun _ hK ↦ (hasDerivAt_bsV_K hS hσ hK hτ).differentiableAt.differentiableWithinAt)
    (fun _ hK ↦ (hasDerivAt_deriv_bsV_K hS hσ hK hτ).differentiableAt.differentiableWithinAt)
    -- the sign is the named butterfly / Breeden-Litzenberger fact (`GreekSigns`)
    fun _ hK ↦ (bsV_partial_KK_nonneg hK hσ hτ S r).trans_eq
      (hasDerivAt_deriv_bsV_K hS hσ hK hτ).deriv.symm

/-- **Put price is convex in the strike on `(0, ∞)`** — free from the call's
strike-convexity: `bsP = bsV + (K·e^{-rτ} − S)` differs from `bsV` by an affine
function of `K`, and convexity is preserved by adding an affine function. The
second-derivative apparatus of `PutStrikeConvexity` is not needed. -/
theorem bsP_strike_convexOn {S r σ τ : ℝ} (hS : 0 < S) (hσ : 0 < σ) (hτ : 0 < τ) :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun K ↦ bsP K r σ S τ) := by
  have h_eq : (fun K ↦ bsP K r σ S τ)
      = (fun K ↦ bsV K r σ S τ) + (fun K ↦ K * Real.exp (-(r * τ)) - S) := by
    funext K; simp only [Pi.add_apply]; rw [bsP_eq_bsV K r σ S τ]; ring
  rw [h_eq]
  refine (bsV_strike_convexOn hS hσ hτ).add ⟨convex_Ioi 0, fun K₁ _ K₂ _ s t _ _ hst ↦ ?_⟩
  dsimp only
  simp only [smul_eq_mul]
  nlinarith [show s * S + t * S = S from by linear_combination S * hst]

end MathFin
