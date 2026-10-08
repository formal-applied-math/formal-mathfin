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

The European call satisfies *the same* convexity-in-`K` fact at every scale of
resolution:

1. **Payoff level**, `K ↦ max(S − K, 0)`. Convex because the positive
   part of an affine function is convex (`ConvexOn.sup` on `(S − ·)` and
   `0`).
2. **Price level, under any law**, `K ↦ ∫ (X − K)⁺ dμ`. Convex because
   integration against a positive measure preserves the convexity of the
   payoff (`convexOn_integral_call`). Strictly convex wherever the law
   charges every interval of strikes (`strictConvexOn_integral_call`): a
   butterfly spread pays a positive amount when `X` ends strictly between
   its outer strikes.
3. **Finite-state price level**, `K ↦ Σ q_i · max(S_i − K, 0)`. Convex
   because non-negative linear combinations of convex functions are convex
   (`ConvexPricingFunctional.callPrice_finiteState_convexOn_K`).
4. **Continuous BS price level**, `K ↦ bsV K r σ S τ`. Convex on `(0, ∞)`
   as scale 2 for the standard normal law, the Black–Scholes price being the
   discounted expected payoff (`bs_call_formula`). Strictly convex: the
   jump-diffusion without jumps, `bsV_strike_strictConvexOn` in
   `JumpDiffusionStrikeConvexity.lean`.

The scales are not separate theorems; they are one principle realised at
different levels of integration. This file packages them so the hierarchy is
visible.

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
  `deriv_deriv_nonneg_of_convexOn`. That convexity comes from the payoff through
  integration (`convexOn_integral_call`), not from the sign of the closed form, so
  this derives the sign of the density from the convexity of the payoff.

## Results

* `convexOn_sub_const_id`: `K ↦ a − K` is convex.
* `convexOn_call_payoff`: `K ↦ max(S − K, 0)` is convex in K (payoff level).
* `antitone_call_payoff`: `K ↦ max(S − K, 0)` is antitone in K.
* `convexOn_integral_call`: `K ↦ ∫ (X − K)⁺ dμ` is convex, for any integrable
  `X` under a finite measure.
* `strictConvexOn_integral_call`: it is strictly convex on a convex set of
  strikes `s` when `μ {k₁ < X < k₂} ≠ 0` for all `k₁ < k₂` in `s`.
* `bsV_strike_convexOn`: `K ↦ bsV K r σ S τ` is convex on `(0, ∞)`
  (continuous BS price level).
-/

@[expose] public section

namespace MathFin

open MeasureTheory Set Real ProbabilityTheory

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

/-! ## The price under any law

Integrating the convex payoff against a law keeps it convex, and a law that
charges every interval of strikes makes it strictly convex. Nothing about the
law is assumed beyond a finite mean. -/

/-- **The call price is convex in the strike, under any law.** For an integrable `X` under a finite
measure `μ`, `k ↦ ∫ (X − k)⁺ dμ` is convex: integration against a positive measure preserves the
convexity of the payoff (`convexOn_call_payoff`). -/
theorem convexOn_integral_call {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : Integrable X μ) :
    ConvexOn ℝ univ fun k ↦ ∫ ω, max (X ω - k) 0 ∂μ := by
  have hcall (k : ℝ) : Integrable (fun ω ↦ max (X ω - k) 0) μ :=
    (hX.sub (integrable_const k)).pos_part
  refine ⟨convex_univ, fun k₁ _ k₂ _ a b ha hb hab ↦ ?_⟩
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hcall k₁).const_mul a) ((hcall k₂).const_mul b)]
  exact integral_mono (hcall _) (((hcall k₁).const_mul a).add ((hcall k₂).const_mul b))
    fun ω ↦ by simpa only [smul_eq_mul] using
      (convexOn_call_payoff (X ω)).2 (mem_univ k₁) (mem_univ k₂) ha hb hab

/-- **The call price is strictly convex in the strike wherever the law charges every interval.**
For an integrable `X` under a finite measure `μ` and a convex set `s` of strikes such that
`μ {k₁ < X < k₂} ≠ 0` whenever `k₁ < k₂` lie in `s`, `k ↦ ∫ (X − k)⁺ dμ` is strictly convex on
`s`: every butterfly spread `a C(k₁) + b C(k₂) − C(a k₁ + b k₂)` (`a, b > 0`, `a + b = 1`) with
strikes in `s` has a positive price. Its payoff is nonnegative (`convexOn_call_payoff`), and
positive when `k₁ < X < k₂`, where the call struck at `k₂` pays nothing. -/
theorem strictConvexOn_integral_call {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : Integrable X μ) {s : Set ℝ} (hs : Convex ℝ s)
    (hμ : ∀ k₁ ∈ s, ∀ k₂ ∈ s, k₁ < k₂ → μ {ω | k₁ < X ω ∧ X ω < k₂} ≠ 0) :
    StrictConvexOn ℝ s fun k ↦ ∫ ω, max (X ω - k) 0 ∂μ := by
  have hcall (k : ℝ) : Integrable (fun ω ↦ max (X ω - k) 0) μ :=
    (hX.sub (integrable_const k)).pos_part
  refine LinearOrder.strictConvexOn_of_lt hs fun k₁ hk₁ k₂ hk₂ hk a b ha hb hab ↦ ?_
  obtain rfl : b = 1 - a := by linarith
  simp only [smul_eq_mul]
  have hA : Integrable (fun ω ↦ a * max (X ω - k₁) 0 + (1 - a) * max (X ω - k₂) 0) μ :=
    ((hcall k₁).const_mul a).add ((hcall k₂).const_mul (1 - a))
  have hφ : Integrable (fun ω ↦ a * max (X ω - k₁) 0 + (1 - a) * max (X ω - k₂) 0
      - max (X ω - (a * k₁ + (1 - a) * k₂)) 0) μ := hA.sub (hcall _)
  -- the butterfly payoff is nonnegative, and positive when `k₁ < X < k₂`
  have h0 : 0 < ∫ ω, (a * max (X ω - k₁) 0 + (1 - a) * max (X ω - k₂) 0
      - max (X ω - (a * k₁ + (1 - a) * k₂)) 0) ∂μ := by
    refine (integral_pos_iff_support_of_nonneg (fun ω ↦ ?_) hφ).2
      (pos_iff_ne_zero.2 fun h ↦ hμ k₁ hk₁ k₂ hk₂ hk (measure_mono_null (fun ω hω ↦ ?_) h))
    · exact sub_nonneg.2 (by simpa only [smul_eq_mul] using
        (convexOn_call_payoff (X ω)).2 (mem_univ k₁) (mem_univ k₂) ha.le hb.le hab)
    · obtain ⟨h₁, h₂⟩ := hω
      simp only [Function.mem_support, max_eq_left (sub_pos.2 h₁).le,
        max_eq_right (sub_nonpos.2 h₂.le), mul_zero, add_zero]
      exact (sub_pos.2 (max_lt (by linarith [mul_pos hb (sub_pos.2 h₂)])
        (mul_pos ha (sub_pos.2 h₁)))).ne'
  rw [integral_sub hA (hcall _), integral_add ((hcall k₁).const_mul a)
    ((hcall k₂).const_mul (1 - a)), integral_const_mul, integral_const_mul] at h0
  linarith

/-! ## The continuous-price face

The Black–Scholes price is the discounted call payoff integrated against the
standard normal law (`bs_call_formula`), so it inherits the convexity of the
payoff through `convexOn_integral_call`. The second strike derivative
`e^{-rτ} · ϕ(d_2) / (K σ √τ)` (`hasDerivAt_deriv_bsV_K`) is then nonnegative as
a consequence (`lognormalTerminalPDF_nonneg_via_strike_convexity`), and also by
its sign (`bsV_partial_KK_nonneg`). -/

/-- **BS call price is convex in the strike on `(0, ∞)`** — the continuous-
price face of the K-convexity principle.

The Black–Scholes price is the discounted expected call payoff under the standard normal law
(`bs_call_formula`), so this is `convexOn_integral_call` for that law. The sign of the second
strike derivative is not used. -/
theorem bsV_strike_convexOn {S r σ τ : ℝ} (hS : 0 < S) (hσ : 0 < σ) (hτ : 0 < τ) :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun K ↦ bsV K r σ S τ) :=
  (((convexOn_integral_call (integrable_bsTerminal_gaussianReal S r σ τ)).subset
      (subset_univ _) (convex_Ioi 0)).smul (Real.exp_pos (-r * τ)).le).congr fun K hK ↦ by
    simp only [smul_eq_mul]
    rw [← integral_const_mul, bsV, ← neg_mul]
    exact bs_call_formula (Q := gaussianReal 0 1) (Z := id)
      ⟨hS, mem_Ioi.1 hK, hσ, hτ, HasLaw.id⟩

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
