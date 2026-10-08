/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.BlackScholes.JumpDiffusionProcess
public import MathFin.BlackScholes.AmericanPut.Stopping.IndependentKernel

/-!
# Option prices at intermediate dates in a jump-diffusion

In the jump-diffusion price process (`JumpDiffusionProcess`), the conditional expectation given
`𝓕_t` of a discounted European payoff at `T` is a function of the price `S_t` alone: the
discounted expected payoff over the remaining time `T − t`, started from the spot `S_t`. The price
functions integrate the payoff against the log-return law over the remaining time
(`jumpDiffusionPutPrice`, `jumpDiffusionCallPrice`).

The put payoff is bounded, so its conditional expectation averages the increment `X_T − X_t`,
which is independent of `𝓕_t`, with the current state `X_t` frozen
(`condExp_independent_kernel`). The call payoff is the put payoff plus a forward
(`mul_max_sub_zero_parity`), and the forward's conditional expectation is
`e^{X_t}·𝔼[e^{X_T − X_t}]` (`condExp_exp_eq_of_indep_increment`). The price functions satisfy the
same put–call parity (`jumpDiffusionCallPrice_eq`), so the two pieces assemble into the call price
function.

At the compensated drift `b = r − σ²/2 − Λ(𝔼[e^J] − 1)` the call price function is Merton's
formula for the jump law: the log-return law over `τ` is the law of the canonical model at
intensity `Λτ`, on which the call is the `Poisson(Λτ)` mixture of Black–Scholes prices
(`JumpDiffusionHyp.call_eq_integral_infinitePi`). So Merton's formula prices the call at every
date, at the current spot and the remaining maturity.

## Main results

* `jumpDiffusionCallPrice_eq`, put–call parity of the price functions:
  `C(S, τ) = P(S, τ) + S·e^{(b + σ²/2 + Λ(𝔼[e^J] − 1) − r)τ} − Ke^{−rτ}`; at the compensated
  drift, `C − P = S − Ke^{−rτ}` (`jumpDiffusionCallPrice_eq_of_compensated`).
* `jumpDiffusionCallPrice_eq_merton`: at the compensated drift, `C(S, τ)` is Merton's formula.
* `JumpDiffusionProcess.condExp_put`: `𝔼[e^{−r(T−t)}(K − S_T)⁺ | 𝓕_t] = P(S_t, T − t)`.
* `JumpDiffusionProcess.condExp_call`: `𝔼[e^{−r(T−t)}(S_T − K)⁺ | 𝓕_t] = C(S_t, T − t)`.
* `JumpDiffusionProcess.condExp_call_eq_merton`: at the compensated drift and for `t < T`, the
  conditional call value is Merton's formula at `S_t` and `T − t`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-- The jump-diffusion put price function: the discounted expected payoff `e^{−rτ}(K − Se^Y)⁺`
over a time `τ`, with `Y` a jump-diffusion log-return over `τ` (`jumpDiffusionIncrementLaw`). -/
noncomputable def jumpDiffusionPutPrice (S K r b σ : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ) (τ : ℝ≥0) :
    ℝ :=
  ∫ y, rexp (-r * τ) * max (K - S * rexp y) 0 ∂(jumpDiffusionIncrementLaw b σ Λ ν τ)

/-- The jump-diffusion call price function: the discounted expected payoff `e^{−rτ}(Se^Y − K)⁺`
over a time `τ`, with `Y` a jump-diffusion log-return over `τ`. -/
noncomputable def jumpDiffusionCallPrice (S K r b σ : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ) (τ : ℝ≥0) :
    ℝ :=
  ∫ y, rexp (-r * τ) * max (S * rexp y - K) 0 ∂(jumpDiffusionIncrementLaw b σ Λ ν τ)

/-- The call payoff is the put payoff plus a forward: `c(x − K)⁺ = c(K − x)⁺ + (cx − cK)`. -/
lemma mul_max_sub_zero_parity (x K c : ℝ) :
    c * max (x - K) 0 = c * max (K - x) 0 + (c * x - c * K) := by
  rcases le_total x K with h | h
  · rw [max_eq_right (show x - K ≤ 0 by linarith), max_eq_left (show 0 ≤ K - x by linarith)]
    ring
  · rw [max_eq_left (show 0 ≤ x - K by linarith), max_eq_right (show K - x ≤ 0 by linarith)]
    ring

/-- **Put–call parity for the price functions**:
`C(S, τ) = P(S, τ) + S·e^{(b + σ²/2 + Λ(𝔼[e^J] − 1) − r)τ} − Ke^{−rτ}`. The forward
`e^{−rτ}Se^Y` has mean `S·e^{(b + σ²/2 + Λ(𝔼[e^J] − 1) − r)τ}`
(`integral_exp_jumpDiffusionIncrementLaw`), which is `S` at the compensated drift. -/
theorem jumpDiffusionCallPrice_eq (S K r b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hν : Integrable rexp ν) (τ : ℝ≥0) :
    jumpDiffusionCallPrice S K r b σ Λ ν τ
      = jumpDiffusionPutPrice S K r b σ Λ ν τ
        + S * rexp ((b + σ ^ 2 / 2 + Λ * (∫ x, rexp x ∂ν - 1) - r) * τ)
        - K * rexp (-r * τ) := by
  have hexp := integrable_exp_jumpDiffusionIncrementLaw b σ Λ hν τ
  have hput : Integrable (fun y ↦ rexp (-r * τ) * max (K - S * rexp y) 0)
      (jumpDiffusionIncrementLaw b σ Λ ν τ) :=
    ((integrable_const K).sub (hexp.const_mul S)).pos_part.const_mul _
  have hfwd : Integrable (fun y ↦ rexp (-r * τ) * (S * rexp y))
      (jumpDiffusionIncrementLaw b σ Λ ν τ) :=
    (hexp.const_mul S).const_mul _
  have hdiff : Integrable (fun y ↦ rexp (-r * τ) * (S * rexp y) - rexp (-r * τ) * K)
      (jumpDiffusionIncrementLaw b σ Λ ν τ) :=
    hfwd.sub (integrable_const _)
  have hfwdI : ∫ y, rexp (-r * τ) * (S * rexp y) ∂(jumpDiffusionIncrementLaw b σ Λ ν τ)
      = S * rexp ((b + σ ^ 2 / 2 + Λ * (∫ x, rexp x ∂ν - 1) - r) * τ) := by
    rw [integral_const_mul, integral_const_mul,
      integral_exp_jumpDiffusionIncrementLaw b σ Λ hν τ, mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  rw [jumpDiffusionCallPrice, jumpDiffusionPutPrice,
    integral_congr_ae (ae_of_all _ fun y ↦ mul_max_sub_zero_parity (S * rexp y) K
      (rexp (-r * τ))),
    integral_add hput hdiff, integral_sub hfwd (integrable_const _), hfwdI, integral_const,
    probReal_univ, one_smul]
  ring

/-- **Put–call parity at the compensated drift**: when `b = r − σ²/2 − Λ(𝔼[e^J] − 1)` the
forward is worth `S`, and `C(S, τ) = P(S, τ) + S − Ke^{−rτ}`. -/
theorem jumpDiffusionCallPrice_eq_of_compensated {S K r b σ : ℝ} {Λ : ℝ≥0} {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hν : Integrable rexp ν)
    (hb : b = r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) (τ : ℝ≥0) :
    jumpDiffusionCallPrice S K r b σ Λ ν τ
      = jumpDiffusionPutPrice S K r b σ Λ ν τ + S - K * rexp (-r * τ) := by
  have h0 : (b + σ ^ 2 / 2 + Λ * (∫ x, rexp x ∂ν - 1) - r) * τ = 0 := by
    rw [hb]
    ring
  rw [jumpDiffusionCallPrice_eq S K r b σ Λ hν τ, h0, Real.exp_zero, mul_one]

/-- **Merton's formula for the call price function.** At the compensated drift
`b = r − σ²/2 − Λ(𝔼[e^J] − 1)`, the call price function is Merton's formula for the jump law `ν`:
the `Poisson(Λτ)` mixture, over the jump count `n`, of the Black–Scholes price at the spot
`Se^{−Λτ(𝔼[e^J] − 1) + ∑_{i<n} jᵢ}`, averaged over the jump sizes `j ∼ ν^ℕ`. The log-return law
over `τ` is the law of the canonical model at intensity `Λτ` (`jumpDiffusionHyp_canonical`), on
which the call is `JumpDiffusionHyp.call_eq_integral_infinitePi`. -/
theorem jumpDiffusionCallPrice_eq_merton {S K r b σ : ℝ} (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ)
    {Λ : ℝ≥0} {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : Integrable rexp ν)
    (hb : b = r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) {τ : ℝ≥0} (hτ : 0 < τ) :
    jumpDiffusionCallPrice S K r b σ Λ ν τ
      = ∫ n, ∫ j, bsV K r σ (S * rexp (-(Λ * τ * (∫ x, rexp x ∂ν - 1))
          + ∑ i ∈ Finset.range n, j i)) τ
          ∂(Measure.infinitePi fun _ : ℕ ↦ ν) ∂(poissonMeasure (Λ * τ)) := by
  obtain ⟨h, hJ⟩ := jumpDiffusionHyp_canonical (Λ * τ) ν
  have hJ0 : Integrable (fun ω : ℝ × ℕ × (ℕ → ℝ) ↦ rexp (ω.2.2 0))
      (jumpDiffusionMeasure (Λ * τ) ν) := by
    rw [← (hJ 0).map_eq] at hν
    exact (integrable_map_measure measurable_exp.aestronglyMeasurable (hJ 0).aemeasurable).1 hν
  have key := h.call_eq_integral_infinitePi (r := r) hJ0 hS hK hσ (NNReal.coe_pos.2 hτ)
    (Λ * τ * (∫ x, rexp x ∂ν - 1))
  rw [(hJ 0).map_eq] at key
  -- the price function integrates the payoff against the canonical model at intensity `Λτ`
  have hf : Measurable fun y : ℝ ↦ rexp (-r * τ) * max (S * rexp y - K) 0 := by fun_prop
  have hmap : jumpDiffusionCallPrice S K r b σ Λ ν τ
      = ∫ ω, rexp (-r * τ) * max (S * rexp (b * τ + σ * Real.sqrt τ * ω.1
          + ∑ i ∈ Finset.range ω.2.1, ω.2.2 i) - K) 0 ∂(jumpDiffusionMeasure (Λ * τ) ν) :=
    integral_map (measurable_jumpDiffusionLogReturn b σ τ).aemeasurable hf.aestronglyMeasurable
  rw [hmap]
  refine Eq.trans (integral_congr_ae (ae_of_all _ fun ω ↦ ?_)) key
  -- at the compensated drift the log-return is the terminal exponent with `κ = Λτ(𝔼[e^J] − 1)`
  have hE : b * τ + σ * Real.sqrt τ * ω.1 + ∑ i ∈ Finset.range ω.2.1, ω.2.2 i
      = (r - σ ^ 2 / 2) * τ - Λ * τ * (∫ x, rexp x ∂ν - 1) + σ * Real.sqrt τ * ω.1
        + ∑ i ∈ Finset.range ω.2.1, ω.2.2 i := by
    rw [hb]
    ring
  show rexp (-r * τ) * max (S * rexp (b * τ + σ * Real.sqrt τ * ω.1
      + ∑ i ∈ Finset.range ω.2.1, ω.2.2 i) - K) 0
    = rexp (-r * τ) * max (S * rexp ((r - σ ^ 2 / 2) * τ - Λ * τ * (∫ x, rexp x ∂ν - 1)
      + σ * Real.sqrt τ * ω.1 + ∑ i ∈ Finset.range ω.2.1, ω.2.2 i) - K) 0
  rw [hE]

namespace JumpDiffusionProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {b σ : ℝ} {Λ : ℝ≥0} {ν : Measure ℝ}

/-- **The put at an intermediate date.** Given `𝓕_t`, the discounted put payoff at `T` has
conditional expectation `P(S_t, T − t)`, the put price function at the current price and the
remaining maturity. The increment `X_T − X_t` is independent of `𝓕_t` with the log-return law
over `T − t`, and the payoff is bounded, so `condExp_independent_kernel` averages the increment
with `X_t` frozen. -/
theorem condExp_put (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν) [IsProbabilityMeasure P]
    {S_0 K : ℝ} (hS_0 : 0 ≤ S_0) (hK : 0 ≤ K) (r : ℝ) {t T : ℝ≥0} (htT : t ≤ T) :
    P[fun ω ↦ rexp (-r * (T - t : ℝ≥0)) * max (K - S_0 * rexp (X T ω)) 0 | 𝓕 t]
      =ᵐ[P] fun ω ↦ jumpDiffusionPutPrice (S_0 * rexp (X t ω)) K r b σ Λ ν (T - t) := by
  have hXt : Measurable[𝓕 t] (X t) := (h.adapted t).measurable
  have hD : Measurable fun ω ↦ X T ω - X t ω :=
    ((h.adapted T).mono (𝓕.le T)).measurable.sub ((h.adapted t).mono (𝓕.le t)).measurable
  have hH : Measurable fun z : ℝ × ℝ ↦
      rexp (-r * ((T - t : ℝ≥0) : ℝ)) * max (K - S_0 * rexp (z.1 + z.2)) 0 := by
    fun_prop
  have hb (z : ℝ × ℝ) : ‖rexp (-r * ((T - t : ℝ≥0) : ℝ)) * max (K - S_0 * rexp (z.1 + z.2)) 0‖
      ≤ rexp (-r * ((T - t : ℝ≥0) : ℝ)) * K := by
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (le_max_right _ _))]
    exact mul_le_mul_of_nonneg_left
      (max_le (sub_le_self K (mul_nonneg hS_0 (Real.exp_pos _).le)) hK) (Real.exp_pos _).le
  have hk := BlackScholes.AmericanPut.Stopping.condExp_independent_kernel (𝓕.le t) hXt hD
    (h.indep t T htT) hH hb
  have hfun : (fun ω ↦ rexp (-r * ((T - t : ℝ≥0) : ℝ)) * max (K - S_0 * rexp (X T ω)) 0)
      = fun ω ↦ rexp (-r * ((T - t : ℝ≥0) : ℝ))
        * max (K - S_0 * rexp (X t ω + (X T ω - X t ω))) 0 := by
    funext ω
    rw [show X t ω + (X T ω - X t ω) = X T ω by ring]
  rw [hfun]
  refine hk.trans (ae_of_all _ fun ω ↦ ?_)
  show ∫ y, rexp (-r * ((T - t : ℝ≥0) : ℝ)) * max (K - S_0 * rexp (X t ω + y)) 0
      ∂(P.map fun ω ↦ X T ω - X t ω)
    = jumpDiffusionPutPrice (S_0 * rexp (X t ω)) K r b σ Λ ν (T - t)
  rw [(h.law t T htT).map_eq, jumpDiffusionPutPrice]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  show rexp (-r * ((T - t : ℝ≥0) : ℝ)) * max (K - S_0 * rexp (X t ω + y)) 0
    = rexp (-r * ((T - t : ℝ≥0) : ℝ)) * max (K - S_0 * rexp (X t ω) * rexp y) 0
  rw [Real.exp_add, mul_assoc]

/-- **The call at an intermediate date.** Given `𝓕_t`, the discounted call payoff at `T` has
conditional expectation `C(S_t, T − t)`, the call price function at the current price and the
remaining maturity. The call payoff is the put payoff (`condExp_put`) plus a forward, whose
conditional expectation is `e^{X_t}·𝔼[e^{X_T − X_t}]` (`condExp_exp_eq_of_indep_increment`), and
the price functions satisfy the same parity (`jumpDiffusionCallPrice_eq`). -/
theorem condExp_call (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν) [IsProbabilityMeasure P]
    [IsProbabilityMeasure ν] (hν : Integrable rexp ν) {S_0 K : ℝ} (hS_0 : 0 ≤ S_0) (hK : 0 ≤ K)
    (r : ℝ) {t T : ℝ≥0} (htT : t ≤ T) :
    P[fun ω ↦ rexp (-r * (T - t : ℝ≥0)) * max (S_0 * rexp (X T ω) - K) 0 | 𝓕 t]
      =ᵐ[P] fun ω ↦ jumpDiffusionCallPrice (S_0 * rexp (X t ω)) K r b σ Λ ν (T - t) := by
  have hE := h.integrable_exp hν T
  have hD_int : Integrable (fun ω ↦ rexp (X T ω - X t ω)) P :=
    Integrable.of_integral_ne_zero (by
      rw [h.integral_exp_increment hν htT]
      exact (Real.exp_pos _).ne')
  have hput_int : Integrable
      (fun ω ↦ rexp (-r * ((T - t : ℝ≥0) : ℝ)) * max (K - S_0 * rexp (X T ω)) 0) P :=
    ((integrable_const K).sub (hE.const_mul S_0)).pos_part.const_mul _
  have hfwd_int : Integrable ((rexp (-r * ((T - t : ℝ≥0) : ℝ)) * S_0) • (fun ω ↦ rexp (X T ω))
      - fun _ ↦ rexp (-r * ((T - t : ℝ≥0) : ℝ)) * K) P :=
    (hE.smul _).sub (integrable_const _)
  -- the call payoff is the put payoff plus a forward
  have hsplit : (fun ω ↦ rexp (-r * ((T - t : ℝ≥0) : ℝ)) * max (S_0 * rexp (X T ω) - K) 0)
      = (fun ω ↦ rexp (-r * ((T - t : ℝ≥0) : ℝ)) * max (K - S_0 * rexp (X T ω)) 0)
        + ((rexp (-r * ((T - t : ℝ≥0) : ℝ)) * S_0) • (fun ω ↦ rexp (X T ω))
          - fun _ ↦ rexp (-r * ((T - t : ℝ≥0) : ℝ)) * K) := by
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_max_sub_zero_parity (S_0 * rexp (X T ω)) K]
    ring
  rw [hsplit]
  calc P[(fun ω ↦ rexp (-r * ((T - t : ℝ≥0) : ℝ)) * max (K - S_0 * rexp (X T ω)) 0)
        + ((rexp (-r * ((T - t : ℝ≥0) : ℝ)) * S_0) • (fun ω ↦ rexp (X T ω))
          - fun _ ↦ rexp (-r * ((T - t : ℝ≥0) : ℝ)) * K) | 𝓕 t]
      =ᵐ[P] P[fun ω ↦ rexp (-r * ((T - t : ℝ≥0) : ℝ)) * max (K - S_0 * rexp (X T ω)) 0 | 𝓕 t]
        + P[(rexp (-r * ((T - t : ℝ≥0) : ℝ)) * S_0) • (fun ω ↦ rexp (X T ω))
          - fun _ ↦ rexp (-r * ((T - t : ℝ≥0) : ℝ)) * K | 𝓕 t] :=
        condExp_add hput_int hfwd_int _
    _ =ᵐ[P] (fun ω ↦ jumpDiffusionPutPrice (S_0 * rexp (X t ω)) K r b σ Λ ν (T - t))
        + ((rexp (-r * ((T - t : ℝ≥0) : ℝ)) * S_0)
            • (fun ω ↦ rexp (X t ω) * ∫ ω', rexp (X T ω' - X t ω') ∂P)
          - fun _ ↦ rexp (-r * ((T - t : ℝ≥0) : ℝ)) * K) := by
        refine (h.condExp_put hS_0 hK r htT).add ?_
        refine (condExp_sub (hE.smul _) (integrable_const _) _).trans ?_
        rw [condExp_const (𝓕.le t)]
        exact ((condExp_smul _ _ _).trans
          ((condExp_exp_eq_of_indep_increment h.adapted (h.indep t T htT) hE
            hD_int).const_smul _)).sub Filter.EventuallyEq.rfl
    _ = fun ω ↦ jumpDiffusionCallPrice (S_0 * rexp (X t ω)) K r b σ Λ ν (T - t) := by
        funext ω
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [jumpDiffusionCallPrice_eq _ K r b σ Λ hν, h.integral_exp_increment hν htT, sub_mul,
          Real.exp_sub, neg_mul, Real.exp_neg]
        ring

/-- **Merton's formula at intermediate dates.** At the compensated drift
`b = r − σ²/2 − Λ(𝔼[e^J] − 1)` and for `t < T`, the discounted call payoff at `T` has conditional
expectation given `𝓕_t` equal to Merton's formula for the jump law `ν` at the current price
`S_t = S₀e^{X_t}` and the remaining maturity `T − t` (`condExp_call`,
`jumpDiffusionCallPrice_eq_merton`). -/
theorem condExp_call_eq_merton (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν)
    [IsProbabilityMeasure P] [IsProbabilityMeasure ν] (hν : Integrable rexp ν) {r : ℝ}
    (hb : b = r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) {S_0 K : ℝ} (hS_0 : 0 < S_0)
    (hK : 0 < K) (hσ : 0 < σ) {t T : ℝ≥0} (htT : t < T) :
    P[fun ω ↦ rexp (-r * (T - t : ℝ≥0)) * max (S_0 * rexp (X T ω) - K) 0 | 𝓕 t]
      =ᵐ[P] fun ω ↦ ∫ n, ∫ j, bsV K r σ (S_0 * rexp (X t ω)
          * rexp (-(Λ * (T - t : ℝ≥0) * (∫ x, rexp x ∂ν - 1)) + ∑ i ∈ Finset.range n, j i))
          (T - t : ℝ≥0) ∂(Measure.infinitePi fun _ : ℕ ↦ ν) ∂(poissonMeasure (Λ * (T - t))) :=
  (h.condExp_call hν hS_0.le hK.le r htT.le).trans <| ae_of_all _ fun _ ↦
    jumpDiffusionCallPrice_eq_merton (mul_pos hS_0 (Real.exp_pos _)) hK hσ hν hb
      (tsub_pos_of_lt htT)

end JumpDiffusionProcess

end MathFin
