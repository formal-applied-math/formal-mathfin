/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.BlackScholes.Chooser
public import MathFin.BlackScholes.PDE
public import MathFin.BlackScholes.PutGreeks
public import MathFin.BlackScholes.GaussianSmoothing
public import MathFin.BlackScholes.GBMLogMoments
public import MathFin.Foundations.GaussianPairLinearLaw

/-!
# Chooser option as call-plus-put portfolio, priced in Black–Scholes

The pre-existing `BlackScholes/Chooser.lean` derives the algebraic identity
`max(C, P) = C + max(0, K_disc − S)` from put-call parity. That identity is
the chooser's *static portfolio replication* at the chooser date.

This file prices it in the Black–Scholes model. At the chooser date `t₁` the call and put
are worth their Black–Scholes prices `C_{t₁} = bsV K r σ S_{t₁} (T − t₁)` and
`P_{t₁} = bsP K r σ S_{t₁} (T − t₁)`, with `S_{t₁}` lognormal (`BSCallHyp` at maturity `t₁`).
Then

  `e^{−r t₁}·𝔼[max(C_{t₁}, P_{t₁})] = bsV K r σ S₀ T + bsP (K e^{−r(T−t₁)}) r σ S₀ t₁`

(`chooser_price_eq_expected_payoff`). Put–call parity splits the payoff into the call and a
put struck at `K e^{−r(T−t₁)}` with maturity `t₁`; the put is `bs_put_formula`; the call
leg uses that the expected discounted call price at `t₁` is today's call price
(`integral_discounted_bsV_at_date`): averaging `bsV` over the lognormal law of `S_{t₁}`
is a Black–Scholes price again (`integral_bsV_mul_exp_gaussianReal_of_sq`,
`BlackScholes/GaussianSmoothing.lean`) whose total variance `σ²T` and forward fold back into
`e^{r t₁}·bsV K r σ S₀ T` (`bsV_spot_growth_total_variance`).

**Scope.** The chooser-date values are taken to be the Black–Scholes prices of `S_{t₁}`;
that they are the conditional expectations of the maturity payoffs given `𝓕_{t₁}` is not
re-derived here.

## Results

* `chooserPrice`: definition `bsV K r σ S_0 T + bsP (K e^{−r(T−t_1)}) r σ S_0 t_1`.
* `chooserPayoff_decompose_BS`: specialisation of `chooser_via_pcp` with the
  BS-style discounted strike.
* `chooser_integral_decomp`: the linearity-of-expectation step.
* `bsV_spot_growth_total_variance`: `bsV K r σ' (S e^{rt}) τ = e^{rt}·bsV K r σ S (τ + t)`
  when `σ'²τ = σ²(τ + t)`.
* `integral_discounted_bsV_at_date`: `e^{−rt}·𝔼[bsV K r σ S_t (T − t)] = bsV K r σ S₀ T`.
* `chooser_price_eq_expected_payoff`: the chooser price is the discounted expected chooser
  payoff.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

/-- **Chooser option closed-form price** under BS: long call (strike `K`,
maturity `T`) + long put (strike `K · e^{−r(T − t_1)}`, maturity `t_1`).

Derivation rationale: at chooser date `t_1`, the holder picks `max(C_{t_1},
P_{t_1})`. By PCP at `t_1`, this equals `C_{t_1} + max(0, K · e^{−r(T −
t_1)} − S_{t_1})`. The first term is the call payoff; the second is the put
payoff with strike `K · e^{−r(T − t_1)}` and maturity `t_1`. Time-0 prices
are then `bsV(K, T)` and `bsP(K · e^{−r(T−t_1)}, t_1)` respectively. -/
noncomputable def chooserPrice (S_0 K r σ T t_1 : ℝ) : ℝ :=
  bsV K r σ S_0 T + bsP (K * Real.exp (-(r * (T - t_1)))) r σ S_0 t_1

/-- **Chooser payoff decomposition with the BS-style discounted strike**:
specialisation of `chooser_via_pcp` to `K_disc = K · e^{−r(T − t_1)}`. -/
theorem chooserPayoff_decompose_BS
    (C P S K r T t_1 : ℝ)
    (hPCP : C - P = S - K * Real.exp (-(r * (T - t_1)))) :
    max C P = C + max 0 (K * Real.exp (-(r * (T - t_1))) - S) :=
  chooser_via_pcp C P S _ hPCP

/-- **Chooser integral decomposition (linearity-of-expectation step)**: for
random call value `C : Ω → ℝ` and put value `P : Ω → ℝ` at the chooser date
satisfying PCP pointwise with discounted strike `K_disc`, the expectation
of the chooser payoff `max(C, P)` decomposes as `E[C] + E[max(0, K_disc − S)]`.

This is the first integration step in the chooser-pricing chain; with each piece priced
(`integral_discounted_bsV_at_date`, `bs_put_formula`) it gives
`chooser_price_eq_expected_payoff`. -/
theorem chooser_integral_decomp
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (Q : Measure Ω)
    (C P S : Ω → ℝ) (K_disc : ℝ)
    (hPCP : ∀ ω, C ω - P ω = S ω - K_disc)
    (hint_C : Integrable C Q)
    (hint_put : Integrable (fun ω ↦ max 0 (K_disc - S ω)) Q) :
    ∫ ω, max (C ω) (P ω) ∂Q =
      (∫ ω, C ω ∂Q) + ∫ ω, max 0 (K_disc - S ω) ∂Q := by
  have h_pointwise : ∀ ω, max (C ω) (P ω) = C ω + max 0 (K_disc - S ω) :=
    fun ω ↦ chooser_via_pcp (C ω) (P ω) (S ω) K_disc (hPCP ω)
  rw [show (fun ω ↦ max (C ω) (P ω)) =
        (fun ω ↦ C ω + max 0 (K_disc - S ω)) from funext h_pointwise]
  exact integral_add hint_C hint_put

/-- **Chooser price expanded** via the BS pricing formulas `bsV` and `bsP`:
`chooserPrice = S_0 · Φ(d_1^{call}) − K · e^{−rT} · Φ(d_2^{call}) +
                K_disc · e^{−r·t_1} · Φ(−d_2^{put}) − S_0 · Φ(−d_1^{put})`,
where the `^{call}` parameters use strike `K`, maturity `T`, and the
`^{put}` parameters use strike `K_disc = K · e^{−r(T − t_1)}`, maturity
`t_1`. This makes the explicit closed form visible. -/
theorem chooserPrice_expanded (S_0 K r σ T t_1 : ℝ) :
    chooserPrice S_0 K r σ T t_1 =
      (S_0 * Phi (bsd1 S_0 K r σ T) -
        K * Real.exp (-(r * T)) * Phi (bsd2 S_0 K r σ T)) +
      ((K * Real.exp (-(r * (T - t_1)))) * Real.exp (-(r * t_1)) *
          Phi (-(bsd2 S_0 (K * Real.exp (-(r * (T - t_1)))) r σ t_1)) -
        S_0 * Phi (-(bsd1 S_0 (K * Real.exp (-(r * (T - t_1)))) r σ t_1))) := by
  unfold chooserPrice bsV bsP
  ring

/-! ### Pricing the chooser in the Black–Scholes model -/

/-- **Total-variance invariance of the Black–Scholes call.** Moving `t` years of maturity into
spot growth — spot `S·e^{rt}`, maturity `τ`, and a volatility `σ'` carrying the same total
variance, `σ'²τ = σ²(τ + t)` — rescales the price by `e^{rt}`:
`bsV K r σ' (S e^{rt}) τ = e^{rt}·bsV K r σ S (τ + t)`. Both `d₁` and `d₂` are unchanged. -/
lemma bsV_spot_growth_total_variance {K r σ σ' S τ t : ℝ} (hS : 0 < S) (hK : 0 < K)
    (hσ : 0 < σ) (hσ' : 0 < σ') (hvar : σ' ^ 2 * τ = σ ^ 2 * (τ + t)) :
    bsV K r σ' (S * Real.exp (r * t)) τ = Real.exp (r * t) * bsV K r σ S (τ + t) := by
  have hsd : σ' * Real.sqrt τ = σ * Real.sqrt (τ + t) := by
    rw [← Real.sqrt_sq hσ'.le, ← Real.sqrt_sq hσ.le, ← Real.sqrt_mul (sq_nonneg _),
      ← Real.sqrt_mul (sq_nonneg _), hvar]
  have hd1 : bsd1 (S * Real.exp (r * t)) K r σ' τ = bsd1 S K r σ (τ + t) := by
    unfold bsd1
    rw [hsd, show S * Real.exp (r * t) / K = S / K * Real.exp (r * t) by ring,
      Real.log_mul (div_pos hS hK).ne' (Real.exp_pos _).ne', Real.log_exp]
    congr 1
    linear_combination hvar / 2
  have hd2 : bsd2 (S * Real.exp (r * t)) K r σ' τ = bsd2 S K r σ (τ + t) := by
    unfold bsd2
    rw [hd1, hsd]
  have he : Real.exp (r * t) * Real.exp (-(r * (τ + t))) = Real.exp (-(r * τ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold bsV
  rw [hd1, hd2]
  linear_combination (K * Phi (bsd2 S K r σ (τ + t))) * he

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q]

/-- **The discounted Black–Scholes call price keeps its expectation across one date.** If the
spot at date `t` is lognormal, `S_t = bsTerminal S₀ r σ t Z` with `Z ~ N(0, 1)`, then the expected
discounted call price at `t`, for the remaining maturity `T − t`, is today's call price:
`e^{−rt}·𝔼[bsV K r σ S_t (T − t)] = bsV K r σ S₀ T`. The average of `bsV` over the lognormal
law of `S_t` is `integral_bsV_mul_exp_gaussianReal_of_sq`; the result is folded back by
`bsV_spot_growth_total_variance`. -/
theorem integral_discounted_bsV_at_date {S_0 K r σ t T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ t Z) (htT : t < T) :
    ∫ ω, Real.exp (-r * t) * bsV K r σ (bsTerminal S_0 r σ t (Z ω)) (T - t) ∂Q
      = bsV K r σ S_0 T := by
  obtain ⟨hS, hK, hσ, ht, hZ⟩ := h
  have hτ : 0 < T - t := sub_pos.mpr htT
  have hT : 0 < T := ht.trans htT
  have hv : ((σ ^ 2 * t).toNNReal : ℝ) = σ ^ 2 * t :=
    Real.coe_toNNReal _ (mul_nonneg (sq_nonneg σ) ht.le)
  have hG : HasLaw (fun ω ↦ bsLogReturn r σ t (Z ω))
      (gaussianReal ((r - σ ^ 2 / 2) * t) (σ ^ 2 * t).toNNReal) Q :=
    bsLogReturn_hasLaw ⟨hS, hK, hσ, ht, hZ⟩
  have hσ' : 0 < σ * Real.sqrt (T / (T - t)) := mul_pos hσ (Real.sqrt_pos.mpr (div_pos hT hτ))
  have hvar : (σ * Real.sqrt (T / (T - t))) ^ 2 * (T - t) = σ ^ 2 * (T - t + t) := by
    rw [mul_pow, Real.sq_sqrt (div_pos hT hτ).le, mul_assoc, div_mul_cancel₀ _ hτ.ne',
      sub_add_cancel]
  have hvar' : (σ * Real.sqrt (T / (T - t))) ^ 2 * (T - t)
      = σ ^ 2 * (T - t) + ((σ ^ 2 * t).toNNReal : ℝ) := by
    rw [hv, hvar]
    ring
  have hmeas : Measurable fun x ↦ bsV K r σ (S_0 * Real.exp x) (T - t) :=
    (measurable_bsV_spot K r σ (T - t)).comp (by fun_prop)
  calc ∫ ω, Real.exp (-r * t) * bsV K r σ (bsTerminal S_0 r σ t (Z ω)) (T - t) ∂Q
      = Real.exp (-r * t) * ∫ x, bsV K r σ (S_0 * Real.exp x) (T - t)
          ∂(gaussianReal ((r - σ ^ 2 / 2) * t) (σ ^ 2 * t).toNNReal) := by
        rw [integral_const_mul]
        congr 1
        exact hG.integral_comp hmeas.aestronglyMeasurable
    _ = Real.exp (-r * t) * bsV K r (σ * Real.sqrt (T / (T - t)))
          (S_0 * Real.exp ((r - σ ^ 2 / 2) * t + ((σ ^ 2 * t).toNNReal : ℝ) / 2)) (T - t) := by
        rw [integral_bsV_mul_exp_gaussianReal_of_sq hS hK hσ hσ' hτ _ hvar']
    _ = bsV K r σ S_0 T := by
        rw [show (r - σ ^ 2 / 2) * t + ((σ ^ 2 * t).toNNReal : ℝ) / 2 = r * t by rw [hv]; ring,
          bsV_spot_growth_total_variance hS hK hσ hσ' hvar, sub_add_cancel, ← mul_assoc,
          ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, one_mul]

/-- **The chooser price is the discounted expected chooser payoff** (Black–Scholes model).
With the spot at the chooser date `t₁ < T` lognormal (`BSCallHyp` at maturity `t₁`) and the
chooser-date call and put valued at their Black–Scholes prices
`C_{t₁} = bsV K r σ S_{t₁} (T − t₁)`, `P_{t₁} = bsP K r σ S_{t₁} (T − t₁)`,

  `e^{−r t₁}·𝔼[max(C_{t₁}, P_{t₁})] = chooserPrice S₀ K r σ T t₁
                                    = bsV K r σ S₀ T + bsP (K e^{−r(T−t₁)}) r σ S₀ t₁`.

Put–call parity at `t₁` (`chooserPayoff_decompose_BS`, `bsP_eq_bsV`) splits the payoff; the
call leg is `integral_discounted_bsV_at_date` and the put leg is `bs_put_formula`. -/
theorem chooser_price_eq_expected_payoff {S_0 K r σ T t_1 : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ t_1 Z) (ht : t_1 < T) :
    ∫ ω, Real.exp (-r * t_1) * max (bsV K r σ (bsTerminal S_0 r σ t_1 (Z ω)) (T - t_1))
        (bsP K r σ (bsTerminal S_0 r σ t_1 (Z ω)) (T - t_1)) ∂Q
      = chooserPrice S_0 K r σ T t_1 := by
  have hput : BSCallHyp Q S_0 (K * Real.exp (-(r * (T - t_1)))) r σ t_1 Z :=
    ⟨h.S_0_pos, mul_pos h.K_pos (Real.exp_pos _), h.σ_pos, h.T_pos, h.Z_law⟩
  have hpt (ω : Ω) : Real.exp (-r * t_1) *
      max (bsV K r σ (bsTerminal S_0 r σ t_1 (Z ω)) (T - t_1))
        (bsP K r σ (bsTerminal S_0 r σ t_1 (Z ω)) (T - t_1))
      = Real.exp (-r * t_1) * bsV K r σ (bsTerminal S_0 r σ t_1 (Z ω)) (T - t_1)
        + Real.exp (-r * t_1) *
          max (K * Real.exp (-(r * (T - t_1))) - bsTerminal S_0 r σ t_1 (Z ω)) 0 := by
    have hpcp := bsP_eq_bsV K r σ (bsTerminal S_0 r σ t_1 (Z ω)) (T - t_1)
    rw [chooserPayoff_decompose_BS (bsV K r σ (bsTerminal S_0 r σ t_1 (Z ω)) (T - t_1))
        (bsP K r σ (bsTerminal S_0 r σ t_1 (Z ω)) (T - t_1)) (bsTerminal S_0 r σ t_1 (Z ω))
        K r T t_1 (by rw [hpcp]; ring), max_comm 0, mul_add]
  have hC : Integrable
      (fun ω ↦ Real.exp (-r * t_1) * bsV K r σ (bsTerminal S_0 r σ t_1 (Z ω)) (T - t_1)) Q :=
    (integrable_bsV_mul_exp (bsLogReturn_hasLaw h).aemeasurable
      (by simpa only [one_mul] using integrable_exp_mul_of_hasLaw (bsLogReturn_hasLaw h) 1) h.S_0_pos h.K_pos
      h.σ_pos (sub_pos.mpr ht)).const_mul _
  simp_rw [hpt]
  rw [integral_add hC
      (integrable_bsPut_payoff h.Z_law S_0 (K * Real.exp (-(r * (T - t_1)))) r σ t_1),
    integral_discounted_bsV_at_date h ht, bs_put_formula hput, chooserPrice, bsP, neg_mul]

end MathFin
