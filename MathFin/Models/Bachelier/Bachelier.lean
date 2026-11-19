/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Gaussian.GaussianPartialMoments

/-!
# Bachelier model option pricing

The Bachelier (1900) model is the historical predecessor of Black-Scholes:
asset prices follow an **arithmetic** Brownian motion `S_T = S_0 + σ · W_T`
(no exponential, no log-normality). Used today for short-tenor / negative-rate
markets where lognormality is inappropriate.

Under `BachelierHyp`, the discounted call price is

    V_bach = (S_0 - K) · Φ(d) + σ √T · ϕ(d),

where `d = (S_0 - K) / (σ √T)`, `Φ` and `ϕ` are the standard normal CDF and
PDF. The terminal price is `N(S_0, σ² T)`, and the formula is the stop-loss transform of a
general Gaussian law, `gaussian_call_formula` in `Probability/Gaussian/GaussianPartialMoments`.

## Main definitions

* `BachelierHyp`: the Bachelier risk-neutral hypothesis: `0 < K`, `0 < σ`, `0 < T` and `Z` standard
  normal under `Q` (the terminal price is then `bachelierTerminal S_0 σ T (Z ω)`).
* `bachelierD`: the dimensionless distance to the strike `d = (S_0 - K) / (σ √T)`.
* `bachelierTerminal`: the terminal price as a function of the driver, `S_0 + σ √T · z`.

## Main results

* `bachelier_call_formula`: under `BachelierHyp`, the expected European call payoff
  `E_Q[max (S_T - K) 0]` equals `(S_0 - K) * Φ d + σ * √T * ϕ d` with `d = bachelierD S_0 K σ T`.

## References

* [Bachelier (1900)][Bachelier1900]
* [F. Black, *The pricing of commodity contracts*][Black1976]
* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006]

## Tags

Bachelier model, arithmetic Brownian motion, normal model, negative rates, call price,
stop-loss transform, MSC 91G20, MSC 60J65, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Filter
open scoped NNReal ENNReal Topology

/-! ### Bachelier model hypothesis -/

/-- Bachelier model risk-neutral hypothesis: the terminal price `S_T = S_0 + σ √T · Z`
with `Z ~ N(0, 1)`. The asset follows arithmetic Brownian motion (no exponential). -/
structure BachelierHyp {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (S_0 K σ T : ℝ) (Z : Ω → ℝ) : Prop where
  K_pos : 0 < K
  σ_pos : 0 < σ
  T_pos : 0 < T
  Z_law : HasLaw Z (gaussianReal 0 1) Q

/-- Bachelier `d`: dimensionless distance to the strike. -/
noncomputable def bachelierD (S_0 K σ T : ℝ) : ℝ :=
  (S_0 - K) / (σ * Real.sqrt T)

/-- Bachelier terminal price `S_T(z) = S_0 + σ √T · z`. -/
noncomputable def bachelierTerminal (S_0 σ T : ℝ) (z : ℝ) : ℝ :=
  S_0 + σ * Real.sqrt T * z

/-! ### Bachelier call pricing formula -/

/-- **Bachelier European call pricing formula.**

For an asset whose risk-neutral dynamics are arithmetic Brownian motion
(`bachelierTerminal(z) = S_0 + σ √T · z` with `Z ~ N(0, 1)`),
the expected payoff of the European call `max(S_T - K, 0)` is

    E_Q[max(S_T - K, 0)] = (S_0 - K) · Φ(d) + σ √T · ϕ(d),

where `d = (S_0 - K) / (σ √T)`.

Derivation: `S_T ~ N(S_0, (σ √T)²)`, so this is the instance `m = S_0`, `v = (σ √T)²` of the
stop-loss transform of a general Gaussian law, `gaussian_call_formula`. -/
theorem bachelier_call_formula {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K σ T : ℝ} {Z : Ω → ℝ}
    (h : BachelierHyp Q S_0 K σ T Z) :
    ∫ ω, max (bachelierTerminal S_0 σ T (Z ω) - K) 0 ∂Q
      = (S_0 - K) * Phi (bachelierD S_0 K σ T) +
        σ * Real.sqrt T * gaussianPDFReal 0 1 (bachelierD S_0 K σ T) := by
  obtain ⟨_, hσ, hT, hZ⟩ := h
  have hc : 0 < σ * Real.sqrt T := mul_pos hσ (Real.sqrt_pos.2 hT)
  have hlaw : HasLaw (fun ω ↦ bachelierTerminal S_0 σ T (Z ω))
      (gaussianReal S_0 (NNReal.mk ((σ * Real.sqrt T) ^ 2) (sq_nonneg _))) Q := by
    have h := gaussianReal_const_add (gaussianReal_const_mul hZ (σ * Real.sqrt T)) S_0
    rw [mul_zero, zero_add, mul_one] at h
    exact h
  have hv : NNReal.mk ((σ * Real.sqrt T) ^ 2) (sq_nonneg _) ≠ 0 :=
    fun h ↦ (pow_pos hc 2).ne' (congrArg NNReal.toReal h)
  have := gaussian_call_formula hlaw hv K
  simpa only [NNReal.coe_mk, Real.sqrt_sq hc.le, bachelierD] using this

end MathFin
