/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- `import Mathlib` comes transitively through `ItoLemma2D` / `PDEFromFeynmanKac`.
public import MathFin.Foundations.ItoLemma2D
public import MathFin.BlackScholes.PDEFromFeynmanKac

/-!
# The Black–Scholes PDE in the Brownian coordinate

Write the stock with drift `r` in its Brownian coordinate, `S = gbmValue S₀ r σ t x =
S₀·exp((r − σ²/2)t + σx)`, where `x` stands for the value `B_t` of the driving Brownian motion,
and consider the discounted Black–Scholes call value

  `f(t, x) = e^{−rt} · bsV K r σ (gbmValue S₀ r σ t x) (T − t)`   (`discountedCallBrownian`).

For a function of `(t, B_t)` the time-dependent Itô formula (`Foundations/ItoFormulaTD`,
`Foundations/ItoFormulaLocalized`) reads
`f(t, B_t) − f(0, B_0) = ∫ f_x(s, B_s) dB_s + ∫ (f_t + ½ f_xx)(s, B_s) ds`. This file proves
the analytic fact that makes the drift integrand vanish: for `t < T`,

  `f_t + ½ f_xx = 0`   (`discountedCallBrownian_heat_equation`),

with `f` differentiable in `t` and `f_x` differentiable in `x`, and identifies the integrand
of the stochastic term, `f_x = σ · e^{−rt} S · Φ(d₁)`, the discounted delta hedge
(`hasDerivAt_discountedCallBrownian_x`).

The proof goes through the Feynman–Kac representation (`BlackScholes/PDEFromFeynmanKac`).
In the Brownian coordinate the discounted price is a heat flow,
`f(t, x) = e^{−rT} · u(σ²(T − t), log S₀ + (r − σ²/2)T + σx)`
(`discountedCallBrownian_eq_heatFlow`), `u = feynmanU (ξ ↦ (e^ξ − K)⁺)`: `∂_t` moves only the
time slot of `u` and `∂_x` only its space slot, so the heat equation `∂_τ u = ½ ∂_yy u`
(`feynmanU_heat_equation`) gives `f_t + ½ f_xx = e^{−rT}·σ²·(−u_τ + ½ u_yy) = 0`.

Not proved here: the stochastic-integral statement itself, that `f(t, B_t)` is a local
martingale on `[0, T)`. Applying the localized Itô formula to `f` needs exponential growth
bounds on `f` and its partials up to third order, uniformly in time, and a localization away
from `t = T`, where `bsV` is not differentiable in `τ`.

## Results

* `discountedCallBrownian`: the discounted call value in the Brownian coordinate.
* `discountedCallBrownian_eq_heatFlow`: its heat-flow (Feynman–Kac) form for `t < T`.
* `hasDerivAt_discountedCallBrownian_x`: `f_x = σ · e^{−rt} S · Φ(d₁)`.
* `discountedCallBrownian_heat_equation`: `f_t + ½ f_xx = 0` for `t < T`.
-/

@[expose] public section

namespace MathFin

open FeynmanKacHeatEquation

/-- The discounted Black–Scholes call value in the Brownian coordinate:
`f(t, x) = e^{−rt} · bsV K r σ (S₀·exp((r − σ²/2)t + σx)) (T − t)`. -/
noncomputable def discountedCallBrownian (K r σ S₀ T t x : ℝ) : ℝ :=
  Real.exp (-(r * t)) * bsV K r σ (gbmValue S₀ r σ t x) (T - t)

/-- **The discounted call is a heat flow in the Brownian coordinate.** For `K, σ, S₀ > 0` and
`t < T`, `f(t, x) = e^{−rT} · u(σ²(T − t), log S₀ + (r − σ²/2)T + σx)` with
`u = feynmanU (ξ ↦ (e^ξ − K)⁺)`: the Feynman–Kac form of `bsV` (`bsV_eq_discount_feynmanU`) at
`S = gbmValue S₀ r σ t x`, where `log S + (r − σ²/2)(T − t) = log S₀ + (r − σ²/2)T + σx` and
`e^{−rt}·e^{−r(T−t)} = e^{−rT}`. -/
theorem discountedCallBrownian_eq_heatFlow {K r σ S₀ T t : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    (hS₀ : 0 < S₀) (ht : t < T) (x : ℝ) :
    discountedCallBrownian K r σ S₀ T t x =
      Real.exp (-(r * T)) * feynmanU (fun ξ ↦ max (Real.exp ξ - K) 0) (σ ^ 2 * (T - t))
        (Real.log S₀ + (r - σ ^ 2 / 2) * T + σ * x) := by
  rw [discountedCallBrownian,
    bsV_eq_discount_feynmanU (show 0 < gbmValue S₀ r σ t x from mul_pos hS₀ (Real.exp_pos _))
      hK hσ (sub_pos.mpr ht),
    ← mul_assoc, ← Real.exp_add, gbmValue, Real.log_mul hS₀.ne' (Real.exp_pos _).ne',
    Real.log_exp]
  congr 2 <;> ring

/-- **The integrand of the stochastic term: the discounted delta hedge.** For `K, σ, S₀ > 0`
and `t < T`, `∂_x f(t, x) = σ · (e^{−rt} S) · Φ(d₁)` with `S = gbmValue S₀ r σ t x` and `d₁`
at `(S, T − t)`: the chain rule through Delta (`hasDerivAt_bsV_S`) and `∂_x S = σ S`. -/
theorem hasDerivAt_discountedCallBrownian_x {K r σ S₀ T t : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    (hS₀ : 0 < S₀) (ht : t < T) (x : ℝ) :
    HasDerivAt (fun y ↦ discountedCallBrownian K r σ S₀ T t y)
      (σ * (Real.exp (-(r * t)) * gbmValue S₀ r σ t x) *
        Phi (bsd1 (gbmValue S₀ r σ t x) K r σ (T - t))) x := by
  have hG : 0 < gbmValue S₀ r σ t x := mul_pos hS₀ (Real.exp_pos _)
  exact (((hasDerivAt_bsV_S (r := r) hK hσ hG (sub_pos.mpr ht)).comp x
    (hasDerivAt_gbmValue_space S₀ r σ t x)).const_mul (Real.exp (-(r * t)))).congr_deriv
      (by ring)

/-- **The Black–Scholes PDE in the Brownian coordinate.** For `K, σ, S₀ > 0` and `t < T`, the
discounted call value `f(t, x) = e^{−rt}·bsV K r σ (S₀e^{(r−σ²/2)t+σx}) (T − t)` is
differentiable in `t`, its `x`-derivative is differentiable in `x`, and

  `∂_t f + ½ ∂_xx f = 0`,

the drift integrand of the time-dependent Itô formula for `f(t, B_t)`. Derived from the
heat-flow form (`discountedCallBrownian_eq_heatFlow`) and the heat equation of the
Feynman–Kac function (`feynmanU_heat_equation`). -/
theorem discountedCallBrownian_heat_equation {K r σ S₀ T t x : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    (hS₀ : 0 < S₀) (ht : t < T) :
    DifferentiableAt ℝ (fun s ↦ discountedCallBrownian K r σ S₀ T s x) t ∧
      DifferentiableAt ℝ (deriv fun y ↦ discountedCallBrownian K r σ S₀ T t y) x ∧
      deriv (fun s ↦ discountedCallBrownian K r σ S₀ T s x) t
        + 1 / 2 * deriv (deriv fun y ↦ discountedCallBrownian K r σ S₀ T t y) x = 0 := by
  -- the call payoff in log-price, with the growth bound the Feynman–Kac lemmas need
  have hhc : Continuous fun ξ : ℝ ↦ max (Real.exp ξ - K) 0 :=
    (Real.continuous_exp.sub continuous_const).max continuous_const
  have hhb (z : ℝ) : |max (Real.exp z - K) 0| ≤ Real.exp z := by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith) (Real.exp_nonneg z)
  have hτ : 0 < σ ^ 2 * (T - t) := mul_pos (pow_pos hσ 2) (sub_pos.mpr ht)
  have hlin (y : ℝ) :
      HasDerivAt (fun y' : ℝ ↦ Real.log S₀ + (r - σ ^ 2 / 2) * T + σ * y') σ y := by
    simpa using ((hasDerivAt_id y).const_mul σ).const_add (Real.log S₀ + (r - σ ^ 2 / 2) * T)
  -- `∂_t`: only the time slot `σ²(T − s)` of the heat flow moves
  have hdt := (((hasDerivAt_feynmanU_t hτ hhc hhb
      (Real.log S₀ + (r - σ ^ 2 / 2) * T + σ * x)).comp t
      (show HasDerivAt (fun s : ℝ ↦ σ ^ 2 * (T - s)) (-σ ^ 2) t by
        simpa using ((hasDerivAt_id t).const_sub T).const_mul (σ ^ 2))).const_mul
      (Real.exp (-(r * T)))).congr_of_eventuallyEq
    ((eventually_lt_nhds ht).mono fun s hs ↦ discountedCallBrownian_eq_heatFlow hK hσ hS₀ hs x)
  -- `∂_x` and `∂_xx`: only the space slot `log S₀ + (r − σ²/2)T + σy` moves
  have hdx (y : ℝ) := (((hasDerivAt_feynmanU_x hτ hhc hhb
      (Real.log S₀ + (r - σ ^ 2 / 2) * T + σ * y)).comp y (hlin y)).const_mul
      (Real.exp (-(r * T)))).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y' ↦ discountedCallBrownian_eq_heatFlow hK hσ hS₀ ht y')
  have hdxx := ((((hasDerivAt_feynmanU_xx hτ hhc hhb
      (Real.log S₀ + (r - σ ^ 2 / 2) * T + σ * x)).comp x (hlin x)).mul_const σ).const_mul
      (Real.exp (-(r * T)))).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y ↦ (hdx y).deriv)
  refine ⟨hdt.differentiableAt, hdxx.differentiableAt, ?_⟩
  rw [hdt.deriv, hdxx.deriv, feynmanU_heat_equation hτ]
  ring

end MathFin
