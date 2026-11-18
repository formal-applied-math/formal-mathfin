/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.BlackScholes.Forward
public import MathFin.Models.Jumps.JumpDiffusionVarianceSwap
public import MathFin.Pricing.ForwardMeasure

/-!
# Volatility swap fair strike under lognormal realized variance

A volatility swap pays `N · (σ_R − K_vol)` where `σ_R = √V` is the square root of the
annualized realized variance `V`. Its fair strike is `E[√V]`, which the replicating-portfolio
argument for the variance swap (`varianceSwap_fairStrike`, the fair variance strike `E[V]`) does
not determine: `√·` is strictly concave, so `E[√V] < √E[V]` whenever `V` is random.

This file computes `E[√V]` under one explicit, **assumed** distribution for the realized
variance: `V` is lognormal with mean `K` (the fair variance strike) and log-volatility `s`,
`V = K · exp(−s²/2 + s·Z)` with `Z` standard normal (`bsTerminal K 0 s 1 Z`). The law of `V`
is an input, not a derived property of any price process; the log-volatility `s` is a free
parameter that a model or the market must supply. Under it,

  `E[√V] = √K · exp(−s²/8)`,

because `√V` is again lognormal with half the log-volatility, and the library's forward identity
`expected_terminal_eq_forward` (`Models/BlackScholes/Forward.lean`) gives its mean. The factor
`exp(−s²/8)` is the *convexity adjustment* of the volatility swap against the square root of the
variance swap strike. To first order in `s²` it agrees with the approximation
`E[√V] ≈ √E[V] − Var(V)/(8 E[V]^{3/2})` of Brockhaus and Long (2000), since
`Var(V) = K²(e^{s²} − 1)` under the assumed law; neither that variance identity nor the
approximation is proved here.

## Main definitions

* `volSwapFairStrike`: the fair volatility strike `√K · exp(−s²/8)`.
* `VolSwapHyp`: the lognormal-realized-variance hypothesis (`0 < K`, `0 < s`, `Z` standard
  normal).

## Main results

* `integral_sqrt_lognormalVariance`: `E[√V] = volSwapFairStrike K s` for
  `V = bsTerminal K 0 s 1 Z`.
* `integral_volSwapPayoff`: the swap `√V − K_vol` has expected payoff
  `volSwapFairStrike K s − K_vol`, so it is zero exactly at the fair strike.
* `volSwapFairStrike_lt_sqrt`: the strict concavity gap `volSwapFairStrike K s < √K` for
  `s ≠ 0`.
* `volSwapFairStrike_at_varianceSwap`: evaluated at the fair variance strike `σ²` produced by
  the log-contract replication `varianceSwap_fairStrike`, the volatility strike is
  `σ · exp(−s²/8) < σ`.

* `volSwapValue_forwardMeasure`: the time-0 value of the swap, paid at `T`, is the discount
  factor `exp(−rT)` times `N · (volSwapFairStrike K s − K_vol)`, when the realized variance is
  lognormal under the `T`-forward measure of a constant bank account `exp(rT)`
  (`forwardMeasure_price`).

## Scope

Undiscounted, unseasoned, annualized strikes; the payment-date discount factor is not
modelled. The lognormal law of `V` is assumed (see above), so these are statements about the
assumed law, not about a Black–Scholes or stochastic-volatility price path.

## References

* [K. Demeterfi, E. Derman, M. Kamal, J. Zou, *More than you ever wanted to know about
  volatility swaps*][DemeterfiDermanKamalZou1999] — the volatility swap as a concave function of
  variance and the replication mismatch of a variance-swap hedge.

## Tags

volatility swap, variance swap, convexity adjustment, lognormal, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

/-- **Fair volatility strike under lognormal realized variance**: `√K · exp(−s²/8)` for fair
variance strike `K` and log-volatility `s` of the realized variance. -/
noncomputable def volSwapFairStrike (K s : ℝ) : ℝ :=
  Real.sqrt K * Real.exp (-(s ^ 2 / 8))

/-- The lognormal-realized-variance hypothesis: fair variance strike `K > 0`, log-volatility
`s > 0` of the realized variance, and `Z` standard normal under `Q`. The realized variance is
then `bsTerminal K 0 s 1 Z = K · exp(−s²/2 + s·Z)`, with `E[V] = K`. -/
structure VolSwapHyp {Ω : Type*} {mΩ : MeasurableSpace Ω} (Q : Measure Ω)
    [IsProbabilityMeasure Q] (K s : ℝ) (Z : Ω → ℝ) : Prop where
  K_pos : 0 < K
  s_pos : 0 < s
  Z_law : HasLaw Z (gaussianReal 0 1) Q

/-- The square root of a driftless unit-horizon lognormal factor is lognormal with half the
log-volatility: `√(K · exp(−s²/2 + s z)) = √K · bsTerminal 1 (−s²/8) (s/2) 1 z`. -/
lemma sqrt_bsTerminal_driftless {K : ℝ} (hK : 0 < K) (s z : ℝ) :
    Real.sqrt (bsTerminal K 0 s 1 z)
      = Real.sqrt K * bsTerminal 1 (-(s ^ 2 / 8)) (s / 2) 1 z := by
  rw [bsTerminal, bsTerminal, Real.sqrt_mul hK.le, one_mul, ← Real.exp_half]
  congr 2
  simp only [Real.sqrt_one, mul_one]
  ring

/-- `√V` has the lognormal factor of half the log-volatility, so it is integrable. -/
lemma integrable_sqrt_lognormalVariance {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q] {K s : ℝ} {Z : Ω → ℝ}
    (h : VolSwapHyp Q K s Z) :
    Integrable (fun ω ↦ Real.sqrt (bsTerminal K 0 s 1 (Z ω))) Q := by
  have h' : BSCallHyp Q 1 1 (-(s ^ 2 / 8)) (s / 2) 1 Z :=
    ⟨one_pos, one_pos, half_pos h.s_pos, one_pos, h.Z_law⟩
  simp_rw [sqrt_bsTerminal_driftless h.K_pos]
  exact (integrable_bsTerminal h'.Z_law 1 (-(s ^ 2 / 8)) (s / 2) 1).const_mul _

/-- **Expected square root of a lognormal realized variance.** For `V = bsTerminal K 0 s 1 Z`
(lognormal, mean `K`, log-volatility `s`), `E[√V] = √K · exp(−s²/8)`. -/
theorem integral_sqrt_lognormalVariance {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q] {K s : ℝ} {Z : Ω → ℝ}
    (h : VolSwapHyp Q K s Z) :
    ∫ ω, Real.sqrt (bsTerminal K 0 s 1 (Z ω)) ∂Q = volSwapFairStrike K s := by
  have h' : BSCallHyp Q 1 1 (-(s ^ 2 / 8)) (s / 2) 1 Z :=
    ⟨one_pos, one_pos, half_pos h.s_pos, one_pos, h.Z_law⟩
  simp_rw [sqrt_bsTerminal_driftless h.K_pos]
  rw [integral_const_mul, expected_terminal_eq_forward h', one_mul, mul_one, volSwapFairStrike]

/-- **The volatility swap is fair at `volSwapFairStrike`.** The swap `√V − K_vol` has expected
payoff `volSwapFairStrike K s − K_vol` under the assumed lognormal law of `V`. -/
theorem integral_volSwapPayoff {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q] {K s : ℝ} {Z : Ω → ℝ}
    (h : VolSwapHyp Q K s Z) (Kvol : ℝ) :
    ∫ ω, (Real.sqrt (bsTerminal K 0 s 1 (Z ω)) - Kvol) ∂Q
      = volSwapFairStrike K s - Kvol := by
  rw [integral_sub (integrable_sqrt_lognormalVariance h) (integrable_const Kvol),
    integral_sqrt_lognormalVariance h]
  simp

/-- The fair volatility strike is positive. -/
lemma volSwapFairStrike_pos {K : ℝ} (hK : 0 < K) (s : ℝ) : 0 < volSwapFairStrike K s :=
  mul_pos (Real.sqrt_pos.2 hK) (Real.exp_pos _)

/-- Without variance-of-variance (`s = 0`) the volatility strike is the square root of the
variance strike. -/
@[simp] lemma volSwapFairStrike_zero (K : ℝ) : volSwapFairStrike K 0 = Real.sqrt K := by
  simp [volSwapFairStrike]

/-- **The concavity gap.** For `s ≠ 0` the fair volatility strike is strictly below the square
root of the fair variance strike, `√K · exp(−s²/8) < √K`. -/
theorem volSwapFairStrike_lt_sqrt {K : ℝ} (hK : 0 < K) {s : ℝ} (hs : s ≠ 0) :
    volSwapFairStrike K s < Real.sqrt K := by
  have h1 : Real.exp (-(s ^ 2 / 8)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have := sq_pos_of_ne_zero hs
    linarith
  calc volSwapFairStrike K s < Real.sqrt K * 1 :=
        mul_lt_mul_of_pos_left h1 (Real.sqrt_pos.2 hK)
    _ = Real.sqrt K := mul_one _

/-- **Volatility strike at the replicated variance strike.** The log-contract replication of the
variance swap gives fair variance strike `σ²` (`varianceSwap_fairStrike`:
`(2/T) · E[log(F/S_T) + (S_T − F)/F] = σ²`); evaluating the volatility strike there gives
`σ · exp(−s²/8)`, strictly below the volatility `σ` that the variance swap alone would suggest
when `s ≠ 0`. -/
theorem volSwapFairStrike_at_varianceSwap {S_0 : ℝ} (hS : 0 < S_0) (r σ T : ℝ) (hT : 0 < T)
    (hσ : 0 < σ) {s : ℝ} (hs : s ≠ 0) :
    volSwapFairStrike ((2 / T) * ∫ z, (Real.log ((S_0 * Real.exp (r * T)) /
              (S_0 * Real.exp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * z)))
         + (S_0 * Real.exp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * z)
              - S_0 * Real.exp (r * T)) / (S_0 * Real.exp (r * T))) ∂(gaussianReal 0 1)) s
      = σ * Real.exp (-(s ^ 2 / 8)) ∧
    σ * Real.exp (-(s ^ 2 / 8)) < σ := by
  rw [varianceSwap_fairStrike hS r σ T hT, volSwapFairStrike, Real.sqrt_sq hσ.le]
  refine ⟨rfl, ?_⟩
  have := volSwapFairStrike_lt_sqrt (K := σ ^ 2) (pow_pos hσ 2) hs
  rwa [volSwapFairStrike, Real.sqrt_sq hσ.le] at this

/-- **Value of the volatility swap under the `T`-forward measure.** For a constant bank account
`exp(r·T)`, let the annualized realized variance be lognormal (`VolSwapHyp`, mean `K`,
log-volatility `s`) under the `T`-forward measure `forwardMeasure Q (fun _ ↦ exp(r·T))`. The swap
pays `N · (√V − K_vol)` at `T`; its time-0 value under `Q`, `𝔼^Q[payoff / exp(r·T)]`, is
`exp(−r·T) · N · (volSwapFairStrike K s − K_vol)`: the deterministic discount factor times the
payoff at the fair strike. The lognormal law under the forward measure is an assumption. -/
theorem volSwapValue_forwardMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    [IsProbabilityMeasure Q] {r T K s : ℝ} {Z : Ω → ℝ}
    [IsProbabilityMeasure (forwardMeasure Q fun _ : Ω ↦ Real.exp (r * T))]
    (h : VolSwapHyp (forwardMeasure Q fun _ : Ω ↦ Real.exp (r * T)) K s Z) (N Kvol : ℝ) :
    ∫ ω, N * (Real.sqrt (bsTerminal K 0 s 1 (Z ω)) - Kvol) / Real.exp (r * T) ∂Q
      = Real.exp (-(r * T)) * (N * (volSwapFairStrike K s - Kvol)) := by
  have hP0 : 0 < ∫ _ : Ω, 1 / Real.exp (r * T) ∂Q := by
    simp [integral_const, Real.exp_pos]
  have hp := forwardMeasure_price (Q := Q) (B := fun _ : Ω ↦ Real.exp (r * T))
    (fun ω ↦ N * (Real.sqrt (bsTerminal K 0 s 1 (Z ω)) - Kvol)) measurable_const
    (fun _ ↦ Real.exp_pos _) hP0
  rw [← hp, integral_const_mul, integral_volSwapPayoff h Kvol]
  simp [integral_const, Real.exp_neg]

end MathFin
