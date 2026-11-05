/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.BlackScholes.PDE
public import MathFin.Foundations.NormalTail

/-!
# Continuous-monitoring floating-strike lookback option: Haug's closed form

The floating-strike lookback option's payoff at maturity is `S_T − m` (call, `m` the running
minimum of the path on `[0, T]`) or `M − S_T` (put, `M` the running maximum). This file
transcribes the continuous-monitoring closed form for its price — Goldman, Sosin & Gatto,
"Path Dependent Options: 'Buy at the Low, Sell at the High'", *J. Finance* 34(5) (1979),
1111–1127, in the cost-of-carry form of Haug, *The Complete Guide to Option Pricing Formulas*,
2nd ed. (2007), ch. 4, "Floating-Strike Lookback Options" — and proves a reduction of the
transcribed closed form to the already-built vanilla Black–Scholes call (`bsV`,
`BlackScholes/PDE.lean`).

Transcribed from QuantLib's `ql/pricingengines/lookback/analyticcontinuousfloatinglookback.cpp`
(`AnalyticContinuousFloatingLookbackEngine::A`, upstream commit `c547e0ae6`, 2026-10-22;
contributed 2006 by Warren Chou), which prices both the call (`η = 1`, strike floats at the
running minimum) and the put (`η = -1`, strike floats at the running maximum) from one formula.
The engine's own zero-carry handling (`|λ| < 1e-7`, upstream commit `060d87ef3`, "Price
continuous lookbacks when the carry is zero") is the true removable-singularity limit this file
does not transcribe — see the Scope section below and `lookbackFloatingPrice`'s own docstring.
With cost of carry `b = r − q`, `a₁ = bsd1 S m b σ T`, `a₂ = bsd2 S m b σ T`
(`BlackScholes/Call.lean`), the price is

  `η·[S·e^{−qT}·Φ(ηa₁) − m·e^{−rT}·Φ(ηa₂)
      + S·e^{−rT}·(σ²/2b)·((S/m)^{−2b/σ²}·Φ(η(−a₁ + 2b√T/σ)) − e^{bT}·Φ(−ηa₁))]`.

**Scope, disclosed honestly**: QuantLib's engine, and Haug's book, also give the **fixed-strike**
lookback closed form (`AnalyticContinuousFixedLookbackEngine`, Conze & Viswanathan 1991) and the
**partial-time** variants of both (Heynen & Kat 1994; Conze & Viswanathan's own partial case). The
fixed-strike engine is genuinely more involved — a two-way case split on the strike against the
running extremum per option type (`A(η) + C(η)` when the strike is on the extremum's side,
`B(η)` otherwise, QuantLib's `calculate()`) rather than the single formula transcribed here — and
the partial-time variants need the bivariate normal CDF's
correlated-window machinery (as in `PartialTimeBarrierOption.lean`). Neither is built in this
file. **This is also a transcription, not a derivation**: that the formula equals the discounted
expected lookback payoff needs the joint law of a drifted Brownian motion and its running
extremum (the reflection principle) — specifically, a closed form for that law linking it to
this file's `Φ`/power-function expression. `Lookback.lean` proves the static payoff bound
`max(S−K,0) ≤ max(M−K,0)` and its discounted-expectation form `bsV_le_lookbackCall` (valid for
*any* a.s.-dominating `M`, with `M`'s law unused); neither links to a closed form for the running
extremum's law, which is the piece this file's transcription route sidesteps.

## Main results

* `lookbackFloatingPrice`: the transcribed closed form (`η = 1` call, `η = -1` put).
* `lookbackFloatingCall_ge_bsV`: **the reduction**. With no dividend (`q = 0`, so `b = r`) and the
  running minimum already at or below the spot (`0 < m ≤ S`), the transcribed floating-strike
  call closed form is at least the vanilla Black–Scholes call struck at the running minimum:
  `bsV m r σ S T ≤ lookbackFloatingPrice 1 S m r 0 σ T`. This is proved directly from the
  transcribed closed form (not via any payoff-dominance argument), by isolating the one term that
  could break the bound — `(S/m)^{−2r/σ²}·Φ(−a₁ + 2r√T/σ) − e^{rT}·Φ(−a₁)`, the term with a
  removable singularity at `r = 0` — and showing it always has the same sign as `r`, via a
  Mills-ratio monotonicity argument reusing `neg_mul_Phi_le_gaussianPDFReal`
  (`Foundations/NormalTail.lean`) in a new role: there it bounds a normal tail, here it supplies a
  derivative sign. **Not a counterpart of `Lookback.lean`'s `lookback_payoff_ge_vanilla`**: that
  lemma is a same-strike fixed-strike statement (`max(S−K,0) ≤ max(M−K,0)` given `S ≤ M`, the
  running *maximum*); this theorem is a floating-strike statement about the running *minimum*,
  with no `max(·,0)` on either side, proved independently. The two share only the theme that a
  lookback value dominates a vanilla one, not a derivation route or a payoff identity.
-/

@[expose] public section

namespace MathFin

open Real Filter Topology ProbabilityTheory
open scoped NNReal

/-- **Floating-strike lookback price**, Haug's cost-of-carry closed form (`b = r − q`),
transcribed from QuantLib's `AnalyticContinuousFloatingLookbackEngine::A`. `η = 1` is the call
(`m` the running minimum), `η = -1` the put (`m` the running maximum). Defined for every `b`; at
`b = 0` the `σ²/(2b)` factor is `0` by Lean's convention (a different value from the true
removable-singularity limit, which this file does not compute). -/
noncomputable def lookbackFloatingPrice (η S m r q σ T : ℝ) : ℝ :=
  η * (S * Real.exp (-q * T) * Phi (η * bsd1 S m (r - q) σ T) -
    m * Real.exp (-r * T) * Phi (η * bsd2 S m (r - q) σ T) +
    S * Real.exp (-r * T) * (σ ^ 2 / (2 * (r - q))) *
      ((S / m) ^ (-(2 * (r - q) / σ ^ 2)) *
          Phi (η * (-bsd1 S m (r - q) σ T + 2 * (r - q) * Real.sqrt T / σ)) -
        Real.exp ((r - q) * T) * Phi (-η * bsd1 S m (r - q) σ T)))

/-! ### The tilt-gap: isolating the one term that needs a sign argument -/

/-- **The exponential-tilt gap** `h(k, d) = e^{k²/2 − kd}·Φ(k − d) − Φ(−d)`. This is the
carry term of `lookbackFloatingPrice`, rewritten on `(k, d)` coordinates with `k` the dimensionless
carry `2r√T/σ` and `d` the zero-carry `a₁`; `h(0, d) = 0`, and the headline reduction needs only
that `h(k, d)` has the same sign as `k`. -/
noncomputable def lookbackTiltGap (k d : ℝ) : ℝ :=
  Real.exp (k ^ 2 / 2 - k * d) * Phi (k - d) - Phi (-d)

@[simp] theorem lookbackTiltGap_zero (d : ℝ) : lookbackTiltGap 0 d = 0 := by
  simp [lookbackTiltGap]

/-- `∂/∂k h(k, d) = e^{k²/2−kd}·[(k−d)·Φ(k−d) + φ(k−d)]`. -/
theorem hasDerivAt_lookbackTiltGap (d k : ℝ) :
    HasDerivAt (lookbackTiltGap · d)
      (Real.exp (k ^ 2 / 2 - k * d) * ((k - d) * Phi (k - d) + gaussianPDFReal 0 1 (k - d))) k := by
  have hlin : HasDerivAt (fun x : ℝ ↦ x - d) 1 k := (hasDerivAt_id k).sub_const d
  have h1 : HasDerivAt (fun x : ℝ ↦ x ^ 2 / 2 - x * d) (k - d) k := by
    have h1' := (hasDerivAt_pow 2 k).div_const 2 |>.sub ((hasDerivAt_id k).mul_const d)
    simp only [id] at h1'
    norm_num at h1'
    exact h1'
  have hexp : HasDerivAt (fun x : ℝ ↦ Real.exp (x ^ 2 / 2 - x * d))
      (Real.exp (k ^ 2 / 2 - k * d) * (k - d)) k := h1.exp
  have hPhi : HasDerivAt (fun x : ℝ ↦ Phi (x - d)) (gaussianPDFReal 0 1 (k - d)) k := by
    have h := (hasDerivAt_Phi (k - d)).comp k hlin
    simp only [mul_one] at h
    exact h
  have h := hexp.mul hPhi
  have hfun : (lookbackTiltGap · d) = fun x : ℝ ↦
      Real.exp (x ^ 2 / 2 - x * d) * Phi (x - d) - Phi (-d) := rfl
  rw [hfun]
  have hfinal := h.sub_const (Phi (-d))
  rw [show Real.exp (k ^ 2 / 2 - k * d) * (k - d) * Phi (k - d) +
      Real.exp (k ^ 2 / 2 - k * d) * gaussianPDFReal 0 1 (k - d) =
      Real.exp (k ^ 2 / 2 - k * d) * ((k - d) * Phi (k - d) + gaussianPDFReal 0 1 (k - d))
      from by ring] at hfinal
  exact hfinal

/-- **`h(·, d)` is monotone**: its derivative `e^{k²/2−kd}·[(k−d)Φ(k−d) + φ(k−d)]` is nonnegative
everywhere, since `xΦ(x) + φ(x) ≥ 0` for every `x`
(`neg_mul_Phi_le_gaussianPDFReal`, rearranged). -/
theorem monotone_lookbackTiltGap (d : ℝ) : Monotone (lookbackTiltGap · d) := by
  apply monotone_of_deriv_nonneg
  · exact fun k ↦ (hasDerivAt_lookbackTiltGap d k).differentiableAt
  · intro k
    rw [(hasDerivAt_lookbackTiltGap d k).deriv]
    have hmills := neg_mul_Phi_le_gaussianPDFReal (k - d)
    have hnn : 0 ≤ (k - d) * Phi (k - d) + gaussianPDFReal 0 1 (k - d) := by linarith
    exact mul_nonneg (Real.exp_pos _).le hnn

/-- **`h(k, d)` has the same sign as `k`**, for any positive rescaling: if `k = x·r` with `0 < x`,
then `0 ≤ r·h(k, d)`. This is the sign fact the headline reduction needs, with `x = 2√T/σ` and
`r` the risk-free rate. -/
theorem lookbackTiltGap_mul_self_sign {x r k d : ℝ} (hx : 0 < x) (hk : k = x * r) :
    0 ≤ r * lookbackTiltGap k d := by
  rcases le_or_gt 0 r with hr | hr
  · have hk0 : 0 ≤ k := hk ▸ mul_nonneg hx.le hr
    have hmono := monotone_lookbackTiltGap d hk0
    simp only [lookbackTiltGap_zero] at hmono
    exact mul_nonneg hr hmono
  · have hk0 : k ≤ 0 := hk ▸ mul_nonpos_of_nonneg_of_nonpos hx.le hr.le
    have hmono := monotone_lookbackTiltGap d hk0
    simp only [lookbackTiltGap_zero] at hmono
    have h1 : 0 ≤ -r := by linarith
    have h2 : 0 ≤ -lookbackTiltGap k d := by linarith
    nlinarith [mul_nonneg h1 h2]

/-! ### The headline reduction -/

/-- **The floating-strike lookback call closed form dominates the vanilla call struck at the
running minimum**, with no dividend (`q = 0`, so `b = r`). Informally: the floating lookback
call's payoff `S_T − min` dominates the vanilla call payoff `max(S_T − m, 0)` once the running
minimum so far is `m` (future lows can only lower `min` further, never raise it above `m`), so the
price inequality is the expected direction — but the proof below does not go through that payoff
argument (the library has no construction of the running minimum's law to take expectations
against); it is a direct algebraic argument from the transcribed closed form. This is **not** a
counterpart of `lookback_payoff_ge_vanilla` (`Lookback.lean`), which is a different, same-strike
statement about the running *maximum* (`max(S−K,0) ≤ max(M−K,0)` given `S ≤ M`) — the two share
only the theme that a lookback value dominates a vanilla one. **At `r = 0`**
`lookbackFloatingPrice`'s `σ²/(2r)` factor takes Lean's division-by-zero value `0`, so the two
sides coincide exactly (the inequality's gap is `0`, not a genuine strict comparison); this says
nothing about the true zero-carry limit, which `lookbackFloatingPrice` does not compute (see its
own docstring). The ordering hypothesis `hS : m ≤ S` is the economically meaningful regime (the
running minimum is at most the current spot) but is not needed by the algebra below, which only
uses `0 < S` (`hSpos`, derived from `hm`/`hS`) and would equally go through with `hSpos` as a
direct hypothesis. -/
theorem lookbackFloatingCall_ge_bsV {S m r σ T : ℝ} (hm : 0 < m) (hS : m ≤ S) (hσ : 0 < σ)
    (hT : 0 < T) :
    bsV m r σ S T ≤ lookbackFloatingPrice 1 S m r 0 σ T := by
  have hSpos : 0 < S := hm.trans_le hS
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 < t ∧ T = t ^ 2 :=
    ⟨Real.sqrt T, Real.sqrt_pos.mpr hT, (Real.sq_sqrt hT.le).symm⟩
  set a1 : ℝ := bsd1 S m r σ (t ^ 2) with ha1_def
  set k : ℝ := 2 * r * t / σ with hk_def
  have hden : σ * t ≠ 0 := (mul_pos hσ ht).ne'
  have hlog : Real.log (S / m) = a1 * (σ * t) - (r + σ ^ 2 / 2) * t ^ 2 := by
    rw [ha1_def, bsd1, Real.sqrt_sq ht.le]
    field_simp
    ring
  have hSm : 0 < S / m := div_pos hSpos hm
  have hpow : (S / m) ^ (-(2 * r / σ ^ 2)) =
      Real.exp (r * t ^ 2) * Real.exp (k ^ 2 / 2 - k * a1) := by
    rw [Real.rpow_def_of_pos hSm, hlog, ← Real.exp_add]
    congr 1
    rw [hk_def]
    field_simp
    ring
  have hcarry : (lookbackFloatingPrice 1 S m r 0 σ (t ^ 2)) - bsV m r σ S (t ^ 2) =
      S * (σ ^ 2 / (2 * r)) * lookbackTiltGap k a1 := by
    have hexpne : Real.exp (r * t ^ 2) ≠ 0 := (Real.exp_pos _).ne'
    simp only [lookbackFloatingPrice, bsV, sub_zero, Real.exp_zero, mul_one, neg_zero, zero_mul,
      one_mul, Real.sqrt_sq ht.le, neg_mul, Real.exp_neg, ← hk_def, ← ha1_def, lookbackTiltGap]
    rw [show (-a1 + k : ℝ) = k - a1 from by ring, hpow]
    field_simp
    ring
  rcases eq_or_ne r 0 with hr0 | hr0
  · have : lookbackFloatingPrice 1 S m r 0 σ (t ^ 2) - bsV m r σ S (t ^ 2) = 0 := by
      rw [hcarry, hr0]
      simp
    linarith
  · have hsign : 0 ≤ r * lookbackTiltGap k a1 :=
      lookbackTiltGap_mul_self_sign (x := 2 * t / σ) (by positivity) (by rw [hk_def]; ring)
    have hr2 : 0 < r ^ 2 := by positivity
    have hcoeff : S * (σ ^ 2 / (2 * r)) * lookbackTiltGap k a1 =
        S * (σ ^ 2 / (2 * r ^ 2)) * (r * lookbackTiltGap k a1) := by
      field_simp
    have hnn : 0 ≤ S * (σ ^ 2 / (2 * r)) * lookbackTiltGap k a1 := by
      rw [hcoeff]
      have : 0 < S * (σ ^ 2 / (2 * r ^ 2)) := by positivity
      exact mul_nonneg this.le hsign
    linarith [hcarry]

end MathFin
