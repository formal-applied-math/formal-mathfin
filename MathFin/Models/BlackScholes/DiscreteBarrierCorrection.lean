/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

public import MathFin.Models.BlackScholes.BarrierParity
public import MathFin.Models.BlackScholes.DividendsGreeks
public import MathFin.Models.BlackScholes.PartialTimeBarrierOption
public import MathFin.Models.BlackScholes.ScalingInvariance

/-!
# Broadie–Glasserman–Kou barrier shift for discretely monitored barrier options

A barrier option monitored only at `m` equally spaced dates (`Δt = T/m`) is worth more than the
continuously monitored one, for a knock-out, because paths can cross the barrier between dates
and return. Broadie, Glasserman and Kou ([BroadieGlassermanKou1997]) give a correction: the
discretely monitored price is approximated by the continuously monitored price with the
barrier moved **away from the spot** by the factor `exp(± β σ √Δt)`, where
`β = −ζ(1/2)/√(2π) ≈ 0.5826` and `ζ` is Riemann's zeta function. The value of `β` is not
proved here: every theorem below is stated for an arbitrary shift constant `β`.

The statement for a down-and-out call with barrier `B` is
`V_d(S, t; B) = V_cont(S, t; B e^{−βσ√(T/N)}) + (an error term)`, as restated in
[HowisonSteinberg2005], §1, which cites [BroadieGlassermanKou1997]. The BGK paper is neither
reproduced nor derived here.

This file takes that shift as a **definition** and proves what follows from the definition alone.
The scaling theorems are identities of closed forms (the time-volatility rescaling for `c > 0`,
the spatial homogeneity for every real `c`): they hold at every input, including the junk
corners (division by zero, `√` of a negative, `log` of a nonpositive), because both sides are the
same expression of the junk value, up to the factor `c` for the homogeneity statement, and they
are not claims that the value is a price. A price needs `σ > 0`, `0 < T`, `0 < S, K, H`, a
(shifted) barrier at most `K` and spot above it (and `1 ≤ m` for the BGK expression); at `H = 0`,
for instance, `ptDownOutCall` is a junk value. The theorems that consume positivity state it.
The continuous down-and-out call is the library's `ptDownOutCall`
(`PartialTimeBarrierOption.lean`, the full-life branch with `X ≥ H`) at cost of carry `b = r`;
no second closed form is introduced. Its image form
`V(S) − (H/S)^{2r/σ²−1} · V(H²/S)`, with `V` the Black–Scholes call price `bsV`, is the
reciprocal-ratio form of the display `V(S) − (S/B)^{1−2(r−q)/σ²} V(B²/S)` of
[HowisonSteinberg2005], §2 (unnumbered, restated as eq. (7) in §3.7), for a strike above the
barrier `B = H` and with a dividend yield `q`; the printed ratio with dividend yield `q` is
`ptDownOutCall_eq_image_printed`, and its `q = 0` case, reciprocated, is
`ptDownOutCall_eq_image`. Lean proves that the image form equals `ptDownOutCall`, the transcribed
Haug (2007) / Reiner–Rubinstein form ([Haug2007], ch. 4; [ReinerRubinstein1991]; see also [Hull]
for the barrier formulas in `q` and in/out form) for a strike above the barrier. That
`ptDownOutCall` is that formula is a matter of transcription, not proved in Lean.

## Main definitions

* `bgkDownBarrier`, `bgkUpBarrier`: the shifted barriers `H e^{∓βσ√(T/m)}`; the up-barrier shift
  `bgkUpBarrier` is defined without a price (no up-and-out closed form in this library).
* `bgkDownOutCall`: `ptDownOutCall` at the shifted down barrier, the BGK approximation to the
  discretely monitored down-and-out call. It reads as a price only for `σ > 0`, `0 < T`,
  `1 ≤ m`, `0 < S, K, H`, a shifted barrier at most `K` and spot above it.
* `bgkKnockIn`: the BGK knock-in expression, the vanilla price `bsV` minus `bgkDownOutCall`. It
  reads as the down-and-in price only under the conditions of `bgkDownOutCall`; at `H = 0` it is
  `bsV`, a junk value (a zero barrier never knocks in).

## Main results

* `bgkDownOutCall_zero_barrier`, `bgkKnockIn_zero_barrier`: at `H = 0` the BGK expression is the
  junk value `0` (by `ptDownOutCall_zero_barrier`), and the BGK knock-in is the vanilla `bsV`.
* The facts about `ptDownOutCall` itself (image form, zero barrier, spatial and time scaling,
  continuity in the barrier) are in `PartialTimeBarrierOption.lean`.
* `bgkDownBarrier_timeScale`, `bgkDownOutCall_timeScale`: the shift `σ√(T/m)` is fixed by the same
  scaling at fixed `m` (`Δt ↦ Δt/c`), so the BGK expression is as well.
* `tendsto_bgkDownBarrier`: the shifted barrier tends to `H` as the number of dates `m → ∞`.
* `tendsto_bgkDownOutCall`: as `m → ∞` the BGK expression tends to `ptDownOutCall` at `H`.
* `abs_knockIn_sub_bgkKnockIn_le`: a linear rearrangement of in–out parity
  (`knockIn_add_knockOut_eq_bsV`), for an arbitrary measurable event `A`: a bound on the error of
  the BGK knock-out expression against a knock-out value transfers to the knock-in. It does not
  link `A` to `H` or the monitoring dates.

## Scope

The accuracy of the shift as an approximation to the discretely monitored price is **not**
proved here. Howison and Steinberg themselves note that the accuracy of BGK's statement, as
written, is limited ([HowisonSteinberg2005], §1). Nothing here is a model of discrete monitoring:
the discretely monitored value never appears, except as the hypothesised benchmark in
`abs_knockIn_sub_bgkKnockIn_le`. Neither is `ptDownOutCall` proved to be a price (the
reflection-principle step is not derived). The library's discretely monitored objects
(`Contracts.upAndIn` and `Contracts.upAndInPayoff` in `Contracts/Instruments/Options.lean`,
priced in `Models/Binomial/BarrierMarket.lean`) are not connected here: this module is closed-form
only.

## References

* [M. Broadie, P. Glasserman, S. Kou, *A continuity correction for discrete barrier
  options*][BroadieGlassermanKou1997]
* [S. Howison, M. Steinberg, *A matched asymptotic expansions approach to continuity corrections
  for discretely sampled options. Part 1: barrier options*][HowisonSteinberg2005], §1, §2 and §3.7
* [E. G. Haug, *The Complete Guide to Option Pricing Formulas*][Haug2007] (2nd ed., 2007), ch. 4
* [E. Reiner and M. Rubinstein, *Breaking down the barriers*][ReinerRubinstein1991]
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], ch. 26

## Tags

barrier option, discrete monitoring, continuity correction, down-and-out call,
Broadie–Glasserman–Kou, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open Filter Topology

/-- The shifted barrier of a down option, `H · exp(−β σ √(T/m))`. It is `H` at `m = 0` and for
`T ≤ 0`, where `T / m` or its square root is a junk value. -/
noncomputable def bgkDownBarrier (β : ℝ) (m : ℕ) (H σ T : ℝ) : ℝ :=
  H * Real.exp (-(β * σ * Real.sqrt (T / m)))

/-- The shifted barrier of an up option, `H · exp(β σ √(T/m))`. It is `H` at `m = 0` and for
`T ≤ 0`. -/
noncomputable def bgkUpBarrier (β : ℝ) (m : ℕ) (H σ T : ℝ) : ℝ :=
  H * Real.exp (β * σ * Real.sqrt (T / m))

/-- The **BGK approximation** to the discretely monitored down-and-out call with `m` equally
spaced monitoring dates: `ptDownOutCall` at the shifted barrier `bgkDownBarrier`. It reads as a
price only for `σ > 0`, `0 < T`, `1 ≤ m`, `0 < S, K, H`, the shifted barrier at most `K` and the
spot above it (for an arbitrary `β` with `β σ < 0` the shifted barrier lies above `H`, so
`H ≤ K` alone does not suffice). At `H = 0` the shifted barrier is `0`, `log (0 / S) = 0`, and
`ptDownOutCall` is a junk value, not the vanilla price. The accuracy of the shift is not proved
here. -/
noncomputable def bgkDownOutCall (β : ℝ) (m : ℕ) (K H r σ S T : ℝ) : ℝ :=
  ptDownOutCall S K (bgkDownBarrier β m H σ T) r r σ T

/-- The BGK knock-in expression: the Black–Scholes vanilla call price minus `bgkDownOutCall`. It
reads as the down-and-in price only under the conditions of `bgkDownOutCall` (`σ > 0`, `0 < T`,
`0 < S, K, H`, shifted barrier at most `K` and below the spot, `1 ≤ m`); at `H = 0` it is `bsV`, a
junk value, not `0`. -/
noncomputable def bgkKnockIn (β : ℝ) (m : ℕ) (K H r σ S T : ℝ) : ℝ :=
  bsV K r σ S T - bgkDownOutCall β m K H r σ S T

/-- **Zero barrier is a junk corner.** At `H = 0` the shifted barrier is `0` and `bgkDownOutCall`
is the junk value `0` of `ptDownOutCall_zero_barrier`, not the vanilla price. -/
theorem bgkDownOutCall_zero_barrier {β : ℝ} {m : ℕ} {K r σ S T : ℝ} :
    bgkDownOutCall β m K 0 r σ S T = 0 := by
  simp [bgkDownOutCall, bgkDownBarrier, ptDownOutCall_zero_barrier]

/-- **Zero barrier is a junk corner for the knock-in.** At `H = 0` the BGK knock-in expression is
the whole vanilla price `bsV`, whereas a down-and-in call with a zero barrier never knocks in and is
worth `0`; the value is a junk value. -/
theorem bgkKnockIn_zero_barrier {β : ℝ} {m : ℕ} {K r σ S T : ℝ} :
    bgkKnockIn β m K 0 r σ S T = bsV K r σ S T := by
  simp [bgkKnockIn, bgkDownOutCall_zero_barrier]

/-- The shifted down barrier is unchanged under `(σ, T) ↦ (σ √c, T / c)` with `m` fixed: the
monitoring step becomes `Δt / c` and the shift `σ √Δt` is invariant. -/
theorem bgkDownBarrier_timeScale {β : ℝ} {m : ℕ} {H σ T c : ℝ} (hc : 0 < c) :
    bgkDownBarrier β m H (σ * Real.sqrt c) (T / c) = bgkDownBarrier β m H σ T := by
  unfold bgkDownBarrier
  rw [mul_assoc β, mul_assoc β, div_right_comm, vol_sqrt_timeScale hc]

/-- The BGK expression is unchanged under `(r, σ, T) ↦ (c r, σ √c, T / c)` with the number of
dates `m` fixed, so it is invariant under the same scaling that fixes `σ² T` and `r T`. -/
theorem bgkDownOutCall_timeScale {β : ℝ} {m : ℕ} {K H r σ S T c : ℝ} (hc : 0 < c) :
    bgkDownOutCall β m K H (c * r) (σ * Real.sqrt c) S (T / c)
      = bgkDownOutCall β m K H r σ S T := by
  unfold bgkDownOutCall
  rw [bgkDownBarrier_timeScale hc, ptDownOutCall_timeScale hc]

/-! ### The limit of many monitoring dates -/

/-- The shifted barrier tends to `H` as the number of dates grows. -/
theorem tendsto_bgkDownBarrier (β H σ T : ℝ) :
    Tendsto (fun m : ℕ ↦ bgkDownBarrier β m H σ T) atTop (𝓝 H) := by
  have h0 : Tendsto (fun m : ℕ ↦ T / (m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat T
  have hs : Tendsto (fun m : ℕ ↦ Real.sqrt (T / (m : ℝ))) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h0
    rwa [Real.sqrt_zero] at this
  have he : Tendsto (fun m : ℕ ↦ Real.exp (-(β * σ * Real.sqrt (T / (m : ℝ))))) atTop
      (𝓝 1) := by
    have := (Real.continuous_exp.tendsto _).comp (hs.const_mul (β * σ)).neg
    rwa [mul_zero, neg_zero, Real.exp_zero] at this
  have := he.const_mul H
  rwa [mul_one] at this

/-- **Many-dates limit.** As `m → ∞` the expression `bgkDownOutCall` tends to `ptDownOutCall` at
the unshifted barrier, for nonzero spot and barrier, at every strike, rate, volatility and
maturity, with no rate of convergence in `m` (the proof consumes only `S ≠ 0` and `H ≠ 0`, so it
also covers the junk values `σ = 0`, `T ≤ 0`). It reads as "the BGK approximation tends to the
continuous price" only for `σ > 0`, `0 < T`, positive `S, K, H` and `1 ≤ m`, with the shifted
barrier at most `K` and below the spot (true for all large `m` when `H < K` and `S > H`). The
hypotheses `S ≠ 0` and `H ≠ 0` keep the statement off the junk corners (at `H = 0` the closed
form is the junk constant `0`, so continuity in the barrier fails wherever the vanilla value is
nonzero, in particular on the price domain); the proof uses both. It is the consistency of the
shift with the continuous limit, not an accuracy result. -/
theorem tendsto_bgkDownOutCall {β K H r σ S T : ℝ} (hS : S ≠ 0) (hH : H ≠ 0) :
    Tendsto (fun m : ℕ ↦ bgkDownOutCall β m K H r σ S T) atTop
      (𝓝 (ptDownOutCall S K H r r σ T)) :=
  (continuousAt_ptDownOutCall_barrier hS hH).tendsto.comp (tendsto_bgkDownBarrier β H σ T)

/-! ### Connection to in–out parity -/

/-- **Error transfer through in–out parity.** Under the Black–Scholes lognormal hypothesis, let
the knock-out and knock-in calls for a measurable barrier event `A` be the contracts that pay
`𝟙_{Aᶜ} · f` and `𝟙_A · f` at time `0` (`Contract.value`, as in `knockOutValue`, `knockInValue`),
with `f` the call payoff and discount factor `e^{−rT}`. If the BGK knock-out expression is within
`ε` of the knock-out value (for example `A` the event that some monitoring date has the price at
or below the barrier, taken as a hypothesis), then the BGK knock-in expression is within `ε` of
the knock-in value: `knockIn + knockOut = bsV` (`knockIn_add_knockOut_eq_bsV`) and
`bgkKnockIn = bsV − bgkDownOutCall`. This is a linear rearrangement of in–out parity with `A`
arbitrary, not tied to `H` or to the monitoring dates; the BGK accuracy claim enters only as the
hypothesis and is not proved. -/
theorem abs_knockIn_sub_bgkKnockIn_le {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure Q]
    {S K r σ T : ℝ} {Z : Ω → ℝ} (h : BSCallHyp Q S K r σ T Z) {A : Set Ω}
    (hA : MeasurableSet A) {β : ℝ} {m : ℕ} {H ε : ℝ}
    (hout : |(Contracts.Contract.pay 0 (Contracts.Payoff.obs () 0)).value Q
        (fun _ _ ↦ Real.exp (-r * T))
        (fun _ _ ↦ Aᶜ.indicator (fun ω ↦ max (bsTerminal S r σ T (Z ω) - K) 0))
        - bgkDownOutCall β m K H r σ S T| ≤ ε) :
    |(Contracts.Contract.pay 0 (Contracts.Payoff.obs () 0)).value Q
        (fun _ _ ↦ Real.exp (-r * T))
        (fun _ _ ↦ A.indicator (fun ω ↦ max (bsTerminal S r σ T (Z ω) - K) 0))
        - bgkKnockIn β m K H r σ S T| ≤ ε := by
  rw [← discountedValue_eq_contract_value] at hout ⊢
  have hp := knockIn_add_knockOut_eq_bsV h hA
  unfold knockInValue knockOutValue at hp
  have : discountedValue (Real.exp (-r * T)) Q
        (A.indicator fun ω ↦ max (bsTerminal S r σ T (Z ω) - K) 0) - bgkKnockIn β m K H r σ S T
      = -(discountedValue (Real.exp (-r * T)) Q
        (Aᶜ.indicator fun ω ↦ max (bsTerminal S r σ T (Z ω) - K) 0)
        - bgkDownOutCall β m K H r σ S T) := by
    unfold bgkKnockIn
    linarith
  rw [this, abs_neg]
  exact hout

end MathFin
