/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.BlackScholes.BarrierParity
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
[HowisonSteinberg2005], §1, which cites [BroadieGlassermanKou1997] and itself flags the accuracy
of the statement as limited. The BGK paper is neither reproduced nor derived here.

This file takes that shift as a **definition** and proves what follows from the definition alone.
The continuous down-and-out call is the library's `ptDownOutCall`
(`PartialTimeBarrierOption.lean`, the full-life branch with `X ≥ H`) at cost of carry `b = r`;
no second closed form is introduced. Its image form
`V(S) − (H/S)^{2r/σ²−1} · V(H²/S)`, with `V` the Black–Scholes call price `bsV`, is the
reciprocal-ratio form of the display `V(S) − (S/B)^{1−2(r−q)/σ²} V(B²/S)` of
[HowisonSteinberg2005], §2 (unnumbered, restated as eq. (7) in §3.7), for a strike above the
barrier `B = H` and with a dividend yield `q`; the case here is `q = 0`. Lean proves that the
image form equals `ptDownOutCall`, the transcribed Reiner–Rubinstein form
([ReinerRubinstein1991]; see also [Hull]) for a strike above the barrier. That `ptDownOutCall` is
the Reiner–Rubinstein/Hull formula is a matter of transcription, not proved in Lean.

## Main definitions

* `bgkDownBarrier`, `bgkUpBarrier`: the shifted barriers `H e^{∓βσ√(T/m)}`.
* `bgkDownOutCall`: `ptDownOutCall` at the shifted down barrier, the BGK approximation to the
  discretely monitored down-and-out call. It reads as a price only when the closed form does
  (`ptDownOutCall`: shifted barrier at most `K`, spot above it). There is no up-and-out closed
  form in this library, so only the up-barrier shift is defined.
* `bgkKnockIn`: the BGK knock-in expression, the vanilla price `bsV` minus `bgkDownOutCall`.

## Main results

* `ptDownOutCall_eq_image`: `ptDownOutCall S K H r r σ T` is the image form
  `bsV K r σ S T − (H/S)^{2r/σ²−1} · bsV K r σ (H²/S) T`, for positive `S, K, H, σ`.
* `ptDownOutCall_scale`: spatial homogeneity, `(S, K, H) ↦ c(S, K, H)` scales it by `c`, at any
  carry.
* `ptDownOutCall_timeScale`: it is unchanged under `(b, r, σ, T) ↦ (c b, c r, σ√c, T/c)`, which
  fixes `σ²T`, `rT` and `σ√T` (via `bsd1_scale`, `bsd1_timeScale` in `ScalingInvariance.lean`).
* `bgkDownBarrier_timeScale`, `bgkDownOutCall_timeScale`: the shift `σ√(T/m)` is fixed by the same
  scaling at fixed `m` (`Δt ↦ Δt/c`), so the BGK expression is as well.
* `continuousAt_ptDownOutCall_barrier`: `ptDownOutCall` is continuous in the barrier at every
  nonzero barrier, for nonzero spot.
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
reflection-principle step is not derived).

## References

* [M. Broadie, P. Glasserman, S. Kou, *A continuity correction for discrete barrier
  options*][BroadieGlassermanKou1997]
* [S. Howison, M. Steinberg, *A matched asymptotic expansions approach to continuity corrections
  for discretely sampled options. Part 1: barrier options*][HowisonSteinberg2005], §1 and §2
* [E. Reiner and M. Rubinstein, *Breaking down the barriers*][ReinerRubinstein1991]
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull] (10th ed., Pearson, 2018), ch. 26

## Tags

barrier option, discrete monitoring, continuity correction, down-and-out call,
Broadie–Glasserman–Kou, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open Filter Topology

/-- **Image form of the full-life down-and-out closed form.** For positive spot, strike, barrier
and volatility, `ptDownOutCall S K H r r σ T` (the transcribed Reiner–Rubinstein full-life
down-and-out call, `X ≥ H` branch, at cost of carry `b = r`) equals
`V(S) − (H/S)^{2r/σ²−1} · V(H²/S)` with `V = bsV`, equivalently the form of [HowisonSteinberg2005],
§2 (restated as eq. (7) in §3.7) with the ratio reciprocated. The exponent `2r/σ² − 1` is
`2 · ptMu r σ`, the term `(H/S)^{2r/σ²−1} · (H²/S)` is `S · ptHSmu1`, and `d₁, d₂` at `H²/S` are
`ptF1, ptF2`. An identity between two closed forms; neither is proved here to be a price. -/
theorem ptDownOutCall_eq_image {K H r σ S T : ℝ} (hS : 0 < S) (hK : 0 < K)
    (hH : 0 < H) (hσ : 0 < σ) :
    ptDownOutCall S K H r r σ T
      = bsV K r σ S T - (H / S) ^ (2 * r / σ ^ 2 - 1) * bsV K r σ (H ^ 2 / S) T := by
  have hHS : 0 < H / S := div_pos hH hS
  have hσ2 : σ ^ 2 ≠ 0 := by positivity
  have hmu : 2 * ptMu r σ = 2 * r / σ ^ 2 - 1 := by
    unfold ptMu hkMu; field_simp
  have h0 : ptHSmu S H r σ = (H / S) ^ (2 * r / σ ^ 2 - 1) := by
    rw [ptHSmu, Real.rpow_def_of_pos hHS, hmu, mul_comm]
  have h1 : ptHSmu1 S H r σ = ptHSmu S H r σ * (H / S) ^ 2 := by
    have : 2 * (ptMu r σ + 1) * Real.log (H / S)
        = 2 * ptMu r σ * Real.log (H / S) + (Real.log (H / S) + Real.log (H / S)) := by ring
    rw [ptHSmu1, this, Real.exp_add, Real.exp_add, Real.exp_log hHS, ← ptHSmu, sq]
  have hsq : H ^ 2 / S = S * (H / S) ^ 2 := by field_simp
  have hf1 : ptF1 S K H r σ T = bsd1 (H ^ 2 / S) K r σ T := by
    unfold ptF1 bsd1
    congr 2
    rw [Real.log_div hS.ne' hK.ne', Real.log_div (by positivity) hK.ne',
      Real.log_div hH.ne' hS.ne', Real.log_div (by positivity) hS.ne', Real.log_pow]
    push_cast; ring
  have hf2 : ptF2 S K H r σ T = bsd2 (H ^ 2 / S) K r σ T := by
    rw [ptF2, bsd2, hf1]
  symm
  unfold ptDownOutCall bsV
  rw [← h0, ← hf1, ← hf2, h1]
  nth_rewrite 1 [hsq]
  simp only [ptD1, ptD2, sub_self, zero_mul, Real.exp_zero, neg_mul]
  ring

/-- Spatial homogeneity of the closed form: scaling spot, strike and barrier by `c > 0` scales
`ptDownOutCall` by `c`, at any cost of carry `b`. -/
theorem ptDownOutCall_scale {K H b r σ S T c : ℝ} (hc : 0 < c) :
    ptDownOutCall (c * S) (c * K) (c * H) b r σ T = c * ptDownOutCall S K H b r σ T := by
  simp only [ptDownOutCall, ptD1, ptD2, ptF1, ptF2, ptHSmu, ptHSmu1, bsd1_scale hc,
    bsd2_scale hc, mul_div_mul_left _ _ hc.ne']
  ring

/-- The closed form is unchanged under `(b, r, σ, T) ↦ (c b, c r, σ √c, T / c)` for `c > 0`, at
any cost of carry `b`: the quantities `(b - r) T`, `r T`, `σ √T`, `(b + σ²/2) T` and
`(b - σ²/2) / σ²` are all fixed. -/
theorem ptDownOutCall_timeScale {K H b r σ S T c : ℝ} (hc : 0 < c) :
    ptDownOutCall S K H (c * b) (c * r) (σ * Real.sqrt c) (T / c)
      = ptDownOutCall S K H b r σ T := by
  have hsq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  have hv : Real.sqrt (T / c) = Real.sqrt T / Real.sqrt c := Real.sqrt_div' T hc.le
  have hden : σ * Real.sqrt c * Real.sqrt (T / c) = σ * Real.sqrt T := by
    rw [hv]; field_simp [(Real.sqrt_pos.2 hc).ne']
  have hnum : (c * b + (σ * Real.sqrt c) ^ 2 / 2) * (T / c) = (b + σ ^ 2 / 2) * T := by
    rw [mul_pow, hsq]; field_simp
  have hmu : ptMu (c * b) (σ * Real.sqrt c) = ptMu b σ := by
    unfold ptMu hkMu
    rw [mul_pow, hsq]
    rcases eq_or_ne σ 0 with h | h
    · simp [h]
    · field_simp
  have hF : ptF1 S K H (c * b) (σ * Real.sqrt c) (T / c) = ptF1 S K H b σ T := by
    unfold ptF1; rw [hnum, hden]
  have hF2 : ptF2 S K H (c * b) (σ * Real.sqrt c) (T / c) = ptF2 S K H b σ T := by
    unfold ptF2; rw [hF, hden]
  have e1 : (c * b - c * r) * (T / c) = (b - r) * T := by field_simp
  have e2 : -(c * r) * (T / c) = -r * T := by field_simp
  have hD : ∀ Y, ptD1 S Y (c * b) (σ * Real.sqrt c) (T / c) = ptD1 S Y b σ T :=
    fun Y => bsd1_timeScale hc
  have hD2 : ∀ Y, ptD2 S Y (c * b) (σ * Real.sqrt c) (T / c) = ptD2 S Y b σ T :=
    fun Y => bsd2_timeScale hc
  simp only [ptDownOutCall, ptHSmu, ptHSmu1, hmu, hF, hF2, hD, hD2, e1, e2]

/-- The shifted barrier of a down option, `H · exp(−β σ √(T/m))`. It is `H` at `m = 0` and for
`T < 0`, where `T / m` or its square root is a junk value. -/
noncomputable def bgkDownBarrier (β : ℝ) (m : ℕ) (H σ T : ℝ) : ℝ :=
  H * Real.exp (-(β * σ * Real.sqrt (T / m)))

/-- The shifted barrier of an up option, `H · exp(β σ √(T/m))`. It is `H` at `m = 0` and for
`T < 0`. -/
noncomputable def bgkUpBarrier (β : ℝ) (m : ℕ) (H σ T : ℝ) : ℝ :=
  H * Real.exp (β * σ * Real.sqrt (T / m))

/-- The **BGK approximation** to the discretely monitored down-and-out call with `m` equally
spaced monitoring dates: `ptDownOutCall` at the shifted barrier `bgkDownBarrier`. It reads as a
price only where `ptDownOutCall` does: the shifted barrier at most `K` and the spot above it
(for an arbitrary `β` with `β σ < 0` the shifted barrier lies above `H`, so `H ≤ K` alone does
not suffice). The accuracy of the shift as an approximation to the discretely monitored price is
not proved here. -/
noncomputable def bgkDownOutCall (β : ℝ) (m : ℕ) (K H r σ S T : ℝ) : ℝ :=
  ptDownOutCall S K (bgkDownBarrier β m H σ T) r r σ T

/-- The BGK knock-in expression: the Black–Scholes vanilla call price minus `bgkDownOutCall`. -/
noncomputable def bgkKnockIn (β : ℝ) (m : ℕ) (K H r σ S T : ℝ) : ℝ :=
  bsV K r σ S T - bgkDownOutCall β m K H r σ S T

/-- The shifted down barrier is unchanged under `(σ, T) ↦ (σ √c, T / c)` with `m` fixed: the
monitoring step becomes `Δt / c` and the shift `σ √Δt` is invariant. -/
theorem bgkDownBarrier_timeScale {β : ℝ} {m : ℕ} {H σ T c : ℝ} (hc : 0 < c) :
    bgkDownBarrier β m H (σ * Real.sqrt c) (T / c) = bgkDownBarrier β m H σ T := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hv : Real.sqrt (T / c / m) = Real.sqrt (T / m) / Real.sqrt c := by
    rw [div_right_comm, Real.sqrt_div' _ hc.le]
  have : σ * Real.sqrt c * Real.sqrt (T / c / m) = σ * Real.sqrt (T / m) := by
    rw [hv]; field_simp
  unfold bgkDownBarrier
  rw [mul_assoc β, mul_assoc β, this]

/-- The BGK expression is unchanged under `(r, σ, T) ↦ (c r, σ √c, T / c)` with the number of
dates `m` fixed, so it is invariant under the same scaling that fixes `σ² T` and `r T`. -/
theorem bgkDownOutCall_timeScale {β : ℝ} {m : ℕ} {K H r σ S T c : ℝ} (hc : 0 < c) :
    bgkDownOutCall β m K H (c * r) (σ * Real.sqrt c) S (T / c)
      = bgkDownOutCall β m K H r σ S T := by
  unfold bgkDownOutCall
  rw [bgkDownBarrier_timeScale hc, ptDownOutCall_timeScale hc]

/-! ### The limit of many monitoring dates -/

/-- `ptDownOutCall` is continuous in the barrier at every nonzero barrier, for nonzero spot. No
claim that it is a price: that needs `H ≤ K` and `S > H`. -/
theorem continuousAt_ptDownOutCall_barrier {K b r σ S T : ℝ} (hS : S ≠ 0) {H : ℝ} (hH : H ≠ 0) :
    ContinuousAt (fun h ↦ ptDownOutCall S K h b r σ T) H := by
  have hl : ContinuousAt (fun h : ℝ ↦ Real.log (h / S)) H :=
    ContinuousAt.log (continuousAt_id.div_const S) (div_ne_zero hH hS)
  have hPhi : ∀ {f : ℝ → ℝ}, ContinuousAt f H → ContinuousAt (fun h ↦ Phi (f h)) H :=
    fun hf ↦ continuous_Phi.continuousAt.comp hf
  have hE : ∀ a : ℝ, ContinuousAt (fun h ↦ Real.exp (a * Real.log (h / S))) H := fun a ↦
    Real.continuous_exp.continuousAt.comp (continuousAt_const.mul hl)
  have hF1 : ContinuousAt (fun h ↦ ptF1 S K h b σ T) H := by
    unfold ptF1
    exact (((continuousAt_const).add (continuousAt_const.mul hl)).add
      continuousAt_const).div_const _
  have hF2 : ContinuousAt (fun h ↦ ptF2 S K h b σ T) H := by
    unfold ptF2; exact hF1.sub continuousAt_const
  unfold ptDownOutCall ptHSmu ptHSmu1
  exact (continuousAt_const.mul (continuousAt_const.sub ((hE _).mul (hPhi hF1)))).sub
    (continuousAt_const.mul (continuousAt_const.sub ((hE _).mul (hPhi hF2))))

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
the unshifted barrier, for nonzero spot and barrier. It is a statement about the closed-form
expression; it reads as "the BGK approximation tends to the continuous price" only where
`ptDownOutCall` is a price. It is the consistency of the shift with the continuous limit, not an
accuracy result. -/
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
