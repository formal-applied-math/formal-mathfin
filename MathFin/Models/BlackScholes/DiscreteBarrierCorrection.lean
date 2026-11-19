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
`V(S) − (H/S)^{2r/σ²−1} · V(H²/S)`, with `V` the Black–Scholes call price `bsV`, is printed in
[HowisonSteinberg2005], §2, eq. (7), and is equivalent to the Reiner–Rubinstein/Hull form
([ReinerRubinstein1991], [Hull]); it is proved here, not assumed, to equal `ptDownOutCall`.

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
* `ptDownOutCall_at_barrier`: the closed form vanishes at `S = H`.
* `ptDownOutCall_scale`: spatial homogeneity, `(S, K, H) ↦ c(S, K, H)` scales it by `c`.
* `ptDownOutCall_timeScale`: it is unchanged under `(r, σ, T) ↦ (c r, σ√c, T/c)`, which fixes
  `σ²T`, `rT` and `σ√T` (`bsV_scale`, `bsV_timeScale` in `ScalingInvariance.lean`).
* `bgkDownBarrier_lt_and_lt_bgkUpBarrier`: the shifted down barrier lies below `H` and the shifted
  up barrier above it, for positive `β σ`.
* `bgkDownBarrier_timeScale`, `bgkDownOutCall_timeScale`: the shift `σ√(T/m)` is fixed by the same
  scaling at fixed `m` (`Δt ↦ Δt/c`), so the BGK expression is as well.
* `bgkDownOutCall_at_shifted_barrier`: it vanishes when the spot is at the shifted barrier.
* `continuousAt_ptDownOutCall_barrier`: `ptDownOutCall` is continuous in the barrier at every
  positive barrier.
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

* [M. Broadie, P. Glasserman, S. Kou, *A continuity correction for discretely monitored barrier
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
`V(S) − (H/S)^{2r/σ²−1} · V(H²/S)` with `V = bsV`, the form printed in [HowisonSteinberg2005],
§2, eq. (7). The exponent `2r/σ² − 1` is `2 · ptMu r σ`, the term `(H/S)^{2r/σ²−1} · (H²/S)` is
`S · ptHSmu1`, and `d₁, d₂` at `H²/S` are `ptF1, ptF2`. An identity between two closed forms;
neither is proved here to be a price. -/
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


/-- The closed form vanishes at the barrier: at `S = H` the reflected point is `H²/H = H` and the
ratio is `1`. -/
theorem ptDownOutCall_at_barrier {K r σ S T : ℝ} (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ) :
    ptDownOutCall S K S r r σ T = 0 := by
  have : S ^ 2 / S = S := by field_simp
  rw [ptDownOutCall_eq_image hS hK hS hσ, div_self hS.ne', this]
  simp

/-- Spatial homogeneity of the closed form: scaling spot, strike and barrier by `c > 0` scales
`ptDownOutCall` by `c`. -/
theorem ptDownOutCall_scale {K H r σ S T c : ℝ} (hc : 0 < c) (hS : 0 < S) (hK : 0 < K)
    (hH : 0 < H) (hσ : 0 < σ) :
    ptDownOutCall (c * S) (c * K) (c * H) r r σ T = c * ptDownOutCall S K H r r σ T := by
  have h1 : c * H / (c * S) = H / S := by field_simp
  have h2 : (c * H) ^ 2 / (c * S) = c * (H ^ 2 / S) := by field_simp
  rw [ptDownOutCall_eq_image (by positivity) (by positivity) (by positivity) hσ,
    ptDownOutCall_eq_image hS hK hH hσ, h1, h2, bsV_scale hc hK, bsV_scale hc hK]
  ring

/-- The closed form is unchanged under `(r, σ, T) ↦ (c r, σ √c, T / c)` for `c > 0`, `0 ≤ T`: the
image exponent `2r/σ² − 1` is fixed because `r/σ²` is, and `bsV` by `bsV_timeScale`. -/
theorem ptDownOutCall_timeScale {K H r σ S T c : ℝ} (hc : 0 < c) (hT : 0 ≤ T) (hS : 0 < S)
    (hK : 0 < K) (hH : 0 < H) (hσ : 0 < σ) :
    ptDownOutCall S K H (c * r) (c * r) (σ * Real.sqrt c) (T / c)
      = ptDownOutCall S K H r r σ T := by
  have hsq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  have hσ' : 0 < σ * Real.sqrt c := mul_pos hσ (Real.sqrt_pos.2 hc)
  have hexp : 2 * (c * r) / (σ * Real.sqrt c) ^ 2 - 1 = 2 * r / σ ^ 2 - 1 := by
    rw [mul_pow, hsq]
    field_simp
  rw [ptDownOutCall_eq_image hS hK hH hσ', ptDownOutCall_eq_image hS hK hH hσ, hexp,
    bsV_timeScale hc hT, bsV_timeScale hc hT]

/-- The shifted barrier of a down option, `H · exp(−β σ √(T/m))`. It is `H` at `m = 0` and for
`T < 0`, where `T / m` or its square root is a junk value. -/
noncomputable def bgkDownBarrier (β : ℝ) (m : ℕ) (H σ T : ℝ) : ℝ :=
  H * Real.exp (-(β * σ * Real.sqrt (T / m)))

/-- The shifted barrier of an up option, `H · exp(β σ √(T/m))`. It is `H` at `m = 0` and for
`T < 0`. -/
noncomputable def bgkUpBarrier (β : ℝ) (m : ℕ) (H σ T : ℝ) : ℝ :=
  H * Real.exp (β * σ * Real.sqrt (T / m))

/-- The shifted down barrier lies below `H` and the shifted up barrier above it, for positive
`β σ`, positive barrier and `0 < T`, `0 < m`. -/
theorem bgkDownBarrier_lt_and_lt_bgkUpBarrier {β σ H T : ℝ} {m : ℕ} (hβ : 0 < β) (hσ : 0 < σ)
    (hH : 0 < H) (hT : 0 < T) (hm : 0 < m) :
    bgkDownBarrier β m H σ T < H ∧ H < bgkUpBarrier β m H σ T := by
  have hs : 0 < Real.sqrt (T / m) := Real.sqrt_pos.2 (by positivity)
  have hp : 0 < β * σ * Real.sqrt (T / m) := by positivity
  refine ⟨?_, ?_⟩
  · unfold bgkDownBarrier
    exact mul_lt_of_lt_one_right hH (by simpa using Real.exp_lt_exp.2 (neg_neg_of_pos hp))
  · unfold bgkUpBarrier
    exact lt_mul_of_one_lt_right hH (by simpa using Real.exp_lt_exp.2 hp)

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

/-- The BGK expression vanishes when the spot sits at the shifted barrier. -/
theorem bgkDownOutCall_at_shifted_barrier {β : ℝ} {m : ℕ} {K H r σ T : ℝ} (hK : 0 < K)
    (hH : 0 < H) (hσ : 0 < σ) :
    bgkDownOutCall β m K H r σ (bgkDownBarrier β m H σ T) T = 0 :=
  ptDownOutCall_at_barrier (mul_pos hH (Real.exp_pos _)) hK hσ

/-- The shifted down barrier is unchanged under `(σ, T) ↦ (σ √c, T / c)` with `m` fixed: the
monitoring step becomes `Δt / c` and the shift `σ √Δt` is invariant. -/
theorem bgkDownBarrier_timeScale {β : ℝ} {m : ℕ} {H σ T c : ℝ} (hc : 0 < c) (hT : 0 ≤ T) :
    bgkDownBarrier β m H (σ * Real.sqrt c) (T / c) = bgkDownBarrier β m H σ T := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hv : Real.sqrt (T / c / m) = Real.sqrt (T / m) / Real.sqrt c := by
    rw [div_right_comm, Real.sqrt_div (by positivity)]
  have : σ * Real.sqrt c * Real.sqrt (T / c / m) = σ * Real.sqrt (T / m) := by
    rw [hv]; field_simp
  unfold bgkDownBarrier
  rw [mul_assoc β, mul_assoc β, this]

/-- The BGK expression is unchanged under `(r, σ, T) ↦ (c r, σ √c, T / c)` with the number of
dates `m` fixed, so it is invariant under the same scaling that fixes `σ² T` and `r T`. -/
theorem bgkDownOutCall_timeScale {β : ℝ} {m : ℕ} {K H r σ S T c : ℝ} (hc : 0 < c)
    (hT : 0 ≤ T) (hS : 0 < S) (hK : 0 < K) (hH : 0 < H) (hσ : 0 < σ) :
    bgkDownOutCall β m K H (c * r) (σ * Real.sqrt c) S (T / c)
      = bgkDownOutCall β m K H r σ S T := by
  unfold bgkDownOutCall
  rw [bgkDownBarrier_timeScale hc hT,
    ptDownOutCall_timeScale hc hT hS hK
      (show 0 < bgkDownBarrier β m H σ T from mul_pos hH (Real.exp_pos _)) hσ]

/-! ### The limit of many monitoring dates -/

/-- For `0 < S`, `0 < K`, `0 < σ`, `0 < T`, `ptDownOutCall` is continuous in the barrier at every
positive barrier (through its image form). No claim that it is a price: that needs `H ≤ K` and
`S > H`. -/
theorem continuousAt_ptDownOutCall_barrier {K r σ S T : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    (hS : 0 < S) (hT : 0 < T) {H : ℝ} (hH : 0 < H) :
    ContinuousAt (fun h ↦ ptDownOutCall S K h r r σ T) H := by
  have hHS : 0 < H ^ 2 / S := by positivity
  have hV : ContinuousAt (fun s ↦ bsV K r σ s T) (H ^ 2 / S) :=
    (hasDerivAt_bsV_S hK hσ hHS hT).continuousAt
  have hq : ContinuousAt (fun h : ℝ ↦ h ^ 2 / S) H := by fun_prop
  have hr : ContinuousAt (fun h : ℝ ↦ (h / S) ^ (2 * r / σ ^ 2 - 1)) H :=
    ((continuousAt_id.div_const S).rpow_const (Or.inl (by simpa using (div_pos hH hS).ne')))
  have himg : ContinuousAt (fun h : ℝ ↦
      bsV K r σ S T - (h / S) ^ (2 * r / σ ^ 2 - 1) * bsV K r σ (h ^ 2 / S) T) H :=
    continuousAt_const.sub (hr.mul (hV.comp_of_eq hq rfl))
  refine himg.congr ?_
  filter_upwards [Ioi_mem_nhds hH] with h hh
  exact (ptDownOutCall_eq_image hS hK hh hσ).symm

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
the unshifted barrier, for positive spot, strike, barrier, volatility and maturity. It is a
statement about the closed-form expression for any positive `H`; it reads as "the BGK
approximation tends to the continuous price" only where `ptDownOutCall` is a price. It is the
consistency of the shift with the continuous limit, not an accuracy result. -/
theorem tendsto_bgkDownOutCall {β K H r σ S T : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S)
    (hH : 0 < H) (hT : 0 < T) :
    Tendsto (fun m : ℕ ↦ bgkDownOutCall β m K H r σ S T) atTop
      (𝓝 (ptDownOutCall S K H r r σ T)) :=
  (continuousAt_ptDownOutCall_barrier hK hσ hS hT hH).tendsto.comp
    (tendsto_bgkDownBarrier β H σ T)

/-! ### Connection to in–out parity -/

/-- **Error transfer through in–out parity.** Under the Black–Scholes lognormal hypothesis, let
the knock-out and knock-in calls for a measurable barrier event `A` be the contracts that pay
`𝟙_{Aᶜ} · f` and `𝟙_A · f` at time `0` (`Contract.value`, as in `knockOutValue`, `knockInValue`),
with `f` the call payoff and discount factor `e^{−rT}`. If the BGK knock-out price is within `ε` of
the knock-out value (for example `A` the event that some monitoring date has the price at or below
the barrier, taken as a hypothesis), then the BGK knock-in price is within `ε` of the knock-in
value: `knockIn + knockOut = bsV` (`knockIn_add_knockOut_eq_bsV`) and
`bgkKnockIn = bsV − bgkDownOutCall`. This is a linear rearrangement of in–out parity with `A`
arbitrary (not tied to `H` or to the monitoring dates), the weakest of the headline results here;
the BGK accuracy claim enters only as the hypothesis and is not proved. -/
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
