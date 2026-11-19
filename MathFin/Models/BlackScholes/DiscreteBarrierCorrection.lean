/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.BlackScholes.BarrierParity
public import MathFin.Models.BlackScholes.PartialTimeBarrierOption

/-!
# Broadie–Glasserman–Kou barrier shift for discretely monitored barrier options

A barrier option monitored only at `m` equally spaced dates (`Δt = T/m`) is worth more than the
continuously monitored one, for a knock-out, because paths can cross the barrier between dates
and return. Broadie, Glasserman and Kou ([BroadieGlassermanKou1997]) give a correction: the
discretely monitored price is approximated by the continuously monitored price with the
barrier moved **away from the spot** by the factor `exp(± β σ √Δt)`, where
`β = −ζ(1/2)/√(2π) ≈ 0.5826` and `ζ` is Riemann's zeta function. The value of `β` is not
proved here: every theorem below is stated for an arbitrary shift constant `β`.

The statement, for a down-and-out call with barrier `B`, is
`V_d(S, t; B) = V_cont(S, t; B e^{−βσ√(T/N)}) + O(σ² T/N)`, as restated in
[HowisonSteinberg2005], §1 (the rate is theirs), which cites
[BroadieGlassermanKou1997]. The BGK paper itself is neither
reproduced nor derived here.

This file takes that shift as a **definition** and proves what follows from the definition alone.

## Main definitions

* `downOutCallCont`: the image-form expression `V(S) − (H/S)^{2r/σ²−1} · V(H²/S)`, where `V` is
  the Black–Scholes call price `bsV`. It is the continuously monitored down-and-out call price
  (transcribed from [ReinerRubinstein1991], see also [Hull]) only for `H ≤ K`, `S > H` and no
  dividends; the theorems below concern the expression for any positive `H`, and the
  reflection-principle step that identifies it with the price is **not** derived here. It is a
  second transcription of the library's `ptDownOutCall`, tied to it by
  `downOutCallCont_eq_ptDownOutCall`.
* `bgkDownBarrier`, `bgkUpBarrier`: the shifted barriers `H e^{∓βσ√(T/m)}`.
* `bgkDownOutCall`: the BGK price of the discretely monitored down-and-out call, the continuous
  price at the shifted barrier. There is no continuous up-and-out closed form in this library,
  so only the up-barrier shift is defined, not an up-and-out price.
* `bgkKnockIn`: the BGK knock-in price, the vanilla price `bsV` minus the BGK knock-out price.

## Main results

* `bgkDownBarrier_lt_and_lt_bgkUpBarrier`: the shifted down barrier lies below `H` and the shifted
  up barrier above it.
* `downOutCallCont_eq_ptDownOutCall`, `bgkDownOutCall_eq_ptDownOutCall`: the image form (and the
  BGK price at the shifted barrier) equals `ptDownOutCall` at cost of carry `b = r`, for positive
  spot, strike, barrier and volatility; an identity between two transcribed closed forms.
* `downOutCallCont_at_barrier`: the continuous price vanishes at `S = H`.
* `bsV_scale`, `downOutCallCont_scale`: spatial homogeneity, `(K, H, S) ↦ c(K, H, S)` scales the
  price by `c`.
* `bsV_timeScale`, `downOutCallCont_timeScale`: the price is unchanged under
  `(r, σ, τ) ↦ (c r, σ√c, τ/c)`, which fixes `σ²τ` and `rτ`.
* `bgkDownBarrier_timeScale`, `bgkDownOutCall_timeScale`: the BGK shift `σ√(T/m)` is fixed by the
  same scaling (for fixed `m`, `Δt ↦ Δt/c`), so the BGK price is as well.
* `bgkDownOutCall_at_shifted_barrier`: the BGK price vanishes when the spot is at the shifted
  barrier.
* `continuousAt_downOutCallCont_barrier`: `downOutCallCont` is continuous in the barrier at every
  positive barrier.
* `tendsto_bgkDownBarrier`: the shifted barrier tends to `H` as the number of dates `m → ∞`.
* `tendsto_bgkDownOutCall`: as the number of dates `m → ∞` the BGK price tends to the continuous
  price.
* `abs_knockIn_sub_bgkKnockIn_le`: a linear rearrangement of in–out parity
  (`knockIn_add_knockOut_eq_bsV`), for an arbitrary measurable event `A`: a bound on the error of
  the BGK knock-out price against a knock-out value transfers to the knock-in. It does not link `A`
  to `H` or the monitoring dates.

## Scope

The accuracy of the shift as an approximation to the discretely monitored price is **not**
proved here. The rate `O(σ² Δt)` is attributed only to the restatement in
[HowisonSteinberg2005], not to [BroadieGlassermanKou1997]. Nothing here is a model of
discrete monitoring: the discretely monitored value never appears, except as the hypothesised
benchmark in `abs_knockIn_sub_bgkKnockIn_le`.

## References

* [M. Broadie, P. Glasserman, S. Kou, *A continuity correction for discretely monitored barrier
  options*][BroadieGlassermanKou1997]
* [S. Howison, M. Steinberg, *A matched asymptotic expansions approach to continuity corrections
  for discretely sampled options. Part 1: barrier options*][HowisonSteinberg2005], §1
* [E. Reiner and M. Rubinstein, *Breaking down the barriers*][ReinerRubinstein1991]
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull] (10th ed., Pearson, 2018), ch. 26

## Tags

barrier option, discrete monitoring, continuity correction, down-and-out call,
Broadie–Glasserman–Kou, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open Filter Topology

/-- The image-form expression `V(S) − (H/S)^{2r/σ²−1} V(H²/S)` with `V = bsV` the Black–Scholes
call price, defined for any `H`. It is the continuously monitored down-and-out call price only for
barrier `H ≤ K`, spot `S > H` and no dividends (a transcribed closed form; the
reflection-principle derivation is not proved here). -/
noncomputable def downOutCallCont (K H r σ S τ : ℝ) : ℝ :=
  bsV K r σ S τ - (H / S) ^ (2 * r / σ ^ 2 - 1) * bsV K r σ (H ^ 2 / S) τ

/-- The image form vanishes at the barrier: at `S = H` the reflected point is `H²/H = H` and the
ratio is `1`. -/
theorem downOutCallCont_at_barrier {K H r σ τ : ℝ} (hH : 0 < H) :
    downOutCallCont K H r σ H τ = 0 := by
  have : H ^ 2 / H = H := by field_simp
  simp [downOutCallCont, div_self hH.ne', this]

/-- **Image form equals the library's full-life closed form.** For positive spot, strike, barrier
and volatility, `downOutCallCont K H r σ S T` is `ptDownOutCall S K H r r σ T`, the transcribed
Rubinstein–Reiner full-life down-and-out call (`PartialTimeBarrierOption.lean`, the `X ≥ H` branch)
at cost of carry `b = r`: the exponent `2r/σ² − 1` is `2 · ptMu r σ`, the term
`(H/S)^{2r/σ²−1} · (H²/S)` is `S · ptHSmu1`, and `d₁, d₂` at `H²/S` are `ptF1, ptF2`. This is an
identity between two transcribed closed forms; neither is proved here to be a price, and
the price reading (`H ≤ K`, `S > H`) is the one `ptDownOutCall` carries. -/
theorem downOutCallCont_eq_ptDownOutCall {K H r σ S T : ℝ} (hS : 0 < S) (hK : 0 < K)
    (hH : 0 < H) (hσ : 0 < σ) :
    downOutCallCont K H r σ S T = ptDownOutCall S K H r r σ T := by
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
  unfold downOutCallCont ptDownOutCall bsV
  rw [← h0, ← hf1, ← hf2, h1]
  nth_rewrite 1 [hsq]
  simp only [ptD1, ptD2, sub_self, zero_mul, Real.exp_zero, neg_mul]
  ring

/-- The shifted barrier of a down option, `H · exp(−β σ √(T/m))`. -/
noncomputable def bgkDownBarrier (β : ℝ) (m : ℕ) (H σ T : ℝ) : ℝ :=
  H * Real.exp (-(β * σ * Real.sqrt (T / m)))

/-- The shifted barrier of an up option, `H · exp(β σ √(T/m))`. -/
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

/-- The **BGK price** of the discretely monitored down-and-out call with `m` equally spaced
monitoring dates: `downOutCallCont` at the shifted barrier `bgkDownBarrier`, a price reading only
for `H ≤ K` and spot above the shifted barrier. The accuracy of the shift as an
approximation to the discretely monitored price is not proved here. -/
noncomputable def bgkDownOutCall (β : ℝ) (m : ℕ) (K H r σ S T : ℝ) : ℝ :=
  downOutCallCont K (bgkDownBarrier β m H σ T) r σ S T

/-- The BGK price is the library's full-life down-and-out closed form `ptDownOutCall` (cost of
carry `b = r`) at the shifted barrier, for positive spot, strike, barrier and volatility. -/
theorem bgkDownOutCall_eq_ptDownOutCall {β : ℝ} {m : ℕ} {K H r σ S T : ℝ} (hS : 0 < S)
    (hK : 0 < K) (hH : 0 < H) (hσ : 0 < σ) :
    bgkDownOutCall β m K H r σ S T = ptDownOutCall S K (bgkDownBarrier β m H σ T) r r σ T :=
  downOutCallCont_eq_ptDownOutCall hS hK (mul_pos hH (Real.exp_pos _)) hσ

/-- The BGK knock-in price: the Black–Scholes vanilla call price minus the BGK knock-out price. -/
noncomputable def bgkKnockIn (β : ℝ) (m : ℕ) (K H r σ S T : ℝ) : ℝ :=
  bsV K r σ S T - bgkDownOutCall β m K H r σ S T

/-- The BGK price vanishes when the spot sits at the shifted barrier. -/
theorem bgkDownOutCall_at_shifted_barrier {β : ℝ} {m : ℕ} {K H r σ T : ℝ} (hH : 0 < H) :
    bgkDownOutCall β m K H r σ (bgkDownBarrier β m H σ T) T = 0 :=
  downOutCallCont_at_barrier (mul_pos hH (Real.exp_pos _))

/-! ### Scaling identities -/

/-- `d₁` is unchanged when spot and strike are scaled together. -/
theorem bsd1_scale {S K r σ τ c : ℝ} (hc : 0 < c) (hK : 0 < K) :
    bsd1 (c * S) (c * K) r σ τ = bsd1 S K r σ τ := by
  have : c * S / (c * K) = S / K := by field_simp
  simp [bsd1, this]

/-- `d₂` is unchanged when spot and strike are scaled together. -/
theorem bsd2_scale {S K r σ τ c : ℝ} (hc : 0 < c) (hK : 0 < K) :
    bsd2 (c * S) (c * K) r σ τ = bsd2 S K r σ τ := by
  simp [bsd2, bsd1_scale hc hK]

/-- **Spatial homogeneity**: `bsV (cK) (cS) = c · bsV K S`. -/
theorem bsV_scale {K r σ S τ c : ℝ} (hc : 0 < c) (hK : 0 < K) :
    bsV (c * K) r σ (c * S) τ = c * bsV K r σ S τ := by
  unfold bsV
  rw [bsd1_scale hc hK, bsd2_scale hc hK]
  ring

/-- Spatial homogeneity of the continuous down-and-out call: scaling strike, barrier and spot by
`c` scales the price by `c`. -/
theorem downOutCallCont_scale {K H r σ S τ c : ℝ} (hc : 0 < c) (hS : 0 < S) (hK : 0 < K)
    (hH : 0 < H) :
    downOutCallCont (c * K) (c * H) r σ (c * S) τ = c * downOutCallCont K H r σ S τ := by
  have h1 : c * H / (c * S) = H / S := by field_simp
  have h2 : (c * H) ^ 2 / (c * S) = c * (H ^ 2 / S) := by field_simp
  have hHS : 0 < H ^ 2 / S := by positivity
  unfold downOutCallCont
  rw [h1, h2, bsV_scale hc hK, bsV_scale hc hK]
  ring

/-- `d₁` is unchanged under `(r, σ, τ) ↦ (c r, σ √c, τ / c)`, which fixes `σ² τ`, `r τ` and
`σ √τ`. -/
theorem bsd1_timeScale {S K r σ τ c : ℝ} (hc : 0 < c) (hτ : 0 ≤ τ) :
    bsd1 S K (c * r) (σ * Real.sqrt c) (τ / c) = bsd1 S K r σ τ := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hsq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  have hv : Real.sqrt (τ / c) = Real.sqrt τ / Real.sqrt c := Real.sqrt_div hτ c
  have hnum : (c * r + (σ * Real.sqrt c) ^ 2 / 2) * (τ / c) = (r + σ ^ 2 / 2) * τ := by
    rw [mul_pow, hsq]; field_simp
  have hden : σ * Real.sqrt c * Real.sqrt (τ / c) = σ * Real.sqrt τ := by
    rw [hv]; field_simp
  unfold bsd1
  rw [hnum, hden]

/-- `d₂` is unchanged under `(r, σ, τ) ↦ (c r, σ √c, τ / c)`. -/
theorem bsd2_timeScale {S K r σ τ c : ℝ} (hc : 0 < c) (hτ : 0 ≤ τ) :
    bsd2 S K (c * r) (σ * Real.sqrt c) (τ / c) = bsd2 S K r σ τ := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hv : Real.sqrt (τ / c) = Real.sqrt τ / Real.sqrt c := Real.sqrt_div hτ c
  have hden : σ * Real.sqrt c * Real.sqrt (τ / c) = σ * Real.sqrt τ := by
    rw [hv]; field_simp
  rw [bsd2, bsd2, bsd1_timeScale hc hτ, hden]

/-- **Time-volatility scaling**: the Black–Scholes call price is unchanged under
`(r, σ, τ) ↦ (c r, σ √c, τ / c)`. -/
theorem bsV_timeScale {K r σ S τ c : ℝ} (hc : 0 < c) (hτ : 0 ≤ τ) :
    bsV K (c * r) (σ * Real.sqrt c) S (τ / c) = bsV K r σ S τ := by
  have hexp : c * r * (τ / c) = r * τ := by field_simp
  unfold bsV
  rw [bsd1_timeScale hc hτ, bsd2_timeScale hc hτ, hexp]

/-- The continuous down-and-out call is unchanged under `(r, σ, τ) ↦ (c r, σ √c, τ / c)`: the
image exponent `2r/σ² − 1` is fixed because `r/σ²` is. -/
theorem downOutCallCont_timeScale {K H r σ S τ c : ℝ} (hc : 0 < c) (hτ : 0 ≤ τ) :
    downOutCallCont K H (c * r) (σ * Real.sqrt c) S (τ / c) = downOutCallCont K H r σ S τ := by
  have hsq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  have hexp : 2 * (c * r) / (σ * Real.sqrt c) ^ 2 - 1 = 2 * r / σ ^ 2 - 1 := by
    rw [mul_pow, hsq]
    rcases eq_or_ne σ 0 with h | h
    · simp [h]
    · field_simp
  unfold downOutCallCont
  rw [hexp, bsV_timeScale hc hτ, bsV_timeScale hc hτ]

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

/-- The BGK price is unchanged under `(r, σ, T) ↦ (c r, σ √c, T / c)` with the number of dates
`m` fixed, so the correction is consistent with the Brownian time-volatility scaling. -/
theorem bgkDownOutCall_timeScale {β : ℝ} {m : ℕ} {K H r σ S T c : ℝ} (hc : 0 < c)
    (hT : 0 ≤ T) :
    bgkDownOutCall β m K H (c * r) (σ * Real.sqrt c) S (T / c)
      = bgkDownOutCall β m K H r σ S T := by
  unfold bgkDownOutCall
  rw [bgkDownBarrier_timeScale hc hT, downOutCallCont_timeScale hc hT]

/-! ### The limit of many monitoring dates -/

/-- For `0 < S`, `0 < K`, `0 < σ`, `0 < τ`, the expression `downOutCallCont` is continuous in `H`
at every positive `H`. No claim that it is a price: that needs `H ≤ K` and `S > H`. -/
theorem continuousAt_downOutCallCont_barrier {K r σ S τ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    (hS : 0 < S) (hτ : 0 < τ) {H : ℝ} (hH : 0 < H) :
    ContinuousAt (fun h ↦ downOutCallCont K h r σ S τ) H := by
  have hHS : 0 < H ^ 2 / S := by positivity
  have hV : ContinuousAt (fun s ↦ bsV K r σ s τ) (H ^ 2 / S) :=
    (hasDerivAt_bsV_S hK hσ hHS hτ).continuousAt
  have hq : ContinuousAt (fun h : ℝ ↦ h ^ 2 / S) H := by fun_prop
  have hr : ContinuousAt (fun h : ℝ ↦ (h / S) ^ (2 * r / σ ^ 2 - 1)) H :=
    ((continuousAt_id.div_const S).rpow_const (Or.inl (by simpa using (div_pos hH hS).ne')))
  unfold downOutCallCont
  exact continuousAt_const.sub (hr.mul (hV.comp_of_eq hq rfl))

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

/-- **Many-dates limit.** As `m → ∞` the expression `bgkDownOutCall` tends to `downOutCallCont`,
for positive spot, strike, barrier, volatility and maturity. It is a statement about the
closed-form expression for any positive `H`; it reads as "discretely monitored price tends to the
continuous price" only for `H ≤ K` and `S > H`. It is the consistency of the shift with the
continuous limit, not the BGK accuracy theorem. -/
theorem tendsto_bgkDownOutCall {β K H r σ S T : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S)
    (hH : 0 < H) (hT : 0 < T) :
    Tendsto (fun m : ℕ ↦ bgkDownOutCall β m K H r σ S T) atTop
      (𝓝 (downOutCallCont K H r σ S T)) :=
  (continuousAt_downOutCallCont_barrier hK hσ hS hT hH).tendsto.comp
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
