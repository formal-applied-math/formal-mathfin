/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.BlackScholes.Call
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-!
# Backward-looking (compounded overnight) caplets: the variance-damping time

A caplet on a compounded overnight rate over an accrual period `[τ₀, τ₁]` pays
`(R(τ₁) − K)⁺` at `τ₁`, where `R(t)` is the conditional expectation of the compounded
rate under the `τ₁`-forward measure. By construction `R` is a martingale under that
measure, so the caplet needs **no mean (drift) adjustment**: the entire effect of
compounding is on the *variance*. Inside the accrual period `R(t)` contains more and more
realised fixings, and its volatility is damped by

  `ψ(t) = min 1 ((τ₁ − t) / (τ₁ − τ₀)) ^ q`,   `q > 0`,

(the family used for backward-looking SABR and market models; `q = 1` is the linear
damping from `1` at `τ₀` to `0` at `τ₁`). For constant volatility `σ` the log-variance of
`R(τ₁)` is `σ² · ∫₀^{τ₁} ψ(t)² dt`.

This file proves, from the definition of `ψ`, the damping-time integral, its linear case,
its bounds and monotonicity in `q`, the reduction of the caplet to the Black formula, and the
Jensen ordering of forward- and backward-looking caplets.

## Main definitions

* `onDamping`: the volatility damping `ψ(t) = min 1 (((τ₁ − t)/(τ₁ − τ₀))^q)`.
* `onEffectiveTime`: the variance time `s + (τ₁ − s)·x^{2q}/(2q + 1)` with `s = max τ₀ 0` and
  `x = (τ₁ − s)/(τ₁ − τ₀)`.

## Main results

* `integral_onDamping_sq`: `∫₀^{τ₁} ψ(t)² dt = onEffectiveTime τ₀ τ₁ q`, derived from the
  definition of `ψ`.
* `onEffectiveTime_one`: for `q = 1` it is `s + (τ₁ − s)³ / (3 (τ₁ − τ₀)²)`.
* `le_onEffectiveTime`, `onEffectiveTime_le`, `onEffectiveTime_anti`: `s ≤ Θ ≤ τ₁`, and `Θ` is
  non-increasing in `q`.
* `backwardCaplet_black`: if `R(τ₁) = R₀ exp(−σ²Θ/2 + σ√Θ·Z)` with `Z` standard normal, the
  caplet equals the Black formula at total variance `σ²Θ`, written with the library's
  `bsd1`/`bsd2`.
* `forwardCaplet_le_backwardCaplet`: `E[(E[R | m] − K)⁺] ≤ E[(R − K)⁺]`, so replacing the payoff
  rate by its conditional expectation at an earlier time can only lower the caplet value.

## Scope and hypotheses

The model `dR = ψ σ R dB` itself is not constructed here: `backwardCaplet_black` takes the
lognormal law of `R(τ₁)` with total variance `σ²Θ` as its hypothesis (`BSCallHyp`) and proves
the pricing reduction. The identity `Var(log R(τ₁)) = σ²Θ` for deterministic integrands is the
Itô isometry and is not re-derived. Constant volatility is assumed. The Jensen theorem does not
derive that the compounded rate is a martingale, and equality holds exactly when `R` is
`m`-measurable, which is not asserted.

## Relation to `Inflation.lean`

`yoyConvexity_eq` is a mean (drift) correction obtained from a joint-Gaussian covariance
between two *different* numeraire-measures. Here the quantity is a martingale under its own
payment measure; the compounding structure changes the variance, via the time-dependent
integrand `ψ²`, not the mean.

## References

* [A. Lyashenko and F. Mercurio, *Looking forward to backward-looking rates: A modeling
  framework for term rates replacing LIBOR*][LyashenkoMercurio2019]
* [S. Willems, *SABR smiles for RFR caplets*][Willems2020], §3

## Tags

overnight rate, compounded rate, backward-looking caplet, volatility damping, variance time,
Jensen inequality, Black formula, MSC 91G30, JEL G12
-/

@[expose] public section

open MeasureTheory ProbabilityTheory intervalIntegral

namespace MathFin

/-- Volatility damping of a compounded overnight rate on the accrual period `[τ₀, τ₁]`:
`ψ(t) = min 1 (((τ₁ − t)/(τ₁ − τ₀))^q)`. -/
noncomputable def onDamping (τ₀ τ₁ q t : ℝ) : ℝ :=
  min 1 (((τ₁ - t) / (τ₁ - τ₀)) ^ q)

/-- The total-variance time of a backward-looking rate observed from `0`:
`s + (τ₁ − s)·x^{2q}/(2q + 1)` with `s = max τ₀ 0` and `x = (τ₁ − s)/(τ₁ − τ₀)`. -/
noncomputable def onEffectiveTime (τ₀ τ₁ q : ℝ) : ℝ :=
  max τ₀ 0 + (τ₁ - max τ₀ 0) * (((τ₁ - max τ₀ 0) / (τ₁ - τ₀)) ^ (2 * q)) / (2 * q + 1)

section Damping

variable {τ₀ τ₁ q : ℝ}

private lemma onDamping_sq_of_le {t : ℝ} (hq : 0 < q) (hτ : τ₀ < τ₁)
    (ht0 : τ₀ ≤ t) (ht1 : t ≤ τ₁) :
    onDamping τ₀ τ₁ q t ^ 2 = ((τ₁ - t) / (τ₁ - τ₀)) ^ (2 * q) := by
  have hL : 0 < τ₁ - τ₀ := sub_pos.mpr hτ
  have hx0 : 0 ≤ (τ₁ - t) / (τ₁ - τ₀) := div_nonneg (by linarith) hL.le
  have hx1 : (τ₁ - t) / (τ₁ - τ₀) ≤ 1 := by
    rw [div_le_one hL]; linarith
  have h1 : ((τ₁ - t) / (τ₁ - τ₀)) ^ q ≤ 1 := Real.rpow_le_one hx0 hx1 hq.le
  rw [onDamping, min_eq_right h1, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
  norm_num [mul_comm]

private lemma onDamping_eq_one_of_le {t : ℝ} (hq : 0 < q) (hτ : τ₀ < τ₁) (ht : t ≤ τ₀) :
    onDamping τ₀ τ₁ q t = 1 := by
  have hL : 0 < τ₁ - τ₀ := sub_pos.mpr hτ
  have hx : 1 ≤ (τ₁ - t) / (τ₁ - τ₀) := by
    rw [le_div_iff₀ hL]; linarith
  have h1 : 1 ≤ ((τ₁ - t) / (τ₁ - τ₀)) ^ q := Real.one_le_rpow hx hq.le
  rw [onDamping, min_eq_left h1]

private lemma continuous_onDamping (hq : 0 < q) :
    Continuous fun t => onDamping τ₀ τ₁ q t := by
  unfold onDamping
  refine continuous_const.min ?_
  exact (Continuous.rpow_const (by fun_prop) fun _ => Or.inr hq.le)

/-- The tail integral `∫_s^{τ₁} ((τ₁ − t)/L)^{2q} dt = (τ₁ − s)·x^{2q}/(2q + 1)`. -/
private lemma integral_tail {s L : ℝ} (hq : 0 < q) (hL : 0 < L) (hs : s < τ₁) :
    ∫ t in s..τ₁, ((τ₁ - t) / L) ^ (2 * q)
      = (τ₁ - s) * (((τ₁ - s) / L) ^ (2 * q)) / (2 * q + 1) := by
  have h2q : 0 < 2 * q := by linarith
  have hsub : ∫ t in s..τ₁, ((τ₁ - t) / L) ^ (2 * q)
      = ∫ u in (0 : ℝ)..(τ₁ - s), (u / L) ^ (2 * q) := by
    have := intervalIntegral.integral_comp_sub_left
      (fun u : ℝ => (u / L) ^ (2 * q)) (a := s) (b := τ₁) τ₁
    simpa using this
  rw [hsub]
  have hinner : ∀ u ∈ Set.uIcc (0 : ℝ) (τ₁ - s),
      (u / L) ^ (2 * q) = (L ^ (2 * q))⁻¹ * u ^ (2 * q) := by
    intro u hu
    have hu0 : 0 ≤ u := by
      rw [Set.uIcc_of_le (by linarith)] at hu; exact hu.1
    rw [Real.div_rpow hu0 hL.le]; ring
  rw [intervalIntegral.integral_congr hinner, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith))]
  have hs' : 0 ≤ τ₁ - s := by linarith
  rw [Real.zero_rpow (by linarith), sub_zero, Real.div_rpow hs' hL.le,
    Real.rpow_add_one (by linarith [h2q]) ]
  field_simp

/-- **Damping-time identity.** For `0 < q`, `τ₀ < τ₁` and `0 < τ₁`, the integral of the
squared damping over `[0, τ₁]` is `onEffectiveTime τ₀ τ₁ q`. -/
theorem integral_onDamping_sq (hq : 0 < q) (hτ : τ₀ < τ₁) (hτ1 : 0 < τ₁) :
    ∫ t in (0 : ℝ)..τ₁, onDamping τ₀ τ₁ q t ^ 2 = onEffectiveTime τ₀ τ₁ q := by
  have hL : 0 < τ₁ - τ₀ := sub_pos.mpr hτ
  have hs0 : 0 ≤ max τ₀ 0 := le_max_right _ _
  have hs1 : max τ₀ 0 < τ₁ := max_lt hτ hτ1
  have hcont : Continuous fun t => onDamping τ₀ τ₁ q t ^ 2 :=
    (continuous_onDamping hq).pow 2
  have hhead : ∫ t in (0 : ℝ)..max τ₀ 0, onDamping τ₀ τ₁ q t ^ 2 = max τ₀ 0 := by
    rcases le_or_gt 0 τ₀ with h0 | h0
    · rw [max_eq_left h0]
      have : ∀ t ∈ Set.uIcc (0 : ℝ) τ₀, onDamping τ₀ τ₁ q t ^ 2 = 1 := by
        intro t ht
        rw [Set.uIcc_of_le h0] at ht
        rw [onDamping_eq_one_of_le hq hτ ht.2]; norm_num
      rw [intervalIntegral.integral_congr this]; simp
    · rw [max_eq_right h0.le]; simp
  have htail : ∫ t in max τ₀ 0..τ₁, onDamping τ₀ τ₁ q t ^ 2
      = ∫ t in max τ₀ 0..τ₁, ((τ₁ - t) / (τ₁ - τ₀)) ^ (2 * q) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hs1.le] at ht
    exact onDamping_sq_of_le hq hτ (le_trans (le_max_left _ _) ht.1) ht.2
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable 0 (max τ₀ 0)) (hcont.intervalIntegrable (max τ₀ 0) τ₁),
    hhead, htail, integral_tail hq hL hs1, onEffectiveTime]

/-- Linear case `q = 1`: `Θ = s + (τ₁ − s)³ / (3 (τ₁ − τ₀)²)`. -/
theorem onEffectiveTime_one (hτ : τ₀ < τ₁) :
    onEffectiveTime τ₀ τ₁ 1 = max τ₀ 0 + (τ₁ - max τ₀ 0) ^ 3 / (3 * (τ₁ - τ₀) ^ 2) := by
  have hL : τ₁ - τ₀ ≠ 0 := (sub_pos.mpr hτ).ne'
  unfold onEffectiveTime
  have : (2 * (1 : ℝ)) = ((2 : ℕ) : ℝ) := by norm_num
  rw [this, Real.rpow_natCast]
  field_simp
  ring

/-- The variance time is at least the already-elapsed part `max τ₀ 0`. -/
theorem le_onEffectiveTime (hq : 0 < q) (hτ : τ₀ < τ₁) (hτ1 : 0 < τ₁) :
    max τ₀ 0 ≤ onEffectiveTime τ₀ τ₁ q := by
  have hL : 0 < τ₁ - τ₀ := sub_pos.mpr hτ
  have hs1 : max τ₀ 0 < τ₁ := max_lt hτ hτ1
  unfold onEffectiveTime
  have hx : 0 ≤ (τ₁ - max τ₀ 0) / (τ₁ - τ₀) := div_nonneg (by linarith) hL.le
  have : 0 ≤ (τ₁ - max τ₀ 0) * (((τ₁ - max τ₀ 0) / (τ₁ - τ₀)) ^ (2 * q)) / (2 * q + 1) :=
    div_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hx _)) (by linarith)
  linarith

/-- The variance time never exceeds the full horizon `τ₁`. -/
theorem onEffectiveTime_le (hq : 0 < q) (hτ : τ₀ < τ₁) (hτ1 : 0 < τ₁) :
    onEffectiveTime τ₀ τ₁ q ≤ τ₁ := by
  have hL : 0 < τ₁ - τ₀ := sub_pos.mpr hτ
  have hs1 : max τ₀ 0 < τ₁ := max_lt hτ hτ1
  have hx0 : 0 ≤ (τ₁ - max τ₀ 0) / (τ₁ - τ₀) := div_nonneg (by linarith) hL.le
  have hx1 : (τ₁ - max τ₀ 0) / (τ₁ - τ₀) ≤ 1 := by
    rw [div_le_one hL]; linarith [le_max_left τ₀ 0]
  have h1 : ((τ₁ - max τ₀ 0) / (τ₁ - τ₀)) ^ (2 * q) ≤ 1 :=
    Real.rpow_le_one hx0 hx1 (by linarith)
  unfold onEffectiveTime
  have h2 : (τ₁ - max τ₀ 0) * (((τ₁ - max τ₀ 0) / (τ₁ - τ₀)) ^ (2 * q)) / (2 * q + 1)
      ≤ τ₁ - max τ₀ 0 := by
    rw [div_le_iff₀ (by linarith)]
    have : (τ₁ - max τ₀ 0) * (((τ₁ - max τ₀ 0) / (τ₁ - τ₀)) ^ (2 * q)) ≤ τ₁ - max τ₀ 0 := by
      calc _ ≤ (τ₁ - max τ₀ 0) * 1 := by gcongr
        _ = _ := mul_one _
    nlinarith [sub_pos.mpr hs1]
  linarith

/-- Faster damping lowers the variance time: `Θ` is non-increasing in `q`. -/
theorem onEffectiveTime_anti {q' : ℝ} (hq : 0 < q) (hqq : q ≤ q') (hτ : τ₀ < τ₁)
    (hτ1 : 0 < τ₁) : onEffectiveTime τ₀ τ₁ q' ≤ onEffectiveTime τ₀ τ₁ q := by
  have hL : 0 < τ₁ - τ₀ := sub_pos.mpr hτ
  have hs1 : max τ₀ 0 < τ₁ := max_lt hτ hτ1
  have hx0 : 0 ≤ (τ₁ - max τ₀ 0) / (τ₁ - τ₀) := div_nonneg (by linarith) hL.le
  have hx1 : (τ₁ - max τ₀ 0) / (τ₁ - τ₀) ≤ 1 := by
    rw [div_le_one hL]; linarith [le_max_left τ₀ 0]
  have hpow : ((τ₁ - max τ₀ 0) / (τ₁ - τ₀)) ^ (2 * q')
      ≤ ((τ₁ - max τ₀ 0) / (τ₁ - τ₀)) ^ (2 * q) := by
    by_cases hz : (τ₁ - max τ₀ 0) / (τ₁ - τ₀) = 0
    · rw [hz, Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]
    · exact Real.rpow_le_rpow_of_exponent_ge (lt_of_le_of_ne hx0 (Ne.symm hz)) hx1
        (by linarith)
  unfold onEffectiveTime
  have hA : 0 < τ₁ - max τ₀ 0 := by linarith
  have hB : (τ₁ - max τ₀ 0) * (((τ₁ - max τ₀ 0) / (τ₁ - τ₀)) ^ (2 * q'))
      ≤ (τ₁ - max τ₀ 0) * (((τ₁ - max τ₀ 0) / (τ₁ - τ₀)) ^ (2 * q)) := by gcongr
  have hC : 0 ≤ (τ₁ - max τ₀ 0) * (((τ₁ - max τ₀ 0) / (τ₁ - τ₀)) ^ (2 * q)) :=
    mul_nonneg hA.le (Real.rpow_nonneg hx0 _)
  have : (τ₁ - max τ₀ 0) * (((τ₁ - max τ₀ 0) / (τ₁ - τ₀)) ^ (2 * q')) / (2 * q' + 1)
      ≤ (τ₁ - max τ₀ 0) * (((τ₁ - max τ₀ 0) / (τ₁ - τ₀)) ^ (2 * q)) / (2 * q + 1) := by
    have hq' : 0 ≤ 2 * q' + 1 := by linarith
    calc _ ≤ (τ₁ - max τ₀ 0) * (((τ₁ - max τ₀ 0) / (τ₁ - τ₀)) ^ (2 * q)) / (2 * q' + 1) := by
          gcongr
      _ ≤ _ := by
          apply div_le_div_of_nonneg_left hC (by linarith) (by linarith)
  linarith

end Damping

section Caplet

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Backward-looking caplet reduction.** If the compounded rate at the end of the accrual
period is `R(τ₁) = R₀ exp(−σ²Θ/2 + σ√Θ·Z)` with `Z` standard normal under the `τ₁`-forward
measure `Q` (the `bsTerminal` form with zero drift and time `Θ = onEffectiveTime`), then
the undiscounted caplet value is the Black formula at total variance `σ²Θ`:
`R₀ Φ(d₁) − K Φ(d₂)` with the library's `bsd1`/`bsd2` at `r = 0`, `T = Θ`.
Multiplication by the discount factor `P(0, τ₁)` gives the price. The lognormal law with
variance `σ²Θ` is a hypothesis here (the Itô isometry for `dR = ψσR dB` is not
re-derived), and there is no mean adjustment because `R` is a `Q`-martingale. -/
theorem backwardCaplet_black {Q : Measure Ω} [IsProbabilityMeasure Q]
    {R₀ K σ τ₀ τ₁ q : ℝ} {Z : Ω → ℝ} (hq : 0 < q) (hτ : τ₀ < τ₁) (hτ1 : 0 < τ₁)
    (hR₀ : 0 < R₀) (hK : 0 < K) (hσ : 0 < σ) (hZ : HasLaw Z (gaussianReal 0 1) Q) :
    ∫ ω, max (bsTerminal R₀ 0 σ (onEffectiveTime τ₀ τ₁ q) (Z ω) - K) 0 ∂Q
      = R₀ * Phi (bsd1 R₀ K 0 σ (onEffectiveTime τ₀ τ₁ q))
        - K * Phi (bsd2 R₀ K 0 σ (onEffectiveTime τ₀ τ₁ q)) := by
  have hT : 0 < onEffectiveTime τ₀ τ₁ q := by
    have hL : 0 < τ₁ - τ₀ := sub_pos.mpr hτ
    have hs1 : max τ₀ 0 < τ₁ := max_lt hτ hτ1
    have hx : 0 < (τ₁ - max τ₀ 0) / (τ₁ - τ₀) := div_pos (by linarith) hL
    have h2 : 0 < (τ₁ - max τ₀ 0) * (((τ₁ - max τ₀ 0) / (τ₁ - τ₀)) ^ (2 * q)) / (2 * q + 1) :=
      div_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hx _)) (by linarith)
    unfold onEffectiveTime
    linarith [le_max_right τ₀ 0]
  have := bs_call_formula (Q := Q) (S_0 := R₀) (K := K) (r := 0) (σ := σ)
    (T := onEffectiveTime τ₀ τ₁ q) (Z := Z) ⟨hR₀, hK, hσ, hT, hZ⟩
  simpa using this

/-- **Jensen ordering of caplets.** For a sub-σ-algebra `m` (the information at an earlier
time) and an integrable rate `R`, the call payoff on the conditional expectation
`E[R | m]` has no larger expected value than the call payoff on `R`:
`E[(E[R | m] − K)⁺] ≤ E[(R − K)⁺]`. With `m` the information at `τ₀` and `R = R(τ₁)` this
is the statement that the forward-looking caplet is worth at most the backward-looking
caplet (`R(τ₀) = E[R(τ₁) | F_{τ₀}]` for the martingale `R`); equality holds exactly when
`R` is `m`-measurable, which is not asserted here. The measure `μ` stands for the
`τ₁`-forward measure (the common discount factor `P(0, τ₁)` is omitted). -/
theorem forwardCaplet_le_backwardCaplet {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {R : Ω → ℝ} (hR : Integrable R μ) (K : ℝ) :
    ∫ ω, max (μ[R | m] ω - K) 0 ∂μ ≤ ∫ ω, max (R ω - K) 0 ∂μ := by
  set φ : ℝ → ℝ := fun x => max (x - K) 0 with hφ
  have hlin : ConvexOn ℝ Set.univ (fun x : ℝ => x - K) := by
    refine ⟨convex_univ, fun x _ y _ a b _ _ hab => ?_⟩
    simp only [smul_eq_mul]
    apply le_of_eq
    rw [show b = 1 - a by linarith]
    ring
  have hcvx : ConvexOn ℝ Set.univ φ := hlin.sup (convexOn_const 0 convex_univ)
  have hcont : Continuous φ := by rw [hφ]; fun_prop
  have hint : Integrable (φ ∘ R) μ := by
    have := (hR.sub (integrable_const K)).pos_part
    simpa [hφ, Function.comp_def, posPart_def] using this
  have hae := hcvx.map_condExp_le_univ hm hcont.lowerSemicontinuous hR hint
  have h1 : Integrable (φ ∘ μ[R | m]) μ := by
    have := (integrable_condExp (m := m) (f := R) (μ := μ)).sub (integrable_const K)
    simpa [hφ, Function.comp_def, posPart_def] using this.pos_part
  calc ∫ ω, max (μ[R | m] ω - K) 0 ∂μ ≤ ∫ ω, μ[φ ∘ R | m] ω ∂μ :=
        integral_mono_ae h1 integrable_condExp hae
    _ = ∫ ω, max (R ω - K) 0 ∂μ := integral_condExp hm

end Caplet

end MathFin
