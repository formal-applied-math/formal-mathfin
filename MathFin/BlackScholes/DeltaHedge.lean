/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.BlackScholes.PDEFromIto
public import MathFin.Foundations.ItoFormulaAdaptedProcess
public import MathFin.Foundations.ItoFormulaUnrestrictedLocMart
public import MathFin.Foundations.NormalQuantile
public import MathFin.Foundations.NormalTail

/-!
# The Black–Scholes delta hedge replicates the call

In the risk-neutral Black–Scholes model `S_t = S₀·exp((r − σ²/2)t + σ B_t)` the call is
replicated by the self-financing delta hedge. With `C(t, S) = bsV K r σ S (T − t)` the call price
at time `t`, the discounted price `e^{−rt} C(t, S_t)` is the initial price plus the gains of
holding `Δ(s, S_s) = Φ(d₁(S_s, T − s))` shares:

  `e^{−rt} C(t, S_t) = C(0, S₀) + ∫₀ᵗ Δ(s, S_s) · σ e^{−rs} S_s dB_s`
  (`bs_delta_hedge_replication`)

almost surely, for all `t ≤ T'` at once, for every horizon `T' < T`. The integrand is the delta
times the diffusion coefficient `σ e^{−rs} S_s` of the discounted stock
(`discountedGBM_eq_itoIntegral`), so the right side is the initial price plus the hedge's gains
from trade `∫ Δ d(e^{−rs} S_s)`; the integral is the library's `predItoIntegral`.

The proof applies Itô's formula as an identity of processes
(`ItoFormulaAdapted.ito_formula_adapted_unbounded_process`) to the discounted call value in the
Brownian coordinate `f(t, x) = e^{−rt} C(t, S(t, x))` of `BlackScholes/PDEFromIto`: its drift
`f_t + ½ f_xx` vanishes by the Black–Scholes PDE (`discountedCallBrownian_heat_equation`) and its
`x`-derivative is the hedge integrand (`hasDerivAt_discountedCallBrownian_x`). The call price is
singular at `t = T`, while the formula needs partials continuous on all of `ℝ × ℝ`; so `f` is
composed with a smooth cap of time `timeCap`, equal to the identity up to `T'` and below `T`
everywhere, and the identity is read at `t ≤ T'`.

At maturity the hedge pays the call: along any path continuous at `T`, `C(t, S_t) → (S_T − K)⁺`
as `t → T⁻` (`tendsto_bsV_gbm_payoff`, the analytic core in `tendsto_bsV_payoff`).

Not proved here: the identity up to `t = T` itself (the hedge's gain integral is stated only on
`[0, T']` for `T' < T`; the two theorems together say the discounted value converges to the
payoff, not that the integral identity extends to `T`); that the strategy is
admissible or self-financing in the sense of a trading-strategy structure; that the stochastic
integral `∫ Δ σ S̃ dB` equals `∫ Δ d S̃` as an integral against the semimartingale `S̃`.

## Main definitions

* `deltaHedgeIntegrand`: the integrand `σ · e^{−rs}S · Φ(d₁)` with `S = gbmValue S₀ r σ s x`.
* `timeCap`: a smooth map equal to the identity up to `a` and bounded by `b` everywhere.

## Main results

* `bs_delta_hedge_replication`: `e^{−rt} C(t, S_t) = C(0, S₀) + ∫₀ᵗ Δ σ e^{−rs}S_s dB_s`,
  almost surely, for all `t ≤ T' < T`.
* `tendsto_bsV_payoff`: `bsV K r σ S τ → (S* − K)⁺` as `S → S* > 0`, `τ → 0⁺`.
* `tendsto_bsV_gbm_payoff`: the call value along a continuous path converges to the payoff at `T`.

## References

* [F. Black and M. Scholes, *The pricing of options and corporate liabilities*][BlackScholes1973]
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], §4.5

## Tags

Black–Scholes, delta hedging, replication, self-financing strategy, Itô formula,
Black–Scholes PDE, MSC 91G20, MSC 60H05, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter Topology Set ItoIntegralL2
open scoped NNReal

/-! ### The hedge integrand and its derivative -/

/-- **The delta-hedge integrand** of the discounted Black–Scholes call in the Brownian
coordinate: `σ · (e^{−rs} S) · Φ(d₁(S, T − s))` with `S = gbmValue S₀ r σ s x`, the delta `Φ(d₁)`
times the diffusion coefficient `σ e^{−rs} S` of the discounted stock. It is the `x`-derivative of
`discountedCallBrownian` for `s < T` (`hasDerivAt_discountedCallBrownian_x`). -/
noncomputable def deltaHedgeIntegrand (K r σ S₀ T s x : ℝ) : ℝ :=
  σ * (Real.exp (-(r * s)) * gbmValue S₀ r σ s x) *
    Phi (bsd1 (gbmValue S₀ r σ s x) K r σ (T - s))

/-- The `x`-derivative of `deltaHedgeIntegrand` (product and chain rule through the gamma formula
`hasDerivAt_Phi_bsd1_S`), written as the rules produce it. -/
noncomputable def deltaHedgeIntegrandDeriv (K r σ S₀ T s x : ℝ) : ℝ :=
  σ * (Real.exp (-(r * s)) * (σ * gbmValue S₀ r σ s x)) *
      Phi (bsd1 (gbmValue S₀ r σ s x) K r σ (T - s))
    + σ * (Real.exp (-(r * s)) * gbmValue S₀ r σ s x) *
      (gaussianPDFReal 0 1 (bsd1 (gbmValue S₀ r σ s x) K r σ (T - s)) /
        (gbmValue S₀ r σ s x * σ * Real.sqrt (T - s)) * (σ * gbmValue S₀ r σ s x))

/-- The `x`-derivative of the hedge integrand, for `s < T`: `deltaHedgeIntegrandDeriv`. -/
theorem hasDerivAt_deltaHedgeIntegrand_x {K r σ S₀ T s : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    (hS₀ : 0 < S₀) (hs : s < T) (x : ℝ) :
    HasDerivAt (fun y ↦ deltaHedgeIntegrand K r σ S₀ T s y)
      (deltaHedgeIntegrandDeriv K r σ S₀ T s x) x := by
  have hG : 0 < gbmValue S₀ r σ s x := mul_pos hS₀ (Real.exp_pos _)
  have hPhi := (hasDerivAt_Phi_bsd1_S (r := r) hK hσ hG (sub_pos.mpr hs)).comp x
    (hasDerivAt_gbmValue_space S₀ r σ s x)
  exact ((((hasDerivAt_gbmValue_space S₀ r σ s x).const_mul (Real.exp (-(r * s)))).const_mul
    σ).mul hPhi)

/-- **The time derivative of the discounted call in the Brownian coordinate**:
`f_t = −½ f_xx`, the Black–Scholes PDE (`discountedCallBrownian_heat_equation`) with
`f_xx = deltaHedgeIntegrandDeriv`. -/
theorem hasDerivAt_discountedCallBrownian_t {K r σ S₀ T t : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    (hS₀ : 0 < S₀) (ht : t < T) (x : ℝ) :
    HasDerivAt (fun s ↦ discountedCallBrownian K r σ S₀ T s x)
      (-(1 / 2) * deltaHedgeIntegrandDeriv K r σ S₀ T t x) t := by
  obtain ⟨hd, -, hheat⟩ := discountedCallBrownian_heat_equation (x := x) hK hσ hS₀ ht
  have h1 : (deriv fun y ↦ discountedCallBrownian K r σ S₀ T t y) =
      fun y ↦ deltaHedgeIntegrand K r σ S₀ T t y :=
    funext fun y ↦ (hasDerivAt_discountedCallBrownian_x hK hσ hS₀ ht y).deriv
  rw [h1, (hasDerivAt_deltaHedgeIntegrand_x hK hσ hS₀ ht x).deriv] at hheat
  convert hd.hasDerivAt using 1
  linarith

/-! ### A smooth cap of time -/

/-- **A smooth cap of time**: `timeCap a b` is `C^∞`, equal to the identity on `(−∞, a]` and
below `b` everywhere (for `a < b`). It is `a + (b − a)·h((t − a)/(b − a))` with
`h(u) = (1 − θ(u))u + θ(u)/2`, `θ` Mathlib's smooth transition from `0` (for `u ≤ 0`) to `1`
(for `u ≥ 1`). -/
noncomputable def timeCap (a b t : ℝ) : ℝ :=
  a + (b - a) * ((1 - Real.smoothTransition ((t - a) / (b - a))) * ((t - a) / (b - a))
    + Real.smoothTransition ((t - a) / (b - a)) / 2)

/-- `timeCap a b` is smooth. -/
theorem contDiff_timeCap {a b : ℝ} (n : ℕ∞) : ContDiff ℝ n (timeCap a b) := by
  have hu : ContDiff ℝ n fun t : ℝ ↦ (t - a) / (b - a) := by fun_prop
  have hs := Real.smoothTransition.contDiff.comp hu
  exact contDiff_const.add (contDiff_const.mul (((contDiff_const.sub hs).mul hu).add
    (hs.div_const 2)))

/-- `timeCap a b` is the identity on `(−∞, a]`. -/
theorem timeCap_of_le {a b t : ℝ} (hab : a < b) (ht : t ≤ a) : timeCap a b t = t := by
  have hu : (t - a) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have hba : b - a ≠ 0 := by linarith
  rw [timeCap, Real.smoothTransition.zero_of_nonpos hu]
  field_simp
  ring

/-- `timeCap a b` stays below `b`. -/
theorem timeCap_lt {a b : ℝ} (hab : a < b) (t : ℝ) : timeCap a b t < b := by
  have hba : 0 < b - a := by linarith
  have hs0 := Real.smoothTransition.nonneg ((t - a) / (b - a))
  have hs1 := Real.smoothTransition.le_one ((t - a) / (b - a))
  have key : ∀ u s : ℝ, 0 ≤ s → s ≤ 1 → (u < 1 ∨ s = 1) → (1 - s) * u + s / 2 < 1 := by
    intro u s hs0 hs1 h
    rcases h with hu | rfl
    · rcases hs0.lt_or_eq with hpos | rfl
      · nlinarith [mul_nonneg (sub_nonneg.2 hs1) (sub_nonneg.2 hu.le)]
      · linarith
    · norm_num
  have hlt : (1 - Real.smoothTransition ((t - a) / (b - a))) * ((t - a) / (b - a))
      + Real.smoothTransition ((t - a) / (b - a)) / 2 < 1 := by
    refine key _ _ hs0 hs1 ?_
    rcases lt_or_ge ((t - a) / (b - a)) 1 with hu | hu
    · exact Or.inl hu
    · exact Or.inr (Real.smoothTransition.one_of_one_le hu)
  have := mul_lt_mul_of_pos_left hlt hba
  rw [timeCap]
  linarith

/-- `timeCap a b` has derivative `1` on `(−∞, a)`: it is the identity nearby. -/
theorem deriv_timeCap_of_lt {a b t : ℝ} (hab : a < b) (ht : t < a) :
    deriv (timeCap a b) t = 1 := by
  have h : timeCap a b =ᶠ[𝓝 t] id :=
    Filter.eventuallyEq_of_mem (Iio_mem_nhds ht) fun s hs ↦
      timeCap_of_le hab (le_of_lt (show s < a from hs))
  rw [h.deriv_eq]
  exact deriv_id

/-- `timeCap a b` has derivative `1` on `(−∞, a]` (at `a` by continuity of the derivative). -/
theorem deriv_timeCap_of_le {a b t : ℝ} (hab : a < b) (ht : t ≤ a) :
    deriv (timeCap a b) t = 1 := by
  rcases ht.lt_or_eq with h | rfl
  · exact deriv_timeCap_of_lt hab h
  · have hc : ContinuousAt (deriv (timeCap t b)) t :=
      ((contDiff_timeCap 1).continuous_deriv le_rfl).continuousAt
    have h1 : Tendsto (deriv (timeCap t b)) (𝓝[<] t) (𝓝 1) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact (deriv_timeCap_of_lt hab (show s < t from hs)).symm)
    exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) h1

/-! ### Continuity of the hedge integrand along a capped time -/

section Continuity

variable {K r σ S₀ T : ℝ}

/-- `d₁` is continuous in any continuous positive price and time to maturity. -/
theorem continuous_bsd1_comp {X : Type*} [TopologicalSpace X] {g τ : X → ℝ} (hK : 0 < K)
    (hσ : 0 < σ) (hg : Continuous g) (hg0 : ∀ x, 0 < g x) (hτ : Continuous τ)
    (hτ0 : ∀ x, 0 < τ x) : Continuous fun x ↦ bsd1 (g x) K r σ (τ x) := by
  unfold bsd1
  refine Continuous.div ((((hg.div_const K).log fun x ↦ (div_pos (hg0 x) hK).ne').add
    (continuous_const.mul hτ))) (continuous_const.mul (Real.continuous_sqrt.comp hτ)) fun x ↦ ?_
  exact (mul_pos hσ (Real.sqrt_pos.2 (hτ0 x))).ne'

variable {ψ : ℝ → ℝ}

/-- The hedge integrand is jointly continuous after a continuous time change below `T`. -/
theorem continuous_deltaHedgeIntegrand_comp (hK : 0 < K) (hσ : 0 < σ) (hS₀ : 0 < S₀)
    (hψ : Continuous ψ) (hψT : ∀ t, ψ t < T) :
    Continuous fun p : ℝ × ℝ ↦ deltaHedgeIntegrand K r σ S₀ T (ψ p.1) p.2 := by
  have hG : Continuous fun p : ℝ × ℝ ↦ gbmValue S₀ r σ (ψ p.1) p.2 := by
    unfold gbmValue; fun_prop
  have hd := continuous_bsd1_comp (K := K) (r := r) (σ := σ) hK hσ hG
    (fun p ↦ mul_pos hS₀ (Real.exp_pos _)) (continuous_const.sub (hψ.comp continuous_fst))
    fun p ↦ sub_pos.2 (hψT _)
  exact (continuous_const.mul ((by fun_prop : Continuous fun p : ℝ × ℝ ↦
    Real.exp (-(r * ψ p.1))).mul hG)).mul (continuous_Phi.comp hd)

/-- Its `x`-derivative is jointly continuous after a continuous time change below `T`. -/
theorem continuous_deltaHedgeIntegrandDeriv_comp (hK : 0 < K) (hσ : 0 < σ) (hS₀ : 0 < S₀)
    (hψ : Continuous ψ) (hψT : ∀ t, ψ t < T) :
    Continuous fun p : ℝ × ℝ ↦ deltaHedgeIntegrandDeriv K r σ S₀ T (ψ p.1) p.2 := by
  have hG : Continuous fun p : ℝ × ℝ ↦ gbmValue S₀ r σ (ψ p.1) p.2 := by
    unfold gbmValue; fun_prop
  have hτ : Continuous fun p : ℝ × ℝ ↦ T - ψ p.1 := continuous_const.sub (hψ.comp continuous_fst)
  have hd := continuous_bsd1_comp (K := K) (r := r) (σ := σ) hK hσ hG
    (fun p ↦ mul_pos hS₀ (Real.exp_pos _)) hτ fun p ↦ sub_pos.2 (hψT _)
  have he : Continuous fun p : ℝ × ℝ ↦ Real.exp (-(r * ψ p.1)) := by fun_prop
  have hφ : Continuous fun p : ℝ × ℝ ↦
      gaussianPDFReal 0 1 (bsd1 (gbmValue S₀ r σ (ψ p.1) p.2) K r σ (T - ψ p.1)) :=
    (continuous_gaussianPDFReal 0 1).comp hd
  have hden : Continuous fun p : ℝ × ℝ ↦
      gbmValue S₀ r σ (ψ p.1) p.2 * σ * Real.sqrt (T - ψ p.1) :=
    (hG.mul continuous_const).mul (Real.continuous_sqrt.comp hτ)
  exact ((continuous_const.mul (he.mul (continuous_const.mul hG))).mul
    (continuous_Phi.comp hd)).add ((continuous_const.mul (he.mul hG)).mul
    ((hφ.div hden fun p ↦ (mul_pos (mul_pos (mul_pos hS₀ (Real.exp_pos _)) hσ)
      (Real.sqrt_pos.2 (sub_pos.2 (hψT _)))).ne').mul (continuous_const.mul hG)))

end Continuity

/-! ### The hedge integrand is predictable -/

section Predictable

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **A Borel function of time and a continuous adapted path is predictable.** -/
theorem isStronglyPredictable_comp_path (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) {h : ℝ → ℝ → ℝ}
    (hh : Measurable fun p : ℝ × ℝ ↦ h p.1 p.2) :
    IsStronglyPredictable (natFiltration hBmeas) fun (s : ℝ≥0) ω ↦ h s (B s ω) := by
  have hBp : IsStronglyPredictable (natFiltration hBmeas) B :=
    StronglyAdapted.isStronglyPredictable_of_leftContinuous (stronglyAdapted_natFiltration hBmeas)
      fun ω _ ↦ (hBcont ω).continuousWithinAt
  have ht : IsStronglyPredictable (natFiltration hBmeas) fun (s : ℝ≥0) (_ : Ω) ↦ (s : ℝ) :=
    StronglyAdapted.isStronglyPredictable_of_leftContinuous (fun _ ↦ stronglyMeasurable_const)
      fun _ _ ↦ NNReal.continuous_coe.continuousWithinAt
  exact (hh.comp (StronglyMeasurable.prodMk ht hBp).measurable).stronglyMeasurable

/-- The delta-hedge integrand along the Brownian path is predictable (for every `T`, with the
junk value of `bsd1` at and after maturity). -/
theorem deltaHedgeIntegrand_isStronglyPredictable (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) (K r σ S₀ T : ℝ) :
    IsStronglyPredictable (natFiltration hBmeas)
      fun (s : ℝ≥0) ω ↦ deltaHedgeIntegrand K r σ S₀ T s (B s ω) := by
  refine isStronglyPredictable_comp_path hBmeas hBcont ?_
  have hPhi : Measurable Phi := continuous_Phi.measurable
  unfold deltaHedgeIntegrand bsd1 gbmValue
  fun_prop

end Predictable

/-! ### The replication theorem -/

open ItoFormulaAdapted ItoIntegralLocalised in
/-- **The Black–Scholes delta hedge replicates the call.** Let `B` be a Brownian motion with
continuous paths, `S_t = S₀·exp((r − σ²/2)t + σ B_t)` the risk-neutral stock, and `T' < T`. Almost
surely, for every `t ≤ T'` at once, the discounted call value is the initial price plus the gains
of the delta hedge:

  `e^{−rt} · C(t, S_t) = C(0, S₀) + ∫₀ᵗ Δ(s, S_s) · σ e^{−rs} S_s dB_s`,

with `C(t, S) = bsV K r σ S (T − t)`, `Δ(s, S) = Φ(d₁(S, T − s))`, and the integral the Itô
integral `predItoIntegral` of the predictable integrand `deltaHedgeIntegrand`. The integrand is
the delta times the diffusion coefficient `σ e^{−rs} S_s` of the discounted stock, so the
right side is the initial price plus the gains from holding `Δ(s, S_s)` shares of the stock.
No bound on `T' < T` beyond strictness: the horizon cannot reach `T` since the delta is not
continuous there. -/
theorem bs_delta_hedge_replication {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    {K r σ S₀ T : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hS₀ : 0 < S₀) (T' : ℝ≥0) (hT' : (T' : ℝ) < T) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ≥0) T',
      Real.exp (-(r * t)) * bsV K r σ (gbmValue S₀ r σ t (B t ω)) (T - t) =
        bsV K r σ S₀ T + predItoIntegral (μ := μ) T' hBmeas
          (deltaHedgeIntegrand_isStronglyPredictable hBmeas hBcont K r σ S₀ T) t ω := by
  set ψ := timeCap (T' : ℝ) T with hψdef
  have hψ : ContDiff ℝ 1 ψ := contDiff_timeCap 1
  have hψc : Continuous ψ := hψ.continuous
  have hψT : ∀ t, ψ t < T := timeCap_lt hT'
  have hψid : ∀ t ≤ (T' : ℝ), ψ t = t := fun t ht ↦ timeCap_of_le hT' ht
  have hψ'1 : ∀ t ≤ (T' : ℝ), deriv ψ t = 1 := fun t ht ↦ deriv_timeCap_of_le hT' ht
  have hψd (t : ℝ) : HasDerivAt ψ (deriv ψ t) t :=
    (hψ.differentiable one_ne_zero t).hasDerivAt
  -- the time-changed value function and its partials
  set f : ℝ → ℝ → ℝ := fun t x ↦ discountedCallBrownian K r σ S₀ T (ψ t) x with hf
  set f_x : ℝ → ℝ → ℝ := fun t x ↦ deltaHedgeIntegrand K r σ S₀ T (ψ t) x with hfx
  set f_xx : ℝ → ℝ → ℝ := fun t x ↦ deltaHedgeIntegrandDeriv K r σ S₀ T (ψ t) x with hfxx
  set f_t : ℝ → ℝ → ℝ := fun t x ↦ -(1 / 2) * f_xx t x * deriv ψ t with hft
  have hf_t (t x : ℝ) : HasDerivAt (fun s ↦ f s x) (f_t t x) t :=
    (hasDerivAt_discountedCallBrownian_t hK hσ hS₀ (hψT t) x).comp t (hψd t)
  have hf_x (t x : ℝ) : HasDerivAt (fun u ↦ f t u) (f_x t x) x :=
    hasDerivAt_discountedCallBrownian_x hK hσ hS₀ (hψT t) x
  have hf_xx (t x : ℝ) : HasDerivAt (fun u ↦ f_x t u) (f_xx t x) x :=
    hasDerivAt_deltaHedgeIntegrand_x hK hσ hS₀ (hψT t) x
  have hf_x_cont : Continuous fun p : ℝ × ℝ ↦ f_x p.1 p.2 :=
    continuous_deltaHedgeIntegrand_comp hK hσ hS₀ hψc hψT
  have hf_xx_cont : Continuous fun p : ℝ × ℝ ↦ f_xx p.1 p.2 :=
    continuous_deltaHedgeIntegrandDeriv_comp hK hσ hS₀ hψc hψT
  have hf_t_cont : Continuous fun p : ℝ × ℝ ↦ f_t p.1 p.2 :=
    (continuous_const.mul hf_xx_cont).mul
      (((contDiff_timeCap 1).continuous_deriv le_rfl).comp continuous_fst)
  set Xp : ℝ≥0 → Ω → ℝ := localItoProcess (μ := μ) T' hBmeas
    (σ := fun _ _ ↦ (1 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) 0
    (fun _ _ ↦ (0 : ℝ)) with hXp
  -- Itô's formula for `B = ∫ 1 dB`
  have hIto := ito_formula_adapted_unbounded_process hB T' hBmeas hBcont
    (σ := fun _ _ ↦ (1 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const)
    (b := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) 0
    hf_t hf_x hf_xx hf_t_cont hf_x_cont hf_xx_cont
  have hX := ae_localItoIntegral_one_eq hB T' hBmeas hBcont
  have hXc := ae_continuousOn_localItoProcess hB T' hBmeas hBcont
    (σ := fun _ _ ↦ (1 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const)
    (b := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ continuous_const) 0
  have hθX := itoIntegrand_isStronglyPredictable hB T' hBmeas hBcont
    (σ := fun _ _ ↦ (1 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const)
    (b := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) 0
    hf_x_cont
  have hθXc : ∀ᵐ ω ∂μ, ContinuousOn (fun s : ℝ≥0 ↦ f_x s (Xp s ω) * 1) (Icc 0 T') :=
    hXc.mono fun ω h ↦ (hf_x_cont.comp_continuousOn
      (NNReal.continuous_coe.continuousOn.prodMk h)).mul continuousOn_const
  have hHc : ∀ᵐ ω ∂μ, ContinuousOn (fun s : ℝ≥0 ↦ deltaHedgeIntegrand K r σ S₀ T s (B s ω))
      (Icc 0 T') :=
    ae_of_all _ fun ω ↦ ((hf_x_cont.comp (NNReal.continuous_coe.prodMk (hBcont ω))).continuousOn
      ).congr fun s hs ↦ by
        show deltaHedgeIntegrand K r σ S₀ T s (B s ω) =
          deltaHedgeIntegrand K r σ S₀ T (ψ s) (B s ω)
        rw [hψid s (NNReal.coe_le_coe.2 hs.2)]
  have hXs (ω : Ω) (hω : ∀ t ∈ Icc (0 : ℝ≥0) T', localItoIntegral (μ := μ) T' hBmeas
      (σ := fun _ _ ↦ (1 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) t ω
        = B t ω) (s : ℝ≥0) (hs : s ∈ Icc (0 : ℝ≥0) T') : Xp s ω = B s ω := by
    simp [Xp, localItoProcess, AdaptedDrift.driftPath, hω s hs]
  have hcongr := ae_predItoIntegral_congr hB T' hBmeas hBcont hθX
    (by simpa only [mul_one] using hθXc)
    (deltaHedgeIntegrand_isStronglyPredictable hBmeas hBcont K r σ S₀ T) hHc
    (by
      filter_upwards [hX] with ω hω s hs
      show f_x s (Xp s ω) * 1 = deltaHedgeIntegrand K r σ S₀ T s (B s ω)
      rw [hXs ω hω s hs, mul_one]
      show deltaHedgeIntegrand K r σ S₀ T (ψ s) (B s ω) = _
      rw [hψid s (NNReal.coe_le_coe.2 hs.2)])
  -- the drift of the formula vanishes up to `T'`: `f_t + ½ f_xx = 0` there
  have hz (t : ℝ≥0) (ht : t ≤ T') (Y : ℝ≥0 → ℝ) :
      ∫ s in Ioc 0 t, (f_t s (Y s) + f_x s (Y s) * 0 + 1 / 2 * (f_xx s (Y s) * 1 ^ 2))
        ∂timeMeasure = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun s hs ↦ ?_
    have hsT : (s : ℝ) ≤ T' := NNReal.coe_le_coe.2 (hs.2.trans ht)
    simp only [hft, hψ'1 _ hsT]
    ring
  filter_upwards [hIto, hX, hcongr] with ω h1 hXω hc t ht
  have htT : (t : ℝ) ≤ T' := NNReal.coe_le_coe.2 ht.2
  have e2 : f (t : ℝ) (Xp t ω) =
      Real.exp (-(r * t)) * bsV K r σ (gbmValue S₀ r σ t (B t ω)) (T - t) := by
    rw [hXs ω hXω t ht]
    simp only [hf, discountedCallBrownian, hψid _ htT]
  have e3 : f 0 0 = bsV K r σ S₀ T := by
    simp [hf, discountedCallBrownian, hψid 0 (NNReal.coe_nonneg T'), gbmValue]
  have key := h1 t ht
  have hz' := hz t ht.2 (fun s ↦ Xp s ω)
  have hc' := hc t ht
  linarith [key, hz', hc', e2, e3]

/-! ### Convergence to the payoff at maturity -/

/-- The standard normal CDF is 1-Lipschitz: `Φ(y) − Φ(x) ≤ y − x` for `x ≤ y` (its density is at
most `1`). -/
theorem Phi_sub_le {x y : ℝ} (hxy : x ≤ y) : Phi y - Phi x ≤ y - x := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := Phi) (C := 1) (s := univ)
    (fun z _ ↦ (hasDerivAt_Phi z).differentiableAt)
    (fun z _ ↦ by
      rw [(hasDerivAt_Phi z).deriv, Real.norm_eq_abs,
        abs_of_nonneg (gaussianPDFReal_nonneg 0 1 z)]
      exact gaussianPDFReal_zero_one_le_one z)
    convex_univ (mem_univ x) (mem_univ y)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hxy)] at h
  exact (le_abs_self _).trans (by simpa using h)

/-- **The Black–Scholes call value converges to the call payoff at maturity.** If `S → S* > 0`
and the time to maturity `τ → 0⁺` along a filter, then `bsV K r σ S τ → (S* − K)⁺`. Write
`V = S(Φ(d₁) − Φ(d₂)) + (S − Ke^{−rτ})Φ(d₂)`: the first term is at most `S σ √τ`
(`Phi_sub_le`, `d₁ − d₂ = σ√τ`), and `Φ(d₂) → 1` or `0` according as `S* > K` or `S* < K`,
while at `S* = K` the factor `S − Ke^{−rτ}` tends to `0`. -/
theorem tendsto_bsV_payoff {α : Type*} {l : Filter α} {K r σ S' : ℝ} {S τ : α → ℝ}
    (hK : 0 < K) (hσ : 0 < σ) (hS' : 0 < S') (hS : Tendsto S l (𝓝 S'))
    (hτ : Tendsto τ l (𝓝[>] 0)) :
    Tendsto (fun a ↦ bsV K r σ (S a) (τ a)) l (𝓝 (max (S' - K) 0)) := by
  have hτ0 : Tendsto τ l (𝓝 0) := hτ.mono_right nhdsWithin_le_nhds
  have hτpos : ∀ᶠ a in l, 0 < τ a := (tendsto_nhdsWithin_iff.1 hτ).2
  have hSpos : ∀ᶠ a in l, 0 < S a := hS.eventually (lt_mem_nhds hS')
  have hsq : Tendsto (fun a ↦ σ * Real.sqrt (τ a)) l (𝓝 0) := by
    simpa using ((Real.continuous_sqrt.tendsto 0).comp hτ0).const_mul σ
  have hdecomp (a : ℝ) (s : ℝ) : bsV K r σ s a =
      s * (Phi (bsd1 s K r σ a) - Phi (bsd2 s K r σ a))
        + (s - K * Real.exp (-(r * a))) * Phi (bsd2 s K r σ a) := by
    unfold bsV; ring
  -- the first term vanishes
  have hT1 : Tendsto (fun a ↦ S a * (Phi (bsd1 (S a) K r σ (τ a))
      - Phi (bsd2 (S a) K r σ (τ a)))) l (𝓝 0) := by
    have hd (a : α) : bsd2 (S a) K r σ (τ a) ≤ bsd1 (S a) K r σ (τ a) := by
      unfold bsd2; linarith [mul_nonneg hσ.le (Real.sqrt_nonneg (τ a))]
    refine squeeze_zero' (g := fun a ↦ S a * (σ * Real.sqrt (τ a))) ?_ ?_
      (by simpa using hS.mul hsq)
    · filter_upwards [hSpos] with a ha
      exact mul_nonneg ha.le (sub_nonneg.2 (strictMono_Phi.monotone (hd a)))
    · filter_upwards [hSpos] with a ha
      exact mul_le_mul_of_nonneg_left ((Phi_sub_le (hd a)).trans_eq (by unfold bsd2; ring)) ha.le
  -- the second term
  have hE : Tendsto (fun a ↦ Real.exp (-(r * τ a))) l (𝓝 1) := by
    simpa [Function.comp_def] using
      ((by fun_prop : Continuous fun x : ℝ ↦ Real.exp (-(r * x))).tendsto 0).comp hτ0
  have hA : Tendsto (fun a ↦ S a - K * Real.exp (-(r * τ a))) l (𝓝 (S' - K)) := by
    simpa using hS.sub (hE.const_mul K)
  have hnum : Tendsto (fun a ↦ Real.log (S a / K) + (r + σ ^ 2 / 2) * τ a) l
      (𝓝 (Real.log (S' / K))) := by
    simpa using ((hS.div_const K).log (div_pos hS' hK).ne').add (hτ0.const_mul (r + σ ^ 2 / 2))
  have hinv : Tendsto (fun a ↦ (σ * Real.sqrt (τ a))⁻¹) l atTop :=
    tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2 ⟨hsq,
      hτpos.mono fun a ha ↦ mul_pos hσ (Real.sqrt_pos.2 ha)⟩)
  have hd2 (a : α) : bsd2 (S a) K r σ (τ a) =
      (Real.log (S a / K) + (r + σ ^ 2 / 2) * τ a) * (σ * Real.sqrt (τ a))⁻¹
        + -(σ * Real.sqrt (τ a)) := by
    unfold bsd2 bsd1; ring
  have hT2 : Tendsto (fun a ↦ (S a - K * Real.exp (-(r * τ a))) *
      Phi (bsd2 (S a) K r σ (τ a))) l (𝓝 (max (S' - K) 0)) := by
    rcases lt_trichotomy S' K with hlt | heq | hgt
    · have hbot : Tendsto (fun a ↦ bsd2 (S a) K r σ (τ a)) l atBot :=
        ((Tendsto.neg_mul_atTop (Real.log_neg (div_pos hS' hK) ((div_lt_one hK).2 hlt)) hnum
          hinv).atBot_add hsq.neg).congr fun a ↦ (hd2 a).symm
      rw [max_eq_right (by linarith)]
      simpa using hA.mul (tendsto_Phi_atBot.comp hbot)
    · have hA0 : Tendsto (fun a ↦ ‖S a - K * Real.exp (-(r * τ a))‖) l (𝓝 0) := by
        simpa [heq] using hA.norm
      rw [heq, sub_self, max_self]
      refine squeeze_zero_norm (fun a ↦ ?_) hA0
      rw [norm_mul, Real.norm_of_nonneg (Phi_nonneg _)]
      exact mul_le_of_le_one_right (norm_nonneg _) (Phi_le_one _)
    · have htop : Tendsto (fun a ↦ bsd2 (S a) K r σ (τ a)) l atTop :=
        ((Tendsto.pos_mul_atTop (Real.log_pos ((one_lt_div hK).2 hgt)) hnum
          hinv).atTop_add hsq.neg).congr fun a ↦ (hd2 a).symm
      rw [max_eq_left (by linarith)]
      simpa using hA.mul (tendsto_Phi_atTop.comp htop)
  simpa [hdecomp] using hT1.add hT2

/-- **The hedge pays the call.** Along a path `x` continuous at `T`, the call value
`C(t, S_t) = bsV K r σ S_t (T − t)` of the stock `S_t = gbmValue S₀ r σ t (x t)` converges, as
`t → T⁻`, to the call payoff `(S_T − K)⁺`. -/
theorem tendsto_bsV_gbm_payoff {K r σ S₀ : ℝ} (T : ℝ≥0) (hK : 0 < K) (hσ : 0 < σ)
    (hS₀ : 0 < S₀) {x : ℝ≥0 → ℝ} (hx : ContinuousAt x T) :
    Tendsto (fun t : ℝ≥0 ↦ bsV K r σ (gbmValue S₀ r σ t (x t)) ((T : ℝ) - t)) (𝓝[<] T)
      (𝓝 (max (gbmValue S₀ r σ T (x T) - K) 0)) := by
  have hg : Continuous fun p : ℝ × ℝ ↦ gbmValue S₀ r σ p.1 p.2 := by
    unfold gbmValue; fun_prop
  have hS : ContinuousAt (fun t : ℝ≥0 ↦ gbmValue S₀ r σ t (x t)) T :=
    hg.continuousAt.comp (f := fun t : ℝ≥0 ↦ ((t : ℝ), x t))
      (NNReal.continuous_coe.continuousAt.prodMk hx)
  refine tendsto_bsV_payoff hK hσ (mul_pos hS₀ (Real.exp_pos _))
    (hS.tendsto.mono_left nhdsWithin_le_nhds) (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
  · have h := (tendsto_const_nhds (x := (T : ℝ))).sub (NNReal.continuous_coe.tendsto T)
    simpa using h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact sub_pos.2 (NNReal.coe_lt_coe.2 ht)

end MathFin
