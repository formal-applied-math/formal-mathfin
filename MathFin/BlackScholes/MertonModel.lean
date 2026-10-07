/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.BlackScholes.MertonJumpDiffusion
public import MathFin.BlackScholes.VarianceSwap
public import MathFin.Foundations.BrownianMartingale
public import MathFin.Foundations.IndepFreezing

/-!
# Merton's jump-diffusion: the price formula derived from the model

`BlackScholes/MertonJumpDiffusion.lean` *defines* the Merton (1976) call price as a Poisson
mixture of Black–Scholes prices, `mertonCallPrice = ∫ n, mertonCallTerm n ∂Poisson(Λ)`. This
file proves that the mixture is the price of the jump-diffusion model. Under the pricing measure
`Q` the model's terminal price is

  `S_T = S₀ · exp((r − σ²/2)T − kΛ + σ√T·Z + ∑_{i<N} Jᵢ)`  (`mertonTerminal`),

where `Z ∼ N(0, 1)` drives the diffusion (the Brownian motion at maturity is `√T·Z`),
`N ∼ Poisson(Λ)` counts the jumps up to maturity (`Λ = λT` for a jump intensity `λ`), and the
log-jump sizes `Jᵢ ∼ N(log(1 + k) − δ²/2, δ²)` are i.i.d., so each jump multiplies the price by
`e^{Jᵢ}`, whose mean is `1 + k`. The count, the diffusion and the jumps are independent
(`MertonHyp`). The `−kΛ` in the exponent is Merton's compensator.

## Main results

* `mertonTerminal_eq_bsTerminal`, `MertonHyp.hasLaw_mertonStd`: with `n` jumps, `S_T` is the
  Black–Scholes terminal price at spot `mertonSpot n` and volatility `mertonVol n`, driven by the
  standard normal `mertonStd`, which is the total log-shock `σ√T·Z + ∑_{i<n} Jᵢ` standardized.
  A sum of independent Gaussians is Gaussian (`hasLaw_sum_range_gaussianReal`).
* `merton_call_given_jumps`: the discounted call payoff with the jump count frozen at `n` has
  expectation `mertonCallTerm n`.
* `merton_call_formula`: `𝔼[e^{−rT}(S_T − K)⁺] = mertonCallPrice`. Conditioning on the jump
  count (`integral_comp_of_hasLaw_poissonMeasure`, the freezing lemma for a Poisson count) turns
  the expectation into the Poisson mixture of the conditional prices.
* `merton_put_formula`: `𝔼[e^{−rT}(K − S_T)⁺] = mertonPutPrice`.
* `merton_discounted_terminal`: `𝔼[e^{−rT}S_T] = S₀`. The compensator `−kΛ` is the drift
  correction that gives the discounted terminal price mean `S₀`.

## Scope

Only the law of the price at maturity is modelled, which is all a European payoff needs. The
price *process* `(S_t)`, Brownian motion plus a compound-Poisson process, and the martingale
property of `e^{−rt}S_t` at intermediate dates are not constructed.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}

/-! ### Sums and standardization of Gaussian variables -/

/-- A sum of `n` independent `N(m, v)` variables is `N(n·m, n·v)`. -/
theorem hasLaw_sum_range_gaussianReal [IsProbabilityMeasure Q] {J : ℕ → Ω → ℝ} {m : ℝ}
    {v : ℝ≥0} (hJ : ∀ i, HasLaw (J i) (gaussianReal m v) Q) (hind : iIndepFun J Q) (n : ℕ) :
    HasLaw (∑ i ∈ Finset.range n, J i) (gaussianReal (n * m) (n * v)) Q := by
  induction n with
  | zero =>
    simp only [Finset.sum_range_zero, Nat.cast_zero, zero_mul, gaussianReal_zero_var]
    exact hasLaw_dirac_of_ae_eq (ae_of_all _ fun _ ↦ rfl)
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h := (hind.indepFun_sum_range_succ₀ (fun i ↦ (hJ i).aemeasurable) n).hasLaw_add ih (hJ n)
    rw [gaussianReal_conv_gaussianReal] at h
    convert h using 2 <;> push_cast <;> ring

/-- Standardizing a Gaussian: if `X ∼ N(μ, s²)` with `s > 0`, then `(X − μ)/s ∼ N(0, 1)`. -/
theorem hasLaw_sub_div_of_gaussianReal {X : Ω → ℝ} {μ s : ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal μ v) Q) (hs : 0 < s) (hv : (v : ℝ) = s ^ 2) :
    HasLaw (fun ω ↦ (X ω - μ) / s) (gaussianReal 0 1) Q := by
  have h := gaussianReal_const_mul (gaussianReal_sub_const hX μ) s⁻¹
  have hparam : gaussianReal (s⁻¹ * (μ - μ)) (.mk (s⁻¹ ^ 2) (sq_nonneg _) * v)
      = gaussianReal 0 1 := by
    congr 1
    · rw [sub_self, mul_zero]
    · ext
      rw [NNReal.coe_mul, NNReal.coe_mk, hv, NNReal.coe_one, inv_pow,
        inv_mul_cancel₀ (pow_pos hs 2).ne']
  rw [hparam] at h
  simpa only [div_eq_inv_mul] using h

/-! ### Black–Scholes payoffs driven by a standard normal are integrable -/

/-- The Black–Scholes terminal price driven by a standard normal is integrable: it is a constant
times the exponential of a Gaussian. -/
theorem integrable_bsTerminal {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) Q)
    (S_0 r σ T : ℝ) : Integrable (fun ω ↦ bsTerminal S_0 r σ T (Z ω)) Q := by
  have h_split : (fun ω ↦ bsTerminal S_0 r σ T (Z ω)) = fun ω ↦
      S_0 * rexp ((r - σ ^ 2 / 2) * T) * rexp (σ * Real.sqrt T * Z ω) := by
    funext ω
    unfold bsTerminal
    rw [Real.exp_add]
    ring
  rw [h_split]
  exact (integrable_exp_mul_of_hasLaw hZ (σ * Real.sqrt T)).const_mul _

/-- The discounted Black–Scholes call payoff driven by a standard normal is integrable: it is
dominated by the discounted terminal price. -/
theorem integrable_bsCall_payoff {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) Q) {S_0 K : ℝ}
    (hS_0 : 0 ≤ S_0) (hK : 0 ≤ K) (r σ T : ℝ) :
    Integrable (fun ω ↦ rexp (-r * T) * max (bsTerminal S_0 r σ T (Z ω) - K) 0) Q := by
  have hmeas : Measurable fun z ↦ rexp (-r * T) * max (bsTerminal S_0 r σ T z - K) 0 := by
    unfold bsTerminal
    fun_prop
  refine ((integrable_bsTerminal hZ S_0 r σ T).const_mul (rexp (-r * T))).mono'
    (hmeas.comp_aemeasurable hZ.aemeasurable).aestronglyMeasurable (ae_of_all _ fun ω ↦ ?_)
  have hS : 0 ≤ bsTerminal S_0 r σ T (Z ω) := mul_nonneg hS_0 (Real.exp_pos _).le
  exact (Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (le_max_right _ _))).trans_le
    (mul_le_mul_of_nonneg_left (max_le (by linarith) hS) (Real.exp_pos _).le)

/-- The discounted Black–Scholes put payoff driven by a standard normal is integrable: it is
bounded by the discounted strike. -/
theorem integrable_bsPut_payoff [IsFiniteMeasure Q] {Z : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) Q) {S_0 K : ℝ} (hS_0 : 0 ≤ S_0) (hK : 0 ≤ K)
    (r σ T : ℝ) :
    Integrable (fun ω ↦ rexp (-r * T) * max (K - bsTerminal S_0 r σ T (Z ω)) 0) Q := by
  have hmeas : Measurable fun z ↦ rexp (-r * T) * max (K - bsTerminal S_0 r σ T z) 0 := by
    unfold bsTerminal
    fun_prop
  refine (integrable_const (rexp (-r * T) * K)).mono'
    (hmeas.comp_aemeasurable hZ.aemeasurable).aestronglyMeasurable (ae_of_all _ fun ω ↦ ?_)
  have hS : 0 ≤ bsTerminal S_0 r σ T (Z ω) := mul_nonneg hS_0 (Real.exp_pos _).le
  exact (Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (le_max_right _ _))).trans_le
    (mul_le_mul_of_nonneg_left (max_le (by linarith) hK) (Real.exp_pos _).le)

/-! ### The model -/

/-- The terminal price of Merton's jump-diffusion at a diffusion sample `z`, a jump count `n`
and log-jump sizes `j`: `S₀ · exp((r − σ²/2)T − kΛ + σ√T·z + ∑_{i<n} jᵢ)`. -/
noncomputable def mertonTerminal (S_0 r σ T k : ℝ) (Λ : ℝ≥0) (z : ℝ) (n : ℕ) (j : ℕ → ℝ) :
    ℝ :=
  S_0 * rexp ((r - σ ^ 2 / 2) * T - k * Λ + σ * Real.sqrt T * z + ∑ i ∈ Finset.range n, j i)

/-- The standard normal of the `n`-jump conditional economy: the total log-shock
`σ√T·z + ∑_{i<n} jᵢ`, centred at its mean `n(log(1 + k) − δ²/2)` and divided by its standard
deviation `mertonVol n · √T`. -/
noncomputable def mertonStd (σ T k δ z : ℝ) (n : ℕ) (j : ℕ → ℝ) : ℝ :=
  (σ * Real.sqrt T * z + ∑ i ∈ Finset.range n, j i - n * (Real.log (1 + k) - δ ^ 2 / 2))
    / (mertonVol σ δ T n * Real.sqrt T)

/-- **Merton's jump-diffusion at maturity**, under a pricing measure `Q`: a standard normal `Z`
(the Brownian motion at maturity is `√T·Z`), a `Poisson(Λ)` jump count `N`, and i.i.d. log-jump
sizes `Jᵢ ∼ N(log(1 + k) − δ²/2, δ²)`, so that the jump multipliers `e^{Jᵢ}` have mean `1 + k`.
The count is independent of the diffusion and the jumps together, and the diffusion is independent
of the jumps; with the jumps mutually independent, this makes `N`, `Z`, `J₀, J₁, …` mutually
independent. -/
structure MertonHyp (Q : Measure Ω) (k δ : ℝ) (Λ : ℝ≥0) (Z : Ω → ℝ) (N : Ω → ℕ)
    (J : ℕ → Ω → ℝ) : Prop where
  Z_law : HasLaw Z (gaussianReal 0 1) Q
  N_law : HasLaw N (poissonMeasure Λ) Q
  J_law : ∀ i, HasLaw (J i) (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) Q
  J_indep : iIndepFun J Q
  Z_indep_J : IndepFun Z (fun ω i ↦ J i ω) Q
  N_indep : IndepFun N (fun ω ↦ (Z ω, fun i ↦ J i ω)) Q

/-- `mertonVol n² · T = σ²T + nδ²`: the conditional log-variance over the horizon. -/
lemma mertonVol_sq_mul (σ δ : ℝ) {T : ℝ} (hT : 0 < T) (n : ℕ) :
    mertonVol σ δ T n ^ 2 * T = σ ^ 2 * T + n * δ ^ 2 := by
  have h0 : 0 ≤ σ ^ 2 + (n : ℝ) * δ ^ 2 / T := by positivity
  rw [mertonVol, Real.sq_sqrt h0, add_mul, div_mul_cancel₀ _ hT.ne']

/-- **Given `n` jumps, the jump-diffusion is a Black–Scholes economy.** The terminal price is the
Black–Scholes terminal price at the conditional spot `mertonSpot n` and volatility `mertonVol n`,
driven by `mertonStd`. -/
theorem mertonTerminal_eq_bsTerminal {S_0 r σ T k : ℝ} (δ : ℝ) (Λ : ℝ≥0) (hσ : 0 < σ)
    (hT : 0 < T) (hk : -1 < k) (z : ℝ) (n : ℕ) (j : ℕ → ℝ) :
    mertonTerminal S_0 r σ T k Λ z n j
      = bsTerminal (mertonSpot S_0 k Λ n) r (mertonVol σ δ T n) T (mertonStd σ T k δ z n j) := by
  have hvs : mertonVol σ δ T n * Real.sqrt T * mertonStd σ T k δ z n j
      = σ * Real.sqrt T * z + ∑ i ∈ Finset.range n, j i
        - n * (Real.log (1 + k) - δ ^ 2 / 2) :=
    mul_div_cancel₀ _ (mul_pos (mertonVol_pos hσ hT n) (Real.sqrt_pos.mpr hT)).ne'
  have h1k : 0 < 1 + k := by linarith
  have hpow : (1 + k) ^ n = rexp (n * Real.log (1 + k)) := by
    rw [Real.exp_nat_mul, Real.exp_log h1k]
  calc mertonTerminal S_0 r σ T k Λ z n j
      = S_0 * (rexp (-(k * (Λ : ℝ))) * (rexp (n * Real.log (1 + k))
          * rexp ((r - mertonVol σ δ T n ^ 2 / 2) * T
            + mertonVol σ δ T n * Real.sqrt T * mertonStd σ T k δ z n j))) := by
        rw [← Real.exp_add, ← Real.exp_add, mertonTerminal]
        congr 2
        linear_combination (1 / 2 : ℝ) * mertonVol_sq_mul σ δ hT n - hvs
    _ = bsTerminal (mertonSpot S_0 k Λ n) r (mertonVol σ δ T n) T
          (mertonStd σ T k δ z n j) := by
        rw [bsTerminal, mertonSpot, hpow]
        ring

/-- **The total log-shock, standardized, is standard normal.** With `n` jumps, `σ√T·Z` is
`N(0, σ²T)`, the sum of `n` log-jumps is `N(n(log(1 + k) − δ²/2), nδ²)`, and they are
independent, so `mertonStd` is `N(0, 1)`. -/
theorem MertonHyp.hasLaw_mertonStd [IsProbabilityMeasure Q] {k δ : ℝ} {Λ : ℝ≥0}
    {Z : Ω → ℝ} {N : Ω → ℕ} {J : ℕ → Ω → ℝ} (h : MertonHyp Q k δ Λ Z N J) {σ T : ℝ}
    (hσ : 0 < σ) (hT : 0 < T) (n : ℕ) :
    HasLaw (fun ω ↦ mertonStd σ T k δ (Z ω) n fun i ↦ J i ω) (gaussianReal 0 1) Q := by
  have hsum : HasLaw (fun ω ↦ ∑ i ∈ Finset.range n, J i ω)
      (gaussianReal (n * (Real.log (1 + k) - δ ^ 2 / 2)) (n * (δ ^ 2).toNNReal)) Q :=
    (hasLaw_sum_range_gaussianReal h.J_law h.J_indep n).congr
      (ae_of_all _ fun ω ↦ (Finset.sum_apply ω _ _).symm)
  have hind : IndepFun (fun ω ↦ σ * Real.sqrt T * Z ω)
      (fun ω ↦ ∑ i ∈ Finset.range n, J i ω) Q :=
    h.Z_indep_J.comp (φ := fun x ↦ σ * Real.sqrt T * x)
      (ψ := fun j : ℕ → ℝ ↦ ∑ i ∈ Finset.range n, j i) (by fun_prop) (by fun_prop)
  have hG := hind.hasLaw_fun_add (gaussianReal_const_mul h.Z_law (σ * Real.sqrt T)) hsum
  rw [gaussianReal_conv_gaussianReal, mul_zero, zero_add] at hG
  refine hasLaw_sub_div_of_gaussianReal hG
    (mul_pos (mertonVol_pos hσ hT n) (Real.sqrt_pos.mpr hT)) ?_
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, NNReal.coe_natCast,
    Real.coe_toNNReal _ (sq_nonneg δ)]
  linear_combination (σ ^ 2 - mertonVol σ δ T n ^ 2) * Real.sq_sqrt hT.le
    - mertonVol_sq_mul σ δ hT n

/-! ### Freezing the jump count -/

/-- **Freezing Merton's jump count.** For a nonnegative functional `F n z j` of the jump count,
the diffusion sample and the log-jumps, whose expectations `c n` with the count frozen at `n` are
integrable against `Poisson(Λ)`, the expectation of `F` at the random count is the Poisson mixture
`∫ n, c n ∂Poisson(Λ)`. -/
theorem MertonHyp.integral_eq_poisson_mixture [IsProbabilityMeasure Q] {k δ : ℝ} {Λ : ℝ≥0}
    {Z : Ω → ℝ} {N : Ω → ℕ} {J : ℕ → Ω → ℝ} (h : MertonHyp Q k δ Λ Z N J)
    {F : ℕ → ℝ → (ℕ → ℝ) → ℝ} (hFm : ∀ n, Measurable fun y : ℝ × (ℕ → ℝ) ↦ F n y.1 y.2)
    (hF0 : ∀ n z j, 0 ≤ F n z j) {c : ℕ → ℝ}
    (hint : ∀ n, Integrable (fun ω ↦ F n (Z ω) fun i ↦ J i ω) Q)
    (hc : ∀ n, ∫ ω, F n (Z ω) (fun i ↦ J i ω) ∂Q = c n)
    (hcint : Integrable c (poissonMeasure Λ)) :
    ∫ ω, F (N ω) (Z ω) (fun i ↦ J i ω) ∂Q = ∫ n, c n ∂(poissonMeasure Λ) :=
  integral_comp_of_hasLaw_poissonMeasure (F := fun n y ↦ F n y.1 y.2) h.N_law
    (h.Z_law.aemeasurable.prodMk (aemeasurable_pi_lambda _ fun i ↦ (h.J_law i).aemeasurable))
    h.N_indep hFm (fun n y ↦ hF0 n y.1 y.2) hint hc hcint

/-! ### The prices -/

/-- **The call, given `n` jumps.** With the jump count frozen at `n`, the discounted call payoff
has expectation `mertonCallTerm n`, the Black–Scholes price at spot `mertonSpot n` and
volatility `mertonVol n`. -/
theorem merton_call_given_jumps [IsProbabilityMeasure Q] {S_0 K r σ T k δ : ℝ} {Λ : ℝ≥0}
    {Z : Ω → ℝ} {N : Ω → ℕ} {J : ℕ → Ω → ℝ} (h : MertonHyp Q k δ Λ Z N J) (hS_0 : 0 < S_0)
    (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (hk : -1 < k) (n : ℕ) :
    ∫ ω, rexp (-r * T) * max (mertonTerminal S_0 r σ T k Λ (Z ω) n (fun i ↦ J i ω) - K) 0 ∂Q
      = mertonCallTerm S_0 K r σ T k δ Λ n := by
  simp_rw [mertonTerminal_eq_bsTerminal δ Λ hσ hT hk]
  exact bs_call_formula ⟨mertonSpot_pos hS_0 hk Λ n, hK, mertonVol_pos (δ := δ) hσ hT n, hT,
    h.hasLaw_mertonStd hσ hT n⟩

/-- **The put, given `n` jumps.** With the jump count frozen at `n`, the discounted put payoff
has expectation `mertonPutTerm n`. -/
theorem merton_put_given_jumps [IsProbabilityMeasure Q] {S_0 K r σ T k δ : ℝ} {Λ : ℝ≥0}
    {Z : Ω → ℝ} {N : Ω → ℕ} {J : ℕ → Ω → ℝ} (h : MertonHyp Q k δ Λ Z N J) (hS_0 : 0 < S_0)
    (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (hk : -1 < k) (n : ℕ) :
    ∫ ω, rexp (-r * T) * max (K - mertonTerminal S_0 r σ T k Λ (Z ω) n (fun i ↦ J i ω)) 0 ∂Q
      = mertonPutTerm S_0 K r σ T k δ Λ n := by
  simp_rw [mertonTerminal_eq_bsTerminal δ Λ hσ hT hk]
  exact bs_put_formula ⟨mertonSpot_pos hS_0 hk Λ n, hK, mertonVol_pos (δ := δ) hσ hT n, hT,
    h.hasLaw_mertonStd hσ hT n⟩

/-- **The discounted terminal price, given `n` jumps**, has expectation `mertonSpot n`: the
Black–Scholes forward `E[S_T] = spot·e^{rT}` at the conditional spot. -/
theorem merton_discounted_given_jumps [IsProbabilityMeasure Q] {S_0 r σ T k δ : ℝ} {Λ : ℝ≥0}
    {Z : Ω → ℝ} {N : Ω → ℕ} {J : ℕ → Ω → ℝ} (h : MertonHyp Q k δ Λ Z N J) (hσ : 0 < σ)
    (hT : 0 < T) (hk : -1 < k) (n : ℕ) :
    ∫ ω, rexp (-r * T) * mertonTerminal S_0 r σ T k Λ (Z ω) n (fun i ↦ J i ω) ∂Q
      = mertonSpot S_0 k Λ n := by
  have hmeas : Measurable (bsTerminal (mertonSpot S_0 k Λ n) r (mertonVol σ δ T n) T) := by
    unfold bsTerminal
    fun_prop
  have hfwd : ∫ ω, bsTerminal (mertonSpot S_0 k Λ n) r (mertonVol σ δ T n) T
        (mertonStd σ T k δ (Z ω) n fun i ↦ J i ω) ∂Q
      = mertonSpot S_0 k Λ n * rexp (r * T) :=
    ((h.hasLaw_mertonStd hσ hT n).integral_comp hmeas.aestronglyMeasurable).trans
      (integral_bsTerminal_eq_forward (mertonSpot S_0 k Λ n) r (mertonVol σ δ T n) T hT.le)
  simp_rw [mertonTerminal_eq_bsTerminal δ Λ hσ hT hk]
  rw [integral_const_mul, hfwd]
  calc rexp (-r * T) * (mertonSpot S_0 k Λ n * rexp (r * T))
      = mertonSpot S_0 k Λ n * rexp (-r * T + r * T) := by
        rw [Real.exp_add]
        ring
    _ = mertonSpot S_0 k Λ n := by
        rw [show -r * T + r * T = 0 by ring, Real.exp_zero, mul_one]

/-- **Merton's call formula, derived from the model.** The discounted expected call payoff of
the jump-diffusion terminal price is `mertonCallPrice`, the Poisson mixture of Black–Scholes
prices: `𝔼[e^{−rT}(S_T − K)⁺] = ∑ₙ e^{−Λ}Λⁿ/n! · C_BS(mertonSpot n, mertonVol n)`. -/
theorem merton_call_formula [IsProbabilityMeasure Q] {S_0 K r σ T k δ : ℝ} {Λ : ℝ≥0}
    {Z : Ω → ℝ} {N : Ω → ℕ} {J : ℕ → Ω → ℝ} (h : MertonHyp Q k δ Λ Z N J) (hS_0 : 0 < S_0)
    (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (hk : -1 < k) :
    ∫ ω, rexp (-r * T) * max (mertonTerminal S_0 r σ T k Λ (Z ω) (N ω) (fun i ↦ J i ω) - K) 0 ∂Q
      = mertonCallPrice S_0 K r σ T k δ Λ :=
  h.integral_eq_poisson_mixture
    (F := fun n z j ↦ rexp (-r * T) * max (mertonTerminal S_0 r σ T k Λ z n j - K) 0)
    (fun n ↦ by
      unfold mertonTerminal
      fun_prop)
    (fun _ _ _ ↦ mul_nonneg (Real.exp_pos _).le (le_max_right _ _))
    (fun n ↦ by
      simp_rw [mertonTerminal_eq_bsTerminal δ Λ hσ hT hk]
      exact integrable_bsCall_payoff (h.hasLaw_mertonStd hσ hT n)
        (mertonSpot_pos hS_0 hk Λ n).le hK.le r _ T)
    (merton_call_given_jumps h hS_0 hK hσ hT hk)
    (integrable_mertonCallTerm δ Λ hS_0 hK hσ hT hk)

/-- **Merton's put formula, derived from the model.** The discounted expected put payoff of the
jump-diffusion terminal price is `mertonPutPrice`. -/
theorem merton_put_formula [IsProbabilityMeasure Q] {S_0 K r σ T k δ : ℝ} {Λ : ℝ≥0}
    {Z : Ω → ℝ} {N : Ω → ℕ} {J : ℕ → Ω → ℝ} (h : MertonHyp Q k δ Λ Z N J) (hS_0 : 0 < S_0)
    (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (hk : -1 < k) :
    ∫ ω, rexp (-r * T) * max (K - mertonTerminal S_0 r σ T k Λ (Z ω) (N ω) (fun i ↦ J i ω)) 0 ∂Q
      = mertonPutPrice S_0 K r σ T k δ Λ :=
  h.integral_eq_poisson_mixture
    (F := fun n z j ↦ rexp (-r * T) * max (K - mertonTerminal S_0 r σ T k Λ z n j) 0)
    (fun n ↦ by
      unfold mertonTerminal
      fun_prop)
    (fun _ _ _ ↦ mul_nonneg (Real.exp_pos _).le (le_max_right _ _))
    (fun n ↦ by
      simp_rw [mertonTerminal_eq_bsTerminal δ Λ hσ hT hk]
      exact integrable_bsPut_payoff (h.hasLaw_mertonStd hσ hT n)
        (mertonSpot_pos hS_0 hk Λ n).le hK.le r _ T)
    (merton_put_given_jumps h hS_0 hK hσ hT hk)
    (integrable_mertonPutTerm δ Λ hS_0 hK hσ hT hk)

/-- **The compensator is the risk-neutral drift.** The discounted terminal price of the
jump-diffusion has mean `S₀`: given `n` jumps its mean is `mertonSpot n`, and the compensator
`e^{−kΛ}` makes those average back to `S₀` (`integral_mertonSpot`). -/
theorem merton_discounted_terminal [IsProbabilityMeasure Q] {S_0 r σ T k δ : ℝ} {Λ : ℝ≥0}
    {Z : Ω → ℝ} {N : Ω → ℕ} {J : ℕ → Ω → ℝ} (h : MertonHyp Q k δ Λ Z N J) (hS_0 : 0 < S_0)
    (hσ : 0 < σ) (hT : 0 < T) (hk : -1 < k) :
    ∫ ω, rexp (-r * T) * mertonTerminal S_0 r σ T k Λ (Z ω) (N ω) (fun i ↦ J i ω) ∂Q = S_0 :=
  (h.integral_eq_poisson_mixture
    (F := fun n z j ↦ rexp (-r * T) * mertonTerminal S_0 r σ T k Λ z n j)
    (fun n ↦ by
      unfold mertonTerminal
      fun_prop)
    (fun _ _ _ ↦ mul_nonneg (Real.exp_pos _).le (mul_nonneg hS_0.le (Real.exp_pos _).le))
    (fun n ↦ by
      simp_rw [mertonTerminal_eq_bsTerminal δ Λ hσ hT hk]
      exact (integrable_bsTerminal (h.hasLaw_mertonStd hσ hT n) _ r _ T).const_mul _)
    (merton_discounted_given_jumps h hσ hT hk)
    (integrable_mertonSpot Λ hS_0 hk)).trans (integral_mertonSpot S_0 k Λ)

end MathFin
