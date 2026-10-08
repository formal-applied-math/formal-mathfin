/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Actuarial.CompoundPoissonMGF
public import MathFin.BlackScholes.MertonModel
public import MathFin.BlackScholes.PriceBounds
public import MathFin.Foundations.NormalQuantile

/-!
# Jump-diffusions with an arbitrary jump law

`BlackScholes/MertonModel.lean` prices Merton's jump-diffusion, whose log-jumps are Gaussian, so
that with `n` jumps the terminal price is again a Black–Scholes terminal price. This file drops
the Gaussian law. Under the pricing measure the terminal price is

  `S_T = S₀ · exp((r − σ²/2)T − κ + σ√T·Z + ∑_{i<N} Jᵢ)`  (`jumpDiffusionTerminal`),

with `Z ∼ N(0, 1)`, a jump count `N ∼ Poisson(Λ)`, i.i.d. log-jumps `Jᵢ` of any law with
`𝔼[e^J] < ∞`, and a drift correction `κ`. The count is independent of the diffusion sample and
the jumps together, and the diffusion sample is independent of the jumps (`JumpDiffusionHyp`).

## Main results

* `jumpDiffusion_call_eq_integral_bsV`, the **mixing formula**: if the log-price is a Gaussian
  diffusion part plus an independent jump part `Y` with `𝔼[e^Y] < ∞`, then
  `𝔼[e^{−rT}(S₀e^{(r−σ²/2)T + σ√T·Z + Y} − K)⁺] = 𝔼[C_BS(S₀e^Y)]`. With `Y` frozen at `y`,
  the terminal price is a Black–Scholes terminal price at the spot `S₀e^y`.
* `jumpDiffusion_discounted_terminal`: the discounted terminal price has mean `S₀·𝔼[e^Y]`.
* `JumpDiffusionHyp.discounted_terminal`: for the compound-Poisson jump part `−κ + ∑_{i<N} Jᵢ`,
  `𝔼[e^{−rT}S_T] = S₀·e^{−κ + Λ(𝔼[e^J] − 1)}`.
* `JumpDiffusionHyp.discounted_terminal_eq_iff`, **the compensator**: `𝔼[e^{−rT}S_T] = S₀`
  exactly when `κ = Λ(𝔼[e^J] − 1)`.
* `JumpDiffusionHyp.call_poisson_mixture`, **Merton's formula for a general jump law** (Merton
  1976, eq. (16)): the call price is a Poisson mixture over the jump count `n` of Black–Scholes
  prices averaged over the jump sizes, `∫ n, 𝔼[C_BS(S₀e^{−κ + ∑_{i<n} Jᵢ})] ∂Poisson(Λ)`.

Merton's lognormal model is the Gaussian case. There `merton_call_given_jumps` prices the call
with the count frozen at `n` in closed form, and `merton_call_formula` sums the series.

## Scope

As in `MertonModel`, only the law of the price at maturity is modelled. The price process and
the martingale property of `e^{−rt}S_t` at intermediate dates are not constructed.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}

/-! ### The mixing formula -/

/-- With the jump part frozen at `y`, the terminal price is the Black–Scholes terminal price at
the spot `S₀e^y`. -/
lemma mul_exp_add_eq_bsTerminal (S_0 r σ T z y : ℝ) :
    S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * z + y)
      = bsTerminal (S_0 * rexp y) r σ T z := by
  rw [Real.exp_add _ y, bsTerminal]
  ring

/-- The Black–Scholes call price is measurable in the spot. -/
lemma measurable_bsV_spot (K r σ T : ℝ) : Measurable fun S ↦ bsV K r σ S T := by
  have := continuous_Phi.measurable
  unfold bsV bsd2 bsd1
  fun_prop

/-- The Black–Scholes call price is the discounted expected call payoff: `bs_call_formula`,
stated for `bsV`. -/
lemma integral_bsCall_payoff_eq_bsV [IsProbabilityMeasure Q] {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    ∫ ω, rexp (-r * T) * max (bsTerminal S_0 r σ T (Z ω) - K) 0 ∂Q = bsV K r σ S_0 T := by
  rw [bs_call_formula h, bsV, neg_mul]

/-- The terminal price of a jump-diffusion with an independent jump part `Y` is integrable when
`𝔼[e^Y] < ∞`: it is a constant times `e^{σ√T·Z}·e^Y`, a product of independent integrable
factors. -/
lemma integrable_jumpDiffusion_terminal {S_0 r σ T : ℝ} {Z Y : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) Q) (hYZ : IndepFun Y Z Q)
    (hexp : Integrable (fun ω ↦ rexp (Y ω)) Q) :
    Integrable (fun ω ↦ S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z ω + Y ω)) Q := by
  have hind : IndepFun (fun ω ↦ rexp (σ * Real.sqrt T * Z ω)) (fun ω ↦ rexp (Y ω)) Q :=
    hYZ.symm.comp (φ := fun z ↦ rexp (σ * Real.sqrt T * z)) (ψ := rexp) (by fun_prop)
      measurable_exp
  have hfun : (fun ω ↦ S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z ω + Y ω))
      = fun ω ↦ S_0 * rexp ((r - σ ^ 2 / 2) * T)
        * (rexp (σ * Real.sqrt T * Z ω) * rexp (Y ω)) := by
    funext ω
    rw [Real.exp_add _ (Y ω), Real.exp_add]
    ring
  rw [hfun]
  exact (hind.integrable_mul (integrable_exp_mul_of_hasLaw hZ _) hexp).const_mul _

/-- The discounted call payoff of a jump-diffusion with an independent jump part `Y` is
integrable when `𝔼[e^Y] < ∞`: it is dominated by the discounted terminal price. -/
lemma integrable_jumpDiffusion_call_payoff {S_0 K r σ T : ℝ} {Z Y : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) Q) (hY : AEMeasurable Y Q) (hYZ : IndepFun Y Z Q)
    (hexp : Integrable (fun ω ↦ rexp (Y ω)) Q) (hS_0 : 0 ≤ S_0) (hK : 0 ≤ K) :
    Integrable (fun ω ↦ rexp (-r * T)
      * max (S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z ω + Y ω) - K) 0) Q := by
  have hmeas : Measurable fun p : ℝ × ℝ ↦ rexp (-r * T)
      * max (S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * p.1 + p.2) - K) 0 := by
    fun_prop
  refine ((integrable_jumpDiffusion_terminal (S_0 := S_0) (r := r) (σ := σ) (T := T) hZ hYZ
    hexp).const_mul (rexp (-r * T))).mono'
    (hmeas.comp_aemeasurable (hZ.aemeasurable.prodMk hY)).aestronglyMeasurable
    (ae_of_all _ fun ω ↦ ?_)
  have hS : 0 ≤ S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z ω + Y ω) :=
    mul_nonneg hS_0 (Real.exp_pos _).le
  exact (Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (le_max_right _ _))).trans_le
    (mul_le_mul_of_nonneg_left (max_le (by linarith) hS) (Real.exp_pos _).le)

/-- **The mixing formula.** If the log-price is a Gaussian diffusion part plus an independent
jump part `Y` with `𝔼[e^Y] < ∞`, the discounted expected call payoff is the Black–Scholes price
averaged over the jump part:
`𝔼[e^{−rT}(S₀e^{(r−σ²/2)T + σ√T·Z + Y} − K)⁺] = 𝔼[C_BS(S₀e^Y)]`.
With `Y` frozen at `y` (`integral_comp_prodMk_of_indepFun`) the terminal price is a Black–Scholes
terminal price at the spot `S₀e^y`, which `bs_call_formula` prices. -/
theorem jumpDiffusion_call_eq_integral_bsV [IsProbabilityMeasure Q] {S_0 K r σ T : ℝ}
    {Z Y : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) Q) (hY : AEMeasurable Y Q)
    (hYZ : IndepFun Y Z Q) (hexp : Integrable (fun ω ↦ rexp (Y ω)) Q) (hS_0 : 0 < S_0)
    (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    ∫ ω, rexp (-r * T)
        * max (S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z ω + Y ω) - K) 0 ∂Q
      = ∫ ω, bsV K r σ (S_0 * rexp (Y ω)) T ∂Q := by
  have hgm : Measurable fun p : ℝ × ℝ ↦
      rexp (-r * T) * max (bsTerminal (S_0 * rexp p.1) r σ T p.2 - K) 0 := by
    unfold bsTerminal
    fun_prop
  have hint := integrable_jumpDiffusion_call_payoff (r := r) (σ := σ) (T := T) hZ hY hYZ hexp
    hS_0.le hK.le
  simp_rw [mul_exp_add_eq_bsTerminal] at hint ⊢
  have hprod := (integrable_comp_prodMk_iff_of_indepFun hYZ hY hZ.aemeasurable
    hgm.aestronglyMeasurable).mp hint
  have hbsV : Measurable fun y ↦ bsV K r σ (S_0 * rexp y) T :=
    (measurable_bsV_spot K r σ T).comp (by fun_prop)
  calc ∫ ω, rexp (-r * T) * max (bsTerminal (S_0 * rexp (Y ω)) r σ T (Z ω) - K) 0 ∂Q
      = ∫ y, ∫ ω, rexp (-r * T) * max (bsTerminal (S_0 * rexp y) r σ T (Z ω) - K) 0 ∂Q
          ∂(Q.map Y) := integral_comp_prodMk_of_indepFun hYZ hY hZ.aemeasurable hprod
    _ = ∫ y, bsV K r σ (S_0 * rexp y) T ∂(Q.map Y) := integral_congr_ae <| ae_of_all _ fun y ↦
        integral_bsCall_payoff_eq_bsV ⟨mul_pos hS_0 (Real.exp_pos y), hK, hσ, hT, hZ⟩
    _ = ∫ ω, bsV K r σ (S_0 * rexp (Y ω)) T ∂Q := integral_map hY hbsV.aestronglyMeasurable

/-- **The discounted terminal price** of a jump-diffusion with an independent jump part `Y` has
mean `S₀ · 𝔼[e^Y]`: the diffusion factor has mean `e^{rT}` and is independent of the jump
part. No integrability is assumed: when `𝔼[e^Y] = ∞` both sides are the Bochner integral's
`0`. -/
theorem jumpDiffusion_discounted_terminal {S_0 r σ T : ℝ} {Z Y : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) Q) (hY : AEMeasurable Y Q) (hYZ : IndepFun Y Z Q)
    (hT : 0 ≤ T) :
    ∫ ω, rexp (-r * T) * (S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z ω + Y ω)) ∂Q
      = S_0 * ∫ ω, rexp (Y ω) ∂Q := by
  have hmeas : Measurable (bsTerminal S_0 r σ T) := by
    unfold bsTerminal
    fun_prop
  have hind : IndepFun (fun ω ↦ bsTerminal S_0 r σ T (Z ω)) (fun ω ↦ rexp (Y ω)) Q :=
    hYZ.symm.comp (φ := bsTerminal S_0 r σ T) (ψ := rexp) hmeas measurable_exp
  have hfwd : ∫ ω, bsTerminal S_0 r σ T (Z ω) ∂Q = S_0 * rexp (r * T) :=
    (hZ.integral_comp hmeas.aestronglyMeasurable).trans
      (integral_bsTerminal_eq_forward S_0 r σ T hT)
  have hfun : (fun ω ↦ rexp (-r * T)
        * (S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * Z ω + Y ω)))
      = fun ω ↦ rexp (-r * T) * (bsTerminal S_0 r σ T (Z ω) * rexp (Y ω)) := by
    funext ω
    rw [Real.exp_add _ (Y ω), bsTerminal]
    ring
  rw [hfun, integral_const_mul, hind.integral_fun_mul_eq_mul_integral
    (hmeas.comp_aemeasurable hZ.aemeasurable).aestronglyMeasurable
    (measurable_exp.comp_aemeasurable hY).aestronglyMeasurable, hfwd]
  calc rexp (-r * T) * (S_0 * rexp (r * T) * ∫ ω, rexp (Y ω) ∂Q)
      = S_0 * (∫ ω, rexp (Y ω) ∂Q) * rexp (-r * T + r * T) := by
        rw [Real.exp_add]
        ring
    _ = S_0 * ∫ ω, rexp (Y ω) ∂Q := by
        rw [show -r * T + r * T = 0 by ring, Real.exp_zero, mul_one]

/-! ### Compound-Poisson jumps -/

/-- The terminal price of a jump-diffusion at a diffusion sample `z`, a jump count `n` and log-jump
sizes `j`, with drift correction `κ`: `S₀ · exp((r − σ²/2)T − κ + σ√T·z + ∑_{i<n} jᵢ)`.
Merton's `mertonTerminal` is this price with `κ = kΛ`. -/
noncomputable def jumpDiffusionTerminal (S_0 r σ T κ z : ℝ) (n : ℕ) (j : ℕ → ℝ) : ℝ :=
  S_0 * rexp ((r - σ ^ 2 / 2) * T - κ + σ * Real.sqrt T * z + ∑ i ∈ Finset.range n, j i)

/-- The jump-diffusion terminal price with the jump part `−κ + ∑_{i<n} jᵢ` split off. -/
lemma jumpDiffusionTerminal_eq (S_0 r σ T κ z : ℝ) (n : ℕ) (j : ℕ → ℝ) :
    jumpDiffusionTerminal S_0 r σ T κ z n j
      = S_0 * rexp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * z
        + (-κ + ∑ i ∈ Finset.range n, j i)) := by
  unfold jumpDiffusionTerminal
  congr 2
  ring

/-- **A jump-diffusion with an arbitrary jump law**: a standard normal diffusion sample `Z`, a
jump count `N ∼ Poisson(Λ)` and i.i.d. log-jump sizes `Jᵢ`, with the count independent of the
diffusion sample and the sizes together, and the diffusion sample independent of the sizes.
These are `MertonHyp`'s independence hypotheses, without its Gaussian jump law. -/
structure JumpDiffusionHyp (Q : Measure Ω) (Λ : ℝ≥0) (Z : Ω → ℝ) (N : Ω → ℕ)
    (J : ℕ → Ω → ℝ) : Prop where
  Z_law : HasLaw Z (gaussianReal 0 1) Q
  N_law : HasLaw N (poissonMeasure Λ) Q
  J_meas : ∀ i, Measurable (J i)
  J_indep : iIndepFun J Q
  J_ident : ∀ i, IdentDistrib (J i) (J 0) Q Q
  Z_indep_J : IndepFun Z (fun ω i ↦ J i ω) Q
  N_indep : IndepFun N (fun ω ↦ (Z ω, fun i ↦ J i ω)) Q

namespace JumpDiffusionHyp

variable {Λ : ℝ≥0} {Z : Ω → ℝ} {N : Ω → ℕ} {J : ℕ → Ω → ℝ}

/-- The diffusion sample and the jump sizes, taken together, form a measurable random element. -/
lemma aemeasurable_diffusion_jumps (h : JumpDiffusionHyp Q Λ Z N J) :
    AEMeasurable (fun ω ↦ (Z ω, fun i ↦ J i ω)) Q :=
  h.Z_law.aemeasurable.prodMk (measurable_pi_lambda _ h.J_meas).aemeasurable

/-- With the count frozen at `n`, the jump part `−κ + ∑_{i<n} Jᵢ` is measurable. -/
lemma measurable_jumps (h : JumpDiffusionHyp Q Λ Z N J) (κ : ℝ) (n : ℕ) :
    Measurable fun ω ↦ -κ + ∑ i ∈ Finset.range n, J i ω :=
  (show Measurable fun j : ℕ → ℝ ↦ -κ + ∑ i ∈ Finset.range n, j i by fun_prop).comp
    (measurable_pi_lambda _ h.J_meas)

/-- With the count frozen at `n`, the jump part `−κ + ∑_{i<n} Jᵢ` is independent of the
diffusion sample. -/
lemma indepFun_jumps (h : JumpDiffusionHyp Q Λ Z N J) (κ : ℝ) (n : ℕ) :
    IndepFun (fun ω ↦ -κ + ∑ i ∈ Finset.range n, J i ω) Z Q :=
  h.Z_indep_J.symm.comp (φ := fun j : ℕ → ℝ ↦ -κ + ∑ i ∈ Finset.range n, j i) (ψ := id)
    (by fun_prop) measurable_id

/-- With the count frozen at `n`, `e^{−κ + ∑_{i<n} Jᵢ}` is integrable when `𝔼[e^J] < ∞`. -/
lemma integrable_exp_jumps (h : JumpDiffusionHyp Q Λ Z N J)
    (hJ : Integrable (fun ω ↦ rexp (J 0 ω)) Q) (κ : ℝ) (n : ℕ) :
    Integrable (fun ω ↦ rexp (-κ + ∑ i ∈ Finset.range n, J i ω)) Q := by
  have h1 := integrable_exp_mul_sum_range_of_iid 1 J h.J_indep h.J_meas h.J_ident
    (by simpa only [one_mul] using hJ) n
  simp_rw [one_mul] at h1
  simp_rw [Real.exp_add]
  exact h1.const_mul _

/-- With the count frozen at `n`, `𝔼[e^{−κ + ∑_{i<n} Jᵢ}] = e^{−κ}·𝔼[e^J]ⁿ`. -/
lemma integral_exp_jumps (h : JumpDiffusionHyp Q Λ Z N J) (κ : ℝ) (n : ℕ) :
    ∫ ω, rexp (-κ + ∑ i ∈ Finset.range n, J i ω) ∂Q
      = rexp (-κ) * (∫ ω, rexp (J 0 ω) ∂Q) ^ n := by
  have h1 := mgf_range_sum_of_iid 1 J h.J_indep h.J_meas h.J_ident n
  simp only [mgf, one_mul] at h1
  simp_rw [Real.exp_add]
  rw [integral_const_mul, h1]

/-- **The discounted terminal price, given `n` jumps**, has mean `S₀e^{−κ}𝔼[e^J]ⁿ`. -/
theorem discounted_terminal_given_jumps (h : JumpDiffusionHyp Q Λ Z N J) (S_0 r σ : ℝ)
    {T : ℝ} (hT : 0 ≤ T) (κ : ℝ) (n : ℕ) :
    ∫ ω, rexp (-r * T) * jumpDiffusionTerminal S_0 r σ T κ (Z ω) n (fun i ↦ J i ω) ∂Q
      = S_0 * (rexp (-κ) * (∫ ω, rexp (J 0 ω) ∂Q) ^ n) := by
  simp_rw [jumpDiffusionTerminal_eq]
  rw [jumpDiffusion_discounted_terminal h.Z_law (h.measurable_jumps κ n).aemeasurable
    (h.indepFun_jumps κ n) hT, h.integral_exp_jumps κ n]

/-- With the count frozen at `n`, the discounted terminal price is integrable when
`𝔼[e^J] < ∞`. -/
lemma integrable_discounted_terminal_given_jumps (h : JumpDiffusionHyp Q Λ Z N J)
    (hJ : Integrable (fun ω ↦ rexp (J 0 ω)) Q) (S_0 r σ T κ : ℝ) (n : ℕ) :
    Integrable (fun ω ↦ rexp (-r * T)
      * jumpDiffusionTerminal S_0 r σ T κ (Z ω) n (fun i ↦ J i ω)) Q := by
  simp_rw [jumpDiffusionTerminal_eq]
  exact (integrable_jumpDiffusion_terminal h.Z_law (h.indepFun_jumps κ n)
    (h.integrable_exp_jumps hJ κ n)).const_mul _

/-- **The discounted terminal price** has mean `S₀·e^{−κ + Λ(𝔼[e^J] − 1)}`. Given `n` jumps the
mean is `S₀e^{−κ}𝔼[e^J]ⁿ` (`discounted_terminal_given_jumps`), and the Poisson probability
generating function sums these. -/
theorem discounted_terminal [IsProbabilityMeasure Q] (h : JumpDiffusionHyp Q Λ Z N J)
    (hJ : Integrable (fun ω ↦ rexp (J 0 ω)) Q) {S_0 : ℝ} (hS_0 : 0 ≤ S_0) (r σ : ℝ) {T : ℝ}
    (hT : 0 ≤ T) (κ : ℝ) :
    ∫ ω, rexp (-r * T) * jumpDiffusionTerminal S_0 r σ T κ (Z ω) (N ω) (fun i ↦ J i ω) ∂Q
      = S_0 * rexp (-κ + Λ * (∫ ω, rexp (J 0 ω) ∂Q - 1)) := by
  calc ∫ ω, rexp (-r * T) * jumpDiffusionTerminal S_0 r σ T κ (Z ω) (N ω) (fun i ↦ J i ω) ∂Q
      = ∫ n, S_0 * (rexp (-κ) * (∫ ω, rexp (J 0 ω) ∂Q) ^ n) ∂(poissonMeasure Λ) :=
        integral_comp_of_hasLaw_poissonMeasure
          (F := fun n p ↦ rexp (-r * T) * jumpDiffusionTerminal S_0 r σ T κ p.1 n p.2)
          h.N_law h.aemeasurable_diffusion_jumps h.N_indep
          (fun n ↦ by
            unfold jumpDiffusionTerminal
            fun_prop)
          (fun _ _ ↦ mul_nonneg (Real.exp_pos _).le (mul_nonneg hS_0 (Real.exp_pos _).le))
          (fun n ↦ h.integrable_discounted_terminal_given_jumps hJ S_0 r σ T κ n)
          (fun n ↦ h.discounted_terminal_given_jumps S_0 r σ hT κ n)
          (((PoissonPgf.integrable_pow_poissonMeasure Λ _).const_mul _).const_mul _)
    _ = S_0 * rexp (-κ + Λ * (∫ ω, rexp (J 0 ω) ∂Q - 1)) := by
        rw [integral_const_mul, integral_const_mul, PoissonPgf.integral_pow_poissonMeasure,
          ← Real.exp_add]

/-- **The compensator.** The discounted terminal price has mean `S₀` exactly when the drift
correction is `κ = Λ(𝔼[e^J] − 1)`, the expected number of jumps times the mean relative jump
`𝔼[e^J − 1]`. -/
theorem discounted_terminal_eq_iff [IsProbabilityMeasure Q] (h : JumpDiffusionHyp Q Λ Z N J)
    (hJ : Integrable (fun ω ↦ rexp (J 0 ω)) Q) {S_0 : ℝ} (hS_0 : 0 < S_0) (r σ : ℝ) {T : ℝ}
    (hT : 0 ≤ T) (κ : ℝ) :
    ∫ ω, rexp (-r * T) * jumpDiffusionTerminal S_0 r σ T κ (Z ω) (N ω) (fun i ↦ J i ω) ∂Q = S_0
      ↔ κ = Λ * (∫ ω, rexp (J 0 ω) ∂Q - 1) := by
  rw [h.discounted_terminal hJ hS_0.le r σ hT κ, mul_eq_left₀ hS_0.ne', Real.exp_eq_one_iff,
    neg_add_eq_zero]

/-- **The call, given `n` jumps.** With the count frozen at `n`, the discounted call payoff has
expectation `𝔼[C_BS(S₀e^{−κ + ∑_{i<n} Jᵢ})]`: the mixing formula for the jump part
`−κ + ∑_{i<n} Jᵢ`. -/
theorem call_given_jumps [IsProbabilityMeasure Q] (h : JumpDiffusionHyp Q Λ Z N J)
    (hJ : Integrable (fun ω ↦ rexp (J 0 ω)) Q) {S_0 K r σ T : ℝ} (hS_0 : 0 < S_0) (hK : 0 < K)
    (hσ : 0 < σ) (hT : 0 < T) (κ : ℝ) (n : ℕ) :
    ∫ ω, rexp (-r * T) * max (jumpDiffusionTerminal S_0 r σ T κ (Z ω) n (fun i ↦ J i ω) - K) 0 ∂Q
      = ∫ ω, bsV K r σ (S_0 * rexp (-κ + ∑ i ∈ Finset.range n, J i ω)) T ∂Q := by
  simp_rw [jumpDiffusionTerminal_eq]
  exact jumpDiffusion_call_eq_integral_bsV h.Z_law (h.measurable_jumps κ n).aemeasurable
    (h.indepFun_jumps κ n) (h.integrable_exp_jumps hJ κ n) hS_0 hK hσ hT

/-- With the count frozen at `n`, the discounted call payoff is integrable when `𝔼[e^J] < ∞`. -/
lemma integrable_call_payoff_given_jumps (h : JumpDiffusionHyp Q Λ Z N J)
    (hJ : Integrable (fun ω ↦ rexp (J 0 ω)) Q) {S_0 K : ℝ} (hS_0 : 0 ≤ S_0) (hK : 0 ≤ K)
    (r σ T κ : ℝ) (n : ℕ) :
    Integrable (fun ω ↦ rexp (-r * T)
      * max (jumpDiffusionTerminal S_0 r σ T κ (Z ω) n (fun i ↦ J i ω) - K) 0) Q := by
  simp_rw [jumpDiffusionTerminal_eq]
  exact integrable_jumpDiffusion_call_payoff h.Z_law (h.measurable_jumps κ n).aemeasurable
    (h.indepFun_jumps κ n) (h.integrable_exp_jumps hJ κ n) hS_0 hK

/-- With the count frozen at `n`, `C_BS(S₀e^{−κ + ∑_{i<n} Jᵢ})` is integrable: it lies between
`0` and `S₀e^{−κ + ∑_{i<n} Jᵢ}`. -/
lemma integrable_bsV_given_jumps [IsProbabilityMeasure Q] (h : JumpDiffusionHyp Q Λ Z N J)
    (hJ : Integrable (fun ω ↦ rexp (J 0 ω)) Q) {S_0 K r σ T : ℝ} (hS_0 : 0 < S_0) (hK : 0 < K)
    (hσ : 0 < σ) (hT : 0 < T) (κ : ℝ) (n : ℕ) :
    Integrable (fun ω ↦ bsV K r σ (S_0 * rexp (-κ + ∑ i ∈ Finset.range n, J i ω)) T) Q := by
  refine ((h.integrable_exp_jumps hJ κ n).const_mul S_0).mono'
    ((measurable_bsV_spot K r σ T).comp
      ((h.measurable_jumps κ n).exp.const_mul S_0)).aestronglyMeasurable
    (ae_of_all _ fun ω ↦ ?_)
  have hS : 0 < S_0 * rexp (-κ + ∑ i ∈ Finset.range n, J i ω) := mul_pos hS_0 (Real.exp_pos _)
  exact (Real.norm_of_nonneg (bsV_nonneg (r := r) ⟨hS, hK, hσ, hT, h.Z_law⟩)).trans_le
    (bsV_le_S K r σ _ T hS.le hK.le)

/-- The averaged Black–Scholes prices given `n` jumps are integrable against `Poisson(Λ)`: the
`n`-th lies between `0` and `S₀e^{−κ}𝔼[e^J]ⁿ`. -/
lemma integrable_call_given_jumps [IsProbabilityMeasure Q] (h : JumpDiffusionHyp Q Λ Z N J)
    (hJ : Integrable (fun ω ↦ rexp (J 0 ω)) Q) {S_0 K r σ T : ℝ} (hS_0 : 0 < S_0) (hK : 0 < K)
    (hσ : 0 < σ) (hT : 0 < T) (κ : ℝ) :
    Integrable (fun n ↦ ∫ ω, bsV K r σ (S_0 * rexp (-κ + ∑ i ∈ Finset.range n, J i ω)) T ∂Q)
      (poissonMeasure Λ) := by
  refine (((PoissonPgf.integrable_pow_poissonMeasure Λ (∫ ω, rexp (J 0 ω) ∂Q)).const_mul
    (rexp (-κ))).const_mul S_0).mono' Measurable.of_discrete.aestronglyMeasurable
    (ae_of_all _ fun n ↦ ?_)
  have hnonneg : 0 ≤ ∫ ω, bsV K r σ (S_0 * rexp (-κ + ∑ i ∈ Finset.range n, J i ω)) T ∂Q :=
    integral_nonneg fun ω ↦
      bsV_nonneg (r := r) ⟨mul_pos hS_0 (Real.exp_pos _), hK, hσ, hT, h.Z_law⟩
  have hle : ∫ ω, bsV K r σ (S_0 * rexp (-κ + ∑ i ∈ Finset.range n, J i ω)) T ∂Q
      ≤ S_0 * (rexp (-κ) * (∫ ω, rexp (J 0 ω) ∂Q) ^ n) := by
    rw [← h.integral_exp_jumps κ n, ← integral_const_mul]
    exact integral_mono (h.integrable_bsV_given_jumps hJ hS_0 hK hσ hT κ n)
      ((h.integrable_exp_jumps hJ κ n).const_mul S_0) fun ω ↦
        bsV_le_S K r σ _ T (mul_pos hS_0 (Real.exp_pos _)).le hK.le
  exact (Real.norm_of_nonneg hnonneg).trans_le hle

/-- **Merton's formula for a general jump law** (Merton 1976, eq. (16)). The discounted expected
call payoff of the jump-diffusion is the Poisson mixture, over the jump count `n`, of the
Black–Scholes price averaged over the jump sizes:
`𝔼[e^{−rT}(S_T − K)⁺] = ∫ n, 𝔼[C_BS(S₀e^{−κ + ∑_{i<n} Jᵢ})] ∂Poisson(Λ)`. -/
theorem call_poisson_mixture [IsProbabilityMeasure Q] (h : JumpDiffusionHyp Q Λ Z N J)
    (hJ : Integrable (fun ω ↦ rexp (J 0 ω)) Q) {S_0 K r σ T : ℝ} (hS_0 : 0 < S_0) (hK : 0 < K)
    (hσ : 0 < σ) (hT : 0 < T) (κ : ℝ) :
    ∫ ω, rexp (-r * T)
        * max (jumpDiffusionTerminal S_0 r σ T κ (Z ω) (N ω) (fun i ↦ J i ω) - K) 0 ∂Q
      = ∫ n, ∫ ω, bsV K r σ (S_0 * rexp (-κ + ∑ i ∈ Finset.range n, J i ω)) T ∂Q
          ∂(poissonMeasure Λ) :=
  integral_comp_of_hasLaw_poissonMeasure
    (F := fun n p ↦ rexp (-r * T) * max (jumpDiffusionTerminal S_0 r σ T κ p.1 n p.2 - K) 0)
    h.N_law h.aemeasurable_diffusion_jumps h.N_indep
    (fun n ↦ by
      unfold jumpDiffusionTerminal
      fun_prop)
    (fun _ _ ↦ mul_nonneg (Real.exp_pos _).le (le_max_right _ _))
    (fun n ↦ h.integrable_call_payoff_given_jumps hJ hS_0.le hK.le r σ T κ n)
    (fun n ↦ h.call_given_jumps hJ hS_0 hK hσ hT κ n)
    (h.integrable_call_given_jumps hJ hS_0 hK hσ hT κ)

end JumpDiffusionHyp

end MathFin
