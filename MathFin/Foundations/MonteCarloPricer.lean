/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.StandardNormal
public import MathFin.BlackScholes.Put

/-!
# Monte Carlo pricing of the European put

The estimator theorem every desk prices by. For a standard-normal ensemble
`Z : ℕ → Ω → ℝ` and the discounted European put payoff

  `payoff z = e^{-rT} · max(K − S_T(z), 0)`,   `S_T z = bsTerminal S₀ r σ T z`,

this module proves, end to end:

* **Consistency (strong law).** the sample-mean estimator converges almost surely to
  `𝔼[payoff]` — which, by `bs_put_formula`, is exactly the Black–Scholes put price
  `K·e^{-rT}·Φ(−d₂) − S₀·Φ(−d₁)`. The law used is Mathlib's Etemadi strong law
  (`strong_law_ae_real`): only **pairwise** independence is hypothesised, so
  antithetic-pair samplers keep consistency (`consistency`); full independence gives
  the familiar specialization (`consistency_iid`).
* **Error bars (CLT).** `√n · (estimator n − P) ⇒ 𝓝(0, σ_H²)` in distribution via
  Mathlib's `tendstoInDistribution_inv_sqrt_mul_sum_sub` (`clt`, library form
  `clt_library`), with the limit variance **identified in closed form** (`variance`):
  `σ_H² = e^{-2rT}·M₂ − P²`, where

    `M₂ = K²·Φ(−d₂) − 2·K·S₀·e^{μ+ν²/2}·Φ(−d₁) + S₀²·e^{2μ+2ν²}·Φ(−d₁−ν)`,

  with `μ = (r − σ²/2)T`, `ν = σ√T` — the truncated second moment of the lognormal
  (`secondMoment_payoff`, computed from `integral_exp_mul_gaussianPDFReal_Iic`, the
  same completing-the-square atom `Put.lean` prices with), discounted (`secondMoment`).
* **The BS bridge.** the mean of one sampled payoff is the put price itself
  (`mean_eq_bsPut`), and the payoff is bounded (`0 ≤ payoff ≤ e^{-rT}·K`,
  `payoff_le`), which licenses integrability (`integrable_payoff`) and `L²`
  membership (`memLp2_payoff`) — exactly the strong-law and CLT hypotheses.

Honest scoping: the ensemble is hypothesized, not constructed — `consistency` takes
pairwise independence (`∀ i j, i ≠ j → Z i ⟂ᵢ[μ] Z j`) plus identical standard-normal
laws, `consistency_iid`/`clt` take the i.i.d. bundle `iIndepFun Z μ`; the
countable-product *construction* is future substrate. Variance reduction and
multi-dimensional payoffs are future layers.

## Result

Public API (all in `namespace MathFin.MonteCarlo`):

* `payoff` — the discounted European put payoff as a function of the draw;
* `estimator` — the sample-mean Monte Carlo estimator over `n` draws;
* `payoff_le` — the discounted-strike pointwise bound `payoff ≤ e^{-rT}·K`;
* `integrable_payoff`, `memLp2_payoff` — the strong-law (`L¹`) and CLT (`L²`)
  integrability of the sampled payoff;
* `mean_eq_bsPut` — the bridge: `𝔼[payoff] = K·e^{-rT}·Φ(−d₂) − S₀·Φ(−d₁)`;
* `consistency` — a.s. convergence of the estimator to the Black–Scholes put price
  under **pairwise** independence (Etemadi's strong law);
* `consistency_iid` — the full-independence specialization;
* `clt_library` — the library-form CLT `(√n)⁻¹·(∑_{i<n} payoff − n·P) ⇒ 𝓝(0, σ_H²)`;
  `clt` — the desk form `√n·(estimator n − P) ⇒ 𝓝(0, σ_H²)`;
* `secondMoment_payoff` — the truncated second moment of the lognormal payoff in
  closed form; `secondMoment` — the discounted second moment `𝔼[payoff²]`;
* `variance` — the CLT limit variance in closed form:
  `σ_H² = e^{-2rT}·M₂ − P²`.

Supporting lemmas (nonnegativity, measurability, law/independence transfer through
the payoff map, the integral-linearity workhorse `integral_lin_comb3`, the estimator
algebra `inv_sqrt_mul_sub_eq`) are `private`.
-/

@[expose] public section

namespace MathFin.MonteCarlo

open MeasureTheory ProbabilityTheory Real MathFin Filter Function
open scoped NNReal ENNReal Topology

/-- The discounted European put payoff as a function of the standard-normal draw:
`H(z) = e^{-rT} · max(K − S_T(z), 0)` with the MathFin terminal map
`S_T(z) = S₀ · exp((r − σ²/2)T + σ√T·z)`. -/
noncomputable def payoff (S_0 K r σ T z : ℝ) : ℝ :=
  Real.exp (-r * T) * max (K - bsTerminal S_0 r σ T z) 0

/-- The terminal map is nonnegative (it is `S₀ · exp(·)`). -/
private lemma terminal_nonneg (hS_0 : 0 ≤ S_0) (r σ T z : ℝ) :
    0 ≤ bsTerminal S_0 r σ T z := by
  unfold bsTerminal
  exact mul_nonneg hS_0 (Real.exp_pos _).le

/-- The discounted put payoff is nonnegative. -/
private lemma payoff_nonneg (S_0 K r σ T z : ℝ) : 0 ≤ payoff S_0 K r σ T z := by
  unfold payoff
  exact mul_nonneg (Real.exp_pos _).le (le_max_right _ _)

/-- **The put payoff is bounded above** by the discounted strike: `H ≤ e^{-rT}·K`.
This boundedness (a put is the easy case of integrability) is what licenses the
strong law and the CLT. -/
theorem payoff_le (hS_0 : 0 < S_0) (hK : 0 ≤ K) (r σ T z : ℝ) :
    payoff S_0 K r σ T z ≤ Real.exp (-r * T) * K := by
  unfold payoff
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  refine max_le ?_ hK
  exact (sub_le_self_iff K).2 (terminal_nonneg hS_0.le r σ T z)

/-- The payoff is a measurable (indeed continuous) function of the draw. -/
private lemma measurable_payoff (S_0 K r σ T : ℝ) : Measurable (payoff S_0 K r σ T) := by
  unfold payoff bsTerminal
  fun_prop

section Ensemble
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {S_0 K r σ T : ℝ}

/-- Single draw: the sampled payoff is a.e. strongly measurable. Its law is the
pushforward of the standard normal through `payoff`. -/
private theorem aestronglyMeasurable_payoff {Z : Ω → ℝ} (h : BSCallHyp μ S_0 K r σ T Z) :
    AEStronglyMeasurable (fun ω => payoff S_0 K r σ T (Z ω)) μ :=
  ((HasLaw.comp (Y := payoff S_0 K r σ T)
      (⟨(measurable_payoff S_0 K r σ T).aemeasurable, rfl⟩ :
        HasLaw (payoff S_0 K r σ T) ((gaussianReal 0 1).map (payoff S_0 K r σ T))
          (gaussianReal 0 1))
      h.Z_law).aemeasurable.aestronglyMeasurable)

/-- **Integrability**: the sampled put payoff is integrable, by the pointwise bound
`0 ≤ H ≤ e^{-rT}·K` on a probability space. -/
theorem integrable_payoff {Z : Ω → ℝ} (h : BSCallHyp μ S_0 K r σ T Z) :
    Integrable (fun ω => payoff S_0 K r σ T (Z ω)) μ := by
  refine memLp_one_iff_integrable.1 ?_
  refine MemLp.of_bound (C := Real.exp (-r * T) * K)
    (aestronglyMeasurable_payoff h) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (payoff_nonneg S_0 K r σ T _)]
  exact payoff_le h.S_0_pos h.K_pos.le r σ T _

/-- The sampled payoff is in L² — the CLT hypothesis. -/
theorem memLp2_payoff {Z : Ω → ℝ} (h : BSCallHyp μ S_0 K r σ T Z) :
    MemLp (fun ω => payoff S_0 K r σ T (Z ω)) 2 μ := by
  refine MemLp.of_bound (C := Real.exp (-r * T) * K)
    (aestronglyMeasurable_payoff h) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (payoff_nonneg S_0 K r σ T _)]
  exact payoff_le h.S_0_pos h.K_pos.le r σ T _

/-- The mean of one sampled payoff is the Black–Scholes put price: this is MathFin's
`bs_put_formula` — the discounted expectation IS the closed form. -/
theorem mean_eq_bsPut {Z : Ω → ℝ} (h : BSCallHyp μ S_0 K r σ T Z) :
    ∫ ω, payoff S_0 K r σ T (Z ω) ∂μ
      = K * Real.exp (-r * T) * Phi (-(bsd2 S_0 K r σ T))
        - S_0 * Phi (-(bsd1 S_0 K r σ T)) := by
  simpa only [payoff] using bs_put_formula h

/-! ### The ensemble: independence and identical distribution transfer -/

variable {Z : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
/-- All sampled payoffs have the same pushforward law. -/
private theorem hasLaw_payoff (hlaw : ∀ i : ℕ, HasLaw (Z i) (gaussianReal 0 1) μ) (i : ℕ) :
    HasLaw (fun ω => payoff S_0 K r σ T (Z i ω))
      ((gaussianReal 0 1).map (payoff S_0 K r σ T)) μ :=
  HasLaw.comp (Y := payoff S_0 K r σ T)
    (⟨(measurable_payoff S_0 K r σ T).aemeasurable, rfl⟩ :
      HasLaw (payoff S_0 K r σ T) ((gaussianReal 0 1).map (payoff S_0 K r σ T))
        (gaussianReal 0 1))
    (hlaw i)

omit [IsProbabilityMeasure μ] in
/-- The sampled payoffs are identically distributed. -/
private theorem identDistrib_payoff (hlaw : ∀ i : ℕ, HasLaw (Z i) (gaussianReal 0 1) μ)
    (i : ℕ) :
    IdentDistrib (fun ω => payoff S_0 K r σ T (Z i ω))
      (fun ω => payoff S_0 K r σ T (Z 0 ω)) μ μ :=
  HasLaw.identDistrib (hasLaw_payoff hlaw i) (hasLaw_payoff hlaw 0)

omit [IsProbabilityMeasure μ] in
/-- Full independence of the ensemble transfers through the payoff map. -/
private theorem iIndepFun_payoff (hindep : iIndepFun Z μ) :
    iIndepFun (fun i => fun ω => payoff S_0 K r σ T (Z i ω)) μ :=
  hindep.comp (fun _ => payoff S_0 K r σ T)
    (fun _ => measurable_payoff S_0 K r σ T)

omit [IsProbabilityMeasure μ] in
/-- Pairwise independence of the ensemble transfers through the payoff map — the
Etemadi hypothesis the strong law consumes. (Stated in unfolded `∀` form: `open
Filter` shadows the root `Pairwise`.) -/
private theorem pairwise_payoff (hindep : _root_.Pairwise ((· ⟂ᵢ[μ] ·) on Z)) :
    ∀ i j : ℕ, i ≠ j →
      (fun ω => payoff S_0 K r σ T (Z i ω)) ⟂ᵢ[μ] (fun ω => payoff S_0 K r σ T (Z j ω)) := by
  intro i j hij
  exact (hindep hij).comp (measurable_payoff S_0 K r σ T)
    (measurable_payoff S_0 K r σ T)

/-- The Monte Carlo estimator: the sample mean of `n` discounted put payoffs. -/
noncomputable def estimator (S_0 K r σ T : ℝ) {Ω : Type*} (Z : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, payoff S_0 K r σ T (Z i ω)) / (n : ℝ)

/-! ### Consistency (strong law, Etemadi pairwise form) -/

/-- **Monte Carlo consistency for the put.**

Under only **pairwise** independence of the standard-normal ensemble (Etemadi's
strong law — the honest hypothesis, so negatively-correlated antithetic pairs
keep consistency) and the risk-neutral lognormal model, the sample-mean estimator
converges almost surely to the Black–Scholes put price
`K·e^{-rT}·Φ(−d₂) − S₀·Φ(−d₁)`. -/
theorem consistency (h : BSCallHyp μ S_0 K r σ T (Z 0))
    (hlaw : ∀ i : ℕ, HasLaw (Z i) (gaussianReal 0 1) μ)
    (hindep : _root_.Pairwise ((· ⟂ᵢ[μ] ·) on Z)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => estimator S_0 K r σ T Z n ω) atTop
      (𝓝 (K * Real.exp (-r * T) * Phi (-(bsd2 S_0 K r σ T))
        - S_0 * Phi (-(bsd1 S_0 K r σ T)))) := by
  have hint : Integrable (fun ω => payoff S_0 K r σ T (Z 0 ω)) μ :=
    integrable_payoff h
  have hslln := strong_law_ae_real
    (X := fun i => fun ω => payoff S_0 K r σ T (Z i ω))
    hint (pairwise_payoff hindep) (fun i => identDistrib_payoff hlaw i)
  filter_upwards [hslln] with ω hω
  rw [← mean_eq_bsPut (Z := Z 0) h]
  exact hω.congr fun _ => rfl

/-- The i.i.d. specialization: full independence gives the pairwise hypothesis. -/
theorem consistency_iid (h : BSCallHyp μ S_0 K r σ T (Z 0))
    (hlaw : ∀ i : ℕ, HasLaw (Z i) (gaussianReal 0 1) μ)
    (hindep : iIndepFun Z μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => estimator S_0 K r σ T Z n ω) atTop
      (𝓝 (K * Real.exp (-r * T) * Phi (-(bsd2 S_0 K r σ T))
        - S_0 * Phi (-(bsd1 S_0 K r σ T)))) := by
  refine consistency h hlaw ?_
  intro i j hij
  exact hindep.indepFun hij

/-! ### Error bars (CLT) -/

/-- **Monte Carlo error bars** — the library-form CLT:
`(√n)⁻¹ · (∑_{i<n} H(Z i) − n·P) ⇒ 𝓝(0, σ_H²)` in distribution, where the limit
variance `σ_H² = Var(H)` is identified by the theorem itself (the closed form is
`variance` below). Full independence is genuinely needed here — this is the
statement that variance-reduction schemes must re-prove for their dependent
sequences. -/
theorem clt_library (h : BSCallHyp μ S_0 K r σ T (Z 0))
    (hlaw : ∀ i : ℕ, HasLaw (Z i) (gaussianReal 0 1) μ)
    (hindep : iIndepFun Z μ)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Y : Ω' → ℝ}
    (hY : HasLaw Y
      (gaussianReal 0 (Var[fun ω => payoff S_0 K r σ T (Z 0 ω); μ]).toNNReal) μ') :
    TendstoInDistribution
      (fun (n : ℕ) (ω : Ω) => (Real.sqrt (n : ℝ))⁻¹ *
        (∑ i ∈ Finset.range n, payoff S_0 K r σ T (Z i ω)
          - (n : ℝ) * ∫ ω', payoff S_0 K r σ T (Z 0 ω') ∂μ))
      atTop Y (fun _ => μ) μ' :=
  tendstoInDistribution_inv_sqrt_mul_sum_sub hY (memLp2_payoff h)
    (iIndepFun_payoff hindep) (fun i => identDistrib_payoff hlaw i)

/-- The algebraic identity equating the library CLT integrand with the desk
estimator: `(√n)⁻¹·(s − n·m) = √n·(s/n − m)`. -/
private lemma inv_sqrt_mul_sub_eq (s m n : ℝ) (hn : 0 ≤ n) :
    (Real.sqrt n)⁻¹ * (s - n * m) = Real.sqrt n * (s / n - m) := by
  rcases eq_or_lt_of_le hn with h0 | hpos
  · subst h0
    simp
  have hn0 : n ≠ 0 := ne_of_gt hpos
  have hnz : Real.sqrt n ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  field_simp [Real.mul_self_sqrt hn]
  rw [Real.sq_sqrt hn]

/-- **Monte Carlo error bars, desk form**: `√n · (estimator n − P) ⇒ 𝓝(0, σ_H²)` in
distribution, against the 𝓝(0, σ_H²) limit — the law is
`gaussianReal 0 (Var[payoff ∘ Z 0; μ]).toNNReal`, not the standard normal. -/
theorem clt (h : BSCallHyp μ S_0 K r σ T (Z 0))
    (hlaw : ∀ i : ℕ, HasLaw (Z i) (gaussianReal 0 1) μ)
    (hindep : iIndepFun Z μ) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : Ω) => Real.sqrt (n : ℝ) *
        (estimator S_0 K r σ T Z n ω - ∫ ω', payoff S_0 K r σ T (Z 0 ω') ∂μ))
      atTop (id : ℝ → ℝ) (fun _ => μ)
      (gaussianReal 0 (Var[fun ω => payoff S_0 K r σ T (Z 0 ω); μ]).toNNReal) := by
  have hlib := clt_library (μ' := gaussianReal 0
      (Var[fun ω => payoff S_0 K r σ T (Z 0 ω); μ]).toNNReal) (Y := (id : ℝ → ℝ))
    h hlaw hindep ⟨by fun_prop, Measure.map_id⟩
  refine TendstoInDistribution.congr (fun n => ?_) Filter.EventuallyEq.rfl hlib
  filter_upwards with ω
  simp only [estimator]
  exact inv_sqrt_mul_sub_eq (∑ i ∈ Finset.range n, payoff S_0 K r σ T (Z i ω))
    (∫ ω', payoff S_0 K r σ T (Z 0 ω') ∂μ) (n : ℝ) (by positivity)

end Ensemble

/-! ### The variance, in closed form

The single-draw section: `Z : Ω → ℝ` is one standard-normal sample. -/

section Moments
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {S_0 K r σ T : ℝ} {Z : Ω → ℝ}

/-- A general three-term linearity lemma for integrals over a measurable set —
the workhorse of the truncated-second-moment computation. -/
private lemma integral_lin_comb3 {s : Set ℝ} (_hs : MeasurableSet s)
    {f₁ f₂ f₃ : ℝ → ℝ}
    (h₁ : IntegrableOn f₁ s volume) (h₂ : IntegrableOn f₂ s volume)
    (h₃ : IntegrableOn f₃ s volume) (b₁ b₂ b₃ : ℝ) :
    ∫ z in s, (b₁ * f₁ z - b₂ * f₂ z + b₃ * f₃ z)
      = b₁ * (∫ i in s, f₁ i) - b₂ * (∫ i in s, f₂ i) + b₃ * (∫ i in s, f₃ i) := by
  have hI1 : IntegrableOn (fun z => b₁ * f₁ z) s volume := h₁.const_mul b₁
  have hI2 : IntegrableOn (fun z => b₂ * f₂ z) s volume := h₂.const_mul b₂
  have hI3 : IntegrableOn (fun z => b₃ * f₃ z) s volume := h₃.const_mul b₃
  have hI12 : IntegrableOn (fun z => b₁ * f₁ z - b₂ * f₂ z) s volume := hI1.sub hI2
  have step1 := integral_add hI12 hI3
  have step2 := integral_sub hI1 hI2
  have step4 := integral_const_mul (μ := volume.restrict s) b₁ f₁
  have step5 := integral_const_mul (μ := volume.restrict s) b₂ f₂
  have step6 := integral_const_mul (μ := volume.restrict s) b₃ f₃
  rw [step1, step2, step4, step5, step6]

/-- **Truncated second moment of the lognormal** (the put's second moment):

  `𝔼[(K − S_T)⁺²] = K²·Φ(−d₂) − 2·K·S₀·e^{μ + ν²/2}·Φ(−d₁)
                    + S₀²·e^{2μ + 2ν²}·Φ(−d₁ − ν)`,

with `μ = (r − σ²/2)T`, `ν = σ√T`, computed from MathFin's completing-the-square
primitive `integral_exp_mul_gaussianPDFReal_Iic` — the same atom `Put.lean` prices
with. -/
theorem secondMoment_payoff (h : BSCallHyp μ S_0 K r σ T Z) :
    ∫ ω, (max (K - bsTerminal S_0 r σ T (Z ω)) 0) ^ 2 ∂μ
      = K ^ 2 * Phi (-(bsd2 S_0 K r σ T))
        - 2 * K * (S_0 * Real.exp ((r - σ^2 / 2) * T + (σ * Real.sqrt T)^2 / 2))
            * Phi (-(bsd1 S_0 K r σ T))
        + S_0 ^ 2 * Real.exp (2 * (r - σ^2 / 2) * T + 2 * (σ * Real.sqrt T)^2)
            * Phi (-(bsd1 S_0 K r σ T) - σ * Real.sqrt T) := by
  obtain ⟨hS_0, hK, hσ, hT, hZ⟩ := h
  set d_2 := bsd2 S_0 K r σ T with d_2_def
  set μ_log := (r - σ^2 / 2) * T with μ_log_def
  set ν_log := σ * Real.sqrt T with ν_log_def
  have hsqrT_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hν_log_sq : ν_log ^ 2 = σ ^ 2 * T := by
    rw [ν_log_def, mul_pow, Real.sq_sqrt hT.le]
  have h_shift1 : (-d_2) - ν_log = -(bsd1 S_0 K r σ T) := by
    rw [d_2_def, bsd2, bsd1]
    field_simp
    ring
  have h_shift2 : (-d_2) - 2 * ν_log = -(bsd1 S_0 K r σ T) - ν_log := by
    rw [d_2_def, bsd2, bsd1]
    field_simp
    ring
  have hmeas : AEStronglyMeasurable
      (fun z : ℝ => (max (K - bsTerminal S_0 r σ T z) 0) ^ 2) (gaussianReal 0 1) := by
    unfold bsTerminal
    fun_prop
  -- Step 1-2: transfer to the standard normal, convert to the density
  rw [show (fun ω => (max (K - bsTerminal S_0 r σ T (Z ω)) 0) ^ 2)
        = (fun z => (max (K - bsTerminal S_0 r σ T z) 0) ^ 2) ∘ Z from rfl,
      hZ.integral_comp hmeas,
      integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  -- Step 3: the square lives on the exercise region `{z ≤ −d₂}`
  rw [show (fun z : ℝ => gaussianPDFReal 0 1 z • (max (K - bsTerminal S_0 r σ T z) 0) ^ 2)
        = (Set.Iic (-d_2)).indicator
            (fun z => gaussianPDFReal 0 1 z * (K - bsTerminal S_0 r σ T z) ^ 2) from
      funext fun z => by
        rw [smul_eq_mul]
        by_cases hz : z ≤ -d_2
        · have h1 : K < bsTerminal S_0 r σ T z ↔ -d_2 < z :=
            bsTerminal_gt_K_iff hS_0 hK hσ hT z
          have hST : ¬ (K < bsTerminal S_0 r σ T z) :=
            fun hc => not_lt.mpr hz (h1.mp hc)
          rw [Set.indicator_of_mem (by simpa using hz : z ∈ Set.Iic (-d_2)),
            max_eq_left (sub_nonneg.mpr (le_of_not_gt hST))]
        · have h1 : K < bsTerminal S_0 r σ T z ↔ -d_2 < z :=
            bsTerminal_gt_K_iff hS_0 hK hσ hT z
          have hlt : -d_2 < z := not_le.mp hz
          rw [Set.indicator_of_notMem (by simpa using hz : z ∉ Set.Iic (-d_2)),
            max_eq_right (sub_nonpos.mpr (le_of_lt (h1.mpr hlt))),
            zero_pow (by norm_num), mul_zero]]
  rw [integral_indicator measurableSet_Iic]
  -- Step 4: expand the square inside the exercise region
  have h_expand : ∀ z ∈ Set.Iic (-d_2),
      gaussianPDFReal 0 1 z * (K - bsTerminal S_0 r σ T z) ^ 2
        = K ^ 2 * gaussianPDFReal 0 1 z
          - (2 * K * (S_0 * Real.exp μ_log)) * (Real.exp (ν_log * z) * gaussianPDFReal 0 1 z)
          + (S_0 ^ 2 * Real.exp (2 * μ_log)) *
              (Real.exp (2 * ν_log * z) * gaussianPDFReal 0 1 z) := by
    intro z _
    have hexp : Real.exp ((r - σ^2 / 2) * T + σ * Real.sqrt T * z)
        = Real.exp μ_log * Real.exp (ν_log * z) := by
      rw [μ_log_def, ν_log_def, Real.exp_add]
    have hexp2 : Real.exp (2 * ν_log * z)
        = Real.exp (ν_log * z) * Real.exp (ν_log * z) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hexp3 : Real.exp (2 * μ_log)
        = Real.exp μ_log * Real.exp μ_log := by
      rw [← Real.exp_add]
      congr 1
      ring
    unfold bsTerminal
    rw [hexp, hexp2, hexp3]
    ring
  rw [setIntegral_congr_fun measurableSet_Iic h_expand]
  -- Step 5: the three integrability pieces (Put.lean's route)
  have hint_pdf : IntegrableOn (gaussianPDFReal 0 1) (Set.Iic (-d_2)) volume :=
    (integrable_gaussianPDFReal 0 1).integrableOn
  have hint_eν : IntegrableOn
      (fun z : ℝ => Real.exp (ν_log * z) * gaussianPDFReal 0 1 z) (Set.Iic (-d_2)) volume := by
    refine (((integrable_gaussianPDFReal ν_log 1).const_mul
      (Real.exp (ν_log ^ 2 / 2))).integrableOn).congr_fun ?_ measurableSet_Iic
    intro z _
    exact (exp_mul_gaussianPDFReal_zero_one ν_log z).symm
  have hint_e2ν : IntegrableOn
      (fun z : ℝ => Real.exp (2 * ν_log * z) * gaussianPDFReal 0 1 z)
      (Set.Iic (-d_2)) volume := by
    refine (((integrable_gaussianPDFReal (2 * ν_log) 1).const_mul
      (Real.exp ((2 * ν_log) ^ 2 / 2))).integrableOn).congr_fun ?_ measurableSet_Iic
    intro z _
    exact (exp_mul_gaussianPDFReal_zero_one (2 * ν_log) z).symm
  -- Step 6: linearity of the integral
  rw [integral_lin_comb3 measurableSet_Iic hint_pdf hint_eν hint_e2ν
      (K ^ 2) (2 * K * (S_0 * Real.exp μ_log)) (S_0 ^ 2 * Real.exp (2 * μ_log))]
  -- Step 7: the three Gaussian primitives
  rw [show ∫ z in Set.Iic (-d_2), gaussianPDFReal 0 1 z = Phi (-d_2) from by
    rw [setIntegral_gaussianPDFReal_eq_toReal measurableSet_Iic (0 : ℝ)]; rfl,
    integral_exp_mul_gaussianPDFReal_Iic,
    integral_exp_mul_gaussianPDFReal_Iic]
  rw [h_shift1, h_shift2, μ_log_def]
  -- Step 8: final algebra — merge the exponentials (`(2ν)²/2 = 2ν²` is pure ring)
  have h2ν : (2 * ν_log) ^ 2 / 2 = 2 * ν_log ^ 2 := by
    have h4 : (2 * ν_log) ^ 2 = 4 * ν_log ^ 2 := by ring
    rw [h4]
    ring
  have hm : Real.exp ((r - σ^2 / 2) * T) * Real.exp (ν_log ^ 2 / 2)
      = Real.exp ((r - σ^2 / 2) * T + ν_log ^ 2 / 2) := (Real.exp_add _ _).symm
  have hn : Real.exp (2 * (r - σ^2 / 2) * T) * Real.exp ((2 * ν_log) ^ 2 / 2)
      = Real.exp (2 * (r - σ^2 / 2) * T + 2 * ν_log ^ 2) := by
    rw [h2ν, Real.exp_add]
  linear_combination (norm := ring_nf)
    -(2 * K * S_0 * Phi (-(bsd1 S_0 K r σ T))) * hm
    + (S_0 ^ 2 * Phi (-(bsd1 S_0 K r σ T) - ν_log)) * hn

/-- **Discounted second moment** of the sampled put payoff: `𝔼[H²] = e^{-2rT}·M₂`
with `M₂` the truncated second moment above. -/
theorem secondMoment (h : BSCallHyp μ S_0 K r σ T Z) :
    ∫ ω, (payoff S_0 K r σ T (Z ω)) ^ 2 ∂μ
      = Real.exp (-2 * r * T) *
          (K ^ 2 * Phi (-(bsd2 S_0 K r σ T))
            - 2 * K * (S_0 * Real.exp ((r - σ^2 / 2) * T + (σ * Real.sqrt T)^2 / 2))
                * Phi (-(bsd1 S_0 K r σ T))
            + S_0 ^ 2 * Real.exp (2 * (r - σ^2 / 2) * T + 2 * (σ * Real.sqrt T)^2)
                * Phi (-(bsd1 S_0 K r σ T) - σ * Real.sqrt T)) := by
  have hexp2 : Real.exp (-r * T) ^ 2 = Real.exp (-2 * r * T) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq : ∀ ω : Ω, (payoff S_0 K r σ T (Z ω)) ^ 2
      = Real.exp (-2 * r * T) * (max (K - bsTerminal S_0 r σ T (Z ω)) 0) ^ 2 := by
    intro ω
    unfold payoff
    rw [mul_pow, hexp2]
  rw [integral_congr_ae (Filter.Eventually.of_forall hsq), integral_const_mul,
    secondMoment_payoff h]

/-- **The CLT limit variance in closed form** —
`σ_H² = e^{-2rT}·(truncated second moment) − P²`: the variance of the discounted
put payoff, composed from `secondMoment` (the truncated second moment) and
`mean_eq_bsPut` (the price `P`). -/
theorem variance (h : BSCallHyp μ S_0 K r σ T Z) :
    Var[fun ω => payoff S_0 K r σ T (Z ω); μ]
      = Real.exp (-2 * r * T) *
          (K ^ 2 * Phi (-(bsd2 S_0 K r σ T))
            - 2 * K * (S_0 * Real.exp ((r - σ^2 / 2) * T + (σ * Real.sqrt T)^2 / 2))
                * Phi (-(bsd1 S_0 K r σ T))
            + S_0 ^ 2 * Real.exp (2 * (r - σ^2 / 2) * T + 2 * (σ * Real.sqrt T)^2)
                * Phi (-(bsd1 S_0 K r σ T) - σ * Real.sqrt T))
        - (K * Real.exp (-r * T) * Phi (-(bsd2 S_0 K r σ T))
            - S_0 * Phi (-(bsd1 S_0 K r σ T))) ^ 2 := by
  rw [variance_eq_sub (memLp2_payoff h)]
  show ∫ ω, payoff S_0 K r σ T (Z ω) ^ 2 ∂μ
      - (∫ ω, payoff S_0 K r σ T (Z ω) ∂μ) ^ 2 = _
  rw [secondMoment h, mean_eq_bsPut h]

end Moments

end MathFin.MonteCarlo
