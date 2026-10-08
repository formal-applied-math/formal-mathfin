/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.BlackScholes.JumpDiffusionProcess
public import MathFin.Foundations.Esscher

/-!
# The law at one date determines the drift and the jumps

The log-return law over a time `τ > 0` of a jump-diffusion with drift `b`, volatility coefficient
`σ`, jump rate `Λ` and jump law `ν` (`jumpDiffusionIncrementLaw`) determines, for a given `σ`, the
drift `b` and the Lévy measure `Λν` away from `0`, and nothing more: jumps of size `0` do not move
the log-price. This is the uniqueness half of the Lévy–Khintchine representation, for finitely many
jumps, read off a single date.

* `jumpDiffusionExponent_eq_levy`: `κ(u) = bu + σ²u²/2 + ∫ (e^{ux} − 1) Π(dx)` wherever
  `∫ e^{ux} dν < ∞`, where `Π` is `Λν` restricted to `x ≠ 0`. The Laplace exponent sees the jumps
  only through `Π`.
* `jumpDiffusionIncrementLaw_eq_iff`: for jump laws whose moment-generating functions are finite
  near `0`, two log-return laws with the same `σ` at the same date `τ > 0` are equal iff their
  drifts agree and their Lévy measures agree off `0`.

The proof reads `κ` off the law near `0` (`mgf_id_jumpDiffusionIncrementLaw`) and takes second
differences in `u`: `κ(u + s) + κ(u − s) − 2κ(u) = σ²s² + ∫ e^{ux}·2(cosh(sx) − 1) Λν(dx)`. The
drift cancels and the Gaussian part is the same constant for both laws. So the finite measures
`2(cosh(sx) − 1)·Λν` have the same moment-generating function near `0`, hence are equal
(`measure_eq_of_mgf_id_eventuallyEq`). Dividing by `2(cosh(sx) − 1)`, which vanishes only at `0`,
gives `Π`, and then `κ` gives `b`. Whether the law also determines `σ²` is not formalized here.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped NNReal ENNReal Topology

/-- The second-difference kernel `2(cosh(sx) − 1) = e^{sx} + e^{−sx} − 2`, as a density: the second
difference of `u ↦ e^{ux}` with step `s` is `e^{ux}` times it (`coshKernel_smul_exp`). -/
noncomputable def coshKernel (s x : ℝ) : ℝ≥0 := Real.toNNReal (2 * (Real.cosh (s * x) - 1))

lemma coe_coshKernel (s x : ℝ) : (coshKernel s x : ℝ) = 2 * (Real.cosh (s * x) - 1) :=
  Real.coe_toNNReal _ (by linarith [Real.one_le_cosh (s * x)])

lemma measurable_coshKernel (s : ℝ) : Measurable (coshKernel s) :=
  (by fun_prop : Measurable fun x ↦ 2 * (Real.cosh (s * x) - 1)).real_toNNReal

/-- For `s ≠ 0` the kernel vanishes only at `0`. -/
lemma coshKernel_eq_zero_iff {s : ℝ} (hs : s ≠ 0) {x : ℝ} : coshKernel s x = 0 ↔ x = 0 := by
  rw [coshKernel, Real.toNNReal_eq_zero]
  refine ⟨fun h ↦ Classical.byContradiction fun hx ↦ ?_, fun hx ↦ by simp [hx]⟩
  linarith [Real.one_lt_cosh.2 (mul_ne_zero hs hx)]

/-- The second difference of `u ↦ e^{ux}` with step `s`:
`2(cosh(sx) − 1)·e^{ux} = e^{(u+s)x} + e^{(u−s)x} − 2e^{ux}`. -/
lemma coshKernel_smul_exp (s u x : ℝ) :
    coshKernel s x • rexp (u * x)
      = rexp ((u + s) * x) + rexp ((u - s) * x) - 2 * rexp (u * x) := by
  rw [NNReal.smul_def, smul_eq_mul, coe_coshKernel, Real.cosh_eq,
    show (u + s) * x = u * x + s * x by ring, show (u - s) * x = u * x + -(s * x) by ring,
    Real.exp_add, Real.exp_add]
  ring

lemma integrable_coshKernel_smul_exp {ν : Measure ℝ} {s u : ℝ}
    (hp : Integrable (fun x ↦ rexp ((u + s) * x)) ν)
    (hm : Integrable (fun x ↦ rexp ((u - s) * x)) ν) (h0 : Integrable (fun x ↦ rexp (u * x)) ν) :
    Integrable (fun x ↦ coshKernel s x • rexp (u * x)) ν := by
  simp_rw [coshKernel_smul_exp]
  exact (hp.add hm).sub (h0.const_mul 2)

/-- **The kernel turns second differences of exponential moments into one integral**:
`∫ 2(cosh(sx) − 1)e^{ux} dν = ∫ e^{(u+s)x} dν + ∫ e^{(u−s)x} dν − 2∫ e^{ux} dν`. -/
lemma integral_coshKernel_smul_exp {ν : Measure ℝ} {s u : ℝ}
    (hp : Integrable (fun x ↦ rexp ((u + s) * x)) ν)
    (hm : Integrable (fun x ↦ rexp ((u - s) * x)) ν) (h0 : Integrable (fun x ↦ rexp (u * x)) ν) :
    ∫ x, coshKernel s x • rexp (u * x) ∂ν
      = ∫ x, rexp ((u + s) * x) ∂ν + ∫ x, rexp ((u - s) * x) ∂ν - 2 * ∫ x, rexp (u * x) ∂ν := by
  have hpm : Integrable (fun x ↦ rexp ((u + s) * x) + rexp ((u - s) * x)) ν := hp.add hm
  simp_rw [coshKernel_smul_exp]
  rw [integral_sub hpm (h0.const_mul 2), integral_add hp hm, integral_const_mul]

/-- The kernel measure `2(cosh(sx) − 1)·Λν` has the exponential moment of order `u` when `ν` has
those of orders `u + s`, `u − s` and `u`. -/
lemma integrable_exp_mul_withDensity_coshKernel (Λ : ℝ≥0) {ν : Measure ℝ} {s u : ℝ}
    (hp : Integrable (fun x ↦ rexp ((u + s) * x)) ν)
    (hm : Integrable (fun x ↦ rexp ((u - s) * x)) ν) (h0 : Integrable (fun x ↦ rexp (u * x)) ν) :
    Integrable (fun x ↦ rexp (u * x)) ((Λ • ν).withDensity fun x ↦ coshKernel s x) :=
  (integrable_withDensity_iff_integrable_smul (measurable_coshKernel s)).2
    (integrable_coshKernel_smul_exp hp hm h0).smul_measure_nnreal

/-- **The moment-generating function of the kernel measure** is `Λ` times the second difference
of the moment-generating function of `ν`. -/
lemma mgf_id_withDensity_coshKernel (Λ : ℝ≥0) {ν : Measure ℝ} {s u : ℝ}
    (hp : Integrable (fun x ↦ rexp ((u + s) * x)) ν)
    (hm : Integrable (fun x ↦ rexp ((u - s) * x)) ν) (h0 : Integrable (fun x ↦ rexp (u * x)) ν) :
    mgf id ((Λ • ν).withDensity fun x ↦ coshKernel s x) u
      = Λ * (∫ x, rexp ((u + s) * x) ∂ν + ∫ x, rexp ((u - s) * x) ∂ν
          - 2 * ∫ x, rexp (u * x) ∂ν) := by
  show ∫ x, rexp (u * x) ∂((Λ • ν).withDensity fun x ↦ coshKernel s x) = _
  rw [integral_withDensity_eq_integral_smul (measurable_coshKernel s),
    integral_smul_nnreal_measure, integral_coshKernel_smul_exp hp hm h0, NNReal.smul_def,
    smul_eq_mul]

/-- The kernel measure is finite when `ν` has the exponential moments of orders `s` and `−s`. -/
lemma isFiniteMeasure_withDensity_coshKernel (Λ : ℝ≥0) {ν : Measure ℝ} [IsFiniteMeasure ν]
    {s : ℝ} (hp : Integrable (fun x ↦ rexp (s * x)) ν)
    (hm : Integrable (fun x ↦ rexp (-s * x)) ν) :
    IsFiniteMeasure ((Λ • ν).withDensity fun x ↦ coshKernel s x) := by
  have h := integrable_exp_mul_withDensity_coshKernel Λ (u := 0) (s := s)
    (by simpa only [zero_add] using hp) (by simpa only [zero_sub] using hm)
    (by simpa only [zero_mul, Real.exp_zero] using integrable_const (1 : ℝ))
  simp only [zero_mul, Real.exp_zero] at h
  exact (integrable_const_iff.1 h).resolve_left one_ne_zero

/-- Off `0` the kernel is positive and finite, so dividing the kernel measure by it gives back the
measure restricted to `x ≠ 0`. -/
lemma restrict_compl_zero_eq_withDensity_inv {s : ℝ} (hs : s ≠ 0) (μ : Measure ℝ) :
    μ.restrict {0}ᶜ = ((μ.withDensity fun x ↦ coshKernel s x).restrict {0}ᶜ).withDensity
      fun x ↦ (coshKernel s x : ℝ≥0∞)⁻¹ := by
  rw [restrict_withDensity (measurableSet_singleton (0 : ℝ)).compl, withDensity_inv_same
    (measurable_coshKernel s).coe_nnreal_ennreal ?_ (ae_of_all _ fun _ ↦ ENNReal.coe_ne_top)]
  filter_upwards [ae_restrict_mem (measurableSet_singleton (0 : ℝ)).compl] with x hx
  exact ENNReal.coe_ne_zero.2 ((coshKernel_eq_zero_iff hs).not.2 (mem_compl_singleton_iff.1 hx))

/-- **The Lévy–Khintchine form of the Laplace exponent**: wherever `∫ e^{ux} dν < ∞`,
`κ(u) = bu + σ²u²/2 + ∫ (e^{ux} − 1) Π(dx)`, where `Π` is the Lévy measure `Λν` restricted to
`x ≠ 0`. Jumps of size `0` contribute nothing. -/
lemma jumpDiffusionExponent_eq_levy (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {u : ℝ} (hu : Integrable (fun x ↦ rexp (u * x)) ν) :
    jumpDiffusionExponent b σ Λ ν u
      = b * u + σ ^ 2 * u ^ 2 / 2 + ∫ x, (rexp (u * x) - 1) ∂((Λ • ν).restrict {0}ᶜ) := by
  have hf : Integrable (fun x ↦ rexp (u * x) - 1) (Λ • ν) :=
    (hu.sub (integrable_const 1)).smul_measure_nnreal
  have h0 : ∫ x in {0}, (rexp (u * x) - 1) ∂(Λ • ν) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦ by simp [mem_singleton_iff.1 hx]
  have h := integral_add_compl (measurableSet_singleton (0 : ℝ)) hf
  rw [h0, zero_add, integral_smul_nnreal_measure, integral_sub hu (integrable_const 1),
    integral_const, probReal_univ, one_smul, NNReal.smul_def, smul_eq_mul] at h
  rw [jumpDiffusionExponent, h]

/-- Equal log-return laws at a date `τ > 0` have equal Laplace exponents near `0`, where the jump
laws have exponential moments. -/
lemma eventually_jumpDiffusionExponent_eq {b₁ b₂ σ₁ σ₂ : ℝ} {Λ₁ Λ₂ : ℝ≥0} {ν₁ ν₂ : Measure ℝ}
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h₁ : 0 ∈ interior (integrableExpSet id ν₁)) (h₂ : 0 ∈ interior (integrableExpSet id ν₂))
    {τ : ℝ≥0} (hτ : 0 < τ)
    (h : jumpDiffusionIncrementLaw b₁ σ₁ Λ₁ ν₁ τ = jumpDiffusionIncrementLaw b₂ σ₂ Λ₂ ν₂ τ) :
    ∀ᶠ u in 𝓝 (0 : ℝ),
      jumpDiffusionExponent b₁ σ₁ Λ₁ ν₁ u = jumpDiffusionExponent b₂ σ₂ Λ₂ ν₂ u := by
  filter_upwards [mem_interior_iff_mem_nhds.1 h₁, mem_interior_iff_mem_nhds.1 h₂] with u hu₁ hu₂
  have e : mgf id (jumpDiffusionIncrementLaw b₁ σ₁ Λ₁ ν₁ τ) u
      = mgf id (jumpDiffusionIncrementLaw b₂ σ₂ Λ₂ ν₂ τ) u := by rw [h]
  rw [mgf_id_jumpDiffusionIncrementLaw b₁ σ₁ Λ₁
      (hu₁ : Integrable (fun x ↦ rexp (u * x)) ν₁) τ,
    mgf_id_jumpDiffusionIncrementLaw b₂ σ₂ Λ₂ (hu₂ : Integrable (fun x ↦ rexp (u * x)) ν₂) τ,
    Real.exp_eq_exp] at e
  exact mul_right_cancel₀ (NNReal.coe_ne_zero.2 hτ.ne') e

/-- **The law at one date determines the drift and the jumps.** For jump laws whose
moment-generating functions are finite near `0`, two jump-diffusion log-return laws with the same
volatility coefficient `σ` at the same date `τ > 0` are equal iff their drifts agree and their
Lévy measures `Λν` agree off `0`. -/
theorem jumpDiffusionIncrementLaw_eq_iff {b₁ b₂ σ : ℝ} {Λ₁ Λ₂ : ℝ≥0} {ν₁ ν₂ : Measure ℝ}
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h₁ : 0 ∈ interior (integrableExpSet id ν₁)) (h₂ : 0 ∈ interior (integrableExpSet id ν₂))
    {τ : ℝ≥0} (hτ : 0 < τ) :
    jumpDiffusionIncrementLaw b₁ σ Λ₁ ν₁ τ = jumpDiffusionIncrementLaw b₂ σ Λ₂ ν₂ τ ↔
      b₁ = b₂ ∧ (Λ₁ • ν₁).restrict {0}ᶜ = (Λ₂ • ν₂).restrict {0}ᶜ := by
  -- near `0` both jump laws have exponential moments
  have hD₁ : ∀ᶠ u in 𝓝 (0 : ℝ), Integrable (fun x ↦ rexp (u * x)) ν₁ :=
    eventually_mem_set.2 (mem_interior_iff_mem_nhds.1 h₁)
  have hD₂ : ∀ᶠ u in 𝓝 (0 : ℝ), Integrable (fun x ↦ rexp (u * x)) ν₂ :=
    eventually_mem_set.2 (mem_interior_iff_mem_nhds.1 h₂)
  constructor
  · intro h
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
      (hD₁.and (hD₂.and (eventually_jumpDiffusionExponent_eq h₁ h₂ hτ h)))
    have hin (y : ℝ) (hy₁ : -ε < y) (hy₂ : y < ε) := hball y (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact ⟨hy₁, hy₂⟩)
    have hs : ε / 2 ≠ 0 := (half_pos hε).ne'
    haveI := isFiniteMeasure_withDensity_coshKernel Λ₁ (s := ε / 2)
      (hin (ε / 2) (by linarith) (by linarith)).1 (hin (-(ε / 2)) (by linarith) (by linarith)).1
    haveI := isFiniteMeasure_withDensity_coshKernel Λ₂ (s := ε / 2)
      (hin (ε / 2) (by linarith) (by linarith)).2.1
      (hin (-(ε / 2)) (by linarith) (by linarith)).2.1
    -- the kernel measures have the same moment-generating function on `(-ε/2, ε/2)`
    have hM : (Λ₁ • ν₁).withDensity (fun x ↦ coshKernel (ε / 2) x)
        = (Λ₂ • ν₂).withDensity fun x ↦ coshKernel (ε / 2) x := by
      have hU : Metric.ball (0 : ℝ) (ε / 2) ∈ 𝓝 0 := Metric.ball_mem_nhds 0 (half_pos hε)
      refine measure_eq_of_mgf_id_eventuallyEq
        (mem_interior_iff_mem_nhds.2 (mem_of_superset hU fun u hu ↦ ?_))
        (eventually_of_mem hU fun u hu ↦ ?_)
      all_goals
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] at hu
        obtain ⟨hu₁, hu₂⟩ := hu
      · exact integrable_exp_mul_withDensity_coshKernel Λ₁
          (hin (u + ε / 2) (by linarith) (by linarith)).1
          (hin (u - ε / 2) (by linarith) (by linarith)).1 (hin u (by linarith) (by linarith)).1
      · have ep := (hin (u + ε / 2) (by linarith) (by linarith)).2.2
        have em := (hin (u - ε / 2) (by linarith) (by linarith)).2.2
        have e0 := (hin u (by linarith) (by linarith)).2.2
        rw [mgf_id_withDensity_coshKernel Λ₁ (hin (u + ε / 2) (by linarith) (by linarith)).1
            (hin (u - ε / 2) (by linarith) (by linarith)).1 (hin u (by linarith) (by linarith)).1,
          mgf_id_withDensity_coshKernel Λ₂ (hin (u + ε / 2) (by linarith) (by linarith)).2.1
            (hin (u - ε / 2) (by linarith) (by linarith)).2.1
            (hin u (by linarith) (by linarith)).2.1]
        simp only [jumpDiffusionExponent] at ep em e0
        linear_combination ep + em - 2 * e0
    -- dividing by the kernel gives the Lévy measures off `0`
    have hΠ : (Λ₁ • ν₁).restrict {0}ᶜ = (Λ₂ • ν₂).restrict {0}ᶜ := by
      rw [restrict_compl_zero_eq_withDensity_inv hs (Λ₁ • ν₁),
        restrict_compl_zero_eq_withDensity_inv hs (Λ₂ • ν₂), hM]
    -- and then `κ` gives the drift
    refine ⟨?_, hΠ⟩
    have e := (hin (ε / 2) (by linarith) (by linarith)).2.2
    rw [jumpDiffusionExponent_eq_levy b₁ σ Λ₁ (hin (ε / 2) (by linarith) (by linarith)).1,
      jumpDiffusionExponent_eq_levy b₂ σ Λ₂ (hin (ε / 2) (by linarith) (by linarith)).2.1,
      hΠ] at e
    have h2 : (b₁ - b₂) * (ε / 2) = 0 := by linear_combination e
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hs)
  · rintro ⟨rfl, hΠ⟩
    have hint : ∀ᶠ u in 𝓝 (0 : ℝ),
        Integrable (fun y ↦ rexp (u * y)) (jumpDiffusionIncrementLaw b₁ σ Λ₁ ν₁ τ) :=
      hD₁.mono fun u hu ↦ integrable_exp_mul_jumpDiffusionIncrementLaw _ _ _ hu τ
    refine measure_eq_of_mgf_id_eventuallyEq (mem_interior_iff_mem_nhds.2 hint)
      ((hD₁.and hD₂).mono fun u hu ↦ ?_)
    rw [mgf_id_jumpDiffusionIncrementLaw _ _ _ hu.1, mgf_id_jumpDiffusionIncrementLaw _ _ _ hu.2,
      jumpDiffusionExponent_eq_levy _ _ _ hu.1, jumpDiffusionExponent_eq_levy _ _ _ hu.2, hΠ]

end MathFin
