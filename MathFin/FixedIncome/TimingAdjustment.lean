/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.Foundations.BrownianMartingale
public import MathFin.Foundations.Numeraire

/-!
# The covariance-between-numéraires identity: timing adjustment and futures-forward basis

Two textbook corrections are the same identity. Let `Q^N` be the measure attached to a
numéraire whose relative weight against the reference numéraire is `e^{−Y}`. For a payoff
`V` with `(ln V, Y)` jointly Gaussian,

  `𝔼^{Q^N}[V] = 𝔼^Q[V] · exp(−Cov(ln V, Y))`.

The static step is `changeOfNumeraire` (`Foundations/Numeraire`): `𝔼^{Q^N}[V]` is
`𝔼^Q[V·e^{−Y}] / 𝔼^Q[e^{−Y}]`. The Gaussian step is the log-normal covariance identity
`𝔼[V·e^{−Y}] = 𝔼[V]·𝔼[e^{−Y}]·exp(−Cov(ln V, Y))`, proved here from the independent-driver
decomposition `Y = n + u(ρ Z₁ + √(1−ρ²) Z₂)`, `ln V = m + s Z₁`, so `Cov(ln V, Y) = ρ s u`.

* **Hull's timing adjustment** (Hull, *Options, Futures, and Other Derivatives*, eq. 30.3):
  `Q` is the `T`-forward measure, `Q^N` the `T*`-forward measure, and `e^{−Y} = P(T,T*)`.
  A payoff fixed at `T` and paid at `T*` has `𝔼^{T*}[V] = 𝔼^T[V]·exp(−Cov(ln V, Y))`.
* **Bagaria's futures-forward basis** (Bagaria, eq. 8.9): `Q` is the risk-neutral measure,
  `Q^N` the `T`-forward measure, and `e^{Y}` the bank account `exp(∫₀ᵀ r)`. The futures price
  `𝔼^Q[V]` is the forward price `𝔼^T[V]` times `exp(Cov(ln V, ∫₀ᵀ r))`.

**Exact vs. linearized.** Both statements here are exact under the Gaussian hypothesis.
Hull's textbook presentation of the timing adjustment, with a `(1 + R_F/m)`-style
simple-compounding denominator, is a first-order linearization of this exponential identity.
That approximate form is not proved here and is not exact.

## Main results

* `integral_mul_exp_neg_gaussian` — `𝔼[V·e^{−Y}] = 𝔼[V]·𝔼[e^{−Y}]·exp(−ρ s u)`.
* `timingAdjustment_gaussian` — Hull eq. 30.3, exact Gaussian form.
* `futuresForwardBasis_gaussian` — Bagaria eq. 8.9, exact Gaussian form.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Standard-normal MGF via `HasLaw` transfer: `𝔼[exp(a·Z)] = exp(a²/2)`. -/
private lemma integral_exp_mul_stdNormal' {Z : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) μ) (a : ℝ) :
    ∫ ω, Real.exp (a * Z ω) ∂μ = Real.exp (a ^ 2 / 2) := by
  have h := hZ.integral_comp
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ ↦ Real.exp (a * x)) (gaussianReal 0 1))
  simp only [Function.comp] at h
  rw [h, integral_exp_mul_gaussianReal_zero a 1]
  simp

/-- The MGF of an affine form in two independent standard normals:
`𝔼[exp(c + a Z₁ + b Z₂)] = exp(c + a²/2 + b²/2)`. -/
private lemma integral_exp_affine_indep {Z₁ Z₂ : Ω → ℝ}
    (h₁ : HasLaw Z₁ (gaussianReal 0 1) μ) (h₂ : HasLaw Z₂ (gaussianReal 0 1) μ)
    (hm₁ : Measurable Z₁) (hm₂ : Measurable Z₂) (hindep : IndepFun Z₁ Z₂ μ) (c a b : ℝ) :
    ∫ ω, Real.exp (c + a * Z₁ ω + b * Z₂ ω) ∂μ = Real.exp (c + a ^ 2 / 2 + b ^ 2 / 2) := by
  have hpt : (fun ω ↦ Real.exp (c + a * Z₁ ω + b * Z₂ ω))
      = fun ω ↦ Real.exp c * (Real.exp (a * Z₁ ω) * Real.exp (b * Z₂ ω)) := by
    funext ω; rw [← Real.exp_add, ← Real.exp_add, add_assoc]
  have hind : IndepFun (fun ω ↦ Real.exp (a * Z₁ ω)) (fun ω ↦ Real.exp (b * Z₂ ω)) μ :=
    hindep.comp (by fun_prop : Measurable fun x ↦ Real.exp (a * x))
      (by fun_prop : Measurable fun x ↦ Real.exp (b * x))
  have hprod : ∫ ω, Real.exp (a * Z₁ ω) * Real.exp (b * Z₂ ω) ∂μ
      = Real.exp (a ^ 2 / 2) * Real.exp (b ^ 2 / 2) := by
    rw [← integral_exp_mul_stdNormal' h₁ a, ← integral_exp_mul_stdNormal' h₂ b]
    exact hind.integral_mul_eq_mul_integral (by fun_prop) (by fun_prop)
  rw [hpt, integral_const_mul, hprod, ← Real.exp_add, ← Real.exp_add, add_assoc]

/-- **The log-normal covariance identity.** With `ln V = m + s Z₁` and
`Y = n + u(ρ Z₁ + √(1−ρ²) Z₂)` for independent standard normals `Z₁, Z₂` (so
`Cov(ln V, Y) = ρ s u`),

  `𝔼[V·e^{−Y}] = 𝔼[V] · 𝔼[e^{−Y}] · exp(−ρ s u)`. -/
theorem integral_mul_exp_neg_gaussian (m s n u ρ : ℝ)
    {Z₁ Z₂ : Ω → ℝ}
    (h₁ : HasLaw Z₁ (gaussianReal 0 1) μ) (h₂ : HasLaw Z₂ (gaussianReal 0 1) μ)
    (hm₁ : Measurable Z₁) (hm₂ : Measurable Z₂) (hindep : IndepFun Z₁ Z₂ μ) :
    ∫ ω, Real.exp (m + s * Z₁ ω)
        * Real.exp (-(n + u * (ρ * Z₁ ω + Real.sqrt (1 - ρ ^ 2) * Z₂ ω))) ∂μ
      = (∫ ω, Real.exp (m + s * Z₁ ω) ∂μ)
        * (∫ ω, Real.exp (-(n + u * (ρ * Z₁ ω + Real.sqrt (1 - ρ ^ 2) * Z₂ ω))) ∂μ)
        * Real.exp (-(ρ * s * u)) := by
  set r := Real.sqrt (1 - ρ ^ 2)
  have eL : (fun ω ↦ Real.exp (m + s * Z₁ ω) * Real.exp (-(n + u * (ρ * Z₁ ω + r * Z₂ ω))))
      = fun ω ↦ Real.exp ((m - n) + (s - u * ρ) * Z₁ ω + (-(u * r)) * Z₂ ω) := by
    funext ω; rw [← Real.exp_add]; congr 1; ring
  have eV : (fun ω ↦ Real.exp (m + s * Z₁ ω))
      = fun ω ↦ Real.exp (m + s * Z₁ ω + 0 * Z₂ ω) := by
    funext ω; simp
  have eP : (fun ω ↦ Real.exp (-(n + u * (ρ * Z₁ ω + r * Z₂ ω))))
      = fun ω ↦ Real.exp (-n + (-(u * ρ)) * Z₁ ω + (-(u * r)) * Z₂ ω) := by
    funext ω; congr 1; ring
  rw [eL, eV, eP, integral_exp_affine_indep h₁ h₂ hm₁ hm₂ hindep,
    integral_exp_affine_indep h₁ h₂ hm₁ hm₂ hindep, integral_exp_affine_indep h₁ h₂ hm₁ hm₂ hindep,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- **Hull's timing adjustment** (Hull, eq. 30.3), exact Gaussian form. Let `Q` be the
`T`-forward measure (reference numéraire `P(·,T)`, worth `1` at `T` and `B₀ = P(0,T)` today),
and let the `T*`-bond be worth `P(T,T*) = e^{−Y}` at `T` and `N₀ = P(0,T*)` today, with the
no-arbitrage normalization `N₀ = B₀·𝔼^T[P(T,T*)]`. For a payoff `V` fixed at `T` and paid at
`T*`, with `(ln V, Y)` jointly Gaussian and `Cov(ln V, Y) = ρ s u`, the `T*`-forward
expectation is

  `𝔼^{T*}[V] = 𝔼^T[V] · exp(−ρ s u)`.

This is exact; the textbook simple-compounding approximation is its linearization. -/
theorem timingAdjustment_gaussian (m s n u ρ B₀ N₀ : ℝ)
    (hB₀ : 0 < B₀) (hN₀ : 0 < N₀)
    {Z₁ Z₂ : Ω → ℝ}
    (h₁ : HasLaw Z₁ (gaussianReal 0 1) μ) (h₂ : HasLaw Z₂ (gaussianReal 0 1) μ)
    (hm₁ : Measurable Z₁) (hm₂ : Measurable Z₂) (hindep : IndepFun Z₁ Z₂ μ)
    (hnorm : N₀ = B₀ *
      ∫ ω, Real.exp (-(n + u * (ρ * Z₁ ω + Real.sqrt (1 - ρ ^ 2) * Z₂ ω))) ∂μ) :
    ∫ ω, Real.exp (m + s * Z₁ ω) ∂(numeraireMeasure μ (fun _ ↦ 1)
        (fun ω ↦ Real.exp (-(n + u * (ρ * Z₁ ω + Real.sqrt (1 - ρ ^ 2) * Z₂ ω)))) B₀ N₀)
      = (∫ ω, Real.exp (m + s * Z₁ ω) ∂μ) * Real.exp (-(ρ * s * u)) := by
  subst hnorm
  set P : Ω → ℝ := fun ω ↦ Real.exp (-(n + u * (ρ * Z₁ ω + Real.sqrt (1 - ρ ^ 2) * Z₂ ω)))
  set V : Ω → ℝ := fun ω ↦ Real.exp (m + s * Z₁ ω)
  have hPm : Measurable P := by fun_prop
  have h := changeOfNumeraire (Q := μ) (fun ω ↦ V ω * P ω) hPm measurable_const
    (fun ω ↦ Real.exp_pos _) (fun _ ↦ one_pos) hB₀.le hN₀
  have hc : (fun ω ↦ V ω * P ω / P ω) = V := by
    funext ω; exact mul_div_cancel_right₀ _ (Real.exp_pos _).ne'
  simp only [hc, div_one] at h
  have hcore := integral_mul_exp_neg_gaussian (μ := μ) m s n u ρ h₁ h₂ hm₁ hm₂ hindep
  change ∫ ω, V ω * P ω ∂μ = (∫ ω, V ω ∂μ) * (∫ ω, P ω ∂μ) * _ at hcore
  rw [hcore] at h
  exact mul_left_cancel₀ hN₀.ne' (h.trans (by ring))

/-- **Bagaria's futures-forward basis** (Bagaria, eq. 8.9), exact Gaussian form. Let `Q` be the
risk-neutral measure with bank account `e^{Y}`, `Y = ∫₀ᵀ r`, and pass to the `T`-forward
measure (numéraire `P(·,T)`, worth `1` at `T` and `N₀ = P(0,T) = 𝔼^Q[e^{−Y}]` today). For an
underlying `V` with `(ln V, Y)` jointly Gaussian and `Cov(ln V, ∫₀ᵀ r) = ρ s u`, the futures
price `𝔼^Q[V]` and the forward price `𝔼^T[V]` satisfy

  `𝔼^Q[V] = 𝔼^T[V] · exp(ρ s u)`. -/
theorem futuresForwardBasis_gaussian (m s n u ρ N₀ : ℝ)
    (hN₀ : 0 < N₀)
    {Z₁ Z₂ : Ω → ℝ}
    (h₁ : HasLaw Z₁ (gaussianReal 0 1) μ) (h₂ : HasLaw Z₂ (gaussianReal 0 1) μ)
    (hm₁ : Measurable Z₁) (hm₂ : Measurable Z₂) (hindep : IndepFun Z₁ Z₂ μ)
    (hnorm : N₀ =
      ∫ ω, Real.exp (-(n + u * (ρ * Z₁ ω + Real.sqrt (1 - ρ ^ 2) * Z₂ ω))) ∂μ) :
    ∫ ω, Real.exp (m + s * Z₁ ω) ∂μ
      = (∫ ω, Real.exp (m + s * Z₁ ω) ∂(numeraireMeasure μ
          (fun ω ↦ Real.exp (n + u * (ρ * Z₁ ω + Real.sqrt (1 - ρ ^ 2) * Z₂ ω)))
          (fun _ ↦ 1) 1 N₀)) * Real.exp (ρ * s * u) := by
  have h := changeOfNumeraire (Q := μ) (fun ω ↦ Real.exp (m + s * Z₁ ω))
    (NT := fun _ ↦ (1 : ℝ))
    (BT := fun ω ↦ Real.exp (n + u * (ρ * Z₁ ω + Real.sqrt (1 - ρ ^ 2) * Z₂ ω)))
    measurable_const (by fun_prop)
    (fun _ ↦ one_pos) (fun ω ↦ Real.exp_pos _) zero_le_one hN₀
  have hc : (fun ω ↦ Real.exp (m + s * Z₁ ω)
        / Real.exp (n + u * (ρ * Z₁ ω + Real.sqrt (1 - ρ ^ 2) * Z₂ ω)))
      = fun ω ↦ Real.exp (m + s * Z₁ ω)
        * Real.exp (-(n + u * (ρ * Z₁ ω + Real.sqrt (1 - ρ ^ 2) * Z₂ ω))) := by
    funext ω; rw [Real.exp_neg, div_eq_mul_inv]
  simp only [div_one, one_mul] at h
  rw [hc, integral_mul_exp_neg_gaussian m s n u ρ h₁ h₂ hm₁ hm₂ hindep, ← hnorm] at h
  have h' : ∫ ω, Real.exp (m + s * Z₁ ω) ∂(numeraireMeasure μ
          (fun ω ↦ Real.exp (n + u * (ρ * Z₁ ω + Real.sqrt (1 - ρ ^ 2) * Z₂ ω)))
          (fun _ ↦ 1) 1 N₀)
      = (∫ ω, Real.exp (m + s * Z₁ ω) ∂μ) * Real.exp (-(ρ * s * u)) := by
    refine mul_left_cancel₀ hN₀.ne' (h.trans ?_)
    ring
  rw [h', mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

end MathFin
