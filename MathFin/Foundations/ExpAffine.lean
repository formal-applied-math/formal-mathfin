/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib

/-!
# The exponential-affine engine: generator invariance and the Riccati flow

The deterministic core of the affine-term-structure method (Bagaria ch. 14,
eqs. 14.4–14.6): applying an affine diffusion's generator to a member
`expAffine φ ψ = x ↦ e^(φ + ψ x)` of the exponential-affine family returns an
affine-in-the-state bracket times the function itself, so matching powers of the
state turns a pricing PDE into the Riccati system `ψ' = bψ + ½dψ²`,
`φ' = aψ + ½cψ²`. Everything here is pure Mathlib — no probability.

Contents: the one-dimensional OU/Vasicek generator `ouGenerator a κ σ`
(`dX_t = (a − κX_t) dt + σ dW_t`) and the CIR generator `cirGenerator κ θ ξ`
(`dV_t = (κθ − κV_t) dt + ξ√V_t dW_t`, diffusion `v`-proportional); the engine
lemmas `ouGenerator_expAffine` / `cirGenerator_expAffine` with their affine-bracket
corollaries; the Bernoulli/Riccati flow `riccatiFlow κ σ ψ₀` solving
`ψ' = −κψ + (σ²/2)ψ²` (the undiscounted exponent equation, with the honest
Bernoulli-denominator guard), in both the OU roles and the CIR roles; and the
lambda-form `HasDerivAt.add`/`.sub` helpers the assemblies consume.

## Result

Public API (all in namespace `MathFin.ExpAffine`):

* `expAffine`, `ouGenerator`, `cirGenerator` — the family and the two generators;
* `hasDerivAt_affine`, `hasDerivAt_expAffine`, `deriv_expAffine`,
  `deriv_expAffine_mul`, `deriv_deriv_expAffine`, `contDiff_expAffine` — the
  derivative substrate of the family;
* `ouGenerator_expAffine`, `ouBracket_affine` — the OU engine lemma and its
  affine-bracket corollary;
* `cirGenerator_expAffine`, `cirBracket_affine`,
  `hasDerivAt_riccatiFlow_cirRoles` — the CIR counterparts;
* `riccatiFlow`, `riccatiFlow_at_zero`, `hasDerivAt_riccatiFlow` — the Riccati
  flow and its ODE;
* `hasDerivAt_add'`, `hasDerivAt_sub'` — lambda-form derivatives of sums and
  differences.
-/

@[expose] public section

namespace MathFin.ExpAffine

/-- The exponential-affine family `x ↦ e^(φ + ψ x)` (Bagaria ch. 14, eq. 14.4). -/
noncomputable def expAffine (φ ψ x : ℝ) : ℝ := Real.exp (φ + ψ * x)

/-- The one-dimensional affine (OU/Vasicek) generator
`Lf = (a - κ x) f' + (σ²/2) f''`. -/
noncomputable def ouGenerator (a κ σ : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => (a - κ * x) * deriv f x + (σ ^ 2 / 2) * deriv (deriv f) x

/-! ### Derivative helpers for the exponential-affine family -/

/-- The affine inner function `y ↦ φ + ψ * y` has derivative `ψ`. -/
theorem hasDerivAt_affine (φ ψ x : ℝ) : HasDerivAt (fun y => φ + ψ * y) ψ x := by
  have h : HasDerivAt (fun y => ψ * y) ψ x := by
    simpa using (hasDerivAt_id x).const_mul ψ
  exact HasDerivAt.const_add φ h

/-- Chain rule instance: `e^(φ + ψ ·)` has derivative `ψ * e^(φ + ψ x)`
(Mathlib's `HasDerivAt.exp`). -/
theorem hasDerivAt_expAffine (φ ψ x : ℝ) :
    HasDerivAt (expAffine φ ψ) (Real.exp (φ + ψ * x) * ψ) x :=
  (hasDerivAt_affine φ ψ x).exp

/-- First derivative of the exponential-affine family: `ψ * e^(φ + ψ x)`. -/
theorem deriv_expAffine (φ ψ : ℝ) :
    deriv (expAffine φ ψ) = fun x => ψ * expAffine φ ψ x := by
  funext x
  simp only [expAffine]
  have h : deriv (expAffine φ ψ) x = Real.exp (φ + ψ * x) * ψ :=
    (hasDerivAt_affine φ ψ x).exp.deriv
  rw [h]
  ring

/-- Bridge form with the right-hand side unfolded (used once, to compute the second
derivative). -/
theorem deriv_expAffine_mul (φ ψ : ℝ) :
    deriv (expAffine φ ψ) = fun x => Real.exp (φ + ψ * x) * ψ := by
  funext x
  exact (hasDerivAt_expAffine φ ψ x).deriv

/-- Second derivative of the exponential-affine family: `ψ² * e^(φ + ψ x)`. -/
theorem deriv_deriv_expAffine (φ ψ : ℝ) :
    deriv (deriv (expAffine φ ψ)) = fun x => ψ^2 * expAffine φ ψ x := by
  rw [deriv_expAffine_mul]
  funext x
  have h : deriv (fun y => Real.exp (φ + ψ * y) * ψ) x = Real.exp (φ + ψ * x) * ψ * ψ :=
    ((hasDerivAt_affine φ ψ x).exp.mul_const ψ).deriv
  rw [h]
  simp only [expAffine]
  ring

/-- The exponential-affine family is smooth. -/
theorem contDiff_expAffine (φ ψ : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (expAffine φ ψ) :=
  Real.contDiff_exp.comp (contDiff_const.add (contDiff_const.mul contDiff_id))

/-! ### The engine lemma -/

/-- **The affine engine.** The generator applied to an
exponential-affine function is an affine-in-`x` bracket times the function itself:
`L e^(φ + ψ x) = ((a ψ - κ ψ x) + σ²/2 ψ²) e^(φ + ψ x)` — Bagaria ch. 14, eq. 14.4
with `μ = a - κ x`, `v = σ²`. -/
theorem ouGenerator_expAffine (a κ σ φ ψ : ℝ) :
    ouGenerator a κ σ (expAffine φ ψ)
      = fun x => ((a * ψ - κ * ψ * x) + σ^2 / 2 * ψ^2) * expAffine φ ψ x := by
  funext x
  simp only [ouGenerator]
  rw [deriv_deriv_expAffine, deriv_expAffine]
  simp only [expAffine]
  ring

/-! ### The Riccati corollary -/

/-- **Riccati corollary (Bagaria ch. 14, eqs. 14.5–14.6).** The bracket of the engine
lemma is affine with slope `c₁ = b ψ = -κ ψ` (the `ψ`-equation's linear term) and
intercept `c₀ = a ψ + ½ d ψ² = a ψ + σ²/2 ψ²`. With `d = σ²`,
`b = -κ`, the slope evolves by `ψ' = b ψ + ½ d ψ²` and the intercept integrates
`φ' = a ψ + ½ c ψ²` (here `c = 0`); the Riccati flow below solves the slope ODE. -/
theorem ouBracket_affine (a κ σ φ ψ : ℝ) :
    ∃ (c₀ c₁ : ℝ), c₁ = -κ * ψ ∧ c₀ = a * ψ + σ^2 / 2 * ψ^2
      ∧ ouGenerator a κ σ (expAffine φ ψ)
        = fun x => (c₀ + c₁ * x) * expAffine φ ψ x := by
  refine ⟨a * ψ + σ^2 / 2 * ψ^2, -κ * ψ, rfl, rfl, ?_⟩
  rw [ouGenerator_expAffine]
  funext x
  ring

/-- The **Riccati flow**: the explicit Bernoulli solution of the CIR `ψ`-equation
`ψ' = −κψ + (σ²/2)ψ²`, `ψ(0) = ψ₀` (the engine's Riccati system with `b = −κ`,
`d = σ²`, Bagaria ch. 14, eq. 14.5):

`ψ(t) = 2κψ₀ e^{−κt} / (2κ − σ²ψ₀ (1 − e^{−κt}))`.

Sign note (checked on paper and symbolically before formalizing): the denominator is
`2κ − σ²ψ₀(1 − e^{−κt})`. The `+` variant does **not** solve the `ψ`-equation — its
residual is `−4κ²ψ₀²σ² / (2κe^{κt} + σ²ψ₀(e^{κt} − 1))² ≠ 0`; the minus-sign form
substitutes back exactly. -/
noncomputable def riccatiFlow (κ σ ψ₀ t : ℝ) : ℝ :=
  (2 * κ * ψ₀ * Real.exp (-(κ * t))) /
    (2 * κ - σ ^ 2 * ψ₀ * (1 - Real.exp (-(κ * t))))

/-- The Riccati flow starts at `ψ₀` (needs `κ ≠ 0`: at `t = 0` the denominator is
exactly `2κ`). -/
theorem riccatiFlow_at_zero (κ σ ψ₀ : ℝ) (hκ : κ ≠ 0) :
    riccatiFlow κ σ ψ₀ 0 = ψ₀ := by
  simp only [riccatiFlow, mul_zero, neg_zero, Real.exp_zero]
  field_simp
  ring

/-- **The Riccati ODE.** The flow solves `ψ' = −κψ + (σ²/2)ψ²`, guarded by the honest
nonvanishing of the Bernoulli denominator (at `t = 0` the guard reads `κ ≠ 0`; it holds
for all `t` whenever `σ²ψ₀ ≤ 2κ` or `t` is small). -/
theorem hasDerivAt_riccatiFlow (κ σ ψ₀ t : ℝ)
    (hD : 2 * κ - σ ^ 2 * ψ₀ * (1 - Real.exp (-(κ * t))) ≠ 0) :
    HasDerivAt (riccatiFlow κ σ ψ₀)
      ((-κ) * riccatiFlow κ σ ψ₀ t + σ ^ 2 / 2 * (riccatiFlow κ σ ψ₀ t) ^ 2) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-(κ * s)))
      (Real.exp (-(κ * t)) * -κ) t := by
    have hlin : HasDerivAt (fun s : ℝ => -κ * s) (-κ) t := by
      simpa using (hasDerivAt_id t).const_mul (-κ)
    simpa using hlin.exp
  have hnum : HasDerivAt (fun s : ℝ => 2 * κ * ψ₀ * Real.exp (-(κ * s)))
      (2 * κ * ψ₀ * (Real.exp (-(κ * t)) * -κ)) t := he.const_mul (2 * κ * ψ₀)
  have hsub1 : HasDerivAt (fun s : ℝ => 1 - Real.exp (-(κ * s)))
      (-(Real.exp (-(κ * t)) * -κ)) t := he.const_sub 1
  have hden : HasDerivAt (fun s : ℝ => 2 * κ - σ ^ 2 * ψ₀ * (1 - Real.exp (-(κ * s))))
      (-(σ ^ 2 * ψ₀ * -(Real.exp (-(κ * t)) * -κ))) t :=
    (hsub1.const_mul (σ ^ 2 * ψ₀)).const_sub (2 * κ)
  have hq := hnum.div hden hD
  have hval :
      ((2 * κ * ψ₀ * (Real.exp (-(κ * t)) * -κ)) *
          (2 * κ - σ ^ 2 * ψ₀ * (1 - Real.exp (-(κ * t)))) -
        (2 * κ * ψ₀ * Real.exp (-(κ * t))) *
          -(σ ^ 2 * ψ₀ * -(Real.exp (-(κ * t)) * -κ))) /
        (2 * κ - σ ^ 2 * ψ₀ * (1 - Real.exp (-(κ * t)))) ^ 2
      = (-κ) * ((2 * κ * ψ₀ * Real.exp (-(κ * t))) /
          (2 * κ - σ ^ 2 * ψ₀ * (1 - Real.exp (-(κ * t))))) +
        σ ^ 2 / 2 * ((2 * κ * ψ₀ * Real.exp (-(κ * t))) /
          (2 * κ - σ ^ 2 * ψ₀ * (1 - Real.exp (-(κ * t))))) ^ 2 := by
    field_simp
    ring
  rw [show riccatiFlow κ σ ψ₀ = fun s : ℝ => (2 * κ * ψ₀ * Real.exp (-(κ * s))) /
      (2 * κ - σ ^ 2 * ψ₀ * (1 - Real.exp (-(κ * s)))) from rfl, ← hval]
  exact hq


/-- The CIR generator `Lf = (κθ − κv) f' + (ξ² v / 2) f''` — the OU generator with drift
`a = κθ`, slope `−κ`, and a **`v`-proportional** diffusion term `½ ξ² v f''`. -/
noncomputable def cirGenerator (κ θ ξ : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun v => (κ * θ - κ * v) * deriv f v + (ξ ^ 2 * v / 2) * deriv (deriv f) v

/-! #### The CIR engine lemma -/

/-- **The CIR engine lemma.** The CIR generator applied to an exponential-affine function
is an affine-in-`v` bracket times the function itself:
`L e^(φ + ψ v) = ((κθψ − κψv) + ξ²/2 ψ² v) e^(φ + ψ v)` — Bagaria ch. 14, eq. 14.4 with
`μ = κθ − κv`, `v = ξ² v`. Reuses the derivative helpers verbatim. -/
theorem cirGenerator_expAffine (κ θ ξ φ ψ : ℝ) :
    cirGenerator κ θ ξ (expAffine φ ψ)
      = fun v => ((κ * θ * ψ - κ * ψ * v) + ξ^2 / 2 * ψ^2 * v) * expAffine φ ψ v := by
  funext v
  simp only [cirGenerator]
  rw [deriv_deriv_expAffine, deriv_expAffine]
  simp only [expAffine]
  ring

/-- **CIR Riccati corollary.** The bracket of `cirGenerator_expAffine` is affine with
intercept `c₀ = κθψ` (which the engine's φ-equation integrates: `φ' = κθψ`, the `c = 0`
case) and slope `c₁ = −κψ + (ξ²/2)ψ²` (the ψ-equation with `b = −κ`, `d = ξ²` — the
engine's Riccati system, Bagaria ch. 14, eqs. 14.5–14.6, in the CIR roles). -/
theorem cirBracket_affine (κ θ ξ φ ψ : ℝ) :
    ∃ (c₀ c₁ : ℝ), c₁ = -κ * ψ + ξ ^ 2 / 2 * ψ ^ 2 ∧ c₀ = κ * θ * ψ
      ∧ cirGenerator κ θ ξ (expAffine φ ψ)
        = fun v => (c₀ + c₁ * v) * expAffine φ ψ v := by
  refine ⟨κ * θ * ψ, -κ * ψ + ξ ^ 2 / 2 * ψ ^ 2, rfl, rfl, ?_⟩
  rw [cirGenerator_expAffine]
  funext v
  ring

/-- **The CIR engine-slope flow.** Reading the Riccati flow in the CIR roles
`(κ, ξ)` (i.e. `σ := ξ`) solves exactly the slope equation of `cirBracket_affine`:
`ψ' = −κψ + (ξ²/2)ψ²`, the `d = ξ²` case of the engine's Riccati system. Guard: the
honest Bernoulli nonvanishing `2κ − ξ²ψ₀(1 − e^{−κt}) ≠ 0`. Role note (honest): this is
the *undiscounted* exponent equation (characteristic-function side); the **bond**
`B`-factor obeys the discount-modified equation `B' = 1 − κB − (ξ²/2)B²` — the
discount term contributes the extra constant. -/
theorem hasDerivAt_riccatiFlow_cirRoles (κ ξ ψ₀ t : ℝ)
    (hD : 2 * κ - ξ ^ 2 * ψ₀ * (1 - Real.exp (-(κ * t))) ≠ 0) :
    HasDerivAt (riccatiFlow κ ξ ψ₀)
      ((-κ) * riccatiFlow κ ξ ψ₀ t + ξ ^ 2 / 2 * (riccatiFlow κ ξ ψ₀ t) ^ 2) t :=
  hasDerivAt_riccatiFlow κ ξ ψ₀ t hD


/-- Lambda form of `HasDerivAt.add`: Mathlib states the sum as the Pi-sum `f + g`;
assembly proofs need the eta-expanded lambda form. -/
theorem hasDerivAt_add' {f g : ℝ → ℝ} {f' g' : ℝ} {x : ℝ}
    (h : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => f y + g y) (f' + g') x := by
  have h2 := h.add hg
  rw [show (f + g) = fun y => f y + g y from by funext y; simp] at h2
  exact h2


/-- Lambda form of `HasDerivAt.sub` (the same Pi-vs-lambda situation as
`hasDerivAt_add'`). -/
theorem hasDerivAt_sub' {f g : ℝ → ℝ} {f' g' : ℝ} {x : ℝ}
    (h : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => f y - g y) (f' - g') x := by
  have h2 := h.sub hg
  rw [show (f - g) = fun y => f y - g y from by funext y; simp] at h2
  exact h2



end MathFin.ExpAffine
