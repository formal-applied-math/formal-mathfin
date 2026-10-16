/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib

/-!
# The OU generator on polynomials: the Hermite eigenlayer

The spectral route to solvability diagonalises the generator instead of diagonalising the
transform. For the OU process `dX = -κX dt + σ dW`, the generator

`L p = -(κ • X) * p' + (σ²/2) • p''`

maps real polynomials to real polynomials, and on that invariant subspace it is exactly
diagonal: the scaled Hermite polynomials `He_n(x/s)` (with stationary scale
`s² = σ²/2κ`) satisfy `L He_n(x/s) = -nκ He_n(x/s)` — eq. 14.16's OU case, Calc 14.14.
This file proves that polynomial core by induction on `Polynomial.hermite_succ`
(`Mathlib/RingTheory/Polynomial/Hermite/Basic.lean:54`), together with:

* the commutator identities that drive the induction (`ouGen_derivative`, `ouGen_X_mul`);
* the Gaussian stationary no-flux condition of Calc 14.13 (`gaussianScore_ou`,
  `gaussianNoFlux_ou`) — the one-dimensional reversibility mechanism, at eval level;
* the two-mode weighted-average gap inequality (`twoMode_rate_ge_gap`): the effective
  decay rate of a two-mode mixture sits above the slowest rate, so a one-exponential fit
  overstates mean reversion.

## Status

* **Proved here:** every declaration in this file, no proof holes; the `#print axioms`
  lines show the standard three for every public theorem.
* **Note on the commutator forms (stated in their general, true form):** the
  commutator identities, `ouGen_{κ,σ} p' = (ouGen_{κ,σ} p)' + κ • p'` and
  `ouGen_{κ,σ} (X*p) = X * ouGen_{κ,σ} p + σ² • p' - κ • (X*p)`, carry the κ and σ²
  coefficients explicitly, and the eigeninduction closes
  **iff `σ² = 2κ`** (the s = 1 stationary scale): at κ = σ = 1 the eigenidentity
  already fails at n = 2, since `ouGen_{1,1}(X² - 1) = -2X² + 1 ≠ -2(X² - 1)`.
  This file therefore states the commutators in their general form (with the κ and σ²
  coefficients), records the κ = σ = 1 displays verbatim as the instances
  (`ouGen_derivative_unit`, `ouGen_X_mul_unit`), and proves the eigenidentity at the
  forced unit normalization `κ = 1, σ² = 2` (spelled `ouGen 1 (Real.sqrt 2)`), where the
  eigenvalue display `-n` is true verbatim.
* **Not here (gated chapter mathematics, by design):** the `L²(π)` operator theory —
  self-adjointness of the generator against the stationary law (Calc 14.13's pairing,
  eq. 14.18), the eigenfunction expansion `P_t f = Σ c_n e^{-λ_n t} φ_n` (eq. 14.17),
  completeness of the Hermite basis, spectral-gap theory beyond the two-mode inequality,
  the general-diffusion no-flux statement (only the Gaussian instance is proved), the
  swirl as a stochastic process, and the Laguerre/Jacobi rows of the Pearson table
  (no Laguerre or Jacobi polynomials are available in the library).
-/

@[expose] public section

namespace MathFin.OUSpectral

open Polynomial Filter Topology Matrix

/-! ## The generator on polynomials -/

/-- **The OU generator as a map on real polynomials** (eq. 14.16's operator, OU case):
`L p = -(κ • X) * p.derivative + (σ²/2) • p.derivative.derivative` — drift term `-κx·p'`
plus diffusion term `(σ²/2)·p''`. Polynomial algebra only: on `Polynomial ℝ` this map is
triangular degree by degree (the drift lowers degree by one, the diffusion by two) —
which is why the polynomial moment ladder sees its diagonal eigenvalues before any
eigenvectors exist. -/
noncomputable def ouGen (κ σ : ℝ) (p : Polynomial ℝ) : Polynomial ℝ :=
  -(κ • Polynomial.X) * p.derivative + (σ ^ 2 / 2) • p.derivative.derivative

#print axioms ouGen

/-- Additivity of the generator (the polynomial derivative is additive). -/
theorem ouGen_add (κ σ : ℝ) (p q : Polynomial ℝ) :
    ouGen κ σ (p + q) = ouGen κ σ p + ouGen κ σ q := by
  simp only [ouGen, derivative_add, ← Polynomial.C_mul']
  ring

/-- Subtraction variant (used by the eigeninduction: `He_{n+1} = X·He_n - He_n'`). -/
theorem ouGen_sub (κ σ : ℝ) (p q : Polynomial ℝ) :
    ouGen κ σ (p - q) = ouGen κ σ p - ouGen κ σ q := by
  simp only [ouGen, derivative_sub, ← Polynomial.C_mul']
  ring

#print axioms ouGen_sub

#print axioms ouGen_add

/-- The generator kills constants (a constant has zero derivative). -/
theorem ouGen_const (κ σ a : ℝ) :
    ouGen κ σ (Polynomial.C a) = 0 := by
  simp [ouGen]

#print axioms ouGen_const

/-! ## The commutator identities (the induction engine)

The two identities below say how the generator commutes with `d/dx` and with
multiplication by `X` — the only two operations the Hermite recursion
`hermite (n+1) = X * hermite n - derivative (hermite n)` is built from. They are stated
in their general form: the coefficients that appear are exactly `κ` and `σ²`, and the
eigeninduction closes precisely when `σ² = 2κ` (the `s = 1` stationary scale). The
unit-parameter displays, which lack these coefficients, hold only at
`κ = σ = 1` and are recorded verbatim as `ouGen_derivative_unit` / `ouGen_X_mul_unit`
below. -/

/-- **Commutator with the derivative.** `L p' = (L p)' + κ • p'`: differentiating and
generating commute up to the drift coefficient `κ` re-supplied to the derivative term.
(At `κ = 1` this is the unit display `ouGen p' = (ouGen p)' + p'`, see
`ouGen_derivative_unit`.) -/
theorem ouGen_derivative (κ σ : ℝ) (p : Polynomial ℝ) :
    ouGen κ σ p.derivative = (ouGen κ σ p).derivative + κ • p.derivative := by
  simp only [ouGen, derivative_add, derivative_mul, derivative_C, derivative_X, map_neg,
    mul_one, ← Polynomial.C_mul']
  ring

#print axioms ouGen_derivative

/-- **Commutator with multiplication by `X`.** `L (X p) = X • L p + σ² • p' - κ • (X p)`:
multiplying by `X` and generating commute up to the creation term `σ² • p'` (the
diffusion coefficient acting on one derivative) minus the drift acting on the new
factor. (At `κ = σ = 1` this is the unit display
`ouGen (X * p) = X • ouGen p + p' - X • p`, see `ouGen_X_mul_unit`. Note the eigenidentity
`ouGen_hermite` below needs the *general* form at `σ² = 2κ`, where the creation
coefficient is `2κ`, not `1` — the two unit displays do not hold at a common
parameter pair; see the module header.) -/
theorem ouGen_X_mul (κ σ : ℝ) (p : Polynomial ℝ) :
    ouGen κ σ (X * p) = X * ouGen κ σ p + σ ^ 2 • p.derivative - κ • (X * p) := by
  have h1 : (X * p).derivative = p + X * p.derivative := by
    rw [derivative_mul, derivative_X, one_mul]
  have h2 : (p + X * p.derivative).derivative
      = p.derivative + (p.derivative + X * p.derivative.derivative) := by
    rw [derivative_add, derivative_mul, derivative_X, one_mul]
  have key : (σ ^ 2 / 2) • (p.derivative + (p.derivative + X * p.derivative.derivative))
      = σ ^ 2 • p.derivative + (σ ^ 2 / 2) • (X * p.derivative.derivative) := by
    rw [smul_add, smul_add, ← add_assoc, ← add_smul,
      show σ ^ 2 / 2 + σ ^ 2 / 2 = σ ^ 2 from by ring]
  simp only [ouGen, h1, h2]
  rw [key]
  simp only [← Polynomial.C_mul']
  ring

#print axioms ouGen_X_mul

/-- The derivative-commutator display, verbatim at the unit point `κ = σ = 1`
where it is true. (Not the parameter pair the eigeninduction runs at.) -/
theorem ouGen_derivative_unit (p : Polynomial ℝ) :
    ouGen 1 1 p.derivative = (ouGen 1 1 p).derivative + p.derivative := by
  rw [ouGen_derivative]
  simp

#print axioms ouGen_derivative_unit

/-- The multiplication-commutator display, verbatim at the unit point
`κ = σ = 1` where it is true. (The eigeninduction runs at `κ = 1, σ² = 2`, where the
creation coefficient is `2`, not `1`.) -/
theorem ouGen_X_mul_unit (p : Polynomial ℝ) :
    ouGen 1 1 (X * p) = X * ouGen 1 1 p + p.derivative - X * p := by
  rw [ouGen_X_mul]
  simp

#print axioms ouGen_X_mul_unit

/-! ## The Hermite eigenfunctions (Calc 14.14's identity)

The unit normalization at which the eigenidentity holds with eigenvalue `-n` is the
`s = 1` stationary scale `σ² = 2κ` with `κ = 1` — spelled `ouGen 1 (Real.sqrt 2)`, i.e.
the operator `p ↦ -X * p' + p''`. This is exactly the classical Hermite ODE
`He_n'' - x He_n' = -n He_n`, so the induction is the recursion
`hermite_succ : hermite (n+1) = X * hermite n - derivative (hermite n)`
(`Mathlib/RingTheory/Polynomial/Hermite/Basic.lean:54`) plus the two commutators. -/

/-- The `n`-th probabilists' Hermite polynomial over `ℝ`: `hermite n` (native to `ℤ[X]`,
`Hermite/Basic.lean:48`) mapped through the integer cast. At a real point `x` its
value is `He_n(x)`. -/
noncomputable def hermiteReal (n : ℕ) : Polynomial ℝ :=
  (Polynomial.hermite n).map (Int.castRingHom ℝ)

#print axioms hermiteReal

theorem hermiteReal_zero : hermiteReal 0 = 1 := by
  simp [hermiteReal, Polynomial.hermite_zero]

#print axioms hermiteReal_zero

theorem hermiteReal_succ (n : ℕ) :
    hermiteReal (n + 1) = X * hermiteReal n - (hermiteReal n).derivative := by
  rw [hermiteReal, Polynomial.hermite_succ, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_X, ← Polynomial.derivative_map]
  rfl

#print axioms hermiteReal_succ

/-- **The Hermite eigenidentity (eq. 14.16's OU case / Calc 14.14 at `κ = 1`, `s = 1`).**
The unit-normalized OU generator `ouGen 1 (Real.sqrt 2) = -X·d/dx + d²/dx²` (stationary
scale `σ² = 2κ = 2`) maps `He_n` to `-n • He_n`: the Hermite polynomials are eigenfunctions
of the OU generator with eigenvalues `-n` — the eigenvalues the triangular moment ladder
finds on the diagonal, now with their eigenvectors. Induction on
`hermite_succ`; the commutators supply the two terms and the induction closes exactly
because `σ² = 2κ` (here `2 = 2`). -/
theorem ouGen_hermite (n : ℕ) :
    ouGen 1 (Real.sqrt 2) (hermiteReal n) = -(n : ℝ) • hermiteReal n := by
  induction n with
  | zero => simp [ouGen, hermiteReal_zero]
  | succ n ih =>
    have hC2 : (Polynomial.C (2 : ℝ) : Polynomial ℝ) = 2 := by
      rw [show (2 : ℝ) = 1 + 1 from by norm_num, map_add, map_one]
      norm_num
    rw [hermiteReal_succ, ouGen_sub, ouGen_X_mul, ouGen_derivative, ih,
      Real.sq_sqrt (by norm_num), derivative_smul]
    simp only [one_smul, ← Polynomial.C_mul', Nat.cast_succ, map_add, map_one, map_neg]
    rw [hC2]
    ring

#print axioms ouGen_hermite

/-! ## The stationary scale: `He_n(x/s)` (Calc 14.14 in general position)

At the stationary scale `s² = σ²/2κ`, the eigenfunctions are the *rescaled* Hermite
polynomials `He_n(x/s)`. The chain rule for the scaling `x ↦ x/s` conjugates the general
generator into the unit one — the diffusion coefficient `σ²/2` loses exactly the factor
`s²` that the two derivatives of the scaling gain — so the unit eigenidentity transfers
with eigenvalue `-nκ` (the chapter's `L He_n = -nκ He_n`, Pearson-table OU row). -/

/-- The scaled Hermite polynomial `q_n(x) = He_n(x/s)`: `hermiteReal n` composed with the
scaling `X ↦ s⁻¹ • X`. -/
noncomputable def scaledHermite (s : ℝ) (n : ℕ) : Polynomial ℝ :=
  (hermiteReal n).comp (s⁻¹ • X)

#print axioms scaledHermite

theorem scaledHermite_eval (n : ℕ) (x s : ℝ) :
    Polynomial.eval x (scaledHermite s n) = Polynomial.eval (x / s) (hermiteReal n) := by
  have hx : Polynomial.eval x (s⁻¹ • X) = x / s := by
    rw [Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_X, div_eq_mul_inv, mul_comm]
  rw [scaledHermite, Polynomial.eval_comp, hx]

#print axioms scaledHermite_eval

/-- The unit generator spelled out: at `κ = 1`, `σ² = 2` the OU generator is the
operator `p ↦ -(X * p') + p''` — the classical Hermite ODE operator. -/
theorem ouGen_sqrt2 (f : Polynomial ℝ) :
    ouGen 1 (Real.sqrt 2) f = -(X * f.derivative) + f.derivative.derivative := by
  rw [ouGen, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), div_self two_ne_zero]
  simp

#print axioms ouGen_sqrt2

/-- **The scaling conjugation (the chain rule for `x ↦ x/s`).** Composing with the
scaling `X ↦ s⁻¹ • X` conjugates the general generator into `κ` times the unit one:
the drift coefficient survives, and the diffusion coefficient `σ²/2` divided by the
`s²` that the two chain-rule factors contribute is exactly `κ` (this is where the
stationary-scale identity `2κs² = σ²` enters). -/
theorem ouGen_comp_smulX (κ σ s : ℝ) (hs : s ≠ 0) (h : 2 * κ * s ^ 2 = σ ^ 2)
    (f : Polynomial ℝ) :
    ouGen κ σ (f.comp (s⁻¹ • X))
      = κ • (ouGen 1 (Real.sqrt 2) f).comp (s⁻¹ • X) := by
  have hX : (s⁻¹ • X).derivative = Polynomial.C s⁻¹ := by
    rw [← Polynomial.C_mul', derivative_mul, derivative_C, derivative_X, zero_mul,
      zero_add, mul_one]
  have hd1 : (f.comp (s⁻¹ • X)).derivative
      = Polynomial.C s⁻¹ * f.derivative.comp (s⁻¹ • X) := by
    rw [Polynomial.derivative_comp, hX]
  have hd2 : (f.comp (s⁻¹ • X)).derivative.derivative
      = Polynomial.C (s⁻¹ * s⁻¹) * f.derivative.derivative.comp (s⁻¹ • X) := by
    rw [hd1, derivative_mul, derivative_C, zero_mul, zero_add, Polynomial.derivative_comp,
      hX, ← mul_assoc, ← map_mul]
  have hκc : σ ^ 2 / 2 * (s⁻¹ * s⁻¹) = κ := by
    rw [← h]
    field_simp
  rw [ouGen, hd2, hd1]
  simp only [← Polynomial.C_mul']
  rw [show Polynomial.C (σ ^ 2 / 2)
        * (Polynomial.C (s⁻¹ * s⁻¹)
          * (derivative (derivative f)).comp (Polynomial.C s⁻¹ * X))
      = Polynomial.C (σ ^ 2 / 2 * (s⁻¹ * s⁻¹))
        * (derivative (derivative f)).comp (Polynomial.C s⁻¹ * X) from by
      rw [← mul_assoc, ← map_mul],
    hκc, ouGen_sqrt2, Polynomial.add_comp, Polynomial.neg_comp, Polynomial.mul_comp,
    Polynomial.X_comp]
  ring

#print axioms ouGen_comp_smulX

/-- **The scaled eigenidentity, polynomial level (Calc 14.14 / Pearson-table OU row).**
At the stationary scale `s² = σ²/2κ`, the generator maps the scaled Hermite polynomial
`q_n = He_n(x/s)` to `-(nκ) • q_n`. The eigenvalue is `-nκ` — the OU row of the
eigenvalue table, and the diagonal of the triangular moment ladder. -/
theorem ouGen_heigen_scaled_poly {κ σ s : ℝ} (hs : s ≠ 0) (h : 2 * κ * s ^ 2 = σ ^ 2)
    (n : ℕ) :
    ouGen κ σ (scaledHermite s n) = (-(n : ℝ) * κ) • scaledHermite s n := by
  rw [scaledHermite, ouGen_comp_smulX κ σ s hs h, ouGen_hermite, Polynomial.smul_comp,
    smul_smul, mul_comm]

#print axioms ouGen_heigen_scaled_poly

/-- **The scaled eigenidentity, eval level (the contract's display).** For
`q_n(x) = He_n(x/s)`: `eval x (L q_n) = -(nκ) · eval x q_n` at every point `x`. -/
theorem ouGen_heigen_scaled {κ σ s : ℝ} (hs : s ≠ 0) (h : 2 * κ * s ^ 2 = σ ^ 2)
    (n : ℕ) (x : ℝ) :
    Polynomial.eval x (ouGen κ σ (scaledHermite s n))
      = -(n : ℝ) * κ * Polynomial.eval x (scaledHermite s n) := by
  rw [ouGen_heigen_scaled_poly hs h n, Polynomial.eval_smul, smul_eq_mul]

#print axioms ouGen_heigen_scaled

theorem hermiteReal_two : hermiteReal 2 = X * X - 1 := by
  have h2 : Polynomial.hermite 2 = (X : Polynomial ℤ) * X - 1 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Polynomial.hermite_succ, Polynomial.hermite_one,
      derivative_X]
  rw [hermiteReal, h2]
  simp

#print axioms hermiteReal_two

/-- **The `n = 2` mechanism of Calc 14.14, verbatim.** With `f = (x/s)² - 1` (the
evaluated `He_2(x/s)`), the generator output evaluates to `-(2κ) · f` — the drift term
lowers the degree, the diffusion term supplies exactly the constant that closes the
polynomial back on itself, and the arithmetic uses `σ²/s² = 2κ` (via the stationary-scale
hypothesis). -/
theorem ouGen_heigen_two {κ σ s : ℝ} (hs : s ≠ 0) (h : 2 * κ * s ^ 2 = σ ^ 2) (x : ℝ) :
    Polynomial.eval x (ouGen κ σ (scaledHermite s 2))
      = -(2 : ℝ) * κ * ((x / s) ^ 2 - 1) := by
  rw [ouGen_heigen_scaled hs h 2 x, scaledHermite_eval, hermiteReal_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_one]
  ring

#print axioms ouGen_heigen_two

/-! ## The Gaussian no-flux condition (Calc 14.13, one dimension)

The reversibility mechanism of the spectral route, at its Gaussian instance: the
stationary density `π(x) ∝ exp(-x²/(2s²))` has score `π'/π = -x/s²`, so the drift and
diffusion fluxes cancel — `(σ²/2)·π' = -κx·π` exactly when `s² = σ²/2κ`. The
family-level engine behind this computation on the stack is the Rodrigues formula
`hermite_eq_deriv_gaussian` (`Mathlib/RingTheory/Polynomial/Hermite/Gaussian.lean:61`:
Hermite polynomials as
Gaussian-density derivatives); the two lemmas below are its `n = 0` and `n = 1`
footprint at the density level. -/

/-- **The Gaussian score (Calc 14.13's derivative, eval level).** The stationary
Gaussian density `π(x) = exp(-x²/(2s²))` satisfies `π'(x) = -(x/s²)·π(x)`: the log-density
is `-(x/s)²/2`, whose gradient `-(x/s²)` is the score. `deriv_exp` + the chain rule. -/
theorem gaussianScore_ou {s : ℝ} (hs : s ≠ 0) (x : ℝ) :
    deriv (fun y => Real.exp (-(y ^ 2 / (2 * s ^ 2)))) x
      = -(x / s ^ 2) * Real.exp (-(x ^ 2 / (2 * s ^ 2))) := by
  have h2 : HasDerivAt (fun y => -(y ^ 2 / (2 * s ^ 2))) (-(x / s ^ 2)) x := by
    have h1 := (hasDerivAt_pow 2 x).div_const (2 * s ^ 2)
    have hval : ((2 : ℕ) * x ^ (2 - 1)) / (2 * s ^ 2) = x / s ^ 2 := by
      norm_num
      field_simp
    rw [hval] at h1
    exact h1.neg
  exact (h2.exp.deriv).trans (by ring)

#print axioms gaussianScore_ou

/-- **The no-flux condition (eq. 14.19's stationary Gaussian instance).** At the
stationary scale `s² = σ²/2κ`, the drift flux `-κx·π` balances the diffusion flux
`(σ²/2)·π'`: `μπ = ½(σ²π)'` of Calc 14.13, which is what makes the generator symmetric
on its polynomial domain. -/
theorem gaussianNoFlux_ou {κ σ s : ℝ} (hs : s ≠ 0) (h : 2 * κ * s ^ 2 = σ ^ 2) (x : ℝ) :
    σ ^ 2 / 2 * deriv (fun y => Real.exp (-(y ^ 2 / (2 * s ^ 2)))) x
      = -(κ * x) * Real.exp (-(x ^ 2 / (2 * s ^ 2))) := by
  have hE : Real.exp (-(x ^ 2 / (2 * s ^ 2))) ≠ 0 := (Real.exp_pos _).ne'
  rw [gaussianScore_ou hs x]
  field_simp
  have hx : σ ^ 2 * x = 2 * x * s ^ 2 * κ := by rw [← h]; ring
  linarith

#print axioms gaussianNoFlux_ou

/-! ## The gap bias (the "asymptotic rate" remark, two modes)

The chapter's effective decay rate of a multimodal expansion is the weighted average
`Σ λ_n c_n e^{-λ_n t} / Σ c_n e^{-λ_n t}`. With two modes and weights of one sign, that
average sits above the slowest rate `λ₁` for every `t` — so fitting a single exponential
to a two-mode decay reads off a rate above `λ₁` and overstates mean reversion (the
chapter's second, independent route to the ch. 20 estimation bias). -/

/-- **The two-mode gap inequality.** For rates `0 ≤ λ₁ ≤ λ₂`, positive mode weights
`0 < c₁, c₂` and any `t ≥ 0`, the effective decay rate of the two-mode mixture — the
weighted average of the rates, weighted by the surviving mode masses — is at least the
slowest rate `λ₁`. The gap `λ₂ - λ₁` shows up as the excess carried by the fast mode;
the chapter's one-exponential-fit warning is exactly this inequality read backwards. -/
theorem twoMode_rate_ge_gap {l₁ l₂ c₁ c₂ t : ℝ} (_hl₁ : 0 ≤ l₁) (hl₂ : l₁ ≤ l₂)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (_ht : 0 ≤ t) :
    (l₁ * c₁ * Real.exp (-(l₁ * t)) + l₂ * c₂ * Real.exp (-(l₂ * t)))
      / (c₁ * Real.exp (-(l₁ * t)) + c₂ * Real.exp (-(l₂ * t))) ≥ l₁ := by
  set E₁ := Real.exp (-(l₁ * t)) with hE₁
  set E₂ := Real.exp (-(l₂ * t)) with hE₂
  have hE₁pos : 0 < E₁ := Real.exp_pos _
  have hE₂pos : 0 < E₂ := Real.exp_pos _
  have hD : (c₁ * E₁ + c₂ * E₂) ≠ 0 :=
    (add_pos (mul_pos hc₁ hE₁pos) (mul_pos hc₂ hE₂pos)).ne'
  have hkey : 0 ≤ (l₂ - l₁) * (c₂ * E₂) :=
    mul_nonneg (sub_nonneg.2 hl₂) (mul_nonneg hc₂.le hE₂pos.le)
  rw [ge_iff_le]
  field_simp
  nlinarith [hkey]

#print axioms twoMode_rate_ge_gap

/-! ## Stretch results (Ex. 14.2 fragments — the swirl, matrix algebra only)

The chapter's two-dimensional counterexample — the swirl `dZ = -AZ dt + dW` with
`A = [[1, θ], [-θ, 1]]`, whose antisymmetric part rotates — contributes two matrix
fragments that need no process theory: the characteristic polynomial of `-A` (roots
`-1 ± iθ`: the spectrum leaves the real line, so no real orthogonal expansion exists),
and the isotropy of the stationary covariance (`AΣ + ΣAᵀ = I` forces `Σ = ½I`: the
rotation drops out of the snapshot, which is exactly why the snapshot cannot detect
reversibility). Plus the stationary-variance limit of the OU law. -/

/-- **Stretch — the swirl's characteristic polynomial.** The eigenvalues of `-A` are the
roots of `(X + 1)² + θ²`, i.e. `-1 ± iθ` — off the real line for `θ ≠ 0`, the spectral
signature of a non-reversible drift. (`Matrix.charpoly` at `Charpoly/Basic.lean:132`,
determinant by `Matrix.det_fin_two_of`.) -/
theorem swirl_charpoly (θ : ℝ) :
    (Matrix.charpoly (!![-1, -θ; θ, -1] : Matrix (Fin 2) (Fin 2) ℝ))
      = (X + 1) ^ 2 + Polynomial.C (θ ^ 2) := by
  have h : (Matrix.charmatrix (!![-1, -θ; θ, -1] : Matrix (Fin 2) (Fin 2) ℝ))
      = !![(X : ℝ[X]) + 1, Polynomial.C θ; -Polynomial.C θ, (X : ℝ[X]) + 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [map_neg, map_one]
  show (Matrix.charmatrix _).det = _
  rw [h, Matrix.det_fin_two_of, mul_neg, ← map_mul, sq θ]
  ring

#print axioms swirl_charpoly

/-- **Stretch — the swirl's stationary covariance is isotropic.** Any symmetric `Σ`
solving the stationary-covariance equation `AΣ + ΣAᵀ = I` for the swirl matrix
`A = [[1, θ], [-θ, 1]]` is `½I`: the rotation term `θ` cancels out of the equation, so
the snapshot carries no trace of the circulation — reversibility fails where the
spectrum went complex, not where the stationary law is visible. -/
theorem swirl_isotropy (θ a b d : ℝ)
    (h : (!![(1 : ℝ), θ; -θ, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![a, b; b, d]
        + !![a, b; b, d] * !![(1 : ℝ), -θ; θ, 1] = 1) :
    (!![(a : ℝ), b; b, d] : Matrix (Fin 2) (Fin 2) ℝ)
      = !![(1 / 2 : ℝ), 0; 0, 1 / 2] := by
  have hM : ((!![(1 : ℝ), θ; -θ, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![a, b; b, d]
        + !![a, b; b, d] * !![(1 : ℝ), -θ; θ, 1])
      = !![2 * a + 2 * θ * b, 2 * b + θ * d - θ * a; 2 * b + θ * d - θ * a,
        2 * d - 2 * θ * b] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp <;> ring
  rw [hM] at h
  have e00 : 2 * a + 2 * θ * b = 1 := by simpa using congrFun (congrFun h 0) 0
  have e01 : 2 * b + θ * d - θ * a = 0 := by simpa using congrFun (congrFun h 0) 1
  have e11 : 2 * d - 2 * θ * b = 1 := by simpa using congrFun (congrFun h 1) 1
  have hda : d - a = 2 * θ * b := by linarith [e00, e11]
  have hθ2 : θ * d - θ * a = 2 * θ * (θ * b) := by
    have h1 : θ * d - θ * a = θ * (d - a) := by ring
    rw [h1, hda]
    ring
  have hsum : 2 * b + 2 * θ * (θ * b) = 0 := by linarith [e01, hθ2]
  have hkey : (1 + θ ^ 2) * b = 0 := by
    have h2 : (1 + θ ^ 2) * b = b + θ * (θ * b) := by ring
    linarith [hsum, h2]
  have hb : b = 0 := by
    rcases mul_eq_zero.1 hkey with h1 | h2
    · exact absurd h1 (by nlinarith [sq_nonneg θ])
    · exact h2
  rw [hb] at e00 e11
  simp only [mul_zero, add_zero] at e00 e11
  have ha : a = 1 / 2 := by linarith [e00]
  have hd : d = 1 / 2 := by linarith [e11]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [ha, hb, hd]

#print axioms swirl_isotropy

/-- **Stretch — the stationary variance as a limit of the OU law.** The variance factor
of the explicit OU law `N(x₀e^{-(k/2)t}, (s²/k)(1 - e^{-kt}))` (the same Gaussian-law
computation as `VasicekSDEGaussian.vasicekShortRate_hasLaw_gaussian`) tends to `s²/k`
as the horizon grows — the stationary
scale `s²/k` (i.e. `σ²/2κ` in generator parametrization) is the limit of a landed law,
not a new object. -/
theorem ouStationaryVariance_tendsto {k s : ℝ} (hk : 0 < k) :
    Tendsto (fun t : ℝ => s ^ 2 / k * (1 - Real.exp (-(k * t)))) atTop (𝓝 (s ^ 2 / k)) := by
  have hkt : Tendsto (fun t : ℝ => k * t) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hk).mpr tendsto_id
  have hn : Tendsto (fun t : ℝ => -(k * t)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hkt
  have he : Tendsto (fun t : ℝ => Real.exp (-(k * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hn
  have hsub := (tendsto_const_nhds (x := (1 : ℝ))).sub he
  simpa using (tendsto_const_nhds (x := s ^ 2 / k)).mul hsub

#print axioms ouStationaryVariance_tendsto
