/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.BlackScholes.SABRImpliedVol

/-!
# The β → 1 and ν → 0 limits of the Le Floc'h–Kennedy SABR building blocks

Le Floc'h & Kennedy, "Explicit SABR Calibration through Simple Expansions" (SSRN 2467231,
2014), write the SABR implied volatility (model `dF = α̂ F^β dW₁`, `dα̂ = ν α̂ dW₂`,
`dW₁ dW₂ = ρ dt`) in terms of two building blocks of the strike `k`, given the forward `F`:

* the normalizing transform `y(k) = ∫_F^k x^(-β) dx = -(F^(1-β) - k^(1-β)) / (1-β)`;
* the distance `Dint(k) = ∫_k^F dx / D(x)`, `D(x) = √(α² + 2αρν y(x) + ν² y(x)²) · x^β`, in
  closed form `Dint = (1/ν) · log((√(1 + 2ρνy/α + (νy/α)²) - ρ - νy/α) / (1-ρ))`;

with leading-order vol `ω₀(k) = log(F/k) / Dint(k)`. Both closed forms are removable
singularities on admissible SABR parameters: `y` is `0/0` at `β = 1` (the lognormal SABR) and
`Dint` is `(1/ν)·log 1 = ∞ · 0` at `ν = 0` (no vol-of-vol). This file proves the limits that
fill them:

* `tendsto_sabrFKY_beta_one` — `y(k) → -log(F/k)` as `β → 1` (`F, k > 0`);
* `tendsto_sabrFKDint_nu_zero` — `Dint → -y/α` as `ν → 0` (`ρ ≠ 1`, every `α`, `y`);
* `tendsto_sabrFKOmega0_nu_zero` — hence `ω₀(k) → -α log(F/k) / y` as `ν → 0` (`y ≠ 0`).

The `ν → 0` limit reuses Hagan's `x(z)` (`sabrX`, `BlackScholes/SABRImpliedVol.lean`):
`Dint = ν⁻¹ · x(-νy/α)` (`sabrFKDint_eq_sabrX`), so the limit is the slope `x'(0) = 1`
(`hasDerivAt_sabrX_zero`) times the inner derivative `-y/α`. The transform `y` itself has no
Hagan counterpart (Hagan's `z` uses the geometric-mean approximation `(Fk)^((1-β)/2) log(F/k)`
in place of the exact integral `y`).

What is *not* formalized: the full Le Floc'h–Kennedy vol (the `ω₀` correction terms in
`log ω₀`, `D(F)`, `D(k)` and the `(k^β - F^β)/(k - F)` factor) and its limit; the derivation of
the expansion from the SABR dynamics; and how well it approximates the true SABR implied vol.
The definitions below are the closed forms as printed, so at `β = 1` / `ν = 0` they take Lean's
junk values (`x / 0 = 0`); the theorems are about the limits, not those values.
-/

@[expose] public section

namespace MathFin

open Filter Topology

/-- **Le Floc'h–Kennedy's normalizing transform** `y(k) = -(F^(1-β) - k^(1-β)) / (1-β)`
(`= ∫_F^k x^(-β) dx` for `β ≠ 1`). At `β = 1` the closed form is `0/0`;
`tendsto_sabrFKY_beta_one` gives its limit `-log(F/k)`. -/
noncomputable def sabrFKY (F k β : ℝ) : ℝ := -(F ^ (1 - β) - k ^ (1 - β)) / (1 - β)

/-- **Le Floc'h–Kennedy's distance** `Dint` as a function of `y = y(k)`:
`(1/ν) · log((√(1 + 2ρνy/α + (νy/α)²) - ρ - νy/α) / (1-ρ))` (`= ∫_k^F dx / D(x)` for
`ν ≠ 0`). At `ν = 0` the closed form is `(1/0) · log 1`; `tendsto_sabrFKDint_nu_zero`
gives its limit `-y/α`. -/
noncomputable def sabrFKDint (α ρ ν y : ℝ) : ℝ :=
  1 / ν * Real.log ((Real.sqrt (1 + 2 * ρ * ν / α * y + (ν / α * y) ^ 2) - ρ - ν / α * y)
    / (1 - ρ))

/-- **The leading-order Le Floc'h–Kennedy vol** `ω₀ = log(F/k) / Dint`, with `Dint` evaluated
at `y`. -/
noncomputable def sabrFKOmega0 (F k α ρ ν y : ℝ) : ℝ := Real.log (F / k) / sabrFKDint α ρ ν y

/-- **`y(k) → -log(F/k)` as `β → 1`, `β ≠ 1`** (`F, k > 0`): the `0/0` in the transform at the
lognormal SABR `β = 1` is removable. With `ε = 1 - β`, `y = (k^ε - F^ε)/ε`, the difference
quotient at `ε = 0` of `ε ↦ k^ε - F^ε`, whose derivative there is `log k - log F`. -/
theorem tendsto_sabrFKY_beta_one {F k : ℝ} (hF : 0 < F) (hk : 0 < k) :
    Tendsto (fun β ↦ sabrFKY F k β) (𝓝[≠] 1) (𝓝 (-Real.log (F / k))) := by
  have hg : HasDerivAt (fun ε : ℝ ↦ k ^ ε - F ^ ε) (Real.log k - Real.log F) 0 := by
    have h1 : HasDerivAt (fun ε : ℝ ↦ k ^ ε) (k ^ (0 : ℝ) * Real.log k) 0 :=
      (Real.hasStrictDerivAt_const_rpow hk 0).hasDerivAt
    have h2 : HasDerivAt (fun ε : ℝ ↦ F ^ ε) (F ^ (0 : ℝ) * Real.log F) 0 :=
      (Real.hasStrictDerivAt_const_rpow hF 0).hasDerivAt
    have h := h1.sub h2
    simp only [Real.rpow_zero, one_mul] at h
    exact h
  have hslope := hasDerivAt_iff_tendsto_slope_zero.mp hg
  have hmap : Tendsto (fun β : ℝ ↦ 1 - β) (𝓝[≠] 1) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun β : ℝ ↦ 1 - β) (𝓝 1) (𝓝 (1 - 1)) :=
        tendsto_const_nhds.sub tendsto_id
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with β hβ
      exact sub_ne_zero.mpr (Ne.symm hβ)
  rw [Real.log_div hF.ne' hk.ne', neg_sub]
  refine (hslope.comp hmap).congr fun β ↦ ?_
  simp only [Function.comp_apply, zero_add, Real.rpow_zero, sub_self, sub_zero, smul_eq_mul,
    sabrFKY]
  ring

/-- **`Dint` is `ν⁻¹ · x(-νy/α)`** for Hagan's `x(z)` (`sabrX`): the two closed forms share the
same `log((√· ± z - ρ)/(1-ρ))` function, at the argument `z = -νy/α`. -/
theorem sabrFKDint_eq_sabrX (α ρ ν y : ℝ) :
    sabrFKDint α ρ ν y = ν⁻¹ * sabrX ρ (-(y / α) * ν) := by
  have hA : 1 + 2 * ρ * ν / α * y + (ν / α * y) ^ 2
      = 1 - 2 * ρ * (-(y / α) * ν) + (-(y / α) * ν) ^ 2 := by ring
  unfold sabrFKDint sabrX
  rw [one_div, hA]
  congr 3
  ring

/-- **`Dint → -y/α` as `ν → 0`, `ν ≠ 0`** (`ρ ≠ 1`, every `α`, `y`): the `∞ · 0` in the
closed form at zero vol-of-vol is removable. Via `sabrFKDint_eq_sabrX`, `Dint` is the difference
quotient at `ν = 0` of `ν ↦ x(-(y/α)ν)`, whose derivative there is `x'(0) · (-y/α) = -y/α`
(`hasDerivAt_sabrX_zero`). This is `∫_k^F dx / D(x)` with `D(x) = α x^β`, the `ν = 0` diffusion
coefficient. -/
theorem tendsto_sabrFKDint_nu_zero {α ρ : ℝ} (hρ : ρ ≠ 1) (y : ℝ) :
    Tendsto (fun ν ↦ sabrFKDint α ρ ν y) (𝓝[≠] 0) (𝓝 (-y / α)) := by
  have hinner : HasDerivAt (fun ν : ℝ ↦ -(y / α) * ν) (-(y / α)) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (-(y / α))
  have hg := HasDerivAt.comp_of_eq (h₂ := sabrX ρ) (0 : ℝ) (hasDerivAt_sabrX_zero hρ) hinner
    (by simp)
  have h0 : sabrX ρ 0 = 0 := by
    have h1ρ : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
    simp [sabrX, h1ρ]
  have hslope := hasDerivAt_iff_tendsto_slope_zero.mp hg
  rw [one_mul] at hslope
  rw [neg_div]
  refine hslope.congr fun ν ↦ ?_
  simp [sabrFKDint_eq_sabrX, h0]

/-- **The leading-order vol at zero vol-of-vol**: `ω₀ → -α log(F/k) / y` as `ν → 0`, `ν ≠ 0`
(`α ≠ 0`, `ρ ≠ 1`, `y ≠ 0`, i.e. `k ≠ F`). With `y = -log(F/k)` (the `β = 1` value of
`tendsto_sabrFKY_beta_one`) this is `α`, the lognormal vol. -/
theorem tendsto_sabrFKOmega0_nu_zero {F k α ρ y : ℝ} (hα : α ≠ 0) (hρ : ρ ≠ 1) (hy : y ≠ 0) :
    Tendsto (fun ν ↦ sabrFKOmega0 F k α ρ ν y) (𝓝[≠] 0) (𝓝 (-α * Real.log (F / k) / y)) := by
  have h := tendsto_const_nhds (x := Real.log (F / k)).div (tendsto_sabrFKDint_nu_zero hρ y)
    (div_ne_zero (neg_ne_zero.mpr hy) hα)
  have e : -α * Real.log (F / k) / y = Real.log (F / k) / (-y / α) := by
    field_simp
  rw [e]
  exact h.congr fun ν ↦ rfl

end MathFin
