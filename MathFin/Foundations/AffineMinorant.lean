/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# Jensen's inequality through a supporting line

If `f` lies above the line through `(m, f m)` with slope `c` at almost every value of `X`, and
`X` has mean `m`, then `f(m) ≤ 𝔼[f(X)]`: the line averages to `f(m)`. For a convex `f` with a
supporting line at the mean this is Jensen's inequality. It asks for no closed domain, unlike
Mathlib's `ConvexOn.map_integral_le`, so it applies on `(0, ∞)`, where Black–Scholes prices are
convex in the spot (`BlackScholes/SpotConvexity.bsV_spot_tangent_le`).

## Main results

* `le_integral_of_affine_le`: `f(m) ≤ 𝔼[f(X)]` from an affine minorant through `(m, f m)`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]

/-- **Jensen's inequality through a supporting line.** If `X` has mean `m` and
`f m + c (X − m) ≤ f(X)` almost surely, then `f(m) ≤ 𝔼[f(X)]`. -/
theorem le_integral_of_affine_le {X : α → ℝ} {f : ℝ → ℝ} {m c : ℝ} (hX : Integrable X μ)
    (hm : ∫ a, X a ∂μ = m) (hf : Integrable (fun a ↦ f (X a)) μ)
    (h : ∀ᵐ a ∂μ, f m + c * (X a - m) ≤ f (X a)) : f m ≤ ∫ a, f (X a) ∂μ := by
  have hlin : Integrable (fun a ↦ c * (X a - m)) μ := (hX.sub (integrable_const m)).const_mul c
  calc f m = ∫ a, (f m + c * (X a - m)) ∂μ := by
        rw [integral_add (integrable_const _) hlin, integral_const_mul,
          integral_sub hX (integrable_const m), hm, integral_const, integral_const, probReal_univ,
          one_smul, one_smul, sub_self, mul_zero, add_zero]
    _ ≤ ∫ a, f (X a) ∂μ := integral_mono_ae ((integrable_const _).add hlin) hf h

end MathFin
