/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.HeatBoundaryKernel

/-! # Continuous half-line boundary extension

The fixed-density formula includes the boundary x=0 without a singular integral.
For x>0 it agrees with integration against the heat boundary kernel in elapsed
time. This file proves continuity, the exact boundary trace, and causality for
bounded continuous data. `HeatBoundaryEquation` proves interior smoothness and
the PDE for compact continuous data. `IntervalHeatBoundary` constructs the
finite-interval heat correction; assembly in pricing coordinates is separate.

## Result

Public entry points include `heatBoundaryExtension`, `heatBoundaryExtension_integrable`,
`heatBoundaryExtension_continuous`, `heatBoundaryExtension_boundary`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory
open scoped Topology

/-- Extension of the boundary datum `g` to depth `x`, as the fixed-density integral
`∫ s in Ioi 0, heatBoundaryKernel s 1 * g (t-x^2*s)`. -/
noncomputable def heatBoundaryExtension (g : ℝ → ℝ) (x t : ℝ) : ℝ :=
  ∫ s in Ioi 0, heatBoundaryKernel s 1 * g (t-x^2*s)

theorem heatBoundaryExtension_integrable {g : ℝ → ℝ} (hg : Continuous g)
    {C : ℝ} (hC : ∀ t, ‖g t‖ ≤ C) (x t : ℝ) :
    IntegrableOn (fun s => heatBoundaryKernel s 1 * g (t-x^2*s)) (Ioi 0) := by
  apply (heatBoundaryKernel_integrable (by norm_num : (0 : ℝ) < 1)).mul_bdd
  · exact (hg.comp (continuous_const.sub (continuous_const.mul continuous_id))).aestronglyMeasurable
  · exact Eventually.of_forall (fun s => hC (t-x^2*s))

theorem heatBoundaryExtension_continuous {g : ℝ → ℝ} (hg : Continuous g)
    {C : ℝ} (hC : ∀ t, ‖g t‖ ≤ C) :
    Continuous (fun z : ℝ × ℝ => heatBoundaryExtension g z.1 z.2) := by
  apply continuous_of_dominated
    (bound := fun s => heatBoundaryKernel s 1 * C)
  · intro z
    exact (heatBoundaryExtension_integrable hg hC z.1 z.2).aestronglyMeasurable
  · intro z
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [norm_mul,Real.norm_of_nonneg (heatBoundaryKernel_pos hs (by norm_num)).le]
    exact mul_le_mul_of_nonneg_left (hC _) (heatBoundaryKernel_pos hs (by norm_num)).le
  · exact (heatBoundaryKernel_integrable (by norm_num : (0 : ℝ) < 1)).mul_const C
  · exact Eventually.of_forall fun s => continuous_const.mul
      (hg.comp (continuous_snd.sub ((continuous_fst.pow 2).mul continuous_const)))

theorem heatBoundaryExtension_boundary (g : ℝ → ℝ) (t : ℝ) :
    heatBoundaryExtension g 0 t = g t := by
  simp only [heatBoundaryExtension,zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_mul,sub_zero]
  rw [integral_mul_const,heatBoundaryKernel_integral (by norm_num : (0 : ℝ) < 1),one_mul]

/-- Joint approach to the boundary is valid, not only a fixed-time trace. -/
theorem heatBoundaryExtension_tendsto {g : ℝ → ℝ} (hg : Continuous g)
    {C : ℝ} (hC : ∀ t, ‖g t‖ ≤ C) (t : ℝ) :
    Tendsto (fun z : ℝ × ℝ => heatBoundaryExtension g z.1 z.2) (𝓝 (0,t)) (𝓝 (g t)) := by
  simpa only [heatBoundaryExtension_boundary] using
    (heatBoundaryExtension_continuous hg hC).continuousAt.tendsto (x := (0,t))

theorem heatBoundaryExtension_causal {g : ℝ → ℝ} {a : ℝ}
    (hg : ∀ t, t ≤ a → g t = 0) (x : ℝ) {t : ℝ} (ht : t ≤ a) :
    heatBoundaryExtension g x t = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro s hs
  rw [hg _ (le_trans (sub_le_self _ (mul_nonneg (sq_nonneg x) hs.le)) ht),mul_zero]

theorem heatBoundaryExtension_bound {g : ℝ → ℝ}
    {C : ℝ} (hC : ∀ t, ‖g t‖ ≤ C) (x t : ℝ) :
    ‖heatBoundaryExtension g x t‖ ≤ C := by
  calc
    ‖heatBoundaryExtension g x t‖ ≤
        ∫ s in Ioi 0, heatBoundaryKernel s 1 * C := by
      apply norm_integral_le_of_norm_le
        ((heatBoundaryKernel_integrable (by norm_num : (0 : ℝ) < 1)).mul_const C)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      rw [norm_mul,Real.norm_of_nonneg (heatBoundaryKernel_pos hs (by norm_num)).le]
      exact mul_le_mul_of_nonneg_left (hC _) (heatBoundaryKernel_pos hs (by norm_num)).le
    _ = C := by
      rw [integral_mul_const,heatBoundaryKernel_integral (by norm_num : (0 : ℝ) < 1),one_mul]

/-- Away from the boundary the fixed-density formula is the usual elapsed-time integral. -/
theorem heatBoundaryExtension_eq_integral (g : ℝ → ℝ) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    heatBoundaryExtension g x t = ∫ s in Ioi 0, heatBoundaryKernel s x * g (t-s) := by
  have he := integral_comp_mul_left_Ioi
    (fun s => heatBoundaryKernel s x * g (t-s)) 0 (sq_pos_of_pos hx)
  calc
    heatBoundaryExtension g x t =
        ∫ s in Ioi 0, x^2 * (heatBoundaryKernel (x^2*s) x * g (t-x^2*s)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      change heatBoundaryKernel s 1 * g (t-x^2*s) =
        x^2 * (heatBoundaryKernel (x^2*s) x * g (t-x^2*s))
      rw [← mul_assoc,heatBoundaryKernel_scale hx hs]
    _ = x^2 * ∫ s in Ioi 0, heatBoundaryKernel (x^2*s) x * g (t-x^2*s) :=
      integral_const_mul _ _
    _ = ∫ s in Ioi 0, heatBoundaryKernel s x * g (t-s) := by
      rw [he]
      simp only [mul_zero,smul_eq_mul]
      field_simp

end MathFin.BlackScholes.AmericanPut.Stopping
