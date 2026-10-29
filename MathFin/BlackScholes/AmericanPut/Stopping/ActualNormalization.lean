/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.GridNormalization

/-! # Physical-unit identification of the actual normalized stopping price

Exact finite-grid normalization passes to the stopping-value limit. This
argument uses neither a classical pricing solution nor boundary regularity.

## Result

Public entry points include `brownianUsualAmericanPut_normalization_log`,
`brownianUsualAmericanPut_normalization`, `brownianAmericanPut_normalization`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped NNReal Topology

theorem brownianUsualAmericanPut_normalization_log {K r q σ : ℝ}
    (hK : 0 < K) (hr : 0 ≤ r) (hσ : 0 < σ) (T : ℝ≥0) (x : ℝ) :
    brownianUsualAmericanPut K r q σ (Real.exp (x+Real.log K)) T =
      K*canonicalPrice (normalizedRate r σ) (normalizedRate q σ) x (σ^2/2*(T : ℝ)) := by
  let a := (σ^2/2).toNNReal
  have ha : 0 < a := Real.toNNReal_pos.mpr (by positivity)
  have hk : 0 ≤ normalizedRate r σ := by unfold normalizedRate; positivity
  have hleft := brownianGridPrice_tendsto_usual (q := q) (σ := σ) hK.le hr T (x+Real.log K)
  have hmesh : Tendsto (fun n => a*gridStep n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := a)).mul gridStep_tendsto_zero
  have hright := (tendsto_const_nhds (x := K)).mul
    (brownianGridPrice_tendsto_usual_of_mesh (q := normalizedRate q σ) (σ := Real.sqrt 2)
      (by norm_num : (0 : ℝ) ≤ 1) hk (a*T) x (fun n => mul_pos ha (gridStep_pos n)) hmesh)
  have hseq : (fun n => brownianGridPrice K r q σ T (gridStep n) (x+Real.log K)) =
      fun n => K*brownianGridPrice 1 (normalizedRate r σ) (normalizedRate q σ) (Real.sqrt 2)
        (a*T) (a*gridStep n) x :=
    funext (fun n => brownianGridPrice_normalization hK hσ T (gridStep n) x)
  rw [hseq] at hleft
  have htime : (σ^2/2*(T : ℝ)).toNNReal = a*T := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (by positivity),NNReal.coe_mul]
    simp only [a,Real.coe_toNNReal _ (by positivity : 0 ≤ σ^2/2)]
  simpa only [canonicalPrice,htime] using tendsto_nhds_unique hleft hright

theorem brownianUsualAmericanPut_normalization {K r q σ S : ℝ}
    (hK : 0 < K) (hr : 0 ≤ r) (hσ : 0 < σ) (hS : 0 < S) (T : ℝ≥0) :
    brownianUsualAmericanPut K r q σ S T =
      K*canonicalPrice (normalizedRate r σ) (normalizedRate q σ)
        (Real.log (S/K)) (σ^2/2*(T : ℝ)) := by
  have he : Real.exp (Real.log (S/K)+Real.log K) = S := by
    rw [Real.exp_add,Real.exp_log (div_pos hS hK),Real.exp_log hK,div_mul_cancel₀ _ hK.ne']
  simpa only [he] using brownianUsualAmericanPut_normalization_log hK hr hσ T (Real.log (S/K))

theorem brownianAmericanPut_normalization {K r q σ S : ℝ}
    (hK : 0 < K) (hr : 0 ≤ r) (hσ : 0 < σ) (hS : 0 < S) (T : ℝ≥0) :
    brownianAmericanPut K r q σ S T =
      K*canonicalPrice (normalizedRate r σ) (normalizedRate q σ)
        (Real.log (S/K)) (σ^2/2*(T : ℝ)) := by
  rw [← brownianUsualAmericanPut_eq_raw_of_pos hK.le hr hS T]
  exact brownianUsualAmericanPut_normalization hK hr hσ hS T

end MathFin.BlackScholes.AmericanPut.Stopping
