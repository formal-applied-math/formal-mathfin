/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Models.LocalVol.ForwardSmile
public import MathFin.Probability.Gaussian.NormalTail

/-!
# Tail condition for the Black form at general positive total variance

For any everywhere-positive total variance `w`, the Black form `blackForm k (w k)` tends to 0 at
large `k` exactly when `d₊(k, w k)` tends to `-∞`.

## Main results

* `blackForm_tendsto_zero_iff_dpl_tendsto_atBot`: Tail condition for the Black form at general
  positive total variance

## References

* [Roper, *Arbitrage free implied volatility surfaces*][Roper2010]

## Tags

tail condition, black form, total variance, d plus, call price, no-arbitrage, smile, MSC 91G20
-/

set_option autoImplicit false

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory ForwardSmile Filter Topology

/-- For any everywhere-positive total variance `w`, the Black form `blackForm k (w k)` tends to
`0` as `k → +∞` iff `dpl k (w k)` tends to `-∞`. -/
theorem blackForm_tendsto_zero_iff_dpl_tendsto_atBot (w : ℝ → ℝ) (hw : ∀ k, 0 < w k) :
    Filter.Tendsto (fun k ↦ MathFin.ForwardSmile.blackForm k (w k)) Filter.atTop (nhds 0) ↔
      Filter.Tendsto (fun k ↦ MathFin.ForwardSmile.dpl k (w k)) Filter.atTop Filter.atBot := by
  have hmills (k : ℝ) : -dmi k (w k) * (Real.exp k * Phi (dmi k (w k))) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left (neg_mul_Phi_le_gaussianPDFReal (dmi k (w k)))
      (Real.exp_pos k).le
    rw [exp_mul_pdf_dmi (hw k)] at this
    linarith [gaussianPDFReal_zero_one_le_one (dpl k (w k))]
  have hdiff (k : ℝ) : dmi k (w k) = dpl k (w k) - Real.sqrt (w k) := by
    rw [dmi_eq, dpl_eq]; ring
  have hs (k : ℝ) : 0 < Real.sqrt (w k) := Real.sqrt_pos.2 (hw k)
  have hE (k : ℝ) : 0 ≤ Real.exp k * Phi (dmi k (w k)) :=
    mul_nonneg (Real.exp_pos k).le (Phi_nonneg _)
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine tendsto_atBot.2 fun y ↦ ?_
    set δ := Phi (-|y|) with hδdef
    have hδ : 0 < δ := (Phi_mem_Ioo _).1
    set R := 4 / δ
    have hR : 0 < R := by positivity
    filter_upwards [(tendsto_order.1 h).2 (δ / 2) (half_pos hδ),
      eventually_ge_atTop (max 0 (R * (R / 2 + |y|)))] with k hlt hk
    by_contra hy
    have hy' : y < dpl k (w k) := not_le.1 hy
    have hk0 : 0 ≤ k := (le_max_left _ _).trans hk
    have hkR : R * (R / 2 + |y|) ≤ k := (le_max_right _ _).trans hk
    have hsd := dpl_eq k (w k)
    have hs0 := hs k
    have hRs : R < Real.sqrt (w k) := by
      by_contra hle
      have hle := not_lt.1 hle
      have hk1 : k = Real.sqrt (w k) * (Real.sqrt (w k) / 2 - dpl k (w k)) := by
        rw [hsd]; field_simp; ring
      have : Real.sqrt (w k) * (Real.sqrt (w k) / 2 - dpl k (w k))
          < R * (R / 2 + |y|) := by
        have h2 : Real.sqrt (w k) / 2 - dpl k (w k) < R / 2 + |y| := by
          linarith [neg_abs_le y]
        calc _ < Real.sqrt (w k) * (R / 2 + |y|) :=
              mul_lt_mul_of_pos_left h2 hs0
          _ ≤ R * (R / 2 + |y|) := mul_le_mul_of_nonneg_right hle (by positivity)
      linarith
    have hd : 2 / δ ≤ -dmi k (w k) := by
      have h1 : 0 ≤ k / Real.sqrt (w k) := div_nonneg hk0 hs0.le
      have h2 : 4 / δ / 2 = 2 / δ := by ring
      rw [dmi_eq]
      have : 4 / δ < Real.sqrt (w k) := hRs
      rw [neg_sub', neg_div]
      linarith
    have h3 := (mul_le_mul_of_nonneg_right hd (hE k)).trans (hmills k)
    rw [div_mul_eq_mul_div, div_le_iff₀ hδ] at h3
    have h4 : δ ≤ Phi (dpl k (w k)) :=
      strictMono_Phi.monotone (by linarith [neg_abs_le y])
    have h5 : blackForm k (w k) = Phi (dpl k (w k)) - Real.exp k * Phi (dmi k (w k)) := rfl
    have h6 : Real.exp k * Phi (dmi k (w k)) ≤ δ / 2 := by
      have hd0 : 0 < 2 / δ := by positivity
      have : 2 / δ * (Real.exp k * Phi (dmi k (w k))) ≤ 1 :=
        (mul_le_mul_of_nonneg_right hd (hE k)).trans (hmills k)
      rw [div_mul_eq_mul_div, div_le_iff₀ hδ] at this
      linarith
    linarith
  · have hΦ : Tendsto (fun k ↦ Phi (dpl k (w k))) atTop (𝓝 0) :=
      tendsto_Phi_atBot.comp h
    have hneg : Tendsto (fun k ↦ -dmi k (w k)) atTop atTop := by
      refine tendsto_atTop_mono (fun k ↦ ?_) (tendsto_neg_atBot_atTop.comp h)
      simp only [Function.comp_apply, hdiff]
      linarith [hs k]
    have hE0 : Tendsto (fun k ↦ Real.exp k * Phi (dmi k (w k))) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (tendsto_inv_atTop_zero.comp hneg) (Eventually.of_forall hE) ?_
      filter_upwards [hneg.eventually_gt_atTop 0] with k hk
      rw [Function.comp_apply, ← one_div, le_div_iff₀ hk]
      linarith [hmills k]
    simpa [blackForm] using hΦ.sub hE0

end MathFin
