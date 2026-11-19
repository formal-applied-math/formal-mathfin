/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Models.LocalVol.ForwardSmile
public import MathFin.Probability.Gaussian.NormalTail

/-!
# The tail condition for the Black form

A total-variance smile `w > 0` prices the forward-normalised call at log-strike `k` by the Black
form `blackForm k (w k) = Φ(d₊) − eᵏΦ(d₋)`. Roper's Theorem 2.1 asks of a call price function
that it vanish at large strikes. For the Black form this is a condition on `d₊` alone: the call
tends to `0` exactly when `d₊(k, w k) → −∞`.

The easy direction is the bound `0 ≤ eᵏΦ(d₋) ≤ 1/|d₋|` (the Mills bound `−xΦ(x) ≤ φ(x)`,
transported by `eᵏφ(d₋) = φ(d₊) ≤ 1`). Conversely, if `d₊` stays above some `y` along a sequence
of strikes, then `Φ(d₊) ≥ Φ(−|y|)` there, while `k = √w(√w/2 − d₊)` forces `√w` to grow, so the
same Mills bound makes `eᵏΦ(d₋)` small and the call stays away from `0`.

The SVI tail condition (`SVI.tendsto_bsSmile_zero_iff`) is the instance at the raw SVI variance.

## Main results

* `blackForm_tendsto_zero_iff_dpl_tendsto_atBot`: for an everywhere-positive total variance `w`,
  `blackForm k (w k) → 0` as `k → ∞` iff `d₊(k, w k) → −∞`.

## References

* [Roper, *Arbitrage free implied volatility surfaces*][Roper2010], Theorem 2.1

## Tags

tail condition, Black form, total variance, large-strike behaviour, call price function,
no-arbitrage, smile, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open ProbabilityTheory ForwardSmile Filter Topology

/-- **The tail condition for the Black form.** For an everywhere-positive total variance `w`,
the Black form `blackForm k (w k)` tends to `0` as `k → ∞` iff `d₊(k, w k)` tends to `−∞`. -/
theorem blackForm_tendsto_zero_iff_dpl_tendsto_atBot (w : ℝ → ℝ) (hw : ∀ k, 0 < w k) :
    Tendsto (fun k ↦ blackForm k (w k)) atTop (𝓝 0) ↔
      Tendsto (fun k ↦ dpl k (w k)) atTop atBot := by
  -- the Mills bound, transported by `eᵏφ(d₋) = φ(d₊) ≤ 1`
  have hmills (k : ℝ) : -dmi k (w k) * (Real.exp k * Phi (dmi k (w k))) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left (neg_mul_Phi_le_gaussianPDFReal (dmi k (w k)))
      (Real.exp_pos k).le
    rw [exp_mul_pdf_dmi (hw k)] at this
    linarith [gaussianPDFReal_zero_one_le_one (dpl k (w k))]
  have hE (k : ℝ) : 0 ≤ Real.exp k * Phi (dmi k (w k)) :=
    mul_nonneg (Real.exp_pos k).le (Phi_nonneg _)
  refine ⟨fun h ↦ tendsto_atBot.2 fun y ↦ ?_, fun h ↦ ?_⟩
  · set δ := Phi (-|y|)
    have hδ : 0 < δ := (Phi_mem_Ioo _).1
    set R := 4 / δ
    filter_upwards [(tendsto_order.1 h).2 (δ / 2) (half_pos hδ),
      eventually_ge_atTop (max 0 (R * (R / 2 + |y|)))] with k hlt hk
    by_contra hy
    have hy : y < dpl k (w k) := not_le.1 hy
    have hk0 : 0 ≤ k := (le_max_left _ _).trans hk
    have hs : 0 < Real.sqrt (w k) := Real.sqrt_pos.2 (hw k)
    -- `k = √w (√w/2 − d₊) < √w (R/2 + |y|)` would contradict `k ≥ R (R/2 + |y|)` were `√w ≤ R`
    have hRs : R < Real.sqrt (w k) := by
      by_contra hle
      have hk1 : k = Real.sqrt (w k) * (Real.sqrt (w k) / 2 - dpl k (w k)) := by
        rw [dpl_eq]; field_simp; ring
      have : Real.sqrt (w k) * (Real.sqrt (w k) / 2 - dpl k (w k)) < R * (R / 2 + |y|) :=
        (mul_lt_mul_of_pos_left (by linarith [neg_abs_le y]) hs).trans_le
          (mul_le_mul_of_nonneg_right (not_lt.1 hle) (by positivity))
      linarith [(le_max_right _ _).trans hk]
    have hd : 2 / δ ≤ -dmi k (w k) := by
      have : 0 ≤ k / Real.sqrt (w k) := div_nonneg hk0 hs.le
      rw [dmi_eq, neg_sub', neg_div]
      linarith [show R / 2 = 2 / δ by ring]
    have h6 : 2 / δ * (Real.exp k * Phi (dmi k (w k))) ≤ 1 :=
      (mul_le_mul_of_nonneg_right hd (hE k)).trans (hmills k)
    rw [div_mul_eq_mul_div, div_le_iff₀ hδ] at h6
    have h4 : δ ≤ Phi (dpl k (w k)) := strictMono_Phi.monotone (by linarith [neg_abs_le y])
    have h5 : blackForm k (w k) = Phi (dpl k (w k)) - Real.exp k * Phi (dmi k (w k)) := rfl
    linarith
  · have hneg : Tendsto (fun k ↦ -dmi k (w k)) atTop atTop := by
      refine tendsto_atTop_mono (fun k ↦ ?_) (tendsto_neg_atBot_atTop.comp h)
      have : dmi k (w k) = dpl k (w k) - Real.sqrt (w k) := by rw [dmi_eq, dpl_eq]; ring
      simp only [Function.comp_apply, this]
      linarith [Real.sqrt_nonneg (w k)]
    have hE0 : Tendsto (fun k ↦ Real.exp k * Phi (dmi k (w k))) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (tendsto_inv_atTop_zero.comp hneg) (Eventually.of_forall hE) ?_
      filter_upwards [hneg.eventually_gt_atTop 0] with k hk
      rw [Function.comp_apply, ← one_div, le_div_iff₀ hk]
      linarith [hmills k]
    simpa [blackForm] using (tendsto_Phi_atBot.comp h).sub hE0

end MathFin
