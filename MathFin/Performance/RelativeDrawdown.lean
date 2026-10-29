/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Performance.DownsideMetrics

/-!
# Relative drawdown is scale invariant

The **relative drawdown** of an equity curve `E` at time `t` is the fraction of the running
peak lost, `1 − E t / max_{s ≤ t} E s`. The running peak is Mathlib's `partialSups E`.

`MathFin.maximumDrawdown` (`Performance/DownsideMetrics.lean`) measures the largest
*absolute* decline, and is positively homogeneous: scaling the curve by `c > 0` scales it by
`c` (`maximumDrawdown_scale`). The relative drawdown is instead *invariant* under
`E ↦ c E`: a fund ten times the size, run with the same strategy, has the same relative
drawdown at every date. This is why relative drawdown, not absolute drawdown, compares
portfolios of different sizes, or denominated in different currencies at a fixed conversion
rate.

The invariance holds for every equity curve, with no positivity hypothesis on `E`: Lean's
`x / 0 = 0` convention makes both sides `1` at a zero peak.

## Main results

* `partialSups_const_mul₀`: the running peak of `c E` is `c` times the running peak of `E`,
  for `c > 0` (multiplication by `c` is an order isomorphism, so it commutes with `⊔`).
* `relativeDrawdown_const_mul`: the relative drawdown of `c E` equals that of `E`.
* `maxRelativeDrawdown_const_mul`: hence so does the maximum relative drawdown up to any time.
* `sub_le_maximumDrawdown`: every chronological decline `E s − E t` (`s ≤ t`) of a finite path
  is at most `maximumDrawdown E`.
* `partialSups_mul_relativeDrawdown_le_maximumDrawdown`: on a finite path the two notions are
  tied: the relative drawdown at `t`, scaled back up by a nonzero running peak, is the
  absolute decline `max_{s ≤ t} E s − E t`, which is at most `maximumDrawdown E`.
-/

@[expose] public section

namespace MathFin

variable {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]

/-- Relative drawdown `1 − E t / max_{s ≤ t} E s` of an equity curve `E` at time `t`: the
fraction of the running peak lost by time `t`. -/
noncomputable def relativeDrawdown (E : ι → ℝ) (t : ι) : ℝ := 1 - E t / partialSups E t

/-- Maximum relative drawdown up to time `t`: the largest relative drawdown at any `s ≤ t`. -/
noncomputable def maxRelativeDrawdown (E : ι → ℝ) (t : ι) : ℝ :=
  partialSups (relativeDrawdown E) t

/-- The running peak is positively homogeneous: multiplication by `c > 0` is an order
isomorphism, so it commutes with the finite suprema defining `partialSups`. This is the
group-with-zero version of Mathlib's `[Group α]` lemma `partialSups_const_mul`. -/
theorem partialSups_const_mul₀ {G₀ : Type*} [GroupWithZero G₀] [SemilatticeSup G₀]
    [PosMulReflectLT G₀] {c : G₀} (hc : 0 < c) (E : ι → G₀) (t : ι) :
    partialSups (fun s ↦ c * E s) t = c * partialSups E t :=
  map_partialSups (OrderIso.mulLeft₀ c hc) E t

/-- **Relative drawdown is scale invariant**: scaling the equity curve by `c > 0` leaves the
relative drawdown unchanged at every time — unlike the absolute `maximumDrawdown`, which
scales by `c`. -/
theorem relativeDrawdown_const_mul {c : ℝ} (hc : 0 < c) (E : ι → ℝ) :
    relativeDrawdown (fun s ↦ c * E s) = relativeDrawdown E := by
  funext t
  simp only [relativeDrawdown, partialSups_const_mul₀ hc, mul_div_mul_left _ _ hc.ne']

/-- The maximum relative drawdown up to any time is scale invariant. -/
theorem maxRelativeDrawdown_const_mul {c : ℝ} (hc : 0 < c) (E : ι → ℝ) :
    maxRelativeDrawdown (fun s ↦ c * E s) = maxRelativeDrawdown E := by
  unfold maxRelativeDrawdown
  rw [relativeDrawdown_const_mul hc]

private theorem le_listMaximum {x : ℝ} : ∀ {xs : List ℝ}, x ∈ xs → x ≤ listMaximum xs
  | _ :: _, .head _ => le_max_left _ _
  | _ :: _, .tail _ h => (le_listMaximum h).trans (le_max_right _ _)

/-- Every chronological peak-to-trough decline `E s − E t` (`s ≤ t`) of a finite path is at
most its `maximumDrawdown`. -/
theorem sub_le_maximumDrawdown {n : ℕ} (E : Fin n → ℝ) {s t : Fin n} (hst : s ≤ t) :
    E s - E t ≤ maximumDrawdown E :=
  le_listMaximum <| List.mem_map.2 ⟨(s, t), by simp, if_pos hst⟩

/-- **Relative drawdown, rescaled by the running peak, is bounded by the absolute maximum
drawdown**: for a nonzero running peak, `(max_{s ≤ t} E s) · relativeDrawdown E t` is the
absolute decline `max_{s ≤ t} E s − E t`, which `maximumDrawdown E` dominates. At a zero running
peak the left side is `0`, and `maximumDrawdown` is nonnegative. -/
theorem partialSups_mul_relativeDrawdown_le_maximumDrawdown {n : ℕ} (E : Fin n → ℝ)
    (t : Fin n) : partialSups E t * relativeDrawdown E t ≤ maximumDrawdown E := by
  rcases eq_or_ne (partialSups E t) 0 with h | h
  · simpa [h] using maximumDrawdown_nonneg E
  rw [relativeDrawdown, mul_sub, mul_one, mul_div_cancel₀ _ h, sub_le_iff_le_add]
  exact partialSups_le _ _ _ fun s hs ↦ sub_le_iff_le_add.1 (sub_le_maximumDrawdown E hs)

end MathFin
