/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib

/-!
# Discrete Debit Valuation Adjustment (DVA)

DVA is CVA's mirror: it prices the bank's *own* default risk against the counterparty's exposure
to the bank, i.e. against the bank's *negative* exposure (what the bank owes, from the
counterparty's point of view). Over a discrete tenor `t₀ < t₁ < ⋯ < tₙ`, with the bank's own
survival probability `Q_B`, loss given the bank's own default `1 - R_B`, and expected discounted
negative exposure `EDNE(tᵢ)`:

  `DVA = (1 - R_B) · ∑ᵢ EDNE(tᵢ) · [Q_B(tᵢ₋₁) - Q_B(tᵢ)]`.

This is the standard discrete CVA/DVA sum-over-default-buckets form (Gregory, *The xVA
Challenge*): `Q_B(tᵢ₋₁) - Q_B(tᵢ)` is the probability the bank defaults in bucket `i`, so the sum
is exactly the loss-given-own-default weighted by the (discrete) probability of owing money to the
counterparty in that bucket.

## Main definitions and results

* `discreteDVA`: the DVA sum, indexed `i = 1, …, n` via `Fin n` buckets against a survival curve
  `Q : Fin (n+1) → ℝ` (so bucket `i : Fin n` spans `[t i.castSucc, t i.succ]`).
* `discreteDVA_nonneg`: DVA is nonnegative when the survival curve is non-increasing, exposure is
  nonnegative, and `R_B ≤ 1`.
* `discreteDVA_scale_lgd`: DVA scales linearly in `1 - R_B`.
* `discreteDVA_zero_exposure`: DVA vanishes when the negative-exposure profile is identically
  zero (no amount is ever owed to the counterparty).
-/

@[expose] public section

namespace MathFin

variable {n : ℕ} (RB : ℝ) (Q : Fin (n + 1) → ℝ) (EDNE : Fin n → ℝ)

/-- **Discrete DVA**: `DVA = (1 - R_B) · ∑ᵢ EDNE(tᵢ) · [Q(tᵢ₋₁) - Q(tᵢ)]`, summed over the `n`
default buckets of the survival curve `Q : Fin (n+1) → ℝ` (bucket `i` runs from `Q i.castSucc` to
`Q i.succ`). -/
noncomputable def discreteDVA (RB : ℝ) (Q : Fin (n + 1) → ℝ) (EDNE : Fin n → ℝ) : ℝ :=
  (1 - RB) * ∑ i : Fin n, EDNE i * (Q i.castSucc - Q i.succ)

/-- **DVA is nonnegative** when the survival curve is non-increasing (`Q` a genuine survival
probability curve), exposure is nonnegative, and the recovery rate is at most `1`. -/
theorem discreteDVA_nonneg (hR : RB ≤ 1) (hQ : Antitone Q) (hE : ∀ i, 0 ≤ EDNE i) :
    0 ≤ discreteDVA RB Q EDNE := by
  unfold discreteDVA
  apply mul_nonneg (by linarith)
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hE i) (by linarith [hQ i.castSucc_le_succ])

/-- **DVA scales linearly in loss-given-own-default `1 - R_B`.** -/
theorem discreteDVA_scale_lgd (c : ℝ) :
    discreteDVA (1 - c * (1 - RB)) Q EDNE = c * discreteDVA RB Q EDNE := by
  unfold discreteDVA
  ring_nf

/-- **DVA vanishes with zero exposure**: if the counterparty is never owed anything
(`EDNE ≡ 0`), DVA is `0`. -/
theorem discreteDVA_zero_exposure (RB : ℝ) (Q : Fin (n + 1) → ℝ) :
    discreteDVA RB Q (fun _ ↦ 0) = 0 := by
  unfold discreteDVA
  simp

end MathFin
