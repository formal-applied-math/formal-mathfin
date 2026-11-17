/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/
import MathFin

/-!
# Finite term insurance identity checks

Specializations and numeric pins for `MathFin.term_add_endowment_eq_annuityDue`
(finite term insurance plus survivor endowment equals `1 - (1 - v) * ä`):

* `v = 1`: term plus endowment equals `1`.
* `n = 0`: term plus endowment equals `1`.
* all survivors (`S ≡ 1`): term plus endowment equals `v ^ n`
  (`allSurvivors_term_add_endowment`, and `1` at `v = 1`).
* integer-date atom (`S 0 = 1`, `S k = 0` otherwise) at `n = 2`: LHS equals `v`.
* nonzero mortality (`S k = (1 / 2) ^ k`, `v = 9 / 10`, `n = 2`): both sides equal
  `171 / 200`, plus the library identity at that instance.
-/

-- v = 1 case: term + endowment = 1
example (S : ℕ → ℝ) (hS0 : S 0 = 1) (n : ℕ) :
    (∑ k ∈ Finset.range n, (1 : ℝ) ^ (k + 1) * (S k - S (k + 1)))
      + (1 : ℝ) ^ n * S n = 1 := by
  have h := MathFin.term_add_endowment_eq_annuityDue S hS0 1 n
  simpa using h

-- n = 0 case: term + endowment = 1
example (S : ℕ → ℝ) (hS0 : S 0 = 1) (v : ℝ) :
    (∑ k ∈ Finset.range 0, v ^ (k + 1) * (S k - S (k + 1)))
      + v ^ 0 * S 0 = 1 := by
  simp [hS0]

-- all survivors: term + endowment = v ^ n
theorem allSurvivors_term_add_endowment (v : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n,
        v ^ (k + 1) * ((fun _ => (1 : ℝ)) k - (fun _ => (1 : ℝ)) (k + 1)))
      + v ^ n * (fun _ => (1 : ℝ)) n = v ^ n := by
  simp

-- all survivors at v = 1: term + endowment = 1
example (n : ℕ) :
    (∑ k ∈ Finset.range n,
        (1 : ℝ) ^ (k + 1) * ((fun _ => (1 : ℝ)) k - (fun _ => (1 : ℝ)) (k + 1)))
      + (1 : ℝ) ^ n * (fun _ => (1 : ℝ)) n = 1 := by
  simp

-- integer-date atom, n = 2: LHS = v
example (v : ℝ) :
    (∑ k ∈ Finset.range 2,
        v ^ (k + 1) * ((fun k => if k = 0 then (1 : ℝ) else 0) k
          - (fun k => if k = 0 then (1 : ℝ) else 0) (k + 1)))
      + v ^ 2 * (fun k => if k = 0 then (1 : ℝ) else 0) 2 = v := by
  simp

-- numeric pin: S k = (1 / 2) ^ k, v = 9 / 10, n = 2; LHS = 171 / 200
example :
    (∑ k ∈ Finset.range 2,
        (9 / 10 : ℝ) ^ (k + 1) * ((fun k => (1 / 2 : ℝ) ^ k) k
          - (fun k => (1 / 2 : ℝ) ^ k) (k + 1)))
      + (9 / 10 : ℝ) ^ 2 * (fun k => (1 / 2 : ℝ) ^ k) 2 = 171 / 200 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  ring

-- numeric pin, right-hand side = 171 / 200
example :
    1 - (1 - (9 / 10 : ℝ)) * ∑ k ∈ Finset.range 2, (9 / 10 : ℝ) ^ k * (1 / 2 : ℝ) ^ k
      = 171 / 200 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  ring

-- numeric pin consistency: the library identity at the pinned instance
example :
    (∑ k ∈ Finset.range 2,
        (9 / 10 : ℝ) ^ (k + 1) * ((1 / 2 : ℝ) ^ k - (1 / 2 : ℝ) ^ (k + 1)))
      + (9 / 10 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ 2
      = 1 - (1 - (9 / 10 : ℝ)) * ∑ k ∈ Finset.range 2, (9 / 10 : ℝ) ^ k * (1 / 2 : ℝ) ^ k :=
  MathFin.term_add_endowment_eq_annuityDue _ (by simp) _ _
