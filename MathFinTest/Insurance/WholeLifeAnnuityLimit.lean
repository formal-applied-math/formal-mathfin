/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/

import MathFin

/-!
# Whole-life annuity limit checks

Specializations and negation checks for `MathFin.wholeLife_add_endowment_eq_annuityDue`
(the finite term-plus-endowment identity converges to the whole-life `A = 1 - d * ä`):

* geometric survival (`S k = q ^ k`, `v * q < 1`): the death sum is
  `v * (1 - q) / (1 - v * q)`, both by direct tsum computation and via the endpoint.
* `v = 1` with geometric survival: the death sum equals `1`.
* immortal (`S ≡ 1`) at `v = 1`: the annuity series is not summable and the tail does not
  vanish, so the summability hypotheses cannot be dropped.
-/

open Filter Topology

-- Geometric survival, direct tsum computation.
theorem geometric_death_tsum_direct (v q : ℝ) (hv : 0 < v) (hq0 : 0 ≤ q)
    (h : v * q < 1) :
    ∑' k, v ^ (k + 1) * (q ^ k - q ^ (k + 1)) = v * (1 - q) / (1 - v * q) := by
  have h0 : (0 : ℝ) ≤ v * q := mul_nonneg hv.le hq0
  have hpoint : ∀ k : ℕ, v ^ (k + 1) * (q ^ k - q ^ (k + 1))
      = (v * (1 - q)) * (v * q) ^ k := by
    intro k
    rw [mul_pow, pow_succ', pow_succ']
    ring
  have hfeq : (fun k : ℕ => v ^ (k + 1) * (q ^ k - q ^ (k + 1)))
      = (fun k => (v * (1 - q)) * (v * q) ^ k) := funext hpoint
  rw [hfeq, tsum_mul_left, tsum_geometric_of_lt_one h0 h, div_eq_mul_inv]

-- Geometric survival via the whole-life endpoint.
theorem geometric_death_tsum_via_wholeLife (v q : ℝ) (hv : 0 < v) (hq0 : 0 ≤ q)
    (h : v * q < 1) :
    ∑' k, v ^ (k + 1) * (q ^ k - q ^ (k + 1)) = v * (1 - q) / (1 - v * q) := by
  have h0 : (0 : ℝ) ≤ v * q := mul_nonneg hv.le hq0
  have hgeom : Summable (fun k : ℕ => (v * q) ^ k) :=
    summable_geometric_of_lt_one h0 h
  have hpoint : ∀ k : ℕ, v ^ (k + 1) * (q ^ k - q ^ (k + 1))
      = (v * (1 - q)) * (v * q) ^ k := by
    intro k
    rw [mul_pow, pow_succ', pow_succ']
    ring
  have hdeath : Summable (fun k => v ^ (k + 1) * (q ^ k - q ^ (k + 1))) := by
    have hfeq : (fun k : ℕ => v ^ (k + 1) * (q ^ k - q ^ (k + 1)))
        = (fun k => (v * (1 - q)) * (v * q) ^ k) := funext hpoint
    rw [hfeq]
    exact hgeom.mul_left (v * (1 - q))
  have hann : Summable (fun k => v ^ k * q ^ k) := by
    have hfeq : (fun k : ℕ => v ^ k * q ^ k) = (fun k => (v * q) ^ k) :=
      funext (fun k => (mul_pow v q k).symm)
    rw [hfeq]
    exact hgeom
  have htail : Tendsto (fun n : ℕ => v ^ n * q ^ n) atTop (𝓝 0) := by
    have hfeq : (fun n : ℕ => v ^ n * q ^ n) = (fun n => (v * q) ^ n) :=
      funext (fun n => (mul_pow v q n).symm)
    rw [hfeq]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one h0 h
  have hann_val : ∑' k, v ^ k * q ^ k = (1 - v * q)⁻¹ := by
    have hfeq : (fun k : ℕ => v ^ k * q ^ k) = (fun k => (v * q) ^ k) :=
      funext (fun k => (mul_pow v q k).symm)
    rw [hfeq, tsum_geometric_of_lt_one h0 h]
  have hW := MathFin.wholeLife_add_endowment_eq_annuityDue (fun k => q ^ k) (by simp) v hv
    hdeath hann htail
  have h2 : ∑' k, v ^ (k + 1) * (q ^ k - q ^ (k + 1))
      = 1 - (1 - v) * ∑' k, v ^ k * q ^ k := hW
  have hne : (1 : ℝ) - v * q ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt h))
  rw [hann_val] at h2
  rw [h2]
  field_simp
  ring

-- v = 1 with geometric survival: the death sum equals 1.
theorem unitDiscount_geometric_death_eq_one (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑' k, (1 : ℝ) ^ (k + 1) * (q ^ k - q ^ (k + 1)) = 1 := by
  have hgeom : Summable (fun k : ℕ => q ^ k) := summable_geometric_of_lt_one hq0 hq1
  have hdeath : Summable (fun k => (1 : ℝ) ^ (k + 1) * (q ^ k - q ^ (k + 1))) := by
    have hpoint : ∀ k : ℕ, (1 : ℝ) ^ (k + 1) * (q ^ k - q ^ (k + 1))
        = (1 - q) * q ^ k := by
      intro k
      rw [one_pow, one_mul, pow_succ']
      ring
    have hfeq : (fun k : ℕ => (1 : ℝ) ^ (k + 1) * (q ^ k - q ^ (k + 1)))
        = (fun k => (1 - q) * q ^ k) := funext hpoint
    rw [hfeq]
    exact hgeom.mul_left (1 - q)
  have hann : Summable (fun k => (1 : ℝ) ^ k * q ^ k) := by
    have hfeq : (fun k : ℕ => (1 : ℝ) ^ k * q ^ k) = (fun k => q ^ k) :=
      funext (fun k => by simp)
    rw [hfeq]
    exact hgeom
  have htail : Tendsto (fun n : ℕ => (1 : ℝ) ^ n * q ^ n) atTop (𝓝 0) := by
    have hfeq : (fun n : ℕ => (1 : ℝ) ^ n * q ^ n) = (fun n => q ^ n) :=
      funext (fun n => by simp)
    rw [hfeq]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have h := MathFin.wholeLife_add_endowment_eq_annuityDue (fun k => q ^ k) (by simp) 1 one_pos
    hdeath hann htail
  simpa using h

-- Immortal (S ≡ 1) at v = 1: the annuity series is not summable.
theorem immortal_annuity_not_summable : ¬ Summable (fun k : ℕ => (1 : ℝ) ^ k * 1) := by
  intro h
  have heq : (fun k : ℕ => (1 : ℝ) ^ k * 1) = (fun _ : ℕ => (1 : ℝ)) :=
    funext (fun k => by simp)
  rw [heq] at h
  exact Infinite.not_finite (Finite.of_summable_const zero_lt_one h)

-- Immortal (S ≡ 1) at v = 1: the tail does not vanish.
theorem immortal_tail_not_vanishing :
    ¬ Tendsto (fun n : ℕ => (1 : ℝ) ^ n * 1) atTop (𝓝 0) := by
  intro h
  have heq : (fun n : ℕ => (1 : ℝ) ^ n * 1) = (fun _ : ℕ => (1 : ℝ)) :=
    funext (fun n => by simp)
  rw [heq] at h
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h01 := tendsto_nhds_unique h h1
  exact zero_ne_one h01
