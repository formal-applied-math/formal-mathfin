/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Mathlib

/-!
# Upward crossings and interval-shaped sublevel sets

A differentiable real function whose derivative is positive at every zero
cannot cross from nonnegative to negative as its argument increases. We prove
this with Mathlib's scalar fencing theorem. If `R'=R*J` and `R>0`, the resulting
sign restriction makes every strict sublevel set of `R` an interval.

## Result

Public entry points include `nonneg_right_of_upward_zeros`, `nonpos_left_of_upward_zeros`,
`upward_zero_unique`, `value_le_right_of_nonneg_factor`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

/-- Once nonnegative, a function with strictly upward zero crossings stays so. -/
theorem nonneg_right_of_upward_zeros {J : ℝ → ℝ} (hJ : Differentiable ℝ J)
    (hcross : ∀ x, J x = 0 → 0 < deriv J x)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ J a) : 0 ≤ J b := by
  have h : -J b ≤ 0 := image_le_of_deriv_right_lt_deriv_boundary
    hJ.continuous.neg.continuousOn
    (fun x _ => (hJ.differentiableAt.hasDerivAt.neg).hasDerivWithinAt)
    (show -J a ≤ (0 : ℝ) by linarith)
    (fun x => hasDerivAt_const x (0 : ℝ)) (by
      intro x _ hx
      have hx0 : J x = 0 := by change -J x = 0 at hx; linarith
      exact neg_neg_of_pos (hcross x hx0)) ⟨hab, le_rfl⟩
  linarith

/-- The corresponding backward invariant for the nonpositive half-line. -/
theorem nonpos_left_of_upward_zeros {J : ℝ → ℝ} (hJ : Differentiable ℝ J)
    (hcross : ∀ x, J x = 0 → 0 < deriv J x)
    {a b : ℝ} (hab : a ≤ b) (hb : J b ≤ 0) : J a ≤ 0 := by
  let K : ℝ → ℝ := fun x => -J (-x)
  have hdK (x : ℝ) : HasDerivAt K (deriv J (-x)) x := by
    convert! ((hJ.differentiableAt.hasDerivAt).comp x (hasDerivAt_id x).neg).neg using 1
    simp
  have hK : Differentiable ℝ K := fun x => (hdK x).differentiableAt
  have hKcross : ∀ x, K x = 0 → 0 < deriv K x := by
    intro x hx
    rw [(hdK x).deriv]
    exact hcross (-x) (by dsimp [K] at hx; linarith)
  have h := nonneg_right_of_upward_zeros hK hKcross
    (show -b ≤ -a by linarith) (show 0 ≤ K (-b) by simpa [K] using hb)
  simpa [K] using h

/-- Strictly upward zero crossings allow at most one zero. -/
theorem upward_zero_unique {J : ℝ → ℝ} (hJ : Differentiable ℝ J)
    (hcross : ∀ x, J x = 0 → 0 < deriv J x)
    {a b : ℝ} (ha : J a = 0) (hb : J b = 0) : a = b := by
  suffices hn : ∀ a b : ℝ, a < b → J a = 0 → J b = 0 → False by
    rcases lt_trichotomy a b with h | h | h
    · exact (hn a b h ha hb).elim
    · exact h
    · exact (hn b a h hb ha).elim
  intro a b hab ha hb
  let m := (a + b) / 2
  have ham : a < m := by dsimp [m]; linarith
  have hmb : m < b := by dsimp [m]; linarith
  have hconst : ∀ x ∈ Set.Icc a b, J x = 0 := by
    intro x hx
    exact le_antisymm
      (nonpos_left_of_upward_zeros hJ hcross hx.2 (le_of_eq hb))
      (nonneg_right_of_upward_zeros hJ hcross hx.1 (le_of_eq ha.symm))
  have heq : J =ᶠ[nhds m] (fun _ => (0 : ℝ)) := by
    filter_upwards [Ioo_mem_nhds ham hmb] with x hx
    exact hconst x ⟨hx.1.le, hx.2.le⟩
  have hd : deriv J m = 0 := by simpa using heq.deriv_eq
  have hp := hcross m (hconst m ⟨ham.le, hmb.le⟩)
  linarith

section PositiveFactor

variable {R J : ℝ → ℝ}
variable (hR : Differentiable ℝ R) (hJ : Differentiable ℝ J)
variable (hRpos : ∀ x, 0 < R x)
variable (hfactor : ∀ x, deriv R x = R x * J x)
variable (hcross : ∀ x, J x = 0 → 0 < deriv J x)

include hR hJ hRpos hfactor hcross

theorem value_le_right_of_nonneg_factor {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ J a) :
    R a ≤ R b := by
  have hmono : MonotoneOn R (Set.Icc a b) := monotoneOn_of_deriv_nonneg
    (convex_Icc a b) hR.continuous.continuousOn hR.differentiableOn (by
      intro x hx
      have hx' : x ∈ Set.Icc a b := interior_subset hx
      rw [hfactor]
      exact mul_nonneg (hRpos x).le (nonneg_right_of_upward_zeros hJ hcross hx'.1 ha))
  exact hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

theorem value_le_left_of_nonpos_factor {a b : ℝ} (hab : a ≤ b) (hb : J b ≤ 0) :
    R b ≤ R a := by
  have hanti : AntitoneOn R (Set.Icc a b) := antitoneOn_of_deriv_nonpos
    (convex_Icc a b) hR.continuous.continuousOn hR.differentiableOn (by
      intro x hx
      have hx' : x ∈ Set.Icc a b := interior_subset hx
      rw [hfactor]
      exact mul_nonpos_of_nonneg_of_nonpos (hRpos x).le
        (nonpos_left_of_upward_zeros hJ hcross hx'.2 hb))
  exact hanti ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

/-- The function cannot form a hill between two lower values. -/
theorem value_between_le_max_of_upward_factor {x y z : ℝ}
    (hxy : x ≤ y) (hyz : y ≤ z) : R y ≤ max (R x) (R z) := by
  by_cases hy : 0 ≤ J y
  · exact (value_le_right_of_nonneg_factor hR hJ hRpos hfactor hcross hyz hy).trans
      (le_max_right _ _)
  · exact (value_le_left_of_nonpos_factor hR hJ hRpos hfactor hcross hxy
      (le_of_not_ge hy)).trans (le_max_left _ _)

theorem sublevel_ordConnected_of_upward_factor (L : ℝ) :
    Set.OrdConnected {x | R x < L} := by
  rw [Set.ordConnected_iff]
  intro x hx z hz _ y hy
  exact (value_between_le_max_of_upward_factor hR hJ hRpos hfactor hcross
    hy.1 hy.2).trans_lt (max_lt hx hz)

/-- Every stationary point is a GLOBAL minimum, without assuming it exists. -/
theorem global_min_of_upward_factor {z : ℝ} (hz : deriv R z = 0) (x : ℝ) :
    R z ≤ R x := by
  have hzJ : J z = 0 := by
    rw [hfactor] at hz
    exact (mul_eq_zero.mp hz).resolve_left (hRpos z).ne'
  rcases le_total z x with hzx | hxz
  · exact value_le_right_of_nonneg_factor hR hJ hRpos hfactor hcross hzx (le_of_eq hzJ.symm)
  · exact value_le_left_of_nonpos_factor hR hJ hRpos hfactor hcross hxz (le_of_eq hzJ)

/-- A level with a value below it cannot contain a stationary point. -/
theorem deriv_ne_zero_of_exists_lower_of_upward_factor {z : ℝ}
    (hlower : ∃ x, R x < R z) : deriv R z ≠ 0 := by
  intro hz
  obtain ⟨x, hx⟩ := hlower
  exact (not_lt_of_ge (global_min_of_upward_factor hR hJ hRpos hfactor hcross hz x)) hx

/-- Three ordered points cannot have the same value. Rolle's theorem would
give two distinct zeros of the upward-crossing slope factor. -/
theorem no_three_equal_values_of_upward_factor {a b c : ℝ}
    (hab : a < b) (hbc : b < c) (heab : R a = R b) (hebc : R b = R c) : False := by
  obtain ⟨u, hu, hud⟩ := exists_deriv_eq_zero hab hR.continuous.continuousOn heab
  obtain ⟨v, hv, hvd⟩ := exists_deriv_eq_zero hbc hR.continuous.continuousOn hebc
  have huJ : J u = 0 := by
    rw [hfactor] at hud
    exact (mul_eq_zero.mp hud).resolve_left (hRpos u).ne'
  have hvJ : J v = 0 := by
    rw [hfactor] at hvd
    exact (mul_eq_zero.mp hvd).resolve_left (hRpos v).ne'
  have he := upward_zero_unique hJ hcross huJ hvJ
  linarith [hu.2, hv.1]

end PositiveFactor

/-- A set of real numbers with no ordered triple is covered by two points.
Unlike a bare `ncard` bound, this also rules out infinite sets. -/
theorem subset_pair_of_no_ordered_triple {s : Set ℝ}
    (h : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a < b → b < c → False) :
    ∃ a b : ℝ, s ⊆ {a, b} := by
  classical
  by_cases hp : ∃ a ∈ s, ∃ b ∈ s, a < b
  · obtain ⟨a, ha, b, hb, hab⟩ := hp
    refine ⟨a, b, ?_⟩
    intro x hx
    rcases lt_trichotomy x a with hxa | hxa | hax
    · exact (h x hx a ha b hb hxa hab).elim
    · simp [hxa]
    · rcases lt_trichotomy x b with hxb | hxb | hbx
      · exact (h a ha x hx b hb hax hxb).elim
      · simp [hxb]
      · exact (h a ha b hb x hx hab hbx).elim
  · by_cases hs : s.Nonempty
    · obtain ⟨a, ha⟩ := hs
      refine ⟨a, a, ?_⟩
      intro x hx
      have he : x = a := by
        rcases lt_trichotomy x a with hxa | he | hax
        · exact (hp ⟨x, hx, a, ha, hxa⟩).elim
        · exact he
        · exact (hp ⟨a, ha, x, hx, hax⟩).elim
      simp [he]
    · exact ⟨0, 0, fun x hx => (hs ⟨x, hx⟩).elim⟩

end MathFin.BlackScholes.AmericanPut.Boundary
