/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.StationaryPutCap

/-! # A strictly positive exercise threshold for the actual stopping value

A constructed stationary supersolution bounds the actual price. At low stock
prices it equals the payoff, forcing exercise and a positive threshold. No
smooth fit or free-boundary regularity is assumed.

## Result

Public entry points include `canonicalPrice_le_stationaryPutCap`,
`canonicalPrice_contact_below_stationary_join`, `canonicalStockBoundary_uniform_pos`,
`canonicalStockBoundary_pos`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter Boundary
open scoped Topology ContDiff

theorem canonicalPrice_le_stationaryPutCap {k h m d : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (hm : 0 < m) (hd0 : d < 0)
    (hd : Real.exp d = m / (1 + m)) (hmQ : 0 ≤ k + (k - h - 1) * m - m^2)
    (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    canonicalPrice k h x t ≤ stationaryPutCap m d x := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨R₀,hR₀⟩ := eventually_atTop.mp (canonicalPrice_decay_uniform (h := h) hk.le t hε)
  let R := max x R₀
  let L := min x (min d (Real.log ε))
  have hLx : L ≤ x := min_le_left _ _
  have hLd : L ≤ d := (min_le_right _ _).trans (min_le_left _ _)
  have hLε : Real.exp L ≤ ε := by
    calc
      Real.exp L ≤ Real.exp (Real.log ε) := Real.exp_le_exp.mpr
        ((min_le_right _ _).trans (min_le_right _ _))
      _ = ε := Real.exp_log hε
  have hcap := stationaryPutCap_ge_payoff hm hd0 hd
  have hnonneg := stationaryPutCap_nonneg hm hd0 hd
  have hbound := canonicalPrice_le_of_upper_supports hk
    (U := fun z => stationaryPutCap m d z.1+ε) (L := L) (R := R) (T := t)
    (((stationaryPutCap_continuous m d).comp continuous_fst).add continuous_const).continuousOn
    (fun z _ => (hcap z.1).trans (le_add_of_nonneg_right hε.le))
    (fun z _ => stationaryPutCap_upper_support hk.le hh hhk hm hd0 hd hmQ hε.le z)
    (fun y _ => by
      rw [canonicalPrice_initial hk.le]
      exact (hcap y).trans (le_add_of_nonneg_right hε.le))
    (fun s _ => by
      dsimp only
      rw [stationaryPutCap,if_pos hLd]
      linarith [(canonicalPrice_bounds (h := h) hk.le L s).2])
    (fun s hs => by
      have hv := (hR₀ R (le_max_right _ _) s hs.2).2
      dsimp only
      linarith [hnonneg R])
  exact hbound (x,t) ⟨⟨hLx,le_max_left _ _⟩,ht,le_rfl⟩

theorem canonicalPrice_contact_below_stationary_join {k h m d : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (hm : 0 < m) (hd0 : d < 0)
    (hd : Real.exp d = m / (1 + m)) (hmQ : 0 ≤ k + (k - h - 1) * m - m^2)
    {x t : ℝ} (hx : x ≤ d) (ht : 0 ≤ t) : canonicalPrice k h x t = putPayoff x := by
  apply le_antisymm _ (canonicalPrice_bounds hk.le x t).1
  have hu := canonicalPrice_le_stationaryPutCap hk hh hhk hm hd0 hd hmQ x ht
  simpa only [stationaryPutCap,if_pos hx,putPayoff,
    max_eq_left (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (hx.trans hd0.le)))] using hu

/-- The positive lower bound is uniform over all nonnegative maturities. -/
theorem canonicalStockBoundary_uniform_pos {k h : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, 0 ≤ t → A ≤ canonicalStockBoundary k h t := by
  obtain ⟨m,d,hm,hd0,hd,hmQ⟩ := exists_stationaryPutCap_parameters (h := h) hk
  refine ⟨Real.exp d,Real.exp_pos d,?_⟩
  intro t ht
  rcases ht.eq_or_lt with he | ht
  · rw [← he,canonicalStockBoundary_initial hk.le]
    exact Real.exp_le_one_iff.mpr hd0.le
  · exact (canonicalPrice_contact_iff hk.le d ht).mp
      (canonicalPrice_contact_below_stationary_join hk hh hhk hm hd0 hd hmQ le_rfl ht.le)

theorem canonicalStockBoundary_pos {k h t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (ht : 0 ≤ t) : 0 < canonicalStockBoundary k h t := by
  obtain ⟨A,hA,hbound⟩ := canonicalStockBoundary_uniform_pos hk hh hhk
  exact hA.trans_le (hbound t ht)

theorem zeroDividend_canonicalStockBoundary_pos {k t : ℝ} (hk : 0 < k)
    (ht : 0 ≤ t) : 0 < canonicalStockBoundary k 0 t :=
  canonicalStockBoundary_pos hk le_rfl hk.le ht

/-- The logarithmic boundary now has a proved positive argument. -/
noncomputable def canonicalLogBoundary (k h t : ℝ) : ℝ :=
  Real.log (canonicalStockBoundary k h t)

theorem exp_canonicalLogBoundary {k h t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (ht : 0 ≤ t) :
    Real.exp (canonicalLogBoundary k h t) = canonicalStockBoundary k h t :=
  Real.exp_log (canonicalStockBoundary_pos hk hh hhk ht)

theorem canonicalLogBoundary_initial {k h : ℝ} (hk : 0 < k) :
    canonicalLogBoundary k h 0 = 0 := by
  simp only [canonicalLogBoundary,canonicalStockBoundary_initial hk.le,Real.log_one]

theorem canonicalLogBoundary_neg {k h t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (ht : 0 < t) : canonicalLogBoundary k h t < 0 :=
  Real.log_neg (canonicalStockBoundary_pos hk hh hhk ht.le) (canonicalStockBoundary_lt_one hk.le ht)

theorem canonicalPrice_contact_iff_logBoundary {k h x t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (ht : 0 < t) :
    canonicalPrice k h x t = putPayoff x ↔ x ≤ canonicalLogBoundary k h t := by
  rw [canonicalPrice_contact_iff hk.le x ht,← exp_canonicalLogBoundary hk hh hhk ht.le,
    Real.exp_le_exp]

theorem canonicalPrice_value_matching {k h t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (ht : 0 < t) :
    canonicalPrice k h (canonicalLogBoundary k h t) t =
      1-Real.exp (canonicalLogBoundary k h t) := by
  have he := (canonicalPrice_contact_iff_logBoundary hk hh hhk ht).mpr
    (le_rfl : canonicalLogBoundary k h t ≤ canonicalLogBoundary k h t)
  simpa only [putPayoff,max_eq_left (sub_nonneg.mpr
    (Real.exp_le_one_iff.mpr (canonicalLogBoundary_neg hk hh hhk ht).le))] using he

theorem canonicalContinuationRegion_eq_logBoundary {k h : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) :
    canonicalContinuationRegion k h = {z | 0 < z.2 ∧ canonicalLogBoundary k h z.2 < z.1} := by
  rw [canonicalContinuationRegion_eq hk.le]
  ext z
  apply and_congr_right
  intro ht
  rw [← exp_canonicalLogBoundary hk hh hhk ht.le,Real.exp_lt_exp]

end MathFin.BlackScholes.AmericanPut.Stopping
