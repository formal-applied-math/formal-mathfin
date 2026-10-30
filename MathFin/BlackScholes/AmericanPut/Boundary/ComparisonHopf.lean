/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.ParabolicHopf
public import MathFin.BlackScholes.AmericanPut.Boundary.MovingLine
public import MathFin.BlackScholes.AmericanPut.Boundary.ComparisonMaximum
public import MathFin.BlackScholes.AmericanPut.Boundary.ComparisonCoefficients

/-!
# The terminal barrier applied to the actual comparison

The moving-coordinate PDE and one-sided zero derivative at contact are derived
from the pricing contract. A positive backward rectangle is then impossible.
The rectangle is constructed in `Tangency` using the interval invariant,
which is proved in `ComparisonUnimodality`; neither is a pricing-contract field.

## Result

Public entry points include `lineDifference`, `lineDifference_continuousOn`,
`lineDifference_contDiffAt`, `lineDifference_equation`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary.Comparison

open Set Filter
open scoped Topology ContDiff

/-- `straightDifference` in line-relative coordinates:
`lineDifference p k h c d y t = straightDifference p k h c d (y + (d - c * t)) t`. -/
noncomputable def lineDifference (p : ℝ → ℝ → ℝ) (k h c d : ℝ) : ℝ → ℝ → ℝ :=
  movingLineTransform (straightDifference p k h c d) c d

variable {k h c d : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}

theorem lineDifference_continuousOn (hp : ContinuousBoundaryPutSolution k h p b) :
    ContinuousOn (fun z : ℝ × ℝ => lineDifference p k h c d z.1 z.2) {z | 0 ≤ z.2} := by
  exact (normalizedDifference_continuousOn (d := d) hp
    (profile_data hp.rate_pos.le) (profile_data hp.dividend_nonneg)).comp
      (show ContinuousOn (fun z : ℝ × ℝ => (z.1 + (d - c * z.2),z.2)) {z | 0 ≤ z.2} by fun_prop)
      (fun _ hz => hz)

theorem lineDifference_contDiffAt (hp : ContinuousBoundaryPutSolution k h p b) {y t : ℝ}
    (ht : 0 < t) (hx : b t < y + (d - c * t)) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => lineDifference p k h c d z.1 z.2) (y,t) := by
  exact (normalizedDifference_contDiffAt hp (profile_data hp.rate_pos.le)
    (profile_data hp.dividend_nonneg) ht hx).comp (y,t)
      (show ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => (z.1 + (d - c * z.2),z.2)) (y,t) by fun_prop)

theorem lineDifference_equation (hp : ContinuousBoundaryPutSolution k h p b) {y t : ℝ}
    (ht : 0 < t) (hx : b t < y + (d - c * t)) :
    deriv (lineDifference p k h c d y) t =
      deriv (deriv (fun z => lineDifference p k h c d z t)) y +
        (k - h - 1 - c + 2 * logSlope (profile (k - h - 1 - c) k) y) *
          deriv (fun z => lineDifference p k h c d z t) y := by
  have hs := normalizedDifference_contDiffAt (c := c) (d := d) hp (profile_data hp.rate_pos.le)
    (profile_data hp.dividend_nonneg) ht hx
  have he := movingLineTransform_equation (V := straightDifference p k h c d) (c := c) (d := d)
    (D := fun x s => k - h - 1 + 2 * deriv (profile (k - h - 1 - c) k) (x + c * s - d) /
      profile (k - h - 1 - c) k (x + c * s - d))
    (hs.differentiableAt (by simp))
    (normalizedDifference_equation (c := c) (d := d) hp (profile_data hp.rate_pos.le)
      (profile_data hp.dividend_nonneg) ht hx)
  have hz : y + (d - c * t) + c * t - d = y := by ring
  rw [hz] at he
  convert! he using 1
  dsimp [lineDifference, logSlope]
  ring

/-- Value matching and RIGHT smooth fit of the actual difference at a line
contact. No spatial derivative of the price across its boundary is required. -/
theorem lineDifference_fit (hp : ContinuousBoundaryPutSolution k h p b) {T : ℝ} (hT : 0 < T)
    (hcontact : b T = d - c * T) :
    lineDifference p k h c d 0 T = 0 ∧
      HasDerivWithinAt (fun y => lineDifference p k h c d y T) 0 (Ici 0) 0 := by
  let f := profile (k - h - 1 - c) k
  have hf : ProfileData (k - h - 1 - c) k f := profile_data hp.rate_pos.le
  obtain ⟨hq,hqd⟩ := straightPrice_fit hp.rate_pos hp.dividend_nonneg c d T
  rw [← hcontact] at hq hqd
  have hn : p (b T) T - straightPrice k h c d (b T) T = 0 := by
    rw [hp.exercise (b T) T hT le_rfl, hq, sub_self]
  have hv : straightDifference p k h c d (b T) T = 0 := by
    change (p (b T) T - straightPrice k h c d (b T) T) / f (b T + c * T - d) = 0
    rw [hn, zero_div]
  have hnum := (hp.smooth_fit T hT).sub hqd.hasDerivWithinAt
  have hden := (shiftedProfile_hasDeriv_x (d := d) hf (b T) T).hasDerivWithinAt (s := Ici (b T))
  have hquot : HasDerivWithinAt (fun x => straightDifference p k h c d x T) 0
      (Ici (b T)) (b T) := by
    convert! hnum.div hden (hf.pos _).ne' using 1
    simp only [Pi.sub_apply, sub_self, zero_mul, hn, zero_div]
  refine ⟨?_, ?_⟩
  · simpa only [lineDifference, movingLineTransform, zero_add, ← hcontact] using hv
  · convert! hquot.comp_of_eq 0 (((hasDerivAt_id 0).add_const (d - c * T)).hasDerivWithinAt)
      (show MapsTo (fun y : ℝ => y + (d - c * T)) (Ici 0) (Ici (b T)) by
        intro y hy; change 0 ≤ y at hy
        change b T ≤ y + (d - c * T); rw [hcontact]; linarith)
      (by simp [hcontact]) using 1
    simp only [zero_mul]

/-- The comparison equals the intrinsic expression on its own line, whereas
the American value dominates that expression. This needs no line/boundary
ordering and supplies the left edge of the Hopf rectangle automatically. -/
theorem lineDifference_on_line_nonneg (hp : ContinuousBoundaryPutSolution k h p b) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ lineDifference p k h c d 0 t := by
  have hq := (straightPrice_fit hp.rate_pos hp.dividend_nonneg c d t).1
  have hpbound : 1 - Real.exp (d - c * t) ≤ p (d - c * t) t :=
    (le_max_left _ _).trans (hp.dominates (d - c * t) t ht)
  change 0 ≤ (p (0 + (d - c * t)) t - straightPrice k h c d (0 + (d - c * t)) t) /
    profile (k - h - 1 - c) k (0 + (d - c * t) + c * t - d)
  rw [zero_add, hq]
  exact div_nonneg (sub_nonneg.mpr hpbound) ((profile_data hp.rate_pos.le).pos _).le

/-- The precise terminal rectangle needed by Step 5 is incompatible with
contact and smooth fit. The comparison PDE, drift bound, left-edge sign, and
zero right derivative are derived here, not assumed. The remaining task is to
construct such a rectangle from a concave tangency and the interval invariant. -/
theorem lineDifference_no_positive_rectangle (hp : ContinuousBoundaryPutSolution k h p b)
    {L a T : ℝ} (hL : 0 < L) (ha : 0 < a) (haT : a ≤ T)
    (hline : ∀ t ∈ Icc a T, b t ≤ d - c * t)
    (hcontact : b T = d - c * T)
    (hbottom : ∀ y ∈ Icc 0 L, 0 < lineDifference p k h c d y a)
    (hright : ∀ t ∈ Icc a T, 0 < lineDifference p k h c d L t) : False := by
  let u := lineDifference p k h c d
  let D : ℝ → ℝ → ℝ := fun y _ => k - h - 1 - c + 2 * logSlope (profile (k - h - 1 - c) k) y
  have hinside (y t : ℝ) (hy : 0 < y) (hat : a < t) (htT : t ≤ T) : b t < y + (d - c * t) := by
    have := hline t ⟨hat.le,htT⟩
    linarith
  have hu : ContinuousOn (fun z : ℝ × ℝ => u z.1 z.2) (movingStrip (fun _ => 0) L a T) :=
    (lineDifference_continuousOn hp).mono (fun _ hz => (ha.le.trans hz.1))
  have hux (y t : ℝ) (hy : 0 < y) (_ : y < L) (hat : a < t) (htT : t ≤ T) :
      ContDiffAt ℝ 2 (fun z => u z t) y := by
    have hs : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => u z.1 z.2) (y,t) :=
      (lineDifference_contDiffAt hp (ha.trans hat) (hinside y t hy hat htT)).of_le
        (WithTop.coe_le_coe.mpr le_top)
    exact hs.comp y (show ContDiffAt ℝ 2 (fun z : ℝ => (z,t)) y by fun_prop)
  have hut (y t : ℝ) (hy : 0 < y) (_ : y < L) (hat : a < t) (htT : t ≤ T) :
      DifferentiableAt ℝ (u y) t := by
    have hs : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => u z.1 z.2) (y,t) :=
      (lineDifference_contDiffAt hp (ha.trans hat) (hinside y t hy hat htT)).of_le
        (WithTop.coe_le_coe.mpr le_top)
    exact (hs.comp t (show ContDiffAt ℝ 2 (fun s : ℝ => (y,s)) t by fun_prop)).differentiableAt
      (by norm_num)
  obtain ⟨hzero,hd⟩ := lineDifference_fit hp (ha.trans_le haT) hcontact
  have hpos := terminal_hopf (D := D)
    (M := -(k - h - 1 - c + 2 * negativeRoot (k - h - 1 - c) k)) hL haT hu hux hut
    (fun y t hy _ hat htT =>
        (lineDifference_equation hp (ha.trans hat) (hinside y t hy hat htT)).ge)
    (fun y t _ _ _ _ => by
      have := (profile_slope_bounds (β := k - h - 1 - c) hp.rate_pos y).1
      dsimp [D]
      linarith)
    hbottom (fun t hat _ => lineDifference_on_line_nonneg hp (ha.le.trans hat)) hright hzero hd
  exact (lt_irrefl 0) hpos

end MathFin.BlackScholes.AmericanPut.Boundary.Comparison
