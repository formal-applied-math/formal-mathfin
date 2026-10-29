/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.ComparisonHopf
public import MathFin.BlackScholes.AmericanPut.Boundary.TangentGeometry

/-!
# Geometric assembly of the terminal rectangle

Step 5 uses the single-positive-interval property as an explicit modular
hypothesis, never a field of the pricing solution. `ComparisonUnimodality`
supplies it on the continuous-boundary contract. Later positivity, the earlier
positive point, continuity, and order connectedness construct the rectangle
prohibited by the checked Hopf argument. Only the final differential-curvature
corollary uses the stronger classical contract.

## Result

Public entry points include `lineDifference_on_line_pos`,
`no_contact_of_past_line_below_and_terminal_positive`, `no_isolated_contact_of_positive_intervals`,
`curvature_nonneg_of_tangent_intervals`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary.Comparison

open Set Filter
open scoped Topology ContDiff

variable {k h c d : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}

/-- If the comparison line is strictly in continuation, its difference from
the American price is positive. No restriction to below-strike points is
needed: the actual payoff dominates the intrinsic expression everywhere. -/
theorem lineDifference_on_line_pos (hp : ContinuousBoundaryPutSolution k h p b) {t : ℝ}
    (ht : 0 < t) (hline : b t < d - c * t) : 0 < lineDifference p k h c d 0 t := by
  have hq := (straightPrice_fit hp.rate_pos hp.dividend_nonneg c d t).1
  have hpbound : 1 - Real.exp (d - c * t) < p (d - c * t) t :=
    (le_max_left _ _).trans_lt (hp.continuation (d - c * t) t ht hline)
  change 0 < (p (0 + (d - c * t)) t - straightPrice k h c d (0 + (d - c * t)) t) /
    profile (k - h - 1 - c) k (0 + (d - c * t) + c * t - d)
  rw [zero_add, hq]
  exact div_pos (sub_pos.mpr hpbound) ((profile_data hp.rate_pos.le).pos _)

/-- Construct the forbidden rectangle from positivity at the terminal slice,
strict line inclusion just before contact, and the interval hypothesis. -/
theorem no_contact_of_past_line_below_and_terminal_positive
    (hp : ContinuousBoundaryPutSolution k h p b) {A T x₁ : ℝ}
    (hA : 0 < A) (hAT : A < T) (hcontact : b T = d - c * T)
    (hline : ∀ t ∈ Ico A T, b t < d - c * t)
    (hx₁ : b T < x₁) (hpos : 0 < straightDifference p k h c d x₁ T)
    (hinterval : ∀ t, 0 < t →
      OrdConnected {x | b t < x ∧ 0 < straightDifference p k h c d x t}) : False := by
  let L := x₁ - (d - c * T)
  have hL : 0 < L := by dsimp [L]; rw [hcontact] at hx₁; linarith
  have hLT : 0 < lineDifference p k h c d L T := by
    simpa only [lineDifference, movingLineTransform, L, sub_add_cancel] using hpos
  have hT : 0 < T := hA.trans hAT
  have hcont : ContinuousAt (lineDifference p k h c d L) T := by
    have hs := (lineDifference_continuousOn (c := c) (d := d) hp) (L,T) hT.le
    have hmap : Tendsto (fun s : ℝ => (L,s)) (𝓝 T) (𝓝[{z : ℝ × ℝ | 0 ≤ z.2}] (L,T)) :=
      tendsto_nhdsWithin_iff.mpr ⟨continuousAt_const.prodMk continuousAt_id, Ici_mem_nhds hT⟩
    exact Tendsto.comp (g := fun z : ℝ × ℝ => lineDifference p k h c d z.1 z.2)
      (f := fun s : ℝ => (L,s)) hs hmap
  obtain ⟨l,r,⟨hl,hr⟩,hnear⟩ := (hcont.eventually (Ioi_mem_nhds hLT)).exists_Ioo_subset
  obtain ⟨a,haa,haT⟩ := exists_between (max_lt hAT hl)
  have hAa : A < a := (le_max_left _ _).trans_lt haa
  have hla : l < a := (le_max_right _ _).trans_lt haa
  have ha : 0 < a := hA.trans hAa
  have hright : ∀ t ∈ Icc a T, 0 < lineDifference p k h c d L t := by
    intro t ht
    exact hnear ⟨hla.trans_le ht.1, ht.2.trans_lt hr⟩
  have hlefta : b a < d - c * a := hline a ⟨hAa.le,haT⟩
  have hline' : ∀ t ∈ Icc a T, b t ≤ d - c * t := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with he | he
    · simpa [he] using hcontact.le
    · exact (hline t ⟨hAa.le.trans ht.1,he⟩).le
  apply lineDifference_no_positive_rectangle hp hL ha haT.le hline' hcontact ?_ hright
  intro y hy
  have hleftpos : 0 < straightDifference p k h c d (d - c * a) a := by
    simpa only [lineDifference, movingLineTransform, zero_add] using
      lineDifference_on_line_pos hp ha hlefta
  have hrpos : 0 < straightDifference p k h c d (L + (d - c * a)) a :=
    hright a ⟨le_rfl,haT.le⟩
  have hrightmem : L + (d - c * a) ∈ {x | b a < x ∧ 0 < straightDifference p k h c d x a} :=
    ⟨by linarith,hrpos⟩
  have hm := (hinterval a ha).out ⟨hlefta,hleftpos⟩ hrightmem
    (show y + (d - c * a) ∈ Icc (d - c * a) (L + (d - c * a)) from
      ⟨by linarith [hy.1], by linarith [hy.2]⟩)
  exact hm.2

/-- Step 5 with its propagation premise explicit. A line
which touches from above at an isolated local contact is impossible if every
positive continuation slice is an interval. -/
theorem no_isolated_contact_of_positive_intervals (hp : ContinuousBoundaryPutSolution k h p b)
    (hc : 0 < c) (hd : d ≤ 0) {T : ℝ} (hT : 0 < T)
    (hcontact : b T = d - c * T)
    (hbelow : ∀ᶠ t in 𝓝 T, t ≠ T → b t < d - c * t)
    (hinterval : ∀ t, 0 < t →
      OrdConnected {x | b t < x ∧ 0 < straightDifference p k h c d x t}) : False := by
  obtain ⟨l,r,⟨hl,hr⟩,hnear⟩ := hbelow.exists_Ioo_subset
  obtain ⟨A,hAl,hAT⟩ := exists_between (max_lt hl hT)
  have hA : 0 < A := (le_max_right _ _).trans_lt hAl
  have hlA : l < A := (le_max_left _ _).trans_lt hAl
  obtain ⟨U,hTU,hUr⟩ := exists_between hr
  have hbU : b U < d - c * U := hnear ⟨hl.trans hTU,hUr⟩ hTU.ne'
  have hposU : 0 < straightDifference p k h c d (d - c * U) U := by
    simpa only [lineDifference, movingLineTransform, zero_add] using
      lineDifference_on_line_pos hp (hT.trans hTU) hbU
  obtain ⟨x₁,hx₁,hpos⟩ :=
      straightDifference_positive_at_earlier_time hp hc hd hT.le hTU.le hbU.le hposU
  exact no_contact_of_past_line_below_and_terminal_positive hp hA hAT hcontact
    (fun t ht => hnear ⟨hlA.trans_le ht.1,ht.2.trans hr⟩ ht.2.ne) hx₁ hpos hinterval

/-- Local curvature conclusion for a decreasing tangent with nonpositive
intercept. Its interval-invariance hypothesis is supplied separately. This theorem
assembles the actual PDE comparison, maximum principle, geometry and Hopf
contradiction; it does not assume an abstract no-tangency principle. -/
theorem curvature_nonneg_of_tangent_intervals (hp : DividendPutSolution k h p b)
    {T : ℝ} (hT : 0 < T) (hspeed : deriv b T < 0)
    (hintercept : b T - T * deriv b T ≤ 0)
    (hinterval : ∀ t, 0 < t → OrdConnected
      {x | b t < x ∧ 0 < straightDifference p k h (-deriv b T) (b T - T * deriv b T) x t}) :
    0 ≤ deriv (deriv b) T := by
  by_contra hn
  have hneg : deriv (deriv b) T < 0 := lt_of_not_ge hn
  have hnear := eventually_lt_tangent_of_second_deriv_neg hp.boundary_smooth hT hneg
  apply no_isolated_contact_of_positive_intervals hp (neg_pos.mpr hspeed) hintercept hT
    (show b T = b T - T * deriv b T - (-deriv b T) * T by ring) ?_ hinterval
  filter_upwards [hnear] with t ht hne
  convert ht hne using 1
  ring

/-- Zero-dividend version of the same conditional local curvature result. -/
theorem zeroDividend_curvature_nonneg_of_tangent_intervals {k : ℝ}
    {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} (hp : NormalizedPutSolution k p b)
    {T : ℝ} (hT : 0 < T) (hspeed : deriv b T < 0)
    (hintercept : b T - T * deriv b T ≤ 0)
    (hinterval : ∀ t, 0 < t → OrdConnected
      {x | b t < x ∧ 0 < straightDifference p k 0 (-deriv b T) (b T - T * deriv b T) x t}) :
    0 ≤ deriv (deriv b) T :=
  curvature_nonneg_of_tangent_intervals (dividendPutSolution_zero_iff.mpr hp)
    hT hspeed hintercept hinterval

end MathFin.BlackScholes.AmericanPut.Boundary.Comparison
