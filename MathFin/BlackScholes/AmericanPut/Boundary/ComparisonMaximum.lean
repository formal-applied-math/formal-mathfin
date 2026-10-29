/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.ComparisonTail
public import MathFin.BlackScholes.AmericanPut.Boundary.ParabolicMaximum

/-!
# Maximum principle for the actual normalized comparison difference

Nonpositive data cannot become positive, on the unbounded moving continuation
region, even when the initial time is expiry. This proves the maximum-principle
parts of Steps 4 and 5, not the positive-interval or zero-number invariant.

## Result

Public entry points include `straightDifference_boundary_nonpos`,
`straightDifference_le_of_initial_le`, `straightDifference_positive_at_earlier_time`,
`zeroDividend_le_of_initial_le`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary.Comparison

open Set Filter
open scoped Topology ContDiff

variable {k h c d : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}

theorem straightDifference_boundary_nonpos (hp : ContinuousBoundaryPutSolution k h p b)
    (hc : 0 ≤ c) (hd : d ≤ 0) {t : ℝ} (ht : 0 ≤ t) :
    straightDifference p k h c d (b t) t ≤ 0 := by
  have hb : b t ≤ 0 := by
    rcases eq_or_lt_of_le ht with he | he
    · simpa [← he] using hp.boundary_initial.le
    · exact hp.boundary_nonpos he
  have hpfit : p (b t) t = 1 - Real.exp (b t) := by
    rcases eq_or_lt_of_le ht with he | he
    · simp [← he, hp.boundary_initial, hp.initial, putPayoff]
    · exact hp.exercise (b t) t he le_rfl
  have hbound := straightPrice_dominates hp.dividend_nonneg
    hp.dividend_le_rate hc hd ht hb
  apply div_nonpos_of_nonpos_of_nonneg _ ((profile_data hp.rate_pos.le).pos _).le
  change p (b t) t - straightPrice k h c d (b t) t ≤ 0
  rw [hpfit]
  linarith

/-- All nonnegative upper levels are preserved if they bound an entire time
slice. This is the no-positive-data branch of Step 4, including `a=0`. -/
theorem straightDifference_le_of_initial_le (hp : ContinuousBoundaryPutSolution k h p b)
    (hc : 0 < c) (hd : d ≤ 0) {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 ≤ ε)
    (hinit : ∀ x, b a ≤ x → straightDifference p k h c d x a ≤ ε)
    {x T : ℝ} (haT : a ≤ T) (hx : b T ≤ x) :
    straightDifference p k h c d x T ≤ ε := by
  obtain ⟨X, hX, htail⟩ := straightDifference_right_negative hp hc hd
  let R := max X x
  let v := straightDifference p k h c d
  let f := profile (k - h - 1 - c) k
  let g := profile (k - h - 1 + 2 - c) h
  have hf : ProfileData (k - h - 1 - c) k f := profile_data hp.rate_pos.le
  have hg : ProfileData (k - h - 1 + 2 - c) h g := profile_data hp.dividend_nonneg
  have hRpos : 0 < R := hX.trans_le (le_max_left _ _)
  have hb : ContinuousOn b (Icc a T) := hp.boundary_continuous.mono (fun _ ht => ha.trans ht.1)
  have hR : ∀ t ∈ Icc a T, b t ≤ R := by
    intro t ht
    have ht0 : 0 ≤ t := ha.trans ht.1
    have hbt : b t ≤ 0 := by
      rcases eq_or_lt_of_le ht0 with he | he
      · simp [← he, hp.boundary_initial]
      · exact hp.boundary_nonpos he
    exact hbt.trans hRpos.le
  have hv : ContinuousOn (fun z : ℝ × ℝ => v z.1 z.2 - ε) (movingStrip b R a T) :=
    ((normalizedDifference_continuousOn (d := d) hp hf hg).mono
      (show movingStrip b R a T ⊆ {z | 0 ≤ z.2} from fun _ ht => ha.trans ht.1)).sub
          continuousOn_const
  have hdt (y t : ℝ) (hat : a < t) (_ : t ≤ T) (hby : b t < y) (_ : y < R) :
      DifferentiableAt ℝ (fun s => v y s - ε) t := by
    have hs : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => v z.1 z.2) (y,t) :=
      (normalizedDifference_contDiffAt hp hf hg (ha.trans_lt hat) hby).of_le
        (WithTop.coe_le_coe.mpr le_top)
    exact ((hs.comp t (show ContDiffAt ℝ 2 (fun s : ℝ => (y,s)) t by fun_prop)).differentiableAt
      (by norm_num)).sub_const ε
  have hresult := parabolic_maximum (u := fun y t => v y t - ε)
    (D := fun y t => k - h - 1 + 2 * deriv f (y + c * t - d) / f (y + c * t - d))
    hb hR hv hdt
    (fun y t hat _ hby _ => (normalizedDifference_shifted_equation (ε := ε)
      hp hf hg (ha.trans_lt hat) hby).le)
    (fun y hby _ => sub_nonpos.mpr (hinit y hby))
    (fun t hat _ => sub_nonpos.mpr
      ((straightDifference_boundary_nonpos hp hc.le hd (ha.trans hat)).trans hε))
    (fun t hat _ => sub_nonpos.mpr
      ((htail R (le_max_left _ _) t (ha.trans hat)).le.trans hε))
    (x,T) ⟨haT, le_rfl, hx, le_max_right _ _⟩
  exact sub_nonpos.mp hresult

/-- The positive point required in Step 5 exists at every earlier time slice
if a positive continuation value exists later. No zero-count premise is used. -/
theorem straightDifference_positive_at_earlier_time (hp : ContinuousBoundaryPutSolution k h p b)
    (hc : 0 < c) (hd : d ≤ 0) {a T x : ℝ} (ha : 0 ≤ a) (haT : a ≤ T)
    (hx : b T ≤ x) (hpos : 0 < straightDifference p k h c d x T) :
    ∃ y, b a < y ∧ 0 < straightDifference p k h c d y a := by
  by_contra hn
  push Not at hn
  have hinit (y : ℝ) (hy : b a ≤ y) : straightDifference p k h c d y a ≤ 0 := by
    rcases eq_or_lt_of_le hy with he | he
    · rw [← he]
      exact straightDifference_boundary_nonpos hp hc.le hd ha
    · exact hn y he
  have := straightDifference_le_of_initial_le hp hc hd ha le_rfl hinit haT hx
  linarith

/-- Zero-dividend checkpoint using the original published-proof solution
contract and `g=1`. It is a maximum principle, not a convexity claim. -/
theorem zeroDividend_le_of_initial_le {k c d : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : NormalizedPutSolution k p b) (hc : 0 < c) (hd : d ≤ 0)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 ≤ ε)
    (hinit : ∀ x, b a ≤ x →
      normalizedDifference p (profile (k - 1 - c) k) (fun _ => 1) c d x a ≤ ε)
    {x T : ℝ} (haT : a ≤ T) (hx : b T ≤ x) :
    normalizedDifference p (profile (k - 1 - c) k) (fun _ => 1) c d x T ≤ ε := by
  have hi : ∀ y, b a ≤ y → straightDifference p k 0 c d y a ≤ ε := by
    simpa only [straightDifference, sub_zero, profile, ↓reduceIte] using hinit
  simpa only [straightDifference, sub_zero, profile, ↓reduceIte] using
    straightDifference_le_of_initial_le
        (dividendPutSolution_zero_iff.mpr hp).toContinuousBoundaryPutSolution hc hd ha hε hi haT hx

end MathFin.BlackScholes.AmericanPut.Boundary.Comparison
