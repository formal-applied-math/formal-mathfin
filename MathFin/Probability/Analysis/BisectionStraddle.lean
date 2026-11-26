/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Probability.Analysis.Bisection
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The straddle form of the bisection method

A bracket `(a, b)` **straddles** the level `C` for `f` when `f a < C ≤ f b`. One
bisection step (`bisectStep` of `Probability/Analysis/Bisection.lean`) maps a
straddling bracket to a straddling bracket, whatever `f` is: at the midpoint `m`,
`f m < C` selects the right half `(m, b)`, whose endpoints still straddle; the
other case selects the left half `(a, m)`.

With `f` continuous on the bracket and `a ≤ b`, the two endpoint sequences are
monotone and nested, so both converge, and the halving of the width
(`bisect_snd_sub_fst`) forces the limits to coincide. Continuity then makes the
common limit `r` a root, `f r = C`, and puts the midpoints within
`(b − a)/2ⁿ⁺¹` of it. This is the textbook bisection theorem: a sign change and
continuity suffice, no monotonicity. (`tendsto_bisectMid` needs neither
continuity nor a sign change, but converges to the *threshold*, which in general
is not a root; continuity makes the limit an actual solution.)

At a *threshold* `σ` of `f` against `C` on the bracket (`f x < C ↔ x < σ`, the
setting `Bisection.lean` analyses) with `lo < σ ≤ hi`, the initial bracket
straddles, so the general theorem applies: the limit is the threshold and
`f σ = C`.

## Main results

* `mapsTo_bisectStep_straddle`: a step preserves the straddle
  `{I | f I.1 < C ∧ C ≤ f I.2}`.
* `monotone_bisect_fst_of_straddle`, `antitone_bisect_snd_of_straddle`: under a
  straddled ordered starting bracket the endpoint sequences are monotone.
* `bisect_tendsto_root`: continuity plus an initial straddle converge the
  nested endpoints and midpoints to a root `r` with `f r = C`, the midpoints
  within `(b − a)/2ⁿ⁺¹` after `n` steps.
* `bisect_threshold_root`: at an interior threshold with continuity, the limit
  is the threshold and the threshold is a root.

## References

* [R. L. Burden and J. D. Faires, *Numerical Analysis*][BurdenFaires2011], §2.1
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 19.10

## Tags

bisection method, root finding, straddle, bracketing, intermediate value,
implied volatility solver, MSC 65M06, JEL C63
-/

@[expose] public section

namespace MathFin

open Filter Set Topology

/-- One bisection step keeps a straddling bracket straddling, whatever `f` and `C` are. -/
theorem mapsTo_bisectStep_straddle (f : ℝ → ℝ) (C : ℝ) :
    MapsTo (bisectStep f C) {I | f I.1 < C ∧ C ≤ f I.2} {I | f I.1 < C ∧ C ≤ f I.2} := by
  intro I hI
  simp only [bisectStep]
  split_ifs with h
  · exact ⟨h, hI.2⟩
  · exact ⟨hI.1, not_lt.1 h⟩

/-- One bisection step keeps both endpoints of an ordered bracket inside it, and keeps the
new endpoints ordered. -/
private lemma bisectStep_mem_Icc_of_le (f : ℝ → ℝ) (C : ℝ) {I : ℝ × ℝ} (hI : I.1 ≤ I.2) :
    (bisectStep f C I).1 ∈ Icc I.1 I.2 ∧ (bisectStep f C I).2 ∈ Icc I.1 I.2 ∧
      (bisectStep f C I).1 ≤ (bisectStep f C I).2 := by
  have hm : (I.1 + I.2) / 2 ∈ Icc I.1 I.2 ∧ I.1 ≤ (I.1 + I.2) / 2 ∧
      (I.1 + I.2) / 2 ≤ I.2 := ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  simp only [bisectStep]
  split_ifs with h
  · exact ⟨hm.1, ⟨hI, le_rfl⟩, hm.2.2⟩
  · exact ⟨⟨le_rfl, hI⟩, hm.1, hm.2.1⟩

/-- Under a straddled starting bracket `(a, b)` with `a ≤ b`, every endpoint of every
bracket stays in `[a, b]`, every bracket straddles, and stays ordered. -/
private lemma bisect_straddle_invariant (f : ℝ → ℝ) (C a b : ℝ) (hab : a ≤ b)
    (hstr : f a < C ∧ C ≤ f b) (n : ℕ) :
    (bisect f C a b n).1 ∈ Icc a b ∧ (bisect f C a b n).2 ∈ Icc a b ∧
      f (bisect f C a b n).1 < C ∧ C ≤ f (bisect f C a b n).2 ∧
      (bisect f C a b n).1 ≤ (bisect f C a b n).2 := by
  induction n with
  | zero => rw [bisect_zero]; exact ⟨⟨le_rfl, hab⟩, ⟨hab, le_rfl⟩, hstr.1, hstr.2, hab⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    obtain ⟨m1, m2, m3⟩ := bisectStep_mem_Icc_of_le f C h5
    have hstr' := mapsTo_bisectStep_straddle f C ⟨h3, h4⟩
    rw [bisect_succ]
    exact ⟨⟨le_trans h1.1 m1.1, le_trans m1.2 h2.2⟩, ⟨le_trans h1.1 m2.1, le_trans m2.2 h2.2⟩,
      hstr'.1, hstr'.2, m3⟩

/-- Under a straddled ordered starting bracket the left endpoints increase. -/
theorem monotone_bisect_fst_of_straddle (f : ℝ → ℝ) (C a b : ℝ) (hab : a ≤ b)
    (hstr : f a < C ∧ C ≤ f b) :
    Monotone fun n ↦ (bisect f C a b n).1 :=
  monotone_nat_of_le_succ fun n ↦ by
    have h5 := (bisect_straddle_invariant f C a b hab hstr n).2.2.2.2
    rw [bisect_succ]
    exact (bisectStep_mem_Icc_of_le f C h5).1.1

/-- Under a straddled ordered starting bracket the right endpoints decrease. -/
theorem antitone_bisect_snd_of_straddle (f : ℝ → ℝ) (C a b : ℝ) (hab : a ≤ b)
    (hstr : f a < C ∧ C ≤ f b) :
    Antitone fun n ↦ (bisect f C a b n).2 :=
  antitone_nat_of_succ_le fun n ↦ by
    have h5 := (bisect_straddle_invariant f C a b hab hstr n).2.2.2.2
    rw [bisect_succ]
    exact (bisectStep_mem_Icc_of_le f C h5).2.1.2

/-- **The textbook bisection theorem**: if `a ≤ b`, the bracket `(a, b)` straddles `C`
(`f a < C ≤ f b`) and `f` is continuous on `[a, b]`, the endpoint sequences and the
midpoint estimates of the bisection all converge to a root: there is `r ∈ [a, b]` with
`f r = C`, and the midpoints are within `(b − a)/2ⁿ⁺¹` of `r` after `n` steps. No
monotonicity of `f` is assumed. -/
theorem bisect_tendsto_root {f : ℝ → ℝ} {C a b : ℝ} (hab : a ≤ b) (hlo : f a < C)
    (hhi : C ≤ f b) (hcont : ContinuousOn f (Icc a b)) :
    ∃ r ∈ Icc a b, f r = C ∧
      Tendsto (fun n ↦ (bisect f C a b n).1) atTop (𝓝 r) ∧
      Tendsto (fun n ↦ (bisect f C a b n).2) atTop (𝓝 r) ∧
      Tendsto (bisectMid f C a b) atTop (𝓝 r) ∧
      ∀ n, |bisectMid f C a b n - r| ≤ (b - a) / 2 ^ (n + 1) := by
  have hstr : f a < C ∧ C ≤ f b := ⟨hlo, hhi⟩
  have hinv := bisect_straddle_invariant f C a b hab hstr
  have ham : Monotone fun n ↦ (bisect f C a b n).1 :=
    monotone_bisect_fst_of_straddle f C a b hab hstr
  have hbm : Antitone fun n ↦ (bisect f C a b n).2 :=
    antitone_bisect_snd_of_straddle f C a b hab hstr
  have hbd_a : BddAbove (range fun n ↦ (bisect f C a b n).1) :=
    ⟨b, fun x hx ↦ by obtain ⟨n, rfl⟩ := mem_range.1 hx; exact (hinv n).1.2⟩
  have hbd_b : BddBelow (range fun n ↦ (bisect f C a b n).2) :=
    ⟨a, fun x hx ↦ by obtain ⟨n, rfl⟩ := mem_range.1 hx; exact (hinv n).2.1.1⟩
  have ha_lim : Tendsto (fun n ↦ (bisect f C a b n).1) atTop
      (𝓝 (⨆ n, (bisect f C a b n).1)) := tendsto_atTop_ciSup ham hbd_a
  have hb_lim : Tendsto (fun n ↦ (bisect f C a b n).2) atTop
      (𝓝 (⨅ n, (bisect f C a b n).2)) := tendsto_atTop_ciInf hbm hbd_b
  have hwid : Tendsto (fun n ↦ (bisect f C a b n).2 - (bisect f C a b n).1) atTop (𝓝 0) := by
    refine (tendsto_const_div_atTop_nhds_zero_nat (b - a)).comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two) |>.congr' ?_
    filter_upwards with n
    rw [bisect_snd_sub_fst f C a b n]
    simp
  have hr_eq : ⨅ n, (bisect f C a b n).2 = ⨆ n, (bisect f C a b n).1 := by
    have h1 : Tendsto (fun n ↦ (bisect f C a b n).2 - (bisect f C a b n).1) atTop
        (𝓝 ((⨅ n, (bisect f C a b n).2) - ⨆ n, (bisect f C a b n).1)) := hb_lim.sub ha_lim
    exact eq_of_sub_eq_zero (tendsto_nhds_unique h1 hwid)
  have hr_ab : ⨆ n, (bisect f C a b n).1 ∈ Icc a b :=
    ⟨le_trans (hinv 0).1.1 (le_ciSup hbd_a 0),
      le_trans (hr_eq ▸ ciInf_le hbd_b 0) (hinv 0).2.1.2⟩
  have hcw : ContinuousWithinAt f (Icc a b) (⨆ n, (bisect f C a b n).1) := hcont _ hr_ab
  have hain : Tendsto (fun n ↦ (bisect f C a b n).1) atTop
      (𝓝[Icc a b] (⨆ n, (bisect f C a b n).1)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ha_lim
      (Eventually.of_forall fun n ↦ (hinv n).1)
  have hbin : Tendsto (fun n ↦ (bisect f C a b n).2) atTop
      (𝓝[Icc a b] (⨆ n, (bisect f C a b n).1)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (hr_eq ▸ hb_lim)
      (Eventually.of_forall fun n ↦ (hinv n).2.1)
  have hfa_lim : Tendsto (fun n ↦ f ((bisect f C a b n).1)) atTop
      (𝓝 (f (⨆ n, (bisect f C a b n).1))) :=
    Filter.Tendsto.comp hcw.tendsto hain
  have hfb_lim : Tendsto (fun n ↦ f ((bisect f C a b n).2)) atTop
      (𝓝 (f (⨆ n, (bisect f C a b n).1))) :=
    Filter.Tendsto.comp hcw.tendsto hbin
  have hC1 : C ≤ f (⨆ n, (bisect f C a b n).1) :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hfb_lim fun n ↦ (hinv n).2.2.2.1
  have hC2 : f (⨆ n, (bisect f C a b n).1) ≤ C :=
    le_of_tendsto_of_tendsto' hfa_lim tendsto_const_nhds fun n ↦ le_of_lt (hinv n).2.2.1
  have hrate : ∀ n, |bisectMid f C a b n - (⨆ n, (bisect f C a b n).1)| ≤
      (b - a) / 2 ^ (n + 1) := by
    intro n
    rw [bisectMid, abs_sub_le_iff, pow_succ, ← div_div, ← bisect_snd_sub_fst f C a b n]
    constructor <;> linarith [le_ciSup hbd_a n, hr_eq ▸ ciInf_le hbd_b n]
  refine ⟨⨆ n, (bisect f C a b n).1, hr_ab, le_antisymm hC2 hC1, ha_lim, hr_eq ▸ hb_lim,
    tendsto_iff_dist_tendsto_zero.2 <| squeeze_zero (fun _ ↦ dist_nonneg) hrate <|
      tendsto_const_nhds.div_atTop <| (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).comp
        (tendsto_add_atTop_nat 1),
    hrate⟩

/-- **The threshold theorem, from the straddle form.** At a threshold `σ` of `f` against
`C` on `[lo, hi]` with `lo < σ ≤ hi` (`f x < C ↔ x < σ`, the setting of
`tendsto_bisectMid`) and `f` continuous on the bracket, the bisection estimates converge
to the threshold and the threshold is a root: `f σ = C`. The plain threshold theorem
needs no continuity; continuity is what makes the limit an actual solution. -/
theorem bisect_threshold_root {f : ℝ → ℝ} {C lo hi σ : ℝ} (hloσ : lo < σ) (hσhi : σ ≤ hi)
    (hC : ∀ x ∈ Icc lo hi, f x < C ↔ x < σ) (hcont : ContinuousOn f (Icc lo hi)) :
    f σ = C ∧ Tendsto (bisectMid f C lo hi) atTop (𝓝 σ) := by
  have hmemσ : σ ∈ Icc lo hi := ⟨le_of_lt hloσ, hσhi⟩
  have hmemhi : hi ∈ Icc lo hi := ⟨le_trans (le_of_lt hloσ) hσhi, le_rfl⟩
  have hstr : f lo < C ∧ C ≤ f hi :=
    ⟨(hC lo ⟨le_refl _, le_trans (le_of_lt hloσ) hσhi⟩).2 hloσ,
      not_lt.1 fun hlt ↦ absurd ((hC hi hmemhi).1 hlt) (not_lt.2 hσhi)⟩
  obtain ⟨r, hr_ab, hr_eq, -, -, hmids, -⟩ :=
    bisect_tendsto_root (le_trans (le_of_lt hloσ) hσhi) hstr.1 hstr.2 hcont
  have hσlim : Tendsto (bisectMid f C lo hi) atTop (𝓝 σ) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ ↦ dist_nonneg) (abs_bisectMid_sub_le hC hmemσ) ?_
    exact tendsto_const_nhds.div_atTop ((tendsto_pow_atTop_atTop_of_one_lt one_lt_two).comp
      (tendsto_add_atTop_nat 1))
  rw [← tendsto_nhds_unique hmids hσlim]
  exact ⟨hr_eq, hmids⟩

end MathFin
