/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.BlackScholes.CallPriceFunction

/-!
# Arbitrage-free interpolation of a quoted call-price smile

Kahalé, "An arbitrage-free interpolation of volatilities" (*Risk*, 17(5), 2004, 102–106),
poses and solves: given finitely many market-quoted call prices at increasing strikes that are
*already* free of static arbitrage, build a continuum of prices between them — an interpolant —
that is itself free of static arbitrage everywhere, not only at the quoted strikes. His published
construction interpolates the prices on each strike interval by a convex piece of Black–Scholes
form plus an affine term, reaching class `C²` through two nested non-linear minimisations; the
original is a paywalled *Risk Magazine* article, and the secondary literature that discusses it
(Fengler, *Arbitrage-Free Smoothing of the Implied Volatility Surface*, SFB 649 Discussion
Paper 2005-019: "piecewise convex polynomials that have the form of the Black Scholes (BS)
valuation formula with an additive linear term" — shortened in the Quantitative Finance 9(4),
2009 published version to "piecewise convex polynomials mimicking the BS pricing formula"; Le
Floc'h, arXiv:2004.08650: "two embedded non-linear minimizations", "not proven ... converges")
names the shape of the pieces but does not reproduce the equations that pin them down. None of
that is enough to transcribe faithfully, so this file does not attempt the `C²` scheme.

**What is formalised instead.** The static no-arbitrage conditions Kahalé's interpolant must
preserve — convexity in the strike (no butterfly arbitrage) and monotonicity (no vertical-spread
arbitrage) — are already in this library as `IsNormalizedCallPrice`
(`CallPriceFunction.lean`, Roper's *Arbitrage free implied volatility surfaces* (2010),
Theorem 2.1). What is missing, and the genuine content of an *interpolation-scheme* result rather
than a *parametrisation* result (the SVI family already covers the latter, `SVI/BlackSmile.lean`),
is the existence half: that finitely many arbitrage-free quotes actually admit an arbitrage-free
extension to every strike in between. This file proves that for the simplest such extension —
the piecewise-**linear** interpolant through the quoted points — which is also the baseline every
smooth scheme, Kahalé's included, is implicitly compared against. A discrete dataset
`(K 0, C 0), …, (K n, C n)` with increasing strikes, non-increasing prices (no vertical-spread
arbitrage among the quotes) and non-decreasing secant slopes (no butterfly arbitrage among the
quotes) extends to a function that is convex and non-increasing on the whole strike range
`[K 0, K n]`, and agrees with the quoted data exactly at every knot and along every linear piece
(`convexOn_piecewiseLinear`, `antitoneOn_piecewiseLinear`, `piecewiseLinear_eq_knot`,
`piecewiseLinear_eq_segment`). **Not formalised**: Kahalé's `C²` construction itself, any
smoothness beyond piecewise-linearity, and any extrapolation outside `[K 0, K n]` — the
asymptotic conditions `IsNormalizedCallPrice` also carries (the limits at strike `0` and at
infinity) are a separate, unrelated concern this file says nothing about. Nor are the price
bounds of `IsNormalizedCallPrice` (`intrinsic_le`, `le_one`) assumed on the quotes or derived
for the interpolant: `IsArbitrageFreeQuotes` is the convexity-and-monotonicity trace only.

## Main definitions and results

* `piecewiseLinear K C n`: the piecewise-linear function through `(K 0, C 0), …, (K n, C n)`,
  defined by recursion on `n` (the number of segments).
* `IsArbitrageFreeQuotes K C n`: the discrete no-arbitrage hypotheses on the quoted data —
  `strikes_mono` (strictly increasing strikes), `prices_anti` (non-increasing prices, the
  discrete no-vertical-spread-arbitrage condition), `no_butterfly` (non-decreasing secant
  slopes, the discrete no-butterfly-arbitrage condition).
* `convexOn_piecewiseLinear`, `antitoneOn_piecewiseLinear`: the interpolant is convex and
  non-increasing on `Set.Icc (K 0) (K n)`.
* `piecewiseLinear_eq_knot`: it reproduces every quoted price exactly.
* `piecewiseLinear_eq_segment`: on each quoted interval it *is* the straight line through the
  two endpoint quotes (so it is genuinely the piecewise-linear interpolant, not merely some
  convex function agreeing with the data at the knots).
* `isArbitrageFreeQuotes_of_isNormalizedCallPrice`: the trace a genuine arbitrage-free call price
  function (`IsNormalizedCallPrice`) leaves on finitely many increasing strikes satisfies
  `IsArbitrageFreeQuotes` — real market quotes sampled from one automatically do. (One direction
  only: `IsArbitrageFreeQuotes` carries no price bounds, so it is weaker than being such a trace.)
-/

@[expose] public section

namespace MathFin

open Set

/-- The piecewise-linear interpolant through `n + 1` quoted points `(K 0, C 0), …, (K n, C n)`,
for `n ≥ 1` (the `n = 0` case returns the junk value `0`, never used by the theorems below).
Defined by recursion on the number of segments: one affine piece for `n = 1`, and for
`n = m + 2` the previous interpolant extended by one more affine piece on `[K (m+1), K (m+2)]`. -/
noncomputable def piecewiseLinear (K C : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, x => C 0 + (C 1 - C 0) / (K 1 - K 0) * (x - K 0)
  | (m + 2), x =>
      if x ≤ K (m + 1) then piecewiseLinear K C (m + 1) x
      else C (m + 1) + (C (m + 2) - C (m + 1)) / (K (m + 2) - K (m + 1)) * (x - K (m + 1))

/-- The discrete no-static-arbitrage conditions on `n + 1` quoted (strike, price) pairs:
strictly increasing strikes, non-increasing prices (no vertical-spread arbitrage), and
non-decreasing secant slopes (no butterfly arbitrage). -/
structure IsArbitrageFreeQuotes (K C : ℕ → ℝ) (n : ℕ) : Prop where
  /-- Strikes are strictly increasing across the quoted range. -/
  strikes_mono : StrictMonoOn K (Iic n)
  /-- Prices are non-increasing: no vertical call spread has a negative price. -/
  prices_anti : AntitoneOn C (Iic n)
  /-- Secant slopes are non-decreasing: no butterfly spread has a negative price. -/
  no_butterfly : ∀ i, i + 2 ≤ n →
      (C (i + 1) - C i) / (K (i + 1) - K i) ≤ (C (i + 2) - C (i + 1)) / (K (i + 2) - K (i + 1))

/-! ### Two generic gluing lemmas

Neither mentions `piecewiseLinear`: they glue an arbitrary convex piece on the left to an
arbitrary *affine* piece on the right, which is the shape the inductive step below always has
(the newest segment is always affine). Monotonicity glues for free (`antitoneOn_glue`); convexity
needs one quantitative hypothesis, `hjump`, bounding every secant from the left piece into the
junction by the new piece's slope — the discrete no-butterfly condition, carried to the
continuum. -/

private lemma antitoneOn_glue {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hleft : AntitoneOn f (Icc a b)) (hright : AntitoneOn f (Icc b c)) :
    AntitoneOn f (Icc a c) := by
  rw [← Icc_union_Icc_eq_Icc hab hbc]
  exact hleft.union_right hright (isGreatest_Icc hab) (isLeast_Icc hbc)

/-- If `L` bounds the secant from `y` into the junction `b`, and `f` is affine with slope `s ≥ L`
beyond `b`, then `L` also bounds the secant from `y` into any point beyond `b`. The algebraic core
of gluing a convex piece to an affine one. -/
private lemma slope_le_of_affine_beyond {f : ℝ → ℝ} {y b z s L : ℝ} (hyb : y < b) (hbz : b < z)
    (hL : L ≤ (f b - f y) / (b - y)) (hLs : L ≤ s) (haff : f z = f b + s * (z - b)) :
    L ≤ (f z - f y) / (z - y) := by
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < b - y)] at hL
  rw [haff, le_div_iff₀ (by linarith : (0 : ℝ) < z - y)]
  nlinarith [mul_le_mul_of_nonneg_right hLs (by linarith : (0 : ℝ) ≤ z - b)]

/-- Gluing a convex left piece to an affine right piece stays convex, provided every secant from
the left piece into the junction is bounded above by the new piece's slope (the continuum form of
the discrete no-butterfly condition at the junction). -/
private lemma convexOn_glue {f : ℝ → ℝ} {a b c s : ℝ} (hab : a < b) (_hbc : b < c)
    (hleft : ConvexOn ℝ (Icc a b) f)
    (hjump : ∀ y ∈ Ico a b, (f b - f y) / (b - y) ≤ s)
    (haffine : ∀ z ∈ Icc b c, f z = f b + s * (z - b)) :
    ConvexOn ℝ (Icc a c) f := by
  apply convexOn_of_slope_mono_adjacent (convex_Icc a c)
  intro x y z hx hz hxy hyz
  by_cases hzb : z ≤ b
  · -- x < y < z ≤ b: all three lie in the left piece
    have hxm : x ∈ Icc a b := ⟨hx.1, (hxy.trans hyz).le.trans hzb⟩
    have hzm : z ∈ Icc a b := ⟨hx.1.trans (hxy.trans hyz).le, hzb⟩
    exact hleft.slope_mono_adjacent hxm hzm hxy hyz
  · replace hzb : b < z := not_le.mp hzb
    by_cases hxb : b ≤ x
    · -- b ≤ x < y < z: all three lie in the (affine) right piece, slopes are literally `s`
      have hxm : x ∈ Icc b c := ⟨hxb, hz.2.trans' (hxy.trans hyz).le⟩
      have hym : y ∈ Icc b c := ⟨hxb.trans hxy.le, hz.2.trans' hyz.le⟩
      have hzm : z ∈ Icc b c := ⟨hxb.trans (hxy.trans hyz).le, hz.2⟩
      have e1 := haffine x hxm
      have e2 := haffine y hym
      have e3 := haffine z hzm
      have hs1 : (f y - f x) / (y - x) = s := by
        rw [e1, e2, div_eq_iff (sub_ne_zero.mpr hxy.ne')]; ring
      have hs2 : (f z - f y) / (z - y) = s := by
        rw [e2, e3, div_eq_iff (sub_ne_zero.mpr hyz.ne')]; ring
      rw [hs1, hs2]
    · -- x < b < z: the junction sits strictly between x and z
      have hxlt : x < b := lt_of_not_ge hxb
      by_cases hyb : y < b
      · -- x < y < b < z
        have h1 := hleft.slope_mono_adjacent ⟨hx.1, hxlt.le⟩ (right_mem_Icc.2 hab.le) hxy hyb
        have h2 : (f b - f y) / (b - y) ≤ (f z - f y) / (z - y) :=
          slope_le_of_affine_beyond hyb hzb le_rfl (hjump y ⟨hx.1.trans hxy.le, hyb⟩)
            (haffine z ⟨hzb.le, hz.2⟩)
        exact h1.trans h2
      · -- x < b ≤ y < z: both `y` and `z` lie in the (affine) right piece
        replace hyb : b ≤ y := not_lt.mp hyb
        have hL := hjump x ⟨hx.1, hxlt⟩
        have hay := haffine y ⟨hyb, hz.2.trans' hyz.le⟩
        have haz := haffine z ⟨hyb.trans hyz.le, hz.2⟩
        have h2 : (f y - f x) / (y - x) ≤ s := by
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < b - x)] at hL
          rw [hay, div_le_iff₀ (by linarith : (0 : ℝ) < y - x)]
          have hring : s * (y - x) = s * (y - b) + s * (b - x) := by ring
          linarith
        have h3 : (f z - f y) / (z - y) = s := by
          rw [hay, haz, div_eq_iff (sub_ne_zero.mpr hyz.ne')]; ring
        rw [h3]; exact h2

/-! ### An affine function is convex, and antitone when its slope is non-positive

The two base-case facts the induction below reduces to: each new segment of
`piecewiseLinear` is an explicit affine function, so its convexity and its monotonicity (given a
non-positive slope) are immediate from the secant characterisations. -/

private lemma convexOn_affine (m b₀ x₀ : ℝ) {s : Set ℝ} (hs : Convex ℝ s) :
    ConvexOn ℝ s (fun x ↦ b₀ + m * (x - x₀)) := by
  apply convexOn_of_slope_mono_adjacent hs
  intro p q r _ _ hpq hqr
  have e1 : (b₀ + m * (q - x₀) - (b₀ + m * (p - x₀))) / (q - p) = m := by
    rw [div_eq_iff (sub_ne_zero.mpr hpq.ne')]; ring
  have e2 : (b₀ + m * (r - x₀) - (b₀ + m * (q - x₀))) / (r - q) = m := by
    rw [div_eq_iff (sub_ne_zero.mpr hqr.ne')]; ring
  rw [e1, e2]

private lemma antitoneOn_affine_of_nonpos {m b₀ x₀ : ℝ} (hm : m ≤ 0) (s : Set ℝ) :
    AntitoneOn (fun x ↦ b₀ + m * (x - x₀)) s := by
  intro p _ q _ hpq
  have h := mul_le_mul_of_nonpos_left hpq hm
  have e : m * (q - x₀) - m * (p - x₀) = m * q - m * p := by ring
  dsimp only
  linarith

/-! ### Restricting arbitrage-free quotes to a shorter prefix -/

private lemma IsArbitrageFreeQuotes.restrict {K C : ℕ → ℝ} {n m : ℕ} (hmn : m ≤ n)
    (h : IsArbitrageFreeQuotes K C n) : IsArbitrageFreeQuotes K C m where
  strikes_mono := h.strikes_mono.mono (Iic_subset_Iic.2 hmn)
  prices_anti := h.prices_anti.mono (Iic_subset_Iic.2 hmn)
  no_butterfly := fun i hi => h.no_butterfly i (hi.trans hmn)

/-! ### The induction -/

/-- The combined specification, proved at once by induction on the number of segments: the
piecewise-linear interpolant through `n + 1` arbitrage-free quotes is convex and non-increasing
on the quoted strike range, reproduces every quote exactly, and on each quoted interval literally
*is* the straight line through its two endpoint quotes. -/
private theorem piecewiseLinear_spec (K C : ℕ → ℝ) : ∀ n, 1 ≤ n →
    IsArbitrageFreeQuotes K C n →
      ConvexOn ℝ (Icc (K 0) (K n)) (piecewiseLinear K C n) ∧
      AntitoneOn (piecewiseLinear K C n) (Icc (K 0) (K n)) ∧
      (∀ i ≤ n, piecewiseLinear K C n (K i) = C i) ∧
      (∀ i, i + 1 ≤ n → ∀ x ∈ Icc (K i) (K (i + 1)),
        piecewiseLinear K C n x = C i + (C (i + 1) - C i) / (K (i + 1) - K i) * (x - K i)) := by
  intro n
  induction n with
  | zero => omega
  | succ m ih =>
    match m, ih with
    | 0, _ =>
      intro _ hq
      have hK01 : K 0 < K 1 := hq.strikes_mono (mem_Iic.2 (by omega)) (mem_Iic.2 le_rfl) one_pos
      have hC01 : C 1 ≤ C 0 := hq.prices_anti (mem_Iic.2 (by omega)) (mem_Iic.2 le_rfl) one_pos.le
      set sl : ℝ := (C 1 - C 0) / (K 1 - K 0) with hsl
      have hslnp : sl ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      have hconv : ConvexOn ℝ (Icc (K 0) (K 1)) (piecewiseLinear K C 1) :=
        convexOn_affine sl (C 0) (K 0) (convex_Icc _ _)
      have hanti : AntitoneOn (piecewiseLinear K C 1) (Icc (K 0) (K 1)) :=
        antitoneOn_affine_of_nonpos hslnp _
      have hd : K 1 - K 0 ≠ 0 := sub_ne_zero.mpr hK01.ne'
      refine ⟨hconv, hanti, ?_, ?_⟩
      · intro i hi
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · show C 0 + sl * (K 0 - K 0) = C 0; ring
        · show C 0 + sl * (K 1 - K 0) = C 1
          rw [hsl, div_mul_cancel₀ _ hd]; ring
      · intro i hi x hx
        obtain rfl : i = 0 := by omega
        show C 0 + sl * (x - K 0) = C 0 + (C 1 - C 0) / (K 1 - K 0) * (x - K 0)
        rw [hsl]
    | (m' + 1), ih =>
      intro _ hq
      obtain ⟨hconv, hanti, hknot, hseg⟩ := ih (by omega) (hq.restrict (by omega))
      have h0n : K 0 < K (m' + 1) :=
        hq.strikes_mono (mem_Iic.2 (by omega)) (mem_Iic.2 (by omega)) (by omega)
      have hKn : K (m' + 1) < K (m' + 2) :=
        hq.strikes_mono (mem_Iic.2 (by omega)) (mem_Iic.2 le_rfl) (by omega)
      have hCn : C (m' + 2) ≤ C (m' + 1) :=
        hq.prices_anti (mem_Iic.2 (by omega)) (mem_Iic.2 le_rfl) (by omega)
      set sl : ℝ := (C (m' + 2) - C (m' + 1)) / (K (m' + 2) - K (m' + 1)) with hsl
      have hslnp : sl ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      have hdef : ∀ x, piecewiseLinear K C (m' + 2) x =
          if x ≤ K (m' + 1) then piecewiseLinear K C (m' + 1) x
          else C (m' + 1) + sl * (x - K (m' + 1)) := fun x ↦ rfl
      have hfb : piecewiseLinear K C (m' + 2) (K (m' + 1)) = C (m' + 1) := by
        rw [hdef, ite_eq_left le_rfl]; exact hknot (m' + 1) le_rfl
      have haffine : ∀ z ∈ Icc (K (m' + 1)) (K (m' + 2)),
          piecewiseLinear K C (m' + 2) z = C (m' + 1) + sl * (z - K (m' + 1)) := by
        intro z hz
        rcases eq_or_lt_of_le hz.1 with hzn | hzn
        · rw [← hzn, hfb]; ring
        · rw [hdef, ite_eq_right (not_le.2 hzn)]
      have heqOn_old : Set.EqOn (piecewiseLinear K C (m' + 1)) (piecewiseLinear K C (m' + 2))
          (Icc (K 0) (K (m' + 1))) := fun x hx ↦ by rw [hdef, ite_eq_left hx.2]
      have hconv' : ConvexOn ℝ (Icc (K 0) (K (m' + 1))) (piecewiseLinear K C (m' + 2)) :=
        hconv.congr heqOn_old
      have hanti' : AntitoneOn (piecewiseLinear K C (m' + 2)) (Icc (K 0) (K (m' + 1))) := by
        intro p hp q hq' hpq
        rw [← heqOn_old hp, ← heqOn_old hq']
        exact hanti hp hq' hpq
      have hjump_glue : ∀ y ∈ Ico (K 0) (K (m' + 1)),
          (piecewiseLinear K C (m' + 2) (K (m' + 1)) - piecewiseLinear K C (m' + 2) y) /
            (K (m' + 1) - y) ≤ sl := by
        intro y hy
        rw [hfb, ← heqOn_old ⟨hy.1, hy.2.le⟩]
        by_cases hcase : K m' ≤ y
        · -- y ∈ [K m', K (m'+1)): the IH's own last piece is affine, so the secant is exactly
          -- the discrete slope between the last two knots, which no_butterfly bounds by `sl`
          have heq := hseg m' (by omega) y ⟨hcase, hy.2.le⟩
          have hbf := hq.no_butterfly m' (by omega)
          have hd : (0 : ℝ) < K (m' + 1) - K m' :=
            sub_pos.2 (hq.strikes_mono (mem_Iic.2 (by omega)) (mem_Iic.2 (by omega)) (by omega))
          have hy' : (0 : ℝ) < K (m' + 1) - y := by linarith [hy.2]
          have hkey : (C (m' + 1) - piecewiseLinear K C (m' + 1) y) / (K (m' + 1) - y) =
              (C (m' + 1) - C m') / (K (m' + 1) - K m') := by
            rw [heq]; field_simp [hy'.ne', hd.ne']; ring
          rw [hkey]; exact hbf
        · -- y < K m': the IH's convexity gives the secant bound via its own last secant
          replace hcase : y < K m' := not_le.mp hcase
          have hKmm1 : K m' < K (m' + 1) :=
            hq.strikes_mono (mem_Iic.2 (by omega)) (mem_Iic.2 (by omega)) (by omega)
          have hmem : y ∈ Icc (K 0) (K (m' + 1)) := ⟨hy.1, hy.2.le⟩
          have hnmem : K (m' + 1) ∈ Icc (K 0) (K (m' + 1)) :=
            ⟨(hq.strikes_mono.monotoneOn (mem_Iic.2 (by omega)) (mem_Iic.2 (by omega))
              (by omega : (0 : ℕ) ≤ m' + 1)), le_rfl⟩
          have h1 := hconv.secant_mono_aux3 hmem hnmem hcase hKmm1
          have h2 : (piecewiseLinear K C (m' + 1) (K (m' + 1)) -
              piecewiseLinear K C (m' + 1) (K m')) / (K (m' + 1) - K m') ≤ sl := by
            rw [hknot (m' + 1) le_rfl, hknot m' (by omega)]
            exact hq.no_butterfly m' (by omega)
          rw [← hknot (m' + 1) le_rfl]
          exact h1.trans h2
      have haffine_glue : ∀ z ∈ Icc (K (m' + 1)) (K (m' + 2)),
          piecewiseLinear K C (m' + 2) z =
            piecewiseLinear K C (m' + 2) (K (m' + 1)) + sl * (z - K (m' + 1)) :=
        fun z hz ↦ (haffine z hz).trans (by rw [hfb])
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact convexOn_glue h0n hKn hconv' hjump_glue haffine_glue
      · have hright_anti : AntitoneOn (piecewiseLinear K C (m' + 2))
            (Icc (K (m' + 1)) (K (m' + 2))) := by
          intro p hp q hq' hpq
          rw [haffine p hp, haffine q hq']
          exact antitoneOn_affine_of_nonpos hslnp _ hp hq' hpq
        exact antitoneOn_glue h0n.le hKn.le hanti' hright_anti
      · intro i hi
        rcases Nat.lt_or_ge i (m' + 2) with hi' | hi'
        · have hi'' : i ≤ m' + 1 := by omega
          rw [hdef, ite_eq_left (hq.strikes_mono.monotoneOn (mem_Iic.2 (by omega))
            (mem_Iic.2 (by omega)) hi'')]
          exact hknot i hi''
        · have hieq : i = m' + 2 := by omega
          subst hieq
          rw [hdef, ite_eq_right (not_le.2 hKn), hsl]
          have hd : K (m' + 2) - K (m' + 1) ≠ 0 := sub_ne_zero.mpr hKn.ne'
          field_simp
          ring
      · intro i hi x hx
        rcases Nat.lt_or_ge (i + 1) (m' + 2) with hi' | hi'
        · have hxle : x ≤ K (m' + 1) := hx.2.trans
            (hq.strikes_mono.monotoneOn (mem_Iic.2 (by omega)) (mem_Iic.2 (by omega)) (by omega))
          rw [hdef, ite_eq_left hxle]
          exact hseg i (by omega) x hx
        · have hieq : i = m' + 1 := by omega
          subst hieq
          exact haffine x hx

/-! ### The public interface -/

/-- **A finite arbitrage-free smile admits a piecewise-linear arbitrage-free interpolant.**
The piecewise-linear function through `n + 1` quoted call prices that are themselves free of
static arbitrage is convex (no butterfly arbitrage) on the whole quoted strike range. -/
theorem convexOn_piecewiseLinear (K C : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n)
    (hq : IsArbitrageFreeQuotes K C n) : ConvexOn ℝ (Icc (K 0) (K n)) (piecewiseLinear K C n) :=
  (piecewiseLinear_spec K C n hn hq).1

/-- The interpolant is also non-increasing (no vertical-spread arbitrage) on the whole quoted
strike range. -/
theorem antitoneOn_piecewiseLinear (K C : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n)
    (hq : IsArbitrageFreeQuotes K C n) : AntitoneOn (piecewiseLinear K C n) (Icc (K 0) (K n)) :=
  (piecewiseLinear_spec K C n hn hq).2.1

/-- The interpolant reproduces every quoted price exactly. -/
theorem piecewiseLinear_eq_knot (K C : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n)
    (hq : IsArbitrageFreeQuotes K C n) {i : ℕ} (hi : i ≤ n) :
    piecewiseLinear K C n (K i) = C i :=
  (piecewiseLinear_spec K C n hn hq).2.2.1 i hi

/-- On each quoted interval the interpolant *is* the straight line through its two endpoint
quotes — it is genuinely the piecewise-linear interpolant, not merely some convex, antitone
function agreeing with the data at the knots. -/
theorem piecewiseLinear_eq_segment (K C : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n)
    (hq : IsArbitrageFreeQuotes K C n) {i : ℕ} (hi : i + 1 ≤ n) {x : ℝ}
    (hx : x ∈ Icc (K i) (K (i + 1))) :
    piecewiseLinear K C n x = C i + (C (i + 1) - C i) / (K (i + 1) - K i) * (x - K i) :=
  (piecewiseLinear_spec K C n hn hq).2.2.2 i hi x hx

/-! ### The bridge to the continuous no-arbitrage conditions

`IsArbitrageFreeQuotes` is not an ad hoc discretisation: the trace a genuine arbitrage-free call
price function (`IsNormalizedCallPrice`, Roper's Theorem 2.1) leaves on any finite increasing set
of strikes satisfies it. Real market quotes sampled from such a surface automatically
satisfy the hypotheses this file's interpolant needs. -/

/-- Sampling a normalised (arbitrage-free) call price function at finitely many positive,
increasing strikes produces arbitrage-free quotes. -/
theorem isArbitrageFreeQuotes_of_isNormalizedCallPrice {Cc : ℝ → ℝ} (hCc : IsNormalizedCallPrice Cc)
    {K : ℕ → ℝ} {n : ℕ} (hK : StrictMonoOn K (Iic n)) (hKpos : ∀ i ≤ n, 0 < K i) :
    IsArbitrageFreeQuotes K (Cc ∘ K) n where
  strikes_mono := hK
  prices_anti := fun i hi j hj hij ↦
    hCc.antitoneOn (hKpos i hi) (hKpos j hj) (hK.monotoneOn hi hj hij)
  no_butterfly := fun i hi ↦
    hCc.convexOn.slope_mono_adjacent (hKpos i (by omega)) (hKpos (i + 2) hi)
      (hK (mem_Iic.2 (by omega)) (mem_Iic.2 (by omega)) (by omega))
      (hK (mem_Iic.2 (by omega)) (mem_Iic.2 (by omega)) (by omega))

end MathFin
