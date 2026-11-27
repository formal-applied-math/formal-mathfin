/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Risk.CompleteMixability
public import MathFin.Probability.Laws.Quantile
public import Mathlib.MeasureTheory.Function.Floor

/-!
# The quantile grid

`k` copies of a law `T` whose sum is deterministic up to the length of `T`'s interval: the
values of the quantile function at the `k` points `frac (w + j / k)`, `j < k`, of a rotated
grid. Each point is uniform when `w` is, so each copy has law `T`; and the grid samples one
point in each cell `[j/k, (j+1)/k)`, where the quantile function and its mean over the cell lie
between the same two values, so the errors telescope to at most `Q(1) - Q(0) ≤ L`.

This is Lemma 2.2 of Shmalo, with the uniform random bijection replaced by a rotation.

## Main results

* `MathFin.hasLaw_quantile_fract`: each grid copy has law `T`.
* `MathFin.abs_sum_quantile_fract_sub_le`: the sum is within `L` of `k` times the mean.

## References

* [Y. Shmalo, *Absolutely continuous laws on a bounded interval are completely mixable for all
  large n*][Shmalo2026CompleteMixability], Lemma 2.2

## Tags

complete mixability, quantile coupling, stratified sampling, MSC 60E05
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set

variable {T : Measure ℝ} [IsProbabilityMeasure T]

/-! ### The rotation of the circle -/

/-- A set squeezed between `Y` and `Y` plus one point has the measure of `Y`. -/
private lemma volume_eq_of_subset_insert {X Y : Set ℝ} {a : ℝ} (h : X ⊆ insert a Y) (h' : Y ⊆ X) :
    volume X = volume Y :=
  le_antisymm ((measure_mono h).trans (by rw [insert_eq]; exact (measure_union_le _ _).trans (by simp))) (measure_mono h')

/-- The rotation `w ↦ frac (w + c)` of the unit circle preserves Lebesgue measure on `(0, 1)`. -/
private lemma measurePreserving_fract_add {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    MeasurePreserving (fun w : ℝ ↦ Int.fract (w + c)) (volume.restrict (Ioo 0 1))
      (volume.restrict (Ioo 0 1)) := by
  have hr : Measurable fun w : ℝ ↦ Int.fract (w + c) := measurable_fract.comp (measurable_add_const c)
  refine ⟨hr, Measure.ext fun s hs ↦ ?_⟩
  rw [Measure.map_apply hr hs, Measure.restrict_apply (hr hs), Measure.restrict_apply hs]
  have hfr1 {w : ℝ} (h0 : 0 ≤ w + c - 1) (h1 : w + c - 1 < 1) :
      Int.fract (w + c) = w + c - 1 := by
    rw [← Int.fract_sub_one, Int.fract_eq_self.2 ⟨h0, h1⟩]
  have hA : MeasurableSet ((fun w : ℝ ↦ w + c) ⁻¹' (s ∩ Ioo c 1)) :=
    measurable_add_const c (hs.inter measurableSet_Ioo)
  have hB : MeasurableSet ((fun w : ℝ ↦ w + (c - 1)) ⁻¹' (s ∩ Ioo 0 c)) :=
    measurable_add_const (c - 1) (hs.inter measurableSet_Ioo)
  have hdisj : Disjoint ((fun w : ℝ ↦ w + c) ⁻¹' (s ∩ Ioo c 1))
      ((fun w : ℝ ↦ w + (c - 1)) ⁻¹' (s ∩ Ioo 0 c)) :=
    Set.disjoint_left.2 fun w hwA hwB ↦ by
      simp only [mem_preimage, mem_inter_iff, mem_Ioo] at hwA hwB
      linarith [hwA.2.2, hwB.2.1]
  have hdisj' : Disjoint (s ∩ Ioo c 1) (s ∩ Ioo 0 c) :=
    Set.disjoint_left.2 fun w hw1 hw2 ↦ by
      simp only [mem_inter_iff, mem_Ioo] at hw1 hw2
      linarith [hw1.2.1, hw2.2.2]
  calc volume ((fun w : ℝ ↦ Int.fract (w + c)) ⁻¹' s ∩ Ioo 0 1)
      = volume ((fun w : ℝ ↦ w + c) ⁻¹' (s ∩ Ioo c 1) ∪
          (fun w : ℝ ↦ w + (c - 1)) ⁻¹' (s ∩ Ioo 0 c)) := by
        refine volume_eq_of_subset_insert (a := 1 - c) ?_ ?_
        · rintro w ⟨hws, hw0, hw1⟩
          by_cases hlt : w + c < 1
          · refine Or.inr (Or.inl ⟨?_, by linarith, hlt⟩)
            rwa [mem_preimage, Int.fract_eq_self.2 ⟨by linarith, hlt⟩] at hws
          · by_cases heq : w = 1 - c
            · exact Or.inl heq
            · have h1 : 1 < w + c :=
                lt_of_le_of_ne (not_lt.1 hlt) fun h ↦ heq (by linarith)
              rw [mem_preimage, hfr1 (by linarith) (by linarith)] at hws
              refine Or.inr (Or.inr ⟨?_, by show 0 < w + (c - 1); linarith,
                by show w + (c - 1) < c; linarith⟩)
              show w + (c - 1) ∈ s
              rwa [show w + (c - 1) = w + c - 1 by ring]
        · rintro w (⟨hws, hw0, hw1⟩ | ⟨hws, hw0, hw1⟩)
          · refine ⟨?_, by linarith, by linarith⟩
            rwa [mem_preimage, Int.fract_eq_self.2 ⟨by linarith, hw1⟩]
          · refine ⟨?_, by linarith, by linarith⟩
            rw [mem_preimage, hfr1 (by linarith) (by linarith),
              show w + c - 1 = w + (c - 1) by ring]
            exact hws
    _ = volume (s ∩ Ioo c 1) + volume (s ∩ Ioo 0 c) := by
        rw [measure_union hdisj hB, measure_preimage_add_right, measure_preimage_add_right]
    _ = volume (s ∩ Ioo 0 1) := by
        rw [← measure_union hdisj' (hs.inter measurableSet_Ioo)]
        refine (volume_eq_of_subset_insert (a := c) ?_ ?_).symm
        · rintro w ⟨hws, hw0, hw1⟩
          rcases lt_trichotomy w c with h | h | h
          · exact Or.inr (Or.inr ⟨hws, hw0, h⟩)
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨hws, h, hw1⟩)
        · rintro w (⟨hws, hw0, hw1⟩ | ⟨hws, hw0, hw1⟩)
          · exact ⟨hws, by linarith, hw1⟩
          · exact ⟨hws, hw0, by linarith⟩

/-- Each copy of the rotated quantile grid has law `T`. -/
theorem hasLaw_quantile_fract (k j : ℕ) :
    HasLaw (fun w ↦ quantile T (Int.fract (w + j / k))) T (volume.restrict (Ioo 0 1)) := by
  have hrot (w : ℝ) : Int.fract (w + j / k) = Int.fract (w + Int.fract ((j : ℝ) / k)) := by
    conv_lhs => rw [← Int.fract_add_floor ((j : ℝ) / k), ← add_assoc, Int.fract_add_intCast]
  simp only [hrot]
  exact (hasLaw_quantile T).comp
    (measurePreserving_fract_add (Int.fract_nonneg _) (Int.fract_lt_one _)).hasLaw

/-! ### The grid sum -/

/-- Cyclic shifts permute `range k`. -/
private lemma sum_range_mod_add (k n : ℕ) [NeZero k] (h : ℕ → ℝ) :
    ∑ j ∈ Finset.range k, h ((n + j) % k) = ∑ i ∈ Finset.range k, h i := by
  rw [Finset.sum_range, Finset.sum_range]
  refine (Finset.sum_congr rfl fun j _ ↦ ?_).trans
    (Equiv.sum_comp (Equiv.addLeft (Fin.ofNat k n)) fun i : Fin k ↦ h i)
  simp [Fin.val_add, Nat.mod_add_mod]

/-- Off the grid `{m / k}`, the rotated grid `frac (w + j / k)`, `j < k`, is the grid
`(i + θ) / k`, `i < k`, for some `θ ∈ (0, 1)`. -/
private lemma sum_fract_grid {k : ℕ} (hk : 0 < k) {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1)
    (hnat : ∀ m : ℕ, w ≠ m / k) (g : ℝ → ℝ) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∑ j ∈ Finset.range k, g (Int.fract (w + j / k)) =
      ∑ i ∈ Finset.range k, g ((i + θ) / k) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have : NeZero k := ⟨hk.ne'⟩
  have hkw : 0 ≤ (k : ℝ) * w := by positivity
  set n := ⌊(k : ℝ) * w⌋₊ with hn
  have hnk : n < k := by
    rw [hn, Nat.floor_lt hkw]; nlinarith
  have hn1 : (n : ℝ) ≤ k * w := Nat.floor_le hkw
  have hθ1 : (k : ℝ) * w - n < 1 := by linarith [Nat.lt_floor_add_one ((k : ℝ) * w)]
  refine ⟨k * w - n, sub_pos.2 (lt_of_le_of_ne hn1 fun h ↦ hnat n ?_), hθ1, ?_⟩
  · field_simp; linarith
  · rw [← sum_range_mod_add k n fun i ↦ g ((i + (k * w - n)) / k)]
    refine Finset.sum_congr rfl fun j _ ↦ congrArg g ?_
    have hdm : (n : ℝ) + j = k * ((n + j) / k : ℕ) + ((n + j) % k : ℕ) := by
      exact_mod_cast (Nat.div_add_mod (n + j) k).symm
    have hr : (((n + j) % k : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast Nat.mod_lt (n + j) hk
    have hr0 : (0 : ℝ) ≤ ((n + j) % k : ℕ) := Nat.cast_nonneg _
    have h1 : w + j / k = ((((n + j) % k : ℕ) : ℝ) + (k * w - n)) / k + ((n + j) / k : ℕ) := by
      field_simp; linarith
    rw [h1, Int.fract_add_natCast]
    exact Int.fract_eq_self.2 ⟨by positivity [hθ1], (div_lt_one hk').2 (by linarith)⟩

/-- **Riemann sums of monotone functions.** For `f` monotone on `[0, 1]`, the sample at one
point per cell `[i/k, (i+1)/k]` differs from `k ∫₀¹ f` by at most `f 1 - f 0`. -/
private lemma abs_sum_sub_le_of_monotoneOn {f : ℝ → ℝ} (hf : MonotoneOn f (Icc 0 1)) {k : ℕ}
    (hk : 0 < k) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    |∑ i ∈ Finset.range k, f ((i + θ) / k) - k * ∫ x in (0 : ℝ)..1, f x| ≤ f 1 - f 0 := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hint {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
      IntervalIntegrable f volume a b :=
    (hf.mono (Set.uIcc_subset_Icc ha hb)).intervalIntegrable
  set a : ℕ → ℝ := fun i ↦ (i : ℝ) / k with ha
  have ha_mem {i : ℕ} (hi : i ≤ k) : a i ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, by rw [ha]; dsimp only; rw [div_le_one hk']; exact_mod_cast hi⟩
  have hI : ∫ x in (0 : ℝ)..1, f x = ∑ i ∈ Finset.range k, ∫ x in a i..a (i + 1), f x := by
    rw [intervalIntegral.sum_integral_adjacent_intervals fun i hi ↦
      hint (ha_mem hi.le) (ha_mem (Nat.succ_le_of_lt hi))]
    simp [ha, hk'.ne']
  have hcell : ∀ i ∈ Finset.range k,
      |f ((i + θ) / k) - k * ∫ x in a i..a (i + 1), f x| ≤ f (a (i + 1)) - f (a i) := by
    intro i hi
    have hik : i < k := Finset.mem_range.1 hi
    have h0 := ha_mem hik.le
    have h1 := ha_mem (Nat.succ_le_of_lt hik)
    have hw : a (i + 1) - a i = 1 / k := by simp only [ha]; push_cast; ring
    have hab : a i ≤ a (i + 1) := by linarith [show (0 : ℝ) ≤ 1 / k by positivity]
    have hsub {x : ℝ} (hx : x ∈ Icc (a i) (a (i + 1))) : x ∈ Icc (0 : ℝ) 1 :=
      ⟨h0.1.trans hx.1, hx.2.trans h1.2⟩
    have hlo : (a (i + 1) - a i) * f (a i) ≤ ∫ x in a i..a (i + 1), f x := by
      simpa using intervalIntegral.integral_mono_on hab intervalIntegrable_const (hint h0 h1)
        fun x hx ↦ hf h0 (hsub hx) hx.1
    have hhi : ∫ x in a i..a (i + 1), f x ≤ (a (i + 1) - a i) * f (a (i + 1)) := by
      simpa using intervalIntegral.integral_mono_on hab (hint h0 h1) intervalIntegrable_const
        fun x hx ↦ hf (hsub hx) h1 hx.2
    have hlo' : f (a i) ≤ k * ∫ x in a i..a (i + 1), f x := by
      have := mul_le_mul_of_nonneg_left hlo hk'.le
      rwa [hw, ← mul_assoc, mul_one_div_cancel hk'.ne', one_mul] at this
    have hhi' : k * ∫ x in a i..a (i + 1), f x ≤ f (a (i + 1)) := by
      have := mul_le_mul_of_nonneg_left hhi hk'.le
      rwa [hw, ← mul_assoc, mul_one_div_cancel hk'.ne', one_mul] at this
    have hp0 : a i ≤ (i + θ) / k := by simp only [ha]; gcongr; linarith
    have hp1 : (i + θ) / k ≤ a (i + 1) := by simp only [ha]; push_cast; gcongr
    have hp : (i + θ) / k ∈ Icc (0 : ℝ) 1 := hsub ⟨hp0, hp1⟩
    have := hf h0 hp hp0
    have := hf hp h1 hp1
    exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  calc _ = |∑ i ∈ Finset.range k,
        (f ((i + θ) / k) - k * ∫ x in a i..a (i + 1), f x)| := by
        rw [hI, Finset.mul_sum, Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ Finset.range k, |f ((i + θ) / k) - k * ∫ x in a i..a (i + 1), f x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range k, (f (a (i + 1)) - f (a i)) := Finset.sum_le_sum hcell
    _ = f (a k) - f (a 0) := Finset.sum_range_sub (fun i ↦ f (a i)) k
    _ = f 1 - f 0 := by simp [ha, hk'.ne']

/-! ### The quantile function on `[0, 1]` -/

/-- A quantile function of a law carried by `[α, α + L]` stays in `[α, α + L]`. -/
private lemma quantile_mem_Icc {α L : ℝ} (hT : T (Icc α (α + L))ᶜ = 0) {p : ℝ}
    (hp : p ∈ Ioo 0 1) : quantile T p ∈ Icc α (α + L) := by
  refine ⟨le_of_forall_lt fun x hx ↦ (lt_quantile_iff hp).2 ?_, (quantile_le_iff hp).2 ?_⟩
  · calc cdf T x = T.real (Iic x) := cdf_eq_real _ _
      _ ≤ T.real (Icc α (α + L))ᶜ :=
        measureReal_mono fun y hy ↦ fun hy' ↦ (hx.trans_le hy'.1).not_ge hy
      _ = 0 := by rw [measureReal_def, hT]; simp
      _ < p := hp.1
  · calc p ≤ 1 := hp.2.le
      _ = T.real (Icc α (α + L)) := by
        rw [measureReal_def, (prob_compl_eq_zero_iff measurableSet_Icc).1 hT]; simp
      _ ≤ T.real (Iic (α + L)) := measureReal_mono Icc_subset_Iic_self
      _ = cdf T (α + L) := (cdf_eq_real _ _).symm

/-- The quantile function with its endpoint values `α` at `0` and `α + L` at `1` filled in. -/
private noncomputable def quantileExt (T : Measure ℝ) (α L p : ℝ) : ℝ :=
  if p ≤ 0 then α else if 1 ≤ p then α + L else quantile T p

omit [IsProbabilityMeasure T] in
private lemma quantileExt_of_le {α L p : ℝ} (h : p ≤ 0) : quantileExt T α L p = α := by
  simp [quantileExt, h]

omit [IsProbabilityMeasure T] in
private lemma quantileExt_of_ge {α L p : ℝ} (h : 1 ≤ p) : quantileExt T α L p = α + L := by
  simp [quantileExt, h, not_le.2 (zero_lt_one.trans_le h)]

omit [IsProbabilityMeasure T] in
private lemma quantileExt_of_mem {α L p : ℝ} (hp : p ∈ Ioo 0 1) :
    quantileExt T α L p = quantile T p := by
  simp [quantileExt, hp.1.not_ge, hp.2.not_ge]

private lemma monotoneOn_quantileExt {α L : ℝ} (hT : T (Icc α (α + L))ᶜ = 0) :
    MonotoneOn (quantileExt T α L) (Icc 0 1) := by
  have hL : 0 ≤ L := by
    have := quantile_mem_Icc hT (p := 1 / 2) ⟨by norm_num, by norm_num⟩
    linarith [this.1, this.2]
  intro x _ y _ hxy
  rcases le_or_gt x 0 with hx0 | hx0
  · rw [quantileExt_of_le hx0]
    rcases le_or_gt y 0 with hy0 | hy0
    · rw [quantileExt_of_le hy0]
    · rcases lt_or_ge y 1 with hy1 | hy1
      · rw [quantileExt_of_mem ⟨hy0, hy1⟩]; exact (quantile_mem_Icc hT ⟨hy0, hy1⟩).1
      · rw [quantileExt_of_ge hy1]; linarith
  · have hy0 : 0 < y := hx0.trans_le hxy
    rcases lt_or_ge x 1 with hx1 | hx1
    · rw [quantileExt_of_mem ⟨hx0, hx1⟩]
      rcases lt_or_ge y 1 with hy1 | hy1
      · rw [quantileExt_of_mem ⟨hy0, hy1⟩]
        exact monotoneOn_quantile ⟨hx0, hx1⟩ ⟨hy0, hy1⟩ hxy
      · rw [quantileExt_of_ge hy1]; exact (quantile_mem_Icc hT ⟨hx0, hx1⟩).2
    · rw [quantileExt_of_ge hx1, quantileExt_of_ge (hx1.trans hxy)]

/-- **The quantile grid** (Shmalo, Lemma 2.2). If `T` is carried by `[α, α + L]`, the sum of
the `k` grid copies is a.s. within `L` of `k` times the mean of `T`. -/
theorem abs_sum_quantile_fract_sub_le {α L : ℝ} (hT : T (Icc α (α + L))ᶜ = 0) {k : ℕ}
    (hk : 0 < k) : ∀ᵐ w ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      |∑ j ∈ Finset.range k, quantile T (Int.fract (w + j / k)) - k * ∫ x, x ∂T| ≤ L := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hmean : ∫ x, x ∂T = ∫ x in (0 : ℝ)..1, quantileExt T α L x := by
    rw [integral_eq_setIntegral_quantile (f := fun x : ℝ ↦ x) aestronglyMeasurable_id,
      intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo fun p hp ↦ (quantileExt_of_mem hp).symm
  have hnull : ∀ᵐ w ∂(volume.restrict (Ioo (0 : ℝ) 1)), w ∉ range fun m : ℕ ↦ (m : ℝ) / k :=
    ae_restrict_of_ae ((countable_range _).ae_notMem _)
  filter_upwards [hnull, ae_restrict_mem measurableSet_Ioo] with w hw hw'
  obtain ⟨θ, hθ0, hθ1, hsum⟩ :=
    sum_fract_grid hk hw'.1 hw'.2 (fun m hm ↦ hw ⟨m, hm.symm⟩) (quantile T)
  have hgrid : ∑ i ∈ Finset.range k, quantile T ((i + θ) / k) =
      ∑ i ∈ Finset.range k, quantileExt T α L ((i + θ) / k) := by
    refine Finset.sum_congr rfl fun i hi ↦ (quantileExt_of_mem ⟨by positivity, ?_⟩).symm
    have : (i : ℝ) + 1 ≤ k := by exact_mod_cast Finset.mem_range.1 hi
    rw [div_lt_one hk']; linarith
  rw [hsum, hgrid, hmean]
  refine (abs_sum_sub_le_of_monotoneOn (monotoneOn_quantileExt hT) hk hθ0 hθ1).trans_eq ?_
  rw [quantileExt_of_ge le_rfl, quantileExt_of_le le_rfl]; ring

end MathFin
