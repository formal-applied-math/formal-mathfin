/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun, Raphael Coelho
-/
module

public import MathFin.Risk.ExpectedShortfall

/-!
# The stop-loss transform across a gap in the law

The stop-loss transform `c ↦ E[(S − c)⁺]` of a loss `S` falls at rate `P(S > c)` just to the right
of `c`. Where the law of `S` puts no mass strictly inside `(c, c + h)` it falls at that rate all the
way to `c + h`: the values at the two ends differ by exactly `h · P(S > c)`,

  `E[(S − (c + h))⁺] = E[(S − c)⁺] − h · P(S > c)`.

On an arithmetic loss, `S ∈ hℤ` almost surely (aggregate claims on a monetary unit `h`, the
setting of Panjer's recursion), every interval `(jh, (j + 1)h)` is such a gap, and the identity is
the recursion that computes stop-loss premiums at the lattice retentions from the tail
probabilities. Through the Rockafellar–Uryasev objective `c + (1 − α)⁻¹E[(S − c)⁺]`, whose least
value is expected shortfall for `α ∈ (0, 1)` (`isLeast_rockafellarUryasev`), it gives the
objective's increment over each gap, `h · (1 − (1 − α)⁻¹ P(S > c))`. The statements take a finite
measure `P` and write `P(S > c)` for `P.real {c < S}`; it is a probability when `P` is one.

## Main results

* `integral_max_sub_add_of_gap`: if `S` has no mass in `(c, c + h)` and `0 ≤ h`, then
  `E[(S − (c + h))⁺] = E[(S − c)⁺] − h · P(S > c)`.
* `ae_notMem_Ioo_of_lattice`: an arithmetic loss `S ∈ hℤ` has no mass inside a lattice cell.
* `integral_max_sub_succ_mul_of_lattice`: for `S ∈ hℤ` almost surely, the stop-loss recursion
  `E[(S − (j + 1)h)⁺] = E[(S − jh)⁺] − h · P(S > jh)`.
* `rockafellarUryasev_add_of_gap`: across a gap, the Rockafellar–Uryasev objective increases by
  `h · (1 − (1 − α)⁻¹ P(S > c))`.
* `isLeast_rockafellarUryasev_lattice`: for an arithmetic loss, expected shortfall is the least
  Rockafellar–Uryasev value over the lattice points, which the recursion computes.

## References

* [S. A. Klugman, H. H. Panjer and G. E. Willmot, *Loss Models*][KlugmanPanjerWillmot],
  Chapter 9 (aggregate loss models: stop-loss premiums of arithmetic distributions)
* [R. T. Rockafellar and S. Uryasev, *Conditional value-at-risk for general loss
  distributions*][RockafellarUryasev2002]

## Tags

stop-loss premium, stop-loss transform, arithmetic distribution, aggregate claims, retention,
Rockafellar–Uryasev, expected shortfall, MSC 91G05, MSC 91G70, JEL G22, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {S : Ω → ℝ}

/-- **The stop-loss transform is affine across a gap in the law.** If the loss `S` takes no value
strictly between `c` and `c + h` (almost surely) and `0 ≤ h`, then
`E[(S − (c + h))⁺] = E[(S − c)⁺] − h · P(S > c)`: above the gap both payoffs differ by `h`, below
it both vanish. -/
theorem integral_max_sub_add_of_gap (hSm : Measurable S) (hS : Integrable S P) {c h : ℝ}
    (hh : 0 ≤ h) (hgap : ∀ᵐ ω ∂P, S ω ∉ Set.Ioo c (c + h)) :
    ∫ ω, max (S ω - (c + h)) 0 ∂P = ∫ ω, max (S ω - c) 0 ∂P - h * P.real {ω | c < S ω} := by
  have hm : MeasurableSet {ω | c < S ω} := measurableSet_lt measurable_const hSm
  have hi : Integrable (fun ω ↦ max (S ω - c) 0) P :=
    (hS.sub (integrable_const c)).sup (integrable_const 0)
  have hpt : ∀ᵐ ω ∂P, max (S ω - (c + h)) 0 =
      max (S ω - c) 0 - {ω | c < S ω}.indicator (fun _ ↦ h) ω := by
    filter_upwards [hgap] with ω hω
    by_cases hc : c < S ω
    · have : c + h ≤ S ω := not_lt.1 fun h' ↦ hω ⟨hc, h'⟩
      rw [Set.indicator_of_mem (hc : ω ∈ {ω | c < S ω}), max_eq_left (by linarith),
        max_eq_left (by linarith)]
      ring
    · have hc' := not_lt.1 hc
      rw [Set.indicator_of_notMem (hc : ω ∉ {ω | c < S ω}), max_eq_right (by linarith),
        max_eq_right (by linarith), sub_zero]
  rw [integral_congr_ae hpt, integral_sub hi ((integrable_const h).indicator hm),
    integral_indicator hm, setIntegral_const, smul_eq_mul]
  ring

omit [IsFiniteMeasure P] in
/-- **An arithmetic loss has no mass inside a lattice cell**: if `S ∈ hℤ` almost surely and
`0 ≤ h`, then almost surely `S ∉ (jh, jh + h)`. -/
theorem ae_notMem_Ioo_of_lattice {h : ℝ} (hh : 0 ≤ h) (hlat : ∀ᵐ ω ∂P, ∃ n : ℤ, S ω = n * h)
    (j : ℤ) : ∀ᵐ ω ∂P, S ω ∉ Set.Ioo (j * h) (j * h + h) := by
  filter_upwards [hlat] with ω ⟨n, hn⟩ ⟨h1, h2⟩
  rw [hn] at h1 h2
  have h3 : (j : ℝ) < n := lt_of_mul_lt_mul_right h1 hh
  have h4 : (n : ℝ) < j + 1 := lt_of_mul_lt_mul_right (by rwa [add_mul, one_mul]) hh
  have : j < n := by exact_mod_cast h3
  have : n < j + 1 := by exact_mod_cast h4
  omega

/-- **The stop-loss recursion of an arithmetic loss.** If `S ∈ hℤ` almost surely, `0 ≤ h`, then
for every integer retention level `j`,
`E[(S − (j + 1)h)⁺] = E[(S − jh)⁺] − h · P(S > jh)`. -/
theorem integral_max_sub_succ_mul_of_lattice (hSm : Measurable S) (hS : Integrable S P) {h : ℝ}
    (hh : 0 ≤ h) (hlat : ∀ᵐ ω ∂P, ∃ n : ℤ, S ω = n * h) (j : ℤ) :
    ∫ ω, max (S ω - (j + 1) * h) 0 ∂P =
      ∫ ω, max (S ω - j * h) 0 ∂P - h * P.real {ω | j * h < S ω} := by
  rw [add_mul, one_mul]
  exact integral_max_sub_add_of_gap hSm hS hh (ae_notMem_Ioo_of_lattice hh hlat j)

/-- **The Rockafellar–Uryasev objective across a gap.** If `S` takes no value in `(c, c + h)`
and `0 ≤ h`, the objective `c ↦ c + (1 − α)⁻¹E[(S − c)⁺]` (whose least value is expected
shortfall when `α ∈ (0, 1)`) increases by `h · (1 − (1 − α)⁻¹ P(S > c))` from `c` to `c + h`. -/
theorem rockafellarUryasev_add_of_gap (hSm : Measurable S) (hS : Integrable S P) {c h : ℝ}
    (hh : 0 ≤ h) (hgap : ∀ᵐ ω ∂P, S ω ∉ Set.Ioo c (c + h)) (α : ℝ) :
    rockafellarUryasev S P α (c + h) =
      rockafellarUryasev S P α c + h * (1 - (1 - α)⁻¹ * P.real {ω | c < S ω}) := by
  rw [rockafellarUryasev, rockafellarUryasev, integral_max_sub_add_of_gap hSm hS hh hgap]
  ring

omit [IsFiniteMeasure P] in
/-- **Expected shortfall of an arithmetic loss is the least Rockafellar–Uryasev value on the
lattice.** If `S ∈ hℤ` almost surely with `h > 0` and `α ∈ (0, 1)`, then `ES_α(S)` is the least of
`c + (1 − α)⁻¹E[(S − c)⁺]` over the lattice points `c = jh`. Between two lattice points the
objective is affine (`rockafellarUryasev_add_of_gap`), so its least value over the line
(`isLeast_rockafellarUryasev`) is taken at an end of the cell holding a minimiser. -/
theorem isLeast_rockafellarUryasev_lattice [IsProbabilityMeasure P] (hSm : Measurable S)
    (hS : Integrable S P) {h : ℝ} (hh : 0 < h) (hlat : ∀ᵐ ω ∂P, ∃ n : ℤ, S ω = n * h) {α : ℝ}
    (hα : α ∈ Set.Ioo 0 1) :
    IsLeast (Set.range fun j : ℤ ↦ rockafellarUryasev S P α (j * h)) (expectedShortfall S P α) := by
  have hES := isLeast_rockafellarUryasev hS hα
  refine ⟨?_, Set.forall_mem_range.2 fun j ↦ hES.2 ⟨_, rfl⟩⟩
  obtain ⟨c, hc⟩ := hES.1
  set j := ⌊c / h⌋
  have hj : (j : ℝ) * h ≤ c := (le_div_iff₀ hh).1 (Int.floor_le _)
  have hj' : c < (j : ℝ) * h + h := by
    have := (div_lt_iff₀ hh).1 (Int.lt_floor_add_one (c / h))
    rwa [add_mul, one_mul] at this
  have hgap := ae_notMem_Ioo_of_lattice hh.le hlat j
  have hcell := rockafellarUryasev_add_of_gap hSm hS (sub_nonneg.2 hj)
    (hgap.mono fun ω hω h' ↦ hω ⟨h'.1, by linarith [h'.2]⟩) α
  rw [show (j : ℝ) * h + (c - j * h) = c by ring] at hcell
  have hnext := rockafellarUryasev_add_of_gap hSm hS hh.le hgap α
  have h1 := hES.2 ⟨(j : ℝ) * h, rfl⟩
  have h2 := hES.2 ⟨(j : ℝ) * h + h, rfl⟩
  rcases le_or_gt 0 (1 - (1 - α)⁻¹ * P.real {ω | (j : ℝ) * h < S ω}) with hs | hs
  · exact ⟨j, le_antisymm (by nlinarith [mul_nonneg (sub_nonneg.2 hj) hs]) h1⟩
  · refine ⟨j + 1, ?_⟩
    simp only [Int.cast_add, Int.cast_one, add_mul, one_mul]
    have := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ h - (c - j * h) by linarith) hs.le
    exact le_antisymm (by nlinarith) h2

end MathFin
