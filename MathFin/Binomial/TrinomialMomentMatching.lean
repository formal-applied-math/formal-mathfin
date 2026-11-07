/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.BlackScholes.GBMLogMoments
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Order.Interval.Set.Basic

/-!
# Trinomial moment matching for an arbitrary node spacing

One step of a recombining trinomial tree sends a node to three children
`x_k - dx`, `x_k`, `x_k + dx` with weights `p₁, p₂, p₃`. Write `v2` for the one-step
conditional variance and `e = m - x_k` for the offset of the conditional mean `m` from
the central child. Matching mass, mean and variance gives the linear system

    p₁ + p₂ + p₃ = 1,   dx (p₃ - p₁) = e,   dx² (p₃ + p₁) = v2 + e²,

whose determinant is `2 dx³`. For `dx ≠ 0` it has the unique solution

    p₁ = (v2 + e² - e dx) / (2 dx²),   p₂ = 1 - (v2 + e²) / dx²,
    p₃ = (v2 + e² + e dx) / (2 dx²).

These are the general-spacing branch weights transcribed from QuantLib's
`ql/methods/lattices/trinomialtree.cpp`, which applies them whenever a grid-wide floor has
widened the node spacing beyond its natural `√3 v`; at the natural spacing the same source
computes the classical closed form (attributed there to Hull–White and Clewlow), which is
the `dx = √3 v`, `v2 = v²` substitution of the same solution.

## Main definitions

* `trinomialProbDown`: the down weight `(v2 + e² - e dx) / (2 dx²)`.
* `trinomialProbMid`: the central weight `1 - (v2 + e²) / dx²`.
* `trinomialProbUp`: the up weight `(v2 + e² + e dx) / (2 dx²)`.

## Main results

* `trinomialProb_sum`, `trinomialProb_mean`, `trinomialProb_secondMoment`: the mass, mean
  and variance equations that define the weights.
* `trinomialProb_unique`: for `dx ≠ 0` the three-equation system has this solution only.
* `trinomialProb_classical`: at the classical spacing `dx = √3 v`, `v2 = v²` the weights are
  the textbook `(1/6, 2/3, 1/6)` at `e = 0`.
* `trinomialProbDownUp_nonneg_iff`, `trinomialProbMid_nonneg_iff`: the exact non-negativity
  conditions `|e| (dx - |e|) ≤ v2` and `v2 + e² ≤ dx²`.
* `trinomialProb_mem_Icc_of_window`: on the window `dx² ≤ 4 v2 ≤ 3 dx²` every offset
  `|e| ≤ dx / 2` keeps all three weights in `[0, 1]`; `trinomialProb_mem_Icc_classical` is
  the classical-spacing case `dx² = 3 v2`.
* `lattice_variance_lower_bound`, `not_exists_nonneg_lattice_scheme`: every non-negative
  weighting of the lattice `c + dx ℤ` with mean `c + e` has variance at least `e (dx - e)`,
  so no branching scheme on that lattice, with any number of branches, matches a variance
  below it.
* `trinomialProb_bsStep_mean`, `trinomialProb_bsStep_variance`: with the variance and the
  mean offset tied to one step of the Black–Scholes log-price, the weights match the
  log-return's mean and variance (`bsLogReturn_mean`, `bsLogReturn_variance`).

## Scope

The statements are about one-step weights and finitely supported laws on a lattice. Nothing
here is a multi-period tree object, and nothing is claimed about the prices a tree built
from these weights produces or about their convergence; the three `full`-strength
non-negativity statements hold on the window above, and outside it the same formulas
produce signed weights (the tradeoff the transcribed source documents and accepts).

## References

* [The QuantLib contributors, *QuantLib*][QuantLib], `ql/methods/lattices/trinomialtree.cpp`
  (the general-spacing branch weights and the classical closed form, transcribed).
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], ch. 21 (the trinomial tree
  among the basic numerical procedures; the formulas are transcribed from the QuantLib
  source, whose classical branch it attributes to Hull–White and Clewlow).

## Tags

trinomial tree, lattice, moment matching, recombining tree, branch probabilities,
Black–Scholes log-return, MSC 91G60, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

/-- Weight of the down child `x_k - dx`: `(v2 + e² - e dx) / (2 dx²)`. -/
noncomputable def trinomialProbDown (v2 e dx : ℝ) : ℝ := (v2 + e ^ 2 - e * dx) / (2 * dx ^ 2)

/-- Weight of the central child `x_k`: `1 - (v2 + e²) / dx²`. -/
noncomputable def trinomialProbMid (v2 e dx : ℝ) : ℝ := 1 - (v2 + e ^ 2) / dx ^ 2

/-- Weight of the up child `x_k + dx`: `(v2 + e² + e dx) / (2 dx²)`. -/
noncomputable def trinomialProbUp (v2 e dx : ℝ) : ℝ := (v2 + e ^ 2 + e * dx) / (2 * dx ^ 2)

/-- Mass equation: the three trinomial weights sum to one. -/
theorem trinomialProb_sum {v2 e dx : ℝ} (hdx : dx ≠ 0) :
    trinomialProbDown v2 e dx + trinomialProbMid v2 e dx + trinomialProbUp v2 e dx = 1 := by
  unfold trinomialProbDown trinomialProbMid trinomialProbUp
  field_simp
  ring

/-- First-moment equation about the central node: `dx (p₃ - p₁) = e`. -/
theorem trinomialProb_mean {v2 e dx : ℝ} (hdx : dx ≠ 0) :
    dx * (trinomialProbUp v2 e dx - trinomialProbDown v2 e dx) = e := by
  unfold trinomialProbDown trinomialProbUp
  field_simp
  ring

/-- Second-moment equation about the central node: `dx² (p₃ + p₁) = v2 + e²`, i.e. the
variance about the mean `x_k + e` is `v2`. -/
theorem trinomialProb_secondMoment {v2 e dx : ℝ} (hdx : dx ≠ 0) :
    dx ^ 2 * (trinomialProbUp v2 e dx + trinomialProbDown v2 e dx) = v2 + e ^ 2 := by
  unfold trinomialProbDown trinomialProbUp
  field_simp
  ring

/-- **Uniqueness.** For `dx ≠ 0`, any weights `(q₁, q₂, q₃)` solving the mass, mean and
second-moment equations are the trinomial weights. -/
theorem trinomialProb_unique {v2 e dx q₁ q₂ q₃ : ℝ} (hdx : dx ≠ 0)
    (hsum : q₁ + q₂ + q₃ = 1) (hmean : dx * (q₃ - q₁) = e)
    (hsec : dx ^ 2 * (q₃ + q₁) = v2 + e ^ 2) :
    q₁ = trinomialProbDown v2 e dx ∧ q₂ = trinomialProbMid v2 e dx ∧
      q₃ = trinomialProbUp v2 e dx := by
  have hdx2 : dx ^ 2 ≠ 0 := pow_ne_zero 2 hdx
  unfold trinomialProbDown trinomialProbMid trinomialProbUp
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    linear_combination hsec - dx * hmean
  · field_simp
    linear_combination dx ^ 2 * hsum - hsec
  · field_simp
    linear_combination hsec + dx * hmean

/-- **Classical spacing.** With `dx = √3 v` and `v2 = v²`, the trinomial weights are the
classical `((1 + e²/v² - √3 e/v)/6, (2 - e²/v²)/3, (1 + e²/v² + √3 e/v)/6)`. -/
theorem trinomialProb_classical {v e : ℝ} (hv : v ≠ 0) :
    trinomialProbDown (v ^ 2) e (√3 * v) = (1 + e ^ 2 / v ^ 2 - √3 * e / v) / 6 ∧
      trinomialProbMid (v ^ 2) e (√3 * v) = (2 - e ^ 2 / v ^ 2) / 3 ∧
      trinomialProbUp (v ^ 2) e (√3 * v) = (1 + e ^ 2 / v ^ 2 + √3 * e / v) / 6 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold trinomialProbDown trinomialProbMid trinomialProbUp
  refine ⟨?_, ?_, ?_⟩ <;> rw [mul_pow, h3] <;> field_simp <;> ring

/-- **Non-negativity of the outer weights.** For `dx > 0`, the down and up weights are both
non-negative iff `|e| (dx - |e|) ≤ v2`. -/
theorem trinomialProbDownUp_nonneg_iff {v2 e dx : ℝ} (hdx : 0 < dx) :
    0 ≤ trinomialProbDown v2 e dx ∧ 0 ≤ trinomialProbUp v2 e dx ↔ |e| * (dx - |e|) ≤ v2 := by
  have hden : 0 < 2 * dx ^ 2 := by positivity
  unfold trinomialProbDown trinomialProbUp
  rw [le_div_iff₀ hden, le_div_iff₀ hden, zero_mul]
  rcases abs_cases e with ⟨he, he0⟩ | ⟨he, he0⟩ <;> rw [he] <;>
    constructor <;> intro h <;> first | nlinarith [h.1, h.2] | constructor <;> nlinarith

/-- **Non-negativity of the central weight.** For `dx ≠ 0`, the central weight is
non-negative iff `v2 + e² ≤ dx²`. -/
theorem trinomialProbMid_nonneg_iff {v2 e dx : ℝ} (hdx : dx ≠ 0) :
    0 ≤ trinomialProbMid v2 e dx ↔ v2 + e ^ 2 ≤ dx ^ 2 := by
  unfold trinomialProbMid
  rw [sub_nonneg, div_le_one₀ (by positivity)]

/-- **Validity window.** If `dx > 0`, `|e| ≤ dx / 2` and `dx² ≤ 4 v2 ≤ 3 dx²` (that is,
`2v/√3 ≤ dx ≤ 2v` with `v2 = v²`), all three trinomial weights lie in `[0, 1]`. -/
theorem trinomialProb_mem_Icc_of_window {v2 e dx : ℝ} (hdx : 0 < dx) (he : |e| ≤ dx / 2)
    (hlo : dx ^ 2 ≤ 4 * v2) (hhi : 4 * v2 ≤ 3 * dx ^ 2) :
    trinomialProbDown v2 e dx ∈ Set.Icc 0 1 ∧ trinomialProbMid v2 e dx ∈ Set.Icc 0 1 ∧
      trinomialProbUp v2 e dx ∈ Set.Icc 0 1 := by
  have habs : 0 ≤ |e| := abs_nonneg e
  have hsq : e ^ 2 = |e| ^ 2 := (sq_abs e).symm
  obtain ⟨h1, h3⟩ := (trinomialProbDownUp_nonneg_iff hdx).2 (by nlinarith)
  have h2 := (trinomialProbMid_nonneg_iff (v2 := v2) (e := e) hdx.ne').2 (by nlinarith)
  have hs := trinomialProb_sum (v2 := v2) (e := e) hdx.ne'
  exact ⟨⟨h1, by linarith⟩, ⟨h2, by linarith⟩, ⟨h3, by linarith⟩⟩

/-- **Classical spacing is valid.** With `dx² = 3 v2` and the nearest-node offset
`|e| ≤ dx / 2`, all three weights lie in `[0, 1]`. This is the condition behind the
transcribed source's check that the unfloored three-branch weights are non-negative. -/
theorem trinomialProb_mem_Icc_classical {v2 e dx : ℝ} (hdx : 0 < dx) (he : |e| ≤ dx / 2)
    (hcl : dx ^ 2 = 3 * v2) :
    trinomialProbDown v2 e dx ∈ Set.Icc 0 1 ∧ trinomialProbMid v2 e dx ∈ Set.Icc 0 1 ∧
      trinomialProbUp v2 e dx ∈ Set.Icc 0 1 :=
  trinomialProb_mem_Icc_of_window hdx he (by nlinarith [sq_nonneg dx])
    (by nlinarith [sq_nonneg dx])

/-- **Lattice variance bound.** Let `w ≥ 0` be weights summing to one on finitely many
points `c + dx n` (`n ∈ s ⊆ ℤ`) of the lattice `c + dx ℤ`, with mean `c + e`. Then the
variance is at least `e (dx - e)`.

The bound is informative when `0 < e < dx`, i.e. when `c` is the lattice point just below
the mean. The proof uses only that `n (n - 1) ≥ 0` for every integer `n`: no lattice point
lies strictly between `c` and `c + dx`. The statement is about finitely supported laws on
the lattice, not about tree prices. -/
theorem lattice_variance_lower_bound {c dx e : ℝ} (s : Finset ℤ) (w : ℤ → ℝ)
    (hw : ∀ n ∈ s, 0 ≤ w n) (hsum : ∑ n ∈ s, w n = 1)
    (hmean : ∑ n ∈ s, w n * (c + dx * n) = c + e) :
    e * (dx - e) ≤ ∑ n ∈ s, w n * (c + dx * n - (c + e)) ^ 2 := by
  have hkey : 0 ≤ ∑ n ∈ s, w n * (dx * n * (dx * n - dx)) := by
    refine Finset.sum_nonneg fun n hn => mul_nonneg (hw n hn) ?_
    have hint : (0 : ℤ) ≤ n * (n - 1) := by
      rcases le_or_gt n 0 with h | h <;> nlinarith
    have hreal : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by exact_mod_cast hint
    have : dx * n * (dx * n - dx) = dx ^ 2 * ((n : ℝ) * ((n : ℝ) - 1)) := by ring
    rw [this]
    positivity
  have hsplit : ∑ n ∈ s, w n * (c + dx * n - (c + e)) ^ 2 =
      ∑ n ∈ s, w n * (dx * n * (dx * n - dx)) + (dx - 2 * e) * ∑ n ∈ s, w n * (c + dx * n) +
        (e ^ 2 - (dx - 2 * e) * c) * ∑ n ∈ s, w n := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hsplit, hmean, hsum]
  nlinarith

/-- **No non-negative lattice scheme matches a small variance.** If `v2 < e (dx - e)`, there
are no non-negative weights, on any finite set of points of the lattice `c + dx ℤ`, with
total mass one, mean `c + e` and variance `v2`. Combined with
`trinomialProbDownUp_nonneg_iff`, this says that whenever the three-branch weights have a
negative entry because `v2 < |e| (dx - |e|)`, every other branching on the same lattice
has one too (measure `e` from the lattice point just below the mean). -/
theorem not_exists_nonneg_lattice_scheme {c dx e v2 : ℝ} (hv : v2 < e * (dx - e)) :
    ¬ ∃ (s : Finset ℤ) (w : ℤ → ℝ), (∀ n ∈ s, 0 ≤ w n) ∧ ∑ n ∈ s, w n = 1 ∧
      ∑ n ∈ s, w n * (c + dx * n) = c + e ∧
      ∑ n ∈ s, w n * (c + dx * n - (c + e)) ^ 2 = v2 := by
  rintro ⟨s, w, hw, hsum, hmean, hvar⟩
  have := lattice_variance_lower_bound s w hw hsum hmean
  linarith

/-! ### One step of the Black–Scholes log-price

The weights' purpose is to discretize a diffusion's one-step first two moments. The
Black–Scholes log-return over a step of length `dt` has mean `(r - σ²/2) dt` and variance
`σ² dt` under the risk-neutral measure (`bsLogReturn_mean`, `bsLogReturn_variance` in
`MathFin/BlackScholes/GBMLogMoments.lean`). At the classical spacing `dx = √3 σ √dt` the
variance sits at the top of the validity window `dx² ≤ 4 v2 ≤ 3 dx²`, so
`trinomialProb_mem_Icc_classical` keeps the weights in `[0, 1]` for every nearest-node
offset; the two theorems below record that the weights then match the log-return's two
moments exactly. -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q]
  {S_0 K r σ dt : ℝ} {Z : Ω → ℝ}

/-- **The trinomial step matches the Black–Scholes log-return's mean.** Under the
Black–Scholes hypothesis over a step `dt`, with the classical spacing `dx = √3 σ √dt` and a
lattice anchor-offset pair `(c, e)` for the risk-neutral log-drift (`c + e =
(r - σ²/2) dt`), the lattice law's mean `c + dx (p₃ - p₁)` equals the log-return's mean
`E[bsLogReturn r σ dt Z]`. -/
theorem trinomialProb_bsStep_mean (h : BSCallHyp Q S_0 K r σ dt Z) (c e : ℝ)
    (he : c + e = (r - σ ^ 2 / 2) * dt) :
    c + (√3 * σ * Real.sqrt dt) *
        (trinomialProbUp (σ ^ 2 * dt) e (√3 * σ * Real.sqrt dt) -
          trinomialProbDown (σ ^ 2 * dt) e (√3 * σ * Real.sqrt dt))
      = ∫ ω, bsLogReturn r σ dt (Z ω) ∂Q := by
  have hdx : √3 * σ * Real.sqrt dt ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by positivity) h.σ_pos.ne')
      (Real.sqrt_pos.mpr h.T_pos).ne'
  rw [bsLogReturn_mean h, ← he, trinomialProb_mean hdx]

/-- **The trinomial step matches the Black–Scholes log-return's variance.** Under the
Black–Scholes hypothesis over a step `dt`, with the classical spacing `dx = √3 σ √dt` and
variance parameter `v2 = σ² dt`, the lattice law's variance about its mean,
`dx² (p₃ + p₁) - e²`, equals the log-return's variance `Var[bsLogReturn r σ dt Z] = σ² dt`
— the offset `e` cancels, so the identity holds for every offset `e`. -/
theorem trinomialProb_bsStep_variance (h : BSCallHyp Q S_0 K r σ dt Z) (e : ℝ) :
    (√3 * σ * Real.sqrt dt) ^ 2 *
        (trinomialProbUp (σ ^ 2 * dt) e (√3 * σ * Real.sqrt dt) +
          trinomialProbDown (σ ^ 2 * dt) e (√3 * σ * Real.sqrt dt)) - e ^ 2
      = Var[fun ω ↦ bsLogReturn r σ dt (Z ω); Q] := by
  have hdx : √3 * σ * Real.sqrt dt ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by positivity) h.σ_pos.ne')
      (Real.sqrt_pos.mpr h.T_pos).ne'
  rw [bsLogReturn_variance h, trinomialProb_secondMoment hdx]
  ring

end MathFin
