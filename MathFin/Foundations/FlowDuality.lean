/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib

/-!
# Flow duality for the constant-coefficient weak forward equation

A probability-measure flow `ρ : ℝ → Measure ℝ` satisfying the integrated weak
forward equation with constant drift `b` and variance `v > 0`,

`∫ f dρ s = ∫ f dρ 0 + ∫ r in 0..s, (b · ∫ f' dρ r + v/2 · ∫ f'' dρ r) dr`

for every test with three uniformly bounded derivatives (and the test itself
bounded), is **determined by its initial law**: two such flows with
`ρ 0 = η 0` coincide at every positive time (`weakForwardUniqueConst`).

The proof pairs each flow against the *explicit adjoint solutions* of the
backward equation `∂_s u + b u' + (v/2) u'' = 0`: for a frequency `ξ`, the real
and imaginary parts of `e^{iξx + (iξb − ξ²v/2)(t−s)}` (`adjRe`, `adjIm`). The
pairing `F(s) = ⟨adjRe(s,·), ρ s⟩` is conserved: the increment over `[s₀, s]`
splits at the frozen pair `(adjRe(s₀,·), ρ s)` into a flow part (the integrated
identity at the frozen test) and a parameter part (differentiating the adjoint
at the frozen measure), and the two averages tend to matching limits whose
generator terms cancel by the backward equation. Conservation at every
frequency, the terminal identification `adjRe(t,·) = cos(ξ·)`, and
`MeasureTheory.Measure.ext_of_charFun` give weak uniqueness.

Two disclosed strengthenings of the hypothesis shape (relative to the
Gyongy-mimicry gate this module is aimed at): the test class also bounds the
test function itself (making every pairing well-defined against a probability
measure), and the identity carries the interval-integrability of the pairing
integrand (automatic when the pairing maps are continuous, e.g. for flows built
from Itô processes).
-/

@[expose] public section

namespace MathFin

open MeasureTheory

/-- A probability-measure flow on `[0, T]` satisfying the integrated weak
forward equation with constant drift `b` and variance `v`, for every test with
three uniformly bounded derivatives (the test itself bounded too), together
with the interval-integrability of the pairing integrand. -/
def IsWeakForwardFlow (b v T : ℝ) (ρ : ℝ → Measure ℝ) : Prop :=
  (∀ s, IsProbabilityMeasure (ρ s)) ∧
  ∀ (f f' f'' f''' : ℝ → ℝ) (C0 C1 C2 C3 : ℝ),
    (∀ x, HasDerivAt f (f' x) x) → (∀ x, HasDerivAt f' (f'' x) x) →
    (∀ x, HasDerivAt f'' (f''' x) x) →
    (∀ x, |f x| ≤ C0) → (∀ x, |f' x| ≤ C1) → (∀ x, |f'' x| ≤ C2) →
    (∀ x, |f''' x| ≤ C3) →
    ∀ s ∈ Set.Ioc 0 T,
      (∫ y, f y ∂(ρ s) = ∫ y, f y ∂(ρ 0)
        + ∫ r in (0)..s,
          (b * ∫ y, f' y ∂(ρ r) + v / 2 * ∫ y, f'' y ∂(ρ r))) ∧
      IntervalIntegrable
        (fun r => b * ∫ y, f' y ∂(ρ r) + v / 2 * ∫ y, f'' y ∂(ρ r)) volume 0 s

/-! ### The explicit adjoint solutions

`adjRe b v ξ t s x` and `adjIm b v ξ t s x` are the real and imaginary parts of
`e^{iξx + (iξb − ξ²v/2)(t−s)}`: for each `s ≤ t`, functions of `x` with
terminal data `cos(ξ·)` resp. `sin(ξ·)` at `s = t`, solving the backward
equation `∂_s u + b u' + (v/2) u'' = 0` pointwise, with all `x`-derivatives
uniformly bounded by the corresponding power of `|ξ|`. -/

/-- The real part of the constant-coefficient adjoint solution with terminal
data `cos(ξ·)` at time `t`. -/
noncomputable def adjRe (b v ξ t s x : ℝ) : ℝ :=
  Real.exp (-(ξ ^ 2 * v / 2) * (t - s)) * Real.cos (ξ * (x + b * (t - s)))

/-- The imaginary part of the constant-coefficient adjoint solution with
terminal data `sin(ξ·)` at time `t`. -/
noncomputable def adjIm (b v ξ t s x : ℝ) : ℝ :=
  Real.exp (-(ξ ^ 2 * v / 2) * (t - s)) * Real.sin (ξ * (x + b * (t - s)))

lemma adjRe_terminal (b v ξ t x : ℝ) : adjRe b v ξ t t x = Real.cos (ξ * x) := by
  simp [adjRe]

lemma adjIm_terminal (b v ξ t x : ℝ) : adjIm b v ξ t t x = Real.sin (ξ * x) := by
  simp [adjIm]

/-- First `x`-derivative of `adjRe`: `−ξ` times `adjIm`. -/
lemma hasDerivAt_adjRe_x (b v ξ t s x : ℝ) :
    HasDerivAt (fun x => adjRe b v ξ t s x) (-ξ * adjIm b v ξ t s x) x := by
  have hin : HasDerivAt (fun y => ξ * (y + b * (t - s))) ξ x := by
    simpa using ((hasDerivAt_id x).add (hasDerivAt_const x (b * (t - s)))).const_mul ξ
  have hs : HasDerivAt (fun y => Real.cos (ξ * (y + b * (t - s))))
      (-(Real.sin (ξ * (x + b * (t - s)))) * ξ) x := (Real.hasDerivAt_cos _).comp x hin
  have he : HasDerivAt (fun y => Real.exp (-(ξ ^ 2 * v / 2) * (t - s))) 0 x :=
    hasDerivAt_const _ _
  have hraw := he.mul hs
  have hfeq : ((fun y => Real.exp (-(ξ ^ 2 * v / 2) * (t - s))) *
      (fun y => Real.cos (ξ * (y + b * (t - s)))))
      = fun y => adjRe b v ξ t s y := by
    funext z; simp [Pi.mul_apply, adjRe]
  rw [hfeq] at hraw
  have hder : (0 * Real.cos (ξ * (x + b * (t - s))) +
      Real.exp (-(ξ ^ 2 * v / 2) * (t - s)) *
        (-(Real.sin (ξ * (x + b * (t - s)))) * ξ))
      = -ξ * adjIm b v ξ t s x := by
    simp [adjIm]; ring
  rw [hder] at hraw
  exact hraw

/-- First `x`-derivative of `adjIm`: `ξ` times `adjRe`. -/
lemma hasDerivAt_adjIm_x (b v ξ t s x : ℝ) :
    HasDerivAt (fun x => adjIm b v ξ t s x) (ξ * adjRe b v ξ t s x) x := by
  have hin : HasDerivAt (fun y => ξ * (y + b * (t - s))) ξ x := by
    simpa using ((hasDerivAt_id x).add (hasDerivAt_const x (b * (t - s)))).const_mul ξ
  have hs : HasDerivAt (fun y => Real.sin (ξ * (y + b * (t - s))))
      (Real.cos (ξ * (x + b * (t - s))) * ξ) x := (Real.hasDerivAt_sin _).comp x hin
  have he : HasDerivAt (fun y => Real.exp (-(ξ ^ 2 * v / 2) * (t - s))) 0 x :=
    hasDerivAt_const _ _
  have hraw := he.mul hs
  have hfeq : ((fun y => Real.exp (-(ξ ^ 2 * v / 2) * (t - s))) *
      (fun y => Real.sin (ξ * (y + b * (t - s)))))
      = fun y => adjIm b v ξ t s y := by
    funext z; simp [Pi.mul_apply, adjIm]
  rw [hfeq] at hraw
  have hder : (0 * Real.sin (ξ * (x + b * (t - s))) +
      Real.exp (-(ξ ^ 2 * v / 2) * (t - s)) *
        (Real.cos (ξ * (x + b * (t - s))) * ξ))
      = ξ * adjRe b v ξ t s x := by
    simp [adjRe]; ring
  rw [hder] at hraw
  exact hraw

/-- Second `x`-derivative link for `adjRe`: the derivative function `−ξ · adjIm`
has derivative `−ξ² · adjRe`. -/
lemma hasDerivAt_adjRe' (b v ξ t s x : ℝ) :
    HasDerivAt (fun x => -ξ * adjIm b v ξ t s x) (-ξ ^ 2 * adjRe b v ξ t s x) x :=
  HasDerivAt.congr_deriv
    (HasDerivAt.const_mul (-ξ) (hasDerivAt_adjIm_x b v ξ t s x)) (by ring)

/-- Second `x`-derivative link for `adjIm`. -/
lemma hasDerivAt_adjIm' (b v ξ t s x : ℝ) :
    HasDerivAt (fun x => ξ * adjRe b v ξ t s x) (-ξ ^ 2 * adjIm b v ξ t s x) x :=
  HasDerivAt.congr_deriv
    (HasDerivAt.const_mul ξ (hasDerivAt_adjRe_x b v ξ t s x)) (by ring)

/-- Third `x`-derivative link for `adjRe`. -/
lemma hasDerivAt_adjRe'' (b v ξ t s x : ℝ) :
    HasDerivAt (fun x => -ξ ^ 2 * adjRe b v ξ t s x) (ξ ^ 3 * adjIm b v ξ t s x) x :=
  HasDerivAt.congr_deriv
    (HasDerivAt.const_mul (-ξ ^ 2) (hasDerivAt_adjRe_x b v ξ t s x)) (by ring)

/-- Third `x`-derivative link for `adjIm`. -/
lemma hasDerivAt_adjIm'' (b v ξ t s x : ℝ) :
    HasDerivAt (fun x => ξ ^ 2 * adjIm b v ξ t s x) (ξ ^ 3 * adjRe b v ξ t s x) x :=
  HasDerivAt.congr_deriv
    (HasDerivAt.const_mul (ξ ^ 2) (hasDerivAt_adjIm_x b v ξ t s x)) (by ring)

/-- The drift-generator image of `adjRe(s,·)`: `b u' + (v/2) u'' = −∂_s u`. -/
lemma linAdjRe (b v ξ t s x : ℝ) :
    b * (-ξ * adjIm b v ξ t s x) + v / 2 * (-ξ ^ 2 * adjRe b v ξ t s x)
      = -((ξ ^ 2 * v / 2) * adjRe b v ξ t s x + ξ * b * adjIm b v ξ t s x) := by
  ring

/-- The drift-generator image of `adjIm(s,·)`. -/
lemma linAdjIm (b v ξ t s x : ℝ) :
    b * (ξ * adjRe b v ξ t s x) + v / 2 * (-ξ ^ 2 * adjIm b v ξ t s x)
      = -((ξ ^ 2 * v / 2) * adjIm b v ξ t s x - ξ * b * adjRe b v ξ t s x) := by
  ring

/-- The `s`-derivative of `adjRe`. -/
lemma hasDerivAt_adjRe_s (b v ξ t x s : ℝ) :
    HasDerivAt (fun s => adjRe b v ξ t s x)
      ((ξ ^ 2 * v / 2) * adjRe b v ξ t s x + ξ * b * adjIm b v ξ t s x) s := by
  have he : HasDerivAt (fun s => Real.exp (-(ξ ^ 2 * v / 2) * (t - s)))
      (Real.exp (-(ξ ^ 2 * v / 2) * (t - s)) * (ξ ^ 2 * v / 2)) s := by
    have h1 : HasDerivAt (fun s => -(ξ ^ 2 * v / 2) * (t - s)) (ξ ^ 2 * v / 2) s := by
      simpa using ((hasDerivAt_const s t).sub (hasDerivAt_id s)).const_mul (-(ξ ^ 2 * v / 2))
    simpa using h1.exp
  have hin : HasDerivAt (fun s => ξ * (x + b * (t - s))) (-ξ * b) s := by
    have h2 : HasDerivAt (fun s => b * (t - s)) (-b) s := by
      simpa [Pi.sub_apply] using
        HasDerivAt.const_mul b ((hasDerivAt_const s t).sub (hasDerivAt_id s))
    have h3 := (hasDerivAt_const s x).add h2
    have h4 : HasDerivAt (fun s => x + b * (t - s)) (0 + -b) s := by
      refine h3.congr_of_eventuallyEq (Eq.eventuallyEq ?_)
      funext z; simp [Pi.add_apply]
    simpa using h4.const_mul ξ
  have hs : HasDerivAt (fun s => Real.cos (ξ * (x + b * (t - s))))
      (-(Real.sin (ξ * (x + b * (t - s)))) * (-ξ * b)) s := (Real.hasDerivAt_cos _).comp s hin
  have hraw := he.mul hs
  have hfeq : ((fun s => Real.exp (-(ξ ^ 2 * v / 2) * (t - s))) *
      (fun s => Real.cos (ξ * (x + b * (t - s)))))
      = fun s => adjRe b v ξ t s x := by
    funext z; simp [Pi.mul_apply, adjRe]
  rw [hfeq] at hraw
  have hder : (Real.exp (-(ξ ^ 2 * v / 2) * (t - s)) * (ξ ^ 2 * v / 2) *
      Real.cos (ξ * (x + b * (t - s))) + Real.exp (-(ξ ^ 2 * v / 2) * (t - s)) *
        (-(Real.sin (ξ * (x + b * (t - s)))) * (-ξ * b)))
      = (ξ ^ 2 * v / 2) * adjRe b v ξ t s x + ξ * b * adjIm b v ξ t s x := by
    simp [adjRe, adjIm]; ring
  rw [hder] at hraw
  exact hraw

/-- The `s`-derivative of `adjIm`. -/
lemma hasDerivAt_adjIm_s (b v ξ t x s : ℝ) :
    HasDerivAt (fun s => adjIm b v ξ t s x)
      ((ξ ^ 2 * v / 2) * adjIm b v ξ t s x - ξ * b * adjRe b v ξ t s x) s := by
  have he : HasDerivAt (fun s => Real.exp (-(ξ ^ 2 * v / 2) * (t - s)))
      (Real.exp (-(ξ ^ 2 * v / 2) * (t - s)) * (ξ ^ 2 * v / 2)) s := by
    have h1 : HasDerivAt (fun s => -(ξ ^ 2 * v / 2) * (t - s)) (ξ ^ 2 * v / 2) s := by
      simpa using ((hasDerivAt_const s t).sub (hasDerivAt_id s)).const_mul (-(ξ ^ 2 * v / 2))
    simpa using h1.exp
  have hin : HasDerivAt (fun s => ξ * (x + b * (t - s))) (-ξ * b) s := by
    have h2 : HasDerivAt (fun s => b * (t - s)) (-b) s := by
      simpa [Pi.sub_apply] using
        HasDerivAt.const_mul b ((hasDerivAt_const s t).sub (hasDerivAt_id s))
    have h3 := (hasDerivAt_const s x).add h2
    have h4 : HasDerivAt (fun s => x + b * (t - s)) (0 + -b) s := by
      refine h3.congr_of_eventuallyEq (Eq.eventuallyEq ?_)
      funext z; simp [Pi.add_apply]
    simpa using h4.const_mul ξ
  have hs : HasDerivAt (fun s => Real.sin (ξ * (x + b * (t - s))))
      (Real.cos (ξ * (x + b * (t - s))) * (-ξ * b)) s := (Real.hasDerivAt_sin _).comp s hin
  have hraw := he.mul hs
  have hfeq : ((fun s => Real.exp (-(ξ ^ 2 * v / 2) * (t - s))) *
      (fun s => Real.sin (ξ * (x + b * (t - s)))))
      = fun s => adjIm b v ξ t s x := by
    funext z; simp [Pi.mul_apply, adjIm]
  rw [hfeq] at hraw
  have hder : (Real.exp (-(ξ ^ 2 * v / 2) * (t - s)) * (ξ ^ 2 * v / 2) *
      Real.sin (ξ * (x + b * (t - s))) + Real.exp (-(ξ ^ 2 * v / 2) * (t - s)) *
        (Real.cos (ξ * (x + b * (t - s))) * (-ξ * b)))
      = (ξ ^ 2 * v / 2) * adjIm b v ξ t s x - ξ * b * adjRe b v ξ t s x := by
    simp [adjRe, adjIm]; ring
  rw [hder] at hraw
  exact hraw

/-! ### Sup bounds (on the backward cone `s ≤ t`, `v > 0`) -/

lemma abs_adjRe_le {b v ξ t s x : ℝ} (hv : 0 < v) (hst : s ≤ t) :
    |adjRe b v ξ t s x| ≤ 1 := by
  have h2 : (0:ℝ) ≤ ξ ^ 2 * v / 2 := by positivity
  have h3 : (0:ℝ) ≤ t - s := sub_nonneg.mpr hst
  have hexp0 : 0 ≤ Real.exp (-(ξ ^ 2 * v / 2) * (t - s)) := Real.exp_nonneg _
  have hbound : |Real.exp (-(ξ ^ 2 * v / 2) * (t - s)) *
      Real.cos (ξ * (x + b * (t - s)))| ≤
      Real.exp (-(ξ ^ 2 * v / 2) * (t - s)) := by
    rw [abs_mul, abs_of_nonneg hexp0]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hexp0).trans_eq (by simp)
  have hexple : Real.exp (-(ξ ^ 2 * v / 2) * (t - s)) ≤ 1 := by
    rw [← Real.exp_zero]
    refine Real.exp_le_exp.mpr ?_
    have hneg : -(ξ ^ 2 * v / 2) ≤ 0 := neg_nonpos.mpr h2
    have havg := mul_le_mul_of_nonneg_right hneg h3
    simpa using havg
  rw [adjRe]
  linarith [hbound, hexple]


/-! ### The pairing layer

Against a probability measure, the pairing with a bounded measurable function
is bounded by the sup bound; the integrated identity then makes every
admissible pairing Lipschitz-continuous in time. -/

/-- The pairing of a bounded measurable function against a probability measure
is bounded by the sup bound. -/
lemma abs_pairing_le {μ : Measure ℝ} (hμ : IsProbabilityMeasure μ) {g : ℝ → ℝ} {C : ℝ}
    (hmeas : Measurable g) (hg : ∀ x, |g x| ≤ C) : |∫ y, g y ∂μ| ≤ C := by
  have h1 : |∫ y, g y ∂μ| ≤ ∫ y, |g y| ∂μ := abs_integral_le_integral_abs
  have h2 : ∫ y, |g y| ∂μ ≤ ∫ y, C ∂μ := by
    have hm1 : Measurable (fun y => |g y| : ℝ → ℝ) := Measurable.abs hmeas
    refine integral_mono_of_nonneg (ae_of_all μ (fun x => abs_nonneg (g x)))
      (integrable_const C) (ae_of_all μ hg)
  rw [integral_const] at h2
  simp at h2
  linarith [h1, h2]

/-- The increment of an admissible pairing over an interval, both endpoints in
`[0, T]`: the difference of pairings is the oriented integral of the pairing
integrand. -/
lemma pairing_increment {b v T : ℝ} {ρ : ℝ → Measure ℝ} (hρ : IsWeakForwardFlow b v T ρ)
    {g g' g'' g''' : ℝ → ℝ} {C0 C1 C2 C3 : ℝ}
    (h1 : ∀ x, HasDerivAt g (g' x) x) (h2 : ∀ x, HasDerivAt g' (g'' x) x)
    (h3 : ∀ x, HasDerivAt g'' (g''' x) x)
    (h0 : ∀ x, |g x| ≤ C0) (hb1 : ∀ x, |g' x| ≤ C1) (hb2 : ∀ x, |g'' x| ≤ C2)
    (hb3 : ∀ x, |g''' x| ≤ C3)
    {s₀ s : ℝ} (hs₀ : s₀ ∈ Set.Icc 0 T) (hs : s ∈ Set.Icc 0 T) :
    ∫ y, g y ∂(ρ s) - ∫ y, g y ∂(ρ s₀)
      = ∫ r in s₀..s, (b * ∫ y, g' y ∂(ρ r) + v / 2 * ∫ y, g'' y ∂(ρ r)) := by
  obtain ⟨hprob, hident⟩ := hρ
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x ↦ (h1 x).continuousAt
  have hg'c : Continuous g' := continuous_iff_continuousAt.mpr fun x ↦ (h2 x).continuousAt
  have hg''c : Continuous g'' := continuous_iff_continuousAt.mpr fun x ↦ (h3 x).continuousAt
  set w : ℝ → ℝ := fun r => b * ∫ y, g' y ∂(ρ r) + v / 2 * ∫ y, g'' y ∂(ρ r) with hw
  have ident : ∀ u ∈ Set.Ioc 0 T,
      ∫ y, g y ∂(ρ u) = ∫ y, g y ∂(ρ 0) + ∫ r in (0)..u, w r ∧
      IntervalIntegrable w volume 0 u := fun u hu =>
    hident g g' g'' g''' C0 C1 C2 C3 h1 h2 h3 h0 hb1 hb2 hb3 u hu
  have interior : ∀ {u₁ u₂ : ℝ}, 0 < u₁ → 0 < u₂ → u₁ ≤ T → u₂ ≤ T →
      ∫ y, g y ∂(ρ u₂) - ∫ y, g y ∂(ρ u₁) = ∫ r in u₁..u₂, w r := by
    intro u₁ u₂ hu₁ hu₂ hu₁T hu₂T
    have hI1 := ident u₁ ⟨hu₁, hu₁T⟩
    have hI2 := ident u₂ ⟨hu₂, hu₂T⟩
    rcases le_total u₂ u₁ with hle | hle
    · have hsub : IntervalIntegrable w volume u₂ u₁ := hI1.2.mono_set
        (Set.uIcc_subset_uIcc (Set.mem_uIcc_of_le (le_of_lt hu₂) hle)
          (Set.mem_uIcc_of_le (le_of_lt hu₁) le_rfl))
      have hadd := intervalIntegral.integral_add_adjacent_intervals hI2.2 hsub
      rw [hI2.1, hI1.1, ← hadd, intervalIntegral.integral_symm u₂ u₁]
      ring
    · have hsub : IntervalIntegrable w volume u₁ u₂ := hI2.2.mono_set
        (Set.uIcc_subset_uIcc (Set.mem_uIcc_of_le (le_of_lt hu₁) hle)
          (Set.mem_uIcc_of_le (le_of_lt hu₂) le_rfl))
      have hadd := intervalIntegral.integral_add_adjacent_intervals hI1.2 hsub
      rw [hI2.1, hI1.1, ← hadd]
      ring
  rcases eq_or_lt_of_le hs₀.1 with h0 | h0pos
  · subst h0
    rcases eq_or_lt_of_le hs.1 with h1eq | h1pos
    · subst h1eq; rw [sub_self, intervalIntegral.integral_same]
    · linarith [(ident s ⟨h1pos, hs.2⟩).1]
  · rcases eq_or_lt_of_le hs.1 with h1eq | h1pos
    · subst h1eq
      have hI1 := ident s₀ ⟨h0pos, hs₀.2⟩
      have hsym : (∫ r in s₀..(0:ℝ), w r) = -(∫ r in (0)..s₀, w r) :=
        intervalIntegral.integral_symm 0 s₀
      rw [hI1.1, hsym]
      ring
    · exact interior h0pos h1pos hs₀.2 hs.2

end MathFin
