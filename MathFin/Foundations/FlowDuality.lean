/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib

/-!
# Weak uniqueness for the constant-coefficient forward equation

A probability-measure flow `ρ : ℝ → Measure ℝ` satisfying the integrated weak
forward equation with constant drift `b` and variance `v`,

`∫ f dρ s = ∫ f dρ 0 + ∫ r in 0..s, (b · ∫ f' dρ r + v/2 · ∫ f'' dρ r) dr`

for every test with three uniformly bounded derivatives (and the test itself
bounded), is **determined by its initial law**: two such flows with
`ρ 0 = η 0` coincide at every positive time (`weakForwardUniqueConst`).

The proof pairs each flow against the trigonometric tests `cos(ξ·)`, `sin(ξ·)`
at a fixed frequency `ξ`. These tests have constant-coefficient derivative
chains (`cos' = −ξ sin`, `cos'' = −ξ² cos`, and the twin identities for
`sin`), so the weak forward identity turns the pairing differences
`U s = ⟨cos(ξ·), ρ s⟩ − ⟨cos(ξ·), η s⟩` and `W s = ⟨sin(ξ·), ρ s⟩ − ⟨sin(ξ·),
η s⟩` into a linear Volterra system with `U 0 = W 0 = 0`. A direct Lipschitz
bound (from the pairing identity's bounded integrand) gives continuity of
`U, W`; the one-sided fundamental theorem of calculus then gives their right
derivatives on `[0, T)`, bounded in the `ℝ × ℝ` sup-norm by `K * ‖(U, W)‖` for
a constant `K` depending on `b, v, ξ`; Grönwall's inequality forces `U = W =
0` on `[0, T]`. Since this holds for every frequency `ξ`, the two flows share
the same characteristic function at every time, and
`MeasureTheory.Measure.ext_of_charFun` concludes.

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

/-! ### The pairing layer

Against a probability measure, the pairing with a bounded measurable function
is bounded by the sup bound; the integrated identity then makes every
admissible pairing Lipschitz-continuous in time. -/

/-- The pairing of a bounded measurable function against a probability measure
is bounded by the sup bound. -/
lemma abs_pairing_le {μ : Measure ℝ} (hμ : IsProbabilityMeasure μ) {g : ℝ → ℝ} {C : ℝ}
    (hg : ∀ x, |g x| ≤ C) : |∫ y, g y ∂μ| ≤ C := by
  have h1 : |∫ y, g y ∂μ| ≤ ∫ y, |g y| ∂μ := abs_integral_le_integral_abs
  have h2 : ∫ y, |g y| ∂μ ≤ ∫ y, C ∂μ :=
    integral_mono_of_nonneg (ae_of_all μ (fun x => abs_nonneg (g x)))
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

/-- The pairing of an admissible test is Lipschitz in time on `[0, T]`: the
pairing increment is an interval integral of an integrand bounded by
`|b| * C1 + |v| / 2 * C2` (via `abs_pairing_le` on each of the two pieces). -/
lemma abs_pairing_lipschitz {b v T : ℝ} {ρ : ℝ → Measure ℝ} (hρ : IsWeakForwardFlow b v T ρ)
    {g g' g'' g''' : ℝ → ℝ} {C0 C1 C2 C3 : ℝ}
    (h1 : ∀ x, HasDerivAt g (g' x) x) (h2 : ∀ x, HasDerivAt g' (g'' x) x)
    (h3 : ∀ x, HasDerivAt g'' (g''' x) x)
    (h0 : ∀ x, |g x| ≤ C0) (hb1 : ∀ x, |g' x| ≤ C1) (hb2 : ∀ x, |g'' x| ≤ C2)
    (hb3 : ∀ x, |g''' x| ≤ C3)
    {s₀ s : ℝ} (hs₀ : s₀ ∈ Set.Icc 0 T) (hs : s ∈ Set.Icc 0 T) :
    |∫ y, g y ∂(ρ s) - ∫ y, g y ∂(ρ s₀)| ≤ (|b| * C1 + |v| / 2 * C2) * |s - s₀| := by
  rw [pairing_increment hρ h1 h2 h3 h0 hb1 hb2 hb3 hs₀ hs, ← Real.norm_eq_abs]
  refine intervalIntegral.norm_integral_le_of_norm_le_const (fun r _ => ?_)
  rw [Real.norm_eq_abs]
  have hb1' : |∫ y, g' y ∂(ρ r)| ≤ C1 := abs_pairing_le (hρ.1 r) hb1
  have hb2' : |∫ y, g'' y ∂(ρ r)| ≤ C2 := abs_pairing_le (hρ.1 r) hb2
  have hhalf : |v / 2| = |v| / 2 := by rw [abs_div]; norm_num
  calc |b * ∫ y, g' y ∂(ρ r) + v / 2 * ∫ y, g'' y ∂(ρ r)|
      ≤ |b * ∫ y, g' y ∂(ρ r)| + |v / 2 * ∫ y, g'' y ∂(ρ r)| := abs_add_le _ _
    _ = |b| * |∫ y, g' y ∂(ρ r)| + |v / 2| * |∫ y, g'' y ∂(ρ r)| := by rw [abs_mul, abs_mul]
    _ ≤ |b| * C1 + |v| / 2 * C2 := by
        rw [hhalf]
        exact add_le_add (mul_le_mul_of_nonneg_left hb1' (abs_nonneg b))
          (mul_le_mul_of_nonneg_left hb2' (by positivity))

/-- A function Lipschitz on `[0, T]` (with a known-nonnegative constant) is continuous
there: the `ε`-`δ` argument shared by every Lipschitz-from-a-pairing-identity bound in
this file. -/
private lemma continuousOn_of_lipschitzOn_Icc {f : ℝ → ℝ} {T L : ℝ} (hL0 : 0 ≤ L)
    (hLip : ∀ s₀ s, s₀ ∈ Set.Icc (0 : ℝ) T → s ∈ Set.Icc (0 : ℝ) T →
      |f s - f s₀| ≤ L * |s - s₀|) :
    ContinuousOn f (Set.Icc 0 T) := by
  rw [Metric.continuousOn_iff]
  intro s hs ε hε
  refine ⟨ε / (L + 1), by positivity, fun s₀ hs₀ hdist => ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  calc |f s₀ - f s| ≤ L * |s₀ - s| := hLip s s₀ hs hs₀
    _ ≤ (L + 1) * |s₀ - s| := by nlinarith [abs_nonneg (s₀ - s)]
    _ < (L + 1) * (ε / (L + 1)) := mul_lt_mul_of_pos_left hdist (by positivity)
    _ = ε := by
          have hpos : (0 : ℝ) < L + 1 := by positivity
          field_simp

/-! ### Trigonometric test chains

`cos(ξ·)` and `sin(ξ·)` have constant-coefficient derivative chains: the
generator `b · (·)' + v/2 · (·)''` maps each to a linear combination of the
other, with no new functions appearing — the algebraic fact that drives the
Volterra system in `pairing_cos_sin_eq`. -/

lemma hasDerivAt_cosMul (ξ x : ℝ) :
    HasDerivAt (fun x => Real.cos (ξ * x)) (-ξ * Real.sin (ξ * x)) x := by
  have hlin : HasDerivAt (fun y : ℝ => ξ * y) ξ x := by
    simpa using (hasDerivAt_id x).const_mul ξ
  exact ((Real.hasDerivAt_cos (ξ * x)).comp x hlin).congr_deriv (by ring)

lemma hasDerivAt_negSinMul (ξ x : ℝ) :
    HasDerivAt (fun x => -ξ * Real.sin (ξ * x)) (-ξ ^ 2 * Real.cos (ξ * x)) x := by
  have hlin : HasDerivAt (fun y : ℝ => ξ * y) ξ x := by
    simpa using (hasDerivAt_id x).const_mul ξ
  exact (((Real.hasDerivAt_sin (ξ * x)).comp x hlin).const_mul (-ξ)).congr_deriv (by ring)

lemma hasDerivAt_negCosSqMul (ξ x : ℝ) :
    HasDerivAt (fun x => -ξ ^ 2 * Real.cos (ξ * x)) (ξ ^ 3 * Real.sin (ξ * x)) x := by
  have hlin : HasDerivAt (fun y : ℝ => ξ * y) ξ x := by
    simpa using (hasDerivAt_id x).const_mul ξ
  exact (((Real.hasDerivAt_cos (ξ * x)).comp x hlin).const_mul (-ξ ^ 2)).congr_deriv (by ring)

lemma hasDerivAt_sinMul (ξ x : ℝ) :
    HasDerivAt (fun x => Real.sin (ξ * x)) (ξ * Real.cos (ξ * x)) x := by
  have hlin : HasDerivAt (fun y : ℝ => ξ * y) ξ x := by
    simpa using (hasDerivAt_id x).const_mul ξ
  exact ((Real.hasDerivAt_sin (ξ * x)).comp x hlin).congr_deriv (by ring)

lemma hasDerivAt_cosMulScaled (ξ x : ℝ) :
    HasDerivAt (fun x => ξ * Real.cos (ξ * x)) (-ξ ^ 2 * Real.sin (ξ * x)) x := by
  have hlin : HasDerivAt (fun y : ℝ => ξ * y) ξ x := by
    simpa using (hasDerivAt_id x).const_mul ξ
  exact (((Real.hasDerivAt_cos (ξ * x)).comp x hlin).const_mul ξ).congr_deriv (by ring)

lemma hasDerivAt_negSinSqMul (ξ x : ℝ) :
    HasDerivAt (fun x => -ξ ^ 2 * Real.sin (ξ * x)) (-ξ ^ 3 * Real.cos (ξ * x)) x := by
  have hlin : HasDerivAt (fun y : ℝ => ξ * y) ξ x := by
    simpa using (hasDerivAt_id x).const_mul ξ
  exact (((Real.hasDerivAt_sin (ξ * x)).comp x hlin).const_mul (-ξ ^ 2)).congr_deriv (by ring)

/-- The sup bounds for the `cos(ξ·)` derivative chain, bundled: `C0 = 1`, `C1 = |ξ|`,
`C2 = ξ²`, `C3 = |ξ|³`. -/
private lemma abs_cosChain_bounds (ξ : ℝ) :
    (∀ y : ℝ, |Real.cos (ξ * y)| ≤ 1) ∧ (∀ y : ℝ, |(-ξ) * Real.sin (ξ * y)| ≤ |ξ|) ∧
    (∀ y : ℝ, |(-ξ ^ 2) * Real.cos (ξ * y)| ≤ ξ ^ 2) ∧
    (∀ y : ℝ, |ξ ^ 3 * Real.sin (ξ * y)| ≤ |ξ| ^ 3) := by
  refine ⟨fun y => Real.abs_cos_le_one _, fun y => ?_, fun y => ?_, fun y => ?_⟩
  · rw [abs_mul]; simpa using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg ξ)
  · rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg ξ)]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (sq_nonneg ξ)).trans_eq (mul_one _)
  · rw [abs_mul, abs_pow]
    exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity)).trans_eq (mul_one _)

/-- The sup bounds for the `sin(ξ·)` derivative chain, bundled: same constants as
`abs_cosChain_bounds`. -/
private lemma abs_sinChain_bounds (ξ : ℝ) :
    (∀ y : ℝ, |Real.sin (ξ * y)| ≤ 1) ∧ (∀ y : ℝ, |ξ * Real.cos (ξ * y)| ≤ |ξ|) ∧
    (∀ y : ℝ, |(-ξ ^ 2) * Real.sin (ξ * y)| ≤ ξ ^ 2) ∧
    (∀ y : ℝ, |(-ξ ^ 3) * Real.cos (ξ * y)| ≤ |ξ| ^ 3) := by
  refine ⟨fun y => Real.abs_sin_le_one _, fun y => ?_, fun y => ?_, fun y => ?_⟩
  · rw [abs_mul]; simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg ξ)
  · rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg ξ)]
    exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (sq_nonneg ξ)).trans_eq (mul_one _)
  · rw [abs_mul, abs_neg, abs_pow]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)).trans_eq (mul_one _)

/-! ### Localizing the fundamental theorem of calculus to `[0, T]`

The pairing identity is only known on `[0, T]`; to differentiate a Volterra
primitive from the right at a point `x ∈ [0, T)` it suffices that the
integrand be continuous *near `x` within `[0, T]`* — `HasDerivWithinAt` only
sees the germ of the function within the target set, so continuity on `[0,
T]` already supplies everything `integral_hasDerivWithinAt_right` needs at
the one-sided filters `Ici x` / `Ioi x`. -/

private lemma icc_mem_nhdsWithin_Ioi_of_lt {x T : ℝ} (hx0 : 0 ≤ x) (hxT : x < T) :
    Set.Icc (0 : ℝ) T ∈ nhdsWithin x (Set.Ioi x) := by
  rw [mem_nhdsWithin]
  refine ⟨Set.Iio T, isOpen_Iio, hxT, ?_⟩
  rintro y ⟨hy1, hy2⟩
  exact ⟨hx0.trans hy2.le, hy1.le⟩

private lemma icc_mem_nhdsWithin_Ici_of_lt {x T : ℝ} (hx0 : 0 ≤ x) (hxT : x < T) :
    Set.Icc (0 : ℝ) T ∈ nhdsWithin x (Set.Ici x) := by
  rw [mem_nhdsWithin]
  refine ⟨Set.Iio T, isOpen_Iio, hxT, ?_⟩
  rintro y ⟨hy1, hy2⟩
  exact ⟨hx0.trans hy2, hy1.le⟩

lemma hasDerivWithinAt_Ici_of_continuousOn {h : ℝ → ℝ} {x T : ℝ}
    (hcont : ContinuousOn h (Set.Icc 0 T)) (hx0 : 0 ≤ x) (hxT : x < T) :
    HasDerivWithinAt (fun u => ∫ r in (0 : ℝ)..u, h r) (h x) (Set.Ici x) x := by
  have hmemx : x ∈ Set.Icc (0 : ℝ) T := ⟨hx0, hxT.le⟩
  have hmem : Set.Icc (0 : ℝ) T ∈ nhdsWithin x (Set.Ioi x) :=
    icc_mem_nhdsWithin_Ioi_of_lt hx0 hxT
  have hmeas : StronglyMeasurableAtFilter h (nhdsWithin x (Set.Ioi x)) :=
    ⟨Set.Icc 0 T, hmem, hcont.aestronglyMeasurable measurableSet_Icc⟩
  have hb : ContinuousWithinAt h (Set.Ioi x) x := by
    have h1 : ContinuousWithinAt h (Set.Icc 0 T) x := hcont x hmemx
    have h2 : ContinuousWithinAt h (Set.Ioi x ∩ Set.Icc 0 T) x :=
      h1.mono Set.inter_subset_right
    exact (continuousWithinAt_inter' hmem).mp h2
  have hintg : IntervalIntegrable h volume 0 x :=
    ContinuousOn.intervalIntegrable_of_Icc hx0 (hcont.mono (Set.Icc_subset_Icc_right hxT.le))
  exact intervalIntegral.integral_hasDerivWithinAt_right hintg hmeas hb

/-! ### The Volterra system at a fixed frequency -/

/-- For a flow obeying the weak forward equation with constant coefficients,
the pairings against `cos(ξ·)` and `sin(ξ·)` are right-differentiable on `[0,
T)`, with derivatives given by the generator applied to the paired
trigonometric test. -/
lemma hasDerivWithinAt_cosPairing_sinPairing {b v T : ℝ} {μ : ℝ → Measure ℝ}
    (hμ : IsWeakForwardFlow b v T μ) (ξ x : ℝ) (hx0 : 0 ≤ x) (hxT : x < T) :
    HasDerivWithinAt (fun s => ∫ y, Real.cos (ξ * y) ∂(μ s))
      (-b * ξ * (∫ y, Real.sin (ξ * y) ∂(μ x)) - v / 2 * ξ ^ 2 * (∫ y, Real.cos (ξ * y) ∂(μ x)))
      (Set.Ici x) x ∧
    HasDerivWithinAt (fun s => ∫ y, Real.sin (ξ * y) ∂(μ s))
      (b * ξ * (∫ y, Real.cos (ξ * y) ∂(μ x)) - v / 2 * ξ ^ 2 * (∫ y, Real.sin (ξ * y) ∂(μ x)))
      (Set.Ici x) x := by
  have hT : 0 < T := hx0.trans_lt hxT
  obtain ⟨hb0, hb1, hb2, hb3⟩ := abs_cosChain_bounds ξ
  obtain ⟨hb0', hb1', hb2', hb3'⟩ := abs_sinChain_bounds ξ
  have hCcont : ContinuousOn (fun s => ∫ y, Real.cos (ξ * y) ∂(μ s)) (Set.Icc 0 T) :=
    continuousOn_of_lipschitzOn_Icc (by positivity) fun s₀ s hs₀ hs =>
      abs_pairing_lipschitz hμ (hasDerivAt_cosMul ξ) (hasDerivAt_negSinMul ξ)
        (hasDerivAt_negCosSqMul ξ) hb0 hb1 hb2 hb3 hs₀ hs
  have hScont : ContinuousOn (fun s => ∫ y, Real.sin (ξ * y) ∂(μ s)) (Set.Icc 0 T) :=
    continuousOn_of_lipschitzOn_Icc (by positivity) fun s₀ s hs₀ hs =>
      abs_pairing_lipschitz hμ (hasDerivAt_sinMul ξ) (hasDerivAt_cosMulScaled ξ)
        (hasDerivAt_negSinSqMul ξ) hb0' hb1' hb2' hb3' hs₀ hs
  set h : ℝ → ℝ := fun r => -b * ξ * (∫ y, Real.sin (ξ * y) ∂(μ r))
      - v / 2 * ξ ^ 2 * (∫ y, Real.cos (ξ * y) ∂(μ r)) with hhdef
  set k : ℝ → ℝ := fun r => b * ξ * (∫ y, Real.cos (ξ * y) ∂(μ r))
      - v / 2 * ξ ^ 2 * (∫ y, Real.sin (ξ * y) ∂(μ r)) with hkdef
  have hhcont : ContinuousOn h (Set.Icc 0 T) := by
    have e1 : ContinuousOn (fun r => (-b * ξ) * (∫ y, Real.sin (ξ * y) ∂(μ r))) (Set.Icc 0 T) :=
      continuousOn_const.mul hScont
    have e2 : ContinuousOn (fun r => (v / 2 * ξ ^ 2) * (∫ y, Real.cos (ξ * y) ∂(μ r))) (Set.Icc 0 T) :=
      continuousOn_const.mul hCcont
    rw [hhdef]
    exact e1.sub e2
  have hkcont : ContinuousOn k (Set.Icc 0 T) := by
    have e1 : ContinuousOn (fun r => (b * ξ) * (∫ y, Real.cos (ξ * y) ∂(μ r))) (Set.Icc 0 T) :=
      continuousOn_const.mul hCcont
    have e2 : ContinuousOn (fun r => (v / 2 * ξ ^ 2) * (∫ y, Real.sin (ξ * y) ∂(μ r))) (Set.Icc 0 T) :=
      continuousOn_const.mul hScont
    rw [hkdef]
    exact e1.sub e2
  have hCprim : ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ y, Real.cos (ξ * y) ∂(μ s)) = (∫ y, Real.cos (ξ * y) ∂(μ 0)) + ∫ r in (0 : ℝ)..s, h r := by
    intro s hs
    have hinc := pairing_increment hμ (hasDerivAt_cosMul ξ) (hasDerivAt_negSinMul ξ) (hasDerivAt_negCosSqMul ξ) hb0 hb1 hb2 hb3
      (Set.left_mem_Icc.mpr hT.le) hs
    have hcongr : (∫ r in (0 : ℝ)..s,
        (b * ∫ y, (-ξ * Real.sin (ξ * y)) ∂(μ r) + v / 2 * ∫ y, (-ξ ^ 2 * Real.cos (ξ * y)) ∂(μ r)))
        = ∫ r in (0 : ℝ)..s, h r := by
      apply intervalIntegral.integral_congr
      intro r _
      simp only [hhdef, integral_const_mul]
      ring
    rw [hcongr] at hinc
    linarith [hinc]
  have hSprim : ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ y, Real.sin (ξ * y) ∂(μ s)) = (∫ y, Real.sin (ξ * y) ∂(μ 0)) + ∫ r in (0 : ℝ)..s, k r := by
    intro s hs
    have hinc := pairing_increment hμ (hasDerivAt_sinMul ξ) (hasDerivAt_cosMulScaled ξ) (hasDerivAt_negSinSqMul ξ) hb0' hb1' hb2' hb3'
      (Set.left_mem_Icc.mpr hT.le) hs
    have hcongr : (∫ r in (0 : ℝ)..s,
        (b * ∫ y, (ξ * Real.cos (ξ * y)) ∂(μ r) + v / 2 * ∫ y, (-ξ ^ 2 * Real.sin (ξ * y)) ∂(μ r)))
        = ∫ r in (0 : ℝ)..s, k r := by
      apply intervalIntegral.integral_congr
      intro r _
      simp only [hkdef, integral_const_mul]
      ring
    rw [hcongr] at hinc
    linarith [hinc]
  have hCderiv0 : HasDerivWithinAt (fun u => ∫ r in (0 : ℝ)..u, h r) (h x) (Set.Ici x) x :=
    hasDerivWithinAt_Ici_of_continuousOn hhcont hx0 hxT
  have hSderiv0 : HasDerivWithinAt (fun u => ∫ r in (0 : ℝ)..u, k r) (k x) (Set.Ici x) x :=
    hasDerivWithinAt_Ici_of_continuousOn hkcont hx0 hxT
  have hmemIci : x ∈ Set.Ici x := le_refl x
  have heqC : (fun s => ∫ y, Real.cos (ξ * y) ∂(μ s))
      =ᶠ[nhdsWithin x (Set.Ici x)]
      (fun s => (∫ y, Real.cos (ξ * y) ∂(μ 0)) + ∫ r in (0 : ℝ)..s, h r) :=
    Filter.eventually_of_mem (icc_mem_nhdsWithin_Ici_of_lt hx0 hxT) hCprim
  have heqS : (fun s => ∫ y, Real.sin (ξ * y) ∂(μ s))
      =ᶠ[nhdsWithin x (Set.Ici x)]
      (fun s => (∫ y, Real.sin (ξ * y) ∂(μ 0)) + ∫ r in (0 : ℝ)..s, k r) :=
    Filter.eventually_of_mem (icc_mem_nhdsWithin_Ici_of_lt hx0 hxT) hSprim
  have hCderiv : HasDerivWithinAt (fun s => ∫ y, Real.cos (ξ * y) ∂(μ s)) (h x) (Set.Ici x) x :=
    (hCderiv0.const_add (∫ y, Real.cos (ξ * y) ∂(μ 0))).congr_of_eventuallyEq_of_mem heqC hmemIci
  have hSderiv : HasDerivWithinAt (fun s => ∫ y, Real.sin (ξ * y) ∂(μ s)) (k x) (Set.Ici x) x :=
    (hSderiv0.const_add (∫ y, Real.sin (ξ * y) ∂(μ 0))).congr_of_eventuallyEq_of_mem heqS hmemIci
  exact ⟨hCderiv, hSderiv⟩

/-- For a fixed frequency `ξ`, the pairings of `ρ` and `η` against `cos(ξ·)`
and `sin(ξ·)` agree throughout `[0, T]`, given agreement at `0`. The pairing
differences solve a linear Volterra system; a Lipschitz bound gives their
continuity, the one-sided FTC gives their right derivatives, and Grönwall's
inequality (applied to the `ℝ × ℝ`-valued pair, whose sup-norm bounds the
derivative by `K` times itself) forces both to vanish. -/
lemma pairing_cos_sin_eq {b v T : ℝ} {ρ η : ℝ → Measure ℝ}
    (hρ : IsWeakForwardFlow b v T ρ) (hη : IsWeakForwardFlow b v T η)
    (hstart : ρ 0 = η 0) (_hT : 0 < T) (ξ : ℝ) :
    ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ y, Real.cos (ξ * y) ∂(ρ s) = ∫ y, Real.cos (ξ * y) ∂(η s)) ∧
      (∫ y, Real.sin (ξ * y) ∂(ρ s) = ∫ y, Real.sin (ξ * y) ∂(η s)) := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := abs_cosChain_bounds ξ
  obtain ⟨hb0', hb1', hb2', hb3'⟩ := abs_sinChain_bounds ξ
  set K : ℝ := |b| * |ξ| + |v| / 2 * ξ ^ 2 with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  set U : ℝ → ℝ := fun s => (∫ y, Real.cos (ξ * y) ∂(ρ s)) - ∫ y, Real.cos (ξ * y) ∂(η s)
    with hUdef
  set W : ℝ → ℝ := fun s => (∫ y, Real.sin (ξ * y) ∂(ρ s)) - ∫ y, Real.sin (ξ * y) ∂(η s)
    with hWdef
  have hUlip : ∀ s₀ s, s₀ ∈ Set.Icc (0 : ℝ) T → s ∈ Set.Icc (0 : ℝ) T →
      |U s - U s₀| ≤ 2 * K * |s - s₀| := by
    intro s₀ s hs₀ hs
    have h1 := abs_pairing_lipschitz hρ (hasDerivAt_cosMul ξ) (hasDerivAt_negSinMul ξ) (hasDerivAt_negCosSqMul ξ) hb0 hb1 hb2 hb3 hs₀ hs
    have h2 := abs_pairing_lipschitz hη (hasDerivAt_cosMul ξ) (hasDerivAt_negSinMul ξ) (hasDerivAt_negCosSqMul ξ) hb0 hb1 hb2 hb3 hs₀ hs
    have heq : U s - U s₀ = ((∫ y, Real.cos (ξ * y) ∂(ρ s)) - ∫ y, Real.cos (ξ * y) ∂(ρ s₀))
        - ((∫ y, Real.cos (ξ * y) ∂(η s)) - ∫ y, Real.cos (ξ * y) ∂(η s₀)) := by
      simp only [hUdef]; ring
    rw [heq]
    calc |((∫ y, Real.cos (ξ * y) ∂(ρ s)) - ∫ y, Real.cos (ξ * y) ∂(ρ s₀))
          - ((∫ y, Real.cos (ξ * y) ∂(η s)) - ∫ y, Real.cos (ξ * y) ∂(η s₀))|
        ≤ |(∫ y, Real.cos (ξ * y) ∂(ρ s)) - ∫ y, Real.cos (ξ * y) ∂(ρ s₀)|
          + |(∫ y, Real.cos (ξ * y) ∂(η s)) - ∫ y, Real.cos (ξ * y) ∂(η s₀)| :=
          abs_sub _ _
      _ ≤ K * |s - s₀| + K * |s - s₀| := by rw [← hKdef] at h1 h2; linarith [h1, h2]
      _ = 2 * K * |s - s₀| := by ring
  have hWlip : ∀ s₀ s, s₀ ∈ Set.Icc (0 : ℝ) T → s ∈ Set.Icc (0 : ℝ) T →
      |W s - W s₀| ≤ 2 * K * |s - s₀| := by
    intro s₀ s hs₀ hs
    have h1 := abs_pairing_lipschitz hρ (hasDerivAt_sinMul ξ) (hasDerivAt_cosMulScaled ξ) (hasDerivAt_negSinSqMul ξ) hb0' hb1' hb2' hb3' hs₀ hs
    have h2 := abs_pairing_lipschitz hη (hasDerivAt_sinMul ξ) (hasDerivAt_cosMulScaled ξ) (hasDerivAt_negSinSqMul ξ) hb0' hb1' hb2' hb3' hs₀ hs
    have heq : W s - W s₀ = ((∫ y, Real.sin (ξ * y) ∂(ρ s)) - ∫ y, Real.sin (ξ * y) ∂(ρ s₀))
        - ((∫ y, Real.sin (ξ * y) ∂(η s)) - ∫ y, Real.sin (ξ * y) ∂(η s₀)) := by
      simp only [hWdef]; ring
    rw [heq]
    calc |((∫ y, Real.sin (ξ * y) ∂(ρ s)) - ∫ y, Real.sin (ξ * y) ∂(ρ s₀))
          - ((∫ y, Real.sin (ξ * y) ∂(η s)) - ∫ y, Real.sin (ξ * y) ∂(η s₀))|
        ≤ |(∫ y, Real.sin (ξ * y) ∂(ρ s)) - ∫ y, Real.sin (ξ * y) ∂(ρ s₀)|
          + |(∫ y, Real.sin (ξ * y) ∂(η s)) - ∫ y, Real.sin (ξ * y) ∂(η s₀)| :=
          abs_sub _ _
      _ ≤ K * |s - s₀| + K * |s - s₀| := by rw [← hKdef] at h1 h2; linarith [h1, h2]
      _ = 2 * K * |s - s₀| := by ring
  have hUcont : ContinuousOn U (Set.Icc 0 T) := continuousOn_of_lipschitzOn_Icc (by positivity) hUlip
  have hWcont : ContinuousOn W (Set.Icc 0 T) := continuousOn_of_lipschitzOn_Icc (by positivity) hWlip
  set F : ℝ → ℝ × ℝ := fun s => (U s, W s) with hFdef
  set F' : ℝ → ℝ × ℝ := fun x => (-b * ξ * W x - v / 2 * ξ ^ 2 * U x,
      b * ξ * U x - v / 2 * ξ ^ 2 * W x) with hF'def
  have hFcont : ContinuousOn F (Set.Icc 0 T) := hUcont.prodMk hWcont
  have hFderiv : ∀ x ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt F (F' x) (Set.Ici x) x := by
    intro x hx
    obtain ⟨hx0, hxT⟩ := hx
    obtain ⟨hCρ, hSρ⟩ := hasDerivWithinAt_cosPairing_sinPairing hρ ξ x hx0 hxT
    obtain ⟨hCη, hSη⟩ := hasDerivWithinAt_cosPairing_sinPairing hη ξ x hx0 hxT
    have hU' : HasDerivWithinAt U (-b * ξ * W x - v / 2 * ξ ^ 2 * U x) (Set.Ici x) x := by
      refine (hCρ.sub hCη).congr_deriv ?_
      simp only [hUdef, hWdef]
      ring
    have hW' : HasDerivWithinAt W (b * ξ * U x - v / 2 * ξ ^ 2 * W x) (Set.Ici x) x := by
      refine (hSρ.sub hSη).congr_deriv ?_
      simp only [hUdef, hWdef]
      ring
    exact hU'.prodMk hW'
  have hF0 : F 0 = 0 := by
    have hU0 : U 0 = 0 := by simp only [hUdef, hstart, sub_self]
    have hW0 : W 0 = 0 := by simp only [hWdef, hstart, sub_self]
    simp [hFdef, hU0, hW0]
  have hFbound : ∀ x ∈ Set.Ico (0 : ℝ) T, ‖F' x‖ ≤ K * ‖F x‖ := by
    intro x _
    rw [hF'def, hFdef, Prod.norm_mk, Prod.norm_mk]
    have hUle : |U x| ≤ max |U x| |W x| := le_max_left _ _
    have hWle : |W x| ≤ max |U x| |W x| := le_max_right _ _
    have hhalf : |v / 2| = |v| / 2 := by rw [abs_div]; norm_num
    apply max_le
    · calc |(-b * ξ * W x - v / 2 * ξ ^ 2 * U x)|
          ≤ |b * ξ * W x| + |v / 2 * ξ ^ 2 * U x| :=
            (abs_sub _ _).trans_eq (by rw [neg_mul, neg_mul, abs_neg])
        _ = |b| * |ξ| * |W x| + |v| / 2 * ξ ^ 2 * |U x| := by
            rw [abs_mul, abs_mul, abs_mul, abs_mul, hhalf, abs_of_nonneg (sq_nonneg ξ)]
        _ ≤ |b| * |ξ| * max |U x| |W x| + |v| / 2 * ξ ^ 2 * max |U x| |W x| :=
            add_le_add (mul_le_mul_of_nonneg_left hWle (by positivity))
              (mul_le_mul_of_nonneg_left hUle (by positivity))
        _ = K * max |U x| |W x| := by rw [hKdef]; ring
    · calc |(b * ξ * U x - v / 2 * ξ ^ 2 * W x)|
          ≤ |b * ξ * U x| + |v / 2 * ξ ^ 2 * W x| := abs_sub _ _
        _ = |b| * |ξ| * |U x| + |v| / 2 * ξ ^ 2 * |W x| := by
            rw [abs_mul, abs_mul, abs_mul, abs_mul, hhalf, abs_of_nonneg (sq_nonneg ξ)]
        _ ≤ |b| * |ξ| * max |U x| |W x| + |v| / 2 * ξ ^ 2 * max |U x| |W x| :=
            add_le_add (mul_le_mul_of_nonneg_left hUle (by positivity))
              (mul_le_mul_of_nonneg_left hWle (by positivity))
        _ = K * max |U x| |W x| := by rw [hKdef]; ring
  have hFzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hFcont hFderiv hF0 hFbound
  intro s hs
  have hz := hFzero s hs
  rw [hFdef] at hz
  have hUz : U s = 0 := by have := congrArg Prod.fst hz; simpa using this
  have hWz : W s = 0 := by have := congrArg Prod.snd hz; simpa using this
  refine ⟨?_, ?_⟩
  · have := hUz; rw [hUdef] at this; linarith [this]
  · have := hWz; rw [hWdef] at this; linarith [this]

/-- Two probability-measure flows obeying the integrated weak forward equation
with the same constant drift and variance, and sharing an initial law,
coincide at every later time: weak uniqueness for the constant-coefficient
forward equation. The argument pairs both flows against `cos(ξ·)`/`sin(ξ·)`
at every frequency `ξ` (`pairing_cos_sin_eq`), giving equal characteristic
functions, and concludes via `MeasureTheory.Measure.ext_of_charFun`. -/
theorem weakForwardUniqueConst {ρ η : ℝ → Measure ℝ} {b v T : ℝ}
    (hρ : IsWeakForwardFlow b v T ρ) (hη : IsWeakForwardFlow b v T η)
    (hstart : ρ 0 = η 0) :
    ∀ s ∈ Set.Ioc (0 : ℝ) T, ρ s = η s := by
  intro s hs
  haveI := hρ.1 s
  haveI := hη.1 s
  have hT : 0 < T := hs.1.trans_le hs.2
  have hsIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hs.2⟩
  have hchar : charFun (ρ s) = charFun (η s) := by
    funext ξ
    obtain ⟨hc, hsi⟩ := pairing_cos_sin_eq hρ hη hstart hT ξ s hsIcc
    have hexp : ∀ x : ℝ, Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)
        = (Real.cos (ξ * x) : ℂ) + (Real.sin (ξ * x) : ℂ) * Complex.I := by
      intro x
      rw [show ((ξ : ℂ) * (x : ℂ)) = ((ξ * x : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
    have hintρc : Integrable (fun x => (Real.cos (ξ * x) : ℂ)) (ρ s) :=
      Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
        (Filter.Eventually.of_forall fun x => by
          simp only [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
    have hintρs : Integrable (fun x => (Real.sin (ξ * x) : ℂ)) (ρ s) :=
      Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
        (Filter.Eventually.of_forall fun x => by
          simp only [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
    have hintηc : Integrable (fun x => (Real.cos (ξ * x) : ℂ)) (η s) :=
      Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
        (Filter.Eventually.of_forall fun x => by
          simp only [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
    have hintηs : Integrable (fun x => (Real.sin (ξ * x) : ℂ)) (η s) :=
      Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
        (Filter.Eventually.of_forall fun x => by
          simp only [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
    calc charFun (ρ s) ξ
        = ∫ x, Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I) ∂(ρ s) := charFun_apply_real ξ
      _ = ∫ x, ((Real.cos (ξ * x) : ℂ) + (Real.sin (ξ * x) : ℂ) * Complex.I) ∂(ρ s) := by
          simp_rw [hexp]
      _ = (∫ x, (Real.cos (ξ * x) : ℂ) ∂(ρ s))
          + (∫ x, (Real.sin (ξ * x) : ℂ) ∂(ρ s)) * Complex.I := by
          rw [integral_add hintρc (hintρs.mul_const Complex.I), integral_mul_const]
      _ = ((∫ x, Real.cos (ξ * x) ∂(ρ s) : ℝ) : ℂ)
          + ((∫ x, Real.sin (ξ * x) ∂(ρ s) : ℝ) : ℂ) * Complex.I := by
          rw [integral_complex_ofReal, integral_complex_ofReal]
      _ = ((∫ x, Real.cos (ξ * x) ∂(η s) : ℝ) : ℂ)
          + ((∫ x, Real.sin (ξ * x) ∂(η s) : ℝ) : ℂ) * Complex.I := by rw [hc, hsi]
      _ = (∫ x, (Real.cos (ξ * x) : ℂ) ∂(η s))
          + (∫ x, (Real.sin (ξ * x) : ℂ) ∂(η s)) * Complex.I := by
          rw [integral_complex_ofReal, integral_complex_ofReal]
      _ = ∫ x, ((Real.cos (ξ * x) : ℂ) + (Real.sin (ξ * x) : ℂ) * Complex.I) ∂(η s) := by
          rw [← integral_mul_const, ← integral_add hintηc (hintηs.mul_const Complex.I)]
      _ = ∫ x, Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I) ∂(η s) := by simp_rw [← hexp]
      _ = charFun (η s) ξ := (charFun_apply_real ξ).symm
  exact Measure.ext_of_charFun hchar

end MathFin
