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
`ρ 0 = η 0` coincide at every time in `(0, T]` (`weakForwardUniqueConst`).

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

Two differences from the hypothesis shape of `MathFin.GyongyMimicry`'s
`gyongy_mimicry_gated` (the gated mimicry theorem this module's hypothesis class
is modeled on, for the constant-coefficient instance wired up downstream in
`MathFin.GyongyMimicry.hgate_const_of_isWeakForwardFlow`): the test class here
also bounds the test function itself, which *restricts* the admissible tests
relative to `gyongy_mimicry_gated`'s `ContDiff ℝ 2 g` (a real restriction, not a
strengthening — though `cos(ξ·)`/`sin(ξ·)` stay admissible, so the argument below
is unaffected by it); and the identity hypothesis here directly supplies the
interval-integrability of the pairing integrand, which `gyongy_mimicry_gated`
does not require (automatic when the pairing maps are continuous, e.g. for flows
built from Itô processes, but not derived here from a weaker hypothesis — a real
strengthening). `MathFin.GyongyMimicry.hgate_const_of_isWeakForwardFlow` wires
`weakForwardUniqueConst` into `gyongy_mimicry_gated`'s `hgate` for the
constant-coefficient instance, given `hgate`'s own hypothesis restricted to the
bounded-test class (the first difference above — a weaker ask of the caller, not
an extra one) together with the interval-integrability conjunct supplied as an
explicit hypothesis (the second difference, the one genuine extra obligation);
deriving that second condition from something weaker (e.g. continuity of the
pairing integrand) is left to a future module.
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

Against a probability measure, the pairing with a bounded function is bounded
by the sup bound; the integrated identity then makes every admissible
pairing Lipschitz-continuous in time. -/

/-- The pairing of a bounded function against a probability measure is
bounded by the sup bound. -/
lemma abs_pairing_le {μ : Measure ℝ} (hμ : IsProbabilityMeasure μ) {g : ℝ → ℝ} {C : ℝ}
    (hg : ∀ x, |g x| ≤ C) : |∫ y, g y ∂μ| ≤ C := by
  simpa using norm_integral_le_of_norm_le_const (μ := μ) (f := g) (ae_of_all μ hg)

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
  set w : ℝ → ℝ := fun r => b * ∫ y, g' y ∂(ρ r) + v / 2 * ∫ y, g'' y ∂(ρ r)
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

/-- Two flows' pairing differences against the same admissible test are Lipschitz, with
twice the single-flow constant: the shared triangle-inequality step behind both `hUlip` and
`hWlip` in `pairing_cos_sin_eq`. -/
private lemma diff_pairing_lipschitz {b v T : ℝ} {ρ η : ℝ → Measure ℝ}
    (hρ : IsWeakForwardFlow b v T ρ) (hη : IsWeakForwardFlow b v T η)
    {g g' g'' g''' : ℝ → ℝ} {C0 C1 C2 C3 : ℝ}
    (h1 : ∀ x, HasDerivAt g (g' x) x) (h2 : ∀ x, HasDerivAt g' (g'' x) x)
    (h3 : ∀ x, HasDerivAt g'' (g''' x) x)
    (h0 : ∀ x, |g x| ≤ C0) (hb1 : ∀ x, |g' x| ≤ C1) (hb2 : ∀ x, |g'' x| ≤ C2)
    (hb3 : ∀ x, |g''' x| ≤ C3)
    {s₀ s : ℝ} (hs₀ : s₀ ∈ Set.Icc (0 : ℝ) T) (hs : s ∈ Set.Icc (0 : ℝ) T) :
    |((∫ y, g y ∂(ρ s)) - ∫ y, g y ∂(η s)) - ((∫ y, g y ∂(ρ s₀)) - ∫ y, g y ∂(η s₀))|
      ≤ 2 * (|b| * C1 + |v| / 2 * C2) * |s - s₀| := by
  have h1' := abs_pairing_lipschitz hρ h1 h2 h3 h0 hb1 hb2 hb3 hs₀ hs
  have h2' := abs_pairing_lipschitz hη h1 h2 h3 h0 hb1 hb2 hb3 hs₀ hs
  calc |((∫ y, g y ∂(ρ s)) - ∫ y, g y ∂(η s)) - ((∫ y, g y ∂(ρ s₀)) - ∫ y, g y ∂(η s₀))|
      = |((∫ y, g y ∂(ρ s)) - ∫ y, g y ∂(ρ s₀)) - ((∫ y, g y ∂(η s)) - ∫ y, g y ∂(η s₀))| := by
        congr 1; ring
    _ ≤ |(∫ y, g y ∂(ρ s)) - ∫ y, g y ∂(ρ s₀)| + |(∫ y, g y ∂(η s)) - ∫ y, g y ∂(η s₀)| :=
        abs_sub _ _
    _ ≤ (|b| * C1 + |v| / 2 * C2) * |s - s₀| + (|b| * C1 + |v| / 2 * C2) * |s - s₀| :=
        add_le_add h1' h2'
    _ = 2 * (|b| * C1 + |v| / 2 * C2) * |s - s₀| := by ring

/-- A function Lipschitz on `[0, T]` (with a known-nonnegative constant) is continuous
there: the `ε`-`δ` argument shared by every Lipschitz-from-a-pairing-identity bound in
this file. -/
private lemma continuousOn_of_lipschitzOn_Icc {f : ℝ → ℝ} {T L : ℝ}
    (hLip : ∀ s₀ s, s₀ ∈ Set.Icc (0 : ℝ) T → s ∈ Set.Icc (0 : ℝ) T →
      |f s - f s₀| ≤ L * |s - s₀|) :
    ContinuousOn f (Set.Icc 0 T) :=
  (LipschitzOnWith.of_dist_le' (K := L) fun s₀ hs₀ s hs => by
    simpa [Real.dist_eq, abs_sub_comm] using hLip s₀ s hs₀ hs).continuousOn

/-- The generator's linear combination against a frequency, bounded by the sup-norm: the
shared triangle-inequality step behind both components of `hFbound` in `pairing_cos_sin_eq`
(the `ℝ × ℝ` Grönwall bound `‖F' x‖ ≤ K * ‖F x‖`). -/
private lemma abs_genLinComb_le (b v ξ p q : ℝ) :
    |b * ξ * p + v / 2 * ξ ^ 2 * q| ≤ (|b| * |ξ| + |v| / 2 * ξ ^ 2) * max |p| |q| := by
  have hp : |p| ≤ max |p| |q| := le_max_left _ _
  have hq : |q| ≤ max |p| |q| := le_max_right _ _
  have hhalf : |v / 2| = |v| / 2 := by rw [abs_div]; norm_num
  calc |b * ξ * p + v / 2 * ξ ^ 2 * q|
      ≤ |b * ξ * p| + |v / 2 * ξ ^ 2 * q| := abs_add_le _ _
    _ = |b| * |ξ| * |p| + |v| / 2 * ξ ^ 2 * |q| := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, hhalf, abs_of_nonneg (sq_nonneg ξ)]
    _ ≤ |b| * |ξ| * max |p| |q| + |v| / 2 * ξ ^ 2 * max |p| |q| :=
        add_le_add (mul_le_mul_of_nonneg_left hp (by positivity))
          (mul_le_mul_of_nonneg_left hq (by positivity))
    _ = (|b| * |ξ| + |v| / 2 * ξ ^ 2) * max |p| |q| := by ring

/-! ### Trigonometric test chains

`cos(ξ·)` and `sin(ξ·)` have constant-coefficient derivative chains: the
generator `b · (·)' + v/2 · (·)''` maps each to a linear combination of the
other, with no new functions appearing — the algebraic fact that drives the
Volterra system in `pairing_cos_sin_eq`. -/

/-- The inner linear map `y ↦ ξ * y` of every chain-rule step below. -/
private lemma hasDerivAt_linMul (ξ x : ℝ) : HasDerivAt (fun y : ℝ => ξ * y) ξ x := by
  simpa using (hasDerivAt_id x).const_mul ξ

lemma hasDerivAt_cosMul (ξ x : ℝ) :
    HasDerivAt (fun x => Real.cos (ξ * x)) (-ξ * Real.sin (ξ * x)) x :=
  ((Real.hasDerivAt_cos (ξ * x)).comp x (hasDerivAt_linMul ξ x)).congr_deriv (by ring)

lemma hasDerivAt_negSinMul (ξ x : ℝ) :
    HasDerivAt (fun x => -ξ * Real.sin (ξ * x)) (-ξ ^ 2 * Real.cos (ξ * x)) x :=
  (((Real.hasDerivAt_sin (ξ * x)).comp x (hasDerivAt_linMul ξ x)).const_mul (-ξ)).congr_deriv
    (by ring)

lemma hasDerivAt_negCosSqMul (ξ x : ℝ) :
    HasDerivAt (fun x => -ξ ^ 2 * Real.cos (ξ * x)) (ξ ^ 3 * Real.sin (ξ * x)) x :=
  (((Real.hasDerivAt_cos (ξ * x)).comp x (hasDerivAt_linMul ξ x)).const_mul
    (-ξ ^ 2)).congr_deriv (by ring)

lemma hasDerivAt_sinMul (ξ x : ℝ) :
    HasDerivAt (fun x => Real.sin (ξ * x)) (ξ * Real.cos (ξ * x)) x :=
  ((Real.hasDerivAt_sin (ξ * x)).comp x (hasDerivAt_linMul ξ x)).congr_deriv (by ring)

lemma hasDerivAt_cosMulScaled (ξ x : ℝ) :
    HasDerivAt (fun x => ξ * Real.cos (ξ * x)) (-ξ ^ 2 * Real.sin (ξ * x)) x :=
  (((Real.hasDerivAt_cos (ξ * x)).comp x (hasDerivAt_linMul ξ x)).const_mul ξ).congr_deriv
    (by ring)

lemma hasDerivAt_negSinSqMul (ξ x : ℝ) :
    HasDerivAt (fun x => -ξ ^ 2 * Real.sin (ξ * x)) (-ξ ^ 3 * Real.cos (ξ * x)) x :=
  (((Real.hasDerivAt_sin (ξ * x)).comp x (hasDerivAt_linMul ξ x)).const_mul
    (-ξ ^ 2)).congr_deriv (by ring)

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

/-- A function equal to its own Volterra primitive on `[0, T]` is right-differentiable there,
with derivative the (continuous) generator value: combines
`hasDerivWithinAt_Ici_of_continuousOn` (the primitive's own derivative) with the
`=ᶠ[𝓝[Ici x] x]` transfer from the primitive identity — the shared step behind both
`hCderiv` and `hSderiv` in `hasDerivWithinAt_cosPairing_sinPairing`. -/
private lemma hasDerivWithinAt_of_volterra_primitive {g h : ℝ → ℝ} {x T : ℝ}
    (hcont : ContinuousOn h (Set.Icc 0 T)) (hx0 : 0 ≤ x) (hxT : x < T)
    (hprim : ∀ s ∈ Set.Icc (0 : ℝ) T, g s = g 0 + ∫ r in (0 : ℝ)..s, h r) :
    HasDerivWithinAt g (h x) (Set.Ici x) x := by
  have hderiv0 : HasDerivWithinAt (fun u => ∫ r in (0 : ℝ)..u, h r) (h x) (Set.Ici x) x :=
    hasDerivWithinAt_Ici_of_continuousOn hcont hx0 hxT
  have heq : g =ᶠ[nhdsWithin x (Set.Ici x)] (fun s => g 0 + ∫ r in (0 : ℝ)..s, h r) :=
    Filter.eventually_of_mem (icc_mem_nhdsWithin_Ici_of_lt hx0 hxT) hprim
  exact (hderiv0.const_add (g 0)).congr_of_eventuallyEq_of_mem heq (le_refl x)

/-- An admissible pairing is the Volterra primitive of its generator value, once the
generator is recognized as a named function `h`: the shared `pairing_increment` + generator
rewrite step behind both `hCprim` and `hSprim` in `hasDerivWithinAt_cosPairing_sinPairing`. -/
private lemma pairing_volterra_primitive {b v T : ℝ} {μ : ℝ → Measure ℝ}
    (hμ : IsWeakForwardFlow b v T μ) (hT : 0 < T)
    {g g' g'' g''' : ℝ → ℝ} {C0 C1 C2 C3 : ℝ}
    (h1 : ∀ x, HasDerivAt g (g' x) x) (h2 : ∀ x, HasDerivAt g' (g'' x) x)
    (h3 : ∀ x, HasDerivAt g'' (g''' x) x)
    (h0 : ∀ x, |g x| ≤ C0) (hb1 : ∀ x, |g' x| ≤ C1) (hb2 : ∀ x, |g'' x| ≤ C2)
    (hb3 : ∀ x, |g''' x| ≤ C3) (h : ℝ → ℝ)
    (hheq : ∀ r, h r = b * ∫ y, g' y ∂(μ r) + v / 2 * ∫ y, g'' y ∂(μ r)) :
    ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ y, g y ∂(μ s)) = (∫ y, g y ∂(μ 0)) + ∫ r in (0 : ℝ)..s, h r := by
  intro s hs
  have hinc := pairing_increment hμ h1 h2 h3 h0 hb1 hb2 hb3 (Set.left_mem_Icc.mpr hT.le) hs
  have hcongr : (∫ r in (0 : ℝ)..s,
      (b * ∫ y, g' y ∂(μ r) + v / 2 * ∫ y, g'' y ∂(μ r))) = ∫ r in (0 : ℝ)..s, h r :=
    intervalIntegral.integral_congr fun r _ => (hheq r).symm
  rw [hcongr] at hinc
  linarith [hinc]

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
    continuousOn_of_lipschitzOn_Icc fun s₀ s hs₀ hs =>
      abs_pairing_lipschitz hμ (hasDerivAt_cosMul ξ) (hasDerivAt_negSinMul ξ)
        (hasDerivAt_negCosSqMul ξ) hb0 hb1 hb2 hb3 hs₀ hs
  have hScont : ContinuousOn (fun s => ∫ y, Real.sin (ξ * y) ∂(μ s)) (Set.Icc 0 T) :=
    continuousOn_of_lipschitzOn_Icc fun s₀ s hs₀ hs =>
      abs_pairing_lipschitz hμ (hasDerivAt_sinMul ξ) (hasDerivAt_cosMulScaled ξ)
        (hasDerivAt_negSinSqMul ξ) hb0' hb1' hb2' hb3' hs₀ hs
  set h : ℝ → ℝ := fun r => -b * ξ * (∫ y, Real.sin (ξ * y) ∂(μ r))
      - v / 2 * ξ ^ 2 * (∫ y, Real.cos (ξ * y) ∂(μ r)) with hhdef
  set k : ℝ → ℝ := fun r => b * ξ * (∫ y, Real.cos (ξ * y) ∂(μ r))
      - v / 2 * ξ ^ 2 * (∫ y, Real.sin (ξ * y) ∂(μ r)) with hkdef
  have hhcont : ContinuousOn h (Set.Icc 0 T) := by
    rw [hhdef]; exact (continuousOn_const.mul hScont).sub (continuousOn_const.mul hCcont)
  have hkcont : ContinuousOn k (Set.Icc 0 T) := by
    rw [hkdef]; exact (continuousOn_const.mul hCcont).sub (continuousOn_const.mul hScont)
  have hCprim : ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ y, Real.cos (ξ * y) ∂(μ s)) = (∫ y, Real.cos (ξ * y) ∂(μ 0)) + ∫ r in (0 : ℝ)..s, h r :=
    pairing_volterra_primitive hμ hT (hasDerivAt_cosMul ξ) (hasDerivAt_negSinMul ξ)
      (hasDerivAt_negCosSqMul ξ) hb0 hb1 hb2 hb3 h fun r => by
        simp only [hhdef, integral_const_mul]; ring
  have hSprim : ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ y, Real.sin (ξ * y) ∂(μ s)) = (∫ y, Real.sin (ξ * y) ∂(μ 0)) + ∫ r in (0 : ℝ)..s, k r :=
    pairing_volterra_primitive hμ hT (hasDerivAt_sinMul ξ) (hasDerivAt_cosMulScaled ξ)
      (hasDerivAt_negSinSqMul ξ) hb0' hb1' hb2' hb3' k fun r => by
        simp only [hkdef, integral_const_mul]; ring
  have hCderiv : HasDerivWithinAt (fun s => ∫ y, Real.cos (ξ * y) ∂(μ s)) (h x) (Set.Ici x) x :=
    hasDerivWithinAt_of_volterra_primitive hhcont hx0 hxT hCprim
  have hSderiv : HasDerivWithinAt (fun s => ∫ y, Real.sin (ξ * y) ∂(μ s)) (k x) (Set.Ici x) x :=
    hasDerivWithinAt_of_volterra_primitive hkcont hx0 hxT hSprim
  exact ⟨hCderiv, hSderiv⟩

/-- For a fixed frequency `ξ`, the pairings of `ρ` and `η` against `cos(ξ·)`
and `sin(ξ·)` agree throughout `[0, T]`, given agreement at `0`. The pairing
differences solve a linear Volterra system; a Lipschitz bound gives their
continuity, the one-sided FTC gives their right derivatives, and Grönwall's
inequality (applied to the `ℝ × ℝ`-valued pair, whose sup-norm bounds the
derivative by `K` times itself) forces both to vanish. -/
lemma pairing_cos_sin_eq {b v T : ℝ} {ρ η : ℝ → Measure ℝ}
    (hρ : IsWeakForwardFlow b v T ρ) (hη : IsWeakForwardFlow b v T η)
    (hstart : ρ 0 = η 0) (ξ : ℝ) :
    ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ y, Real.cos (ξ * y) ∂(ρ s) = ∫ y, Real.cos (ξ * y) ∂(η s)) ∧
      (∫ y, Real.sin (ξ * y) ∂(ρ s) = ∫ y, Real.sin (ξ * y) ∂(η s)) := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := abs_cosChain_bounds ξ
  obtain ⟨hb0', hb1', hb2', hb3'⟩ := abs_sinChain_bounds ξ
  set K : ℝ := |b| * |ξ| + |v| / 2 * ξ ^ 2 with hKdef
  set U : ℝ → ℝ := fun s => (∫ y, Real.cos (ξ * y) ∂(ρ s)) - ∫ y, Real.cos (ξ * y) ∂(η s)
    with hUdef
  set W : ℝ → ℝ := fun s => (∫ y, Real.sin (ξ * y) ∂(ρ s)) - ∫ y, Real.sin (ξ * y) ∂(η s)
    with hWdef
  have hUlip : ∀ s₀ s, s₀ ∈ Set.Icc (0 : ℝ) T → s ∈ Set.Icc (0 : ℝ) T →
      |U s - U s₀| ≤ 2 * K * |s - s₀| := by
    intro s₀ s hs₀ hs
    have := diff_pairing_lipschitz hρ hη (hasDerivAt_cosMul ξ) (hasDerivAt_negSinMul ξ)
      (hasDerivAt_negCosSqMul ξ) hb0 hb1 hb2 hb3 hs₀ hs
    simpa only [hUdef, hKdef] using this
  have hWlip : ∀ s₀ s, s₀ ∈ Set.Icc (0 : ℝ) T → s ∈ Set.Icc (0 : ℝ) T →
      |W s - W s₀| ≤ 2 * K * |s - s₀| := by
    intro s₀ s hs₀ hs
    have := diff_pairing_lipschitz hρ hη (hasDerivAt_sinMul ξ) (hasDerivAt_cosMulScaled ξ)
      (hasDerivAt_negSinSqMul ξ) hb0' hb1' hb2' hb3' hs₀ hs
    simpa only [hWdef, hKdef] using this
  have hUcont : ContinuousOn U (Set.Icc 0 T) := continuousOn_of_lipschitzOn_Icc hUlip
  have hWcont : ContinuousOn W (Set.Icc 0 T) := continuousOn_of_lipschitzOn_Icc hWlip
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
    apply max_le
    · have heq : (-b * ξ * W x - v / 2 * ξ ^ 2 * U x)
          = b * ξ * (-W x) + v / 2 * ξ ^ 2 * (-U x) := by ring
      rw [heq]
      have hb := abs_genLinComb_le b v ξ (-W x) (-U x)
      rwa [abs_neg, abs_neg, max_comm, ← hKdef] at hb
    · have heq : (b * ξ * U x - v / 2 * ξ ^ 2 * W x) = b * ξ * U x + v / 2 * ξ ^ 2 * (-W x) := by
        ring
      rw [heq]
      have hb := abs_genLinComb_le b v ξ (U x) (-W x)
      rwa [abs_neg, ← hKdef] at hb
  have hFzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hFcont hFderiv hF0 hFbound
  intro s hs
  have hz := hFzero s hs
  rw [hFdef] at hz
  have hUz : U s = 0 := by have := congrArg Prod.fst hz; simpa using this
  have hWz : W s = 0 := by have := congrArg Prod.snd hz; simpa using this
  refine ⟨?_, ?_⟩
  · have := hUz; rw [hUdef] at this; linarith [this]
  · have := hWz; rw [hWdef] at this; linarith [this]

/-- The characteristic function of a probability measure, split into its real/imaginary
`cos`/`sin` pairings: the shared computation behind both sides of `weakForwardUniqueConst`'s
`charFun` comparison (applied once to `ρ s`, once to `η s`). -/
private lemma charFun_eq_cos_add_sin_mul_I {μ : Measure ℝ} [IsProbabilityMeasure μ] (ξ : ℝ) :
    charFun μ ξ = ((∫ x, Real.cos (ξ * x) ∂μ : ℝ) : ℂ)
      + ((∫ x, Real.sin (ξ * x) ∂μ : ℝ) : ℂ) * Complex.I := by
  have hexp : ∀ x : ℝ, Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)
      = (Real.cos (ξ * x) : ℂ) + (Real.sin (ξ * x) : ℂ) * Complex.I := by
    intro x
    rw [show ((ξ : ℂ) * (x : ℂ)) = ((ξ * x : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have hint : ∀ g : ℝ → ℝ, Continuous g → (∀ x, |g x| ≤ 1) →
      Integrable (fun x => (g x : ℂ)) μ := fun g hgc hg =>
    Integrable.mono' (integrable_const (1 : ℝ))
      (Complex.continuous_ofReal.comp hgc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simp only [Complex.norm_real, Real.norm_eq_abs]; exact hg x)
  rw [charFun_apply_real]
  simp_rw [hexp]
  rw [integral_add (hint _ (by fun_prop) fun x => Real.abs_cos_le_one (ξ * x))
    ((hint _ (by fun_prop) fun x => Real.abs_sin_le_one (ξ * x)).mul_const Complex.I),
    integral_mul_const, integral_complex_ofReal, integral_complex_ofReal]

/-- Two probability-measure flows obeying the integrated weak forward equation
with the same constant drift and variance, and sharing an initial law, coincide
at every time in `(0, T]`: weak uniqueness for the constant-coefficient forward
equation. The argument pairs both flows against `cos(ξ·)`/`sin(ξ·)` at every
frequency `ξ` (`pairing_cos_sin_eq`), giving equal characteristic functions, and
concludes via `MeasureTheory.Measure.ext_of_charFun`. -/
theorem weakForwardUniqueConst {ρ η : ℝ → Measure ℝ} {b v T : ℝ}
    (hρ : IsWeakForwardFlow b v T ρ) (hη : IsWeakForwardFlow b v T η)
    (hstart : ρ 0 = η 0) :
    ∀ s ∈ Set.Ioc (0 : ℝ) T, ρ s = η s := by
  intro s hs
  haveI := hρ.1 s
  haveI := hη.1 s
  have hsIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hs.2⟩
  refine Measure.ext_of_charFun (funext fun ξ => ?_)
  obtain ⟨hc, hsi⟩ := pairing_cos_sin_eq hρ hη hstart ξ s hsIcc
  rw [charFun_eq_cos_add_sin_mul_I, charFun_eq_cos_add_sin_mul_I, hc, hsi]

end MathFin
