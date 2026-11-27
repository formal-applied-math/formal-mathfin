/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Brownian.Ito.ItoFormulaCutoff

/-! # The triple cutoff for `f(t, x, y)`

The cutoff of `ItoFormulaCutoff` in three variables, for the two-factor Itô formula
(`ItoFormulaTwoFactorLocal`): a function `f(t, x, y)` with jointly continuous partials is cut off,
in time and in both space variables, onto a compact cube where its partials are bounded, so the
bounded-partials formula (`ito_formula_adapted_two_factor_against`) applies to it.

* `SummitC.fTrunc3 N (t, x, y) = f(φₙ t, φₙ x, φₙ y)`, with the six partials
  `fTruncT3`, `fTruncX3`, `fTruncY3`, `fTruncXX3`, `fTruncXY3`, `fTruncYY3` in closed form by the
  chain rule, each globally bounded, jointly continuous, and equal to the partials of `f` where
  `|t|, |x|, |y| ≤ N`.

## Main definitions

* `SummitC.fTrunc3`: the triple cutoff `f(φₙ t, φₙ x, φₙ y)`.
* `SummitC.fTruncT3`, `fTruncX3`, `fTruncY3`, `fTruncXX3`, `fTruncXY3`, `fTruncYY3`: its partials
  `f_t`, `f_x`, `f_y`, `f_xx`, `f_xy = ∂_y f_x`, `f_yy`.

## Main results

* `SummitC.fTrunc3_hasDerivAt_t` and its five analogues: the partials of the cutoff.
* `SummitC.fTruncT3_bdd` and its five analogues: for jointly continuous partials of `f` each
  partial of the cutoff is globally bounded.
* `SummitC.fTruncT3_continuous` and its five analogues: each is jointly continuous.
* `SummitC.fTrunc3_eq_of` and its six analogues: for `|s|, |x|, |y| ≤ N` the cutoff and its
  partials are those of `f`.

## References

* [I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991],
  Theorem 3.3.6

## Tags

cutoff function, localisation, Itô formula, two-dimensional Itô formula, MSC 60H05
-/

@[expose] public section

namespace MathFin

namespace SummitC

variable {f f_t f_x f_y f_xx f_xy f_yy : ℝ → ℝ → ℝ → ℝ}

/-- The triple cutoff `fTrunc3 N (t, x, y) = f(φₙ t, φₙ x, φₙ y)`. -/
noncomputable def fTrunc3 (f : ℝ → ℝ → ℝ → ℝ) (S : SmoothTrunc) (N : ℕ) (t x y : ℝ) : ℝ :=
  f (S.cut N t) (S.cut N x) (S.cut N y)

/-- `∂_t fTrunc3 = f_t(φₙ t, φₙ x, φₙ y)·φₙ'(t)`. -/
noncomputable def fTruncT3 (f_t : ℝ → ℝ → ℝ → ℝ) (S : SmoothTrunc) (N : ℕ) (t x y : ℝ) : ℝ :=
  f_t (S.cut N t) (S.cut N x) (S.cut N y) * S.cutD1 N t

/-- `∂_x fTrunc3 = f_x(φₙ t, φₙ x, φₙ y)·φₙ'(x)`. -/
noncomputable def fTruncX3 (f_x : ℝ → ℝ → ℝ → ℝ) (S : SmoothTrunc) (N : ℕ) (t x y : ℝ) : ℝ :=
  f_x (S.cut N t) (S.cut N x) (S.cut N y) * S.cutD1 N x

/-- `∂_y fTrunc3 = f_y(φₙ t, φₙ x, φₙ y)·φₙ'(y)`. -/
noncomputable def fTruncY3 (f_y : ℝ → ℝ → ℝ → ℝ) (S : SmoothTrunc) (N : ℕ) (t x y : ℝ) : ℝ :=
  f_y (S.cut N t) (S.cut N x) (S.cut N y) * S.cutD1 N y

/-- `∂_xx fTrunc3 = f_xx·(φₙ' x)² + f_x·φₙ''(x)`. -/
noncomputable def fTruncXX3 (f_x f_xx : ℝ → ℝ → ℝ → ℝ) (S : SmoothTrunc) (N : ℕ)
    (t x y : ℝ) : ℝ :=
  f_xx (S.cut N t) (S.cut N x) (S.cut N y) * (S.cutD1 N x * S.cutD1 N x) +
    f_x (S.cut N t) (S.cut N x) (S.cut N y) * S.cutD2 N x

/-- `∂_y ∂_x fTrunc3 = f_xy·φₙ'(y)·φₙ'(x)`. -/
noncomputable def fTruncXY3 (f_xy : ℝ → ℝ → ℝ → ℝ) (S : SmoothTrunc) (N : ℕ) (t x y : ℝ) : ℝ :=
  f_xy (S.cut N t) (S.cut N x) (S.cut N y) * S.cutD1 N y * S.cutD1 N x

/-- `∂_yy fTrunc3 = f_yy·(φₙ' y)² + f_y·φₙ''(y)`. -/
noncomputable def fTruncYY3 (f_y f_yy : ℝ → ℝ → ℝ → ℝ) (S : SmoothTrunc) (N : ℕ)
    (t x y : ℝ) : ℝ :=
  f_yy (S.cut N t) (S.cut N x) (S.cut N y) * (S.cutD1 N y * S.cutD1 N y) +
    f_y (S.cut N t) (S.cut N x) (S.cut N y) * S.cutD2 N y

/-! ### The partials of the cutoff -/

lemma fTrunc3_hasDerivAt_t (hf_t : ∀ t x y, HasDerivAt (fun s ↦ f s x y) (f_t t x y) t)
    (S : SmoothTrunc) (N : ℕ) (t x y : ℝ) :
    HasDerivAt (fun s ↦ fTrunc3 f S N s x y) (fTruncT3 f_t S N t x y) t :=
  (hf_t (S.cut N t) (S.cut N x) (S.cut N y)).comp t (S.cut_hasDerivAt N t)

lemma fTrunc3_hasDerivAt_x (hf_x : ∀ t x y, HasDerivAt (fun u ↦ f t u y) (f_x t x y) x)
    (S : SmoothTrunc) (N : ℕ) (t x y : ℝ) :
    HasDerivAt (fun u ↦ fTrunc3 f S N t u y) (fTruncX3 f_x S N t x y) x :=
  (hf_x (S.cut N t) (S.cut N x) (S.cut N y)).comp x (S.cut_hasDerivAt N x)

lemma fTrunc3_hasDerivAt_y (hf_y : ∀ t x y, HasDerivAt (fun v ↦ f t x v) (f_y t x y) y)
    (S : SmoothTrunc) (N : ℕ) (t x y : ℝ) :
    HasDerivAt (fun v ↦ fTrunc3 f S N t x v) (fTruncY3 f_y S N t x y) y :=
  (hf_y (S.cut N t) (S.cut N x) (S.cut N y)).comp y (S.cut_hasDerivAt N y)

lemma fTrunc3_hasDerivAt_xx (hf_xx : ∀ t x y, HasDerivAt (fun u ↦ f_x t u y) (f_xx t x y) x)
    (S : SmoothTrunc) (N : ℕ) (t x y : ℝ) :
    HasDerivAt (fun u ↦ fTruncX3 f_x S N t u y) (fTruncXX3 f_x f_xx S N t x y) x := by
  have hu : HasDerivAt (fun u ↦ f_x (S.cut N t) (S.cut N u) (S.cut N y))
      (f_xx (S.cut N t) (S.cut N x) (S.cut N y) * S.cutD1 N x) x :=
    (hf_xx (S.cut N t) (S.cut N x) (S.cut N y)).comp x (S.cut_hasDerivAt N x)
  have hv : HasDerivAt (fun u ↦ S.cutD1 N u) (S.cutD2 N x) x := S.cutD1_hasDerivAt N x
  rw [show fTruncXX3 f_x f_xx S N t x y
      = f_xx (S.cut N t) (S.cut N x) (S.cut N y) * S.cutD1 N x * S.cutD1 N x
        + f_x (S.cut N t) (S.cut N x) (S.cut N y) * S.cutD2 N x from by
    unfold fTruncXX3; ring]
  exact hu.mul hv

lemma fTrunc3_hasDerivAt_xy (hf_xy : ∀ t x y, HasDerivAt (fun v ↦ f_x t x v) (f_xy t x y) y)
    (S : SmoothTrunc) (N : ℕ) (t x y : ℝ) :
    HasDerivAt (fun v ↦ fTruncX3 f_x S N t x v) (fTruncXY3 f_xy S N t x y) y :=
  ((hf_xy (S.cut N t) (S.cut N x) (S.cut N y)).comp y (S.cut_hasDerivAt N y)).mul_const
    (S.cutD1 N x)

lemma fTrunc3_hasDerivAt_yy (hf_yy : ∀ t x y, HasDerivAt (fun v ↦ f_y t x v) (f_yy t x y) y)
    (S : SmoothTrunc) (N : ℕ) (t x y : ℝ) :
    HasDerivAt (fun v ↦ fTruncY3 f_y S N t x v) (fTruncYY3 f_y f_yy S N t x y) y := by
  have hu : HasDerivAt (fun v ↦ f_y (S.cut N t) (S.cut N x) (S.cut N v))
      (f_yy (S.cut N t) (S.cut N x) (S.cut N y) * S.cutD1 N y) y :=
    (hf_yy (S.cut N t) (S.cut N x) (S.cut N y)).comp y (S.cut_hasDerivAt N y)
  have hv : HasDerivAt (fun v ↦ S.cutD1 N v) (S.cutD2 N y) y := S.cutD1_hasDerivAt N y
  rw [show fTruncYY3 f_y f_yy S N t x y
      = f_yy (S.cut N t) (S.cut N x) (S.cut N y) * S.cutD1 N y * S.cutD1 N y
        + f_y (S.cut N t) (S.cut N x) (S.cut N y) * S.cutD2 N y from by
    unfold fTruncYY3; ring]
  exact hu.mul hv

/-! ### Constant bounds on the truncated partials -/

/-- A jointly continuous `g` is bounded after all three arguments pass through the cutoff. -/
lemma exists_bound_cut3 (S : SmoothTrunc) (N : ℕ) {g : ℝ → ℝ → ℝ → ℝ}
    (hg : Continuous fun p : ℝ × ℝ × ℝ ↦ g p.1 p.2.1 p.2.2) :
    ∃ C : ℝ, ∀ t x y, |g (S.cut N t) (S.cut N x) (S.cut N y)| ≤ C := by
  set r : ℝ := S.M₀ * ((N : ℝ) + 1)
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := -r) (b := r)).prod
    ((isCompact_Icc (a := -r) (b := r)).prod
      (isCompact_Icc (a := -r) (b := r)))).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨C, fun t x y ↦ ?_⟩
  have hmem : ((S.cut N t, S.cut N x, S.cut N y) : ℝ × ℝ × ℝ)
      ∈ Set.Icc (-r) r ×ˢ (Set.Icc (-r) r ×ˢ Set.Icc (-r) r) :=
    ⟨by rw [Set.mem_Icc, ← abs_le]; exact S.cut_bdd N t,
     by rw [Set.mem_Icc, ← abs_le]; exact S.cut_bdd N x,
     by rw [Set.mem_Icc, ← abs_le]; exact S.cut_bdd N y⟩
  have := hC _ hmem
  rwa [Real.norm_eq_abs] at this

lemma fTruncT3_bdd (S : SmoothTrunc) (N : ℕ)
    (hcont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_t p.1 p.2.1 p.2.2) :
    ∃ C : ℝ, ∀ t x y, |fTruncT3 f_t S N t x y| ≤ C := by
  obtain ⟨B, hB⟩ := exists_bound_cut3 S N hcont
  exact ⟨B * S.M₁, fun t x y ↦ abs_mul_le_mul_of_abs_le (hB t x y) (S.cutD1_bdd N t)⟩

lemma fTruncX3_bdd (S : SmoothTrunc) (N : ℕ)
    (hcont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_x p.1 p.2.1 p.2.2) :
    ∃ C : ℝ, ∀ t x y, |fTruncX3 f_x S N t x y| ≤ C := by
  obtain ⟨B, hB⟩ := exists_bound_cut3 S N hcont
  exact ⟨B * S.M₁, fun t x y ↦ abs_mul_le_mul_of_abs_le (hB t x y) (S.cutD1_bdd N x)⟩

lemma fTruncY3_bdd (S : SmoothTrunc) (N : ℕ)
    (hcont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_y p.1 p.2.1 p.2.2) :
    ∃ C : ℝ, ∀ t x y, |fTruncY3 f_y S N t x y| ≤ C := by
  obtain ⟨B, hB⟩ := exists_bound_cut3 S N hcont
  exact ⟨B * S.M₁, fun t x y ↦ abs_mul_le_mul_of_abs_le (hB t x y) (S.cutD1_bdd N y)⟩

lemma fTruncXX3_bdd (S : SmoothTrunc) (N : ℕ)
    (hf_x_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_x p.1 p.2.1 p.2.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_xx p.1 p.2.1 p.2.2) :
    ∃ C : ℝ, ∀ t x y, |fTruncXX3 f_x f_xx S N t x y| ≤ C := by
  obtain ⟨Bx, hBx⟩ := exists_bound_cut3 S N hf_x_cont
  obtain ⟨Bxx, hBxx⟩ := exists_bound_cut3 S N hf_xx_cont
  refine ⟨Bxx * (S.M₁ * S.M₁) + Bx * S.M₂, fun t x y ↦ ?_⟩
  unfold fTruncXX3
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · exact abs_mul_le_mul_of_abs_le (hBxx t x y)
      (abs_mul_le_mul_of_abs_le (S.cutD1_bdd N x) (S.cutD1_bdd N x))
  · exact abs_mul_le_mul_of_abs_le (hBx t x y) (S.cutD2_bdd N x)

lemma fTruncXY3_bdd (S : SmoothTrunc) (N : ℕ)
    (hf_xy_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_xy p.1 p.2.1 p.2.2) :
    ∃ C : ℝ, ∀ t x y, |fTruncXY3 f_xy S N t x y| ≤ C := by
  obtain ⟨B, hB⟩ := exists_bound_cut3 S N hf_xy_cont
  refine ⟨B * S.M₁ * S.M₁, fun t x y ↦ ?_⟩
  unfold fTruncXY3
  exact abs_mul_le_mul_of_abs_le (abs_mul_le_mul_of_abs_le (hB t x y) (S.cutD1_bdd N y))
    (S.cutD1_bdd N x)

lemma fTruncYY3_bdd (S : SmoothTrunc) (N : ℕ)
    (hf_y_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_y p.1 p.2.1 p.2.2)
    (hf_yy_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_yy p.1 p.2.1 p.2.2) :
    ∃ C : ℝ, ∀ t x y, |fTruncYY3 f_y f_yy S N t x y| ≤ C := by
  obtain ⟨By, hBy⟩ := exists_bound_cut3 S N hf_y_cont
  obtain ⟨Byy, hByy⟩ := exists_bound_cut3 S N hf_yy_cont
  refine ⟨Byy * (S.M₁ * S.M₁) + By * S.M₂, fun t x y ↦ ?_⟩
  unfold fTruncYY3
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · exact abs_mul_le_mul_of_abs_le (hByy t x y)
      (abs_mul_le_mul_of_abs_le (S.cutD1_bdd N y) (S.cutD1_bdd N y))
  · exact abs_mul_le_mul_of_abs_le (hBy t x y) (S.cutD2_bdd N y)

/-! ### Joint continuity of the partials -/

/-- `p ↦ (φₙ p.1, φₙ p.2.1, φₙ p.2.2)` is continuous. -/
private lemma continuous_cut_triple (S : SmoothTrunc) (N : ℕ) :
    Continuous fun p : ℝ × ℝ × ℝ ↦ ((S.cut N p.1, S.cut N p.2.1, S.cut N p.2.2) : ℝ × ℝ × ℝ) :=
  ((S.continuous_cut N).comp continuous_fst).prodMk
    (((S.continuous_cut N).comp continuous_snd.fst).prodMk
      ((S.continuous_cut N).comp continuous_snd.snd))

lemma fTruncT3_continuous (S : SmoothTrunc) (N : ℕ)
    (hf_t_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_t p.1 p.2.1 p.2.2) :
    Continuous fun p : ℝ × ℝ × ℝ ↦ fTruncT3 f_t S N p.1 p.2.1 p.2.2 := by
  simp only [fTruncT3]
  exact (hf_t_cont.comp (continuous_cut_triple S N)).mul
    ((S.continuous_cutD1 N).comp continuous_fst)

lemma fTruncX3_continuous (S : SmoothTrunc) (N : ℕ)
    (hf_x_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_x p.1 p.2.1 p.2.2) :
    Continuous fun p : ℝ × ℝ × ℝ ↦ fTruncX3 f_x S N p.1 p.2.1 p.2.2 := by
  simp only [fTruncX3]
  exact (hf_x_cont.comp (continuous_cut_triple S N)).mul
    ((S.continuous_cutD1 N).comp continuous_snd.fst)

lemma fTruncY3_continuous (S : SmoothTrunc) (N : ℕ)
    (hf_y_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_y p.1 p.2.1 p.2.2) :
    Continuous fun p : ℝ × ℝ × ℝ ↦ fTruncY3 f_y S N p.1 p.2.1 p.2.2 := by
  simp only [fTruncY3]
  exact (hf_y_cont.comp (continuous_cut_triple S N)).mul
    ((S.continuous_cutD1 N).comp continuous_snd.snd)

lemma fTruncXX3_continuous (S : SmoothTrunc) (N : ℕ)
    (hf_x_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_x p.1 p.2.1 p.2.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_xx p.1 p.2.1 p.2.2) :
    Continuous fun p : ℝ × ℝ × ℝ ↦ fTruncXX3 f_x f_xx S N p.1 p.2.1 p.2.2 := by
  simp only [fTruncXX3]
  refine ((hf_xx_cont.comp (continuous_cut_triple S N)).mul
    (((S.continuous_cutD1 N).comp continuous_snd.fst).mul
      ((S.continuous_cutD1 N).comp continuous_snd.fst))).add ?_
  exact (hf_x_cont.comp (continuous_cut_triple S N)).mul
    ((S.continuous_cutD2 N).comp continuous_snd.fst)

lemma fTruncXY3_continuous (S : SmoothTrunc) (N : ℕ)
    (hf_xy_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_xy p.1 p.2.1 p.2.2) :
    Continuous fun p : ℝ × ℝ × ℝ ↦ fTruncXY3 f_xy S N p.1 p.2.1 p.2.2 := by
  simp only [fTruncXY3]
  exact ((hf_xy_cont.comp (continuous_cut_triple S N)).mul
    ((S.continuous_cutD1 N).comp continuous_snd.snd)).mul
    ((S.continuous_cutD1 N).comp continuous_snd.fst)

lemma fTruncYY3_continuous (S : SmoothTrunc) (N : ℕ)
    (hf_y_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_y p.1 p.2.1 p.2.2)
    (hf_yy_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_yy p.1 p.2.1 p.2.2) :
    Continuous fun p : ℝ × ℝ × ℝ ↦ fTruncYY3 f_y f_yy S N p.1 p.2.1 p.2.2 := by
  simp only [fTruncYY3]
  refine ((hf_yy_cont.comp (continuous_cut_triple S N)).mul
    (((S.continuous_cutD1 N).comp continuous_snd.snd).mul
      ((S.continuous_cutD1 N).comp continuous_snd.snd))).add ?_
  exact (hf_y_cont.comp (continuous_cut_triple S N)).mul
    ((S.continuous_cutD2 N).comp continuous_snd.snd)

/-! ### Cut inactivity -/

/-- On the inert region `fTrunc3 N = f`. -/
lemma fTrunc3_eq_of (S : SmoothTrunc) {N : ℕ} {s x y : ℝ} (hs : |s| ≤ (N : ℝ))
    (hx : |x| ≤ (N : ℝ)) (hy : |y| ≤ (N : ℝ)) : fTrunc3 f S N s x y = f s x y := by
  unfold fTrunc3
  rw [(cut_inactive S hs).1, (cut_inactive S hx).1, (cut_inactive S hy).1]

/-- On the inert region `fTruncT3 N = f_t`. -/
lemma fTruncT3_eq_of (S : SmoothTrunc) {N : ℕ} {s x y : ℝ} (hs : |s| ≤ (N : ℝ))
    (hx : |x| ≤ (N : ℝ)) (hy : |y| ≤ (N : ℝ)) : fTruncT3 f_t S N s x y = f_t s x y := by
  rw [fTruncT3, (cut_inactive S hs).1, (cut_inactive S hx).1, (cut_inactive S hy).1,
    (cut_inactive S hs).2.1, mul_one]

/-- On the inert region `fTruncX3 N = f_x`. -/
lemma fTruncX3_eq_of (S : SmoothTrunc) {N : ℕ} {s x y : ℝ} (hs : |s| ≤ (N : ℝ))
    (hx : |x| ≤ (N : ℝ)) (hy : |y| ≤ (N : ℝ)) : fTruncX3 f_x S N s x y = f_x s x y := by
  rw [fTruncX3, (cut_inactive S hs).1, (cut_inactive S hx).1, (cut_inactive S hy).1,
    (cut_inactive S hx).2.1, mul_one]

/-- On the inert region `fTruncY3 N = f_y`. -/
lemma fTruncY3_eq_of (S : SmoothTrunc) {N : ℕ} {s x y : ℝ} (hs : |s| ≤ (N : ℝ))
    (hx : |x| ≤ (N : ℝ)) (hy : |y| ≤ (N : ℝ)) : fTruncY3 f_y S N s x y = f_y s x y := by
  rw [fTruncY3, (cut_inactive S hs).1, (cut_inactive S hx).1, (cut_inactive S hy).1,
    (cut_inactive S hy).2.1, mul_one]

/-- On the inert region `fTruncXX3 N = f_xx`. -/
lemma fTruncXX3_eq_of (S : SmoothTrunc) {N : ℕ} {s x y : ℝ} (hs : |s| ≤ (N : ℝ))
    (hx : |x| ≤ (N : ℝ)) (hy : |y| ≤ (N : ℝ)) :
    fTruncXX3 f_x f_xx S N s x y = f_xx s x y := by
  rw [fTruncXX3, (cut_inactive S hs).1, (cut_inactive S hx).1, (cut_inactive S hy).1,
    (cut_inactive S hx).2.1, (cut_inactive S hx).2.2]
  ring

/-- On the inert region `fTruncXY3 N = f_xy`. -/
lemma fTruncXY3_eq_of (S : SmoothTrunc) {N : ℕ} {s x y : ℝ} (hs : |s| ≤ (N : ℝ))
    (hx : |x| ≤ (N : ℝ)) (hy : |y| ≤ (N : ℝ)) :
    fTruncXY3 f_xy S N s x y = f_xy s x y := by
  rw [fTruncXY3, (cut_inactive S hs).1, (cut_inactive S hx).1, (cut_inactive S hy).1,
    (cut_inactive S hx).2.1, (cut_inactive S hy).2.1, mul_one, mul_one]

/-- On the inert region `fTruncYY3 N = f_yy`. -/
lemma fTruncYY3_eq_of (S : SmoothTrunc) {N : ℕ} {s x y : ℝ} (hs : |s| ≤ (N : ℝ))
    (hx : |x| ≤ (N : ℝ)) (hy : |y| ≤ (N : ℝ)) :
    fTruncYY3 f_y f_yy S N s x y = f_yy s x y := by
  rw [fTruncYY3, (cut_inactive S hs).1, (cut_inactive S hx).1, (cut_inactive S hy).1,
    (cut_inactive S hy).2.1, (cut_inactive S hy).2.2]
  ring

end SummitC

end MathFin
