/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Mathlib.Geometry.Manifold.SmoothApprox
public import MathFin.BlackScholes.AmericanPut.Stopping.LocalizationTimes

/-! # Uniformly bounded smooth compact minorants of a continuous payoff

The minorants need not be nonnegative or monotone in the sequence index.
Their common absolute bound is what permits dominated convergence.

## Result

Public entry points include `exists_smooth_compact_minorant`,
`exists_smooth_compact_minorant_sequence`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter Metric
open scoped Topology

theorem exists_smooth_compact_minorant {f : ℝ → ℝ}
    (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ m : ℝ → ℝ, ContDiff ℝ 2 m ∧ HasCompactSupport m ∧
      (∀ x, m x ≤ f x) ∧ (∀ x, ‖m x‖ ≤ 2) ∧
      (∀ x, |x| ≤ R → |m x-f x| ≤ 2*ε) := by
  let χ : ContDiffBump (0 : ℝ) :=
    { rIn := R, rOut := 2*R, rIn_pos := hR, rIn_lt_rOut := by linarith }
  let φ : ContDiffBump (0 : ℝ) :=
    { rIn := 2*R, rOut := 3*R, rIn_pos := by linarith, rIn_lt_rOut := by linarith }
  let F : ℝ → ℝ := fun x => χ x*f x
  have hF : Continuous F := χ.continuous.mul hf
  have hFc : HasCompactSupport F := χ.hasCompactSupport.mul_right
  obtain ⟨g,hg,happrox,hsupp⟩ := hF.exists_contDiff_approx 2
    (continuous_const : Continuous (fun _ : ℝ => ε)) (fun _ => hε)
  have hF0 (x : ℝ) : 0 ≤ F x := mul_nonneg χ.nonneg (hf0 x)
  have hFle (x : ℝ) : F x ≤ f x := by
    exact (mul_le_mul_of_nonneg_right χ.le_one (hf0 x)).trans_eq (one_mul _)
  have hgerr (x : ℝ) : |g x-F x| < ε := by
    simpa only [Real.dist_eq] using happrox x
  have hφ (x : ℝ) (hx : g x ≠ 0) : φ x = 1 := by
    have hxF : F x ≠ 0 := hsupp hx
    have hxχ : χ x ≠ 0 := fun h => hxF (by simp [F,h])
    have hball : x ∈ ball (0 : ℝ) (2*R) := by
      exact χ.support_eq ▸ hxχ
    have hxlt : |x| < 2*R := by
      simpa only [mem_ball,Real.dist_eq,sub_zero] using hball
    exact φ.one_of_mem_closedBall (by simpa using hxlt.le)
  have hφsmooth : ContDiff ℝ 2 (fun x => ε*φ x) := contDiff_const.mul φ.contDiff
  refine ⟨fun x => g x-ε*φ x, hg.sub hφsmooth,
    (hFc.mono hsupp).sub (φ.hasCompactSupport.mul_left), ?_, ?_, ?_⟩
  · intro x
    dsimp only
    by_cases hx : g x = 0
    · have hφ0 : 0 ≤ φ x := φ.nonneg
      rw [hx]
      nlinarith [hf0 x]
    · rw [hφ x hx]
      have hh := (abs_lt.mp (hgerr x)).2
      linarith [hFle x]
  · intro x
    rw [Real.norm_eq_abs,abs_le]
    have he := abs_lt.mp (hgerr x)
    have hφ0 : 0 ≤ φ x := φ.nonneg
    have hφ1 : φ x ≤ 1 := φ.le_one
    constructor <;> nlinarith [hF0 x,hFle x,hf1 x]
  · intro x hx
    dsimp only
    have hχ1 : χ x = 1 := χ.one_of_mem_closedBall (by simpa using hx)
    have hφ1 : φ x = 1 := φ.one_of_mem_closedBall (by
      change dist x 0 ≤ 2*R
      simpa only [Real.dist_eq,sub_zero] using (show |x| ≤ 2*R by linarith))
    have he := abs_lt.mp (hgerr x)
    simp only [F,hχ1,one_mul] at he
    rw [hφ1,mul_one,abs_le]
    constructor <;> linarith

theorem exists_smooth_compact_minorant_sequence {f : ℝ → ℝ}
    (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    ∃ m : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ 2 (m n)) ∧
      (∀ n, HasCompactSupport (m n)) ∧ (∀ n x, m n x ≤ f x) ∧
      (∀ n x, ‖m n x‖ ≤ 2) ∧ (∀ x, Tendsto (fun n => m n x) atTop (𝓝 (f x))) := by
  have hex (n : ℕ) := exists_smooth_compact_minorant hf hf0 hf1
    (show 0 < (n : ℝ)+1 by positivity) (localizationEps_pos n)
    (show localizationEps n ≤ 1 by
      unfold localizationEps
      exact inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]))
  choose m hm hc hle hb herr using hex
  refine ⟨m,hm,hc,hle,hb,?_⟩
  intro x
  have hR : ∀ᶠ n : ℕ in atTop, |x| ≤ (n : ℝ)+1 :=
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop |x|)
  have he : Tendsto (fun n => 2*localizationEps n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul localizationEps_tendsto
  have hnorm : Tendsto (fun n => ‖m n x-f x‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg (m n x-f x))) ?_ he
    filter_upwards [hR] with n hn
    simpa only [Real.norm_eq_abs] using herr n x hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

end MathFin.BlackScholes.AmericanPut.Stopping
