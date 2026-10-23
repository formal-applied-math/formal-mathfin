/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.StrictDrift

/-! # Pointwise generator tests for the actual continuation price

Shrinking driver rectangles places both a local touching inequality and a
hypothetical strict wrong generator sign on the entire stopped trajectory.
Strict drift then contradicts the integrated test inequality.

## Result

Public entry points include `exists_driverRectangle_subset`, `exists_continuationRectangle_in_nhds`,
`canonicalPrice_upper_pointwise_test`, `canonicalPrice_lower_pointwise_test`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

theorem exists_driverRectangle_subset (k h : ℝ) {U : Set (ℝ × ℝ)}
    (hU : U ∈ 𝓝 (0, 0)) {R₀ : ℝ} (hR₀ : 0 < R₀)
    {δ₀ : ℝ≥0} (hδ₀ : 0 < δ₀) :
    ∃ R : ℝ, 0 < R ∧ R ≤ R₀ ∧ ∃ δ : ℝ≥0,
      0 < δ ∧ δ ≤ δ₀ ∧ driverRectangle k h R δ ⊆ U := by
  let F : ℝ × ℝ → ℝ × ℝ := fun z => (z.1,(z.2-(k-h-1)*z.1)/Real.sqrt 2)
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hF0 : F (0,0) = (0,0) := by simp [F]
  have hpre : F ⁻¹' U ∈ 𝓝 (0,0) := by
    apply (hF.tendsto (0,0)).eventually
    rwa [hF0]
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hpre
  let R := min R₀ (ε/2)
  let d := min (δ₀ : ℝ) (ε/2)
  have hd : 0 < d := lt_min (by exact_mod_cast hδ₀) (half_pos hε)
  refine ⟨R,lt_min hR₀ (half_pos hε),min_le_left _ _,d.toNNReal,
    Real.toNNReal_pos.mpr hd,?_,?_⟩
  · exact_mod_cast (show (d.toNNReal : ℝ) ≤ δ₀ by
      rw [Real.coe_toNNReal _ hd.le]; exact min_le_left _ _)
  · intro z hz
    let v : ℝ × ℝ := (z.1,(k-h-1)*z.1+Real.sqrt 2*z.2)
    have hv : v ∈ Metric.ball (0,0) ε := by
      change dist v (0,0) < ε
      rw [Prod.dist_eq]
      apply max_lt
      · have htime : z.1 ≤ ε/2 := hz.2.1.trans (by
          rw [Real.coe_toNNReal _ hd.le]; exact min_le_right _ _)
        simpa only [v,Real.dist_eq,sub_zero,abs_of_nonneg hz.1] using
          htime.trans_lt (half_lt_self hε)
      · exact (show dist v.2 0 ≤ ε/2 by
          simpa only [v,Real.dist_eq,sub_zero] using hz.2.2.trans (min_le_right R₀ (ε/2))).trans_lt
          (half_lt_self hε)
    have hinv : F v = z := by
      ext
      · rfl
      · dsimp [F,v]
        field_simp [Real.sqrt_ne_zero'.mpr (show (0 : ℝ) < 2 by norm_num)]
        ring
    have hh := hball hv
    change F v ∈ U at hh
    rwa [hinv] at hh

theorem exists_continuationRectangle_in_nhds {k h x : ℝ} (hk : 0 ≤ k) {T : ℝ≥0}
    (hp : (x, (T : ℝ)) ∈ canonicalContinuationRegion k h)
    {U : Set (ℝ × ℝ)} (hU : U ∈ 𝓝 (0, 0)) :
    ∃ R : ℝ, 0 < R ∧ ∃ δ : ℝ≥0, 0 < δ ∧ δ < T ∧
      InContinuationRectangle k h x T R δ ∧ driverRectangle k h R δ ⊆ U := by
  obtain ⟨R₀,hR₀,δ₀,hδ₀,hδT,hrect⟩ := exists_continuationRectangle hk hp
  obtain ⟨R,hR,hRR,δ,hδ,hδδ,hsub⟩ := exists_driverRectangle_subset k h hU hR₀ hδ₀
  exact ⟨R,hR,δ,hδ,hδδ.trans_lt hδT,
    fun s hs y hy => hrect s (hs.trans hδδ) y (hy.trans hRR),hsub⟩

/-- A compact C3 test touching the discounted actual price from above has
nonnegative backward-driver generator. -/
theorem canonicalPrice_upper_pointwise_test {k h x : ℝ} (hk : 0 ≤ k) {T : ℝ≥0}
    (hp : (x, (T : ℝ)) ∈ canonicalContinuationRegion k h)
    {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 3 G) (hc : HasCompactSupport G)
    (h0 : G (0, 0) = canonicalPrice k h x (T : ℝ))
    (htouch : ∀ᶠ z in 𝓝 (0, 0), canonicalDiscountedPlane k h x T z ≤ G z) :
    0 ≤ planeGenerator G (0,0) := by
  by_contra! hneg
  have hn : ∀ᶠ z in 𝓝 (0,0), planeGenerator G z < 0 :=
    (planeGenerator_continuous hG).continuousAt.eventually_lt_const hneg
  obtain ⟨R,hR,δ,hδ,hδT,hrect,hsub⟩ := exists_continuationRectangle_in_nhds hk hp (htouch.and hn)
  have hnonneg := canonicalPrice_rectangle_upper_test_of_patch hk hR hδ hδT.le hrect hG hc h0
    (fun z hz => (hsub hz).1)
  have hnegative := expected_rectangle_drift_neg k h x hR hδ hG hc (fun z hz => (hsub hz).2)
  exact (not_lt_of_ge hnonneg) hnegative

theorem canonicalPrice_lower_pointwise_test {k h x : ℝ} (hk : 0 ≤ k) {T : ℝ≥0}
    (hp : (x, (T : ℝ)) ∈ canonicalContinuationRegion k h)
    {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 3 G) (hc : HasCompactSupport G)
    (h0 : G (0, 0) = canonicalPrice k h x (T : ℝ))
    (htouch : ∀ᶠ z in 𝓝 (0, 0), G z ≤ canonicalDiscountedPlane k h x T z) :
    planeGenerator G (0,0) ≤ 0 := by
  by_contra! hpos
  have hn : ∀ᶠ z in 𝓝 (0,0), 0 < planeGenerator G z :=
    (planeGenerator_continuous hG).continuousAt.eventually_const_lt hpos
  obtain ⟨R,hR,δ,hδ,hδT,hrect,hsub⟩ := exists_continuationRectangle_in_nhds hk hp (htouch.and hn)
  have hnonpos := canonicalPrice_rectangle_lower_test_of_patch hk hR hδ hδT.le hrect hG hc h0
    (fun z hz => (hsub hz).1)
  have hpositive := expected_rectangle_drift_pos k h x hR hδ hG hc (fun z hz => (hsub hz).2)
  exact (not_lt_of_ge hnonpos) hpositive

theorem planeGenerator_congr {F G : ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    (he : F =ᶠ[𝓝 z] G) : planeGenerator F z = planeGenerator G z := by
  have hx : planePartial F (0,1) =ᶠ[𝓝 z] planePartial G (0,1) :=
    (he.fderiv (𝕜 := ℝ)).fun_comp (fun A : (ℝ × ℝ) →L[ℝ] ℝ => A (0,1))
  have ht : planePartial F (1,0) z = planePartial G (1,0) z :=
    congrArg (fun A : (ℝ × ℝ) →L[ℝ] ℝ => A (1,0)) he.fderiv_eq
  have hxx : planePartial (planePartial F (0,1)) (0,1) z =
      planePartial (planePartial G (0,1)) (0,1) z :=
    congrArg (fun A : (ℝ × ℝ) →L[ℝ] ℝ => A (0,1)) hx.fderiv_eq
  exact congrArg₂ (fun a b : ℝ => a+(1/2)*b) ht hxx

theorem exists_compact_test {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 3 F) (z : ℝ × ℝ) :
    ∃ G : ℝ × ℝ → ℝ, ContDiff ℝ 3 G ∧ HasCompactSupport G ∧ G =ᶠ[𝓝 z] F := by
  let χ : ContDiffBump z := {
    rIn := 1
    rOut := 2
    rIn_pos := by norm_num
    rIn_lt_rOut := by norm_num }
  refine ⟨fun y => χ y*F y,χ.contDiff.mul hF,χ.hasCompactSupport.mul_right,?_⟩
  filter_upwards [χ.eventuallyEq_one] with y hy
  simp only [Pi.one_apply] at hy
  rw [hy,one_mul]

theorem canonicalPrice_upper_generator_test {k h x : ℝ} (hk : 0 ≤ k) {T : ℝ≥0}
    (hp : (x, (T : ℝ)) ∈ canonicalContinuationRegion k h)
    {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    (h0 : F (0, 0) = canonicalPrice k h x (T : ℝ))
    (htouch : ∀ᶠ z in 𝓝 (0, 0), canonicalDiscountedPlane k h x T z ≤ F z) :
    0 ≤ planeGenerator F (0,0) := by
  obtain ⟨G,hG,hc,he⟩ := exists_compact_test hF (0,0)
  rw [← planeGenerator_congr he]
  apply canonicalPrice_upper_pointwise_test hk hp hG hc (he.self_of_nhds.trans h0)
  filter_upwards [htouch,he] with z hz hez
  rwa [hez]

theorem canonicalPrice_lower_generator_test {k h x : ℝ} (hk : 0 ≤ k) {T : ℝ≥0}
    (hp : (x, (T : ℝ)) ∈ canonicalContinuationRegion k h)
    {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    (h0 : F (0, 0) = canonicalPrice k h x (T : ℝ))
    (htouch : ∀ᶠ z in 𝓝 (0, 0), F z ≤ canonicalDiscountedPlane k h x T z) :
    planeGenerator F (0,0) ≤ 0 := by
  obtain ⟨G,hG,hc,he⟩ := exists_compact_test hF (0,0)
  rw [← planeGenerator_congr he]
  apply canonicalPrice_lower_pointwise_test hk hp hG hc (he.self_of_nhds.trans h0)
  filter_upwards [htouch,he] with z hz hez
  rwa [hez]

end MathFin.BlackScholes.AmericanPut.Stopping
