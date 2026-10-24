/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.SmoothPricingComparison

/-! # Local smooth comparison and identification for the actual stopping price

Existence of a smooth Dirichlet solution is not assumed silently: the final
identification theorem takes that comparator and its PDE/boundary data explicitly.

## Result

Public entry points include `pricingOperator_neg`, `canonicalPrice_smooth_subsolution`,
`neg_canonicalPrice_smooth_subsolution`, `canonicalPrice_le_smooth_on_cylinder`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory
open scoped Topology NNReal

theorem pricingOperator_neg (k h : ℝ) (F : ℝ × ℝ → ℝ) (z : ℝ × ℝ) :
    pricingOperator k h (fun y => -F y) z = -pricingOperator k h F z := by
  simp only [pricingOperator,deriv.fun_neg']
  ring

theorem canonicalPrice_smooth_subsolution {k h : ℝ} (hk : 0 ≤ k) :
    SmoothPricingSubsolutionOn k h (fun z => canonicalPrice k h z.1 z.2)
      (canonicalContinuationRegion k h) := by
  intro z hz F hF h0 htouch
  have ht : 0 ≤ z.2 := hz.1.le
  have hh := canonicalPrice_upper_pricing_test (T := z.2.toNNReal) hk
    (by simpa only [Real.coe_toNNReal _ ht] using hz) hF
    (by simpa only [Real.coe_toNNReal _ ht] using h0)
    (by simpa only [Real.coe_toNNReal _ ht] using htouch)
  simp only [Real.coe_toNNReal _ ht] at hh
  unfold pricingOperator
  linarith

theorem neg_canonicalPrice_smooth_subsolution {k h : ℝ} (hk : 0 ≤ k) :
    SmoothPricingSubsolutionOn k h (fun z => -canonicalPrice k h z.1 z.2)
      (canonicalContinuationRegion k h) := by
  intro z hz F hF h0 htouch
  have ht : 0 ≤ z.2 := hz.1.le
  have h0' : -F z = canonicalPrice k h z.1 z.2 := by linarith
  have htouch' : ∀ᶠ y in 𝓝 z, -F y ≤ canonicalPrice k h y.1 y.2 := by
    filter_upwards [htouch] with y hy
    linarith
  have hh := canonicalPrice_lower_pricing_test (T := z.2.toNNReal) hk
    (by simpa only [Real.coe_toNNReal _ ht] using hz) hF.neg
    (by simpa only [Real.coe_toNNReal _ ht] using h0')
    (by simpa only [Real.coe_toNNReal _ ht] using htouch')
  have ho : 0 ≤ pricingOperator k h (fun y => -F y) z := by
    simp only [Real.coe_toNNReal _ ht] at hh
    unfold pricingOperator
    linarith
  rw [pricingOperator_neg] at ho
  linarith

theorem canonicalPrice_le_smooth_on_cylinder {k h : ℝ} (hk : 0 ≤ k)
    {F : ℝ × ℝ → ℝ} {L R a T : ℝ} (haT : a < T)
    (hcont : Ioo L R ×ˢ Ioo a T ⊆ canonicalContinuationRegion k h)
    (hF : ContinuousOn F (Icc L R ×ˢ Icc a T))
    (hFs : ContDiffOn ℝ 3 F (Ioo L R ×ˢ Ioo a T))
    (hpde : ∀ z ∈ Ioo L R ×ˢ Ioo a T, 0 ≤ pricingOperator k h F z)
    (hbottom : ∀ x ∈ Icc L R, canonicalPrice k h x a ≤ F (x, a))
    (hleft : ∀ t ∈ Icc a T, canonicalPrice k h L t ≤ F (L, t))
    (hright : ∀ t ∈ Icc a T, canonicalPrice k h R t ≤ F (R, t)) :
    ∀ z ∈ Icc L R ×ˢ Icc a T, canonicalPrice k h z.1 z.2 ≤ F z :=
  smoothPricingSubsolution_le hk haT (canonicalPrice_continuous hk).continuousOn hF hFs
    (fun z hz => canonicalPrice_smooth_subsolution hk z (hcont hz)) hpde hbottom hleft hright

theorem smooth_le_canonicalPrice_on_cylinder {k h : ℝ} (hk : 0 ≤ k)
    {F : ℝ × ℝ → ℝ} {L R a T : ℝ} (haT : a < T)
    (hcont : Ioo L R ×ˢ Ioo a T ⊆ canonicalContinuationRegion k h)
    (hF : ContinuousOn F (Icc L R ×ˢ Icc a T))
    (hFs : ContDiffOn ℝ 3 F (Ioo L R ×ˢ Ioo a T))
    (hpde : ∀ z ∈ Ioo L R ×ˢ Ioo a T, pricingOperator k h F z ≤ 0)
    (hbottom : ∀ x ∈ Icc L R, F (x, a) ≤ canonicalPrice k h x a)
    (hleft : ∀ t ∈ Icc a T, F (L, t) ≤ canonicalPrice k h L t)
    (hright : ∀ t ∈ Icc a T, F (R, t) ≤ canonicalPrice k h R t) :
    ∀ z ∈ Icc L R ×ˢ Icc a T, F z ≤ canonicalPrice k h z.1 z.2 := by
  have hh := smoothPricingSubsolution_le hk haT (canonicalPrice_continuous hk).neg.continuousOn
    hF.neg hFs.neg (fun z hz => neg_canonicalPrice_smooth_subsolution hk z (hcont hz))
    (fun z hz => by
      change 0 ≤ pricingOperator k h (fun y => -F y) z
      rw [pricingOperator_neg]
      exact neg_nonneg.mpr (hpde z hz))
    (fun x hx => neg_le_neg (hbottom x hx)) (fun t ht => neg_le_neg (hleft t ht))
    (fun t ht => neg_le_neg (hright t ht))
  intro z hz
  exact neg_le_neg_iff.mp (hh z hz)

/-- A continuous, interior-C3 solution with the actual price's initial/lateral
data equals that price throughout the closed cylinder. Existence is separate. -/
theorem canonicalPrice_eq_smooth_on_cylinder {k h : ℝ} (hk : 0 ≤ k)
    {F : ℝ × ℝ → ℝ} {L R a T : ℝ} (haT : a < T)
    (hcont : Ioo L R ×ˢ Ioo a T ⊆ canonicalContinuationRegion k h)
    (hF : ContinuousOn F (Icc L R ×ˢ Icc a T))
    (hFs : ContDiffOn ℝ 3 F (Ioo L R ×ˢ Ioo a T))
    (hpde : ∀ z ∈ Ioo L R ×ˢ Ioo a T, pricingOperator k h F z = 0)
    (hbottom : ∀ x ∈ Icc L R, F (x, a) = canonicalPrice k h x a)
    (hleft : ∀ t ∈ Icc a T, F (L, t) = canonicalPrice k h L t)
    (hright : ∀ t ∈ Icc a T, F (R, t) = canonicalPrice k h R t) :
    ∀ z ∈ Icc L R ×ˢ Icc a T, canonicalPrice k h z.1 z.2 = F z := by
  have hu := canonicalPrice_le_smooth_on_cylinder hk haT hcont hF hFs
    (fun z hz => (hpde z hz).ge) (fun x hx => (hbottom x hx).ge)
    (fun t ht => (hleft t ht).ge) (fun t ht => (hright t ht).ge)
  have hl := smooth_le_canonicalPrice_on_cylinder hk haT hcont hF hFs
    (fun z hz => (hpde z hz).le) (fun x hx => (hbottom x hx).le)
    (fun t ht => (hleft t ht).le) (fun t ht => (hright t ht).le)
  exact fun z hz => le_antisymm (hu z hz) (hl z hz)

end MathFin.BlackScholes.AmericanPut.Stopping
