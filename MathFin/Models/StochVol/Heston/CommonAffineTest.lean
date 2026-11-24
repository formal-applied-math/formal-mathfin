/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Models.StochVol.Heston.CommonAffineCalc
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Cut-off affine exponential test functions on the clock–price–variance space

For a real-linear functional `ℓ : ℂ →L[ℝ] ℝ` (real or imaginary part) we build compactly
supported `C²` functions on `Fin 3 → ℝ` that agree with
`ℓ (exp (C(T - t) + u x + D(T - t) v))` on a box, and compute their partial derivatives
there.

## Main definitions

* `cutoff`
* `InPlateau`
* `affTest`

## Main results

* `drift_affTest_eq_zero`
* `itoTest_affTest`
* `affTest_eq_of_plateau`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

noncomputable section
namespace MathFin.Heston
open MathFin.FilteredIto
namespace CommonAffine

open MeasureTheory Filter Topology Set
open MathFin.FilteredIto.CommonIto
open scoped NNReal ENNReal

section Test
variable (p : Parameters) (u w : ℂ) (T : ℝ)

/-- The space-time affine exponential `(t, x, v) ↦ exp(C(T - t) + u x + D(T - t) v)`. -/
def affST (y : Fin 3 → ℝ) : ℂ := globalAffineTransform p u w (y 1) (y 2) (T - y 0)

lemma affST_line_one (y : Fin 3 → ℝ) (s : ℝ) :
    affST p u w T (y + s • (Pi.single 1 1 : Fin 3 → ℝ))
      = affST p u w T y * Complex.exp (u * s) := by
  simp only [affST, globalAffineTransform, ← Complex.exp_add]
  congr 1
  simp
  ring

lemma affST_line_two (y : Fin 3 → ℝ) (s : ℝ) :
    affST p u w T (y + s • (Pi.single 2 1 : Fin 3 → ℝ))
      = affST p u w T y * Complex.exp (globalLaplaceD p u w (T - y 0) * s) := by
  simp only [affST, globalAffineTransform, ← Complex.exp_add]
  congr 1
  simp
  ring

lemma affST_line_zero (y : Fin 3 → ℝ) (s : ℝ) :
    affST p u w T (y + s • (Pi.single 0 1 : Fin 3 → ℝ))
      = Complex.exp (globalLaplaceC p u w (T - y 0 - s) + u * (y 1 : ℂ)
          + globalLaplaceD p u w (T - y 0 - s) * (y 2 : ℂ)) := by
  simp only [affST, globalAffineTransform]
  congr 1
  simp
  ring_nf

/-- Derivative along `e₁`. -/
lemma hasDerivAt_affST_one (y : Fin 3 → ℝ) :
    HasDerivAt (fun s : ℝ ↦ affST p u w T (y + s • (Pi.single 1 1 : Fin 3 → ℝ)))
      (affST p u w T y * u) 0 := by
  have h : HasDerivAt (fun s : ℝ ↦ affST p u w T y * Complex.exp (u * s))
      (affST p u w T y * (Complex.exp (u * ((0 : ℝ) : ℂ)) * (u * 1))) 0 :=
    (((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul u).cexp).const_mul _
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, mul_one] at h
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun s => affST_line_one p u w T y s)

/-- Derivative along `e₂`. -/
lemma hasDerivAt_affST_two (y : Fin 3 → ℝ) :
    HasDerivAt (fun s : ℝ ↦ affST p u w T (y + s • (Pi.single 2 1 : Fin 3 → ℝ)))
      (affST p u w T y * globalLaplaceD p u w (T - y 0)) 0 := by
  have h : HasDerivAt
      (fun s : ℝ ↦ affST p u w T y * Complex.exp (globalLaplaceD p u w (T - y 0) * s))
      (affST p u w T y * (Complex.exp (globalLaplaceD p u w (T - y 0) * ((0 : ℝ) : ℂ))
        * (globalLaplaceD p u w (T - y 0) * 1))) 0 :=
    (((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul _).cexp).const_mul _
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, mul_one] at h
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun s => affST_line_two p u w T y s)

/-- Derivative along the clock direction `e₀`, at times with `T - t ≥ 0`. -/
lemma hasDerivAt_affST_zero (hξ : 0 < p.xi) (hρ : |p.rho| ≤ 1)
    (hu : inClosedLaplaceStrip u) (hw : w.re ≤ 0) (y : Fin 3 → ℝ) (hy : y 0 ≤ T) :
    HasDerivAt (fun s : ℝ ↦ affST p u w T (y + s • (Pi.single 0 1 : Fin 3 → ℝ)))
      (affST p u w T y * (-(laplaceCarry p u + modelA p * globalLaplaceD p u w (T - y 0))
        - laplaceRhs p u (globalLaplaceD p u w (T - y 0)) * (y 2 : ℂ))) 0 := by
  have hτ : 0 ≤ T - y 0 := sub_nonneg.2 hy
  have hlin : HasDerivAt (fun s : ℝ ↦ T - y 0 - s) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_sub (T - y 0)
  have hC := (hasDerivAt_globalLaplaceC p u w hξ hρ hu hw (T - y 0) hτ)
  have hD := (hasDerivAt_globalLaplaceD p u w hξ hρ hu hw (T - y 0) hτ)
  have hτ0 : T - y 0 = T - y 0 - 0 := by ring
  have hC' := HasDerivAt.scomp_of_eq (x := (0 : ℝ)) hC hlin hτ0
  have hD' := HasDerivAt.scomp_of_eq (x := (0 : ℝ)) hD hlin hτ0
  have hsum := ((hC'.add_const (u * (y 1 : ℂ))).add (hD'.mul_const (y 2 : ℂ))).cexp
  refine (hsum.congr_deriv ?_).congr_of_eventuallyEq
    (Eventually.of_forall fun s => affST_line_zero p u w T y s)
  simp only [affST, globalAffineTransform, Function.comp, Pi.add_apply, sub_zero, neg_one_smul]
  ring

end Test
/-! ### Cut-offs -/

section Cutoff

/-- Clock cut-off: equal to `1` on `[-δ/3, T + δ/3]`, vanishing outside `(-2δ/3, T + 2δ/3)`. -/
def timeBump (T δ : ℝ) (hT : 0 ≤ T) (hδ : 0 < δ) : ContDiffBump (T / 2) where
  rIn := T / 2 + δ / 3
  rOut := T / 2 + 2 * δ / 3
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- Space cut-off: equal to `1` on `[-(n+1), n+1]`, vanishing outside `(-(n+2), n+2)`. -/
def spaceBump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := n + 1
  rOut := n + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- The product cut-off on `Fin 3 → ℝ`. -/
def cutoff (T δ : ℝ) (hT : 0 ≤ T) (hδ : 0 < δ) (n : ℕ) (y : Fin 3 → ℝ) : ℝ :=
  timeBump T δ hT hδ (y 0) * spaceBump n (y 1) * spaceBump n (y 2)

variable (T δ : ℝ) (hT : 0 ≤ T) (hδ : 0 < δ) (n : ℕ)

lemma contDiff_cutoff : ContDiff ℝ 2 (cutoff T δ hT hδ n) := by
  have h0 := (timeBump T δ hT hδ).contDiff (n := 2) |>.comp (contDiff_apply ℝ (fun _ : Fin 3 ↦
        ℝ) (0 : Fin 3))
  have h1 := (spaceBump n).contDiff (n := 2) |>.comp (contDiff_apply ℝ (fun _ : Fin 3 ↦ ℝ) (1 :
        Fin 3))
  have h2 := (spaceBump n).contDiff (n := 2) |>.comp (contDiff_apply ℝ (fun _ : Fin 3 ↦ ℝ) (2 :
        Fin 3))
  exact (h0.mul h1).mul h2

/-- The open plateau on which the cut-off equals one. -/
def InPlateau (y : Fin 3 → ℝ) : Prop :=
  |y 0 - T / 2| < T / 2 + δ / 3 ∧ |y 1| < n + 1 ∧ |y 2| < n + 1

lemma isOpen_plateau : IsOpen {y : Fin 3 → ℝ | InPlateau T δ n y} := by
  have h0 : Continuous fun y : Fin 3 → ℝ ↦ |y 0 - T / 2| :=
    continuous_abs.comp ((continuous_apply (0 : Fin 3)).sub continuous_const)
  have h1 : Continuous fun y : Fin 3 → ℝ ↦ |y 1| := continuous_abs.comp (continuous_apply (1 :
        Fin 3))
  have h2 : Continuous fun y : Fin 3 → ℝ ↦ |y 2| := continuous_abs.comp (continuous_apply (2 :
        Fin 3))
  exact (isOpen_lt h0 continuous_const).inter
    ((isOpen_lt h1 continuous_const).inter (isOpen_lt h2 continuous_const))

lemma cutoff_eq_one {y : Fin 3 → ℝ} (hy : InPlateau T δ n y) : cutoff T δ hT hδ n y = 1 := by
  obtain ⟨h0, h1, h2⟩ := hy
  have e0 : timeBump T δ hT hδ (y 0) = 1 := (timeBump T δ hT hδ).one_of_mem_closedBall (by
    rw [Metric.mem_closedBall, Real.dist_eq]; exact h0.le)
  have e1 : spaceBump n (y 1) = 1 := (spaceBump n).one_of_mem_closedBall (by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact h1.le)
  have e2 : spaceBump n (y 2) = 1 := (spaceBump n).one_of_mem_closedBall (by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact h2.le)
  simp only [cutoff, e0, e1, e2, mul_one]

lemma cutoff_eq_zero_of_time {y : Fin 3 → ℝ} (hy : T + 2 * δ / 3 ≤ y 0) :
    cutoff T δ hT hδ n y = 0 := by
  have h : timeBump T δ hT hδ (y 0) = 0 := (timeBump T δ hT hδ).zero_of_le_dist (by
    show T / 2 + 2 * δ / 3 ≤ dist (y 0) (T / 2)
    rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith)
  simp only [cutoff, h, zero_mul]

lemma cutoff_eq_zero_of_norm {y : Fin 3 → ℝ} (hy : T + δ + n + 2 < ‖y‖) :
    cutoff T δ hT hδ n y = 0 := by
  have hex : ∃ i, T + δ + n + 2 < |y i| := by
    by_contra h
    simp only [not_exists, not_lt] at h
    have : ‖y‖ ≤ T + δ + n + 2 :=
      (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => by rw [Real.norm_eq_abs]; exact h i
    linarith
  obtain ⟨i, hi⟩ := hex
  fin_cases i
  · have hi0 : T + δ + n + 2 < |y 0| := hi
    have h : timeBump T δ hT hδ (y 0) = 0 := (timeBump T δ hT hδ).zero_of_le_dist (by
      show T / 2 + 2 * δ / 3 ≤ dist (y 0) (T / 2)
      have := abs_sub_abs_le_abs_sub (y 0) (T / 2)
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ T / 2)] at this
      rw [Real.dist_eq]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)
    simp only [cutoff, h, zero_mul]
  · have hi1 : T + δ + n + 2 < |y 1| := hi
    have h : spaceBump n (y 1) = 0 := (spaceBump n).zero_of_le_dist (by
      show (n : ℝ) + 2 ≤ dist (y 1) 0
      rw [Real.dist_eq, sub_zero]; linarith)
    simp only [cutoff, h, mul_zero, zero_mul]
  · have hi2 : T + δ + n + 2 < |y 2| := hi
    have h : spaceBump n (y 2) = 0 := (spaceBump n).zero_of_le_dist (by
      show (n : ℝ) + 2 ≤ dist (y 2) 0
      rw [Real.dist_eq, sub_zero]; linarith)
    simp only [cutoff, h, mul_zero]

end Cutoff

/-! ### The cut-off test function -/

section AffTest
variable (p : Parameters) (u w : ℂ) (T δ : ℝ) (hT : 0 ≤ T) (hδ : 0 < δ) (n : ℕ)
  (ℓ : ℂ →L[ℝ] ℝ)

/-- `ℓ` of the affine exponential, cut off to a compact set. -/
def affTest (y : Fin 3 → ℝ) : ℝ := cutoff T δ hT hδ n y * ℓ (affST p u w T y)

lemma contDiffAt_affST (hDC : ContDiffOn ℝ 2 (globalLaplaceD p u w) (Ioi (-δ)))
    (hCC : ContDiffOn ℝ 2 (globalLaplaceC p u w) (Ioi (-δ))) {y : Fin 3 → ℝ}
    (hτ : T - y 0 ∈ Ioi (-δ)) : ContDiffAt ℝ 2 (affST p u w T) y := by
  have h0 : ContDiffAt ℝ 2 (fun y : Fin 3 → ℝ ↦ T - y 0) y :=
    contDiffAt_const.sub (contDiff_apply ℝ (fun _ : Fin 3 ↦ ℝ) (0 : Fin 3)).contDiffAt
  have hCa := (hCC.contDiffAt (isOpen_Ioi.mem_nhds hτ)).comp y h0
  have hDa := (hDC.contDiffAt (isOpen_Ioi.mem_nhds hτ)).comp y h0
  have h1 : ContDiffAt ℝ 2 (fun y : Fin 3 → ℝ ↦ ((y 1 : ℝ) : ℂ)) y :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ (fun _ : Fin 3 ↦ ℝ) (1 : Fin 3))).contDiffAt
  have h2 : ContDiffAt ℝ 2 (fun y : Fin 3 → ℝ ↦ ((y 2 : ℝ) : ℂ)) y :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ (fun _ : Fin 3 ↦ ℝ) (2 : Fin 3))).contDiffAt
  exact ((hCa.add (contDiffAt_const.mul h1)).add (hDa.mul h2)).cexp

theorem contDiff_affTest (hDC : ContDiffOn ℝ 2 (globalLaplaceD p u w) (Ioi (-δ)))
    (hCC : ContDiffOn ℝ 2 (globalLaplaceC p u w) (Ioi (-δ))) :
    ContDiff ℝ 2 (affTest p u w T δ hT hδ n ℓ) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  rcases lt_or_ge (y 0) (T + δ) with hy | hy
  · have hτ : T - y 0 ∈ Ioi (-δ) := by simp only [mem_Ioi]; linarith
    exact (contDiff_cutoff T δ hT hδ n).contDiffAt.mul
      (ℓ.contDiff.contDiffAt.comp y (contDiffAt_affST p u w T δ hDC hCC hτ))
  · have hev : affTest p u w T δ hT hδ n ℓ =ᶠ[𝓝 y] fun _ ↦ (0 : ℝ) := by
      have h : ∀ᶠ y' in 𝓝 y, T + 2 * δ / 3 < y' 0 :=
        ((continuous_apply 0).tendsto y).eventually (lt_mem_nhds (by linarith))
      filter_upwards [h] with y' hy'
      simp only [affTest, cutoff_eq_zero_of_time T δ hT hδ n hy'.le, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem hasCompactSupport_affTest : HasCompactSupport (affTest p u w T δ hT hδ n ℓ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin 3 → ℝ) (T + δ + n + 2))
    fun y hy => ?_
  have hR : T + δ + n + 2 < ‖y‖ := by
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy; exact hy
  simp only [affTest, cutoff_eq_zero_of_norm T δ hT hδ n hR, zero_mul]

lemma affTest_eventuallyEq {y : Fin 3 → ℝ} (hy : InPlateau T δ n y) :
    affTest p u w T δ hT hδ n ℓ =ᶠ[𝓝 y] fun y' ↦ ℓ (affST p u w T y') := by
  filter_upwards [(isOpen_plateau T δ n).mem_nhds hy] with y' hy'
  simp only [affTest, cutoff_eq_one T δ hT hδ n hy', one_mul]

lemma tendsto_line (y : Fin 3 → ℝ) (i : Fin 3) :
    Tendsto (fun s : ℝ ↦ y + s • (Pi.single i 1 : Fin 3 → ℝ)) (𝓝 0) (𝓝 y) := by
  have := (hasDerivAt_line y i).continuousAt.tendsto
  simpa using this

variable {p u w T δ hT hδ n ℓ}

lemma pd_affTest_of (hdiff : ContDiff ℝ 2 (affTest p u w T δ hT hδ n ℓ)) {y : Fin 3 → ℝ}
    (hy : InPlateau T δ n y) {i : Fin 3} {d : ℝ}
    (h : HasDerivAt (fun s : ℝ ↦ ℓ (affST p u w T (y + s • (Pi.single i 1 : Fin 3 → ℝ)))) d 0) :
    pd (affTest p u w T δ hT hδ n ℓ) i y = d := by
  refine pd_eq_of_hasDerivAt (hdiff.differentiable (by norm_num) y) ?_
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [(tendsto_line y i).eventually
    (affTest_eventuallyEq p u w T δ hT hδ n ℓ hy)] with s hs
  exact hs

lemma pd2_affTest_of (hdiff : ContDiff ℝ 2 (affTest p u w T δ hT hδ n ℓ)) {y : Fin 3 → ℝ}
    (hy : InPlateau T δ n y) {i k : Fin 3} {d : ℝ} {g : (Fin 3 → ℝ) → ℝ}
    (hg : ∀ y', InPlateau T δ n y' → pd (affTest p u w T δ hT hδ n ℓ) k y' = g y')
    (h : HasDerivAt (fun s : ℝ ↦ g (y + s • (Pi.single i 1 : Fin 3 → ℝ))) d 0) :
    pd2 (affTest p u w T δ hT hδ n ℓ) i k y = d := by
  refine pd2_eq_of_hasDerivAt hdiff ?_
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [(tendsto_line y i).eventually ((isOpen_plateau T δ n).mem_nhds hy)] with s hs
  exact hg _ hs

lemma line_coord_zero_one (y : Fin 3 → ℝ) (s : ℝ) :
    (y + s • (Pi.single 1 1 : Fin 3 → ℝ)) 0 = y 0 := by simp

lemma line_coord_zero_two (y : Fin 3 → ℝ) (s : ℝ) :
    (y + s • (Pi.single 2 1 : Fin 3 → ℝ)) 0 = y 0 := by simp

theorem pd_affTest_one (hdiff : ContDiff ℝ 2 (affTest p u w T δ hT hδ n ℓ))
    {y : Fin 3 → ℝ} (hy : InPlateau T δ n y) :
    pd (affTest p u w T δ hT hδ n ℓ) 1 y = ℓ (affST p u w T y * u) :=
  pd_affTest_of hdiff hy (ℓ.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_affST_one p u w T y))

theorem pd_affTest_two (hdiff : ContDiff ℝ 2 (affTest p u w T δ hT hδ n ℓ))
    {y : Fin 3 → ℝ} (hy : InPlateau T δ n y) :
    pd (affTest p u w T δ hT hδ n ℓ) 2 y
      = ℓ (affST p u w T y * globalLaplaceD p u w (T - y 0)) :=
  pd_affTest_of hdiff hy (ℓ.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_affST_two p u w T y))

theorem pd_affTest_zero (hξ : 0 < p.xi) (hρ : |p.rho| ≤ 1) (hu : inClosedLaplaceStrip u)
    (hw : w.re ≤ 0) (hdiff : ContDiff ℝ 2 (affTest p u w T δ hT hδ n ℓ))
    {y : Fin 3 → ℝ} (hy : InPlateau T δ n y) (hyT : y 0 ≤ T) :
    pd (affTest p u w T δ hT hδ n ℓ) 0 y
      = ℓ (affST p u w T y * (-(laplaceCarry p u + modelA p * globalLaplaceD p u w (T - y 0))
        - laplaceRhs p u (globalLaplaceD p u w (T - y 0)) * (y 2 : ℂ))) :=
  pd_affTest_of hdiff hy
    (ℓ.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_affST_zero p u w T hξ hρ hu hw y hyT))

theorem pd2_affTest_11 (hdiff : ContDiff ℝ 2 (affTest p u w T δ hT hδ n ℓ))
    {y : Fin 3 → ℝ} (hy : InPlateau T δ n y) :
    pd2 (affTest p u w T δ hT hδ n ℓ) 1 1 y = ℓ (affST p u w T y * u * u) :=
  pd2_affTest_of hdiff hy (fun _ hy' => pd_affTest_one hdiff hy')
    (ℓ.hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_affST_one p u w T y).mul_const u))

theorem pd2_affTest_12 (hdiff : ContDiff ℝ 2 (affTest p u w T δ hT hδ n ℓ))
    {y : Fin 3 → ℝ} (hy : InPlateau T δ n y) :
    pd2 (affTest p u w T δ hT hδ n ℓ) 1 2 y
      = ℓ (affST p u w T y * u * globalLaplaceD p u w (T - y 0)) := by
  refine pd2_affTest_of hdiff hy (fun _ hy' => pd_affTest_two hdiff hy') ?_
  have h := ℓ.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    ((hasDerivAt_affST_one p u w T y).mul_const (globalLaplaceD p u w (T - y 0)))
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp only [Function.comp, line_coord_zero_one]

theorem pd2_affTest_21 (hdiff : ContDiff ℝ 2 (affTest p u w T δ hT hδ n ℓ))
    {y : Fin 3 → ℝ} (hy : InPlateau T δ n y) :
    pd2 (affTest p u w T δ hT hδ n ℓ) 2 1 y
      = ℓ (affST p u w T y * globalLaplaceD p u w (T - y 0) * u) :=
  pd2_affTest_of hdiff hy (fun _ hy' => pd_affTest_one hdiff hy')
    (ℓ.hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_affST_two p u w T y).mul_const u))

theorem pd2_affTest_22 (hdiff : ContDiff ℝ 2 (affTest p u w T δ hT hδ n ℓ))
    {y : Fin 3 → ℝ} (hy : InPlateau T δ n y) :
    pd2 (affTest p u w T δ hT hδ n ℓ) 2 2 y
      = ℓ (affST p u w T y * globalLaplaceD p u w (T - y 0) * globalLaplaceD p u w (T - y 0)) := by
  refine pd2_affTest_of hdiff hy (fun _ hy' => pd_affTest_two hdiff hy') ?_
  have h := ℓ.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    ((hasDerivAt_affST_two p u w T y).mul_const (globalLaplaceD p u w (T - y 0)))
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp only [Function.comp, line_coord_zero_two]

/-- **The drift of the affine test function vanishes on the plateau** (Riccati equations). -/
theorem drift_affTest_eq_zero (hξ : 0 < p.xi) (hρ : |p.rho| ≤ 1) (hu : inClosedLaplaceStrip u)
    (hw : w.re ≤ 0) (hdiff : ContDiff ℝ 2 (affTest p u w T δ hT hδ n ℓ)) {ρ' : ℝ}
    (hρ' : p.rho ^ 2 + ρ' ^ 2 = 1) {y : Fin 3 → ℝ} (hy : InPlateau T δ n y) (hyT : y 0 ≤ T)
    (hv : 0 ≤ y 2) {a b c : Fin 3 → ℝ} (ha0 : a 0 = 1) (ha1 : a 1 = (p.r - p.q) - (1 / 2 : ℝ) * y 2)
    (ha2 : a 2 = p.kappa * (p.theta - y 2)) (hb0 : b 0 = 0) (hb1 : b 1 = p.rho * Real.sqrt (y 2))
    (hb2 : b 2 = p.xi * Real.sqrt (y 2)) (hc0 : c 0 = 0) (hc1 : c 1 = ρ' * Real.sqrt (y 2))
    (hc2 : c 2 = 0) :
    ∑ i, pd (affTest p u w T δ hT hδ n ℓ) i y * a i
      + (1 / 2) * ∑ i, ∑ k, pd2 (affTest p u w T δ hT hδ n ℓ) i k y * (b i * b k + c i * c k)
      = 0 := by
  have e0 := pd_affTest_zero hξ hρ hu hw hdiff hy hyT
  have e1 := pd_affTest_one hdiff hy
  have e2 := pd_affTest_two hdiff hy
  have e11 := pd2_affTest_11 hdiff hy
  have e12 := pd2_affTest_12 hdiff hy
  have e21 := pd2_affTest_21 hdiff hy
  have e22 := pd2_affTest_22 hdiff hy
  simp only [Fin.sum_univ_three, ha0, ha1, ha2, hb0, hb1, hb2, hc0, hc1, hc2, zero_mul, mul_zero,
    add_zero, zero_add, mul_one]
  rw [e0, e1, e2, e11, e12, e21, e22]
  set G := affST p u w T y with hG
  set Dv := globalLaplaceD p u w (T - y 0) with hDv
  set s := Real.sqrt (y 2) with hs
  have hss : s * s = y 2 := Real.mul_self_sqrt hv
  have hss' : (s : ℂ) * (s : ℂ) = (y 2 : ℂ) := by exact_mod_cast hss
  have hρ'' : (p.rho : ℂ) ^ 2 + (ρ' : ℂ) ^ 2 = 1 := by exact_mod_cast hρ'
  have hE : (1 : ℝ) • (G * (-(laplaceCarry p u + modelA p * Dv) - laplaceRhs p u Dv * (y 2 : ℂ)))
      + ((p.r - p.q) - (1 / 2 : ℝ) * y 2) • (G * u) + (p.kappa * (p.theta - y 2)) • (G * Dv)
      + (1 / 2 : ℝ) • ((p.rho * s * (p.rho * s) + ρ' * s * (ρ' * s)) • (G * u * u)
        + (p.rho * s * (p.xi * s)) • (G * u * Dv) + (p.xi * s * (p.rho * s)) • (G * Dv * u)
        + (p.xi * s * (p.xi * s)) • (G * Dv * Dv)) = 0 := by
    simp only [Complex.real_smul, laplaceCarry, modelA, laplaceRhs, laplaceA, laplaceB,
      laplaceConstant]
    push_cast
    linear_combination (G * ((p.xi : ℂ) ^ 2 * Dv ^ 2 / 2 + (p.rho : ℂ) * p.xi * u * Dv
      + u ^ 2 / 2)) * hss' + (G * (1 / 2) * u ^ 2 * (s : ℂ) ^ 2) * hρ''
  have hfin := congrArg ℓ hE
  simp only [map_add, map_smul, smul_eq_mul, map_zero] at hfin
  linear_combination hfin

end AffTest

section AffTest2
variable (p : Parameters) (u w : ℂ) (T δ : ℝ) (hT : 0 ≤ T) (hδ : 0 < δ) (n : ℕ)
  (ℓ : ℂ →L[ℝ] ℝ)

/-- The cut-off affine test function is an Itô test function. -/
theorem itoTest_affTest (hDC : ContDiffOn ℝ 2 (globalLaplaceD p u w) (Ioi (-δ)))
    (hCC : ContDiffOn ℝ 2 (globalLaplaceC p u w) (Ioi (-δ))) :
    ∃ C₁ C₂, ItoTest (affTest p u w T δ hT hδ n ℓ) C₁ C₂ :=
  itoTest_of_hasCompactSupport (contDiff_affTest p u w T δ hT hδ n ℓ hDC hCC)
    (hasCompactSupport_affTest p u w T δ hT hδ n ℓ)

/-- On the plateau the test function equals `ℓ` of the affine exponential. -/
lemma affTest_eq_of_plateau {y : Fin 3 → ℝ} (hy : InPlateau T δ n y) :
    affTest p u w T δ hT hδ n ℓ y = ℓ (affST p u w T y) := by
  simp only [affTest, cutoff_eq_one T δ hT hδ n hy, one_mul]

end AffTest2

end CommonAffine
end MathFin.Heston
