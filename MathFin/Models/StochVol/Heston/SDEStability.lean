/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Models.StochVol.Heston.CIRYamada

/-!
# Gronwall's inequality on `(0,T]` and `L²` stability of Itô processes

`gronwall_timeMeasure`: a bounded, locally integrable `u` with `u(t) ≤ A + C ∫₀ᵗ u` satisfies
`u(t) ≤ A e^{Ct}`; the proof iterates the inequality, `u(t) ≤ A Σ_{k<n} (Ct)^k/k! + M (Ct)^n/n!`.

`norm_sq_l2ItoProcessLp_sub_le`: if two `L²` Itô processes with the same initial value have drift
difference `c · (X - X')`, then `‖X - X'‖² ≤ 2T ‖γ - γ'‖² e^{2Tc²T}` — the band energy of the
difference satisfies the Gronwall inequality.

## Main definitions

* `expPartial`

## Main results

* `bandEnergy_smul`
* `l2ItoProcessLp_sub`
* `norm_sq_l2ItoProcessLp_sub_le`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section
namespace MathFin.Heston
open MathFin.FilteredIto
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open MathFin MathFin.ItoIntegralL2 MathFin.ItoIntegralCLM MathFin.ItoIntegralProcessGeneral
open MathFin.ItoIntegralProcessContinuousModification MathFin.ItoFormulaAdapted
open MathFin.AdaptedDrift MathFin.ItoIntegralAgainstMartingale

/-! ## Gronwall -/

/-- Partial sums of the exponential series. -/
def expPartial (x : ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, x ^ k / (k.factorial : ℝ)

theorem integrableOn_Ioc_of_continuous {f : ℝ≥0 → ℝ} (hf : Continuous f) (t : ℝ≥0) :
    IntegrableOn f (Set.Ioc 0 t) timeMeasure := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ≥0) t)).exists_bound_of_continuousOn
    hf.continuousOn
  refine Measure.integrableOn_of_bounded (M := M) ?_ hf.aestronglyMeasurable ?_
  · rw [timeMeasure_Ioc]; exact ENNReal.ofReal_ne_top
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hM s ⟨zero_le, hs.2⟩

theorem continuous_expPartial_mul (C : ℝ) (n : ℕ) :
    Continuous fun s : ℝ≥0 => expPartial (C * s) n := by
  unfold expPartial
  exact continuous_finsetSum _ fun k _ => by fun_prop

theorem mul_setIntegral_pow_div_factorial (C : ℝ) (n : ℕ) (t : ℝ≥0) :
    C * ∫ s in Set.Ioc (0 : ℝ≥0) t, (C * s) ^ n / (n.factorial : ℝ) ∂timeMeasure
      = (C * t) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  have hfun : (fun s : ℝ≥0 => (C * s) ^ n / (n.factorial : ℝ))
      = fun s : ℝ≥0 => (C ^ n / (n.factorial : ℝ)) * (s : ℝ) ^ n := by
    funext s; rw [mul_pow]; ring
  rw [hfun, integral_const_mul, setIntegral_timeMeasure_pow, Nat.factorial_succ, Nat.cast_mul,
    mul_pow]
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

theorem one_add_mul_setIntegral_expPartial (C : ℝ) (n : ℕ) (t : ℝ≥0) :
    1 + C * ∫ s in Set.Ioc (0 : ℝ≥0) t, expPartial (C * s) n ∂timeMeasure
      = expPartial (C * t) (n + 1) := by
  induction n with
  | zero => simp [expPartial]
  | succ n ih =>
    have hsum : ∀ x : ℝ, expPartial x (n + 1) = expPartial x n + x ^ n / (n.factorial : ℝ) :=
      fun x => Finset.sum_range_succ _ _
    have hi1 : IntegrableOn (fun s : ℝ≥0 => expPartial (C * s) n) (Set.Ioc 0 t) timeMeasure :=
      integrableOn_Ioc_of_continuous (continuous_expPartial_mul C n) t
    have hi2 : IntegrableOn (fun s : ℝ≥0 => (C * s) ^ n / (n.factorial : ℝ)) (Set.Ioc 0 t)
        timeMeasure := integrableOn_Ioc_of_continuous (by fun_prop) t
    simp_rw [hsum]
    rw [integral_add hi1 hi2, mul_add, ← add_assoc, ih, mul_setIntegral_pow_div_factorial,
      show expPartial (C * t) (n + 1 + 1)
        = expPartial (C * t) (n + 1) + (C * t) ^ (n + 1) / ((n + 1).factorial : ℝ) from
        Finset.sum_range_succ _ _]

/-- **Gronwall's inequality** for `timeMeasure` integrals over `(0,t]`. -/
theorem gronwall_timeMeasure {u : ℝ≥0 → ℝ} {A C M : ℝ} {T : ℝ≥0} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hu_int : ∀ t, IntegrableOn u (Set.Ioc 0 t) timeMeasure)
    (huM : ∀ t ≤ T, u t ≤ M)
    (h : ∀ t ≤ T, u t ≤ A + C * ∫ s in Set.Ioc 0 t, u s ∂timeMeasure) :
    ∀ t ≤ T, u t ≤ A * Real.exp (C * t) := by
  have key : ∀ n : ℕ, ∀ t ≤ T,
      u t ≤ A * expPartial (C * t) n + M * ((C * t) ^ n / (n.factorial : ℝ)) := by
    intro n
    induction n with
    | zero =>
      intro t ht
      simp only [expPartial, Finset.range_zero, Finset.sum_empty, mul_zero, zero_add, pow_zero,
        Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
      exact huM t ht
    | succ n ih =>
      intro t ht
      have hpoly_int : IntegrableOn (fun s : ℝ≥0 => A * expPartial (C * s) n
          + M * ((C * s) ^ n / (n.factorial : ℝ))) (Set.Ioc 0 t) timeMeasure :=
        integrableOn_Ioc_of_continuous
          (((continuous_expPartial_mul C n).const_mul A).add (by fun_prop)) t
      have hle : ∫ s in Set.Ioc 0 t, u s ∂timeMeasure
          ≤ ∫ s in Set.Ioc 0 t, (A * expPartial (C * s) n
            + M * ((C * s) ^ n / (n.factorial : ℝ))) ∂timeMeasure :=
        setIntegral_mono_on (hu_int t) hpoly_int measurableSet_Ioc
          (fun s hs => ih s (hs.2.trans ht))
      have hi1 : IntegrableOn (fun s : ℝ≥0 => A * expPartial (C * s) n) (Set.Ioc 0 t)
          timeMeasure :=
        integrableOn_Ioc_of_continuous ((continuous_expPartial_mul C n).const_mul A) t
      have hi2 : IntegrableOn (fun s : ℝ≥0 => M * ((C * s) ^ n / (n.factorial : ℝ)))
          (Set.Ioc 0 t) timeMeasure := integrableOn_Ioc_of_continuous (by fun_prop) t
      have hsplit : ∫ s in Set.Ioc 0 t, (A * expPartial (C * s) n
            + M * ((C * s) ^ n / (n.factorial : ℝ))) ∂timeMeasure
          = A * ∫ s in Set.Ioc 0 t, expPartial (C * s) n ∂timeMeasure
            + M * ∫ s in Set.Ioc 0 t, (C * s) ^ n / (n.factorial : ℝ) ∂timeMeasure := by
        rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul]
      calc u t ≤ A + C * ∫ s in Set.Ioc 0 t, u s ∂timeMeasure := h t ht
        _ ≤ A + C * (A * ∫ s in Set.Ioc 0 t, expPartial (C * s) n ∂timeMeasure
            + M * ∫ s in Set.Ioc 0 t, (C * s) ^ n / (n.factorial : ℝ) ∂timeMeasure) :=
            by linarith [mul_le_mul_of_nonneg_left (hle.trans hsplit.le) hC]
        _ = A * (1 + C * ∫ s in Set.Ioc 0 t, expPartial (C * s) n ∂timeMeasure)
            + M * (C * ∫ s in Set.Ioc 0 t, (C * s) ^ n / (n.factorial : ℝ) ∂timeMeasure) := by
            ring
        _ = A * expPartial (C * t) (n + 1)
            + M * ((C * t) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
            rw [one_add_mul_setIntegral_expPartial, mul_setIntegral_pow_div_factorial]
  intro t ht
  have hCt : 0 ≤ C * t := mul_nonneg hC t.coe_nonneg
  have hfac := FloorSemiring.tendsto_pow_div_factorial_atTop (C * (t : ℝ))
  have hlim := (hfac.const_mul M).const_add (A * Real.exp (C * t))
  rw [mul_zero, add_zero] at hlim
  refine ge_of_tendsto' hlim (fun n => (key n t ht).trans ?_)
  have hexp := mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hCt n) hA
  unfold expPartial
  linarith

/-! ## `L²` stability -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

section Stability
variable (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)

theorem bandEnergy_smul (c : ℝ) (Z : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) (t : ℝ≥0) :
    bandEnergy T hBmeas (c • Z) t = c ^ 2 * bandEnergy T hBmeas Z t := by
  unfold bandEnergy
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul c Z)] with z hz
  rw [hz, Pi.smul_apply, smul_eq_mul, mul_pow]

theorem l2ItoProcessLp_sub (x₀ : ℝ) (β γ β' γ' : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    l2ItoProcessLp hB T hBmeas hBcont x₀ β γ - l2ItoProcessLp hB T hBmeas hBcont x₀ β' γ'
      = driftProcessAssembled (μ := μ) T hBmeas (β - β')
        + itoProcessAssembled hB T hBmeas hBcont (γ - γ') := by
  simp only [l2ItoProcessLp, map_sub, itoProcessAssembled_sub]
  abel

/-- **`L²` stability** of Itô processes whose drift difference is linear in the difference. -/
theorem norm_sq_l2ItoProcessLp_sub_le (x₀ : ℝ)
    (β γ β' γ' : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) (c : ℝ)
    (hβ : β - β' = c • (l2ItoProcessLp hB T hBmeas hBcont x₀ β γ
      - l2ItoProcessLp hB T hBmeas hBcont x₀ β' γ')) :
    ‖l2ItoProcessLp hB T hBmeas hBcont x₀ β γ - l2ItoProcessLp hB T hBmeas hBcont x₀ β' γ'‖ ^ 2
      ≤ 2 * T * ‖γ - γ'‖ ^ 2 * Real.exp (2 * T * c ^ 2 * T) := by
  set Δ := l2ItoProcessLp hB T hBmeas hBcont x₀ β γ - l2ItoProcessLp hB T hBmeas hBcont x₀ β' γ'
    with hΔ
  have hdecomp := l2ItoProcessLp_sub hB T hBmeas hBcont x₀ β γ β' γ'
  rw [← hΔ] at hdecomp
  have hu : ∀ t ≤ T, bandEnergy T hBmeas Δ t
      ≤ 2 * T * ‖γ - γ'‖ ^ 2 + 2 * T * c ^ 2 * ∫ s in Set.Ioc 0 t, bandEnergy T hBmeas Δ s
        ∂timeMeasure := by
    intro t ht
    have h1 := bandEnergy_add_le T hBmeas (driftProcessAssembled (μ := μ) T hBmeas (β - β'))
      (itoProcessAssembled hB T hBmeas hBcont (γ - γ')) t
    have h2 := bandEnergy_driftProcessAssembled T hBmeas (β - β') ht
    have h3 := bandEnergy_itoProcessAssembled hB T hBmeas hBcont (γ - γ') ht
    have h4 : ∫ s in Set.Ioc 0 t, bandEnergy T hBmeas (γ - γ') s ∂timeMeasure
        ≤ ‖γ - γ'‖ ^ 2 * t :=
      setIntegral_le_of_ae_le_const (sq_nonneg _)
        (ae_of_all _ fun s => bandEnergy_le_norm_sq T hBmeas _ s)
    have h5 : ∀ s, bandEnergy T hBmeas (β - β') s = c ^ 2 * bandEnergy T hBmeas Δ s := by
      intro s; rw [hβ, bandEnergy_smul]
    simp only [h5, integral_const_mul] at h2
    have hT0 : (0 : ℝ) ≤ T := T.coe_nonneg
    have htT : (t : ℝ) ≤ T := by exact_mod_cast ht
    have hI0 : 0 ≤ ∫ s in Set.Ioc 0 t, bandEnergy T hBmeas Δ s ∂timeMeasure :=
      setIntegral_nonneg measurableSet_Ioc fun s _ => bandEnergy_nonneg T hBmeas Δ s
    have hg0 : 0 ≤ ‖γ - γ'‖ ^ 2 := sq_nonneg _
    calc bandEnergy T hBmeas Δ t
        = bandEnergy T hBmeas (driftProcessAssembled (μ := μ) T hBmeas (β - β')
          + itoProcessAssembled hB T hBmeas hBcont (γ - γ')) t := by rw [hdecomp]
      _ ≤ 2 * bandEnergy T hBmeas (driftProcessAssembled (μ := μ) T hBmeas (β - β')) t
          + 2 * bandEnergy T hBmeas (itoProcessAssembled hB T hBmeas hBcont (γ - γ')) t := h1
      _ ≤ 2 * (T * (c ^ 2 * ∫ s in Set.Ioc 0 t, bandEnergy T hBmeas Δ s ∂timeMeasure))
          + 2 * (‖γ - γ'‖ ^ 2 * t) := by
          rw [h3]; linarith
      _ ≤ 2 * T * ‖γ - γ'‖ ^ 2 + 2 * T * c ^ 2 * ∫ s in Set.Ioc 0 t, bandEnergy T hBmeas Δ s
          ∂timeMeasure := by
          have : ‖γ - γ'‖ ^ 2 * t ≤ ‖γ - γ'‖ ^ 2 * T := mul_le_mul_of_nonneg_left htT hg0
          nlinarith
  have hg := gronwall_timeMeasure (u := bandEnergy T hBmeas Δ) (A := 2 * T * ‖γ - γ'‖ ^ 2)
    (C := 2 * T * c ^ 2) (M := ‖Δ‖ ^ 2) (by positivity) (by positivity)
    (integrableOn_bandEnergy T hBmeas Δ) (fun t _ => bandEnergy_le_norm_sq T hBmeas Δ t) hu T le_rfl
  rwa [bandEnergy_self] at hg

end Stability

end MathFin.Heston
