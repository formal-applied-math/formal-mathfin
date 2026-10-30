/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.StrictExerciseGeometry

/-! # A first-contact rule constructed from the actual stopping price

The undiscounted price/payoff gap is continuous, adapted, nonnegative and zero
at expiry. Its first zero is therefore an admissible rule with actual payoff
contact. Optimality and the dynamic programming principle are not assumed.

## Result

Public entry points include `canonicalLogPath`, `canonicalGap`, `canonicalLogPath_exp`,
`canonicalGap_continuous`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped NNReal Topology

variable {Ω : Type*}

/-- Log-price path from `x` with drift `k-h-1` and volatility `Real.sqrt 2`, evaluated at
the capped time `min t T`. -/
noncomputable def canonicalLogPath (W : ℝ≥0 → Ω → ℝ) (k h x : ℝ)
    (T t : ℝ≥0) (ω : Ω) : ℝ :=
  x+(k-h-1)*(min t T : ℝ)+Real.sqrt 2*W (min t T) ω

/-- Gap between the canonical price at remaining time `T-min t T` and the put payoff, both
taken along `canonicalLogPath`. -/
noncomputable def canonicalGap (W : ℝ≥0 → Ω → ℝ) (k h x : ℝ)
    (T t : ℝ≥0) (ω : Ω) : ℝ :=
  canonicalPrice k h (canonicalLogPath W k h x T t ω) ((T : ℝ)-(min t T : ℝ))-
    putPayoff (canonicalLogPath W k h x T t ω)

theorem canonicalLogPath_exp (W : ℝ≥0 → Ω → ℝ) (k h x : ℝ)
    (T t : ℝ≥0) (ω : Ω) :
    Real.exp (canonicalLogPath W k h x T t ω) =
      MathFin.gbmValue (Real.exp x) (k-h) (Real.sqrt 2) (min t T) (W (min t T) ω) := by
  unfold canonicalLogPath MathFin.gbmValue
  rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),← Real.exp_add]
  congr 1
  ring

theorem canonicalGap_continuous {W : ℝ≥0 → Ω → ℝ} {k h : ℝ} (hk : 0 ≤ k)
    (hpaths : ∀ ω, Continuous (fun t => W t ω)) (x : ℝ) (T : ℝ≥0) (ω : Ω) :
    Continuous (fun t => canonicalGap W k h x T t ω) := by
  have hx : Continuous (fun t => canonicalLogPath W k h x T t ω) := by
    unfold canonicalLogPath
    fun_prop
  have hp := (canonicalPrice_continuous (h := h) hk).comp
    (hx.prodMk (show Continuous (fun t : ℝ≥0 => (T : ℝ)-(min t T : ℝ)) by fun_prop))
  exact hp.sub (by unfold putPayoff; fun_prop)

theorem canonicalGap_nonneg {W : ℝ≥0 → Ω → ℝ} {k h : ℝ} (hk : 0 ≤ k)
    (x : ℝ) (T t : ℝ≥0) (ω : Ω) : 0 ≤ canonicalGap W k h x T t ω :=
  sub_nonneg.mpr (canonicalPrice_bounds hk _ _).1

theorem canonicalGap_terminal {W : ℝ≥0 → Ω → ℝ} {k h : ℝ} (hk : 0 ≤ k)
    (x : ℝ) (T : ℝ≥0) (ω : Ω) : canonicalGap W k h x T T ω = 0 := by
  simp only [canonicalGap,min_self,sub_self,canonicalPrice_initial hk]

variable [MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
  {W : ℝ≥0 → Ω → ℝ} {k h : ℝ}

theorem canonicalGap_adapted (hk : 0 ≤ k) (hW : Adapted 𝓕 W) (x : ℝ) (T : ℝ≥0) :
    Adapted 𝓕 (canonicalGap W k h x T) := by
  intro t
  have hw : Measurable[𝓕 t] (W (min t T)) :=
    (hW _).mono (𝓕.mono (min_le_left t T)) le_rfl
  have hx : Measurable[𝓕 t] (canonicalLogPath W k h x T t) := by
    unfold canonicalLogPath
    fun_prop
  have hp := (canonicalPrice_continuous (h := h) hk).measurable.comp
    (hx.prodMk (measurable_const (a := (T : ℝ)-(min t T : ℝ))))
  exact hp.sub (by unfold putPayoff; fun_prop)

/-- The rule stopping at the first zero of `canonicalGap`, that is, at first contact of the
price with the payoff. -/
noncomputable def canonicalContactRule (hk : 0 ≤ k) (hW : Adapted 𝓕 W)
    (hpaths : ∀ ω, Continuous (fun t => W t ω)) (x : ℝ) (T : ℝ≥0) : StoppingRule 𝓕 T :=
  firstContactRule (Z := canonicalGap W k h x T)
    (canonicalGap_adapted hk hW x T) (canonicalGap_continuous hk hpaths x T)
    (canonicalGap_nonneg hk x T) T (canonicalGap_terminal hk x T)

theorem canonicalContactRule_contact (hk : 0 ≤ k) (hW : Adapted 𝓕 W)
    (hpaths : ∀ ω, Continuous (fun t => W t ω)) (x : ℝ) (T : ℝ≥0) (ω : Ω) :
    let θ := canonicalContactRule (h := h) hk hW hpaths x T
    canonicalGap W k h x T (θ.time ω) ω = 0 :=
  (firstContactTime_mem (canonicalGap_continuous hk hpaths x T)
    (canonicalGap_terminal hk x T) ω).2

theorem canonicalContactRule_continuation_before (hk : 0 ≤ k) (hW : Adapted 𝓕 W)
    (hpaths : ∀ ω, Continuous (fun t => W t ω)) (x : ℝ) (T : ℝ≥0) (ω : Ω)
    {t : ℝ≥0} (ht : t < (canonicalContactRule (h := h) hk hW hpaths x T).time ω) :
    (canonicalLogPath W k h x T t ω, (T : ℝ)-(t : ℝ)) ∈ canonicalContinuationRegion k h := by
  have hT := (canonicalContactRule (h := h) hk hW hpaths x T).le_horizon ω
  have htT : t < T := ht.trans_le hT
  have hg := firstContactTime_pos_before (canonicalGap_continuous (h := h) hk hpaths x T)
    (canonicalGap_nonneg hk x T) (canonicalGap_terminal hk x T) ω ht
  refine ⟨sub_pos.mpr (by exact_mod_cast htT),?_⟩
  simpa only [canonicalGap,NNReal.coe_min,
    min_eq_left (show (t : ℝ) ≤ (T : ℝ) by exact_mod_cast htT.le),sub_pos] using hg

theorem canonicalContactRule_exercise_before_expiry (hk : 0 ≤ k) (hW : Adapted 𝓕 W)
    (hpaths : ∀ ω, Continuous (fun t => W t ω)) (x : ℝ) (T : ℝ≥0) (ω : Ω)
    (ht : (canonicalContactRule (h := h) hk hW hpaths x T).time ω < T) :
    let s := (canonicalContactRule (h := h) hk hW hpaths x T).time ω
    Real.exp (canonicalLogPath W k h x T s ω) ≤ canonicalStockBoundary k h ((T : ℝ)-(s : ℝ)) := by
  let s := (canonicalContactRule (h := h) hk hW hpaths x T).time ω
  have hs : (s : ℝ) < (T : ℝ) := by exact_mod_cast ht
  have hz := canonicalContactRule_contact (h := h) hk hW hpaths x T ω
  change canonicalGap W k h x T s ω = 0 at hz
  have he : canonicalPrice k h (canonicalLogPath W k h x T s ω) ((T : ℝ)-(s : ℝ)) =
      putPayoff (canonicalLogPath W k h x T s ω) := by
    apply sub_eq_zero.mp
    simpa only [canonicalGap,NNReal.coe_min,min_eq_left hs.le] using hz
  exact (canonicalPrice_contact_iff hk _ (sub_pos.mpr hs)).mp he

theorem brownianUsual_adapted :
    @Adapted _ _ (completedMeasurableSpace gaussianLimit) _ _ _
        brownianUsualFiltration brownian := by
  intro t
  exact (brownian_adapted t).mono (brownian_completedRaw_le_usual t) le_rfl

/-- Concrete admissible rule on the completed usual Brownian space. -/
noncomputable def brownianUsualActualContactRule {k h : ℝ} (hk : 0 ≤ k) (x : ℝ) (T : ℝ≥0) :
    @StoppingRule (ℝ≥0 → ℝ) (completedMeasurableSpace gaussianLimit) ℝ≥0 _
      brownianUsualFiltration T :=
  @canonicalContactRule _ (completedMeasurableSpace gaussianLimit) brownianUsualFiltration
    brownian k h hk brownianUsual_adapted continuous_brownian x T

end MathFin.BlackScholes.AmericanPut.Stopping
