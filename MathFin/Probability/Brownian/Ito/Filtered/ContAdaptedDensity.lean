/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.SDEGlobal
public import MathFin.Probability.Brownian.Ito.StochasticIntegralCharacterisation
public import MathFin.Probability.Brownian.Ito.AdaptedProcessToLp

/-!
# Density of bounded continuous adapted processes in the predictable `L²` space

Every element of `E = Lp ℝ 2 (trimMeasure T)` is an `L²` limit of processes that are
bounded, adapted to the Brownian filtration and continuous along **every** path.  Each simple
predictable process `∑ 1_{(a,b]}(t) Z` is smoothed by replacing the interval indicator with the
continuous ramp `clamp₀₁((n+1)(t-a)) - clamp₀₁((n+1)(t-b))`, which vanishes for `t ≤ a` and so
keeps adaptedness; dominated convergence gives `L²` convergence, and the simple processes are
dense by `approxSeq`.

## Main definitions

* `ContAdaptedBdd.toLp`
* `rampProc`
* `rampCAB`

## Main results

* `tendsto_rampCAB_toLp`
* `exists_contAdaptedBdd_near`
* `exists_seq_contAdaptedBdd_tendsto`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section
namespace MathFin.FilteredIto
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open MathFin MathFin.ItoIntegralL2 MathFin.ItoIntegralCLM
open MathFin.ItoIntegralProcessContinuousModification

/-! ### The ramp -/

/-- `clamp₀₁ x = max 0 (min 1 x)`. -/
def clamp01 (x : ℝ) : ℝ := max 0 (min 1 x)

theorem continuous_clamp01 : Continuous clamp01 := by unfold clamp01; fun_prop

theorem clamp01_nonneg (x : ℝ) : 0 ≤ clamp01 x := le_max_left _ _

theorem clamp01_le_one (x : ℝ) : clamp01 x ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem clamp01_of_nonpos {x : ℝ} (hx : x ≤ 0) : clamp01 x = 0 := by
  unfold clamp01; exact max_eq_left (min_le_of_right_le hx)

theorem clamp01_of_one_le {x : ℝ} (hx : 1 ≤ x) : clamp01 x = 1 := by
  unfold clamp01; rw [min_eq_left hx]; exact max_eq_right zero_le_one

/-- The continuous ramp approximating `1_{(a,b]}`. -/
def rampFn (a b : ℝ≥0) (n : ℕ) (t : ℝ≥0) : ℝ :=
  clamp01 (((n : ℝ) + 1) * ((t : ℝ) - a)) - clamp01 (((n : ℝ) + 1) * ((t : ℝ) - b))

theorem continuous_rampFn (a b : ℝ≥0) (n : ℕ) : Continuous (rampFn a b n) := by
  unfold rampFn
  exact (continuous_clamp01.comp (by fun_prop)).sub (continuous_clamp01.comp (by fun_prop))

theorem abs_rampFn_le_one (a b : ℝ≥0) (n : ℕ) (t : ℝ≥0) : |rampFn a b n t| ≤ 1 := by
  unfold rampFn
  have h1 := clamp01_nonneg (((n : ℝ) + 1) * ((t : ℝ) - a))
  have h2 := clamp01_le_one (((n : ℝ) + 1) * ((t : ℝ) - a))
  have h3 := clamp01_nonneg (((n : ℝ) + 1) * ((t : ℝ) - b))
  have h4 := clamp01_le_one (((n : ℝ) + 1) * ((t : ℝ) - b))
  rw [abs_le]; constructor <;> linarith

theorem rampFn_of_le {a b : ℝ≥0} (hab : a ≤ b) (n : ℕ) {t : ℝ≥0} (ht : t ≤ a) :
    rampFn a b n t = 0 := by
  unfold rampFn
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hta : (t : ℝ) - a ≤ 0 := by have : (t : ℝ) ≤ a := by exact_mod_cast ht
                                   linarith
  have htb : (t : ℝ) - b ≤ 0 := by have : (t : ℝ) ≤ b := by exact_mod_cast ht.trans hab
                                   linarith
  rw [clamp01_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hn hta),
    clamp01_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hn htb), sub_zero]

/-- For large `n` the ramp agrees with the indicator of `(a,b]`. -/
theorem eventually_rampFn_eq_indicator {a b : ℝ≥0} (hab : a ≤ b) (t : ℝ≥0) :
    ∀ᶠ n : ℕ in atTop, rampFn a b n t = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) t := by
  by_cases hta : t ≤ a
  · refine Eventually.of_forall fun n => ?_
    rw [rampFn_of_le hab n hta, Set.indicator_of_notMem]
    simp only [Set.mem_Ioc, not_and, not_le]
    intro h; exact absurd hta (not_le.mpr h)
  · have hta' : (a : ℝ) < t := by exact_mod_cast not_le.mp hta
    by_cases htb : t ≤ b
    · -- `a < t ≤ b`
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ((t : ℝ) - a))
      filter_upwards [eventually_ge_atTop N] with n hn
      rw [Set.indicator_of_mem (show t ∈ Set.Ioc a b from ⟨not_le.mp hta, htb⟩)]
      unfold rampFn
      have hpos : 0 < (t : ℝ) - a := by linarith
      have h1 : 1 ≤ ((n : ℝ) + 1) * ((t : ℝ) - a) := by
        have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
        have := (div_lt_iff₀ hpos).mp hN
        nlinarith
      have h2 : ((n : ℝ) + 1) * ((t : ℝ) - b) ≤ 0 := by
        have : (t : ℝ) ≤ b := by exact_mod_cast htb
        have hn0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
        exact mul_nonpos_of_nonneg_of_nonpos hn0 (by linarith)
      rw [clamp01_of_one_le h1, clamp01_of_nonpos h2, sub_zero]
    · -- `b < t`
      have htb' : (b : ℝ) < t := by exact_mod_cast not_le.mp htb
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ((t : ℝ) - b))
      filter_upwards [eventually_ge_atTop N] with n hn
      have hout : t ∉ Set.Ioc a b := fun ht ↦ htb ht.2
      rw [Set.indicator_of_notMem hout]
      unfold rampFn
      have hposb : 0 < (t : ℝ) - b := by linarith
      have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hb1 : 1 ≤ ((n : ℝ) + 1) * ((t : ℝ) - b) := by
        have := (div_lt_iff₀ hposb).mp hN
        nlinarith
      have ha1 : 1 ≤ ((n : ℝ) + 1) * ((t : ℝ) - a) := by
        have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
        nlinarith
      rw [clamp01_of_one_le ha1, clamp01_of_one_le hb1, sub_self]

/-! ### Bounded continuous adapted processes -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ}

/-- A process adapted to the Brownian filtration, continuous along every path and bounded. -/
structure ContAdaptedBdd (hBmeas : ∀ t, Measurable (B t)) where
  /-- Time-indexed random coefficient. -/
  toFun : ℝ≥0 → Ω → ℝ
  adapted : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (toFun t)
  cont : ∀ ω, Continuous fun t => toFun t ω
  /-- Uniform bound on the absolute value of the coefficient. -/
  bound : ℝ
  bdd : ∀ t ω, |toFun t ω| ≤ bound

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The class of a bounded continuous adapted process in `E`. -/
def ContAdaptedBdd.toLp (T : ℝ≥0) {hBmeas : ∀ t, Measurable (B t)}
    (s : ContAdaptedBdd hBmeas) : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) :=
  processToLp T hBmeas s.adapted s.cont s.bdd

theorem ContAdaptedBdd.coeFn_toLp (T : ℝ≥0) {hBmeas : ∀ t, Measurable (B t)}
    (s : ContAdaptedBdd hBmeas) :
    ⇑(s.toLp (μ := μ) T) =ᵐ[trimMeasure (μ := μ) T hBmeas] Function.uncurry s.toFun :=
  processToLp_coeFn T hBmeas s.adapted s.cont s.bdd

/-- The ramp smoothing of a simple process. -/
def rampProc (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ p ∈ V.value.support, rampFn p.1 p.2 n t * V.value p ω

theorem rampProc_adapted (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (n : ℕ) (t : ℝ≥0) :
    StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (rampProc hBmeas V n t) := by
  have hterm : ∀ p ∈ V.value.support,
      StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)]
        (fun ω => rampFn p.1 p.2 n t * V.value p ω) := by
    intro p hp
    by_cases htp : t ≤ p.1
    · have h0 : (fun ω => rampFn p.1 p.2 n t * V.value p ω) = fun _ => 0 := by
        funext ω; rw [rampFn_of_le (V.le_of_mem_support_value p hp) n htp, zero_mul]
      rw [h0]; exact stronglyMeasurable_const
    · have hle : (natFiltration hBmeas p.1 : MeasurableSpace Ω) ≤ natFiltration hBmeas t :=
        (natFiltration hBmeas).mono (not_le.mp htp).le
      have hm : Measurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (V.value p) :=
        (V.measurable_value p).mono hle le_rfl
      exact (hm.const_mul _).stronglyMeasurable
  have := Finset.stronglyMeasurable_sum (f := fun p ω => rampFn p.1 p.2 n t * V.value p ω)
    V.value.support hterm
  convert this using 1
  funext ω
  simp [rampProc, Finset.sum_apply]

theorem rampProc_cont (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (n : ℕ) (ω : Ω) :
    Continuous fun t => rampProc hBmeas V n t ω := by
  unfold rampProc
  exact continuous_finsetSum _ fun p _ => (continuous_rampFn p.1 p.2 n).mul continuous_const

theorem rampProc_bdd (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    |rampProc hBmeas V n t ω| ≤ (V.value.support.card : ℝ) * V.valueBound := by
  unfold rampProc
  calc |∑ p ∈ V.value.support, rampFn p.1 p.2 n t * V.value p ω|
      ≤ ∑ p ∈ V.value.support, |rampFn p.1 p.2 n t * V.value p ω| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ V.value.support, V.valueBound := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [abs_mul]
        have h1 := abs_rampFn_le_one p.1 p.2 n t
        have h2 : |V.value p ω| ≤ V.valueBound := by
          simpa [Real.norm_eq_abs] using V.value_le_valueBound p ω
        calc |rampFn p.1 p.2 n t| * |V.value p ω| ≤ 1 * V.valueBound :=
              mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
          _ = V.valueBound := one_mul _
    _ = (V.value.support.card : ℝ) * V.valueBound := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The ramp smoothing as a bounded continuous adapted process. -/
def rampCAB (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (n : ℕ) : ContAdaptedBdd hBmeas where
  toFun := rampProc hBmeas V n
  adapted := rampProc_adapted hBmeas V n
  cont := rampProc_cont hBmeas V n
  bound := (V.value.support.card : ℝ) * V.valueBound
  bdd := rampProc_bdd hBmeas V n

/-- Pointwise convergence of the ramp smoothing off time zero. -/
theorem tendsto_rampProc (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) {t : ℝ≥0} (ht : t ≠ 0) (ω : Ω) :
    Tendsto (fun n => rampProc hBmeas V n t ω) atTop (𝓝 (⇑V t ω)) := by
  have hV : ⇑V t ω = ∑ p ∈ V.value.support,
      (Set.Ioc p.1 p.2).indicator (fun _ => (1 : ℝ)) t * V.value p ω := by
    rw [SimpleProcess.apply_eq, Set.indicator_of_notMem (by simpa using ht), zero_add,
      Finsupp.sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : t ∈ Set.Ioc p.1 p.2
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
  rw [hV]
  apply tendsto_finsetSum
  intro p hp
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_rampFn_eq_indicator (V.le_of_mem_support_value p hp) t] with n hn
  rw [hn]

section Density
variable (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))

theorem tendsto_rampCAB_toLp (V : TBoundedSP T hBmeas) :
    Tendsto (fun n => (rampCAB hBmeas V.val n).toLp (μ := μ) T) atTop
      (𝓝 (simpleAssemblyHorizon (μ := μ) T hBmeas V)) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  set bnd : ℝ := (V.val.value.support.card : ℝ) * V.val.valueBound
  have hcoeV : ⇑(simpleAssemblyHorizon (μ := μ) T hBmeas V)
      =ᵐ[trimMeasure (μ := μ) T hBmeas] Function.uncurry ⇑V.val :=
    (memLp_uncurry_trimMeasure T hBmeas V.val).coeFn_toLp
  have key := MathFin.tendsto_eLpNorm_sub_of_dominated_convergence
    (p := 2) (ν := trimMeasure (μ := μ) T hBmeas) (by norm_num)
    (F := fun n => ⇑((rampCAB hBmeas V.val n).toLp (μ := μ) T))
    (f := ⇑(simpleAssemblyHorizon (μ := μ) T hBmeas V)) (fun _ => bnd)
    (fun n => (Lp.aestronglyMeasurable _)) (memLp_const bnd)
    (fun n => by
      filter_upwards [(rampCAB hBmeas V.val n).coeFn_toLp (μ := μ) T] with z hz
      rw [hz, Real.norm_eq_abs]
      exact rampProc_bdd hBmeas V.val n z.1 z.2)
    (by
      filter_upwards [hcoeV, ae_fst_mem_Ioc_trimMeasure (μ := μ) T hBmeas,
        ae_all_iff.mpr fun n => (rampCAB hBmeas V.val n).coeFn_toLp (μ := μ) T]
        with z hzV hz1 hzn
      rw [hzV]
      simp only [hzn]
      exact tendsto_rampProc hBmeas V.val (ne_of_gt hz1.1) z.2)
  exact key

/-- **Density**: every element of the predictable `L²` space is approximated by bounded,
everywhere-continuous adapted processes. -/
theorem exists_contAdaptedBdd_near (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : ContAdaptedBdd hBmeas, ‖s.toLp (μ := μ) T - φ‖ < ε := by
  obtain ⟨V, hV⟩ := approxSeq (μ := μ) T hBmeas φ
  have hlim : Tendsto (fun n : ℕ => (2⁻¹ : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds (half_pos hε))).exists
  have hconv := tendsto_rampCAB_toLp (μ := μ) T hBmeas (V N)
  rw [tendsto_iff_norm_sub_tendsto_zero] at hconv
  obtain ⟨m, hm⟩ := (hconv.eventually (gt_mem_nhds (half_pos hε))).exists
  refine ⟨rampCAB hBmeas (V N).val m, ?_⟩
  calc ‖(rampCAB hBmeas (V N).val m).toLp (μ := μ) T - φ‖
      = ‖((rampCAB hBmeas (V N).val m).toLp (μ := μ) T - simpleAssemblyHorizon (μ := μ) T hBmeas
            (V N))
          + (simpleAssemblyHorizon (μ := μ) T hBmeas (V N) - φ)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖(rampCAB hBmeas (V N).val m).toLp (μ := μ) T - simpleAssemblyHorizon (μ := μ) T hBmeas
          (V N)‖
          + ‖simpleAssemblyHorizon (μ := μ) T hBmeas (V N) - φ‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hm ((hV N).trans_lt hN)
    _ = ε := add_halves ε

theorem exists_seq_contAdaptedBdd_tendsto (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ∃ s : ℕ → ContAdaptedBdd hBmeas,
      Tendsto (fun n => (s n).toLp (μ := μ) T) atTop (𝓝 φ) := by
  choose s hs using fun n : ℕ =>
    exists_contAdaptedBdd_near (μ := μ) T hBmeas φ (Nat.one_div_pos_of_nat (n := n))
  refine ⟨s, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hs n).le) ?_
  exact tendsto_one_div_add_atTop_nhds_zero_nat

end Density
end MathFin.FilteredIto
