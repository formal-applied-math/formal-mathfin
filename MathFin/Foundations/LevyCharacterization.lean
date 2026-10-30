/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.BoundedLocalMartingale
public import MathFin.Foundations.ExitTime
public import MathFin.Foundations.ExpMartingaleBrownian
public import MathFin.Foundations.UnifIntegrableL2
public import MathFin.Foundations.LevyExpMartingale

/-!
# Lévy's characterisation of Brownian motion

A continuous local martingale `M` with `M₀ = 0` such that `M² − t` is a local martingale is a
Brownian motion (issue #179):

* `isBrownianReal_of_localMartingale` — `IsBrownianReal M P`;
* `isFilteredPreBrownian_of_localMartingale` — `IsFilteredPreBrownian M 𝓕 P`: moreover every
  increment `M_t − M_s` is independent of `𝓕_s`.

"Local martingale" is BrownianMotion's `IsLocalMartingale` (a localising sequence of stopped
càdlàg martingales). There is no quadratic-variation process and no stochastic integral against
`M`: the bracket enters only through the local martingale property of `M² − t`. This matters at
the pin, where BrownianMotion's Doob–Meyer decomposition is `sorry`.

For a *bounded* martingale `M` with `M² − t` a martingale, no localisation is needed:
`isBrownianReal_of_bounded_martingale`, `isFilteredPreBrownian_of_bounded_martingale`.

## The argument

1. **Bounded case** (`LevyQuadraticSums`, `LevyExpMartingale`, `ExpMartingaleBrownian`). If `M`
   is a bounded martingale with continuous paths and `M² − A` is a martingale for a slow clock
   `A` (`0 ≤ A_q − A_p ≤ q − p`), then `exp(a·M − a²A/2)` is a martingale for every `a`, by a
   cell-by-cell Itô expansion along uniform partitions. For `A_t = t` this is the data
   `IsExpQMartingale P 𝓕 M T`, from which `isFilteredPreBrownian_of_expMartingale` gives the
   Brownian conclusion.
2. **Stopping** (`stoppedProcess_exitTime`). Stop `M` at the exit time `ρ_n` of `|M|` from
   `(−n−1, n+1)` (`exitTime`, a localising sequence for continuous adapted `M`). The stopped
   process `M^{ρ_n}` is a bounded local martingale, hence a martingale
   (`bounded_localMartingale_is_martingale`), and `(M^{ρ_n})² − (t ∧ ρ_n)` is a locally bounded
   local martingale, hence a martingale. The clock `t ∧ ρ_n` is slow
   (`isSlowClock_stoppedProcess`), so step 1 applies: `exp(a·M^{ρ_n} − a²(t ∧ ρ_n)/2)` is a
   martingale.
3. **Limit** (`tendsto_setIntegral_stopped_exp`). For fixed `t`, `ρ_n > t` eventually, so these
   exponentials converge to `exp(a·M_t − a²t/2)` pointwise. They are bounded in `L²`:
   `E[exp(2aM^{ρ}_t − a²(t∧ρ))] ≤ e^{a²t}·E[exp(2aM^{ρ}_t − 2a²(t∧ρ))] = e^{a²t}`, the last
   factor being the exponential martingale at `2a` started at `1`. An `L²`-bounded sequence
   converging a.e. converges on sets
   (`tendsto_setIntegral_of_subseq_ae_of_sq_bound`, Vitali), which passes the martingale identity over `𝓕_s`-sets to the limit: `IsExpQMartingale P 𝓕 M T`
   (`isExpQMartingale_of_localMartingale`).

## Scope

`M` is assumed adapted (`StronglyAdapted 𝓕 M`), with *every* path continuous and `M₀ = 0`
*everywhere*. The local martingale hypotheses are BrownianMotion's, so they include càdlàg paths
of the stopped processes. The conclusion `IsBrownianReal M P` is Mathlib's: `M` is a Brownian
motion with respect to its own law, and with `IsFilteredPreBrownian M 𝓕 P` also with respect to
`𝓕`.
-/

@[expose] public section

namespace MathFin
namespace LevyCharacterization

open MeasureTheory ProbabilityTheory Filter Topology Set LevyQuadraticSums LevyExpMartingale
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ} {K : ℝ}

/-! ### The bounded case -/

/-- **Lévy's characterisation, bounded case.** A bounded martingale `M` with continuous paths,
started at `0`, such that `M² − t` is a martingale, is a Brownian motion that is `𝓕`-filtered:
every increment `M_t − M_s` is independent of `𝓕_s`. -/
theorem isFilteredPreBrownian_of_bounded_martingale (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω ↦ M t ω ^ 2 - (t : ℝ)) 𝓕 P) (hK : ∀ t ω, |M t ω| ≤ K)
    (hcont : ∀ ω, Continuous fun t ↦ M t ω) (hM0 : M 0 =ᵐ[P] 0) :
    IsFilteredPreBrownian M 𝓕 P :=
  isFilteredPreBrownian_of_expMartingale (isExpQMartingale hM hM2 hK hcont hM0)

/-- **Lévy's characterisation, bounded case.** A bounded martingale `M` with continuous paths,
started at `0`, such that `M² − t` is a martingale, is a Brownian motion. -/
theorem isBrownianReal_of_bounded_martingale (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω ↦ M t ω ^ 2 - (t : ℝ)) 𝓕 P) (hK : ∀ t ω, |M t ω| ≤ K)
    (hcont : ∀ ω, Continuous fun t ↦ M t ω) (hM0 : M 0 =ᵐ[P] 0) : IsBrownianReal M P :=
  isBrownianReal_of_expMartingale (isExpQMartingale hM hM2 hK hcont hM0) (.of_forall hcont)

/-! ### The clock `t ∧ ρ` -/

private lemma coe_untopA (x : ℝ≥0) : ((x : WithTop ℝ≥0)).untopA = x := rfl

/-- `min t ρ`, read back in `ℝ≥0`, is again `min t ρ` in `WithTop ℝ≥0`. -/
theorem coe_untopA_min (t : ℝ≥0) (c : WithTop ℝ≥0) :
    (((min (t : WithTop ℝ≥0) c).untopA : ℝ≥0) : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) c := by
  induction c using WithTop.recTopCoe with
  | top => rw [min_top_right]; rfl
  | coe c => rw [← WithTop.coe_min, coe_untopA]

/-- `t ↦ (t ∧ ρ)` is continuous. -/
theorem continuous_untopA_min (c : WithTop ℝ≥0) :
    Continuous fun t : ℝ≥0 ↦ (min (t : WithTop ℝ≥0) c).untopA := by
  induction c using WithTop.recTopCoe with
  | top => simp only [min_top_right]; exact continuous_id
  | coe c =>
    simp only [← WithTop.coe_min, coe_untopA]
    exact continuous_id.min continuous_const

/-- At time `0` the stopped time is `0`. -/
theorem untopA_min_zero (c : WithTop ℝ≥0) : (min ((0 : ℝ≥0) : WithTop ℝ≥0) c).untopA = 0 := by
  induction c using WithTop.recTopCoe with
  | top => rw [min_top_right]; rfl
  | coe c => rw [← WithTop.coe_min, coe_untopA]; simp

private lemma stoppedClock_sub (c : WithTop ℝ≥0) {p q : ℝ≥0} (hpq : p ≤ q) :
    0 ≤ (((min (q : WithTop ℝ≥0) c).untopA : ℝ≥0) : ℝ)
        - ((min (p : WithTop ℝ≥0) c).untopA : ℝ≥0) ∧
      (((min (q : WithTop ℝ≥0) c).untopA : ℝ≥0) : ℝ)
        - ((min (p : WithTop ℝ≥0) c).untopA : ℝ≥0) ≤ (q : ℝ) - p := by
  have hpq' : (p : ℝ) ≤ q := hpq
  induction c using WithTop.recTopCoe with
  | top =>
    simp only [min_top_right]
    exact ⟨sub_nonneg.2 hpq', le_rfl⟩
  | coe c =>
    simp only [← WithTop.coe_min, coe_untopA, NNReal.coe_min]
    rcases min_cases (p : ℝ) c with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
      rcases min_cases (q : ℝ) c with ⟨h2, _⟩ | ⟨h2, _⟩ <;> constructor <;> linarith

/-- **The stopped clock `t ∧ ρ` is a slow clock.** -/
theorem isSlowClock_stoppedProcess (ρ : Ω → WithTop ℝ≥0) :
    IsSlowClock (stoppedProcess (fun (t : ℝ≥0) (_ : Ω) ↦ (t : ℝ)) ρ) where
  zero ω := by simp [stoppedProcess]
  sub_nonneg _ _ hpq ω := (stoppedClock_sub (ρ ω) hpq).1
  sub_le _ _ hpq ω := (stoppedClock_sub (ρ ω) hpq).2

/-! ### Stopping at the exit time -/

section Stopped

/-- The exit time of `|M|` from `(−n−1, n+1)` is positive when `M₀ = 0`. -/
theorem bot_lt_exitTime (hcont : ∀ ω, Continuous fun t ↦ M t ω) (hM0 : ∀ ω, M 0 ω = 0) (n : ℕ)
    (ω : Ω) : ⊥ < exitTime M (n + 1) ω := by
  refine lt_of_not_ge fun h ↦ ?_
  obtain ⟨s, hs, hle⟩ := (exitTime_le_iff hcont (n + 1) 0 ω).1 h
  obtain rfl : s = 0 := le_antisymm hs.2 hs.1
  rw [hM0, abs_zero] at hle
  have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  linarith

/-- When every exit time is positive, the indicator in the stopped process is inert. -/
theorem stoppedProcess_indicator_eq {ρ : Ω → WithTop ℝ≥0} (hρ : ∀ ω, ⊥ < ρ ω)
    (X : ℝ≥0 → Ω → ℝ) :
    stoppedProcess (fun i ↦ {ω | ⊥ < ρ ω}.indicator (X i)) ρ = stoppedProcess X ρ := by
  funext t ω
  simp only [stoppedProcess]
  exact Set.indicator_of_mem (s := {ω : Ω | ⊥ < ρ ω}) (hρ ω) _

/-- The stopped process is bounded by `n + 1`: up to the exit time, `|M| ≤ n + 1`. -/
theorem abs_stoppedProcess_le (hcont : ∀ ω, Continuous fun t ↦ M t ω) (hM0 : ∀ ω, M 0 ω = 0)
    (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    |stoppedProcess M (exitTime M (n + 1)) t ω| ≤ ((n + 1 : ℕ) : ℝ) :=
  abs_le_of_le_exitTime hcont (bot_lt_exitTime hcont hM0 n ω) (by
    rw [coe_untopA_min]; exact min_le_right _ _)

/-- The stopped process has continuous paths. -/
theorem continuous_stoppedProcess (hcont : ∀ ω, Continuous fun t ↦ M t ω)
    (ρ : Ω → WithTop ℝ≥0) (ω : Ω) :
    Continuous fun t ↦ stoppedProcess M ρ t ω :=
  (hcont ω).comp (continuous_untopA_min (ρ ω))

/-- **Stopped at the exit time, `M` and `M² − t` are martingales.** For a local martingale `M`
with continuous paths and `M₀ = 0`, the process `M` stopped at the exit time of `|M|` from
`(−n−1, n+1)` is a bounded local martingale, hence a martingale, and `(M^ρ)² − (t ∧ ρ)` — the
stopped `M² − t` — is a locally bounded local martingale, hence a martingale. -/
theorem martingale_stoppedProcess_exitTime (hadapt : StronglyAdapted 𝓕 M)
    (hcont : ∀ ω, Continuous fun t ↦ M t ω) (hM0 : ∀ ω, M 0 ω = 0)
    (hM : IsLocalMartingale M 𝓕 P)
    (hM2 : IsLocalMartingale (fun t ω ↦ M t ω ^ 2 - (t : ℝ)) 𝓕 P) (n : ℕ) :
    Martingale (stoppedProcess M (exitTime M (n + 1))) 𝓕 P ∧
      Martingale (fun t ω ↦ stoppedProcess M (exitTime M (n + 1)) t ω ^ 2
        - stoppedProcess (fun (t : ℝ≥0) (_ : Ω) ↦ (t : ℝ)) (exitTime M (n + 1)) t ω) 𝓕 P := by
  have hρ : IsStoppingTime 𝓕 (exitTime M (n + 1)) :=
    isStoppingTime_exitTime_of_measurable (fun t ↦ (hadapt t).measurable) hcont (n + 1)
  have hpos := bot_lt_exitTime hcont hM0 n
  have hU : StronglyAdapted 𝓕 (fun t ω ↦ M t ω ^ 2 - (t : ℝ)) :=
    fun t ↦ ((hadapt t).pow 2).sub stronglyMeasurable_const
  have hUc : ∀ ω, Continuous fun t ↦ M t ω ^ 2 - (t : ℝ) := fun ω ↦
    ((hcont ω).pow 2).sub NNReal.continuous_coe
  refine ⟨?_, ?_⟩
  · have hloc := (isStable_martingale (𝓕 := 𝓕) (P := P)).locally M hM _ hρ
    rw [stoppedProcess_indicator_eq hpos] at hloc
    have had := hadapt.stoppedProcess_indicator (fun ω ↦ (hcont ω).isCadlag.right_continuous) hρ
    rw [stoppedProcess_indicator_eq hpos] at had
    exact bounded_localMartingale_is_martingale hloc had
      (C := ((n + 1 : ℕ) : ℝ)) fun t ω ↦ by
        rw [Real.norm_eq_abs]; exact abs_stoppedProcess_le hcont hM0 n t ω
  · have hloc := (isStable_martingale (𝓕 := 𝓕) (P := P)).locally _ hM2 _ hρ
    rw [stoppedProcess_indicator_eq hpos] at hloc
    have had := hU.stoppedProcess_indicator (fun ω ↦ (hUc ω).isCadlag.right_continuous) hρ
    rw [stoppedProcess_indicator_eq hpos] at had
    refine locally_bounded_localMartingale_is_martingale hloc had fun T ↦
      ⟨((n + 1 : ℕ) : ℝ) ^ 2 + T, fun t ht ω ↦ ?_⟩
    set s : ℝ≥0 := (min (t : WithTop ℝ≥0) (exitTime M (n + 1) ω)).untopA with hs
    have hst : (s : ℝ) ≤ t := NNReal.coe_le_coe.2 (WithTop.untopA_le (min_le_left _ _))
    have hb : |M s ω| ≤ ((n + 1 : ℕ) : ℝ) := abs_stoppedProcess_le hcont hM0 n t ω
    have hsq : M s ω ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := sq_le_sq' (abs_le.1 hb).1 (abs_le.1 hb).2
    have ht' : (t : ℝ) ≤ T := ht
    show ‖M s ω ^ 2 - (s : ℝ)‖ ≤ _
    rw [Real.norm_eq_abs, abs_le]
    have := NNReal.coe_nonneg s
    have := NNReal.coe_nonneg t
    constructor <;> nlinarith [sq_nonneg (M s ω), sq_nonneg (((n + 1 : ℕ) : ℝ))]

/-- The stopped exponential martingale identity over `𝓕_s`-sets, for the process stopped at the
`n`-th exit time (`setIntegral_exp_eq` with the slow clock `t ∧ ρ_n`). -/
theorem setIntegral_stopped_exp_eq (hadapt : StronglyAdapted 𝓕 M)
    (hcont : ∀ ω, Continuous fun t ↦ M t ω) (hM0 : ∀ ω, M 0 ω = 0)
    (hM : IsLocalMartingale M 𝓕 P) (hM2 : IsLocalMartingale (fun t ω ↦ M t ω ^ 2 - (t : ℝ)) 𝓕 P)
    (n : ℕ) (a : ℝ) {s t : ℝ≥0} (hst : s ≤ t) {S : Set Ω} (hS : MeasurableSet[𝓕 s] S) :
    ∫ ω in S, Real.exp (a * stoppedProcess M (exitTime M (n + 1)) t ω
        - a ^ 2 * stoppedProcess (fun (t : ℝ≥0) (_ : Ω) ↦ (t : ℝ)) (exitTime M (n + 1)) t ω / 2) ∂P
      = ∫ ω in S, Real.exp (a * stoppedProcess M (exitTime M (n + 1)) s ω
        - a ^ 2 * stoppedProcess (fun (t : ℝ≥0) (_ : Ω) ↦ (t : ℝ)) (exitTime M (n + 1)) s ω / 2) ∂P :=
  setIntegral_exp_eq (isSlowClock_stoppedProcess _)
    (martingale_stoppedProcess_exitTime hadapt hcont hM0 hM hM2 n).1
    (martingale_stoppedProcess_exitTime hadapt hcont hM0 hM hM2 n).2
    (abs_stoppedProcess_le hcont hM0 n) (continuous_stoppedProcess hcont _) a hst hS

/-! ### The limit `n → ∞` -/

/-- **The stopped exponentials converge on sets.** For a fixed time `r`, a set `S`, and every
`a`, the integrals over `S` of the stopped exponentials `exp(a·M^{ρₙ}_r − a²(r ∧ ρₙ)/2)` converge
to `∫_S exp(a·M_r − a²r/2)`. Pointwise the exponentials are eventually equal to the limit (the
exit times escape to `⊤`), and they are bounded in `L²` by `e^{a²r}`: the square is dominated by
`e^{a²r}` times the stopped exponential martingale at `2a`, which has expectation `1`. Vitali's
theorem (`tendsto_setIntegral_of_subseq_ae_of_sq_bound`) finishes. -/
theorem tendsto_setIntegral_stopped_exp (hadapt : StronglyAdapted 𝓕 M)
    (hcont : ∀ ω, Continuous fun t ↦ M t ω) (hM0 : ∀ ω, M 0 ω = 0)
    (hM : IsLocalMartingale M 𝓕 P) (hM2 : IsLocalMartingale (fun t ω ↦ M t ω ^ 2 - (t : ℝ)) 𝓕 P)
    (a : ℝ) (r : ℝ≥0) (S : Set Ω) :
    Tendsto (fun n : ℕ ↦ ∫ ω in S, Real.exp (a * stoppedProcess M (exitTime M (n + 1)) r ω
        - a ^ 2 * stoppedProcess (fun (t : ℝ≥0) (_ : Ω) ↦ (t : ℝ)) (exitTime M (n + 1)) r ω / 2) ∂P)
      atTop (𝓝 (∫ ω in S, Real.exp (a * M r ω - a ^ 2 * (r : ℝ) / 2) ∂P)) := by
  have hmart := martingale_stoppedProcess_exitTime hadapt hcont hM0 hM hM2
  have hexp (n : ℕ) (b : ℝ) := martingale_exp (isSlowClock_stoppedProcess
    (exitTime M (n + 1))) (hmart n).1 (hmart n).2 (abs_stoppedProcess_le hcont hM0 n)
    (continuous_stoppedProcess hcont _) b
  have hf (n : ℕ) : Measurable fun ω ↦ Real.exp (a * stoppedProcess M (exitTime M (n + 1)) r ω
      - a ^ 2 * stoppedProcess (fun (t : ℝ≥0) (_ : Ω) ↦ (t : ℝ)) (exitTime M (n + 1)) r ω / 2) :=
    (((hexp n a).stronglyAdapted r).mono (𝓕.le r)).measurable
  have hbd (n : ℕ) (ω : Ω) : |Real.exp (a * stoppedProcess M (exitTime M (n + 1)) r ω
      - a ^ 2 * stoppedProcess (fun (t : ℝ≥0) (_ : Ω) ↦ (t : ℝ)) (exitTime M (n + 1)) r ω / 2)|
      ≤ Real.exp (|a| * ((n + 1 : ℕ) : ℝ)) := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact exp_le_exp_abs_mul (isSlowClock_stoppedProcess _) (abs_stoppedProcess_le hcont hM0 n)
      a r ω
  have hmem (n : ℕ) : MemLp (fun ω ↦ Real.exp (a * stoppedProcess M (exitTime M (n + 1)) r ω
      - a ^ 2 * stoppedProcess (fun (t : ℝ≥0) (_ : Ω) ↦ (t : ℝ)) (exitTime M (n + 1)) r ω / 2)) 2 P :=
    (MemLp.of_bound (hf n).aestronglyMeasurable _
      (.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hbd n ω)).mono_exponent le_top
  have hB (n : ℕ) : ∫ ω, (Real.exp (a * stoppedProcess M (exitTime M (n + 1)) r ω
      - a ^ 2 * stoppedProcess (fun (t : ℝ≥0) (_ : Ω) ↦ (t : ℝ)) (exitTime M (n + 1)) r ω / 2)) ^ 2 ∂P
      ≤ Real.exp (a ^ 2 * (r : ℝ)) := by
    have hone : ∫ ω, Real.exp (2 * a * stoppedProcess M (exitTime M (n + 1)) r ω
        - (2 * a) ^ 2 * stoppedProcess (fun (t : ℝ≥0) (_ : Ω) ↦ (t : ℝ)) (exitTime M (n + 1)) r ω / 2) ∂P
        = 1 := by
      have h := setIntegral_stopped_exp_eq hadapt hcont hM0 hM hM2 n (2 * a) (zero_le : (0 : ℝ≥0) ≤ r)
        (S := Set.univ) MeasurableSet.univ
      simp only [Measure.restrict_univ] at h
      rw [h]
      have h0 : stoppedProcess M (exitTime M (n + 1)) 0 = 0 := by
        funext ω
        simp only [stoppedProcess, untopA_min_zero, hM0]; rfl
      have h0' := (isSlowClock_stoppedProcess (Ω := Ω) (exitTime M (n + 1))).zero
      simp [h0, h0']
    calc ∫ ω, Real.exp (a * stoppedProcess M (exitTime M (n + 1)) r ω
          - a ^ 2 * stoppedProcess (fun (t : ℝ≥0) (_ : Ω) ↦ (t : ℝ)) (exitTime M (n + 1)) r ω / 2) ^ 2 ∂P
        ≤ ∫ ω, Real.exp (a ^ 2 * (r : ℝ)) * Real.exp (2 * a * stoppedProcess M
            (exitTime M (n + 1)) r ω - (2 * a) ^ 2 * stoppedProcess (fun (t : ℝ≥0) (_ : Ω) ↦ (t : ℝ))
            (exitTime M (n + 1)) r ω / 2) ∂P := by
          refine integral_mono ?_ (((hexp n (2 * a)).integrable r).const_mul _) fun ω ↦ ?_
          · exact (hmem n).integrable_sq
          · rw [sq, ← Real.exp_add, ← Real.exp_add]
            refine Real.exp_le_exp.2 ?_
            have := (isSlowClock_stoppedProcess (Ω := Ω) (exitTime M (n + 1))).apply_le r ω
            nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg a)]
      _ = Real.exp (a ^ 2 * (r : ℝ)) := by rw [integral_const_mul, hone, mul_one]
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ Real.exp (a * stoppedProcess M (exitTime M (n + 1)) r ω
      - a ^ 2 * stoppedProcess (fun (t : ℝ≥0) (_ : Ω) ↦ (t : ℝ)) (exitTime M (n + 1)) r ω / 2)) atTop
      (𝓝 (Real.exp (a * M r ω - a ^ 2 * (r : ℝ) / 2))) := by
    refine .of_forall fun ω ↦ ?_
    have hr : ∀ᶠ n : ℕ in atTop, (r : WithTop ℝ≥0) < exitTime M (n + 1) ω :=
      (WithTop.tendsto_nhds_top_iff _).1
        ((exitTime_tendsto_top hcont ω).comp (tendsto_add_atTop_nat 1)) r
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hr] with n hn
    have hmin : min (r : WithTop ℝ≥0) (exitTime M (n + 1) ω) = r := min_eq_left hn.le
    simp only [stoppedProcess, hmin, coe_untopA]
  have hg : MemLp (fun ω ↦ Real.exp (a * M r ω - a ^ 2 * (r : ℝ) / 2)) 1 P :=
    (memLp_two_of_subseq_ae_of_sq_bound hmem hf hB ⟨id, hlim⟩).mono_exponent (by norm_num)
  exact tendsto_setIntegral_of_subseq_ae_of_sq_bound hmem hB hg
    (fun ns hns ↦ ⟨id, hlim.mono fun ω h ↦ h.comp hns⟩) S

/-- **Lévy's characterisation: the exponential-martingale data.** A continuous adapted local
martingale `M` with `M₀ = 0` and `M² − t` a local martingale satisfies `IsExpQMartingale P 𝓕 M T`
for every horizon `T`: the exponential martingale identity of the stopped processes
(`setIntegral_stopped_exp_eq`) passes to the limit (`tendsto_setIntegral_stopped_exp`). -/
theorem isExpQMartingale_of_localMartingale (hadapt : StronglyAdapted 𝓕 M)
    (hcont : ∀ ω, Continuous fun t ↦ M t ω) (hM0 : ∀ ω, M 0 ω = 0)
    (hM : IsLocalMartingale M 𝓕 P) (hM2 : IsLocalMartingale (fun t ω ↦ M t ω ^ 2 - (t : ℝ)) 𝓕 P)
    (T : ℝ≥0) : IsExpQMartingale P 𝓕 M T where
  adapted := hadapt
  zero_start := .of_forall hM0
  martingale a s t hst _ S hS := tendsto_nhds_unique
    (tendsto_setIntegral_stopped_exp hadapt hcont hM0 hM hM2 a t S)
    ((tendsto_setIntegral_stopped_exp hadapt hcont hM0 hM hM2 a s S).congr fun n ↦
      (setIntegral_stopped_exp_eq hadapt hcont hM0 hM hM2 n a hst hS).symm)

end Stopped

/-! ### Lévy's characterisation -/

/-- **Lévy's characterisation of Brownian motion (filtered form).** An adapted process `M` with
continuous paths and `M₀ = 0` such that `M` and `M² − t` are local martingales is a Brownian
motion for `𝓕`: it is pre-Brownian and every increment `M_t − M_s` is independent of `𝓕_s`. -/
theorem isFilteredPreBrownian_of_localMartingale (hadapt : StronglyAdapted 𝓕 M)
    (hcont : ∀ ω, Continuous fun t ↦ M t ω) (hM0 : ∀ ω, M 0 ω = 0)
    (hM : IsLocalMartingale M 𝓕 P) (hM2 : IsLocalMartingale (fun t ω ↦ M t ω ^ 2 - (t : ℝ)) 𝓕 P) :
    IsFilteredPreBrownian M 𝓕 P :=
  isFilteredPreBrownian_of_expMartingale (isExpQMartingale_of_localMartingale hadapt hcont hM0 hM hM2)

/-- **Lévy's characterisation of Brownian motion.** An adapted process `M` with continuous paths
and `M₀ = 0` such that `M` and `M² − t` are local martingales is a Brownian motion. -/
theorem isBrownianReal_of_localMartingale (hadapt : StronglyAdapted 𝓕 M)
    (hcont : ∀ ω, Continuous fun t ↦ M t ω) (hM0 : ∀ ω, M 0 ω = 0)
    (hM : IsLocalMartingale M 𝓕 P) (hM2 : IsLocalMartingale (fun t ω ↦ M t ω ^ 2 - (t : ℝ)) 𝓕 P) :
    IsBrownianReal M P :=
  isBrownianReal_of_expMartingale (isExpQMartingale_of_localMartingale hadapt hcont hM0 hM hM2)
    (.of_forall hcont)

end LevyCharacterization
end MathFin
