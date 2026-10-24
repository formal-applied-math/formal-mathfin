/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.CompactLocalization
public import MathFin.BlackScholes.AmericanPut.Stopping.BrownianInteriorLocalization

/-!
# Compact regions containing the interior-stopped trajectories

The frozen price/payoff gap is extended continuously to the whole time/driver
plane only to define closed compact regions. Smoothness is used exclusively
inside continuation, where physical time is strictly below maturity.

## Result

Public entry points include `planeClassicalGap`, `planeClassicalGap_continuous`,
`planeClassicalGap_eq`, `interiorRegion`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped NNReal Topology

/-- The classical price/payoff gap on the time/driver plane: time `Real.toNNReal z.1`, driver
frozen at `z.2`. -/
noncomputable def planeClassicalGap (p : ℝ → ℝ → ℝ) (K r q σ S : ℝ) (T : ℝ≥0)
    (z : ℝ × ℝ) : ℝ :=
  classicalGap (fun _ (_ : Unit) => z.2) K r q σ S p T (Real.toNNReal z.1) ()

theorem planeClassicalGap_continuous {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {k h K r q σ S : ℝ}
    (hp : DividendPutSolution k h p b) (T : ℝ≥0) :
    Continuous (planeClassicalGap p K r q σ S T) := by
  let s : ℝ × ℝ → ℝ≥0 := fun z => min (Real.toNNReal z.1) T
  have hs : Continuous (fun z => (s z : ℝ)) := by dsimp [s]; fun_prop
  have hc : Continuous (fun z : ℝ × ℝ =>
      p (Real.log (S/K)+(r-q-σ^2/2)*(s z : ℝ)+σ*z.2) (σ^2/2*((T : ℝ)-(s z : ℝ)))) :=
    hp.price_continuous.comp_continuous
      (show Continuous (fun z : ℝ × ℝ =>
        (Real.log (S/K)+(r-q-σ^2/2)*(s z : ℝ)+σ*z.2,σ^2/2*((T : ℝ)-(s z : ℝ)))) by fun_prop)
      (fun z => by
        change 0 ≤ σ^2/2*((T : ℝ)-(s z : ℝ))
        exact mul_nonneg (by positivity)
          (sub_nonneg.mpr (by exact_mod_cast min_le_right (Real.toNNReal z.1) T)))
  change Continuous (fun z : ℝ × ℝ =>
    Real.exp (-r*(s z : ℝ))*(K*p (Real.log (S/K)+(r-q-σ^2/2)*(s z : ℝ)+σ*z.2)
      (σ^2/2*((T : ℝ)-(s z : ℝ)))) -
    Real.exp (-r*(s z : ℝ))*max (K-MathFin.gbmValue S (r-q) σ (s z) z.2) 0)
  unfold MathFin.gbmValue
  exact ((show Continuous (fun z => Real.exp (-r*(s z : ℝ))) by fun_prop).mul
    (continuous_const.mul hc)).sub (by fun_prop)

theorem planeClassicalGap_eq {Ω : Type*} (W : ℝ≥0 → Ω → ℝ)
    (p : ℝ → ℝ → ℝ) (K r q σ S : ℝ) {T t : ℝ≥0} (ht : t ≤ T) (ω : Ω) :
    planeClassicalGap p K r q σ S T (t,W t ω) = classicalGap W K r q σ S p T t ω := by
  simp [planeClassicalGap,classicalGap,classicalCandidate,classicalLogSpot,
    frozenPutReward,putReward,Real.toNNReal_coe,min_eq_left ht]

/-- The plane points with time in `[0,T]`, driver in `[-(n+1),n+1]`, gap at least
`localizationEps n`, and at least that much maturity left. -/
def interiorRegion (p : ℝ → ℝ → ℝ) (K r q σ S : ℝ) (T : ℝ≥0) (n : ℕ) : Set (ℝ × ℝ) :=
  (Icc 0 (T : ℝ) ×ˢ Icc (-(n : ℝ)-1) ((n : ℝ)+1)) ∩
    {z | localizationEps n ≤ planeClassicalGap p K r q σ S T z ∧
      z.1+localizationEps n ≤ T}

theorem interiorRegion_isCompact {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {k h K r q σ S : ℝ}
    (hp : DividendPutSolution k h p b) (T : ℝ≥0) (n : ℕ) :
    IsCompact (interiorRegion p K r q σ S T n) :=
  (isCompact_Icc.prod isCompact_Icc).inter_right
    ((isClosed_le continuous_const (planeClassicalGap_continuous hp T)).inter
      (isClosed_le (show Continuous (fun z : ℝ × ℝ => z.1+localizationEps n) by fun_prop)
        continuous_const))

theorem interiorRegion_subset_continuation {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {k h K r q σ S : ℝ}
    (hp : DividendPutSolution k h p b) (hK : 0 < K) (hS : 0 < S) (hσ : 0 < σ)
    (T : ℝ≥0) (n : ℕ) :
    interiorRegion p K r q σ S T n ⊆ kernelContinuation b r q σ (Real.log (S/K)) T := by
  intro z hz
  have ht : z.1 < T := by linarith [hz.2.2,localizationEps_pos n]
  refine ⟨ht,lt_of_not_ge ?_⟩
  intro hx
  have ht' : Real.toNNReal z.1 < T := by
    exact_mod_cast (show (Real.toNNReal z.1 : ℝ) < T by rw [Real.coe_toNNReal _ hz.1.1.1]; exact ht)
  have hzero := (classicalGap_zero_iff (W := fun _ (_ : Unit) => z.2) hp hK hS hσ ht' ()).mpr
    (by simpa [classicalLogSpot,Real.coe_toNNReal _ hz.1.1.1] using hx)
  change planeClassicalGap p K r q σ S T z = 0 at hzero
  linarith [hz.2.1,localizationEps_pos n]

theorem brownianInteriorRule_mem_region {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {K r q σ S : ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    {T : ℝ≥0} {n : ℕ} (ω : ℝ≥0 → ℝ)
    (hpos : 0 < (brownianInteriorRule (K := K) (S := S) hp T n).time ω)
    {t : ℝ≥0} (ht : t ≤ (brownianInteriorRule (K := K) (S := S) hp T n).time ω) :
    ((t : ℝ),brownian t ω) ∈ interiorRegion p K r q σ S T n := by
  have hm : localizationEps n ≤ classicalGap brownian K r q σ S p T t ω ∧
      |brownian t ω| ≤ (n : ℝ)+1 ∧ (t : ℝ)+localizationEps n ≤ T := by
    rcases lt_or_eq_of_le ht with hlt | heq
    · have hh := interiorRule_before (classicalGap_adapted hp brownian_adapted T) brownian_adapted
        (classicalGap_continuous hp continuous_brownian T) continuous_brownian ω hlt
      exact ⟨hh.1.le,hh.2.1.le,hh.2.2.le⟩
    · subst t
      exact interiorRule_at_positive_exit (classicalGap_adapted hp brownian_adapted T)
          brownian_adapted
        (classicalGap_continuous hp continuous_brownian T) continuous_brownian ω hpos
  have htT : t ≤ T := ht.trans ((brownianInteriorRule hp T n).le_horizon ω)
  refine ⟨⟨⟨t.coe_nonneg,by exact_mod_cast htT⟩,?_,(abs_le.mp hm.2.1).2⟩,?_,hm.2.2⟩
  · linarith [(abs_le.mp hm.2.1).1]
  · rw [planeClassicalGap_eq brownian p K r q σ S htT ω]
    exact hm.1

theorem brownianInteriorRule_smooth_extension {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {K r q σ S : ℝ}
    (hp : DividendPutSolution (normalizedRate r σ) (normalizedRate q σ) p b)
    (hK : 0 < K) (hS : 0 < S) (hσ : 0 < σ) (T : ℝ≥0) (n : ℕ) :
    ∃ G : ℝ × ℝ → ℝ, ContDiff ℝ 3 G ∧ HasCompactSupport G ∧
      ∀ ω, 0 < (brownianInteriorRule (K := K) (S := S) hp T n).time ω →
        ∀ t ≤ (brownianInteriorRule (K := K) (S := S) hp T n).time ω,
          G (t,brownian t ω) = classicalCandidate brownian K r q σ S p T t ω ∧
          planeGenerator G (t,brownian t ω) = 0 := by
  obtain ⟨G,hG,hcompact,heq,hzero⟩ := brownianPriceKernel_compact_localization (K := K) hp hσ
    (interiorRegion_isCompact (K := K) (S := S) hp T n)
    (interiorRegion_subset_continuation hp hK hS hσ T n)
  refine ⟨G,hG,hcompact,?_⟩
  intro ω hpos t ht
  have hz := brownianInteriorRule_mem_region hp ω hpos ht
  refine ⟨?_,hzero _ hz⟩
  rw [classicalCandidate_eq_kernel brownian p K r q σ S
    (ht.trans ((brownianInteriorRule hp T n).le_horizon ω)) ω]
  exact heq.self_of_nhdsSet hz

end MathFin.BlackScholes.AmericanPut.Stopping
