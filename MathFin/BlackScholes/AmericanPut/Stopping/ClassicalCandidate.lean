/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.Verification
public import MathFin.BlackScholes.AmericanPut.Boundary.ContinuousBoundaryProblem

/-!
# The discounted classical-price candidate

The process is frozen at maturity. Its continuity, boundedness and payoff
domination follow from `PutEnvelope p` alone: the price is continuous, lies between the payoff
and the strike, and equals the payoff at expiry. No PDE, boundary or smoothness is used, so the
results apply to any such price, classical or the stopping value itself. Supermartingality and the
contact-rule martingale property are NOT asserted here; they are the remaining
stochastic verification obligations.

## Result

Public entry points include `classicalLogSpot`, `classicalCandidate`, `scaled_classical_payoff`,
`classicalCandidate_bounds`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory Set
open MathFin.BlackScholes.AmericanPut.Boundary
open scoped NNReal

variable {Ω : Type*}

/-- The strike-normalized log spot `log (S/K)+(r-q-σ^2/2)*t+σ*W t ω`. -/
noncomputable def classicalLogSpot (W : ℝ≥0 → Ω → ℝ) (K r q σ S : ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.log (S/K)+(r-q-σ^2/2)*(t : ℝ)+σ*W t ω

/-- The discounted classical price `K*p` along the log spot, frozen at maturity: evaluated at
`min t T` with remaining normalized time `σ^2/2*(T-min t T)`. -/
noncomputable def classicalCandidate (W : ℝ≥0 → Ω → ℝ) (K r q σ S : ℝ)
    (p : ℝ → ℝ → ℝ) (T t : ℝ≥0) (ω : Ω) : ℝ :=
  let s := min t T
  Real.exp (-r*(s : ℝ))*
    (K*p (classicalLogSpot W K r q σ S s ω) (σ^2/2*((T : ℝ)-(s : ℝ))))

theorem scaled_classical_payoff (W : ℝ≥0 → Ω → ℝ) {K r q σ S : ℝ}
    (hK : 0 < K) (hS : 0 < S) (t : ℝ≥0) (ω : Ω) :
    K*putPayoff (classicalLogSpot W K r q σ S t ω) =
      max (K-MathFin.gbmValue S (r-q) σ t (W t ω)) 0 := by
  have he : K*Real.exp (classicalLogSpot W K r q σ S t ω) =
      MathFin.gbmValue S (r-q) σ t (W t ω) := by
    simp only [classicalLogSpot,Real.exp_add,Real.exp_log (div_pos hS hK),MathFin.gbmValue]
    field_simp
  unfold putPayoff
  rw [mul_max_of_nonneg _ _ hK.le,mul_zero,mul_sub,mul_one,he]

theorem classicalCandidate_bounds {K r q σ S : ℝ} {p : ℝ → ℝ → ℝ}
    (hp : PutEnvelope p) (W : ℝ≥0 → Ω → ℝ)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (T t : ℝ≥0) (ω : Ω) :
    0 ≤ classicalCandidate W K r q σ S p T t ω ∧
      classicalCandidate W K r q σ S p T t ω ≤ K := by
  have ht : 0 ≤ σ^2/2*((T : ℝ)-(min t T : ℝ)) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr (by exact_mod_cast min_le_right t T))
  have hlo := (le_max_right (1-Real.exp (classicalLogSpot W K r q σ S (min t T) ω)) 0).trans
    (hp.dominates _ _ ht)
  have hhi := hp.bounded (classicalLogSpot W K r q σ S (min t T) ω) _ ht
  have he : Real.exp (-r*(min t T : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr) (min t T).coe_nonneg)
  dsimp only [classicalCandidate]
  constructor
  · exact mul_nonneg (Real.exp_pos _).le (mul_nonneg hK hlo)
  · calc
      _ ≤ 1*(K*p (classicalLogSpot W K r q σ S (min t T) ω)
          (σ^2/2*((T : ℝ)-(min t T : ℝ)))) :=
        mul_le_mul_of_nonneg_right he (mul_nonneg hK hlo)
      _ ≤ K := by simpa only [one_mul,mul_one] using mul_le_mul_of_nonneg_left hhi hK

theorem classicalCandidate_dominates {K r q σ S : ℝ} {p : ℝ → ℝ → ℝ}
    (hp : PutEnvelope p) (W : ℝ≥0 → Ω → ℝ)
    (hK : 0 < K) (hS : 0 < S) {T t : ℝ≥0} (ht : t ≤ T) (ω : Ω) :
    putReward W K r q σ S (fun _ => t) ω ≤ classicalCandidate W K r q σ S p T t ω := by
  have htime : 0 ≤ σ^2/2*((T : ℝ)-(t : ℝ)) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr (by exact_mod_cast ht))
  simpa only [classicalCandidate,min_eq_left ht,putReward,scaled_classical_payoff W hK hS] using
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (hp.dominates (classicalLogSpot W K r q σ S t ω) _ htime) hK.le)
          (Real.exp_pos (-r*(t : ℝ))).le

theorem classicalCandidate_continuous {K r q σ S : ℝ} {p : ℝ → ℝ → ℝ}
    (hp : PutEnvelope p) {W : ℝ≥0 → Ω → ℝ}
    (hW : ∀ ω, Continuous (fun t => W t ω)) (T : ℝ≥0) (ω : Ω) :
    Continuous (fun t => classicalCandidate W K r q σ S p T t ω) := by
  have hlog : Continuous (fun t => classicalLogSpot W K r q σ S (min t T) ω) := by
    unfold classicalLogSpot
    fun_prop
  have ht : Continuous (fun t : ℝ≥0 => σ^2/2*((T : ℝ)-(min t T : ℝ))) := by fun_prop
  have hpcont : Continuous (fun t : ℝ≥0 => p (classicalLogSpot W K r q σ S (min t T) ω)
      (σ^2/2*((T : ℝ)-(min t T : ℝ)))) :=
    hp.price_continuous.comp_continuous (hlog.prodMk ht) (fun t => by
      change 0 ≤ σ^2/2*((T : ℝ)-(min t T : ℝ))
      exact mul_nonneg (by positivity) (sub_nonneg.mpr (by exact_mod_cast min_le_right t T)))
  unfold classicalCandidate
  exact (show Continuous (fun t : ℝ≥0 => Real.exp (-r*(min t T : ℝ))) by fun_prop).mul
    (continuous_const.mul hpcont)

theorem classicalCandidate_maturity {K r q σ S : ℝ} {p : ℝ → ℝ → ℝ}
    (hp : PutEnvelope p) (W : ℝ≥0 → Ω → ℝ)
    (hK : 0 < K) (hS : 0 < S) (T : ℝ≥0) (ω : Ω) :
    classicalCandidate W K r q σ S p T T ω = putReward W K r q σ S (fun _ => T) ω := by
  simp only [classicalCandidate,min_self,sub_self,mul_zero,hp.initial,
    scaled_classical_payoff W hK hS,putReward]

theorem classicalCandidate_initial [MeasurableSpace Ω] {P : Measure Ω}
    {W : ℝ≥0 → Ω → ℝ} (hzero : ∀ᵐ ω ∂P, W 0 ω = 0)
    (K r q σ S : ℝ) (p : ℝ → ℝ → ℝ) (T : ℝ≥0) :
    classicalCandidate W K r q σ S p T 0 =ᵐ[P]
      fun _ => K*p (Real.log (S/K)) (σ^2/2*(T : ℝ)) := by
  filter_upwards [hzero] with ω hω
  simp [classicalCandidate,classicalLogSpot,hω]

/-- Classical price identification reduced to the actual candidate's two
stochastic properties and an admissible contact rule. These hypotheses remain
explicit: this is not yet PDE-to-stopping verification. -/
theorem classical_price_eq_value_of_verification [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → ℝ}
    {K r q σ S : ℝ} {p : ℝ → ℝ → ℝ} {T : ℝ≥0}
    (hp : PutEnvelope p) (hW : Measurable W.uncurry)
    (hpaths : ∀ ω, Continuous (fun t => W t ω)) (hzero : ∀ᵐ ω ∂P, W 0 ω = 0)
    (hK : 0 < K) (hr : 0 ≤ r) (hS : 0 < S)
    (hsuper : Supermartingale (classicalCandidate W K r q σ S p T) 𝓕 P)
    (θ : StoppingRule 𝓕 T)
    (hcontact : ∀ᵐ ω ∂P, classicalCandidate W K r q σ S p T (θ.time ω) ω =
      putReward W K r q σ S θ.time ω)
    (hmart : Martingale (fun t ω => classicalCandidate W K r q σ S p T
      (min t (θ.time ω)) ω) 𝓕 P) :
    americanPutValue P 𝓕 W K r q σ S T = K*p (Real.log (S/K)) (σ^2/2*(T : ℝ)) := by
  have hbound : ∀ t ω, ‖classicalCandidate W K r q σ S p T t ω‖ ≤ K := by
    intro t ω
    obtain ⟨hlo,hhi⟩ := classicalCandidate_bounds (q := q) (σ := σ) (S := S) hp W hK.le hr T t ω
    simpa only [Real.norm_eq_abs,abs_of_nonneg hlo] using hhi
  rw [value_eq_of_contact_martingale hW hK.le hr hS.le hsuper
    (classicalCandidate_continuous hp hpaths T) hbound
    (fun _ ht ω => classicalCandidate_dominates hp W hK hS ht ω) θ hcontact hmart,
    integral_congr_ae (classicalCandidate_initial hzero K r q σ S p T)]
  simp

end MathFin.BlackScholes.AmericanPut.Stopping
