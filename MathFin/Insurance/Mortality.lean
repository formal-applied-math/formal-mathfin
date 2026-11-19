/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Adam Kiezun
-/
module

public import MathFin.Models.Credit.HazardCurve
public import MathFin.Probability.Analysis.ExponentialDiscount
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Force of mortality and survival functions

The classical actuarial setup. Let `S : ℝ → ℝ` denote a survival function
(`S(t) = P(T > t)` where `T` is the time of death). The **force of mortality**
at age `t` is

  `μ(t) := -S'(t) / S(t) = -d/dt log S(t)`,

so survival reconstructs from the force as

  `S(t) = exp(-∫₀^t μ(u) du)`.

Under a **Gompertz** mortality law `μ(t) = B · e^{c·t}`:

  `∫₀^t μ(u) du = (B/c) · (e^{c·t} - 1)`,

so `S(t) = exp(-(B/c)·(e^{c·t} - 1))`. The structural identity in this file is
the FTC connection between cumulative force and survival.

We mirror `Models/Credit/HazardCurve.lean` (which formalizes the same exponential
identity for credit hazard) — the actuarial and credit terminologies share the
same calculus.

## Main definitions

* `forceCumulative`: the cumulative force of mortality `∫₀^t μ(u) du`.
* `survivalFromForce`: the survival probability `exp(−∫₀^t μ(u) du)` built from the force `μ`.
* `IsLundbergAdjustmentCoefficient`: the adjustment-coefficient equation
  `λ · (M(R) − 1) − c · R = 0`.
* `thieleFactor`: the Thiele discount factor, the discount at the force of interest times the
  survival probability `hazardSurvival μ s / hazardSurvival μ t` of the force of mortality.
* `thieleReserve`: the prospective reserve, the `thieleFactor`-discounted future death benefits
  less premiums plus the terminal payment.

## Main results

* `survivalFromForce_at_zero`: `S(0) = 1`.
* `survivalFromForce_pos`: positivity.
* `gompertz_cumulative_force`: for `c ≠ 0`, `∫₀^t B·e^{c·u} du = (B/c)·(e^{c·t} − 1)`.
* `thieleFactor_eq_exp_neg_integral`: the factor is `exp(−∫ₜˢ (δ + μ))`.
* `hasDerivAt_thieleReserve`: Thiele's equation `V' = (δ + μ) V + π − μ b` for the
  prospective reserve integral `thieleReserve`, at interior times.

## References

* [Bowers and others, *Actuarial Mathematics*][BowersEtAl]
* [D. C. M. Dickson, M. R. Hardy and H. R. Waters, *Actuarial Mathematics for Life
  Contingent Risks*][DicksonHardyWaters2013], Chapter 7
  (policy values, Thiele's differential equation)

## Tags

force of mortality, hazard rate, Gompertz law, survival function, mortality law, cumulative hazard,
MSC 91G05, JEL G22
-/

@[expose] public section

namespace MathFin

open Real MeasureTheory intervalIntegral

/-- Cumulative force of mortality `∫₀^t μ(u) du` — the mortality instance of the
shared `cumulativeIntensity` (`Probability/Analysis/ExponentialDiscount`). -/
noncomputable def forceCumulative (μ : ℝ → ℝ) (t : ℝ) : ℝ :=
  cumulativeIntensity μ t

/-- Survival probability from the force of mortality `S(t) = exp(-∫₀^t μ(u) du)` —
the mortality instance of the shared `survivalFromIntensity`. -/
noncomputable def survivalFromForce (μ : ℝ → ℝ) (t : ℝ) : ℝ :=
  survivalFromIntensity μ t

/-- `S(0) = 1` (no mortality before age `0`). -/
lemma survivalFromForce_at_zero (μ : ℝ → ℝ) :
    survivalFromForce μ 0 = 1 :=
  survivalFromIntensity_zero μ

/-- Survival is strictly positive (an instance of the `ExponentialDiscount`
principle `discount_pos`). -/
lemma survivalFromForce_pos (μ : ℝ → ℝ) (t : ℝ) :
    0 < survivalFromForce μ t := discount_pos _

/-- **Force of mortality as the negative log-derivative of survival** — the
recovery direction `μ(t) = −d/dt log S(t)` that the classical definition
`μ(t) = −S'(t)/S(t)` encodes: for continuous `μ`, the mortality instance of
`hasDerivAt_neg_log_survivalFromIntensity`. -/
theorem force_eq_neg_log_deriv_survival {μ : ℝ → ℝ} (t : ℝ)
    (hμ : Continuous μ) :
    HasDerivAt (fun s ↦ -(Real.log (survivalFromForce μ s))) (μ t) t :=
  hasDerivAt_neg_log_survivalFromIntensity hμ t

/-- **Gompertz cumulative force** in closed form:
`∫₀^t B · e^{c u} du = (B/c) · (e^{c t} − 1)` for `c ≠ 0`. -/
theorem gompertz_cumulative_force (B c t : ℝ) (hc : c ≠ 0) :
    ∫ u in (0:ℝ)..t, B * Real.exp (c * u) =
      (B / c) * (Real.exp (c * t) - 1) := by
  -- Antiderivative: (B/c) e^{c u}. Use FTC for HasDerivAt.
  have h_anti : ∀ u, HasDerivAt (fun u ↦ (B / c) * Real.exp (c * u))
                      (B * Real.exp (c * u)) u := by
    intro u
    have h_cu : HasDerivAt (fun u : ℝ ↦ c * u) c u := by
      have := (hasDerivAt_id u).const_mul c
      simpa using this
    have h_exp : HasDerivAt (fun u ↦ Real.exp (c * u))
                  (Real.exp (c * u) * c) u := h_cu.exp
    have h := h_exp.const_mul (B / c)
    rw [show B * Real.exp (c * u) = B / c * (Real.exp (c * u) * c) from by field_simp]
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ h_anti u)
        (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp [Real.exp_zero]
  ring

/-! ## Compound Poisson MGF (folded from `CompoundPoisson.lean`)

For `N ~ Poisson(λ)` with iid claim sizes `X_i` of MGF `M_X`, the compound
Poisson aggregate `S = ∑_{i=1}^N X_i` has MGF `exp(λ · (M_X(t) − 1))`.
The algebraic core is `e^{−λ} · e^{λ M} = e^{λ(M − 1)}`. The Lundberg
adjustment coefficient solves `λ · (M(R) − 1) − c · R = 0`. -/

/-- **Compound Poisson MGF algebraic core**: `e^{−λ} · e^{λ M} = e^{λ(M − 1)}`. -/
theorem compoundPoisson_mgf_identity (lam M : ℝ) :
    Real.exp (-lam) * Real.exp (lam * M) = Real.exp (lam * (M - 1)) := by
  rw [← Real.exp_add]
  congr 1; ring

/-- **Lundberg adjustment-coefficient equation**: `λ · (M(R) − 1) − c · R = 0`. -/
def IsLundbergAdjustmentCoefficient (lam c R : ℝ) (M : ℝ → ℝ) : Prop :=
  lam * (M R - 1) - c * R = 0

/-- **Trivial root at zero**: `R = 0` always satisfies the adjustment equation
when `M 0 = 1` (which holds for any MGF). -/
theorem lundberg_zero_at_zero (lam c : ℝ) (M : ℝ → ℝ) (hM0 : M 0 = 1) :
    IsLundbergAdjustmentCoefficient lam c 0 M := by
  unfold IsLundbergAdjustmentCoefficient
  rw [hM0]
  ring

/-- The **Thiele discount factor** from `t` to `s`: the discount `exp(−∫ₜˢ δ)` at the force of
interest `δ`, times the survival factor `hazardSurvival μ s / hazardSurvival μ t` from `t` to `s`
under the force of mortality `μ`, a probability when `μ ≥ 0`
(`survivalFromForce μ = hazardSurvival μ`, the credit survival curve of
`Models/Credit/HazardCurve.lean`). -/
noncomputable def thieleFactor (δ μ : ℝ → ℝ) (t s : ℝ) : ℝ :=
  Real.exp (-∫ u in t..s, δ u) * (hazardSurvival μ s / hazardSurvival μ t)

/-- **The Thiele factor is the exponential of the integrated force of interest plus mortality**:
`thieleFactor δ μ t s = exp(−∫ₜˢ (δ + μ))`, when `δ` is integrable on `[t, s]` and `μ` on
`[0, t]` and `[0, s]`. -/
theorem thieleFactor_eq_exp_neg_integral {δ μ : ℝ → ℝ} {t s : ℝ}
    (hδ : IntervalIntegrable δ volume t s) (hμt : IntervalIntegrable μ volume 0 t)
    (hμs : IntervalIntegrable μ volume 0 s) :
    thieleFactor δ μ t s = Real.exp (-∫ u in t..s, (δ u + μ u)) := by
  rw [thieleFactor, hazardSurvival, hazardSurvival, survivalFromIntensity, survivalFromIntensity,
    cumulativeIntensity, cumulativeIntensity, ← Real.exp_sub, ← Real.exp_add,
    integral_add hδ (hμt.symm.trans hμs), ← integral_interval_sub_left hμs hμt]
  congr 1
  ring

/-- Prospective reserve at time `t`: the discounted value of future benefits
minus premiums plus the discounted terminal payment `g`, all discounted with
`thieleFactor`. -/
noncomputable def thieleReserve (δ μ prem b : ℝ → ℝ) (g T t : ℝ) : ℝ :=
  (∫ s in t..T, thieleFactor δ μ t s * (μ s * b s - prem s)) + thieleFactor δ μ t T * g

/-- **Thiele's differential equation.** At each interior time `t`, the reserve
`V` satisfies `V' = (δ + μ) * V + prem - μ * b`. The proof factors the discount
factor as `S s / S t` with `S u = exp (-∫₀ᵘ (δ + μ))`, so `V` is a quotient of
an integral (depending on `t` only through its lower limit) by `S`, and applies
the fundamental theorem of calculus with the quotient rule. -/
theorem hasDerivAt_thieleReserve (δ μ prem b : ℝ → ℝ) (g T : ℝ) (hT : 0 < T)
    (hδ : ContinuousOn δ (Set.Icc 0 T)) (hμ : ContinuousOn μ (Set.Icc 0 T))
    (hprem : ContinuousOn prem (Set.Icc 0 T)) (hb : ContinuousOn b (Set.Icc 0 T))
    (t : ℝ) (ht0 : 0 < t) (htT : t < T) :
    HasDerivAt (thieleReserve δ μ prem b g T)
      ((δ t + μ t) * thieleReserve δ μ prem b g T t + prem t - μ t * b t) t := by
  set lam : ℝ → ℝ := fun u => δ u + μ u
  set S : ℝ → ℝ := fun u => Real.exp (-∫ v in (0:ℝ)..u, lam v)
  set G : ℝ → ℝ := fun s => S s * (μ s * b s - prem s)
  set A : ℝ → ℝ := fun u => (∫ s in u..T, G s) + S T * g
  have hlamC : ContinuousOn lam (Set.Icc 0 T) := hδ.add hμ
  have hP : ContinuousOn (fun u => ∫ v in (0:ℝ)..u, lam v) (Set.uIcc 0 T) :=
    continuousOn_primitive_interval'
      (ContinuousOn.intervalIntegrable_of_Icc hT.le hlamC) Set.left_mem_uIcc
  have hSC : ContinuousOn S (Set.Icc 0 T) := by
    have hP' : ContinuousOn (fun u => ∫ v in (0:ℝ)..u, lam v) (Set.Icc 0 T) := by
      rw [← Set.uIcc_of_le hT.le]
      exact hP
    exact Real.continuous_exp.comp_continuousOn hP'.neg
  have hGC : ContinuousOn G (Set.Icc 0 T) := hSC.mul ((hμ.mul hb).sub hprem)
  have hmem : Set.Icc (0:ℝ) T ∈ nhds t := Icc_mem_nhds ht0 htT
  have hlamAt : ∀ x ∈ Set.Ioo (0:ℝ) T, ContinuousAt lam x :=
    fun x hx => hlamC.continuousAt (Icc_mem_nhds hx.1 hx.2)
  have hGAt : ∀ x ∈ Set.Ioo (0:ℝ) T, ContinuousAt G x :=
    fun x hx => hGC.continuousAt (Icc_mem_nhds hx.1 hx.2)
  have hlamM : StronglyMeasurableAtFilter lam (nhds t) volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo hlamAt t ⟨ht0, htT⟩
  have hGM : StronglyMeasurableAtFilter G (nhds t) volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo hGAt t ⟨ht0, htT⟩
  have htT' : t ≤ T := htT.le
  have hlamInt0t : IntervalIntegrable lam volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht0.le
      (hlamC.mono (Set.Icc_subset_Icc le_rfl htT'))
  have hGInt : IntervalIntegrable G volume t T :=
    ContinuousOn.intervalIntegrable_of_Icc htT'
      (hGC.mono (Set.Icc_subset_Icc ht0.le le_rfl))
  have hPderiv : HasDerivAt (fun u => ∫ v in (0:ℝ)..u, lam v) (lam t) t :=
    integral_hasDerivAt_right hlamInt0t hlamM (hlamAt t ⟨ht0, htT⟩)
  have hSderiv : HasDerivAt S (S t * -lam t) t := by
    have h1 : HasDerivAt (fun u => -∫ v in (0:ℝ)..u, lam v) (-lam t) t :=
      hPderiv.neg
    exact h1.exp
  have hAderiv : HasDerivAt A (-G t) t := by
    have h1 : HasDerivAt (fun u => ∫ s in u..T, G s) (-G t) t :=
      integral_hasDerivAt_left hGInt hGM (hGAt t ⟨ht0, htT⟩)
    have h2 : HasDerivAt (fun _ => S T * g) 0 t := hasDerivAt_const t (S T * g)
    have h3 : HasDerivAt ((fun u => ∫ s in u..T, G s) + (fun _ => S T * g))
        (-G t) t := by
      simpa using h1.add h2
    exact h3
  have hSapp : ∀ v : ℝ, S v = Real.exp (-∫ w in (0:ℝ)..v, lam w) :=
    fun v => rfl
  have hSt : S t ≠ 0 := by
    rw [hSapp t]
    exact Real.exp_ne_zero _
  have hdiv : HasDerivAt (A / S)
      ((-G t * S t - A t * (S t * -lam t)) / S t ^ 2) t :=
    HasDerivAt.div hAderiv hSderiv hSt
  have hGs : ∀ s : ℝ, G s = S s * (μ s * b s - prem s) := fun s => rfl
  have hlamt : lam t = δ t + μ t := rfl
  have hI (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 T)) {a b : ℝ} (ha : a ∈ Set.Icc (0:ℝ) T)
      (hb : b ∈ Set.Icc (0:ℝ) T) : IntervalIntegrable f volume a b :=
    (hf.mono (Set.uIcc_subset_Icc ha hb)).intervalIntegrable
  have hFactor : ∀ u ∈ Set.Icc (0:ℝ) T, ∀ s ∈ Set.Icc (0:ℝ) T,
      thieleFactor δ μ u s = S s / S u := by
    intro u hu s hs
    have h0 : (0 : ℝ) ∈ Set.Icc (0:ℝ) T := ⟨le_rfl, hT.le⟩
    rw [thieleFactor_eq_exp_neg_integral (hI δ hδ hu hs) (hI μ hμ h0 hu) (hI μ hμ h0 hs)]
    change Real.exp (-∫ v in u..s, lam v) = Real.exp (-∫ v in (0:ℝ)..s, lam v)
      / Real.exp (-∫ v in (0:ℝ)..u, lam v)
    rw [← Real.exp_sub, ← integral_interval_sub_left (hI lam hlamC h0 hs) (hI lam hlamC h0 hu)]
    congr 1
    ring
  have hAu : ∀ u : ℝ, A u = (∫ s in u..T, G s) + S T * g := fun u => rfl
  have hVeq : ∀ u ∈ Set.Icc (0:ℝ) T, thieleReserve δ μ prem b g T u = A u / S u := by
    intro u hu
    have hsub2 : Set.uIcc u T ⊆ Set.Icc (0:ℝ) T := by
      rw [Set.uIcc_of_le hu.2]
      exact Set.Icc_subset_Icc hu.1 le_rfl
    have hInt : (∫ s in u..T, thieleFactor δ μ u s * (μ s * b s - prem s))
        = (∫ s in u..T, G s) / S u := by
      rw [← intervalIntegral.integral_div]
      apply integral_congr
      intro s hs
      change thieleFactor δ μ u s * (μ s * b s - prem s) = G s / S u
      have hsT : s ∈ Set.Icc (0:ℝ) T := hsub2 hs
      rw [hFactor u hu s hsT, hGs s, div_mul_eq_mul_div]
    have hFT : thieleFactor δ μ u T * g = (S T * g) / S u := by
      rw [hFactor u hu T ⟨hT.le, le_rfl⟩, div_mul_eq_mul_div]
    rw [show thieleReserve δ μ prem b g T u
        = (∫ s in u..T, thieleFactor δ μ u s * (μ s * b s - prem s))
          + thieleFactor δ μ u T * g from rfl, hInt, hFT, ← add_div, hAu u]
  have heq : thieleReserve δ μ prem b g T =ᶠ[nhds t] (A / S) := by
    change ∀ᶠ u in nhds t, thieleReserve δ μ prem b g T u = (A / S) u
    exact Filter.eventually_of_mem hmem
      (fun u hu => by simp only [hVeq u hu, Pi.div_apply])
  have hmain := hdiv.congr_of_eventuallyEq heq
  have hAS : (A t / S t) * (S t ^ 2) = A t * S t := by
    rw [pow_two, ← mul_assoc, div_mul_cancel₀ _ hSt]
  have hD : (-G t * S t - A t * (S t * -lam t)) / S t ^ 2
      = (δ t + μ t) * thieleReserve δ μ prem b g T t + prem t - μ t * b t := by
    rw [hVeq t ⟨ht0.le, htT.le⟩, hGs t, hlamt, div_eq_iff (pow_ne_zero 2 hSt)]
    field_simp
    ring
  rw [← hD]
  exact hmain

end MathFin
