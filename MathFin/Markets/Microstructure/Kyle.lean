/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Init
public import MathFin.Probability.Gaussian.BivariateGaussian
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Integration

/-!
# The Kyle single-period equilibrium

Kyle's one-period model (the first section of his 1985 paper) derives price impact from strategic
informed trading. A fundamental value `v ∼ N(p₀, σ_v²)` is observed by one informed trader; noise
traders submit `u ∼ N(0, σ_u²)`, independent of `v`; a competitive market maker clears the batch
`x + u` at a linear price `p = p₀ + λ·(x + u)`. The informed trader of signal `c = v − p₀` submits
the linear demand `x = β·c`. For `σ_v, σ_u > 0` the linear equilibrium exists and its coefficients
are `β = σ_u/σ_v` and `λ = σ_v/(2σ_u)`: the price-impact constant of the model.

Unlike the Glosten–Milgrom modules of this area, the model has a strategic informed trader
choosing a quantity and batch clearing against their sequential direction trades. The two share
the market-maker reading of a price as a conditional expectation of the value: here
`E[v | x + u] = p` is derived from the bivariate Gaussian projection of
`Probability/Gaussian/BivariateGaussian.lean`. The prior mean `p₀` enters the model only as the
location of `v` and of the price: no coefficient depends on its value. Uniqueness of the
equilibrium among all demands is a separate open problem and is not claimed here.

## Main definitions

* `KyleModel`: the model bundle — Gaussian value and noise, their means and variances, and their
  independence.
* `kyleFlow`: the order flow `β · (v − p₀) + u` of the linear demand against the noise.

## Main results

* `kyleConditionalProfit`: the informed trader's expected profit given the signal is the
  quadratic `(v − p₀)·x − λ·x²`, almost surely (the noise term vanishes under independence).
* `kyleMarketEfficiency`: for any demand slope `β`, the market maker's linear rule with slope
  `λ = β·σ_v²/(β²·σ_v² + σ_u²)` is the conditional expectation of the value given the order flow,
  almost surely.
* `kyleEquilibriumCoefficients`: a pair `(β, λ)` whose demand is an unrestricted best response at
  every signal and whose pricing rule is efficient has `λ = σ_v/(2σ_u)` and `β = σ_u/σ_v`.
* `existsKyleEquilibrium`: the pair `β = σ_u/σ_v, λ = σ_v/(2σ_u)` satisfies both conditions: the
  linear equilibrium exists.
* `kyleModel_prod`: the model hypotheses are satisfiable, witnessed by independent Gaussian
  coordinates.

## References

* [A. S. Kyle, *Continuous Auctions and Insider Trading*][Kyle1985], §1

## Tags

Kyle model, price impact, market microstructure, informed trading, adverse selection, linear
equilibrium, conditional expectation, MSC 91B26, MSC 91G14, JEL D82, JEL G14
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {v u : Ω → ℝ} {p₀ σ_v σ_u : ℝ}

/-- The Kyle model: a Gaussian fundamental value `v` of mean `p₀` and variance `σ_v²`, and
independent Gaussian noise trading `u` of mean `0` and variance `σ_u²`. -/
structure KyleModel (P : Measure Ω) (v u : Ω → ℝ) (p₀ σ_v σ_u : ℝ) : Prop where
  σ_v_pos : 0 < σ_v
  σ_u_pos : 0 < σ_u
  v_meas : Measurable v
  u_meas : Measurable u
  v_gaussian : HasGaussianLaw v P
  u_gaussian : HasGaussianLaw u P
  indep : v ⟂ᵢ[P] u
  mean_v : ∫ ω, v ω ∂P = p₀
  var_v : Var[v; P] = σ_v ^ 2
  mean_u : ∫ ω, u ω ∂P = 0
  var_u : Var[u; P] = σ_u ^ 2

/-- The order flow of the linear demand `β · (v − p₀)` against the noise `u`. -/
def kyleFlow (β : ℝ) (v u : Ω → ℝ) (p₀ : ℝ) : Ω → ℝ :=
  fun ω ↦ β * (v ω - p₀) + u ω

@[simp] lemma kyleFlow_apply (β : ℝ) (v u : Ω → ℝ) (p₀ : ℝ) (ω : Ω) :
    kyleFlow β v u p₀ ω = β * (v ω - p₀) + u ω :=
  rfl

/-- A translate of a Gaussian random vector is Gaussian. -/
private lemma hasGaussianLaw_fun_add_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (P : Measure Ω) {Z : Ω → E} (c : E)
    (hZ : HasGaussianLaw Z P) :
    HasGaussianLaw (fun ω ↦ Z ω + c) P := by
  have hmap : Measure.map (fun ω ↦ Z ω + c) P = Measure.map (fun x ↦ x + c) (Measure.map Z P) := by
    rw [show (fun ω ↦ Z ω + c) = (fun x ↦ x + c) ∘ Z from rfl]
    exact (AEMeasurable.map_map_of_aemeasurable (by fun_prop) hZ.aemeasurable).symm
  have hinst : IsGaussian (Measure.map Z P) := hZ.isGaussian_map
  exact ⟨by fun_prop, by rw [hmap]; exact inferInstanceAs (IsGaussian _)⟩

/-- The linear map `(x₁, x₂) ↦ (x₁, β·x₁ + x₂)` underlying the pair of value and order flow. -/
private def kyleFlowPair (β : ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (β • ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] private lemma kyleFlowPair_apply (β : ℝ) (p : ℝ × ℝ) :
    kyleFlowPair β p = (p.1, β * p.1 + p.2) := by
  simp [kyleFlowPair]

/-- The covariance of the centered signal with the noise vanishes: the value and the noise are
independent, and the shift by `p₀` carries no covariance. -/
private lemma cov_signal_u (h : KyleModel P v u p₀ σ_v σ_u) :
    cov[fun ω ↦ v ω - p₀, u; P] = 0 := by
  have hint_v : Integrable v P := h.v_gaussian.integrable
  have heq : (fun ω ↦ v ω - p₀) = (fun ω ↦ v ω + (-p₀)) := by ext ω; ring
  rw [heq, covariance_add_const_left hint_v (-p₀)]
  have hindep : v ⟂ᵢ[P] u := h.indep
  have hfac : ∫ ω, v ω * u ω ∂P = (∫ ω, v ω ∂P) * ∫ ω, u ω ∂P :=
    IndepFun.integral_fun_mul_eq_mul_integral hindep
      h.v_meas.aestronglyMeasurable h.u_meas.aestronglyMeasurable
  rw [covariance_eq_sub h.v_gaussian.memLp_two h.u_gaussian.memLp_two]
  simp only [Pi.mul_apply]
  rw [hfac, h.mean_v, h.mean_u]
  ring

/-- The mean of the order flow is zero: no coefficient of the equilibrium depends on `p₀`
beyond the location of `v`. -/
private lemma meanFlow (h : KyleModel P v u p₀ σ_v σ_u) (β : ℝ) :
    ∫ ω, kyleFlow β v u p₀ ω ∂P = 0 := by
  have hintv0 : Integrable (fun ω ↦ v ω - p₀) P :=
    (h.v_gaussian.memLp_two.sub (memLp_const p₀)).integrable (by simp)
  have hint1 : Integrable (fun ω ↦ β * (v ω - p₀)) P := hintv0.const_mul β
  have hint2 : Integrable u P := h.u_gaussian.integrable
  have h1 : ∫ ω, β * (v ω - p₀) ∂P = 0 := by
    rw [integral_const_mul, integral_sub h.v_gaussian.integrable (integrable_const p₀),
      h.mean_v, integral_const]
    simp
  rw [show kyleFlow β v u p₀ = (fun ω ↦ β * (v ω - p₀)) + u from rfl]
  simp only [Pi.add_apply]
  rw [integral_add hint1 hint2, h1, h.mean_u]
  simp

/-- The variance of the order flow is `β²·σ_v² + σ_u²`. -/
private lemma varFlow (h : KyleModel P v u p₀ σ_v σ_u) (β : ℝ) :
    Var[kyleFlow β v u p₀; P] = β ^ 2 * σ_v ^ 2 + σ_u ^ 2 := by
  have hvo : MemLp (fun ω ↦ v ω - p₀) 2 P := h.v_gaussian.memLp_two.sub (memLp_const p₀)
  have hv' : MemLp (fun ω ↦ β * (v ω - p₀)) 2 P := hvo.const_mul β
  have hu : MemLp u 2 P := h.u_gaussian.memLp_two
  have hvo_var : Var[fun ω ↦ v ω - p₀; P] = σ_v ^ 2 := by
    rw [variance_sub_const h.v_meas.aestronglyMeasurable p₀, h.var_v]
  have hcov0 : cov[fun ω ↦ β * (v ω - p₀), u; P] = 0 := by
    rw [covariance_const_mul_left β, cov_signal_u h]
    ring
  rw [show kyleFlow β v u p₀ = (fun ω ↦ β * (v ω - p₀)) + u from rfl, variance_add hv' hu,
    variance_const_mul β _ P, hvo_var, hcov0, h.var_u]
  ring

/-- The covariance of the value with the order flow is `β·σ_v²`. -/
private lemma cov_v_flow (h : KyleModel P v u p₀ σ_v σ_u) (β : ℝ) :
    cov[v, kyleFlow β v u p₀; P] = β * σ_v ^ 2 := by
  have hvo : MemLp (fun ω ↦ v ω - p₀) 2 P := h.v_gaussian.memLp_two.sub (memLp_const p₀)
  have hv' : MemLp (fun ω ↦ β * (v ω - p₀)) 2 P := hvo.const_mul β
  have hv : MemLp v 2 P := h.v_gaussian.memLp_two
  have hu : MemLp u 2 P := h.u_gaussian.memLp_two
  have hself : cov[v, v; P] = σ_v ^ 2 := by
    rw [covariance_self (Measurable.aemeasurable h.v_meas), h.var_v]
  have hconst : cov[v, u; P] = 0 := by
    have hindep : v ⟂ᵢ[P] u := h.indep
    have hfac : ∫ ω, v ω * u ω ∂P = (∫ ω, v ω ∂P) * ∫ ω, u ω ∂P :=
      IndepFun.integral_fun_mul_eq_mul_integral hindep
        h.v_meas.aestronglyMeasurable h.u_meas.aestronglyMeasurable
    rw [covariance_eq_sub hv hu]
    simp only [Pi.mul_apply]
    rw [hfac, h.mean_v, h.mean_u]
    ring
  have hsig : cov[v, fun ω ↦ v ω - p₀; P] = σ_v ^ 2 := by
    rw [show cov[v, fun ω ↦ v ω - p₀; P] = cov[v, v - fun _ ↦ p₀; P] from rfl,
      covariance_sub_right hv hv (memLp_const p₀), hself, covariance_const_right]
    ring
  rw [show kyleFlow β v u p₀ = (fun ω ↦ β * (v ω - p₀)) + u from rfl,
    covariance_add_right hv hv' hu, covariance_const_mul_right β, hsig, hconst]
  ring

/-- **Market efficiency.** For any demand slope `β` the market maker's conditional expectation of
the value given the order flow is the linear rule with slope `λ = β·σ_v²/(β²·σ_v² + σ_u²)`:
with that pricing rule, `p = E[v | x + u]` almost surely. -/
theorem kyleMarketEfficiency (h : KyleModel P v u p₀ σ_v σ_u) (β : ℝ) :
    P[v | MeasurableSpace.comap (kyleFlow β v u p₀) inferInstance]
      =ᵐ[P] fun ω ↦ p₀ + (β * σ_v ^ 2 / (β ^ 2 * σ_v ^ 2 + σ_u ^ 2)) * kyleFlow β v u p₀ ω := by
  have hs : 0 < β ^ 2 * σ_v ^ 2 + σ_u ^ 2 := by
    have h2u : 0 < σ_u ^ 2 := pow_pos h.σ_u_pos 2
    have hsq : 0 ≤ β ^ 2 * σ_v ^ 2 := by positivity
    linarith
  have hpair : HasGaussianLaw (fun ω ↦ (v ω, u ω)) P :=
    h.indep.hasGaussianLaw h.v_gaussian h.u_gaussian
  have hlin : HasGaussianLaw (fun ω ↦ kyleFlowPair β (v ω, u ω)) P := by
    refine HasGaussianLaw.congr
      (hpair.map_of_measurable (kyleFlowPair β) (kyleFlowPair β).continuous.measurable) ?_
    rfl
  have hjoint : HasGaussianLaw (fun ω ↦ (v ω, kyleFlow β v u p₀ ω)) P := by
    refine HasGaussianLaw.congr
      (hasGaussianLaw_fun_add_const P (c := (0, -β * p₀))
        (Z := fun ω ↦ kyleFlowPair β (v ω, u ω)) hlin) ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    have h1 : (kyleFlowPair β (v ω, u ω) + (0, -β * p₀)).1 = (v ω, kyleFlow β v u p₀ ω).1 := by
      rw [Prod.fst_add, kyleFlowPair_apply]
      simp
    have h2 : (kyleFlowPair β (v ω, u ω) + (0, -β * p₀)).2 = (v ω, kyleFlow β v u p₀ ω).2 := by
      rw [Prod.snd_add, kyleFlowPair_apply, kyleFlow]
      ring
    exact Prod.ext h1 h2
  set σ_y := Real.sqrt (β ^ 2 * σ_v ^ 2 + σ_u ^ 2) with hσy_def
  have hσy_pos : 0 < σ_y := Real.sqrt_pos.mpr hs
  have hσy_sq : σ_y ^ 2 = β ^ 2 * σ_v ^ 2 + σ_u ^ 2 := by rw [hσy_def, Real.sq_sqrt hs.le]
  have hbundle : BivariateGaussianHyp P v (kyleFlow β v u p₀) p₀ 0 σ_v σ_y (β * σ_v / σ_y) := {
    σ_X_pos := h.σ_v_pos
    σ_Y_pos := hσy_pos
    X_meas := h.v_meas
    Y_meas := ((h.v_meas.sub measurable_const).const_mul β).add h.u_meas
    joint_gaussian := hjoint
    mean_X := h.mean_v
    mean_Y := meanFlow h β
    var_Y := by rw [varFlow h β, hσy_sq]
    cov_XY := by rw [cov_v_flow h β]; field_simp [hσy_pos.ne]
  }
  refine (BivariateGaussianHyp.conditional_expectation_formula hbundle).trans ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  show p₀ + (β * σ_v / σ_y * σ_v / σ_y) * (kyleFlow β v u p₀ ω - 0)
      = p₀ + (β * σ_v ^ 2 / (β ^ 2 * σ_v ^ 2 + σ_u ^ 2)) * kyleFlow β v u p₀ ω
  rw [sub_zero]
  have hcoef : β * σ_v / σ_y * σ_v / σ_y = β * σ_v ^ 2 / σ_y ^ 2 := by
    field_simp [hσy_pos.ne]
  rw [hcoef, hσy_sq]

section BestResponse

/-- The completed-square bound on the trader's expected profit: the quadratic
`c·t − λ·t²` never exceeds `c²/(4λ)` for `lam > 0`. -/
private lemma kyleProfit_le_max {lam : ℝ} (hlam : 0 < lam) (c t : ℝ) :
    c * t - lam * t ^ 2 ≤ c ^ 2 / (4 * lam) := by
  have h1 : 4 * lam * (c * t - lam * t ^ 2) ≤ c ^ 2 := by
    have h2 : (c - 2 * lam * t) ^ 2 ≥ 0 := sq_nonneg _
    nlinarith
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- The best-response condition pins the coefficients: a demand slope whose linear demand is an
unrestricted maximizer of the expected profit at every signal has positive price impact and
satisfies `β = 1/(2λ)`. -/
private lemma kyleMaxCoefficients {β lam : ℝ}
    (h : ∀ c t : ℝ, c * (β * c) - lam * (β * c) ^ 2 ≥ c * t - lam * t ^ 2) :
    0 < lam ∧ β = 1 / (2 * lam) := by
  have h1 : ∀ t : ℝ, β - lam * β ^ 2 ≥ t - lam * t ^ 2 := by
    intro t
    have := h 1 t
    simpa using this
  have hlam0 : lam ≠ 0 := by
    intro h0
    subst h0
    have := h1 (β + 1)
    simp at this
    linarith
  by_cases hlampos : 0 < lam
  · refine ⟨hlampos, ?_⟩
    have hkey := h1 (1 / (2 * lam))
    have hsq : (2 * lam * β - 1) ^ 2 ≤ 0 := by
      have h4 : 0 < 4 * lam := by linarith
      field_simp at hkey ⊢
      nlinarith
    have heq : 2 * lam * β - 1 = 0 := sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))
    field_simp
    linarith
  · have hlamle : lam ≤ 0 := not_lt.mp hlampos
    have hlamneg : lam < 0 := lt_of_le_of_ne hlamle hlam0
    have hpair : ∀ t : ℝ, β - lam * β ^ 2 ≥ -lam * t ^ 2 := by
      intro t
      have h2 := h1 t
      have h3 := h1 (-t)
      linarith
    set k := -lam with hk_def
    have hkpos : 0 < k := by linarith
    set s := (β - lam * β ^ 2) / k with hs_def
    have hcontr := hpair (s + 1)
    have hks : k * s = β - lam * β ^ 2 := by rw [hs_def]; field_simp [hk_def]
    rw [← hks] at hcontr
    have hstep : (s + 1) ^ 2 ≤ s := le_of_mul_le_mul_left hcontr hkpos
    nlinarith [sq_nonneg (s + 1 / 2)]

end BestResponse

/-- The informed trader's expected profit given the signal: for a demand measurable with
respect to the signal, the noise term vanishes under independence and the conditional
expectation is the quadratic `(v − p₀)·x − lam·x²`, almost surely. -/
theorem kyleConditionalProfit (h : KyleModel P v u p₀ σ_v σ_u) (lam : ℝ) {x : Ω → ℝ}
    (hxs : StronglyMeasurable[MeasurableSpace.comap v inferInstance] x)
    (hint1 : Integrable (fun ω ↦ (v ω - p₀) * x ω) P)
    (hint2 : Integrable (fun ω ↦ x ω ^ 2) P)
    (hint3 : Integrable (fun ω ↦ x ω * u ω) P) :
    P[(fun ω ↦ (v ω - p₀) * x ω - lam * x ω ^ 2 - lam * x ω * u ω)
        | MeasurableSpace.comap v inferInstance]
      =ᵐ[P] fun ω ↦ (v ω - p₀) * x ω - lam * x ω ^ 2 := by
  have hvle : MeasurableSpace.comap v inferInstance ≤ mΩ := h.v_meas.comap_le
  have hvs : StronglyMeasurable[MeasurableSpace.comap v inferInstance] v :=
    (Measurable.of_comap_le le_rfl).stronglyMeasurable
  have hus : StronglyMeasurable[MeasurableSpace.comap u inferInstance] u :=
    (Measurable.of_comap_le le_rfl).stronglyMeasurable
  have hvm : StronglyMeasurable[MeasurableSpace.comap v inferInstance]
      (fun ω ↦ v ω - p₀) := hvs.sub stronglyMeasurable_const
  have hxs' : Measurable[MeasurableSpace.comap v inferInstance] x := hxs.measurable
  have hterm1 : StronglyMeasurable[MeasurableSpace.comap v inferInstance]
      (fun ω ↦ (v ω - p₀) * x ω) := hvm.mul hxs
  have hterm2 : StronglyMeasurable[MeasurableSpace.comap v inferInstance]
      (fun ω ↦ lam * x ω ^ 2) := (hxs.pow 2).const_mul lam
  have hintc1 : Integrable (fun ω ↦ lam * x ω ^ 2) P := hint2.const_mul lam
  have hintc3 : Integrable (fun ω ↦ lam * x ω * u ω) P := by
    simpa [mul_assoc] using hint3.const_mul lam
  have hind : Indep (MeasurableSpace.comap u inferInstance)
      (MeasurableSpace.comap v inferInstance) P :=
    ((IndepFun_iff_Indep v u P).mp h.indep).symm
  have hucond : P[u | MeasurableSpace.comap v inferInstance]
      =ᵐ[P] fun _ ↦ (∫ ω, u ω ∂P) :=
    condExp_indep_eq h.u_meas.comap_le hvle hus hind
  have hu_pull : P[(fun ω ↦ lam * x ω * u ω) | MeasurableSpace.comap v inferInstance]
      =ᵐ[P] fun _ ↦ (0 : ℝ) := by
    refine (condExp_mul_of_aestronglyMeasurable_left
      (f := fun ω ↦ lam * x ω) (g := u)
      (stronglyMeasurable_const.mul hxs).aestronglyMeasurable
      hintc3 h.u_gaussian.integrable).trans ?_
    filter_upwards [hucond] with ω hw
    simp only [Pi.mul_apply]
    rw [hw]
    simp [h.mean_u]
  show P[(((fun ω ↦ (v ω - p₀) * x ω) - (fun ω ↦ lam * x ω ^ 2))
      - (fun ω ↦ lam * x ω * u ω)) | MeasurableSpace.comap v inferInstance]
    =ᵐ[P] ((fun ω ↦ (v ω - p₀) * x ω) - (fun ω ↦ lam * x ω ^ 2))
  have hp12 : P[((fun ω ↦ (v ω - p₀) * x ω) - (fun ω ↦ lam * x ω ^ 2))
      | MeasurableSpace.comap v inferInstance]
      = ((fun ω ↦ (v ω - p₀) * x ω) - (fun ω ↦ lam * x ω ^ 2)) :=
    condExp_of_stronglyMeasurable hvle (hterm1.sub hterm2) (hint1.sub hintc1)
  have step1 := condExp_sub (f := ((fun ω ↦ (v ω - p₀) * x ω) - (fun ω ↦ lam * x ω ^ 2)))
    (g := fun ω ↦ lam * x ω * u ω) (hint1.sub hintc1) hintc3
    (MeasurableSpace.comap v inferInstance)
  refine step1.trans ?_
  have step2 : P[((fun ω ↦ (v ω - p₀) * x ω) - (fun ω ↦ lam * x ω ^ 2))
      | MeasurableSpace.comap v inferInstance] - P[(fun ω ↦ lam * x ω * u ω)
      | MeasurableSpace.comap v inferInstance]
      =ᵐ[P] ((fun ω ↦ (v ω - p₀) * x ω) - (fun ω ↦ lam * x ω ^ 2))
        - P[(fun ω ↦ lam * x ω * u ω) | MeasurableSpace.comap v inferInstance] := by
    filter_upwards [] with ω
    simp only [Pi.sub_apply, hp12]
  refine step2.trans ?_
  filter_upwards [hu_pull] with ω hw
  simp only [Pi.sub_apply, hw, sub_zero]

/-- **The Kyle equilibrium coefficients.** A pair `(β, lam)` whose linear demand is an
unrestricted best response at every signal and whose pricing rule is efficient satisfies
`lam = σ_v/(2σ_u)` and `β = σ_u/σ_v`. -/
theorem kyleEquilibriumCoefficients (h : KyleModel P v u p₀ σ_v σ_u) {β lam : ℝ}
    (hb : ∀ c t : ℝ, c * (β * c) - lam * (β * c) ^ 2 ≥ c * t - lam * t ^ 2)
    (he : P[v | MeasurableSpace.comap (kyleFlow β v u p₀) inferInstance]
          =ᵐ[P] fun ω ↦ p₀ + lam * kyleFlow β v u p₀ ω) :
    lam = σ_v / (2 * σ_u) ∧ β = σ_u / σ_v := by
  obtain ⟨hlampos, hbeta⟩ := kyleMaxCoefficients hb
  have heff := kyleMarketEfficiency h β
  have hay : ∀ᵐ (ω : Ω) ∂P,
      β * σ_v ^ 2 / (β ^ 2 * σ_v ^ 2 + σ_u ^ 2) * kyleFlow β v u p₀ ω
        = lam * kyleFlow β v u p₀ ω := by
    filter_upwards [heff, he] with ω h1 h2
    linarith
  have hcoef : β * σ_v ^ 2 / (β ^ 2 * σ_v ^ 2 + σ_u ^ 2) = lam := by
    by_contra hne
    exfalso
    have hy0 : ∀ᵐ (ω : Ω) ∂P, kyleFlow β v u p₀ ω = 0 := by
      filter_upwards [hay] with ω hw
      have hz : (β * σ_v ^ 2 / (β ^ 2 * σ_v ^ 2 + σ_u ^ 2) - lam) * kyleFlow β v u p₀ ω = 0 :=
        by linear_combination hw
      rcases mul_eq_zero.mp hz with h0 | h1
      · exact absurd (by linarith) hne
      · exact h1
    have hy0eq : (kyleFlow β v u p₀) =ᵐ[P] fun _ ↦ (0 : ℝ) := hy0
    have hvar0 : Var[kyleFlow β v u p₀; P] = 0 := by
      rw [variance_congr hy0eq]
      exact variance_zero P
    rw [varFlow h β] at hvar0
    have h2u : 0 < σ_u ^ 2 := pow_pos h.σ_u_pos 2
    have hsqp : 0 ≤ β ^ 2 * σ_v ^ 2 := by nlinarith [sq_nonneg β, sq_nonneg σ_v]
    linarith
  have hfix : lam * (β ^ 2 * σ_v ^ 2 + σ_u ^ 2) = β * σ_v ^ 2 :=
    (eq_div_iff (by
      have h2u : 0 < σ_u ^ 2 := pow_pos h.σ_u_pos 2
      have hsq : 0 ≤ β ^ 2 * σ_v ^ 2 := by nlinarith [sq_nonneg β, sq_nonneg σ_v]
      linarith)).mp hcoef.symm
  have e1 : 2 * lam * β = 1 := by rw [hbeta]; field_simp
  have e2 : 2 * lam * β * σ_v ^ 2 = σ_v ^ 2 := by rw [e1]; ring_nf
  have e3 : 2 * lam * (lam * (β ^ 2 * σ_v ^ 2 + σ_u ^ 2)) = 2 * lam * (β * σ_v ^ 2) := by rw [hfix]
  have e4 : 2 * lam ^ 2 * β ^ 2 * σ_v ^ 2 + 2 * lam ^ 2 * σ_u ^ 2 = σ_v ^ 2 := by
    linear_combination e3 + e2
  rw [hbeta] at e4
  field_simp at e4
  rw [show (2:ℝ) ^ 2 = 4 from by norm_num] at e4
  have h4 : 4 * lam ^ 2 * σ_u ^ 2 = σ_v ^ 2 := by linarith
  have hsq0 : (2 * lam * σ_u) ^ 2 = σ_v ^ 2 := by
    rw [pow_two]
    calc (2 * lam * σ_u) * (2 * lam * σ_u) = 4 * lam ^ 2 * σ_u ^ 2 := by ring
      _ = σ_v ^ 2 := h4
  rw [pow_two, pow_two] at hsq0
  have hpos : 2 * lam * σ_u = σ_v := by
    rcases mul_self_eq_mul_self_iff.mp hsq0 with hp | hn
    · exact hp
    · exact absurd hn (by
        have h1 := h.σ_v_pos
        have h2 := h.σ_u_pos
        have h3 := hlampos
        nlinarith)
  refine ⟨by rw [← hpos]; field_simp [h.σ_u_pos.ne'],
    by rw [hbeta, ← hpos]; field_simp [h.σ_v_pos.ne', h.σ_u_pos.ne']⟩

end MathFin

