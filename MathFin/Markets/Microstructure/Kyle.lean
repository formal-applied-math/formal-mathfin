/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Init
public import MathFin.Probability.Gaussian.BivariateGaussian
public import Mathlib.Probability.ConditionalExpectation
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

end MathFin
