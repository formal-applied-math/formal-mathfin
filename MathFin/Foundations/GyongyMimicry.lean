/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Foundations.ItoIntegralProcessGeneral
public import MathFin.Foundations.ItoIntegralProcess
public import MathFin.Foundations.AdaptedProcessToLp
public import MathFin.Foundations.ItoIntegralL2
public import MathFin.Foundations.ItoIntegralCLM
public import MathFin.Foundations.AdaptedDrift
public import MathFin.Foundations.ItoIntegralCrossHorizon
public import MathFin.Foundations.ItoFormulaAdaptedDrift

/-! # Gyöngy mimicry — the generator-matching core and the weak forward equation

Bagaria ch. 9 / Thm 9.6 (Gyöngy 1986): for an Itô process `dX_t = β_t dt + δ_t dW_t` with
bounded adapted `β, δ` and uniformly nondegenerate diffusion (`δ_t² ≥ λ > 0`), the Markov
diffusion with coefficients
`a(t, x) = 𝔼[β_t | X_t = x]`, `b²(t, x) = 𝔼[δ_t² | X_t = x]` has the same one-time
marginals as `X`. The existence and uniqueness of the mimicking diffusion `Y` (an SDE with
merely-measurable coefficients, outside MathFin's Lipschitz/Picard `SDEExistence.lean`) are
not proved; this module proves the generator-matching part of the argument and states the
mimicry under a flow-uniqueness hypothesis:

* the **generator-matching identities** `𝔼[f'(X_t) β_t] = 𝔼[f'(X_t) a_t]` and
  `𝔼[f''(X_t) δ_t²] = 𝔼[f''(X_t) b²_t]` (tower step + Doob–Dynkin measurability);
* the **weak forward equation** for the marginal flow of the *constructed* adapted
  process — the dynamics carried as explicit data (`X t = c + driftPath β t + M t`, `M`
  pinned to the CLM Itô integral by `hMeq`, in place of a general Itô-decomposition
  predicate):
  * `marginal_flow_weak_equation_constructed` — the `HasDerivAt` form at `t` with
    `Real.toNNReal t < T`;
  * `marginal_flow_weak_equation_fn_constructed` — the same with the
    conditional-expectation coefficients replaced by Borel coefficient functions
    `â, b̂² : ℝ → ℝ → ℝ` (the Doob–Dynkin upgrade);
* the **Doob–Dynkin coefficient-function layer** (`exists_driftCoeff_fn`,
  `exists_diffCoeffSq_fn`) and `gyongy_mimicry_gated` — one-time-marginal mimicry of `X`
  by a given `Y`, under a flow-uniqueness hypothesis.

This module consumes the adapted integrated Itô–drift identity
(`ItoDriftConditional.itoDrift_expectation_identity_adapted`), the cross-horizon
consistency of the CLM integral (`ae_eq_itoProcessCLM_min`,
`itoProcessCLM_consist`), and the drift-path layer
(`AdaptedDrift.driftPath` and its measurability/continuity lemmas).

## Result

Public API (all in namespace `MathFin.GyongyMimicry`):

* `BoundedCoeffData` — bounded, path-continuous `X, β, δ` (the Itô relation is not a field);
* `sigmaGen`, `driftCoeff`, `diffCoeffSq` — the conditioning σ-algebra and the Gyöngy
  coefficients as conditional expectations;
* `tower_identity`, `expectation_beta_eq_a`, `expectation_deltaSq_eq_b2` — the
  generator-matching identities;
* `continuous_marginal_integrand` — the derivative/expectation interchange (proved);
* `continuous_f2_of_contDiff2`, `sigmaGen_le`, `measurable_comp_comap`,
  `stronglyMeasurable_test`, `measurable_f2_comp`, `integrable_of_bounded`,
  `generatorIntegrand` — the measure-theory and integrability utilities of the core
  (`sigmaGen_le` and `stronglyMeasurable_test` are consumed by `MathFin.Dupire`);
* `reindexed`, `stronglyMeasurable_X_hXrel` — the real-time reindexing `t ↦ X_{t⁺}` and
  the adaptedness lemma behind the constructed instance's measurability field
  (`reindexed` is consumed by `MathFin.Dupire`);
* `timeMeasure_Ioc_eq_interval` — the `timeMeasure` → `intervalIntegral` bridge;
* `constructedCoeffData`, `constructedGenIntegrandExp` (+ `_coe`), the integrated drift
  identities `hitoid_constructed_terminal` / `hitoid_constructed_band`, and the weak
  forward equation in both forms;
* `exists_driftCoeff_fn`, `exists_diffCoeffSq_fn`, `marginal_flow_weak_equation_fn_constructed`,
  `gyongy_mimicry_gated` — the coefficient functions and the mimicry statement.

Supporting lemmas (`integrable_testβ`, `integrable_testδsq`, `hasDerivAt_marginal_flow_core`,
`constructedGenIntegrandExp_eq`, `exists_coeffFn_comp`,
`hitoid_constructed_fn_Ioc`) are `private`.
-/

@[expose] public section

namespace MathFin.GyongyMimicry

open MeasureTheory Filter Topology
open scoped Interval


section Process

/-- Bounded, path-continuous coefficient data; the Itô relation is not a field. A triple of
processes `X, β, δ` with `|β| ≤ B`, `|δ| ≤ D`, each measurable at every time and continuous in
time along every path. The dynamics `dX = β dt + δ dW` enter only through the integrated
Itô-drift hypothesis `hitoid` of `GyongyMimicry.hasDerivAt_marginal_flow_core`, which
`constructedCoeffData` supplies for the constructed process.

Path continuity is the pointwise input of `GyongyMimicry.continuous_marginal_integrand`,
which proves the derivative/expectation interchange; it is what makes the weak equation hold
at every time `t` rather than for almost every `t`. -/
structure BoundedCoeffData (Ω : Type*) [mΩ : MeasurableSpace Ω] where
  /-- the state process -/
  X : ℝ → Ω → ℝ
  /-- the drift rate process, `|β_t| ≤ B` -/
  β : ℝ → Ω → ℝ
  /-- the diffusion coefficient process, `|δ_t| ≤ D` -/
  δ : ℝ → Ω → ℝ
  /-- the (constant) bound on the drift rate -/
  B : ℝ
  /-- the (constant) bound on the diffusion coefficient -/
  D : ℝ
  Bpos : 0 ≤ B
  Dpos : 0 ≤ D
  hXmeas : ∀ t, Measurable (X t)
  hβmeas : ∀ t, Measurable (β t)
  hδmeas : ∀ t, Measurable (δ t)
  hβbdd : ∀ t ω, |β t ω| ≤ B
  hδbdd : ∀ t ω, |δ t ω| ≤ D
  /- path continuity -/
  hXcont : ∀ ω, Continuous fun t => X t ω
  hβcont : ∀ ω, Continuous fun t => β t ω
  hδcont : ∀ ω, Continuous fun t => δ t ω

end Process

section Smoothness

/-- From `ContDiff ℝ 2 f` plus the two `HasDerivAt` links pinning `f'` and `f''` as the
first and second derivatives of `f`, the second derivative `f''` is continuous — the `C²`
half (continuous second derivative) of the test-function class of Bagaria ch. 9 / Thm 9.6's
proof. No `Measurable f''` hypothesis is needed: measurability of `f''`
(and of `f'' ∘ X_t`, see `GyongyMimicry.measurable_f2_comp`) is *derived* from the smoothness
package.

Route: `contDiff_succ_iff_deriv` turns `ContDiff ℝ 2 f` into `ContDiff ℝ 1 (deriv f)`;
`ContDiff.continuous_deriv` then makes `deriv (deriv f)` continuous; the two `HasDerivAt`
chains identify `deriv f = f'` and `deriv f' = f''` by `funext`. -/
theorem continuous_f2_of_contDiff2 {f f' f'' : ℝ → ℝ} (h2 : ContDiff ℝ 2 f)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x) :
    Continuous f'' := by
  have h1 : ContDiff ℝ 1 (deriv f) := (contDiff_succ_iff_deriv.mp h2).2.2
  have hderivf : deriv f = f' := funext fun x => (hf x).deriv
  have hderivf' : deriv f' = f'' := funext fun x => (hf' x).deriv
  rw [← hderivf', ← hderivf]
  exact h1.continuous_deriv le_rfl

end Smoothness

section Setup

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `σ(X_t)`: the pullback of Borel measurability along `X t` — the σ-algebra generated by
the time-`t` marginal variable (the "condition on `X_t`" of Thm 9.6). -/
abbrev sigmaGen (X : ℝ → Ω → ℝ) (t : ℝ) : MeasurableSpace Ω :=
  Real.measurableSpace.comap (X t)

/-- `σ(X_t)` is a sub-σ-algebra of the ambient one as soon as `X t` is measurable. -/
theorem sigmaGen_le (X : ℝ → Ω → ℝ) (t : ℝ) (hX : Measurable (X t)) :
    sigmaGen X t ≤ mΩ :=
  hX.comap_le

/-- Gyöngy's drift coefficient at time `t`, as a random variable:
`a_t = 𝔼[β_t | σ(X_t)]`. (A conditional expectation is defined only up to μ-a.e.
equality; all statements below integrate, so the representative is irrelevant.) -/
noncomputable def driftCoeff (μ : Measure Ω) (X β : ℝ → Ω → ℝ) (t : ℝ) : Ω → ℝ :=
  μ[β t | sigmaGen X t]

/-- Gyöngy's squared-diffusion coefficient: `b²_t = 𝔼[δ_t² | σ(X_t)]`. -/
noncomputable def diffCoeffSq (μ : Measure Ω) (X δ : ℝ → Ω → ℝ) (t : ℝ) : Ω → ℝ :=
  μ[(fun ω => δ t ω * δ t ω) | sigmaGen X t]

omit mΩ in
/-- Elementary Doob–Dynkin half: `f ∘ X` is `σ(X)`-measurable for Borel-measurable `f`.
One line from the definition of `MeasurableSpace.comap`. (The full factorization form of
Doob–Dynkin in this Mathlib rev is `MeasureTheory.StronglyMeasurable.exists_eq_measurable_comp`.) -/
theorem measurable_comp_comap {X : Ω → ℝ} {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable[Real.measurableSpace.comap X] (fun ω => f (X ω)) := by
  intro s hs
  exact ⟨f ⁻¹' s, MeasurableSet.preimage hs hf, rfl⟩

omit mΩ in
/-- `f ∘ X t` is `σ(X_t)`-strongly-measurable for Borel `f` — the fact that licenses
`f'(X_t)` "passing through" the conditional expectation in Thm 9.6's proof. -/
theorem stronglyMeasurable_test (X : ℝ → Ω → ℝ) (t : ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) : StronglyMeasurable[sigmaGen X t] (fun ω => f (X t ω)) :=
  (measurable_comp_comap hf).stronglyMeasurable

/-- **Measurability of `f'' ∘ X`** (derived, not hypothesized):
continuity of `f''` (obtained from `ContDiff ℝ 2 f` via
`GyongyMimicry.continuous_f2_of_contDiff2`) composed with the measurability of `X` gives Borel
measurability of `f'' ∘ X`. -/
theorem measurable_f2_comp {X : Ω → ℝ} (hX : Measurable X) {f'' : ℝ → ℝ}
    (hf''cont : Continuous f'') : Measurable (fun ω => f'' (X ω)) :=
  hf''cont.measurable.comp hX

/-- Bounded measurable functions are integrable under a probability measure (the standing
hypothesis on `μ` in this section). -/
theorem integrable_of_bounded {g : Ω → ℝ} (hg : Measurable g) (C : ℝ) (hC : ∀ ω, |g ω| ≤ C) :
    Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable C
    (Eventually.of_forall fun ω => by simpa using hC ω)

/-- **The tower identity** — the engine of Gyöngy's proof (Bagaria ch. 9 / Thm 9.6, the
"condition on `X_t`" step): an `m`-measurable factor `h` crosses the conditional
expectation, `𝔼[h · g] = 𝔼[h · 𝔼[g | m]]`. -/
theorem tower_identity {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {h g : Ω → ℝ}
    (hh : StronglyMeasurable[m] h) (hgh : Integrable (h * g) μ) (hg : Integrable g μ) :
    ∫ ω, h ω * g ω ∂μ = ∫ ω, h ω * μ[g | m] ω ∂μ := by
  calc ∫ ω, h ω * g ω ∂μ
      = ∫ ω, μ[h * g | m] ω ∂μ := (integral_condExp hm).symm
    _ = ∫ ω, h ω * μ[g | m] ω ∂μ :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hh hgh hg)

end Setup

section Matching

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Integrability of the drift test-product `f'(X_t) · β_t`, from the two bounds. -/
private theorem integrable_testβ (P : BoundedCoeffData Ω) (t : ℝ) {f' : ℝ → ℝ}
    (hf'meas : Measurable f') {C : ℝ} (hfbdd : ∀ x, |f' x| ≤ C) :
    Integrable (fun ω => f' (P.X t ω) * P.β t ω) μ := by
  refine integrable_of_bounded ((hf'meas.comp (P.hXmeas t)).mul (P.hβmeas t)) (C * P.B)
    (fun ω => ?_)
  rw [abs_mul]
  calc |f' (P.X t ω)| * |P.β t ω|
      ≤ C * |P.β t ω| := mul_le_mul_of_nonneg_right (hfbdd _) (abs_nonneg _)
    _ ≤ C * P.B := mul_le_mul_of_nonneg_left (P.hβbdd t ω)
        (le_trans (abs_nonneg _) (hfbdd 0))

/-- Integrability of the diffusion test-product `f''(X_t) · δ_t²`, from the two bounds. -/
private theorem integrable_testδsq (P : BoundedCoeffData Ω) (t : ℝ) {f'' : ℝ → ℝ}
    (hf''meas : Measurable f'') {C : ℝ} (hfbdd : ∀ x, |f'' x| ≤ C) :
    Integrable (fun ω => f'' (P.X t ω) * (P.δ t ω * P.δ t ω)) μ := by
  refine integrable_of_bounded
    ((hf''meas.comp (P.hXmeas t)).mul ((P.hδmeas t).mul (P.hδmeas t))) (C * (P.D * P.D))
    (fun ω => ?_)
  rw [abs_mul, abs_mul]
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hfbdd 0)
  calc |f'' (P.X t ω)| * (|P.δ t ω| * |P.δ t ω|)
      ≤ C * (|P.δ t ω| * |P.δ t ω|) :=
        mul_le_mul_of_nonneg_right (hfbdd (P.X t ω))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ ≤ C * (P.D * P.D) :=
        mul_le_mul_of_nonneg_left
          (calc |P.δ t ω| * |P.δ t ω| ≤ P.D * |P.δ t ω| :=
              mul_le_mul_of_nonneg_right (P.hδbdd t ω) (abs_nonneg _)
            _ ≤ P.D * P.D := mul_le_mul_of_nonneg_left (P.hδbdd t ω) P.Dpos) hC0

/-- **Generator matching, drift** (Bagaria ch. 9 / Thm 9.6, first tower step):
`𝔼[f'(X_t) · β_t] = 𝔼[f'(X_t) · a_t]` — `f'(X_t)` is a function of `X_t` alone, so it
passes through the conditional expectation as a constant. -/
theorem expectation_beta_eq_a (P : BoundedCoeffData Ω) (t : ℝ) {f' : ℝ → ℝ}
    (hf'meas : Measurable f') {C : ℝ} (hfbdd : ∀ x, |f' x| ≤ C) :
    ∫ ω, f' (P.X t ω) * P.β t ω ∂μ = ∫ ω, f' (P.X t ω) * driftCoeff μ P.X P.β t ω ∂μ :=
  tower_identity (sigmaGen_le P.X t (P.hXmeas t))
    (stronglyMeasurable_test P.X t hf'meas)
    (integrable_testβ P t hf'meas hfbdd)
    (integrable_of_bounded (P.hβmeas t) P.B (P.hβbdd t))

/-- **Generator matching, diffusion** (Bagaria ch. 9 / Thm 9.6, second tower step):
`𝔼[f''(X_t) · δ_t²] = 𝔼[f''(X_t) · b²_t]`. -/
theorem expectation_deltaSq_eq_b2 (P : BoundedCoeffData Ω) (t : ℝ) {f'' : ℝ → ℝ}
    (hf''meas : Measurable f'') {C : ℝ} (hfbdd : ∀ x, |f'' x| ≤ C) :
    ∫ ω, f'' (P.X t ω) * (P.δ t ω * P.δ t ω) ∂μ
      = ∫ ω, f'' (P.X t ω) * diffCoeffSq μ P.X P.δ t ω ∂μ :=
  tower_identity (sigmaGen_le P.X t (P.hXmeas t))
    (stronglyMeasurable_test P.X t hf''meas)
    (integrable_testδsq P t hf''meas hfbdd)
    (integrable_of_bounded ((P.hδmeas t).mul (P.hδmeas t)) (P.D * P.D) (fun ω => by
      rw [abs_mul]
      calc |P.δ t ω| * |P.δ t ω| ≤ P.D * |P.δ t ω| :=
          mul_le_mul_of_nonneg_right (P.hδbdd t ω) (abs_nonneg _)
        _ ≤ P.D * P.D := mul_le_mul_of_nonneg_left (P.hδbdd t ω) P.Dpos))

end Matching

section Flow

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The generator integrand along `X` for the test function `f`: at time `s` this is
`f'(X_s) β_s + ½ f''(X_s) δ_s²` — the drift term of Itô's formula for `f(X_s)`. -/
noncomputable def generatorIntegrand (X β δ : ℝ → Ω → ℝ) (f' f'' : ℝ → ℝ) (s : ℝ) : Ω → ℝ :=
  fun ω => f' (X s ω) * β s ω + 1 / 2 * (f'' (X s ω) * (δ s ω * δ s ω))

/-- **Continuity of the expectation of the generator integrand** (the DCT interchange,
*proved* from the structure's own data rather than hypothesized): the map
`s ↦ ∫ ω, generatorIntegrand X β δ f' f'' s ω ∂μ` is continuous on `ℝ`.

Proof: pointwise in `ω`, `s ↦ generatorIntegrand … s ω` is continuous (path continuity of
`X, β, δ` — structure fields — composed with the continuous `f', f''`); it is dominated by
the constant `C₁·B + ½·C₂·D²` (integrable under the probability `μ`); every slice is
measurable. The filter-form dominated convergence theorem for integrals
(`MeasureTheory.tendsto_integral_filter_of_dominated_convergence`, index filter `𝓝 t`,
countably generated because `ℝ` is first-countable) then gives continuity at every `t` —
no sequential bridging needed. -/
theorem continuous_marginal_integrand (P : BoundedCoeffData Ω) {f' f'' : ℝ → ℝ}
    (hf'cont : Continuous f') (hf''cont : Continuous f'')
    {C1 C2 : ℝ} (hf'bd : ∀ x, |f' x| ≤ C1) (hf''bd : ∀ x, |f'' x| ≤ C2) :
    Continuous (fun s => ∫ ω, generatorIntegrand P.X P.β P.δ f' f'' s ω ∂μ) := by
  have hf'meas : Measurable f' := hf'cont.measurable
  have hf''meas : Measurable f'' := hf''cont.measurable
  -- (a) pointwise continuity of the integrand in `s`
  have hpoint : ∀ ω : Ω, Continuous (fun s => generatorIntegrand P.X P.β P.δ f' f'' s ω) := by
    intro ω
    have hXc : Continuous (fun s => P.X s ω) := P.hXcont ω
    have hβc : Continuous (fun s => P.β s ω) := P.hβcont ω
    have hδc : Continuous (fun s => P.δ s ω) := P.hδcont ω
    have hterm1 : Continuous (fun s => f' (P.X s ω) * P.β s ω) :=
      (hf'cont.comp' hXc).mul hβc
    have hterm2 : Continuous (fun s => f'' (P.X s ω) * (P.δ s ω * P.δ s ω)) :=
      (hf''cont.comp' hXc).mul (hδc.mul hδc)
    exact hterm1.add (hterm2.const_mul (1 / 2))
  -- (b) the dominating bound `C₁·B + ½·C₂·D²`
  have hbdd : ∀ (s : ℝ) (ω : Ω),
      |generatorIntegrand P.X P.β P.δ f' f'' s ω| ≤ C1 * P.B + 1 / 2 * (C2 * (P.D * P.D)) := by
    intro s ω
    simp only [generatorIntegrand]
    have hC1 : 0 ≤ C1 := le_trans (abs_nonneg _) (hf'bd 0)
    have hC2 : 0 ≤ C2 := le_trans (abs_nonneg _) (hf''bd 0)
    have hβ : |f' (P.X s ω)| * |P.β s ω| ≤ C1 * P.B := by
      calc |f' (P.X s ω)| * |P.β s ω| ≤ C1 * |P.β s ω| :=
            mul_le_mul_of_nonneg_right (hf'bd _) (abs_nonneg _)
        _ ≤ C1 * P.B := mul_le_mul_of_nonneg_left (P.hβbdd s ω) hC1
    have hδ : |f'' (P.X s ω)| * (|P.δ s ω| * |P.δ s ω|) ≤ C2 * (P.D * P.D) := by
      calc |f'' (P.X s ω)| * (|P.δ s ω| * |P.δ s ω|)
          ≤ C2 * (|P.δ s ω| * |P.δ s ω|) :=
            mul_le_mul_of_nonneg_right (hf''bd _)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ ≤ C2 * (P.D * P.D) :=
            mul_le_mul_of_nonneg_left
              (calc |P.δ s ω| * |P.δ s ω| ≤ P.D * |P.δ s ω| :=
                    mul_le_mul_of_nonneg_right (P.hδbdd s ω) (abs_nonneg _)
                _ ≤ P.D * P.D := mul_le_mul_of_nonneg_left (P.hδbdd s ω) P.Dpos) hC2
    have hterm1 : |f' (P.X s ω) * P.β s ω| ≤ C1 * P.B := by
      rw [abs_mul]; exact hβ
    have hterm2 : |1 / 2 * (f'' (P.X s ω) * (P.δ s ω * P.δ s ω))|
        ≤ 1 / 2 * (C2 * (P.D * P.D)) := by
      have habseq : |1 / 2 * (f'' (P.X s ω) * (P.δ s ω * P.δ s ω))|
          = (1 : ℝ) / 2 * (|f'' (P.X s ω)| * (|P.δ s ω| * |P.δ s ω|)) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
      rw [habseq]
      exact mul_le_mul_of_nonneg_left hδ (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    calc |f' (P.X s ω) * P.β s ω + 1 / 2 * (f'' (P.X s ω) * (P.δ s ω * P.δ s ω))|
        ≤ |f' (P.X s ω) * P.β s ω| + |1 / 2 * (f'' (P.X s ω) * (P.δ s ω * P.δ s ω))| := by
          simpa only [Real.norm_eq_abs] using
            norm_add_le (f' (P.X s ω) * P.β s ω)
              (1 / 2 * (f'' (P.X s ω) * (P.δ s ω * P.δ s ω)))
      _ ≤ C1 * P.B + 1 / 2 * (C2 * (P.D * P.D)) := add_le_add hterm1 hterm2
  -- measurability of every slice
  have hmeas : ∀ s : ℝ, Measurable (generatorIntegrand P.X P.β P.δ f' f'' s) := by
    intro s
    have hEq : generatorIntegrand P.X P.β P.δ f' f'' s
        = fun ω => f' (P.X s ω) * P.β s ω + 1 / 2 * (f'' (P.X s ω) * (P.δ s ω * P.δ s ω)) :=
      rfl
    rw [hEq]
    exact ((hf'meas.comp (P.hXmeas s)).mul (P.hβmeas s)).add
      (((hf''meas.comp (P.hXmeas s)).mul ((P.hδmeas s).mul (P.hδmeas s))).const_mul (1 / 2))
  -- (c) dominated convergence at the filter `𝓝 t`, for each `t`
  refine continuous_iff_continuousAt.2 fun t => ?_
  exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (l := (𝓝 t : Filter ℝ))
    (F := fun (s : ℝ) (ω : Ω) => generatorIntegrand P.X P.β P.δ f' f'' s ω)
    (f := fun (ω : Ω) => generatorIntegrand P.X P.β P.δ f' f'' t ω)
    (bound := fun (_ : Ω) => C1 * P.B + 1 / 2 * (C2 * (P.D * P.D)))
    (hF_meas := Eventually.of_forall fun s => (hmeas s).aestronglyMeasurable)
    (h_bound := Eventually.of_forall fun s =>
      Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hbdd s ω)
    (bound_integrable := integrable_const _)
    (h_lim := Eventually.of_forall fun ω => (hpoint ω).continuousAt)

/-- The engine behind the constructed marginal-flow weak equations
(`GyongyMimicry.marginal_flow_weak_equation_constructed` and
`GyongyMimicry.marginal_flow_weak_equation_fn_constructed`), in the *band* form:
the integrated Itô-drift identity is consumed only through the filter equality `=ᶠ[𝓝 t]`,
so it suffices that it hold on an open band `Ioo 0 T` around `t` — exactly the shape in
which the constructed instance supplies it (see the `Constructed` section).

The two facts that could have been carried as hypotheses — measurability of `f''` and
continuity of `u` — appear here only as derived `have`s:
* `hf''meas` — from `h2 : ContDiff ℝ 2 f` plus the `HasDerivAt` chain, via
  `GyongyMimicry.continuous_f2_of_contDiff2` and `Continuous.measurable`;
* `hucont` — from `GyongyMimicry.continuous_marginal_integrand` (DCT interchange), fed by the
  path-continuity fields of `BoundedCoeffData` and the derivative bounds. -/
private theorem hasDerivAt_marginal_flow_core (P : BoundedCoeffData Ω) {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (h2 : ContDiff ℝ 2 f)
    {C1 C2 : ℝ} (hf'bd : ∀ x, |f' x| ≤ C1) (hf''bd : ∀ x, |f'' x| ≤ C2)
    (u : ℝ → ℝ)
    (hu : ∀ s, u s = ∫ ω, generatorIntegrand P.X P.β P.δ f' f'' s ω ∂μ)
    {T : ℝ}
    (hitoid : ∀ s ∈ Set.Ioo 0 T, ∫ ω, f (P.X s ω) ∂μ
      = ∫ ω, f (P.X 0 ω) ∂μ + ∫ x in (0)..s, u x)
    (t : ℝ) (ht0 : 0 < t) (htT : t < T) :
    HasDerivAt (fun s => ∫ ω, f (P.X s ω) ∂μ)
      (∫ ω, f' (P.X t ω) * driftCoeff μ P.X P.β t ω ∂μ
        + 1 / 2 * ∫ ω, f'' (P.X t ω) * diffCoeffSq μ P.X P.δ t ω ∂μ) t := by
  -- measurability of `f''` and continuity of `u` are derived below, not assumed
  have hf'diff : Differentiable ℝ f' := fun x => (hf' x).differentiableAt
  have hf'meas : Measurable f' := hf'diff.continuous.measurable
  have hf''cont : Continuous f'' := continuous_f2_of_contDiff2 h2 hf hf'
  have hf''meas : Measurable f'' := hf''cont.measurable
  have hucont : Continuous u := by
    rw [show u = (fun s => ∫ ω, generatorIntegrand P.X P.β P.δ f' f'' s ω ∂μ) from funext hu]
    exact continuous_marginal_integrand P hf'diff.continuous hf''cont hf'bd hf''bd
  -- FTC-1 on the integrated drift identity: it differentiates to the generator integrand
  have hint : HasDerivAt (fun s => ∫ x in (0)..s, u x) (u t) t :=
    intervalIntegral.integral_hasDerivAt_right (hucont.intervalIntegrable 0 t)
      (hucont.stronglyMeasurableAtFilter volume (𝓝 t)) hucont.continuousAt
  have key := hint.add_const (∫ ω, f (P.X 0 ω) ∂μ)
  -- the identity is consumed only through `=ᶠ[𝓝 t]`: an open band around `t` suffices
  have heq : (fun s => ∫ ω, f (P.X s ω) ∂μ)
      =ᶠ[𝓝 t] (fun s => (∫ x in (0)..s, u x) + ∫ ω, f (P.X 0 ω) ∂μ) := by
    filter_upwards [Ioo_mem_nhds ht0 htT] with s hs
    show ∫ ω, f (P.X s ω) ∂μ = (∫ x in (0)..s, u x) + ∫ ω, f (P.X 0 ω) ∂μ
    rw [add_comm]
    exact hitoid s hs
  have hmain := key.congr_of_eventuallyEq heq
  rw [hu t] at hmain
  simp only [generatorIntegrand] at hmain
  have h2' : Integrable (fun ω => 1 / 2 * (f'' (P.X t ω) * (P.δ t ω * P.δ t ω))) μ :=
    (integrable_testδsq P t hf''meas hf''bd).const_mul (1 / 2)
  rw [integral_add (integrable_testβ P t hf'meas hf'bd) h2',
    integral_const_mul,
    expectation_beta_eq_a P t hf'meas hf'bd,
    expectation_deltaSq_eq_b2 P t hf''meas hf''bd] at hmain
  exact hmain

end Flow

section Transfer

open MathFin ItoIntegralL2
open scoped NNReal

/-- **The `timeMeasure` ↔ interval-integral bridge** (the
definitional transfer of the adapted assembly's time integral into the
`intervalIntegral` form the marginal-flow machinery consumes): since
`ItoIntegralL2.timeMeasure = Measure.comap ((↑) : ℝ≥0 → ℝ) volume`, a `timeMeasure`
integral over the time band `(0, T]` *is* the Lebesgue integral over `(0, ↑T)` of the
coe-reindexing, read as an `intervalIntegral` by `intervalIntegral.integral_of_le`.

Route: `(comap c ν).restrict S = comap c (ν.restrict (c '' S))`
(`MeasurableEmbedding.restrict_comap` at the embedding
`ItoIntegralL2.measurableEmbedding_nnrealCoe`), `map c (comap c ν') = ν'.restrict (range c)`
(`MeasurableEmbedding.map_comap`, with `range c ⊇ c '' S`), and
`MeasurableEmbedding.integral_map` moves the integral to the `volume` side. Unconditional:
no measurability or integrability hypotheses — the bridge is a measure-theoretic
change of variables. -/
theorem timeMeasure_Ioc_eq_interval {g : ℝ≥0 → ℝ} (T : ℝ≥0) :
    ∫ s in Set.Ioc (0:ℝ≥0) T, g s ∂ItoIntegralL2.timeMeasure
      = ∫ x in (0)..(T:ℝ), g (Real.toNNReal x) := by
  have himg : ((↑) : ℝ≥0 → ℝ) '' Set.Ioc (0:ℝ≥0) T = Set.Ioc (0:ℝ) (T:ℝ) := by
    ext x
    simp only [Set.mem_image, Set.mem_Ioc]
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      exact ⟨by exact_mod_cast hy1, by exact_mod_cast hy2⟩
    · rintro ⟨hx1, hx2⟩
      have hy : (Real.toNNReal x : ℝ) = x := Real.coe_toNNReal x hx1.le
      have hle : (Real.toNNReal x : ℝ) ≤ (T:ℝ) := by rw [hy]; exact hx2
      exact ⟨Real.toNNReal x, Set.mem_Ioc.2 ⟨Real.toNNReal_pos.2 hx1,
        NNReal.coe_le_coe.mp hle⟩, hy⟩
  have hrng : ((↑) : ℝ≥0 → ℝ) '' Set.Ioc (0:ℝ≥0) T ⊆ Set.range ((↑) : ℝ≥0 → ℝ) :=
    Set.image_subset_range _ _
  have hmap : MeasureTheory.Measure.map ((↑) : ℝ≥0 → ℝ)
      (ItoIntegralL2.timeMeasure.restrict (Set.Ioc (0:ℝ≥0) T))
      = MeasureTheory.volume.restrict (((↑) : ℝ≥0 → ℝ) '' Set.Ioc (0:ℝ≥0) T) := by
    rw [ItoIntegralL2.timeMeasure,
      MeasurableEmbedding.restrict_comap measurableEmbedding_nnrealCoe,
      MeasurableEmbedding.map_comap measurableEmbedding_nnrealCoe,
      Measure.restrict_restrict measurableEmbedding_nnrealCoe.measurableSet_range,
      Set.inter_eq_right.2 hrng]
  calc ∫ s in Set.Ioc (0:ℝ≥0) T, g s ∂ItoIntegralL2.timeMeasure
      = ∫ x, g (Real.toNNReal (↑x)) ∂(ItoIntegralL2.timeMeasure.restrict (Set.Ioc (0:ℝ≥0) T)) :=
        MeasureTheory.integral_congr_ae (Eventually.of_forall fun x => by
          simp only [Real.toNNReal_coe])
    _ = ∫ y, g (Real.toNNReal y) ∂(MeasureTheory.Measure.map ((↑) : ℝ≥0 → ℝ)
          (ItoIntegralL2.timeMeasure.restrict (Set.Ioc (0:ℝ≥0) T))) :=
          (measurableEmbedding_nnrealCoe.integral_map
            (fun y : ℝ => g (Real.toNNReal y))).symm
    _ = ∫ y, g (Real.toNNReal y) ∂(MeasureTheory.volume.restrict
          (((↑) : ℝ≥0 → ℝ) '' Set.Ioc (0:ℝ≥0) T)) := by rw [hmap]
    _ = ∫ x in ((↑) : ℝ≥0 → ℝ) '' Set.Ioc (0:ℝ≥0) T, g (Real.toNNReal x) ∂volume := rfl
    _ = ∫ x in Set.Ioc (0:ℝ) (T:ℝ), g (Real.toNNReal x) ∂volume := by rw [himg]
    _ = ∫ x in (0)..(T:ℝ), g (Real.toNNReal x) ∂volume :=
        (intervalIntegral.integral_of_le (NNReal.coe_nonneg T)).symm

end Transfer

section Constructed

open MeasureTheory ProbabilityTheory Filter Topology
open MathFin ItoIntegralL2 ItoIntegralProcessGeneral
open scoped NNReal ENNReal

/-! ### The constructed instance and its `hitoid`

The concrete instantiation of `BoundedCoeffData` from the adapted integrated Itô-drift
identity `ItoDriftConditional.itoDrift_expectation_identity_adapted`, for which the
`hitoid` hypothesis of the marginal-flow core is proved below: `X t = c + ∫₀ᵗ β + M t`
(`AdaptedDrift.driftPath`-form; `β, δ`
bounded adapted path-continuous; `M` an adapted version of the CLM Itô integral of `δ` on
`[0, T]`; `X` path-continuous), reindexed to the real time axis by `t ↦ X_{t⁺}`
(`Real.toNNReal`).

* `constructedCoeffData` — the abstract structure's fields, all derived.
* `constructedGenIntegrandExp` — the generator integrand on the real time axis,
  `u x = 𝔼[f'(X_{x⁺})·β_{x⁺}] + ½·𝔼[f''(X_{x⁺})·δ²_{x⁺}]`.
* `hitoid_constructed_terminal` — the weakened `hitoid` at the horizon `↑T`, with no
  hypotheses beyond the assembly's own.
* `hitoid_constructed_band` — the `hitoid` on the open band `(0, ↑T)`, the form the
  marginal-flow engine consumes; the horizon consistency of the CLM integral is available
  (`itoProcessCLM_consist`/`ae_eq_itoProcessCLM_min`), so only the same horizon-`T` pinning `hMeq`
  as
  the terminal identity is needed.
* `marginal_flow_weak_equation_constructed` — **the generator-matching core of Bagaria
  ch. 9 / Thm 9.6 for the constructed process**: on `(0, ↑T)` the marginal flow solves the
  weak forward equation generated by the Gyöngy coefficients of the reindexed process. -/

/-- The real-time reindexing of an `ℝ≥0`-indexed process: negative real times are
identified with `0` (`X_{t⁺} = X_{max t 0}`). This is the concrete `ℝ`-indexed face of
the constructed process — and the process of the `BoundedCoeffData` instance below. -/
abbrev reindexed {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (s : ℝ) (ω : Ω) : ℝ := X (Real.toNNReal s) ω

/-- The constructed process is adapted (`AdaptedDrift.stronglyMeasurable_driftPath` + `hMadap`
through the decomposition `hXrel`). -/
theorem stronglyMeasurable_X_hXrel
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ}
    (hBmeas : ∀ t, Measurable (B t))
    {β : ℝ≥0 → Ω → ℝ}
    (hβadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (β t))
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db)
    {M : ℝ≥0 → Ω → ℝ}
    (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
    {X : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (hXrel : ∀ t : ℝ≥0, X t = fun ω : Ω ↦ c + AdaptedDrift.driftPath β t ω + M t ω)
    (t : ℝ≥0) : StronglyMeasurable[natFiltration hBmeas t] (X t) := by
  rw [hXrel t]
  exact (((AdaptedDrift.stronglyMeasurable_driftPath hBmeas hβadap hβcont hβbdd
  t).measurable.const_add c).add
    (hMadap t).measurable).stronglyMeasurable

/-- **The concrete `BoundedCoeffData` instance**: the abstract
ℝ-indexed structure of this file, instantiated from the constructed process `X = c + ∫β + M`
by real-time reindexing `t ↦ t⁺` and the natural Brownian filtration
`𝓕_s = 𝓕ᴮ_{s⁺}`. Every field is *derived*: measurability of `X` from
`GyongyMimicry.stronglyMeasurable_X_hXrel` (the decomposition +
`AdaptedDrift.stronglyMeasurable_driftPath`), path continuity from the assembly's
path-continuity hypotheses composed with `continuous_real_toNNReal`, and the coefficient
bounds from the assembly's (with `B = |Db|`, `D = |Dd|`). -/
noncomputable def constructedCoeffData
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ}
    (hBmeas : ∀ t, Measurable (B t))
    {β : ℝ≥0 → Ω → ℝ}
    (hβadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (β t))
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db)
    {δ : ℝ≥0 → Ω → ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    {Dd : ℝ} (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
    {M : ℝ≥0 → Ω → ℝ}
    (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
    {X : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (hXcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ X s ω)
    (hXrel : ∀ t : ℝ≥0, X t = fun ω : Ω ↦ c + AdaptedDrift.driftPath β t ω + M t ω) :
    BoundedCoeffData Ω where
  X := reindexed X
  β := reindexed β
  δ := reindexed δ
  B := |Db|
  D := |Dd|
  Bpos := abs_nonneg Db
  Dpos := abs_nonneg Dd
  hXmeas := fun s ↦
    (stronglyMeasurable_X_hXrel hBmeas hβadap hβcont hβbdd hMadap c hXrel
      (Real.toNNReal s)).measurable.mono ((natFiltration hBmeas).le (Real.toNNReal s)) le_rfl
  hβmeas := fun s ↦
    (hβadap (Real.toNNReal s)).measurable.mono
      ((natFiltration hBmeas).le (Real.toNNReal s)) le_rfl
  hδmeas := fun s ↦
    (hδadap (Real.toNNReal s)).measurable.mono
      ((natFiltration hBmeas).le (Real.toNNReal s)) le_rfl
  hβbdd := fun s ω ↦ (hβbdd (Real.toNNReal s) ω).trans (le_abs_self Db)
  hδbdd := fun s ω ↦ (hδbdd (Real.toNNReal s) ω).trans (le_abs_self Dd)
  hXcont := fun ω ↦ (hXcont ω).comp continuous_real_toNNReal
  hβcont := fun ω ↦ (hβcont ω).comp continuous_real_toNNReal
  hδcont := fun ω ↦ (hδcont ω).comp continuous_real_toNNReal

/-- **The generator integrand of the constructed process, on the real time axis**
(the `u` of the marginal-flow machinery): at real
time `x` this is

  `u x = 𝔼[f'(X_{x⁺})·β_{x⁺}] + ½·𝔼[f''(X_{x⁺})·δ²_{x⁺}]`,

exactly the assembly's integrated integrand
(`ItoDriftConditional.itoDrift_expectation_identity_adapted`'s `timeMeasure` integrand) read
on the real axis. -/
noncomputable def constructedGenIntegrandExp {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) (X β δ : ℝ≥0 → Ω → ℝ) (f' f'' : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ ω, f' (reindexed X x ω) * reindexed β x ω ∂μ)
    + (1 / 2) * (∫ ω, f'' (reindexed X x ω) * (reindexed δ x ω * reindexed δ x ω) ∂μ)

/-- At `ℝ≥0` times the real-axis integrand reads the assembly's integrand verbatim. -/
theorem constructedGenIntegrandExp_coe {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) (X β δ : ℝ≥0 → Ω → ℝ) (f' f'' : ℝ → ℝ) (t : ℝ≥0) :
    constructedGenIntegrandExp μ X β δ f' f'' ↑t
      = (∫ ω, f' (X t ω) * β t ω ∂μ)
        + (1 / 2) * (∫ ω, f'' (X t ω) * (δ t ω * δ t ω) ∂μ) := by
  simp [constructedGenIntegrandExp, reindexed, Real.toNNReal_coe]

/-- The bridge to the instance's `generatorIntegrand` expectation — exactly the `hu`
hypothesis of the marginal-flow engine for `u := constructedGenIntegrandExp`. -/
private theorem constructedGenIntegrandExp_eq
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hBmeas : ∀ t, Measurable (B t))
    {β : ℝ≥0 → Ω → ℝ}
    (hβadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (β t))
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db)
    {δ : ℝ≥0 → Ω → ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    {Dd : ℝ} (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
    {M : ℝ≥0 → Ω → ℝ}
    (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
    {X : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (hXrel : ∀ t : ℝ≥0, X t = fun ω : Ω ↦ c + AdaptedDrift.driftPath β t ω + M t ω)
    {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (h2 : ContDiff ℝ 2 f)
    {C1 C2 : ℝ} (hg1 : ∀ x, |f' x| ≤ C1) (hg2 : ∀ x, |f'' x| ≤ C2)
    (x : ℝ) :
    constructedGenIntegrandExp μ X β δ f' f'' x
      = ∫ ω, generatorIntegrand (reindexed X) (reindexed β) (reindexed δ) f' f'' x ω ∂μ := by
  -- measurability of the factors (the instance's data, rederived pointwise)
  have hf'diff : Differentiable ℝ f' := fun x => (hf' x).differentiableAt
  have hf'meas : Measurable f' := hf'diff.continuous.measurable
  have hf''cont : Continuous f'' := continuous_f2_of_contDiff2 h2 hf hf'
  have hf''meas : Measurable f'' := hf''cont.measurable
  have hXmeas : ∀ t : ℝ≥0, Measurable (X t) := fun t ↦
    (stronglyMeasurable_X_hXrel hBmeas hβadap hβcont hβbdd hMadap c hXrel t).measurable.mono
      ((natFiltration hBmeas).le t) le_rfl
  have hβmeas : ∀ t : ℝ≥0, Measurable (β t) := fun t ↦
    (hβadap t).measurable.mono ((natFiltration hBmeas).le t) le_rfl
  have hδmeas : ∀ t : ℝ≥0, Measurable (δ t) := fun t ↦
    (hδadap t).measurable.mono ((natFiltration hBmeas).le t) le_rfl
  have hC1 : 0 ≤ C1 := le_trans (abs_nonneg _) (hg1 0)
  have hC2 : 0 ≤ C2 := le_trans (abs_nonneg _) (hg2 0)
  have h1 : Integrable (fun ω => f' (reindexed X x ω) * reindexed β x ω) μ :=
    integrable_of_bounded ((hf'meas.comp (hXmeas _)).mul (hβmeas _)) (C1 * |Db|)
      (fun ω => by
        rw [abs_mul]
        calc |f' (reindexed X x ω)| * |reindexed β x ω|
            ≤ C1 * |reindexed β x ω| := mul_le_mul_of_nonneg_right (hg1 _) (abs_nonneg _)
          _ ≤ C1 * |Db| := mul_le_mul_of_nonneg_left
              ((hβbdd (Real.toNNReal x) ω).trans (le_abs_self Db)) hC1)
  have h2i : Integrable (fun ω => f'' (reindexed X x ω)
      * (reindexed δ x ω * reindexed δ x ω)) μ :=
    integrable_of_bounded
      ((hf''meas.comp (hXmeas _)).mul ((hδmeas _).mul (hδmeas _))) (C2 * (|Dd| * |Dd|))
      (fun ω => by
        rw [abs_mul, abs_mul]
        calc |f'' (reindexed X x ω)| * (|reindexed δ x ω| * |reindexed δ x ω|)
            ≤ C2 * (|reindexed δ x ω| * |reindexed δ x ω|) :=
              mul_le_mul_of_nonneg_right (hg2 _)
                (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          _ ≤ C2 * (|Dd| * |Dd|) :=
              mul_le_mul_of_nonneg_left
                (calc |reindexed δ x ω| * |reindexed δ x ω|
                      ≤ |Dd| * |reindexed δ x ω| :=
                          mul_le_mul_of_nonneg_right
                            ((hδbdd (Real.toNNReal x) ω).trans (le_abs_self Dd))
                            (abs_nonneg _)
                    _ ≤ |Dd| * |Dd| :=
                          mul_le_mul_of_nonneg_left
                            ((hδbdd (Real.toNNReal x) ω).trans (le_abs_self Dd))
                            (abs_nonneg Dd)) hC2)
  show (∫ ω, f' (reindexed X x ω) * reindexed β x ω ∂μ)
    + (1 / 2) * (∫ ω, f'' (reindexed X x ω) * (reindexed δ x ω * reindexed δ x ω) ∂μ)
    = ∫ ω, (f' (reindexed X x ω) * reindexed β x ω
        + 1 / 2 * (f'' (reindexed X x ω) * (reindexed δ x ω * reindexed δ x ω))) ∂μ
  rw [integral_add h1 (h2i.const_mul (1 / 2)), integral_const_mul]

/-- **Terminal form of `hitoid` for the constructed instance, at the horizon**: the
integrated Itô–drift identity `ItoDriftConditional.itoDrift_expectation_identity_adapted`,
transferred to the interval-integral form, for the constructed process and its generator
integrand.
No hypotheses beyond the assembly's own. -/
theorem hitoid_constructed_terminal
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    {T : ℝ≥0} {β : ℝ≥0 → Ω → ℝ}
    (hβadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (β t))
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db)
    {δ : ℝ≥0 → Ω → ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    {Dd : ℝ} (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
    {M : ℝ≥0 → Ω → ℝ}
    (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
    (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
      (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))
    {X : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (hXcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ X s ω)
    (hXrel : ∀ t : ℝ≥0, X t = fun ω : Ω ↦ c + AdaptedDrift.driftPath β t ω + M t ω)
    {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    {f''' : ℝ → ℝ} (hf'' : ∀ x, HasDerivAt f'' (f''' x) x)
    {C1 C2 C3 : ℝ} (hg1 : ∀ x, |f' x| ≤ C1) (hg2 : ∀ x, |f'' x| ≤ C2)
    (hg3 : ∀ x, |f''' x| ≤ C3) :
    ∫ ω, f (X T ω) ∂μ
      = ∫ ω, f (X (0:ℝ≥0) ω) ∂μ
        + ∫ x in (0)..(T:ℝ), constructedGenIntegrandExp μ X β δ f' f'' x := by
  have hident := ItoDriftConditional.itoDrift_expectation_identity_adapted hB hBmeas hδadap
    hδcont hδbdd hMadap hMeq hβadap hβcont hβbdd c (Eventually.of_forall hXcont) hXrel
    hf hf' hf'' hg1 hg2 hg3
  rw [hident, timeMeasure_Ioc_eq_interval]
  rfl

/-- **Band form of `hitoid` on the open band `(0, ↑T)`**, the form the marginal-flow core
consumes (`=ᶠ[𝓝 t]` for `t` in the band), proved from the horizon-`T` pinning `hMeq` alone.
That the same `M` represents the CLM Itô integral at every horizon `τ ≤ T` is
`ae_eq_itoProcessCLM_min` (cross-horizon consistency), used through the **frozen
reversion** `t ↦ M (min t τ)`:

* `ae_eq_itoProcessCLM_min` shows the reversion represents the τ-horizon CLM
  process at *every* time — at `t ≤ τ` by the cross-horizon consistency
  (`itoProcessCLM_consist`), past `τ` by the freeze law
  (`itoProcessCLM_eq_terminal_of_ge`);
* the reversion is adapted (`𝓕_{min t τ} ≤ 𝓕_t`) and path-continuous (`min` is
  continuous, `M` is along `X`), so the adapted identity re-runs at the interior
  horizon `τ = ↑s` for the reverted process;
* the reverted process agrees with `X` *pointwise* at every time `t ≤ τ` (there
  `min t τ = t`), so the identity at the horizon and on the band reads verbatim as the
  band identity for `X`. -/
theorem hitoid_constructed_band
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    {T : ℝ≥0} {β : ℝ≥0 → Ω → ℝ}
    (hβadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (β t))
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db)
    {δ : ℝ≥0 → Ω → ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    {Dd : ℝ} (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
    {M : ℝ≥0 → Ω → ℝ}
    (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
    (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
      (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))
    {X : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (hXcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ X s ω)
    (hXrel : ∀ t : ℝ≥0, X t = fun ω : Ω ↦ c + AdaptedDrift.driftPath β t ω + M t ω)
    {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    {f''' : ℝ → ℝ} (hf'' : ∀ x, HasDerivAt f'' (f''' x) x)
    {C1 C2 C3 : ℝ} (hg1 : ∀ x, |f' x| ≤ C1) (hg2 : ∀ x, |f'' x| ≤ C2)
    (hg3 : ∀ x, |f''' x| ≤ C3)
    {s : ℝ} (hs : s ∈ Set.Ioo 0 (T : ℝ)) :
    ∫ ω, f (X (Real.toNNReal s) ω) ∂μ
      = ∫ ω, f (X (0:ℝ≥0) ω) ∂μ
        + ∫ x in (0)..s, constructedGenIntegrandExp μ X β δ f' f'' x := by
  have hτ0 : (Real.toNNReal s : ℝ) = s := Real.coe_toNNReal s hs.1.le
  have hτT : Real.toNNReal s ≤ T := by
    have h : Real.toNNReal s ≤ Real.toNNReal (T:ℝ) := Real.toNNReal_mono hs.2.le
    rwa [Real.toNNReal_coe] at h
  -- the frozen reversion of `M` at the interior horizon `τ = ↑s`
  set Mfrz : ℝ≥0 → Ω → ℝ := fun t ↦ M (min t (Real.toNNReal s)) with hMfrz
  set Xfrz : ℝ≥0 → Ω → ℝ :=
    fun t ω ↦ c + AdaptedDrift.driftPath β t ω + Mfrz t ω with hXfrz
  -- `Mfrz` represents the τ-horizon CLM process at every time (the consistency lemma)
  have hMeqτ := ae_eq_itoProcessCLM_min hB hBmeas hδadap hδcont hδbdd hMeq
    (Real.toNNReal s) hτT
  -- the reversion is adapted (monotone filtration through `min`)
  have hMadapτ : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (Mfrz t) := fun t ↦
    StronglyMeasurable.mono (hMadap (min t (Real.toNNReal s)))
      ((natFiltration hBmeas).mono (min_le_left t (Real.toNNReal s)))
  -- path continuity: `M` is along `X` (via `hXrel`), and `min` is continuous
  have hcontM : ∀ ω, Continuous (fun u : ℝ≥0 ↦ M u ω) := by
    intro ω
    have hEq : (fun u : ℝ≥0 ↦ M u ω)
        = (fun u : ℝ≥0 ↦ X u ω - c - AdaptedDrift.driftPath β u ω) := by
      funext u
      simp only [hXrel u]
      ring
    rw [hEq]
    exact (((hXcont ω).sub continuous_const).sub
      (AdaptedDrift.continuous_driftPath hβcont hβbdd ω))
  have hMfrzcont : ∀ ω, Continuous (fun u : ℝ≥0 ↦ Mfrz u ω) :=
    fun ω ↦ (hcontM ω).comp
      (continuous_min.comp ((continuous_id).prodMk continuous_const))
  have hXfrzcont : ∀ ω, Continuous (fun u : ℝ≥0 ↦ Xfrz u ω) := fun ω ↦
    (continuous_const.add
      (AdaptedDrift.continuous_driftPath hβcont hβbdd ω)).add
      (hMfrzcont ω)
  -- the reverted process agrees with `X` pointwise on `[0, τ]`
  have hXeqfrz : ∀ t : ℝ≥0, t ≤ Real.toNNReal s → Xfrz t = X t := by
    intro t ht
    funext ω
    simp only [hXfrz, hMfrz, hXrel t, min_eq_left ht]
  -- the adapted identity, re-run at the interior horizon for the reversion
  have hident := ItoDriftConditional.itoDrift_expectation_identity_adapted hB hBmeas hδadap
    hδcont hδbdd hMadapτ hMeqτ hβadap hβcont hβbdd c (Eventually.of_forall hXfrzcont)
    (fun t => rfl) hf hf'
    hf'' hg1 hg2 hg3 (T := Real.toNNReal s) (M := Mfrz) (X := Xfrz)
  -- the time-band integrand transfers to the generator integrand of `X`
  have hbandeq : ∫ s2 in Set.Ioc (0:ℝ≥0) (Real.toNNReal s),
      ((∫ ω, f' (Xfrz s2 ω) * β s2 ω ∂μ)
        + (1 / 2) * (∫ ω, f'' (Xfrz s2 ω) * (δ s2 ω * δ s2 ω) ∂μ))
      ∂ItoIntegralL2.timeMeasure
      = ∫ x in (0)..s, constructedGenIntegrandExp μ X β δ f' f'' x := by
    rw [timeMeasure_Ioc_eq_interval, hτ0]
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hx0 : (0:ℝ) ≤ x := by
      rw [← min_eq_left hs.1.le]
      exact hx.1
    have hxs : x ≤ s := by
      rw [← max_eq_right hs.1.le]
      exact hx.2
    have hXfr : Xfrz (Real.toNNReal x) = X (Real.toNNReal x) :=
      hXeqfrz _ (Real.toNNReal_mono hxs)
    simp only [constructedGenIntegrandExp]
    rw [hXfr]
  -- assemble: the horizon and band identities for the reversion read for `X` verbatim
  rw [← hXeqfrz (Real.toNNReal s) le_rfl, ← hXeqfrz 0 (by simp), hident, hbandeq]

/-- **The weak forward equation — the generator-matching core of Bagaria ch. 9 /
Thm 9.6 for the constructed process**: on the open band `(0, ↑T)` the marginal flow
`s ↦ 𝔼[f(X_{s⁺})]` of the constructed Itô process `X = c + ∫β + M` is differentiable,
with derivative the `(a, b²)`-generator of the **Gyöngy coefficients of the reindexed
process**,

  `d/dt 𝔼[f(X_{t⁺})] = 𝔼[f'(X_{t⁺}) · a] + ½·𝔼[f''(X_{t⁺}) · b²]`,
  `a = 𝔼[β_{⟨t⟩} | σ(X_{⟨t⟩})]`, `b² = 𝔼[δ²_{⟨t⟩} | σ(X_{⟨t⟩})]`,

driven by the *real* integrated Itô–drift identity
(`ItoDriftConditional.itoDrift_expectation_identity_adapted`,
transferred) rather than the `hitoid` hypothesis. This is the computation whose
uniqueness-up-to-marginals content is Gyöngy's theorem; the mimicking diffusion's
*existence* is not proved (see the module docstring). The horizon consistency of the CLM
integral (`itoProcessCLM_consist`/`ae_eq_itoProcessCLM_min`) means this theorem needs only
the same horizon-`T` pinning `hMeq` as the terminal identity. -/
theorem marginal_flow_weak_equation_constructed
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    {T : ℝ≥0} {β : ℝ≥0 → Ω → ℝ}
    (hβadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (β t))
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db)
    {δ : ℝ≥0 → Ω → ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    {Dd : ℝ} (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
    {M : ℝ≥0 → Ω → ℝ}
    (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
    (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
      (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))
    {X : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (hXcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ X s ω)
    (hXrel : ∀ t : ℝ≥0, X t = fun ω : Ω ↦ c + AdaptedDrift.driftPath β t ω + M t ω)
    {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (h2 : ContDiff ℝ 2 f)
    {f''' : ℝ → ℝ} (hf'' : ∀ x, HasDerivAt f'' (f''' x) x)
    {C1 C2 C3 : ℝ} (hg1 : ∀ x, |f' x| ≤ C1) (hg2 : ∀ x, |f'' x| ≤ C2)
    (hg3 : ∀ x, |f''' x| ≤ C3)
    (t : ℝ) (ht : 0 < t) (htT : Real.toNNReal t < T) :
    HasDerivAt (fun s : ℝ => ∫ ω, f (X (Real.toNNReal s) ω) ∂μ)
      (∫ ω, f' (X (Real.toNNReal t) ω) * driftCoeff μ (reindexed X) (reindexed β) t ω ∂μ
        + 1 / 2 * ∫ ω, f'' (X (Real.toNNReal t) ω)
            * diffCoeffSq μ (reindexed X) (reindexed δ) t ω ∂μ) t := by
  have htlT : t < (T:ℝ) := by
    have h1 : ((Real.toNNReal t : ℝ)) = t := Real.coe_toNNReal t ht.le
    have h2lt : ((Real.toNNReal t : ℝ)) < (T:ℝ) := NNReal.coe_lt_coe.mpr htT
    rwa [h1] at h2lt
  refine hasDerivAt_marginal_flow_core
    (constructedCoeffData hBmeas hβadap hβcont hβbdd hδadap hδcont hδbdd hMadap c
      hXcont hXrel)
    hf hf' h2 hg1 hg2 (constructedGenIntegrandExp μ X β δ f' f'') ?_ ?_ t ht htlT
  · exact constructedGenIntegrandExp_eq hBmeas hβadap hβcont hβbdd hδadap hδbdd hMadap c
      hXrel hf hf' h2 hg1 hg2
  · intro s hs
    have hband := hitoid_constructed_band hB hBmeas hβadap hβcont hβbdd hδadap hδcont hδbdd
      hMadap hMeq c hXcont hXrel hf hf' hf'' hg1 hg2 hg3 hs
    -- the instance's time-0 point is `reindexed X 0 = X ⟨0⁺⟩`; `Real.toNNReal 0 = 0`
    have h0 : (0:ℝ≥0) = Real.toNNReal 0 := (Real.toNNReal_zero).symm
    rw [h0] at hband
    exact hband

end Constructed



/-!
# The Doob–Dynkin coefficient functions and the mimicry statement (Thm 9.6's Y-side)

The Ω-level conditional-expectation coefficients `driftCoeff`/`diffCoeffSq` of the
*constructed* process are upgraded to Borel coefficient *functions*
`â, b̂² : ℝ → ℝ → ℝ` via the Doob–Dynkin lemma
(`MeasureTheory.StronglyMeasurable.exists_eq_measurable_comp`) — the coefficients of
Thm 9.6 in `(t, x)` form. On top of it, `gyongy_mimicry_gated` — one-time-marginal
mimicry of the constructed `X` by a given `Y`, under a *flow-uniqueness hypothesis*
(the test-function form of martingale-problem uniqueness); `Y`'s existence with
merely-measurable coefficients and that uniqueness are not proved.
-/


section Fn

open MeasureTheory ProbabilityTheory Filter Topology
open MathFin ItoIntegralL2 ItoIntegralProcessGeneral
open scoped NNReal ENNReal

/-- The general Doob–Dynkin factorization step: a
`σ(X_t)`-strongly-measurable random variable is a Borel function of `X_t` — *pointwise*, with
a measurable version. This is `MeasureTheory.StronglyMeasurable.exists_eq_measurable_comp`
(Doob–Dynkin, `FactorsThrough.lean`) read at `sigmaGen X t = Real.measurableSpace.comap (X t)`
(the fit is exact: `Z := ℝ` is nonempty and completely metrizable), with the strongly
measurable factorization function upgraded to `Measurable` through ℝ's standard-Borel
structure. -/
private theorem exists_coeffFn_comp {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ → Ω → ℝ) (g : Ω → ℝ) (t : ℝ) (hg : StronglyMeasurable[sigmaGen X t] g) :
    ∃ a : ℝ → ℝ, Measurable a ∧ ∀ ω, g ω = a (X t ω) := by
  obtain ⟨a, ha, haeq⟩ := hg.exists_eq_measurable_comp
  exact ⟨a, ha.measurable, fun ω => congrFun haeq ω⟩

/-- **Drift coefficient function**: for the
constructed-process data of the `marginal_flow_weak_equation_constructed` instance (same
hypotheses shape), Gyöngy's drift coefficient `a_t = 𝔼[β_t | σ(X_t)]` *is* a Borel function
of the current state, pointwise: `∃ â : ℝ → ℝ`, `Measurable â` and
`driftCoeff 𝔼 X β t ω = â (X_t ω)` for every `ω` — the `(t, ·)`-section of Thm 9.6's
`a(t, x) = 𝔼[β_t | X_t = x]` as a deterministic function.

Engine: `stronglyMeasurable_condExp` (unconditional in this Mathlib rev) +
`GyongyMimicry.exists_coeffFn_comp`. Doob–Dynkin needs no dynamics data at all (the
coefficient's σ(X_t)-strong-measurability is unconditional), so the statement carries no
Itô-process hypotheses: it is available at any measurability level of the underlying data,
in particular for the constructed process of `marginal_flow_weak_equation_constructed`.

The bound `|â (X_t ω)| ≤ B` holds only a.e. (the factorization is pointwise but
`|μ[g | m]| ≤ B` holds a.e.) and is not part of the statement. -/
theorem exists_driftCoeff_fn
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {X : ℝ≥0 → Ω → ℝ} {β : ℝ≥0 → Ω → ℝ} (t : ℝ) :
    ∃ a : ℝ → ℝ, Measurable a ∧ ∀ ω, driftCoeff μ (reindexed X) (reindexed β) t ω
      = a (reindexed X t ω) :=
  exists_coeffFn_comp (reindexed X) (driftCoeff μ (reindexed X) (reindexed β) t) t
    stronglyMeasurable_condExp

/-- **Squared-diffusion coefficient function**: the twin
of `GyongyMimicry.exists_driftCoeff_fn` for `b²_t = 𝔼[δ_t² | σ(X_t)]`:
`∃ b̂² : ℝ → ℝ`, `Measurable b̂²` and `diffCoeffSq 𝔼 X δ t ω = b̂² (X_t ω)` pointwise —
the `(t, ·)`-section of Thm 9.6's `b²(t, x) = 𝔼[δ_t² | X_t = x]`.

Nonnegativity `0 ≤ b̂² (X_t ω)` holds only a.e. (`condExp` nonnegativity) and is not part of
the statement. -/
theorem exists_diffCoeffSq_fn
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {X : ℝ≥0 → Ω → ℝ} {δ : ℝ≥0 → Ω → ℝ} (t : ℝ) :
    ∃ b : ℝ → ℝ, Measurable b ∧ ∀ ω, diffCoeffSq μ (reindexed X) (reindexed δ) t ω
      = b (reindexed X t ω) :=
  exists_coeffFn_comp (reindexed X) (diffCoeffSq μ (reindexed X) (reindexed δ) t) t
    stronglyMeasurable_condExp

/-- **The weak forward equation in coefficient-function form**: the weak forward equation
restated with the composed Borel coefficient functions: on the band `(0, ↑T)` the marginal
flow of the constructed process is differentiable with derivative

  `d/dt 𝔼[f(X_{t⁺})] = 𝔼[f'(X_{t⁺}) · â(t, X_{t⁺})] + ½ · 𝔼[f''(X_{t⁺}) · b̂²(t, X_{t⁺})]`,

where `â, b̂² : ℝ → ℝ → ℝ` are any Borel coefficient *functions* representing the Gyöngy
coefficients pointwise (`hafn`, `hbfn` — provided at every time by
`GyongyMimicry.exists_driftCoeff_fn`
and `GyongyMimicry.exists_diffCoeffSq_fn`). The generator no longer mentions the Ω-level
conditional expectations, only deterministic functions of the state.

Proof: `marginal_flow_weak_equation_constructed` plus funext-level congruence transport of the
two integrands (the representations are pointwise `∀ ω`, so `integral_congr_ae` needs no
measurability of the representing functions). -/
theorem marginal_flow_weak_equation_fn_constructed
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    {T : ℝ≥0} {β : ℝ≥0 → Ω → ℝ}
    (hβadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (β t))
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db)
    {δ : ℝ≥0 → Ω → ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    {Dd : ℝ} (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
    {M : ℝ≥0 → Ω → ℝ}
    (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
    (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
      (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))
    {X : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (hXcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ X s ω)
    (hXrel : ∀ t : ℝ≥0, X t = fun ω : Ω ↦ c + AdaptedDrift.driftPath β t ω + M t ω)
    {afn bfn : ℝ → ℝ → ℝ}
    (hafn : ∀ s, Measurable (afn s) ∧ ∀ ω, driftCoeff μ (reindexed X) (reindexed β) s ω
      = afn s (X (Real.toNNReal s) ω))
    (hbfn : ∀ s, Measurable (bfn s) ∧ ∀ ω, diffCoeffSq μ (reindexed X) (reindexed δ) s ω
      = bfn s (X (Real.toNNReal s) ω))
    {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (h2 : ContDiff ℝ 2 f)
    {f''' : ℝ → ℝ} (hf'' : ∀ x, HasDerivAt f'' (f''' x) x)
    {C1 C2 C3 : ℝ} (hg1 : ∀ x, |f' x| ≤ C1) (hg2 : ∀ x, |f'' x| ≤ C2)
    (hg3 : ∀ x, |f''' x| ≤ C3)
    (t : ℝ) (ht : 0 < t) (htT : Real.toNNReal t < T) :
    HasDerivAt (fun s : ℝ => ∫ ω, f (X (Real.toNNReal s) ω) ∂μ)
      (∫ ω, f' (X (Real.toNNReal t) ω) * afn t (X (Real.toNNReal t) ω) ∂μ
        + 1 / 2 * ∫ ω, f'' (X (Real.toNNReal t) ω) * bfn t (X (Real.toNNReal t) ω) ∂μ) t := by
  -- the congruence transport: the representations are pointwise, so the integrands rewrite
  have e1 : (∫ ω, f' (X (Real.toNNReal t) ω)
          * driftCoeff μ (reindexed X) (reindexed β) t ω ∂μ)
      = (∫ ω, f' (X (Real.toNNReal t) ω) * afn t (X (Real.toNNReal t) ω) ∂μ) :=
    integral_congr_ae (Eventually.of_forall fun ω => by
      show f' (X (Real.toNNReal t) ω) * driftCoeff μ (reindexed X) (reindexed β) t ω
        = f' (X (Real.toNNReal t) ω) * afn t (X (Real.toNNReal t) ω)
      rw [(hafn t).2 ω])
  have e2 : (∫ ω, f'' (X (Real.toNNReal t) ω)
          * diffCoeffSq μ (reindexed X) (reindexed δ) t ω ∂μ)
      = (∫ ω, f'' (X (Real.toNNReal t) ω) * bfn t (X (Real.toNNReal t) ω) ∂μ) :=
    integral_congr_ae (Eventually.of_forall fun ω => by
      show f'' (X (Real.toNNReal t) ω) * diffCoeffSq μ (reindexed X) (reindexed δ) t ω
        = f'' (X (Real.toNNReal t) ω) * bfn t (X (Real.toNNReal t) ω)
      rw [(hbfn t).2 ω])
  rw [← e1, ← e2]
  exact marginal_flow_weak_equation_constructed hB hBmeas hβadap hβcont hβbdd hδadap hδcont
    hδbdd hMadap hMeq c hXcont hXrel hf hf' h2 hf'' hg1 hg2 hg3 t ht htT

/-- The congruence transport at the level of the constructed generator integrand:
`constructedGenIntegrandExp` — the Ω-level conditional
expectation form `𝔼[f'(X_{x⁺})·β_{x⁺}] + ½·𝔼[f''(X_{x⁺})·δ²_{x⁺}]` — equals the
coefficient-function form `𝔼[f'(X_{x⁺})·â(x, X_{x⁺})] + ½·𝔼[f''(X_{x⁺})·b̂²(x, X_{x⁺})]`
whenever `afn`/`bfn` represent the Gyöngy coefficients pointwise. Route: the two
generator-matching identities `expectation_beta_eq_a`/`expectation_deltaSq_eq_b2` (tower
step, against the constructed instance) then pointwise congruence of the representations. -/
private theorem constructedGenIntegrandExp_fn
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hBmeas : ∀ t, Measurable (B t))
    {β : ℝ≥0 → Ω → ℝ}
    (hβadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (β t))
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db)
    {δ : ℝ≥0 → Ω → ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    {Dd : ℝ} (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
    {M : ℝ≥0 → Ω → ℝ}
    (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
    {X : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (hXcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ X s ω)
    (hXrel : ∀ t : ℝ≥0, X t = fun ω : Ω ↦ c + AdaptedDrift.driftPath β t ω + M t ω)
    {afn bfn : ℝ → ℝ → ℝ}
    (hafnRep : ∀ (s : ℝ) (ω : Ω), driftCoeff μ (reindexed X) (reindexed β) s ω
      = afn s (X (Real.toNNReal s) ω))
    (hbfnRep : ∀ (s : ℝ) (ω : Ω), diffCoeffSq μ (reindexed X) (reindexed δ) s ω
      = bfn s (X (Real.toNNReal s) ω))
    {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (h2 : ContDiff ℝ 2 f)
    {C1 C2 : ℝ} (hg1 : ∀ x, |f' x| ≤ C1) (hg2 : ∀ x, |f'' x| ≤ C2)
    (x : ℝ) :
    constructedGenIntegrandExp μ X β δ f' f'' x
      = (∫ ω, f' (X (Real.toNNReal x) ω) * afn x (X (Real.toNNReal x) ω) ∂μ)
        + 1 / 2 * (∫ ω, f'' (X (Real.toNNReal x) ω) * bfn x (X (Real.toNNReal x) ω) ∂μ) := by
  have hf'diff : Differentiable ℝ f' := fun x => (hf' x).differentiableAt
  have hf'meas : Measurable f' := hf'diff.continuous.measurable
  have hf''cont : Continuous f'' := continuous_f2_of_contDiff2 h2 hf hf'
  have hf''meas : Measurable f'' := hf''cont.measurable
  have e1 : (∫ ω, f' (reindexed X x ω) * reindexed β x ω ∂μ)
      = (∫ ω, f' (X (Real.toNNReal x) ω) * afn x (X (Real.toNNReal x) ω) ∂μ) := by
    calc (∫ ω, f' (reindexed X x ω) * reindexed β x ω ∂μ)
        = (∫ ω, f' (reindexed X x ω)
            * driftCoeff μ (reindexed X) (reindexed β) x ω ∂μ) :=
          expectation_beta_eq_a
            (constructedCoeffData hBmeas hβadap hβcont hβbdd hδadap hδcont hδbdd
              hMadap c hXcont hXrel) x hf'meas hg1
      _ = (∫ ω, f' (X (Real.toNNReal x) ω) * afn x (X (Real.toNNReal x) ω) ∂μ) :=
          integral_congr_ae (Eventually.of_forall fun ω => by
            show f' (reindexed X x ω) * driftCoeff μ (reindexed X) (reindexed β) x ω
              = f' (X (Real.toNNReal x) ω) * afn x (X (Real.toNNReal x) ω)
            rw [hafnRep x ω])
  have e2 : (∫ ω, f'' (reindexed X x ω) * (reindexed δ x ω * reindexed δ x ω) ∂μ)
      = (∫ ω, f'' (X (Real.toNNReal x) ω) * bfn x (X (Real.toNNReal x) ω) ∂μ) := by
    calc (∫ ω, f'' (reindexed X x ω) * (reindexed δ x ω * reindexed δ x ω) ∂μ)
        = (∫ ω, f'' (reindexed X x ω)
            * diffCoeffSq μ (reindexed X) (reindexed δ) x ω ∂μ) :=
          expectation_deltaSq_eq_b2
            (constructedCoeffData hBmeas hβadap hβcont hβbdd hδadap hδcont hδbdd
              hMadap c hXcont hXrel) x hf''meas hg2
      _ = (∫ ω, f'' (X (Real.toNNReal x) ω) * bfn x (X (Real.toNNReal x) ω) ∂μ) :=
          integral_congr_ae (Eventually.of_forall fun ω => by
            show f'' (reindexed X x ω) * diffCoeffSq μ (reindexed X) (reindexed δ) x ω
              = f'' (X (Real.toNNReal x) ω) * bfn x (X (Real.toNNReal x) ω)
            rw [hbfnRep x ω])
  show (∫ ω, f' (reindexed X x ω) * reindexed β x ω ∂μ)
      + 1 / 2 * (∫ ω, f'' (reindexed X x ω) * (reindexed δ x ω * reindexed δ x ω) ∂μ) = _
  rw [e1, e2]

/-- The integrated forward identity of the constructed process in **coefficient-function
form**, on the whole time band `(0, ↑T]`: for every test
function of the class, `∫ g(X_{s⁺}) = ∫ g(X_0) + ∫_{(0,s]} (𝔼[g'(X_{x⁺})·â(x, X_{x⁺})] +
½ 𝔼[g''(X_{x⁺})·b̂²(x, X_{x⁺})]) dx`. Assembled from the two `hitoid` forms —
`hitoid_constructed_band` on the open band, `hitoid_constructed_terminal` at the horizon —
with the integrand transported by `GyongyMimicry.constructedGenIntegrandExp_fn`. -/
private theorem hitoid_constructed_fn_Ioc
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    {T : ℝ≥0} {β : ℝ≥0 → Ω → ℝ}
    (hβadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (β t))
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db)
    {δ : ℝ≥0 → Ω → ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    {Dd : ℝ} (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
    {M : ℝ≥0 → Ω → ℝ}
    (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
    (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
      (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))
    {X : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (hXcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ X s ω)
    (hXrel : ∀ t : ℝ≥0, X t = fun ω : Ω ↦ c + AdaptedDrift.driftPath β t ω + M t ω)
    {afn bfn : ℝ → ℝ → ℝ}
    (hafnRep : ∀ (s : ℝ) (ω : Ω), driftCoeff μ (reindexed X) (reindexed β) s ω
      = afn s (X (Real.toNNReal s) ω))
    (hbfnRep : ∀ (s : ℝ) (ω : Ω), diffCoeffSq μ (reindexed X) (reindexed δ) s ω
      = bfn s (X (Real.toNNReal s) ω))
    (g g' g'' g''' : ℝ → ℝ)
    (hg1 : ∀ x, HasDerivAt g (g' x) x) (hg2 : ∀ x, HasDerivAt g' (g'' x) x)
    (hg3 : ContDiff ℝ 2 g) (hg4 : ∀ x, HasDerivAt g'' (g''' x) x)
    {C1 C2 C3 : ℝ} (hb1 : ∀ x, |g' x| ≤ C1) (hb2 : ∀ x, |g'' x| ≤ C2)
    (hb3 : ∀ x, |g''' x| ≤ C3)
    {s : ℝ} (hs : s ∈ Set.Ioc (0:ℝ) (T:ℝ)) :
    ∫ ω, g (X (Real.toNNReal s) ω) ∂μ = ∫ ω, g (X (0:ℝ≥0) ω) ∂μ
      + ∫ x in (0)..s, ((∫ ω, g' (X (Real.toNNReal x) ω) * afn x (X (Real.toNNReal x) ω) ∂μ)
        + 1 / 2 * (∫ ω, g'' (X (Real.toNNReal x) ω) * bfn x (X (Real.toNNReal x) ω) ∂μ)) := by
  have htr : ∀ x : ℝ, constructedGenIntegrandExp μ X β δ g' g'' x
      = (∫ ω, g' (X (Real.toNNReal x) ω) * afn x (X (Real.toNNReal x) ω) ∂μ)
        + 1 / 2 * (∫ ω, g'' (X (Real.toNNReal x) ω) * bfn x (X (Real.toNNReal x) ω) ∂μ) :=
    fun x => constructedGenIntegrandExp_fn hBmeas hβadap hβcont hβbdd hδadap hδcont hδbdd
      hMadap c hXcont hXrel hafnRep hbfnRep hg1 hg2 hg3 hb1 hb2 x
  rcases lt_or_eq_of_le hs.2 with hlt | heq
  · -- open band: the band identity plus integrand transport
    have hband := hitoid_constructed_band hB hBmeas hβadap hβcont hβbdd hδadap hδcont hδbdd
      hMadap hMeq c hXcont hXrel hg1 hg2 hg4 hb1 hb2 hb3 ⟨hs.1, hlt⟩
    have hI : (∫ x in (0)..s, constructedGenIntegrandExp μ X β δ g' g'' x)
        = (∫ x in (0)..s, ((∫ ω, g' (X (Real.toNNReal x) ω)
            * afn x (X (Real.toNNReal x) ω) ∂μ)
          + 1 / 2 * (∫ ω, g'' (X (Real.toNNReal x) ω)
            * bfn x (X (Real.toNNReal x) ω) ∂μ))) :=
      intervalIntegral.integral_congr fun x _ => htr x
    rw [hband, hI]
  · -- the horizon: the terminal identity plus the same transport
    subst heq
    rw [Real.toNNReal_coe]
    have hterm := hitoid_constructed_terminal hB hBmeas hβadap hβcont hβbdd hδadap hδcont
      hδbdd hMadap hMeq c hXcont hXrel hg1 hg2 hg4 hb1 hb2 hb3
    have hI : (∫ x in (0)..(T:ℝ), constructedGenIntegrandExp μ X β δ g' g'' x)
        = (∫ x in (0)..(T:ℝ), ((∫ ω, g' (X (Real.toNNReal x) ω)
            * afn x (X (Real.toNNReal x) ω) ∂μ)
          + 1 / 2 * (∫ ω, g'' (X (Real.toNNReal x) ω)
            * bfn x (X (Real.toNNReal x) ω) ∂μ))) :=
      intervalIntegral.integral_congr fun x _ => htr x
    rw [hterm, hI]

/-! ### Mimicry under a flow-uniqueness hypothesis (the Thm 9.6 conclusion)

The mimicking process `Y` is given on its own probability space (`ν`), *not* constructed
(weak existence for merely-measurable coefficients is not proved); its dynamics enter as the
integrated forward identity `hyflow`, which suffices because the conclusion is
distributional. Uniqueness of measure-flow solutions of the deterministic-coefficient weak
forward equation is the explicit hypothesis `hgate`.

After `marginal_flow_weak_equation_fn_constructed` the forward equation's right-hand side
depends on the process only through its current one-time marginal, so the law flows
`s ↦ ν.map (Y s)` and `s ↦ μ.map (X_{s⁺})` both solve the *same* measure-level equation from
the same initial law, and `hgate` turns the two solutions into equal one-time marginals. -/

/-- **Thm 9.6's one-time-marginal mimicry, under a flow-uniqueness hypothesis.** Given

* (i) the constructed `X` of `marginal_flow_weak_equation_fn_constructed` with coefficient
  functions `afn = â`, `bfn = b̂²` (Borel, representing the Gyöngy coefficients pointwise);
* (ii) `hyflow` — the Y-side integrated forward identity for the test class: for every
  `C²` test function with bounded first, second and third derivatives (the third
  derivative is what the X-side identities require), `∫ f(Y_s) = ∫ f(Y_0) +
  ∫_{(0,s]} (𝔼[f'(Y_x)·â(x, Y_x)] + ½ 𝔼[f''(Y_x)·b̂²(x, Y_x)]) dx` on `s ∈ (0, ↑T]` — the
  expectation characterization of `dY = â(t,Y) dt + b(t,Y) dW`;
* (iii) `hY0law` — `Y_0` has the same law as `X_0` (`HasLaw` form);
* (iv) `hgate` — flow uniqueness: two probability-measure flows solving the weak forward
  equation of `GyongyMimicry.marginal_flow_weak_equation_fn_constructed` (integrated form,
  every test function of the class) from the same initial law coincide;

then at every `t ∈ (0, ↑T]` and every `C²` test `f`, `∫ f(Y_t) ∂ν = ∫ f(X_{t⁺}) ∂μ` — the
one-time marginals of `Y` mimic those of the constructed `X`.

No nondegeneracy of `δ` is assumed. Without it (Gyöngy's theorem needs `δ² ≥ λ > 0`) the
forward equation with the merely measurable coefficients `â, b̂²` can have several
measure-flow solutions from the same initial law, and then `hgate` is false.

The conclusion is *measure-level* (`ρ s = η s`), so of the test-function data only
`h2 : ContDiff ℝ 2 f` (through the measurability of `f` in the `integral_map` transports) is
used for `f`. -/
theorem gyongy_mimicry_gated
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    {T : ℝ≥0} {β : ℝ≥0 → Ω → ℝ}
    (hβadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (β t))
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db)
    {δ : ℝ≥0 → Ω → ℝ}
    (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
    (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
    {Dd : ℝ} (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
    {M : ℝ≥0 → Ω → ℝ}
    (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
    (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
      (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))
    {X : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (hXcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ X s ω)
    (hXrel : ∀ t : ℝ≥0, X t = fun ω : Ω ↦ c + AdaptedDrift.driftPath β t ω + M t ω)
    {Ω' : Type*} [mΩ' : MeasurableSpace Ω'] {ν : Measure Ω'} [IsProbabilityMeasure ν]
    (Y : ℝ → Ω' → ℝ) (hYmeas : ∀ s, Measurable (Y s))
    {afn bfn : ℝ → ℝ → ℝ}
    (hafn : ∀ s, Measurable (afn s)) (hbfn : ∀ s, Measurable (bfn s))
    (hafnRep : ∀ (s : ℝ) (ω : Ω), driftCoeff μ (reindexed X) (reindexed β) s ω
      = afn s (X (Real.toNNReal s) ω))
    (hbfnRep : ∀ (s : ℝ) (ω : Ω), diffCoeffSq μ (reindexed X) (reindexed δ) s ω
      = bfn s (X (Real.toNNReal s) ω))
    (hY0law : HasLaw (Y 0) (μ.map fun ω => X 0 ω) ν)
    (hyflow : ∀ (f f' f'' f''' : ℝ → ℝ) (C1 C2 C3 : ℝ),
      (∀ x, HasDerivAt f (f' x) x) → (∀ x, HasDerivAt f' (f'' x) x) → ContDiff ℝ 2 f →
      (∀ x, HasDerivAt f'' (f''' x) x) →
      (∀ x, |f' x| ≤ C1) → (∀ x, |f'' x| ≤ C2) → (∀ x, |f''' x| ≤ C3) →
      ∀ s ∈ Set.Ioc (0:ℝ) (T:ℝ),
      ∫ ω, f (Y s ω) ∂ν = ∫ ω, f (Y 0 ω) ∂ν
        + ∫ x in (0)..s, ((∫ ω, f' (Y x ω) * afn x (Y x ω) ∂ν)
          + 1 / 2 * (∫ ω, f'' (Y x ω) * bfn x (Y x ω) ∂ν)))
    (hgate : ∀ (ρ η : ℝ → Measure ℝ),
      (∀ s, IsProbabilityMeasure (ρ s)) → (∀ s, IsProbabilityMeasure (η s)) →
      (∀ (g g' g'' g''' : ℝ → ℝ) (C1 C2 C3 : ℝ),
        (∀ x, HasDerivAt g (g' x) x) → (∀ x, HasDerivAt g' (g'' x) x) → ContDiff ℝ 2 g →
        (∀ x, HasDerivAt g'' (g''' x) x) →
        (∀ x, |g' x| ≤ C1) → (∀ x, |g'' x| ≤ C2) → (∀ x, |g''' x| ≤ C3) →
        ∀ s ∈ Set.Ioc (0:ℝ) (T:ℝ),
        ∫ y, g y ∂(ρ s) = ∫ y, g y ∂(ρ 0)
          + ∫ x in (0)..s, ((∫ y, g' y * afn x y ∂(ρ x))
            + 1 / 2 * (∫ y, g'' y * bfn x y ∂(ρ x)))) →
      (∀ (g g' g'' g''' : ℝ → ℝ) (C1 C2 C3 : ℝ),
        (∀ x, HasDerivAt g (g' x) x) → (∀ x, HasDerivAt g' (g'' x) x) → ContDiff ℝ 2 g →
        (∀ x, HasDerivAt g'' (g''' x) x) →
        (∀ x, |g' x| ≤ C1) → (∀ x, |g'' x| ≤ C2) → (∀ x, |g''' x| ≤ C3) →
        ∀ s ∈ Set.Ioc (0:ℝ) (T:ℝ),
        ∫ y, g y ∂(η s) = ∫ y, g y ∂(η 0)
          + ∫ x in (0)..s, ((∫ y, g' y * afn x y ∂(η x))
            + 1 / 2 * (∫ y, g'' y * bfn x y ∂(η x)))) →
      ρ 0 = η 0 →
      ∀ s ∈ Set.Ioc (0:ℝ) (T:ℝ), ρ s = η s)
    {f : ℝ → ℝ} (h2 : ContDiff ℝ 2 f)
    (t : ℝ) (ht : 0 < t) (htT : t ≤ (T:ℝ)) :
    ∫ ω, f (Y t ω) ∂ν = ∫ ω, f (X (Real.toNNReal t) ω) ∂μ := by
  -- the X-side state maps are measurable (a field of the constructed instance)
  have hXm : ∀ s : ℝ, Measurable fun ω => X (Real.toNNReal s) ω := fun s =>
    (constructedCoeffData hBmeas hβadap hβcont hβbdd hδadap hδcont hδbdd hMadap c
      hXcont hXrel).hXmeas s
  have hfmeas : Measurable f := h2.continuous.measurable
  -- the Y-side law flow solves the weak forward equation (map form), from `hyflow`
  have hρflow : ∀ (g g' g'' g''' : ℝ → ℝ) (C1 C2 C3 : ℝ),
      (∀ x, HasDerivAt g (g' x) x) → (∀ x, HasDerivAt g' (g'' x) x) → ContDiff ℝ 2 g →
      (∀ x, HasDerivAt g'' (g''' x) x) →
      (∀ x, |g' x| ≤ C1) → (∀ x, |g'' x| ≤ C2) → (∀ x, |g''' x| ≤ C3) →
      ∀ s ∈ Set.Ioc (0:ℝ) (T:ℝ),
      ∫ y, g y ∂(Measure.map (Y s) ν) = ∫ y, g y ∂(Measure.map (Y 0) ν)
        + ∫ x in (0)..s, ((∫ y, g' y * afn x y ∂(Measure.map (Y x) ν))
          + 1 / 2 * (∫ y, g'' y * bfn x y ∂(Measure.map (Y x) ν))) := by
    intro g g' g'' g''' C1 C2 C3 hgd1 hgd2 hgd3 hgd4 hgb1 hgb2 hgb3 s hs
    have hy := hyflow g g' g'' g''' C1 C2 C3 hgd1 hgd2 hgd3 hgd4 hgb1 hgb2 hgb3 s hs
    have hgm : Measurable g := hgd3.continuous.measurable
    have hgd' : Differentiable ℝ g' := fun x => (hgd2 x).differentiableAt
    have hgm' : Measurable g' := hgd'.continuous.measurable
    have hgm'' : Measurable g'' := (continuous_f2_of_contDiff2 hgd3 hgd1 hgd2).measurable
    have t1 : ∫ y, g y ∂(Measure.map (Y s) ν) = ∫ ω, g (Y s ω) ∂ν :=
      integral_map (hYmeas s).aemeasurable hgm.stronglyMeasurable.aestronglyMeasurable
    have t0 : ∫ y, g y ∂(Measure.map (Y 0) ν) = ∫ ω, g (Y 0 ω) ∂ν :=
      integral_map (hYmeas 0).aemeasurable hgm.stronglyMeasurable.aestronglyMeasurable
    have t2 : ∀ x : ℝ, (∫ y, g' y * afn x y ∂(Measure.map (Y x) ν))
        = (∫ ω, g' (Y x ω) * afn x (Y x ω) ∂ν) := fun x =>
      integral_map (hYmeas x).aemeasurable
        ((hgm'.mul (hafn x)).stronglyMeasurable.aestronglyMeasurable)
    have t3 : ∀ x : ℝ, (∫ y, g'' y * bfn x y ∂(Measure.map (Y x) ν))
        = (∫ ω, g'' (Y x ω) * bfn x (Y x ω) ∂ν) := fun x =>
      integral_map (hYmeas x).aemeasurable
        ((hgm''.mul (hbfn x)).stronglyMeasurable.aestronglyMeasurable)
    have hI : (∫ x in (0)..s, ((∫ y, g' y * afn x y ∂(Measure.map (Y x) ν))
          + 1 / 2 * (∫ y, g'' y * bfn x y ∂(Measure.map (Y x) ν))))
        = (∫ x in (0)..s, ((∫ ω, g' (Y x ω) * afn x (Y x ω) ∂ν)
          + 1 / 2 * (∫ ω, g'' (Y x ω) * bfn x (Y x ω) ∂ν))) :=
      intervalIntegral.integral_congr fun x _ => by rw [t2 x, t3 x]
    rw [t1, t0, hI]
    exact hy
  -- the X-side law flow solves the same equation (map form), from the integrated
  -- coefficient-function identity of the constructed process
  have hηflow : ∀ (g g' g'' g''' : ℝ → ℝ) (C1 C2 C3 : ℝ),
      (∀ x, HasDerivAt g (g' x) x) → (∀ x, HasDerivAt g' (g'' x) x) → ContDiff ℝ 2 g →
      (∀ x, HasDerivAt g'' (g''' x) x) →
      (∀ x, |g' x| ≤ C1) → (∀ x, |g'' x| ≤ C2) → (∀ x, |g''' x| ≤ C3) →
      ∀ s ∈ Set.Ioc (0:ℝ) (T:ℝ),
      ∫ y, g y ∂(Measure.map (fun ω => X (Real.toNNReal s) ω) μ)
        = ∫ y, g y ∂(Measure.map (fun ω => X (Real.toNNReal 0) ω) μ)
        + ∫ x in (0)..s, ((∫ y, g' y * afn x y
            ∂(Measure.map (fun ω => X (Real.toNNReal x) ω) μ))
          + 1 / 2 * (∫ y, g'' y * bfn x y
            ∂(Measure.map (fun ω => X (Real.toNNReal x) ω) μ))) := by
    intro g g' g'' g''' C1 C2 C3 hgd1 hgd2 hgd3 hgd4 hgb1 hgb2 hgb3 s hs
    have hx := hitoid_constructed_fn_Ioc hB hBmeas hβadap hβcont hβbdd hδadap hδcont hδbdd
      hMadap hMeq c hXcont hXrel hafnRep hbfnRep g g' g'' g''' hgd1 hgd2 hgd3 hgd4 hgb1 hgb2
      hgb3 hs
    rw [show (0:ℝ≥0) = Real.toNNReal (0:ℝ) from Real.toNNReal_zero.symm] at hx
    have hgm : Measurable g := hgd3.continuous.measurable
    have hgd' : Differentiable ℝ g' := fun x => (hgd2 x).differentiableAt
    have hgm' : Measurable g' := hgd'.continuous.measurable
    have hgm'' : Measurable g'' := (continuous_f2_of_contDiff2 hgd3 hgd1 hgd2).measurable
    have t1 : ∫ y, g y ∂(Measure.map (fun ω => X (Real.toNNReal s) ω) μ)
        = ∫ ω, g (X (Real.toNNReal s) ω) ∂μ :=
      integral_map (hXm s).aemeasurable hgm.stronglyMeasurable.aestronglyMeasurable
    have t0 : ∫ y, g y ∂(Measure.map (fun ω => X (Real.toNNReal 0) ω) μ)
        = ∫ ω, g (X (Real.toNNReal 0) ω) ∂μ :=
      integral_map (hXm 0).aemeasurable hgm.stronglyMeasurable.aestronglyMeasurable
    have t2 : ∀ x : ℝ, (∫ y, g' y * afn x y
          ∂(Measure.map (fun ω => X (Real.toNNReal x) ω) μ))
        = (∫ ω, g' (X (Real.toNNReal x) ω) * afn x (X (Real.toNNReal x) ω) ∂μ) := fun x =>
      integral_map (hXm x).aemeasurable
        ((hgm'.mul (hafn x)).stronglyMeasurable.aestronglyMeasurable)
    have t3 : ∀ x : ℝ, (∫ y, g'' y * bfn x y
          ∂(Measure.map (fun ω => X (Real.toNNReal x) ω) μ))
        = (∫ ω, g'' (X (Real.toNNReal x) ω) * bfn x (X (Real.toNNReal x) ω) ∂μ) := fun x =>
      integral_map (hXm x).aemeasurable
        ((hgm''.mul (hbfn x)).stronglyMeasurable.aestronglyMeasurable)
    have hI : (∫ x in (0)..s, ((∫ y, g' y * afn x y
            ∂(Measure.map (fun ω => X (Real.toNNReal x) ω) μ))
          + 1 / 2 * (∫ y, g'' y * bfn x y
            ∂(Measure.map (fun ω => X (Real.toNNReal x) ω) μ))))
        = (∫ x in (0)..s, ((∫ ω, g' (X (Real.toNNReal x) ω)
            * afn x (X (Real.toNNReal x) ω) ∂μ)
          + 1 / 2 * (∫ ω, g'' (X (Real.toNNReal x) ω)
            * bfn x (X (Real.toNNReal x) ω) ∂μ))) :=
      intervalIntegral.integral_congr fun x _ => by rw [t2 x, t3 x]
    rw [t1, t0, hI]
    exact hx
  -- both law flows are probability flows
  have hρprob : ∀ s, IsProbabilityMeasure (Measure.map (Y s) ν) := fun s =>
    ν.isProbabilityMeasure_map (hYmeas s).aemeasurable
  have hηprob : ∀ s, IsProbabilityMeasure (Measure.map (fun ω => X (Real.toNNReal s) ω) μ) :=
    fun s => μ.isProbabilityMeasure_map (hXm s).aemeasurable
  -- the initial laws agree (`Y₀` has the law of `X₀`)
  have hz : (fun ω => X (Real.toNNReal (0:ℝ)) ω) = (X 0) := by
    funext ω
    rw [Real.toNNReal_zero]
  have h0 : Measure.map (Y 0) ν = Measure.map (fun ω => X (Real.toNNReal 0) ω) μ := by
    rw [hz]
    exact hY0law.map_eq
  -- flow uniqueness: two flows solving the same equation from the same initial law coincide
  have hfin := hgate (fun s => Measure.map (Y s) ν)
    (fun s => Measure.map (fun ω => X (Real.toNNReal s) ω) μ) hρprob hηprob hρflow hηflow h0
    t ⟨ht, htT⟩
  -- read the measure equality through `integral_map`
  calc ∫ ω, f (Y t ω) ∂ν = ∫ y, f y ∂(Measure.map (Y t) ν) :=
        (integral_map (hYmeas t).aemeasurable
          hfmeas.stronglyMeasurable.aestronglyMeasurable).symm
    _ = ∫ y, f y ∂(Measure.map (fun ω => X (Real.toNNReal t) ω) μ) := by rw [hfin]
    _ = ∫ ω, f (X (Real.toNNReal t) ω) ∂μ :=
        integral_map (hXm t).aemeasurable hfmeas.stronglyMeasurable.aestronglyMeasurable


end Fn

end MathFin.GyongyMimicry
