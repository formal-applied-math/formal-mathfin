/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.BlackScholes.MertonJumpDiffusion

-- pointers: MathFin/BlackScholes/MertonJumpDiffusion.lean
-- main-module: MathFin/BlackScholes/MertonJumpDiffusionDelta.lean
-- benchmark: benchmarks/mathematical_finance.json
-- benchmark-id: mf-merton-jd-delta
-- source-issue: 129
-- deferred: gamma mixture: the analogous second S-derivative (Poisson-weighted BS gammas) of mertonCallPrice; vega mixture: the analogous σ-derivative of mertonCallPrice, requiring the chain rule through mertonVol σ δ T n

/-!
Merton call delta as the Poisson-weighted mixture of chain-ruled Black–Scholes deltas, with the mixture bounded in [0,1].
-/

set_option autoImplicit false

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- **Merton call delta**: `∂_{S₀} mertonCallPrice` is the Poisson-weighted mixture of
chain-ruled conditional Black–Scholes deltas, `∑' n, w(n) · (Sₙ(S₀)/S₀) · Φ(d₁(Sₙ(S₀)))`
(the factor `Sₙ(S₀)/S₀` being `deriv (fun S ↦ mertonSpot S k Λ n) S₀`), and this mixture
delta is itself a probability, i.e. lies in `[0, 1]`. -/
theorem mertonCallPrice_hasDerivAt {S_0 K r σ T k : ℝ} (δ : ℝ) (Λ : ℝ≥0)
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (hk : -1 < k) :
    HasDerivAt (fun S ↦ mertonCallPrice S K r σ T k δ Λ)
        (∑' n : ℕ, Real.exp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / (n.factorial : ℝ)
          * (mertonSpot S_0 k Λ n / S_0)
          * deriv (fun S ↦ bsV K r (mertonVol σ δ T n) S T) (mertonSpot S_0 k Λ n)) S_0
      ∧ (∑' n : ℕ, Real.exp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / (n.factorial : ℝ)
          * (mertonSpot S_0 k Λ n / S_0)
          * deriv (fun S ↦ bsV K r (mertonVol σ δ T n) S T) (mertonSpot S_0 k Λ n))
        ∈ Set.Icc (0 : ℝ) 1 := by
  -- Closed form for the chain-ruled delta: `deriv (bsV at spot_n) = Φ(d₁ⁿ)`.
  have hdelta (n : ℕ) :
      deriv (fun S ↦ bsV K r (mertonVol σ δ T n) S T) (mertonSpot S_0 k Λ n)
        = Phi (bsd1 (mertonSpot S_0 k Λ n) K r (mertonVol σ δ T n) T) :=
    (hasDerivAt_bsV_S hK (mertonVol_pos hσ hT n) (mertonSpot_pos hS_0 hk Λ n) hT).deriv
  simp_rw [hdelta]
  -- `mertonSpot` is linear (through the origin) in its first argument, at any base point.
  have hspot_deriv (x : ℝ) (n : ℕ) :
      HasDerivAt (fun y : ℝ ↦ mertonSpot y k Λ n) (mertonSpot S_0 k Λ n / S_0) x := by
    have hval : mertonSpot S_0 k Λ n / S_0
        = 1 * Real.exp (-(k * (Λ : ℝ))) * (1 + k) ^ n := by
      unfold mertonSpot
      field_simp
    rw [hval]
    exact ((hasDerivAt_id x).mul_const (Real.exp (-(k * (Λ : ℝ))))).mul_const ((1 + k) ^ n)
  -- Chain rule at any positive `x`: `mertonCallTerm` is `bsV` precomposed with the linear
  -- spot map, so its derivative is delta times the constant slope.
  have hterm_deriv (x : ℝ) (hx : 0 < x) (n : ℕ) :
      HasDerivAt (fun y : ℝ ↦ mertonCallTerm y K r σ T k δ Λ n)
        ((mertonSpot S_0 k Λ n / S_0)
          * Phi (bsd1 (mertonSpot x k Λ n) K r (mertonVol σ δ T n) T)) x := by
    have heq : (fun y : ℝ ↦ mertonCallTerm y K r σ T k δ Λ n)
        = fun y : ℝ ↦ bsV K r (mertonVol σ δ T n) (mertonSpot y k Λ n) T :=
      funext fun y ↦ mertonCallTerm_eq_bsV y K r σ T k δ Λ n
    rw [heq, mul_comm (mertonSpot S_0 k Λ n / S_0)
      (Phi (bsd1 (mertonSpot x k Λ n) K r (mertonVol σ δ T n) T))]
    exact (hasDerivAt_bsV_S hK (mertonVol_pos hσ hT n) (mertonSpot_pos hx hk Λ n) hT).comp x
      (hspot_deriv x n)
  -- A uniform Lipschitz bound on `(0, ∞)`, by the mean value inequality with the constant
  -- slope `mertonSpot S_0 k Λ n / S_0` (delta is itself bounded by `1`).
  have hlip (n : ℕ) :
      LipschitzOnWith (Real.nnabs (mertonSpot S_0 k Λ n / S_0))
        (fun y : ℝ ↦ mertonCallTerm y K r σ T k δ Λ n) (Set.Ioi (0 : ℝ)) := by
    refine Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_Ioi 0)
      (fun x hx ↦ (hterm_deriv x hx n).hasDerivWithinAt) (fun x hx ↦ ?_)
    have hΦ0 := Phi_nonneg (bsd1 (mertonSpot x k Λ n) K r (mertonVol σ δ T n) T)
    have hΦ1 := Phi_le_one (bsd1 (mertonSpot x k Λ n) K r (mertonVol σ δ T n) T)
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs, Real.norm_eq_abs,
      abs_mul, abs_of_nonneg (div_nonneg (mertonSpot_pos hS_0 hk Λ n).le hS_0.le),
      abs_of_nonneg hΦ0]
    exact mul_le_of_le_one_right (div_nonneg (mertonSpot_pos hS_0 hk Λ n).le hS_0.le) hΦ1
  have hbound_integrable :
      Integrable (fun n : ℕ ↦ mertonSpot S_0 k Λ n / S_0) (poissonMeasure Λ) :=
    (integrable_mertonSpot Λ hS_0 hk).div_const S_0
  -- Differentiate under the (Poisson-mixture) integral sign.
  have key := hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := poissonMeasure Λ)
    (F := fun x n ↦ mertonCallTerm x K r σ T k δ Λ n)
    (x₀ := S_0) (s := Set.Ioi (0 : ℝ))
    (bound := fun n ↦ mertonSpot S_0 k Λ n / S_0)
    (F' := fun n ↦ (mertonSpot S_0 k Λ n / S_0)
      * Phi (bsd1 (mertonSpot S_0 k Λ n) K r (mertonVol σ δ T n) T))
    (isOpen_Ioi.mem_nhds hS_0)
    (Filter.Eventually.of_forall fun _ ↦ Measurable.of_discrete.aestronglyMeasurable)
    (integrable_mertonCallTerm δ Λ hS_0 hK hσ hT hk)
    Measurable.of_discrete.aestronglyMeasurable
    (ae_of_all _ hlip)
    hbound_integrable
    (ae_of_all _ fun n ↦ hterm_deriv S_0 hS_0 n)
  have hderiv' : HasDerivAt (fun S ↦ mertonCallPrice S K r σ T k δ Λ)
      (∑' n : ℕ, Real.exp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / (n.factorial : ℝ)
        * (mertonSpot S_0 k Λ n / S_0)
        * Phi (bsd1 (mertonSpot S_0 k Λ n) K r (mertonVol σ δ T n) T)) S_0 := by
    have hFtsum : ∑' n : ℕ, Real.exp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / (n.factorial : ℝ)
          * (mertonSpot S_0 k Λ n / S_0)
          * Phi (bsd1 (mertonSpot S_0 k Λ n) K r (mertonVol σ δ T n) T)
        = ∫ n, ((mertonSpot S_0 k Λ n / S_0)
            * Phi (bsd1 (mertonSpot S_0 k Λ n) K r (mertonVol σ δ T n) T)) ∂(poissonMeasure Λ) := by
      rw [integral_poissonMeasure]
      simp_rw [smul_eq_mul, mul_assoc]
    rw [hFtsum]
    exact key.2
  -- The mixture lies in `[0, 1]`: it is a Poisson-weighted average of `Φ`-values (each in
  -- `[0, 1]`) with weights `w(n) · (spot_n/S₀)` summing to `1` (spot recombination).
  have hw_nonneg (n : ℕ) : 0 ≤ Real.exp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / (n.factorial : ℝ) := by
    positivity
  have hc_nonneg (n : ℕ) : 0 ≤ mertonSpot S_0 k Λ n / S_0 :=
    div_nonneg (mertonSpot_pos hS_0 hk Λ n).le hS_0.le
  have hterm_nonneg (n : ℕ) :
      0 ≤ Real.exp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / (n.factorial : ℝ) * (mertonSpot S_0 k Λ n / S_0)
          * Phi (bsd1 (mertonSpot S_0 k Λ n) K r (mertonVol σ δ T n) T) :=
    mul_nonneg (mul_nonneg (hw_nonneg n) (hc_nonneg n)) (Phi_nonneg _)
  have hterm_le (n : ℕ) :
      Real.exp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / (n.factorial : ℝ) * (mertonSpot S_0 k Λ n / S_0)
          * Phi (bsd1 (mertonSpot S_0 k Λ n) K r (mertonVol σ δ T n) T)
        ≤ Real.exp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / (n.factorial : ℝ) * (mertonSpot S_0 k Λ n / S_0) := by
    simpa using mul_le_mul_of_nonneg_left
      (Phi_le_one (bsd1 (mertonSpot S_0 k Λ n) K r (mertonVol σ δ T n) T))
      (mul_nonneg (hw_nonneg n) (hc_nonneg n))
  have hc_summable : Summable (fun n : ℕ ↦
      Real.exp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / (n.factorial : ℝ) * (mertonSpot S_0 k Λ n / S_0)) := by
    have h := (summable_weights_mul_mertonSpot S_0 k Λ).div_const S_0
    simpa [mul_div_assoc] using h
  have hspot_tsum :
      ∑' n : ℕ, Real.exp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / (n.factorial : ℝ) * mertonSpot S_0 k Λ n
        = S_0 := by
    have h := integral_mertonSpot S_0 k Λ
    rw [integral_poissonMeasure] at h
    simpa [smul_eq_mul] using h
  have hc_tsum :
      ∑' n : ℕ, Real.exp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / (n.factorial : ℝ)
          * (mertonSpot S_0 k Λ n / S_0)
        = 1 := by
    rw [show (fun n : ℕ ↦ Real.exp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / (n.factorial : ℝ)
          * (mertonSpot S_0 k Λ n / S_0))
        = fun n ↦ (Real.exp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / (n.factorial : ℝ) * mertonSpot S_0 k Λ n)
          / S_0
        from funext fun n ↦ (mul_div_assoc _ _ _).symm,
      tsum_div_const, hspot_tsum, div_self hS_0.ne']
  refine ⟨hderiv', tsum_nonneg (fun n ↦ hterm_nonneg n), ?_⟩
  calc ∑' n : ℕ, Real.exp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / (n.factorial : ℝ)
          * (mertonSpot S_0 k Λ n / S_0)
          * Phi (bsd1 (mertonSpot S_0 k Λ n) K r (mertonVol σ δ T n) T)
      ≤ ∑' n : ℕ, Real.exp (-(Λ : ℝ)) * (Λ : ℝ) ^ n / (n.factorial : ℝ)
          * (mertonSpot S_0 k Λ n / S_0) :=
        Summable.tsum_le_tsum (fun n ↦ hterm_le n)
          (Summable.of_nonneg_of_le (fun n ↦ hterm_nonneg n) (fun n ↦ hterm_le n) hc_summable)
          hc_summable
    _ = 1 := hc_tsum

end MathFin
