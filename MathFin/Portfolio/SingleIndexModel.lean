/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.Portfolio.MarkowitzNAsset

/-!
# Single-index covariance structure and its large-`N` limit

Sharpe's single-index model writes each asset's return as `Rᵢ = βᵢ·R_M + εᵢ`, with idiosyncratic
shocks `εᵢ` uncorrelated across assets and with the market. The implied covariance kernel is
`Σ = ββ'σ_M² + D_ε` (`D_ε` diagonal). We work directly with this kernel and
`Portfolio/MarkowitzNAsset.lean`'s sum-form portfolio variance:

  `Var(Rp) = (w'β)² σ_M² + w'D_εw`,

in which, for a bounded idiosyncratic variance and the equal-weight portfolio, the idiosyncratic
term tends to `0` as `n → ∞` — i.e. idiosyncratic risk diversifies away, leaving only systematic
risk `(β_p σ_M)²`.

## Main definitions and results

* `singleIndexKernel`: `σᵢⱼ = βᵢβⱼσ_M² + (idiosyncratic diagonal)`.
* `portfolioVarN_singleIndex_eq`: `Var(Rp) = (∑ wᵢβᵢ)² σ_M² + ∑ wᵢ² D_ε(i)`.
* `idiosyncraticTerm_equalWeight_le`: for equal weights `1/n` and idiosyncratic variances
  bounded by `M`, the idiosyncratic term is at most `M / n`.
* `tendsto_idiosyncraticTerm_equalWeight_zero`: hence it tends to `0` as `n → ∞`
  (idiosyncratic risk diversifies away under equal weighting).
-/

@[expose] public section

namespace MathFin

open Filter Topology

variable {ι : Type*} (s : Finset ι) (w β : ι → ℝ) (σM : ℝ) (Dε : ι → ℝ)

/-- The single-index covariance kernel `σᵢⱼ = βᵢβⱼσ_M² + 1[i=j]·D_ε(i)`. -/
def singleIndexKernel [DecidableEq ι] (i j : ι) : ℝ :=
  β i * β j * σM ^ 2 + if i = j then Dε i else 0

/-- `portfolioVarN` is additive in the covariance kernel: `Var` of a sum-kernel is the sum of the
`Var`s. Pure linearity of the double `Finset.sum`. -/
lemma portfolioVarN_add_kernel (f g : ι → ι → ℝ) :
    portfolioVarN s w (fun i j ↦ f i j + g i j) = portfolioVarN s w f + portfolioVarN s w g := by
  unfold portfolioVarN
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- The rank-one ("market") kernel's portfolio variance is `σ_M² · (∑ wᵢβᵢ)²`: the double sum over
a rank-one kernel `βᵢβⱼ` factors into the product of two copies of the same single sum. -/
lemma portfolioVarN_rankOne_eq :
    portfolioVarN s w (fun i j ↦ β i * β j * σM ^ 2) = σM ^ 2 * (∑ i ∈ s, w i * β i) ^ 2 := by
  unfold portfolioVarN
  have heq : ∑ i ∈ s, ∑ j ∈ s, w i * w j * (β i * β j * σM ^ 2) =
      (∑ i ∈ s, w i * β i * σM) * ∑ j ∈ s, w j * β j * σM :=
    (Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ show
        w i * w j * (β i * β j * σM ^ 2) = (w i * β i * σM) * (w j * β j * σM) by ring).trans
      (Finset.sum_mul_sum s s (fun i ↦ w i * β i * σM) (fun j ↦ w j * β j * σM)).symm
  have hX : (∑ i ∈ s, w i * β i * σM) = σM * ∑ i ∈ s, w i * β i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [heq, hX]
  ring

/-- **Single-index portfolio variance**: `Var(Rp) = (∑ wᵢβᵢ)² σ_M² + ∑ wᵢ² D_ε(i)`. -/
theorem portfolioVarN_singleIndex_eq [DecidableEq ι] :
    portfolioVarN s w (singleIndexKernel β σM Dε) =
      (∑ i ∈ s, w i * β i) ^ 2 * σM ^ 2 + ∑ i ∈ s, w i ^ 2 * Dε i := by
  unfold singleIndexKernel
  rw [portfolioVarN_add_kernel s w, portfolioVarN_rankOne_eq,
    portfolioVarN_diag s w _ fun i _ j _ hij ↦ if_neg hij]
  simp
  ring

/-- **Idiosyncratic-term bound under equal weighting**: with weights `1/n` on an index set of
cardinality `n` and idiosyncratic variances bounded by `M`, the idiosyncratic term is at most
`M / n`. -/
lemma idiosyncraticTerm_equalWeight_le {n : ℕ} (M : ℝ)
    (hM : ∀ i ∈ s, Dε i ≤ M) (hcard : s.card = n) :
    ∑ i ∈ s, ((1 : ℝ) / n) ^ 2 * Dε i ≤ M / n := by
  have hbound : ∑ i ∈ s, ((1 : ℝ) / n) ^ 2 * Dε i ≤ ∑ _i ∈ s, ((1 : ℝ) / n) ^ 2 * M :=
    Finset.sum_le_sum fun i hi ↦
      mul_le_mul_of_nonneg_left (hM i hi) (sq_nonneg _)
  have heq : ∑ _i ∈ s, ((1 : ℝ) / n) ^ 2 * M = M / n := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    field_simp
  rwa [heq] at hbound

/-- **Diversification**: the idiosyncratic term under equal weighting on an index set of
cardinality `n` tends to `0` as `n → ∞`, for nonnegative idiosyncratic variances uniformly bounded
by `M` — idiosyncratic risk diversifies away, leaving only the systematic term `(β_p σ_M)²`. -/
theorem tendsto_idiosyncraticTerm_equalWeight_zero
    (t : ℕ → Finset ι) (D : ℕ → ι → ℝ) (M : ℝ)
    (hM : ∀ n, ∀ i ∈ t n, D n i ≤ M) (hMnn : ∀ n, ∀ i ∈ t n, 0 ≤ D n i)
    (hcard : ∀ n, (t n).card = n) :
    Tendsto (fun n ↦ ∑ i ∈ t n, ((1 : ℝ) / n) ^ 2 * D n i) atTop (𝓝 0) := by
  have hlo (n : ℕ) : 0 ≤ ∑ i ∈ t n, ((1 : ℝ) / n) ^ 2 * D n i :=
    Finset.sum_nonneg fun i hi ↦ mul_nonneg (sq_nonneg _) (hMnn n i hi)
  have hhi (n : ℕ) : ∑ i ∈ t n, ((1 : ℝ) / n) ^ 2 * D n i ≤ M / n :=
    idiosyncraticTerm_equalWeight_le (t n) (D n) M (hM n) (hcard n)
  exact squeeze_zero hlo hhi (tendsto_const_div_atTop_nhds_zero_nat M)

end MathFin
