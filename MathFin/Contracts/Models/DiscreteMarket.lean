/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Contracts.Parity
public import MathFin.Foundations.DalangMortonWillinger

/-!
# The contracts priced in a discrete-time market with an equivalent martingale measure

The third model for the instruments of `Contracts/Instruments/Options.lean`, after the
Black–Scholes and binomial ones, and the seam between the contracts layer and the multi-period
FTAP. A one-asset discrete-time market on a general filtered probability space, a price
`S : ℕ → Ω → ℝ` with an equivalent martingale measure `IsEMM 𝓕 P S T Q`, is a contract model
map: between integer dates the underlying is constant, `discreteAssets S T () t = S ⌊t⌋₊` frozen
at the horizon `T` (the price is a `Q`-martingale only up to `T`). The price `S` is quoted in
units of the numeraire, so cash is not discounted, `D ≡ 1`.

The filtration of the model is `floorFiltration 𝓕`, `t ↦ 𝓕 ⌊t⌋₊`, and the frozen price is a
martingale for it (`martingale_floor`). The risk-neutral lemmas of `Contracts/Parity.lean` then
apply as they stand: the forward is worth `S₀ − K` and call minus put is `S₀ − K` at every
maturity (`value_forward`, `value_europeanCall_sub_put`); at an integer maturity `n` the
underlying is `S (min n T)` (`discreteAssets_natCast`). Parity is not re-proved here.

The composite `exists_isEMM_parity` closes the loop with the Dalang–Morton–Willinger reduction:
**assuming `ConditionalOnePeriodFTAP`** (the conditional one-period FTAP, not proved in this
library), an arbitrage-free adapted integrable market has an equivalent martingale measure `Q`
under which the forward is worth `S₀ − K` and the contracts satisfy parity.

## Main definitions

* `floorFiltration`: the continuous-time filtration `t ↦ 𝓕 ⌊t⌋₊` of a discrete one.
* `discreteAssets`: the discrete market as a contract model map, frozen at the horizon.

## Main results

* `martingale_floor`: a discrete martingale is a martingale for `floorFiltration`.
* `value_forward`, `value_europeanCall_sub_put`: forward value and put–call parity under an `IsEMM`.
* `exists_isEMM_parity`: no arbitrage gives a measure under which parity holds, given
  `ConditionalOnePeriodFTAP`.

## References

* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete Time*][FollmerSchied],
  §5.2

## Tags

discrete-time market, equivalent martingale measure, put–call parity, forward price,
contract model, Dalang–Morton–Willinger, MSC 91G20, JEL G13
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MathFin.Contracts.DiscreteMarket

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The continuous-time filtration `t ↦ 𝓕 ⌊t⌋₊` of a discrete-time one. -/
noncomputable def floorFiltration (𝓕 : Filtration ℕ mΩ) : Filtration ℝ≥0 mΩ where
  seq t := 𝓕 ⌊t⌋₊
  mono' _ _ hst := 𝓕.mono (Nat.floor_mono hst)
  le' t := 𝓕.le _

/-- A discrete-time price as a contract model map: constant between integer dates and frozen at
the horizon `T`. -/
noncomputable def discreteAssets (S : ℕ → Ω → ℝ) (T : ℕ) : Unit → ℝ≥0 → Ω → ℝ :=
  fun _ t ω ↦ S (min ⌊t⌋₊ T) ω

/-- At an integer date `n` the underlying is the price at `min n T`. -/
theorem discreteAssets_natCast (S : ℕ → Ω → ℝ) (T n : ℕ) (ω : Ω) :
    discreteAssets S T () (n : ℝ≥0) ω = S (min n T) ω := by
  simp [discreteAssets]

/-- **A discrete martingale is a martingale for the floor filtration**, along `t ↦ ⌊t⌋₊`. -/
theorem martingale_floor {𝓕 : Filtration ℕ mΩ} {Q : Measure Ω} {f : ℕ → Ω → ℝ}
    (hM : Martingale f 𝓕 Q) :
    Martingale (fun t ω ↦ f ⌊t⌋₊ ω) (floorFiltration 𝓕) Q :=
  ⟨fun t ↦ hM.1 ⌊t⌋₊, fun _ _ hst ↦ hM.2 _ _ (Nat.floor_mono hst)⟩

variable {𝓕 : Filtration ℕ mΩ} {P Q : Measure Ω} {S : ℕ → Ω → ℝ} {T : ℕ} {S₀ : ℝ}

/-- Under an equivalent martingale measure the model's (undiscounted) price is a martingale for
the floor filtration. -/
theorem martingale_discreteAssets (hQ : IsEMM 𝓕 P S T Q) :
    Martingale (fun t ω ↦ (fun _ : ℝ≥0 ↦ (1 : ℝ)) t * discreteAssets S T () t ω)
      (floorFiltration 𝓕) Q := by
  simpa only [one_mul, discreteAssets] using martingale_floor hQ.martingale

/-- **The forward's value under an equivalent martingale measure**: the forward struck at `K`, at
any maturity, is worth `S₀ - K` (the price is in numeraire units, `D ≡ 1`), for a price starting
at `S₀`. This is `value_forward_of_martingale`. -/
theorem value_forward (hQ : IsEMM 𝓕 P S T Q) (hS₀ : ∀ ω, S 0 ω = S₀) (K : ℝ) (τ : ℝ≥0) :
    (forward K τ).value Q (fun _ ↦ 1) (discreteAssets S T) = S₀ - K := by
  haveI := hQ.isProb
  have := value_forward_of_martingale (K := K) (T := τ) (𝓕 := floorFiltration 𝓕)
    (martingale_discreteAssets hQ) rfl
    (fun ω ↦ by
      show S (min ⌊(0 : ℝ≥0)⌋₊ T) ω = S₀
      rw [Nat.floor_zero, Nat.zero_min]
      exact hS₀ ω)
  simpa using this

/-- **Put–call parity under an equivalent martingale measure**: at any maturity, call minus put
is `S₀ - K`. This is `value_europeanCall_sub_put_of_martingale`. -/
theorem value_europeanCall_sub_put (hQ : IsEMM 𝓕 P S T Q) (hS₀ : ∀ ω, S 0 ω = S₀) (K : ℝ)
    (τ : ℝ≥0) :
    (europeanCall K τ).value Q (fun _ ↦ 1) (discreteAssets S T)
      - (europeanPut K τ).value Q (fun _ ↦ 1) (discreteAssets S T) = S₀ - K := by
  haveI := hQ.isProb
  have := value_europeanCall_sub_put_of_martingale (K := K) (T := τ) (𝓕 := floorFiltration 𝓕)
    (martingale_discreteAssets hQ) rfl
    (fun ω ↦ by
      show S (min ⌊(0 : ℝ≥0)⌋₊ T) ω = S₀
      rw [Nat.floor_zero, Nat.zero_min]
      exact hS₀ ω)
  simpa using this

/-- **No arbitrage gives a measure under which the contracts satisfy parity**, assuming the
conditional one-period FTAP. For an adapted integrable one-asset price with
`ConditionalOnePeriodFTAP` (an hypothesis, **not proved** in this library: see
`DalangMortonWillinger.lean`), no arbitrage yields an equivalent martingale measure `Q`, and under
it the forward is worth `S₀ - K` and call minus put equals `S₀ - K` at every maturity. -/
theorem exists_isEMM_parity [IsProbabilityMeasure P]
    (hS : ∀ t ≤ T, StronglyMeasurable[𝓕 t] (S t)) (hint : ∀ t ≤ T, Integrable (S t) P)
    (hcond : ConditionalOnePeriodFTAP 𝓕 P S T) (hNA : NoArbitrage 𝓕 P S T)
    (hS₀ : ∀ ω, S 0 ω = S₀) (K : ℝ) (τ : ℝ≥0) :
    ∃ Q, IsEMM 𝓕 P S T Q ∧
      (forward K τ).value Q (fun _ ↦ 1) (discreteAssets S T) = S₀ - K ∧
      (europeanCall K τ).value Q (fun _ ↦ 1) (discreteAssets S T)
        - (europeanPut K τ).value Q (fun _ ↦ 1) (discreteAssets S T) = S₀ - K := by
  obtain ⟨Q, hQ⟩ := exists_isEMM_of_noArbitrage hS hint hcond hNA
  exact ⟨Q, hQ, value_forward hQ hS₀ K τ, value_europeanCall_sub_put hQ hS₀ K τ⟩

end MathFin.Contracts.DiscreteMarket
