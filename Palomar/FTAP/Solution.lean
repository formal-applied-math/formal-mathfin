/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Pricing.FTAP.OneAssetDMW
public import MathFin.Pricing.FTAP.FTAPComplete

/-!
# Proofs of the discrete-time fundamental theorems, one risky asset

The declarations of `Palomar/FTAP/Challenge.lean` repeated verbatim and proved from the library.
The Challenge's `NoArbitrage`, `IsEMM` and `IsCompleteMarket` are the library's
`MathFin.NoArbitrage`, `MathFin.IsEMM` and `MathFin.IsCompleteMarket` at the asset space `F = ℝ`,
written without the library's vocabulary: the gain is `MathFin.martingaleTransform`
(`MathFin.martingaleTransform_real`), the norm on `ℝ` is the absolute value, and an equivalent
martingale measure carries the same four fields. The bridges below say so, and the two theorems are
then

* `MathFin.OneAsset.noArbitrage_iff_exists_isEMM` (`MathFin/Pricing/FTAP/OneAssetDMW.lean`), the
  one-asset Dalang–Morton–Willinger theorem;
* `MathFin.ftap_two` (`MathFin/Pricing/FTAP/FTAPComplete.lean`), the second fundamental theorem on
  a finite space.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace DiscreteFTAP

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The **gain** up to date `n` of the strategy `φ` trading the price `S`:
`∑_{k < n} φ (k + 1) ω * (S (k + 1) ω - S k ω)`. The holding `φ (k + 1)` is carried over the
period `(k, k + 1]`. -/
noncomputable def gains (φ S : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, φ (k + 1) ω * (S (k + 1) ω - S k ω)

/-- **No arbitrage** up to the horizon `T`: every predictable (`φ (t + 1)` is `𝓕 t`-measurable
for `t < T`) and bounded strategy whose gain at `T` is `P`-almost surely nonnegative has gain
`P`-almost surely zero. -/
def NoArbitrage (𝓕 : Filtration ℕ m0) (P : Measure Ω) (S : ℕ → Ω → ℝ) (T : ℕ) : Prop :=
  ∀ φ : ℕ → Ω → ℝ, (∀ t < T, StronglyMeasurable[𝓕 t] (φ (t + 1))) →
    (∃ K : ℝ, ∀ n ≤ T, ∀ ω, |φ n ω| ≤ K) →
    0 ≤ᵐ[P] gains φ S T → gains φ S T =ᵐ[P] 0

/-- `Q` is an **equivalent martingale measure** for the price `S` up to the horizon `T`: a
probability measure with the same null sets as `P` under which the price stopped at the horizon,
`t ↦ S (min t T)`, is a martingale for `𝓕`. -/
structure IsEMM (𝓕 : Filtration ℕ m0) (P : Measure Ω) (S : ℕ → Ω → ℝ) (T : ℕ)
    (Q : Measure Ω) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure Q
  absolutelyContinuous : Q ≪ P
  absolutelyContinuous' : P ≪ Q
  martingale : Martingale (fun t ↦ S (min t T)) 𝓕 Q

/-- The market is **complete** up to the horizon `T`: every bounded `𝓕 T`-measurable claim `H`
is, `P`-almost surely, the terminal wealth `x + gains φ S T` of some initial capital `x` and some
predictable bounded strategy `φ`. -/
def IsCompleteMarket (𝓕 : Filtration ℕ m0) (P : Measure Ω) (S : ℕ → Ω → ℝ) (T : ℕ) : Prop :=
  ∀ H : Ω → ℝ, StronglyMeasurable[𝓕 T] H → (∃ C : ℝ, ∀ ω, |H ω| ≤ C) →
    ∃ (x : ℝ) (φ : ℕ → Ω → ℝ), (∀ t < T, StronglyMeasurable[𝓕 t] (φ (t + 1))) ∧
      (∃ K : ℝ, ∀ n ≤ T, ∀ ω, |φ n ω| ≤ K) ∧ H =ᵐ[P] fun ω ↦ x + gains φ S T ω

variable {𝓕 : Filtration ℕ m0} {P : Measure Ω} {S : ℕ → Ω → ℝ} {T : ℕ}

theorem gains_eq_martingaleTransform (φ S : ℕ → Ω → ℝ) (n : ℕ) :
    gains φ S n = MathFin.martingaleTransform φ S n :=
  funext fun ω ↦ (MathFin.martingaleTransform_real φ S n ω).symm

theorem noArbitrage_iff_mathFin : NoArbitrage 𝓕 P S T ↔ MathFin.NoArbitrage 𝓕 P S T := by
  simp only [NoArbitrage, MathFin.NoArbitrage, gains_eq_martingaleTransform, Real.norm_eq_abs]

theorem isEMM_iff_mathFin {Q : Measure Ω} : IsEMM 𝓕 P S T Q ↔ MathFin.IsEMM 𝓕 P S T Q :=
  ⟨fun h ↦ ⟨⟨h.isProbabilityMeasure, h.absolutelyContinuous, h.absolutelyContinuous'⟩,
    h.martingale⟩, fun h ↦ ⟨h.isProb, h.ac, h.ac', h.martingale⟩⟩

theorem isCompleteMarket_iff_mathFin :
    IsCompleteMarket 𝓕 P S T ↔ MathFin.IsCompleteMarket 𝓕 P S T := by
  simp only [IsCompleteMarket, MathFin.IsCompleteMarket, gains_eq_martingaleTransform,
    Real.norm_eq_abs]

theorem noArbitrage_iff_exists_isEMM [IsProbabilityMeasure P]
    (hS : ∀ t ≤ T, StronglyMeasurable[𝓕 t] (S t)) :
    NoArbitrage 𝓕 P S T ↔ ∃ Q, IsEMM 𝓕 P S T Q := by
  simpa only [noArbitrage_iff_mathFin, isEMM_iff_mathFin] using
    MathFin.OneAsset.noArbitrage_iff_exists_isEMM hS

theorem isCompleteMarket_iff_existsUnique_isEMM [Finite Ω] [Nonempty Ω]
    [MeasurableSingletonClass Ω] (hS : StronglyAdapted 𝓕 S) (hP : ∀ ω, 0 < P {ω})
    (hT : 𝓕 T = m0) (hNA : NoArbitrage 𝓕 P S T) :
    IsCompleteMarket 𝓕 P S T ↔ ∃! Q, IsEMM 𝓕 P S T Q := by
  have := Fintype.ofFinite Ω
  simpa only [isCompleteMarket_iff_mathFin, isEMM_iff_mathFin] using
    MathFin.ftap_two 𝓕 P S T hS hP hT (noArbitrage_iff_mathFin.1 hNA)

end DiscreteFTAP
