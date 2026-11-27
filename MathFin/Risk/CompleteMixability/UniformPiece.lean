/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Risk.CompleteMixability.QuantileGrid
public import MathFin.Risk.CompleteMixability.Average

/-!
# Laws with a uniform piece are completely mixable in many copies

If a law `G` on an interval of length `R` contains `q` times the uniform law on `[c - H, c + H]`,
then `N` copies of `G` and one copy of any law `E` on an interval of length `L` are jointly
mixable once `N ≥ (2(2R + L)/H + 9)/q`. Nothing is assumed about the rest of `G`.

The construction, for `G = q U + (1 - q) T`:

* `K` copies of `T` on the quantile grid (`QuantileGrid.lean`), with `K` one of the two
  integers next to `N(1 - q)` and mean `N(1 - q)`. Their sum misses its mean by at most `R`.
* The error `C` left for the uniform copies is bounded by `2R + L` and has mean zero. Two
  copies `c + Z` and `c + Z'`, with `Z` uniform on `[-H, H)` and `Z' = wrap (d - Z)` for
  `d = C mod 2H`, absorb it up to a multiple `2H J`: a rotation of the circle keeps `Z'`
  uniform whatever `d` is.
* `4|J|` copies of the half-interval uniform `U[c, c + H]` (or `U[c - H, c]` when `J < 0`),
  completely mixed, and the rest of the copies of `U[c - H, c + H]`, completely mixed, absorb
  `2H J` exactly: each half-interval copy moves the sum by `H/2`.
* A uniform random permutation of the positions.

A position's law is the average of the slots' laws. The half-interval copies enter it
affinely in `J`, as `4J (U[c, c + H] - U)` since `U[c - H, c] = 2U - U[c, c + H]`, and
`E J = 0`, so every position has law `G`.

This replaces the linear tilts of Shmalo's Proposition 3.1, whose complete mixability rests on
Wang and Wang's criterion for monotone densities, and the measurable selection or weak limit his
proof needs: every coupling here is an explicit map of finitely many independent uniforms.

## Main results

* `MathFin.jointlyMixable_of_uniform_piece`: the joint version, with one extra law `E`.
* `MathFin.completelyMixable_of_uniform_piece`: the case `E = δ₀` (Shmalo, Theorem 1.2).

## References

* [Y. Shmalo, *Absolutely continuous laws on a bounded interval are completely mixable for all
  large n*][Shmalo2026CompleteMixability], Proposition 3.1 and Theorem 1.2

## Tags

complete mixability, joint mixability, uniform law, rotation, MSC 60E05, MSC 91G70
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- **The coupling for a fixed count `k` of `T`-copies.** For `|m - k| ≤ 1` and room for the
uniform blocks, there is a coupling of `N + 1` coordinates with sum identically
`(N - m) c + m · mean T + mean E`, law `E` in the last coordinate, and, in the first `N`, `k` copies
of `T`, `N - k` copies of `U = U[c - H, c + H]` and the half-interval correction
`4 E[J] (U[c, c + H] - U)` with `2H E[J] = (m - k)(mean T - c)`. The construction is in the
module docstring. -/
theorem exists_coupling_of_count {T E : Measure ℝ} [IsProbabilityMeasure T]
    [IsProbabilityMeasure E] {c H α R β L m : ℝ} (hH : 0 < H) (hT : T (Icc α (α + R))ᶜ = 0)
    (hU : Icc (c - H) (c + H) ⊆ Icc α (α + R)) (hE : E (Icc β (β + L))ᶜ = 0) {N k : ℕ}
    (hk : k ≤ N) (hm : |m - k| ≤ 1) (hroom : 2 * (2 * R + L) / H + 8 ≤ (N - k : ℝ)) :
    ∃ ρ : Measure (Fin (N + 1) → ℝ), IsProbabilityMeasure ρ ∧
      (∀ᵐ x ∂ρ, ∑ i, x i = (N - m) * c + m * ∫ x, x ∂T + ∫ x, x ∂E) ∧
      ρ.map (fun x ↦ x (Fin.last N)) = E ∧
      ∀ B, MeasurableSet B → (∑ i : Fin N, ρ.map (fun x ↦ x i.castSucc) B).toReal =
        k * (T B).toReal + (N - k) * (volume[|Icc (c - H) (c + H)] B).toReal +
          2 * (m - k) * (∫ x, x ∂T - c) / H *
            ((volume[|Icc c (c + H)] B).toReal - (volume[|Icc (c - H) (c + H)] B).toReal) := by
  sorry

/-- **Laws with a uniform piece, jointly with one more law.** `N` copies of
`G = q U[c - H, c + H] + (1 - q) T`, with `T` and the uniform piece in an interval of length
`R`, and one copy of a law `E` on an interval of length `L`, are jointly mixable once
`N ≥ (2(2R + L)/H + 9)/q`. -/
theorem jointlyMixable_of_uniform_piece {T E : Measure ℝ} [IsProbabilityMeasure T]
    [IsProbabilityMeasure E] {q c H α R β L : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hH : 0 < H)
    (hT : T (Icc α (α + R))ᶜ = 0) (hU : Icc (c - H) (c + H) ⊆ Icc α (α + R))
    (hE : E (Icc β (β + L))ᶜ = 0) {N : ℕ} (hN : (2 * (2 * R + L) / H + 9) / q ≤ N) :
    JointlyMixable (Fin.snoc (α := fun _ ↦ Measure ℝ) (fun _ : Fin N ↦
      ENNReal.ofReal q • volume[|Icc (c - H) (c + H)] + ENNReal.ofReal (1 - q) • T) E) := by
  sorry

/-- **Laws with a uniform piece** (Shmalo, Theorem 1.2, with the constant `(4R/H + 9)/q`). -/
theorem completelyMixable_of_uniform_piece {T : Measure ℝ} [IsProbabilityMeasure T]
    {q c H α R : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hH : 0 < H) (hT : T (Icc α (α + R))ᶜ = 0)
    (hU : Icc (c - H) (c + H) ⊆ Icc α (α + R)) {N : ℕ} (hN : (4 * R / H + 9) / q ≤ N) :
    CompletelyMixable N
      (ENNReal.ofReal q • volume[|Icc (c - H) (c + H)] + ENNReal.ofReal (1 - q) • T) := by
  sorry

end MathFin
