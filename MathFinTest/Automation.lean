/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import MathFin

/-!
# What the library's automation closes

`docs/design.md` §5: a hub definition comes with the automation its users need. Each example
here is a fact a user should get from one tactic call; it stops building if a tag is dropped or
an interface lemma goes missing. The grind set `pricing` is registered in `MathFin/Init.lean`.
-/

open MathFin

/-! ## `grind [pricing]`: put–call parity and the trees' risk-neutral probabilities -/

/-- Put–call parity on the closed forms, twice: the box spread. -/
example (K₁ K₂ r σ S τ : ℝ) :
    (bsV K₁ r σ S τ - bsP K₁ r σ S τ) - (bsV K₂ r σ S τ - bsP K₂ r σ S τ) =
      (K₂ - K₁) * Real.exp (-(r * τ)) := by
  grind [pricing]

/-- A long call, a short put and a bond paying `K` replicate the forward. -/
example (K r σ S τ : ℝ) :
    bsV K r σ S τ - bsP K r σ S τ + K * Real.exp (-(r * τ)) = S := by
  grind [pricing]

/-- The binomial up-probability makes the discounted stock fair, in either form. -/
example {u d r : ℝ} (h : BinomialNoArb u d r) :
    crrUpProb u d r * u + (1 - crrUpProb u d r) * d = Real.exp r := by
  grind [pricing]

example {u d r : ℝ} (h : BinomialNoArb u d r) :
    1 - crrUpProb u d r = (u - Real.exp r) / (u - d) := by
  grind [pricing]

/-- Merton's conditional values obey put–call parity term by term. -/
example (S_0 K r σ T k δ : ℝ) (Λ : NNReal) (n : ℕ) :
    mertonCallTerm S_0 K r σ T k δ Λ n =
      mertonPutTerm S_0 K r σ T k δ Λ n + mertonSpot S_0 k Λ n - K * Real.exp (-r * T) := by
  grind [pricing]

/-- Exchanging the two assets in Margrabe's formula costs their spread. -/
example (S1 S2 σ T : ℝ) (hS1 : 0 < S1) (hS2 : 0 < S2) (hσ : σ ≠ 0) (hT : 0 < T) :
    margrabePrice S1 S2 σ T = margrabePrice S2 S1 σ T + (S1 - S2) := by
  grind [pricing]

/-! ## `positivity`, `gcongr`, `fun_prop` on the hub definitions -/

/-- A discounted digital: a bond times a normal probability. -/
example (r t T x : ℝ) : 0 < zcb r t T * Phi x := by positivity

/-- `Φ` is monotone in its argument, and `gcongr` knows it. -/
example {S K K' r σ T : ℝ} (h : bsd2 S K' r σ T ≤ bsd2 S K r σ T) :
    Phi (bsd2 S K' r σ T) ≤ Phi (bsd2 S K r σ T) := by gcongr

example {a b c : ℝ} (h : a < b) : Phi a + c < Phi b + c := by gcongr

/-- A function built from `Φ` is continuous. -/
example (a b : ℝ) : Continuous fun x : ℝ ↦ Phi (a * x + b) := by fun_prop
