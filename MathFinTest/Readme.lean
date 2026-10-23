/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import MathFin

/-!
# The README's Lean, as a downstream project sees it

This file imports only the umbrella `MathFin`, as a project that requires the library does, and
restates the theorem quoted at the top of `README.md` word for word. It stops building if that
statement changes or the umbrella stops exporting it. `.github/workflows/downstream.yml` compiles
the same file in a fresh Lake project that requires this repository.
-/

open MathFin Filter
open scoped Topology

/-- The Cox–Ross–Rubinstein call price converges to the Black–Scholes price, as quoted in the
README. -/
example {r σ T S₀ K : ℝ}
    (hσ : 0 < σ) (hT : 0 < T) (hS₀ : 0 < S₀) (hK : 0 < K)
    (hna : ∀ n, 0 < n → BinomialNoArb (crrUp σ T n) (crrDown σ T n) (crrPerStepRate r T n)) :
    Tendsto (fun n : ℕ ↦ binomialPrice (crrUp σ T n) (crrDown σ T n) (crrPerStepRate r T n)
        (fun x ↦ max (x - K) 0) n S₀) atTop
      (𝓝 (S₀ * Phi (bsd1 S₀ K r σ T)
          - K * Real.exp (-(r * T)) * Phi (bsd2 S₀ K r σ T))) :=
  binomialPrice_call_tendsto_bs_closed hσ hT hS₀ hK hna

/-- The README's remark that `hna` holds whenever `|r|√T < σ`: with `binomialNoArb_crr` the limit
holds with no hypothesis on the trees. -/
example {r σ T S₀ K : ℝ}
    (hσ : 0 < σ) (hT : 0 < T) (hS₀ : 0 < S₀) (hK : 0 < K) (hrT : |r| * Real.sqrt T < σ) :
    Tendsto (fun n : ℕ ↦ binomialPrice (crrUp σ T n) (crrDown σ T n) (crrPerStepRate r T n)
        (fun x ↦ max (x - K) 0) n S₀) atTop
      (𝓝 (S₀ * Phi (bsd1 S₀ K r σ T)
          - K * Real.exp (-(r * T)) * Phi (bsd2 S₀ K r σ T))) :=
  binomialPrice_call_tendsto_bs_closed hσ hT hS₀ hK fun _ hn ↦ binomialNoArb_crr hT hrT hn
