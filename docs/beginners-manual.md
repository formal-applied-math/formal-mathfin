# Lean 4 and formal-mathfin: a manual for mathematicians

This manual is for readers who know probability and mathematical finance but have not used Lean. By
the end you should be able to install the library, read its statements, find the theorem you need,
and prove small results with it. No programming background is needed. The exercises at the end
have solutions in [`MathFinTest/Manual.lean`](../MathFinTest/Manual.lean), which the build
checks.

If you want to contribute rather than read, [`onboarding.md`](onboarding.md) is the next step
after this one.

## 1. What Lean checks

Lean is a proof assistant: a programming language in which a theorem is a type and a proof is a
term of that type. When a file compiles, a small program called the kernel has checked every step
of every proof down to the axioms. Nothing is taken on trust, including the steps a textbook would
call obvious.

Three things follow, and they explain most of what is unusual about the library.

- **Every hypothesis is written down.** A proof that silently uses integrability, measurability or
  a positive denominator does not compile. The statements are therefore longer than the textbook's,
  and the difference is usually where the interesting mathematics is.
- **What is checked is the statement, not its name.** The kernel proves exactly the formula
  written. Whether that formula is the theorem a finance reader has in mind is a separate question,
  and the library answers it in prose: every entry of the [benchmark corpus](../benchmarks)
  records whether it proves the textbook result in full or a narrower version, and what it leaves
  out.
- **The axioms are known.** A build-time audit checks that each cited theorem uses only Lean's
  three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and no `sorry`, Lean's
  placeholder for a missing proof.

The library sits on [Mathlib](https://github.com/leanprover-community/mathlib4), the community's
library of formalized mathematics, which supplies measure theory, conditional expectation and
martingales, and on Rémy Degenne's
[BrownianMotion](https://github.com/RemyDegenne/brownian-motion) package, which constructs Brownian
motion and the stochastic integral.

## 2. Installing

1. Install Lean's version manager, [elan](https://lean-lang.org/install/), and the
   [VS Code](https://code.visualstudio.com/) extension `lean4`. The extension's setup guide does
   both.
2. Get the library and the prebuilt Mathlib files:

   ```bash
   git clone https://github.com/formal-applied-math/formal-mathfin.git
   cd formal-mathfin
   lake exe cache get
   lake build
   ```

   The first `lake build` compiles BrownianMotion and the library from source, which takes a
   while. Later builds only recompile what changed.
3. Open the folder in VS Code and open any `.lean` file. The panel on the right, the *infoview*,
   shows the state of the proof at the cursor: the hypotheses available and the goal still to
   prove. Moving the cursor through a proof is the best way to read one.

To use the library from your own project instead, see
[the README](../README.md#using-the-library-in-a-project).

## 3. Reading a file

Open [`MathFin/Binomial/Model.lean`](../MathFin/Binomial/Model.lean), the one-period binomial model.
Its parts appear in every file.

```lean
/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
```

The header names the authors. `module` and `public import` say which other files this one builds
on; here, all of Mathlib. A block `/-! … -/` that follows is the module's documentation, in
Markdown, and states what the file proves.

```lean
/-- The risk-neutral up-probability `q = (e^r - d) / (u - d)`. -/
noncomputable def crrUpProb (u d r : ℝ) : ℝ :=
  (Real.exp r - d) / (u - d)
```

A `def` introduces a definition. The comment `/-- … -/` above it is its docstring. `(u d r : ℝ)`
are its arguments, three real numbers, and `: ℝ` after them is the type of the result.
`noncomputable` only says that Lean cannot run the definition as a program, since real numbers are
not finite objects; it has no mathematical meaning.

```lean
/-- No-arbitrage condition for the binomial single-period model:
`d < e^r < u` (and `d > 0`). -/
structure BinomialNoArb (u d r : ℝ) : Prop where
  d_pos : 0 < d
  d_lt : d < Real.exp r
  lt_u : Real.exp r < u
```

A `structure … : Prop` bundles several conditions into one proposition. A proof `h` of
`BinomialNoArb u d r` gives back each condition by name: `h.d_pos : 0 < d`, and so on.

```lean
/-- Under no-arbitrage, the risk-neutral up-probability is in `(0, 1)`. -/
lemma crrUpProb_mem_Ioo {u d r : ℝ} (h : BinomialNoArb u d r) :
    crrUpProb u d r ∈ Set.Ioo 0 1 := by
  have h_ud : 0 < u - d := by linarith [h.d_lt_u]
  refine ⟨?_, ?_⟩
  · unfold crrUpProb
    exact div_pos (by linarith [h.d_lt]) h_ud
  · unfold crrUpProb
    rw [div_lt_one h_ud]; linarith [h.lt_u]
```

A `lemma` or `theorem` has a name, hypotheses, a colon, and the statement. Read it as: *for real
`u`, `d`, `r`, if the tree has no arbitrage then `q ∈ (0, 1)`*. Arguments in braces `{u d r : ℝ}`
are implicit: Lean works them out from the other arguments, so a user writes
`crrUpProb_mem_Ioo h`, not `crrUpProb_mem_Ioo u d r h`.

After `:= by` comes the proof, as a sequence of *tactics*, each of which transforms the goal shown
in the infoview. Here `have` proves an intermediate fact, `refine ⟨?_, ?_⟩` splits membership in
the interval into its two inequalities, `unfold` replaces `crrUpProb` by its definition, and
`linarith` closes linear inequalities from the hypotheses. You do not need to know the tactics to
read the library. The statement is what the library claims; the proof is what the kernel checked.

## 4. Reading statements

Most of the notation is Mathlib's and reads as mathematics. The pieces that come up most in the
library:

| Lean | Meaning |
| --- | --- |
| `∀ x, P x`, `∃ x, P x` | for all, there exists |
| `fun x ↦ f x` | the function `x ↦ f(x)` |
| `f x` | `f(x)`: application is written without parentheses |
| `[IsProbabilityMeasure P]` | an assumption Lean finds by itself from context, here that `P` is a probability measure |
| `∫ x, f x ∂μ` | the integral of `f` against `μ` |
| `μ[X \| m]` | the conditional expectation of `X` given the σ-algebra `m` |
| `f =ᵐ[μ] g` | `f = g` almost everywhere |
| `HasLaw X μ P` | the law of `X` under `P` is `μ` |
| `Tendsto f atTop (𝓝 a)` | `f(n) → a` as `n → ∞` |
| `HasDerivAt f f' x` | `f` is differentiable at `x` with derivative `f'` |

Long statements usually rely on a `variable` line earlier in the file, which declares arguments
shared by every theorem below it. The discrete fundamental theorem of asset pricing in
[`Foundations/FTAPDiscrete.lean`](../MathFin/Foundations/FTAPDiscrete.lean) reads

```lean
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] {mΩ : MeasurableSpace Ω}
  [MeasurableSingletonClass Ω] (𝓕 : Filtration ℕ mΩ)
  (P : Measure Ω) [IsProbabilityMeasure P] (S : ℕ → Ω → ℝ) (T : ℕ)

theorem ftap_discrete (hS : StronglyAdapted 𝓕 S) (hP : ∀ ω, 0 < P {ω}) :
    NoArbitrage 𝓕 P S T ↔ ∃ Q, IsEMM 𝓕 P S T Q
```

so the full statement is: on a finite, nonempty sample space with a filtration `𝓕` and a
probability `P` charging every point, a price process `S` adapted to `𝓕` has no arbitrage up to
time `T` if and only if there is an equivalent martingale measure. Each assumption in brackets is
part of the theorem, and the definitions `NoArbitrage` and `IsEMM` a few lines above it say exactly
what the two sides mean.

One habit of Lean needs care. Division by zero is defined to be `0`, and so is the integral of a
non-integrable function. Nothing false follows from this, but such a value can look like a price.
A theorem that calls something a price or an expectation therefore carries the conditions that
make it one, such as `BinomialNoArb` above, which keeps `u − d` positive. Exercise 6 shows what
happens without it. [`design.md`](design.md#2-a-junk-value-never-gets-a-financial-meaning)
discusses this further.

## 5. Finding a theorem

- **By topic.** The library is organized by area: `Foundations/` for stochastic calculus and
  no-arbitrage theory, then `BlackScholes/`, `Binomial/`, `FixedIncome/`, `Portfolio/`,
  `RiskMeasures/` and so on. Each module's documentation lists what it proves.
- **By source.** Each benchmark file in [`benchmarks/`](../benchmarks) lists results from the
  literature, with the reference, a description of what the entry proves, and the name of the Lean
  theorem. The same corpus is published as a
  [Hugging Face dataset](https://huggingface.co/datasets/formal-applied-math/formal-mathfin-theorems).
- **By dependency.** [`blueprint.md`](blueprint.md) draws the chain from Brownian motion to the
  Black–Scholes formula, each node linked to its proof.
- **Inside Lean.** In any file that imports the library, `#check binomialNoArb_crr` prints a
  theorem's statement in the infoview, and the tactic `exact?` searches Mathlib and the library for
  a lemma that closes the current goal. Mathlib's [documentation](https://leanprover-community.github.io/mathlib4_docs/)
  and the search engine [Loogle](https://loogle.lean-lang.org) cover Mathlib.

## 6. Exercises

Create a file `Scratch.lean` at the root of the repository, start it with

```lean
import MathFin

open MathFin
```

and replace each `sorry` below with a proof. The infoview shows the goal as you go. Solutions are
in [`MathFinTest/Manual.lean`](../MathFinTest/Manual.lean).

**1. A tree with no arbitrage.** Take `u = 2`, `d = 1/2` and `r = 0`. Show the tree has no
arbitrage. *Hint:* a proof of a structure is written `⟨proof₁, proof₂, proof₃⟩`, one per field, and
the tactic `norm_num` proves numerical facts, including `Real.exp 0 = 1`.

```lean
example : BinomialNoArb 2 (1 / 2) 0 := sorry
```

**2. Using a lemma.** Deduce, by applying `crrUpProb_mem_Ioo` from section 3, that the
risk-neutral probability of that tree lies in `(0, 1)`.

```lean
example : crrUpProb 2 (1 / 2) 0 ∈ Set.Ioo 0 1 := sorry
```

**3. Computing.** Show that it equals `1/3`. *Hint:* `norm_num [crrUpProb]` unfolds the definition
and computes.

```lean
example : crrUpProb 2 (1 / 2) 0 = 1 / 3 := sorry
```

**4. Pricing a call.** With spot `1` and strike `1`, a call pays `max (2 - 1) 0` after an up move
and `max (1/2 - 1) 0` after a down move. Show that its price,
`binomialOptionPriceOnePeriod`, is `1/3`.

```lean
example : binomialOptionPriceOnePeriod 2 (1 / 2) 0 (max (2 - 1) 0) (max (1 / 2 - 1) 0) = 1 / 3 :=
  sorry
```

**5. A riskless payoff.** Show that a claim paying `c` in both states is worth `e^{-r} c`, for any
`u`, `d` and `r`. *Hint:* `unfold binomialOptionPriceOnePeriod`, then `ring`. Note that the proof
needs no no-arbitrage hypothesis: `q · c + (1 − q) · c = c` whatever `q` is.

```lean
example (u d r c : ℝ) : binomialOptionPriceOnePeriod u d r c c = Real.exp (-r) * c := sorry
```

**6. A degenerate tree.** When `u = d` the tree has no risk-neutral probability, yet `crrUpProb`
is still a real number. Before reading the statement below, work out which number from the
definition and the convention `x / 0 = 0`; then prove it. *Hint:* `simp [crrUpProb]`.

```lean
example (u r : ℝ) : crrUpProb u u r = 0 := sorry
```

Exercise 6 is why `BinomialNoArb` appears in every pricing theorem of the binomial model, and why
Exercise 5 is a statement about prices only where `BinomialNoArb` holds.

## 7. Where to go next

- The [README](../README.md#main-results) lists the main results, with links to their proofs.
- [`MathFinExamples/Tour.lean`](../MathFinExamples/Tour.lean) walks through five representative
  proofs.
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/) and
  [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) are the
  standard introductions to Lean itself.
- To add a result, read [`onboarding.md`](onboarding.md) and [`design.md`](design.md).
