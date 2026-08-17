# The contract is not the model: a reified payoff tower — design

**Date:** 2026-08-16 · **Status:** design, awaiting approval · **Corpus at design time:** 358
**Companions:** [`mathematical-architecture.md`](../mathematical-architecture.md),
[`bridges.md`](../bridges.md), [`roadmap.md`](../roadmap.md),
[`2026-08-16-ito-chain-rule-design.md`](2026-08-16-ito-chain-rule-design.md) (in flight, disjoint)

**External source:** Bilokon, *The Contract Is Not the Model: Proof-Carrying Exotic
Derivatives and the Economics of Model Risk*, working paper, 9 August 2026;
code at `github.com/thalesians/lean_contracts` (Apache-2.0). Consulted as a
**source, not a template** — see §6.

---

## 0. Summary

MathFin has 275 modules and 59k lines and no object that represents *a contract*.
All 62 payoff-bearing modules hard-code the payoff as a Lean function
(`fun S ↦ max (S - K) 0`), so the payoff and the model are the same syntactic
object and nothing can be said about one without the other.

This spec builds a small reified payoff language, proves that its evaluation is
measurable and adapted, and closes the loop by proving that the reified European
call, put, digital and capped call price to the closed forms we already have in
`MathFin/BlackScholes/`.

Three rungs, all in scope:

| rung | content |
|---|---|
| **(a)** | `Payoff ι` / `Contract ι` as inductives over a **typed** underlying index, with `eval` and `pathPV` |
| **(b)** | `eval` is measurable; `obsTimes ≤ u` ⟹ `eval` is `𝓕 u`-measurable; the discounted value process is a `Q`-martingale under `IsEMM` |
| **(c)** | `value (europeanCall K T) = bs_call_formula`, and the same for put / cash-or-nothing / capped call — the last by **composition**, not by a new integral |

Rung (c) is the point. A reified contract whose price is a machine-checked
Black–Scholes formula does not exist anywhere, including in the source paper,
whose pricing layer is a `structure` and one `congrArg`.

---

## 1. The gap, precisely

`MathFin/BlackScholes/Digital.lean:67` proves

```lean
theorem bs_cash_or_nothing_formula (h : BSCallHyp Q S_0 K r σ T Z) :
    ∫ ω, Real.exp (-r * T) *
        (Set.Ioi K).indicator (fun _ ↦ (1 : ℝ)) (bsTerminal S_0 r σ T (Z ω)) ∂Q
      = Real.exp (-r * T) * Phi (bsd2 S_0 K r σ T)
```

The integrand is the contract. It is written inline, as a lambda, and it exists
nowhere else in the library. Consequences:

* **Nothing composes.** `CappedCall.lean:32` proves `cappedCall_eq_bull_spread`
  as a pointwise real identity, then stops — there is no object on which to say
  "the value of a sum of contracts is the sum of the values", so the bull-spread
  decomposition cannot be turned into a price.
* **Nothing is reusable across models.** Swap the lognormal hypothesis for a
  Bachelier one and every payoff is re-typed by hand.
* **Nothing is checkable.** There is no `Contract` to lint, so "did we encode the
  term sheet correctly" is not a question the library can be asked.

The five-layer decomposition in the source paper (source terms → contract
semantics → lifecycle → pricing → numerics) names this gap correctly, and its
central claim — *validate the derivative before you validate the model* — is
right. Its Lean artifact does not close the gap: the whole probability content is
a `PricingModel` structure, a Bochner integral of a function never shown
integrable, and `value_eq_of_pathPV_eq`, which is `congrArg` under `∫`.

---

## 2. Design

### 2.1 Typed, not stringly typed

The source encodes underlyings, rates, entities and decisions as `String`
(`abbrev Underlying := String`), and scenarios as `Scalar → Time → ℝ` with
`Time := Nat`. Both choices are rejected here:

```lean
/-- A fully specified market outcome: the level of each underlying at each time.
    Stochastic models are laws on this type. -/
abbrev Scenario (ι : Type*) := ι → ℝ≥0 → ℝ
```

`ι` is the caller's index type (`Unit` for single-asset, `Fin n` for a basket),
and time is `ℝ≥0` — the index of `Filtration ℝ≥0 mΩ` throughout `Foundations/`.
A `String` key admits `level "SPX" t` and `level "spx" t` as distinct
observables with no error; `ι` makes that unrepresentable, and makes the
adaptedness theorem in §2.4 statable without a well-formedness side condition.

### 2.2 One inductive, not two mutual ones

The source uses a `mutual` block (`NumExpr` / `BoolExpr`), which costs a mutual
recursor at every proof. Comparisons only ever appear here as indicators, so a
single inductive suffices:

```lean
inductive Payoff (ι : Type*) where
  | const (c : ℝ)
  | obs (i : ι) (t : ℝ≥0)
  | add (a b : Payoff ι)
  | sub (a b : Payoff ι)
  | mul (a b : Payoff ι)
  | max (a b : Payoff ι)
  | min (a b : Payoff ι)
  | indicatorLt (a b : Payoff ι)   -- `1` if `a < b`, else `0`
```

`indicatorLt` gives digitals; `max (sub (obs i T) (const K)) (const 0)` gives the
call; `min`/`max` give caps, floors and worst-of. Every proof in rung (b) is then
a plain `induction e` with eight cases and no mutual block.

### 2.3 Contracts, and what is deliberately absent

```lean
inductive Contract (ι : Type*) where
  | zero
  | pay (t : ℝ≥0) (amount : Payoff ι)
  | both (a b : Contract ι)
  | scale (c : ℝ) (a : Contract ι)
```

Absent by design, each with the case that would force it:

* **`ifThen` / branching contracts.** Redundant at this rung: a digital *payoff*
  covers every instrument in `BlackScholes/`. Forced by the first autocall.
* **Currency.** Forced by the first FX instrument; until then a currency field is
  a tag no theorem reads.
* **`scale` by a `Payoff`** (the source's choice). Redundant: `Payoff.mul`
  already scales inside a `pay`. `scale` stays a plain `ℝ` for notional.
* **The lifecycle layer** (outstanding notional, termination, partial
  redemption). This is the strongest part of the source artifact and the right
  next rung — but it earns its place only once a callable instrument is in the
  corpus, and none is today.

This is the source's own METHODOLOGY §4 discipline ("extended only when a case
requires it"), applied to the source.

### 2.4 The theorems that make it worth having

The source's `Contract.observationTimes` exists only to feed a syntactic
chronology check discharged `by decide` — a linter with a proof term. The same
function here carries content:

```lean
/-- `eval` of a payoff whose observations all precede `u` is `𝓕 u`-measurable. -/
theorem Payoff.measurable_eval_of_obsTimes_le
    (e : Payoff ι) (X : ι → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i t, Measurable[𝓕 t] (X i t))
    (hle : ∀ t ∈ e.obsTimes, t ≤ u) :
    Measurable[𝓕 u] fun ω ↦ e.eval (fun i t ↦ X i t ω)
```

That is the bridge from the syntactic layer to `Foundations/`: it is what lets a
contract be an integrand at all, and it is exactly what the source's `value`
assumes without proof.

The pricing statement is then stated against the EMM object we already have,
`ContinuousMarket.IsEMM` (`MathFin/Foundations/ContinuousMarket.lean:75`), rather
than against a fresh `PricingModel` record.

---

## 3. The honest ceiling

Stated here so no downstream prose outruns it:

1. **This is not a term-sheet formalisation.** The corpus entries will carry a
   `formalization_scope` saying the object is a payoff kernel over a given
   observation grid, not a legal instrument. Calendars, business-day conventions,
   disruption, corporate actions and issuer credit are all absent and are not
   claimed.
2. **The martingale rung is the value process, not the hedge.** Rung (b) proves
   the discounted value process is a `Q`-martingale with the right terminal value
   and time-0 value. It does **not** prove that process is the wealth of a
   replicating strategy — that needs `∫ψ dS`, which is the separate in-flight
   `2026-08-16-ito-chain-rule-design.md`. The two specs must not be merged and
   must not be executed in the same worktree.
3. **Rung (c) is single-asset.** `bs_call_formula` and friends are stated under
   `BSCallHyp` at `ι = Unit`. Multi-asset instances need a joint law we do not
   have.
4. **`Payoff` is finitely observed.** `obsTimes` is a `List`, so continuously
   monitored barriers are outside the language. Discretely monitored ones are in.

---

## 4. Why in-repo and not a dependency

Settled: the contract layer lives at `MathFin/Contracts/`.

* **Direction.** Rung (b) imports `Foundations/ContinuousMarket`; rung (c)
  imports `BlackScholes/{Call,Put,Digital,CappedCall}`. A `require` on an
  upstream contracts package can hold rung (a) and nothing else — the 200 lines
  with no theorems in them.
* **Pin.** `lean_contracts` pins Lean `v4.32.2` + mathlib `v4.32.2`; we are on
  `v4.32.0` with BrownianMotion `4d52fa77`. Lake takes one toolchain for the
  tree, so consuming it means bumping us, which stales every ledger row.
* **It has never been kernel-built.** Its own README and the paper's Limitations
  §4 say so. Its `code/README.md` describes a `.github/workflows/ci.yml` that is
  not in the repository.
* **Gates.** `test_values.py` scans `MathFin/`; the ledger input-hash covers the
  transitive MathFin modules an entry imports plus the toolchain pins. A vendored
  dependency is invisible to both.
* **Import weight.** Its `Core.lean` opens with `import Mathlib`, dragging the
  full closure — the one that already OOM-kills `leanchecker` at 16 GB — into
  everything downstream.

A separate downstream repo becomes right if and when the production surface
appears (calendars, fixing/disruption semantics, vendor data adapters — the
source paper's §"Next formalization steps"). That work has a different audience
and a different cadence. The mathematical core does not.

---

## 5. Corpus and gate impact

* Adds ~8 entries to `benchmarks/mathematical_finance.json`, domain
  `mathematical_finance`, status `full`.
* `REVIEW_SLACK_ENTRIES = 12` and the newest recorded values review covers corpus
  **358**, against a live corpus of **358** — both moved when PR #198 (the Itô
  chain rule) merged to `main` on 2026-08-16 and recorded its own review round.
  Eight new entries reach 366 — inside slack, but a second phase on top trips
  `test_values_review_is_current`. Budget a values-review round at the close.
  Re-derive both numbers at execution time rather than trusting this line:
  `python3 -m tools.verify.coverage_report`, and the newest `corpus <N>` header
  in `docs/values-review.md`.
* `MathFin/AxiomAuditGen.lean` must be regenerated
  (`python3 -m tools.verify.axiom_audit_gen --write`) after the benchmark edit.
* `MathFin.lean` gains five import lines (six if the optional `Scope.lean` rung lands). It is a **single-file bind mount**:
  after editing, re-sync into any running container or restart the service.

---

## 6. Attribution, licence, and what is and is not ours

This work is **derived from published work by a named author**, and every artifact
it produces says so. Nothing here is presented as an independent invention.

### 6.1 The source

> Paul Bilokon. *The Contract Is Not the Model: Proof-Carrying Exotic Derivatives
> and the Economics of Model Risk.* Working paper, 9 August 2026. Mathematical
> Finance, Department of Mathematics, Imperial College London.
> Code: <https://github.com/thalesians/lean_contracts> (Thalesians organisation),
> licensed **Apache-2.0**.

The paper's own lineage is acknowledged in turn and must be carried with it: the
compositional contract-DSL idea is Peyton Jones, Eber and Seward (2000); the
certified-contract-management line is Bahr, Berthold and Elsman (2015) and
Annenkov (2018) in Coq; the blockchain-derivative line is Arusoaie et al.
(Findel). Citing Bilokon without citing the tradition he cites would be a second
kind of erasure.

### 6.2 What is his

Taken as ideas, and credited as his in every module docstring that uses them:

* **The thesis.** "The contract is not the model" — that the deterministic
  cashflow map is a separate object from the probability law over scenarios, and
  that it must be validated first. Our entire file layout is that sentence.
* **The five-layer decomposition.** Source terms → contract semantics →
  lifecycle → pricing semantics → numerical/risk refinement, with theorem
  boundaries between the layers.
* **Contract-semantic risk** as a named category of model risk, distinct from
  data, model and numerical risk.
* **Unmodelled clauses as first-class data** — that a validation certificate
  must carry the list of what it does not cover. This is the direct ancestor of
  `Contracts/Scope.lean` and of the drift gate that pins it to
  `metadata.formalization_scope`.
* **The lifecycle-as-state-machine design** (outstanding notional, absorbing
  termination, compile-to-DSL with a semantics-preservation theorem). Not built
  in this spec, and when it is built, it is built as his design.

### 6.3 What is ours

Stated so the credit line is precise in both directions, not so it is minimised:

* the typed underlying index and `ℝ≥0` time (§2.1), against his `String` keys
  and `Nat` time;
* the single inductive with `indicatorLt` (§2.2), against his mutual
  `NumExpr` / `BoolExpr` pair;
* the measurability and adaptedness theorems (§2.4), which have no counterpart
  in the source — his `PricingModel.value` integrates a function never shown
  measurable, and the paper's Limitations §4 records that the artifact has not
  been kernel-built;
* the reduction of each reified instrument to an existing `MathFin/BlackScholes/`
  closed form (rung c), which the source paper lists as future work.

### 6.4 Licence

**No code is copied.** Every definition, statement and proof in
`MathFin/Contracts/` is written here. Apache-2.0 §4's notice-retention
obligations therefore do not attach, and no `NOTICE` file is required.

We cite anyway, prominently and by name, because taking someone's idea and
presenting it as one's own is wrong independently of what a licence compels. If
any code is ever copied from `lean_contracts` — a definition, a proof, a
docstring — it arrives with its Apache-2.0 header intact, the copied region
marked in-file, and a `NOTICE` entry, and this section is amended to say what was
copied. Until then this section stands as written.

### 6.5 Where the attribution lives

Attribution is **machine-enforced**, not left to good intentions:

1. Every `MathFin/Contracts/*.lean` module docstring ends with a `## Source`
   section naming Bilokon, the paper title, the date, the repository URL and its
   licence. Gated by `tests/test_values.py::test_contracts_cite_source`.
2. Every corpus entry for this tower carries the paper in
   `metadata.reference`, so the citation ships in the HF dataset alongside the
   claim.
3. `docs/sources.md` catalogues the external formalisations this library has
   consulted, what was taken from each, and what was not — seeded with the AFP
   `Survival_Model` precedent and this one.
4. `README.md`'s landmark row for the capped call names the source paper.

### 6.6 The precedent

This follows the pattern set with AFP `Survival_Model`: an external
formalisation is a **source**, designed afresh in our idiom and cited honestly,
never a template to copy from and never a dependency to absorb quietly. The rule
that produced this section is the standing one — *external formalizations are
sources, not templates* — and it cuts both ways: we do not copy, and we do not
pretend we arrived unaided.
