# Contracts Tower Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Give MathFin a reified payoff language whose evaluation is provably adapted and whose European call, put, cash-or-nothing and capped call price to the Black–Scholes closed forms the library already proves.

**Architecture:** One inductive `Payoff ι` over a typed underlying index plus a four-constructor `Contract ι`, evaluated into discounted pathwise cashflows. Measurability and adaptedness are proved by structural induction on `Payoff`, which is what lets a contract be an integrand at all. Pricing is an integral against a measure and is stated against the existing `ContinuousMarket.IsEMM`, not a fresh model record. The tower closes by reducing each reified instrument's `value` to an existing `MathFin/BlackScholes/` theorem.

**Tech Stack:** Lean 4 `v4.32.0`, Mathlib (pinned via `lake-manifest.json`), Degenne BrownianMotion `4d52fa77`; Python 3.11 stdlib for `tools.verify`; Docker `lean-repl` daemon for iteration.

**Spec:** [`docs/specs/2026-08-16-contracts-tower-design.md`](../specs/2026-08-16-contracts-tower-design.md)

---

## Global Constraints

Every task's requirements implicitly include this section.

- **Work in an isolated worktree.** As of 2026-08-16 at least two other Claude sessions have cwd `/mnt/c/Users/rapha/Documents/Code/formal-mathfin` and one is actively editing `MathFin/Foundations/ContinuousMarket.lean` on branch `feat/ito-chain-rule`. Do **not** branch, build, or run the daemon in the shared tree. Create the worktree first (Task 1, Step 1).
- **Never `docker compose build` locally.** Only `docker compose -f docker/docker-compose.yml pull verify`. Image builds escape compose's memory caps on a 10 GB box.
- **One Lean-loaded process at a time.** The `lean-repl` daemon is the default slot occupant. A `lake build` requires `docker compose -f docker/docker-compose.yml down lean-repl` first.
- **Every file under `MathFin/` MUST have**, in this order: the Apache-2.0 copyright block naming `Raphael Coelho`, `module`, its `public import`s, the module docstring, then `@[expose] public section`. Without the last line every declaration is module-private: importers see nothing and `lake build` stays green. Enforced by `tests/test_router.py::test_mathfin_module_files_expose_public_section`.
- **Forbidden in `MathFin/` sources** (enforced by `tests/test_values.py`): `sorry`, `admit`, `native_decide`, `polyrith`, `?`-suggestion tactics, `hammer`, `loogle`, `leansearch`. Comments are exempt.
- **Attribution is a hard requirement, not a courtesy.** This tower is derived
  from published work by a named author. Every `MathFin/Contracts/*.lean` module
  docstring MUST end with this block, verbatim except for the per-file "what this
  file takes" sentence:

  ```
  ## Source

  The layered separation of contract semantics from pricing semantics, and the
  framing "the contract is not the model", are due to Paul Bilokon, *The Contract
  Is Not the Model: Proof-Carrying Exotic Derivatives and the Economics of Model
  Risk* (working paper, 9 August 2026; Mathematical Finance, Imperial College
  London), with code at <https://github.com/thalesians/lean_contracts>
  (Apache-2.0). That paper in turn builds on the compositional contract-DSL of
  Peyton Jones, Eber and Seward (2000) and the certified-contract work of Bahr,
  Berthold and Elsman (2015) and Annenkov (2018).

  <one sentence: what THIS file takes from that source, and what is ours.>

  No code is copied from `lean_contracts`; every definition and proof here is
  written for this library. See `docs/specs/2026-08-16-contracts-tower-design.md`
  §6 for the full credit line.
  ```

  Enforced by `tests/test_values.py::test_contracts_cite_source` (Task 6 Step 6).
  A `Contracts/` module without it is a failed task, not a minor finding.
- **No `Co-Authored-By` trailer and no Claude attribution** in any commit message, docstring, doc, or PR body.
- **Namespace:** `MathFin.Contracts`. **Underlying index:** a type variable `ι`, never `String`. **Time:** `ℝ≥0`, matching `Filtration ℝ≥0 mΩ` throughout `Foundations/`.
- **Idiomatic register** (`docs/patterns.md` → "Mathlib house-style golf"): bare proof term over `by exact`; let Lean insert coercions, never hand-write `↑`; bind ∀-vars in the `have` signature; `simpa … using e` over `have`/`simp at`/`exact`; `↦` over `=>`; no gratuitous `classical`; prefer `suffices`/`show … from` to a long `have`-ladder.
- **The spurious-guard rule.** Before shipping any theorem, delete each hypothesis and re-run the proof. A hypothesis the proof consumes is not necessarily one the theorem needs. Four of four drafts failed this on 2026-07-31 and every gate passed them. Task 4 contains a live instance of this trap — read it before writing that file.
- **Git:** specific `git add <path>` only. Never `git add -A` or `git add .`.

### The repo-native TDD cycle

Lean has no separate test file and `sorry` is banned in `MathFin/`, so the red/green cycle is **statement-first, in a scratch file**:

1. Write the theorem **statement** with `sorry` for the body, in `/tmp/claude-*/scratchpad/probe.lean`, importing the real modules.
2. `./scripts/lean-check.sh <scratch file>` → expect `{"success": true, ..., "sorry_count": 1}`. This is the failing test: it proves the statement *elaborates* — that every name exists, the types line up, and the coercions resolve. A statement that will not elaborate is the single most common way a Lean task dies.
3. Prove it in the scratch file until `sorry_count: 0`.
4. Move the finished declaration into its `MathFin/` module, re-run `lean-check.sh` on the real file.
5. Commit.

`lean-check.sh` runs with `autoImplicit true` while `lake build` runs with it `false`. A file can pass the daemon and fail the build on a typo'd identifier that the daemon silently auto-bound. **Always finish a task with `lake build MathFin` (daemon down) before calling it green.**

---

## File Structure

| File | Responsibility |
|---|---|
| `MathFin/Contracts/Core.lean` | `Payoff`, `Contract`, `Scenario`, `eval`, `cashflows`, `pathPV`, and the three `pathPV` algebra lemmas |
| `MathFin/Contracts/Adapted.lean` | `Payoff.obsTimes`; `eval` is measurable; `obsTimes ≤ u ⟹ eval` is `𝓕 u`-measurable |
| `MathFin/Contracts/Pricing.lean` | `value`; its linearity; the value process is a martingale; the EMM seam theorem |
| `MathFin/Contracts/BlackScholes.lean` | `europeanCall`, `europeanPut`, `digitalCall` + their closed-form values |
| `MathFin/Contracts/CappedCall.lean` | the capped call as a composed contract: payoff identity + value by composition |
| `MathFin/Contracts/Scope.lean` | *(Task 8, optional)* in-Lean scope disclosure + the drift gate |
| `MathFin.lean` | umbrella; gains one `import` line per module above |
| `benchmarks/mathematical_finance.json` | 8 new entries |
| `tests/test_values.py` | *(Task 8 only)* the scope-drift gate |

Files that change together live together: the two capped-call theorems share every lemma they use, and are the only consumers of `value_both`/`value_scale`, so they get their own file rather than being appended to `BlackScholes.lean`.

---

## Task 1: Core — the payoff language and its cashflow semantics

**Files:**
- Create: `MathFin/Contracts/Core.lean`
- Modify: `MathFin.lean` (append one import)
- Probe: `<scratchpad>/probe1.lean`

**Interfaces:**
- Consumes: nothing (this is the base of the tower).
- Produces, all in namespace `MathFin.Contracts`:
  - `abbrev Scenario (ι : Type*) := ι → ℝ≥0 → ℝ`
  - `inductive Payoff (ι : Type*)` with constructors `const (c : ℝ)`, `obs (i : ι) (t : ℝ≥0)`, `add`, `sub`, `mul`, `max`, `min`, `indicatorLt` (each binary one taking `(a b : Payoff ι)`)
  - `Payoff.eval : Scenario ι → Payoff ι → ℝ`
  - `inductive Contract (ι : Type*)` with `zero`, `pay (t : ℝ≥0) (amount : Payoff ι)`, `both (a b : Contract ι)`, `scale (c : ℝ) (a : Contract ι)`
  - `Contract.cashflows : Scenario ι → Contract ι → List (ℝ≥0 × ℝ)`
  - `Contract.pathPV : (ℝ≥0 → ℝ) → Scenario ι → Contract ι → ℝ`
  - `Contract.pathPV_pay`, `Contract.pathPV_both`, `Contract.pathPV_scale`

- [ ] **Step 1: Create the isolated worktree**

The shared tree is occupied. Run from the repo root:

```bash
cd /mnt/c/Users/rapha/Documents/Code/formal-mathfin
git worktree add -b feat/contracts-tower ../formal-mathfin-contracts main
cd ../formal-mathfin-contracts
git config merge.mathfin-ledger.name "semantic merge for verification_ledger.json"
git config merge.mathfin-ledger.driver "python3 tools/verify/ledger_merge.py %O %A %B %L %P"
git config core.hooksPath .githooks
```

The last three lines are per-clone git config, which is not versioned. Without the merge driver, `verification_ledger.json` text-merges silently and can drop rows — that is how main went red on 2026-08-07.

- [ ] **Step 2: Bring up the daemon in the worktree**

```bash
docker compose -f docker/docker-compose.yml up -d lean-repl
docker compose -f docker/docker-compose.yml logs -f lean-repl | grep -m1 READY
```

Every cheap readiness signal lies. The only sound check is an actual `lean-check.sh` round-trip, which Step 4 performs.

- [ ] **Step 3: Write the failing statement probe**

Write `<scratchpad>/probe1.lean`:

```lean
import Mathlib

open scoped NNReal

namespace Probe

abbrev Scenario (ι : Type*) := ι → ℝ≥0 → ℝ

inductive Payoff (ι : Type*) where
  | const (c : ℝ)
  | obs (i : ι) (t : ℝ≥0)
  | add (a b : Payoff ι)
  | sub (a b : Payoff ι)
  | mul (a b : Payoff ι)
  | max (a b : Payoff ι)
  | min (a b : Payoff ι)
  | indicatorLt (a b : Payoff ι)

noncomputable def Payoff.eval {ι : Type*} (s : Scenario ι) : Payoff ι → ℝ
  | .const c => c
  | .obs i t => s i t
  | .add a b => eval s a + eval s b
  | .sub a b => eval s a - eval s b
  | .mul a b => eval s a * eval s b
  | .max a b => Max.max (eval s a) (eval s b)
  | .min a b => Min.min (eval s a) (eval s b)
  | .indicatorLt a b => if eval s a < eval s b then 1 else 0

inductive Contract (ι : Type*) where
  | zero
  | pay (t : ℝ≥0) (amount : Payoff ι)
  | both (a b : Contract ι)
  | scale (c : ℝ) (a : Contract ι)

noncomputable def Contract.cashflows {ι : Type*} (s : Scenario ι) :
    Contract ι → List (ℝ≥0 × ℝ)
  | .zero => []
  | .pay t a => [(t, a.eval s)]
  | .both a b => cashflows s a ++ cashflows s b
  | .scale c a => (cashflows s a).map fun p ↦ (p.1, c * p.2)

noncomputable def Contract.pathPV {ι : Type*} (D : ℝ≥0 → ℝ) (s : Scenario ι)
    (c : Contract ι) : ℝ :=
  ((c.cashflows s).map fun p ↦ D p.1 * p.2).sum

theorem Contract.pathPV_both {ι : Type*} (D : ℝ≥0 → ℝ) (s : Scenario ι)
    (a b : Contract ι) :
    (Contract.both a b).pathPV D s = a.pathPV D s + b.pathPV D s := sorry

theorem Contract.pathPV_scale {ι : Type*} (D : ℝ≥0 → ℝ) (s : Scenario ι)
    (c : ℝ) (a : Contract ι) :
    (Contract.scale c a).pathPV D s = c * a.pathPV D s := sorry

end Probe
```

- [ ] **Step 4: Run the probe and confirm it elaborates with exactly two sorries**

```bash
./scripts/lean-check.sh <scratchpad>/probe1.lean
```

Expected: `{"success": true, ..., "sorry_count": 2}`.

If `success` is false, the *definitions* are wrong — fix those before touching the proofs. The likely failures are `Max.max`/`Min.min` needing explicit qualification because `Payoff.max` shadows them inside the namespace, and the `noncomputable` markers (`Real` has no executable `<` decision procedure, so `indicatorLt` forces `noncomputable` and pulls it up through `cashflows` and `pathPV`).

- [ ] **Step 5: Prove the two lemmas in the probe**

```lean
theorem Contract.pathPV_both {ι : Type*} (D : ℝ≥0 → ℝ) (s : Scenario ι)
    (a b : Contract ι) :
    (Contract.both a b).pathPV D s = a.pathPV D s + b.pathPV D s := by
  simp [pathPV, cashflows]

theorem Contract.pathPV_scale {ι : Type*} (D : ℝ≥0 → ℝ) (s : Scenario ι)
    (c : ℝ) (a : Contract ι) :
    (Contract.scale c a).pathPV D s = c * a.pathPV D s := by
  simp only [pathPV, cashflows, List.map_map]
  rw [← List.sum_map_mul_left]
  exact congrArg List.sum (List.map_congr_left fun p _ ↦ by ring)
```

`List.sum_map_mul_left` is the intended shape (`(l.map fun x ↦ a * f x).sum = a * (l.map f).sum`). Confirm the exact name and argument order in the daemon before relying on it — do not guess from memory. If it does not exist under that name, `induction (a.cashflows s)` with `simp [mul_add, mul_left_comm]` closes it directly.

- [ ] **Step 6: Run the probe and confirm zero sorries**

```bash
./scripts/lean-check.sh <scratchpad>/probe1.lean
```

Expected: `{"success": true, ..., "sorry_count": 0}`.

- [ ] **Step 7: Create the real module**

Create `MathFin/Contracts/Core.lean` with the copyright block, `module`, `public import Mathlib`, the module docstring below, `@[expose] public section`, `namespace MathFin.Contracts`, and the proven declarations from the probe (dropping the `Probe` namespace and the explicit `{ι : Type*}` binders in favour of a file-level `variable {ι : Type*}`).

The docstring must carry the attribution and the scope ceiling:

```lean
/-!
# A reified payoff language

`Payoff ι` and `Contract ι` represent *what an instrument pays*, independently of
any stochastic model. Market outcomes enter through `Scenario ι = ι → ℝ≥0 → ℝ`;
a stochastic model is a law on that type, and appears only from
`Contracts/Pricing.lean` onward.

Every other payoff in this library — `BlackScholes/Call.lean`, `Digital.lean`,
`CappedCall.lean` — is written inline as a lambda inside the integral that prices
it, so the payoff and the model are the same syntactic object. This file
separates them, which is what lets `Contracts/CappedCall.lean` price a capped
call by *composing* two European call values rather than by evaluating a third
integral.

## Deliberately absent

Branching contracts (`ifThen`), currency, and the lifecycle layer (outstanding
notional, termination, partial redemption). Each is additive and each waits for
the corpus entry that forces it; see
`docs/specs/2026-08-16-contracts-tower-design.md` §2.3.

## Main results

* `Contract.pathPV_both`, `Contract.pathPV_scale` — `pathPV` is additive over
  `both` and homogeneous over `scale`. These are what `Contracts/Pricing.lean`
  integrates to get linearity of `value`.

## Source

The layered separation of contract semantics from pricing semantics, and the
framing "the contract is not the model", are due to Paul Bilokon, *The Contract
Is Not the Model: Proof-Carrying Exotic Derivatives and the Economics of Model
Risk* (working paper, 9 August 2026; Mathematical Finance, Imperial College
London), with code at <https://github.com/thalesians/lean_contracts>
(Apache-2.0). That paper in turn builds on the compositional contract-DSL of
Peyton Jones, Eber and Seward (2000) and the certified-contract work of Bahr,
Berthold and Elsman (2015) and Annenkov (2018).

This file takes his separation of the payoff object from the probability law.
The type design is ours: a typed underlying index rather than `String` keys, a
single inductive rather than a mutual `NumExpr` / `BoolExpr` pair, and `ℝ≥0` time
matching `Filtration ℝ≥0 mΩ`.

No code is copied from `lean_contracts`; every definition and proof here is
written for this library. See `docs/specs/2026-08-16-contracts-tower-design.md`
§6 for the full credit line.
-/
```

- [ ] **Step 8: Add the umbrella import**

Append to `MathFin.lean`:

```lean
import MathFin.Contracts.Core
```

`MathFin.lean` is a **single-file bind mount**, so a rename-based write replaces the host inode and a running container keeps the old content. Re-sync it:

```bash
docker exec -i docker-lean-repl-1 sh -c 'cat > /app/MathFin.lean' < MathFin.lean
```

- [ ] **Step 9: Check the real module, then build**

```bash
./scripts/lean-check.sh MathFin/Contracts/Core.lean
docker compose -f docker/docker-compose.yml down lean-repl
docker compose -f docker/docker-compose.yml run --rm --entrypoint lake verify build MathFin
```

Expected: `lean-check` reports `sorry_count: 0`, and the build is green. The build is the gate that catches what the daemon's `autoImplicit true` hides.

- [ ] **Step 10: Commit**

```bash
git add MathFin/Contracts/Core.lean MathFin.lean docs/specs/2026-08-16-contracts-tower-design.md
git commit -m "feat(contracts): a reified payoff language and its cashflow semantics"
```

---

## Task 2: Adapted — the theorem that makes a contract an integrand

**Files:**
- Create: `MathFin/Contracts/Adapted.lean`
- Modify: `MathFin.lean`
- Probe: `<scratchpad>/probe2.lean`

**Interfaces:**
- Consumes: `Payoff`, `Payoff.eval`, `Scenario` from Task 1.
- Produces:
  - `Payoff.obsTimes : Payoff ι → List ℝ≥0`
  - `Payoff.measurable_eval (e) (X : ι → ℝ≥0 → Ω → ℝ) (hX : ∀ i t, Measurable (X i t)) : Measurable fun ω ↦ e.eval (fun i t ↦ X i t ω)`
  - `Payoff.measurable_eval_of_obsTimes_le (e) (𝓕 : Filtration ℝ≥0 mΩ) (X) (hX : ∀ i t, Measurable[𝓕 t] (X i t)) (hle : ∀ t ∈ e.obsTimes, t ≤ u) : Measurable[𝓕 u] fun ω ↦ e.eval (fun i t ↦ X i t ω)`

**Why this task exists.** The source paper's `Contract.observationTimes` feeds a syntactic chronology check discharged `by decide` — a linter with a proof term attached. The same function here is the hypothesis of an adaptedness theorem, which is what a payoff must satisfy to be an integrand at all. The source's `PricingModel.value` is a Bochner integral of a function never shown measurable; this task is the reason ours is not.

- [ ] **Step 1: Write the failing statement probe**

Write `<scratchpad>/probe2.lean`. Import `MathFin.Contracts.Core` (not `Mathlib` — the module re-exports it):

```lean
import MathFin.Contracts.Core

open MeasureTheory
open scoped NNReal

namespace MathFin.Contracts

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω}

def Payoff.obsTimes : Payoff ι → List ℝ≥0
  | .const _ => []
  | .obs _ t => [t]
  | .add a b | .sub a b | .mul a b | .max a b | .min a b | .indicatorLt a b =>
      a.obsTimes ++ b.obsTimes

theorem Payoff.measurable_eval (e : Payoff ι) (X : ι → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i t, Measurable (X i t)) :
    Measurable fun ω ↦ e.eval (fun i t ↦ X i t ω) := sorry

theorem Payoff.measurable_eval_of_obsTimes_le
    {𝓕 : Filtration ℝ≥0 mΩ} {u : ℝ≥0} (e : Payoff ι) (X : ι → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i t, Measurable[𝓕 t] (X i t))
    (hle : ∀ t ∈ e.obsTimes, t ≤ u) :
    Measurable[𝓕 u] fun ω ↦ e.eval (fun i t ↦ X i t ω) := sorry

end MathFin.Contracts
```

- [ ] **Step 2: Run the probe and confirm it elaborates with exactly two sorries**

```bash
./scripts/lean-check.sh <scratchpad>/probe2.lean
```

Expected: `{"success": true, ..., "sorry_count": 2}`.

If `Payoff.obsTimes` fails to compile, the grouped-alternative syntax (`| .add a b | .sub a b => …`) requires every grouped constructor to bind the same variable names in the same order — check that all six binary constructors are declared `(a b : Payoff ι)`.

- [ ] **Step 3: Prove `measurable_eval`**

```lean
theorem Payoff.measurable_eval (e : Payoff ι) (X : ι → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i t, Measurable (X i t)) :
    Measurable fun ω ↦ e.eval (fun i t ↦ X i t ω) := by
  induction e with
  | const c => exact measurable_const
  | obs i t => exact hX i t
  | add a b ha hb => exact ha.add hb
  | sub a b ha hb => exact ha.sub hb
  | mul a b ha hb => exact ha.mul hb
  | max a b ha hb => exact ha.max hb
  | min a b ha hb => exact ha.min hb
  | indicatorLt a b ha hb =>
      exact Measurable.ite (measurableSet_lt ha hb) measurable_const measurable_const
```

`measurableSet_lt` wants `{ω | f ω < g ω}` measurable from two measurable real functions; confirm its exact form in the daemon. `Measurable.ite` takes the `MeasurableSet` of the condition first.

- [ ] **Step 4: Prove `measurable_eval_of_obsTimes_le`**

Same induction, with the `obs` case doing the real work — the filtration is monotone, so `𝓕 t ≤ 𝓕 u` whenever `t ≤ u`:

```lean
theorem Payoff.measurable_eval_of_obsTimes_le
    {𝓕 : Filtration ℝ≥0 mΩ} {u : ℝ≥0} (e : Payoff ι) (X : ι → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i t, Measurable[𝓕 t] (X i t))
    (hle : ∀ t ∈ e.obsTimes, t ≤ u) :
    Measurable[𝓕 u] fun ω ↦ e.eval (fun i t ↦ X i t ω) := by
  induction e with
  | const c => exact measurable_const
  | obs i t =>
      exact (hX i t).mono (𝓕.mono (hle t (by simp [obsTimes]))) le_rfl
  | add a b ha hb =>
      exact (ha fun t ht ↦ hle t (by simp [obsTimes, ht])).add
        (hb fun t ht ↦ hle t (by simp [obsTimes, ht]))
  | sub a b ha hb =>
      exact (ha fun t ht ↦ hle t (by simp [obsTimes, ht])).sub
        (hb fun t ht ↦ hle t (by simp [obsTimes, ht]))
  | mul a b ha hb =>
      exact (ha fun t ht ↦ hle t (by simp [obsTimes, ht])).mul
        (hb fun t ht ↦ hle t (by simp [obsTimes, ht]))
  | max a b ha hb =>
      exact (ha fun t ht ↦ hle t (by simp [obsTimes, ht])).max
        (hb fun t ht ↦ hle t (by simp [obsTimes, ht]))
  | min a b ha hb =>
      exact (ha fun t ht ↦ hle t (by simp [obsTimes, ht])).min
        (hb fun t ht ↦ hle t (by simp [obsTimes, ht]))
  | indicatorLt a b ha hb =>
      exact Measurable.ite
        (measurableSet_lt (ha fun t ht ↦ hle t (by simp [obsTimes, ht]))
          (hb fun t ht ↦ hle t (by simp [obsTimes, ht])))
        measurable_const measurable_const
```

Note the induction hypotheses `ha`/`hb` are now *functions* of the `hle` restriction, because `hle` mentions `e`. If Lean does not generalise `hle` automatically, add `induction e generalizing u` or restructure as `induction e with … ` after `revert hle`. The six binary cases are identical up to one identifier — after it compiles, factor the repetition out (see Step 5).

- [ ] **Step 5: Cut the repetition**

Six identical branches is exactly the slop the values review's zero-slop lens catches. Extract the shared step:

```lean
  have sub_le {a b : Payoff ι} (h : ∀ t ∈ (Payoff.add a b).obsTimes, t ≤ u) :
      (∀ t ∈ a.obsTimes, t ≤ u) ∧ (∀ t ∈ b.obsTimes, t ≤ u) := by
    constructor <;> intro t ht <;> exact h t (by simp [Payoff.obsTimes, ht])
```

`obsTimes` is the same `a.obsTimes ++ b.obsTimes` for all six, so one helper stated at `add` reuses definitionally across the rest. If it does not, state the helper on the raw list instead: `(h : ∀ t ∈ l₁ ++ l₂, t ≤ u) → (∀ t ∈ l₁, t ≤ u) ∧ (∀ t ∈ l₂, t ≤ u)`, which is `List.mem_append` and is unconditionally reusable.

- [ ] **Step 6: Run the probe and confirm zero sorries**

```bash
./scripts/lean-check.sh <scratchpad>/probe2.lean
```

Expected: `{"success": true, ..., "sorry_count": 0}`.

- [ ] **Step 7: Create the real module and add the umbrella import**

Create `MathFin/Contracts/Adapted.lean` (copyright block, `module`, `public import MathFin.Contracts.Core`, docstring **ending with the `## Source` block from Global Constraints**, `@[expose] public section`). The docstring's "Main results" section must state plainly that `obsTimes` is a *syntactic* over-approximation of the times a payoff reads, and that the adaptedness theorem is therefore sufficient, not necessary.

Append `import MathFin.Contracts.Adapted` to `MathFin.lean` and re-sync the bind mount:

```bash
docker exec -i docker-lean-repl-1 sh -c 'cat > /app/MathFin.lean' < MathFin.lean
```

- [ ] **Step 8: Check, build, commit**

```bash
./scripts/lean-check.sh MathFin/Contracts/Adapted.lean
docker compose -f docker/docker-compose.yml down lean-repl
docker compose -f docker/docker-compose.yml run --rm --entrypoint lake verify build MathFin
git add MathFin/Contracts/Adapted.lean MathFin.lean
git commit -m "feat(contracts): payoff evaluation is measurable, and adapted to its observation times"
```

---

## Task 3: Pricing — value, its linearity, and the EMM seam

**Files:**
- Create: `MathFin/Contracts/Pricing.lean`
- Modify: `MathFin.lean`
- Probe: `<scratchpad>/probe3.lean`

**Interfaces:**
- Consumes: `Contract`, `Contract.pathPV`, `pathPV_both`, `pathPV_scale` (Task 1); `MathFin.ContinuousMarket.IsEMM` (`MathFin/Foundations/ContinuousMarket.lean:71`). It does **not** consume Task 2's measurability results: the `Integrable` hypotheses here are assumed, not derived. Task 5 Step 6 is where measurability would be used, if the integrability hypotheses get discharged there.
- Produces:
  - `Contract.value (Q : Measure Ω) (D : ℝ≥0 → ℝ) (X : ι → ℝ≥0 → Ω → ℝ) (c : Contract ι) : ℝ`
  - `Contract.value_both`, `Contract.value_scale`
  - `Contract.value_deliverAsset`

### ⚠ The spurious-guard trap in this file

The obvious martingale statement —

```lean
theorem value_process_martingale (hEMM : IsEMM S Q) (c : Contract ι) … :
    Martingale (fun t ↦ Q[fun ω ↦ c.pathPV D (scen X ω) | 𝓕 t]) 𝓕 Q
```

— **does not use `hEMM` at all.** It is `martingale_condExp`, which holds for the conditional expectation of *any* integrable function under *any* measure with a `SigmaFiniteFiltration`. Shipping it with an `IsEMM` hypothesis would assert that the martingale property is an EMM fact when it is a conditional-expectation fact, and every gate in this repo would pass it. That is precisely the failure recorded on 2026-07-31 (four of four drafts, all green).

So this task ships **two** theorems with **different** hypotheses:

1. `value_process_martingale` — no `IsEMM`, and a docstring saying why it needs none.
2. `value_deliverAsset` — the seam theorem, which genuinely consumes `hEMM.martingale`.

- [ ] **Step 1: Write the failing statement probe**

Write `<scratchpad>/probe3.lean`:

```lean
import MathFin.Contracts.Adapted
import MathFin.Foundations.ContinuousMarket

open MeasureTheory MathFin.ContinuousMarket
open scoped NNReal

namespace MathFin.Contracts

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The scenario read off a model at a single outcome. -/
def scenarioAt (X : ι → ℝ≥0 → Ω → ℝ) (ω : Ω) : Scenario ι := fun i t ↦ X i t ω

noncomputable def Contract.value (Q : Measure Ω) (D : ℝ≥0 → ℝ)
    (X : ι → ℝ≥0 → Ω → ℝ) (c : Contract ι) : ℝ :=
  ∫ ω, c.pathPV D (scenarioAt X ω) ∂Q

theorem Contract.value_scale (Q : Measure Ω) (D : ℝ≥0 → ℝ)
    (X : ι → ℝ≥0 → Ω → ℝ) (r : ℝ) (a : Contract ι) :
    (Contract.scale r a).value Q D X = r * a.value Q D X := sorry

theorem Contract.value_both (Q : Measure Ω) (D : ℝ≥0 → ℝ)
    (X : ι → ℝ≥0 → Ω → ℝ) (a b : Contract ι)
    (ha : Integrable (fun ω ↦ a.pathPV D (scenarioAt X ω)) Q)
    (hb : Integrable (fun ω ↦ b.pathPV D (scenarioAt X ω)) Q) :
    (Contract.both a b).value Q D X = a.value Q D X + b.value Q D X := sorry

theorem Contract.value_deliverAsset {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {S : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} (hEMM : IsEMM (P := P) (𝓕 := 𝓕) S Q)
    (T : ℝ≥0) :
    (Contract.pay T (Payoff.obs () T)).value Q (fun _ ↦ 1) (fun _ ↦ S)
      = ∫ ω, S 0 ω ∂Q := sorry

end MathFin.Contracts
```

Note `ι := Unit` is forced in `value_deliverAsset` by `Payoff.obs ()`; let Lean infer it rather than annotating.

- [ ] **Step 2: Run the probe and confirm it elaborates with exactly three sorries**

```bash
./scripts/lean-check.sh <scratchpad>/probe3.lean
```

Expected: `{"success": true, ..., "sorry_count": 3}`.

The likely failure is the implicit-argument shape of `IsEMM`: it is stated with `{P : Measure Ω}` and `{𝓕 : Filtration ℝ≥0 mΩ}` as section variables over a general inner-product-space-valued `S`, so at `F = ℝ` the instances must resolve. Read `MathFin/Foundations/ContinuousMarket.lean:60-78` for the exact `variable` block before adjusting.

- [ ] **Step 3: Prove `value_scale` and `value_both`**

```lean
theorem Contract.value_scale (Q : Measure Ω) (D : ℝ≥0 → ℝ)
    (X : ι → ℝ≥0 → Ω → ℝ) (r : ℝ) (a : Contract ι) :
    (Contract.scale r a).value Q D X = r * a.value Q D X := by
  simp only [value, Contract.pathPV_scale]
  exact integral_const_mul r _

theorem Contract.value_both (Q : Measure Ω) (D : ℝ≥0 → ℝ)
    (X : ι → ℝ≥0 → Ω → ℝ) (a b : Contract ι)
    (ha : Integrable (fun ω ↦ a.pathPV D (scenarioAt X ω)) Q)
    (hb : Integrable (fun ω ↦ b.pathPV D (scenarioAt X ω)) Q) :
    (Contract.both a b).value Q D X = a.value Q D X + b.value Q D X := by
  simp only [value, Contract.pathPV_both]
  exact integral_add ha hb
```

`value_scale` needs no integrability — `integral_const_mul` holds unconditionally in Mathlib's Bochner integral, which returns `0` for non-integrable functions. `value_both` genuinely needs both hypotheses: `integral_add` is false without them. State that asymmetry in the docstring; it is the honest content of "linearity" here.

- [ ] **Step 4: Prove `value_deliverAsset`**

Reduce the left side to `∫ ω, S T ω ∂Q`, then apply the martingale property between `0` and `T`:

```lean
theorem Contract.value_deliverAsset … : … := by
  have h0T : (0 : ℝ≥0) ≤ T := zero_le _
  simp only [value, Contract.pathPV, Contract.cashflows, Payoff.eval, scenarioAt,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero]
  exact (hEMM.martingale.integral_eq h0T).symm
```

`Martingale.integral_eq` may not exist under that name. The reliable route is the defining property: `hEMM.martingale.condExp_ae_eq h0T : Q[S T | 𝓕 0] =ᵐ[Q] S 0`, then `integral_condExp` to get `∫ Q[S T | 𝓕 0] = ∫ S T`, and chain. Search the daemon for the available `Martingale` API before committing to a route; do not invent a lemma name.

- [ ] **Step 5: Add the martingale value process — with the honest hypotheses**

Add, and note that `hEMM` is deliberately *not* a hypothesis:

```lean
/-- The conditional-expectation value process of any integrable contract is a
`Q`-martingale. This needs **no** EMM hypothesis: it is a property of conditional
expectation, not of the pricing measure. `value_deliverAsset` is the statement in
this file that actually consumes `IsEMM`. -/
theorem Contract.value_process_martingale {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    [SigmaFiniteFiltration Q 𝓕] (D : ℝ≥0 → ℝ) (X : ι → ℝ≥0 → Ω → ℝ)
    (c : Contract ι) :
    Martingale (fun t ↦ Q[fun ω ↦ c.pathPV D (scenarioAt X ω) | 𝓕 t]) 𝓕 Q :=
  martingale_condExp _ 𝓕 Q
```

Use the **minimal** typeclass the callee needs — `SigmaFiniteFiltration`, not `IsFiniteMeasure`.

- [ ] **Step 6: Drop-and-reprove every hypothesis**

For each of the five hypotheses across the four theorems (`ha`, `hb`, `hEMM`, `[SigmaFiniteFiltration]`, `D`'s use in `value_deliverAsset`), delete it and re-run the proof in the probe. Any hypothesis whose deletion still leaves a green proof must be removed from the shipped statement. Record the result of each drop in the commit body.

- [ ] **Step 7: Run the probe, create the module, build, commit**

```bash
./scripts/lean-check.sh <scratchpad>/probe3.lean          # sorry_count: 0
# create MathFin/Contracts/Pricing.lean (docstring MUST end with the ## Source block), append umbrella import
docker exec -i docker-lean-repl-1 sh -c 'cat > /app/MathFin.lean' < MathFin.lean
./scripts/lean-check.sh MathFin/Contracts/Pricing.lean
docker compose -f docker/docker-compose.yml down lean-repl
docker compose -f docker/docker-compose.yml run --rm --entrypoint lake verify build MathFin
git add MathFin/Contracts/Pricing.lean MathFin.lean
git commit -m "feat(contracts): contract value, its linearity, and the EMM seam"
```

---

## Task 4: Black–Scholes instances — the reified call, put and digital

**Files:**
- Create: `MathFin/Contracts/BlackScholes.lean`
- Modify: `MathFin.lean`
- Probe: `<scratchpad>/probe4.lean`

**Interfaces:**
- Consumes: `Contract.value` (Task 3); `MathFin.BSCallHyp`, `MathFin.bsd1`, `MathFin.bsd2`, `MathFin.bsTerminal` (`MathFin/BlackScholes/Call.lean:88,102,107`); `MathFin.Phi` (`MathFin/Foundations/StandardNormal.lean:53`); `MathFin.bs_call_formula`, `MathFin.bs_put_formula`, `MathFin.bs_cash_or_nothing_formula` (`MathFin/BlackScholes/Digital.lean:67`).
- Produces: `bsAssets`, `europeanCall`, `europeanPut`, `digitalCall`, `value_europeanCall`, `value_europeanPut`, `value_digitalCall`.

- [ ] **Step 1: Read the three target theorems before writing anything**

```bash
sed -n '85,115p' MathFin/BlackScholes/Call.lean
sed -n '60,75p'  MathFin/BlackScholes/Digital.lean
grep -n 'theorem bs_call_formula' -A 12 MathFin/BlackScholes/Call.lean
grep -n 'theorem bs_put_formula'  -A 12 MathFin/BlackScholes/Put.lean
```

Copy the exact statement of each right-hand side into the probe. Do not retype it from the benchmark `description` — the description is prose and may be weaker or stronger than the statement.

- [ ] **Step 2: Write the failing statement probe**

Write `<scratchpad>/probe4.lean`:

```lean
import MathFin.Contracts.Pricing
import MathFin.BlackScholes.Digital
import MathFin.BlackScholes.Put

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace MathFin.Contracts

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The single-asset Black–Scholes market as a model map. Every instrument in
this file observes only at `T`, so the value at other times is irrelevant; a
path-dependent instance needs the full GBM path and is deferred. -/
noncomputable def bsAssets (S_0 r σ T : ℝ) (Z : Ω → ℝ) : Unit → ℝ≥0 → Ω → ℝ :=
  fun _ _ ω ↦ bsTerminal S_0 r σ T (Z ω)

noncomputable def europeanCall (K : ℝ) (T : ℝ≥0) : Contract Unit :=
  .pay T (.max (.sub (.obs () T) (.const K)) (.const 0))

noncomputable def europeanPut (K : ℝ) (T : ℝ≥0) : Contract Unit :=
  .pay T (.max (.sub (.const K) (.obs () T)) (.const 0))

noncomputable def digitalCall (K : ℝ) (T : ℝ≥0) : Contract Unit :=
  .pay T (.indicatorLt (.const K) (.obs () T))

theorem value_europeanCall {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ : ℝ} {T : ℝ≥0} {Z : Ω → ℝ} (h : BSCallHyp Q S_0 K r σ T Z) :
    (europeanCall K T).value Q (fun _ ↦ Real.exp (-r * T)) (bsAssets S_0 r σ T Z)
      = S_0 * Phi (bsd1 S_0 K r σ T) - K * Real.exp (-r * T) * Phi (bsd2 S_0 K r σ T) :=
  sorry

theorem value_digitalCall {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ : ℝ} {T : ℝ≥0} {Z : Ω → ℝ} (h : BSCallHyp Q S_0 K r σ T Z) :
    (digitalCall K T).value Q (fun _ ↦ Real.exp (-r * T)) (bsAssets S_0 r σ T Z)
      = Real.exp (-r * T) * Phi (bsd2 S_0 K r σ T) := sorry

theorem value_europeanPut {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ : ℝ} {T : ℝ≥0} {Z : Ω → ℝ} (h : BSCallHyp Q S_0 K r σ T Z) :
    (europeanPut K T).value Q (fun _ ↦ Real.exp (-r * T)) (bsAssets S_0 r σ T Z)
      = K * Real.exp (-r * T) * Phi (-(bsd2 S_0 K r σ T)) - S_0 * Phi (-(bsd1 S_0 K r σ T)) :=
  sorry

end MathFin.Contracts
```

The `T : ℝ≥0` in the contract and the `T : ℝ` in `BSCallHyp` are bridged by the `ℝ≥0 → ℝ` coercion. Write `T` bare everywhere and let Lean insert `↑` — do **not** hand-write the arrow.

- [ ] **Step 3: Run the probe and confirm it elaborates with exactly three sorries**

```bash
./scripts/lean-check.sh <scratchpad>/probe4.lean
```

Expected: `{"success": true, ..., "sorry_count": 3}`.

If the right-hand sides do not elaborate, the argument order of `bsd1`/`bsd2` or the shape of `BSCallHyp` differs from what Step 1 read. Fix the statement, not the source theorem.

- [ ] **Step 4: Prove `value_europeanCall`**

The whole proof is: unfold the contract semantics until the integrand is literally `bs_call_formula`'s, then apply it.

```lean
theorem value_europeanCall … := by
  simp only [Contract.value, Contract.pathPV, Contract.cashflows, europeanCall,
    Payoff.eval, scenarioAt, bsAssets, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  exact MathFin.bs_call_formula h
```

If the final `exact` fails on `max (x - K) 0` versus `max (x - K) 0` up to argument order or `sub_eq_add_neg` normalisation, insert a `show` with the exact integrand copied from `Call.lean` and close with `MathFin.bs_call_formula h` after it. Prefer `show … from` over building a `have`-ladder.

- [ ] **Step 5: Prove `value_digitalCall`**

The one real step is `indicatorLt (const K) (obs () T)` ↦ `(Set.Ioi K).indicator (fun _ ↦ 1)`:

```lean
theorem value_digitalCall … := by
  have hind (x : ℝ) :
      (if K < x then (1 : ℝ) else 0)
        = (Set.Ioi K).indicator (fun _ ↦ (1 : ℝ)) x := by
    simp [Set.indicator_apply, Set.mem_Ioi]
  simp only [Contract.value, Contract.pathPV, Contract.cashflows, digitalCall,
    Payoff.eval, scenarioAt, bsAssets, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, hind]
  exact MathFin.bs_cash_or_nothing_formula h
```

- [ ] **Step 6: Prove `value_europeanPut`**

Identical in shape to Step 4 against `MathFin.bs_put_formula h`. Write it out; do not write "as in Step 4".

```lean
theorem value_europeanPut … := by
  simp only [Contract.value, Contract.pathPV, Contract.cashflows, europeanPut,
    Payoff.eval, scenarioAt, bsAssets, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  exact MathFin.bs_put_formula h
```

- [ ] **Step 7: Fold the three proofs if they are the same shape**

If Steps 4, 5 and 6 differ only in the closing `exact`, extract the `simp only` list into a single `Contract.value_pay_simps` simp set or a private lemma

```lean
private theorem value_pay_eq (Q : Measure Ω) (D : ℝ≥0 → ℝ)
    (X : ι → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (a : Payoff ι) :
    (Contract.pay t a).value Q D X = ∫ ω, D t * a.eval (scenarioAt X ω) ∂Q := by
  simp [Contract.value, Contract.pathPV, Contract.cashflows]
```

and rewrite each instance through it. Three copies of an eleven-lemma `simp only` list is the kind of thing the zero-slop lens exists to catch.

- [ ] **Step 8: Run the probe, create the module, build, commit**

```bash
./scripts/lean-check.sh <scratchpad>/probe4.lean          # sorry_count: 0
# create MathFin/Contracts/BlackScholes.lean (docstring MUST end with the ## Source block), append umbrella import
docker exec -i docker-lean-repl-1 sh -c 'cat > /app/MathFin.lean' < MathFin.lean
./scripts/lean-check.sh MathFin/Contracts/BlackScholes.lean
docker compose -f docker/docker-compose.yml down lean-repl
docker compose -f docker/docker-compose.yml run --rm --entrypoint lake verify build MathFin
git add MathFin/Contracts/BlackScholes.lean MathFin.lean
git commit -m "feat(contracts): the reified call, put and digital price to their closed forms"
```

---

## Task 5: The capped call — the compositionality payoff

**Files:**
- Create: `MathFin/Contracts/CappedCall.lean`
- Modify: `MathFin.lean`
- Probe: `<scratchpad>/probe5.lean`

**Interfaces:**
- Consumes: `europeanCall`, `value_europeanCall`, `bsAssets` (Task 4); `Contract.value_both`, `Contract.value_scale` (Task 3); `MathFin.cappedCall_eq_bull_spread` (`MathFin/BlackScholes/CappedCall.lean:32`).
- Produces: `cappedCall`, `cappedCall_payoff_eq`, `value_cappedCall`.

**This is the headline result of the tower.** `CappedCall.lean:32` currently proves `cappedCall_eq_bull_spread` as a pointwise real identity and stops, because there is no object on which to say "the value of a sum is the sum of the values". Here the capped call is *defined* as a composed contract, and its price is obtained without evaluating a third integral.

**Two theorems, and the second is worthless without the first.** `value_cappedCall` alone proves the value of a bull spread, and naming that definition `cappedCall` would be prose outrunning the statement. `cappedCall_payoff_eq` is what earns the name.

- [ ] **Step 1: Read the existing identity**

```bash
sed -n '25,50p' MathFin/BlackScholes/CappedCall.lean
```

Record the exact form — in particular which of `min (max (S - K₁) 0) (K₂ - K₁)` or `max (S-K₁) 0 - max (S-K₂) 0` is on which side, and the direction of the `K₁ ≤ K₂` hypothesis.

- [ ] **Step 2: Write the failing statement probe**

Write `<scratchpad>/probe5.lean`:

```lean
import MathFin.Contracts.BlackScholes
import MathFin.BlackScholes.CappedCall

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace MathFin.Contracts

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A capped call struck at `K₁` and capped at `K₂`, built as a long call at `K₁`
and a short call at `K₂`. `cappedCall_payoff_eq` proves this composed object
really does pay `min (max (S - K₁) 0) (K₂ - K₁)`. -/
noncomputable def cappedCall (K₁ K₂ : ℝ) (T : ℝ≥0) : Contract Unit :=
  .both (europeanCall K₁ T) (.scale (-1) (europeanCall K₂ T))

theorem cappedCall_payoff_eq {K₁ K₂ : ℝ} (h : K₁ ≤ K₂) {T : ℝ≥0}
    (s : Scenario Unit) :
    (cappedCall K₁ K₂ T).pathPV (fun _ ↦ 1) s
      = min (max (s () T - K₁) 0) (K₂ - K₁) := sorry

theorem value_cappedCall {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K₁ K₂ r σ : ℝ} {T : ℝ≥0} {Z : Ω → ℝ}
    (h₁ : BSCallHyp Q S_0 K₁ r σ T Z) (h₂ : BSCallHyp Q S_0 K₂ r σ T Z)
    (hi₁ : Integrable (fun ω ↦ (europeanCall K₁ T).pathPV
      (fun _ ↦ Real.exp (-r * T)) (scenarioAt (bsAssets S_0 r σ T Z) ω)) Q)
    (hi₂ : Integrable (fun ω ↦ ((Contract.scale (-1) (europeanCall K₂ T))).pathPV
      (fun _ ↦ Real.exp (-r * T)) (scenarioAt (bsAssets S_0 r σ T Z) ω)) Q) :
    (cappedCall K₁ K₂ T).value Q (fun _ ↦ Real.exp (-r * T)) (bsAssets S_0 r σ T Z)
      = (S_0 * Phi (bsd1 S_0 K₁ r σ T) - K₁ * Real.exp (-r * T) * Phi (bsd2 S_0 K₁ r σ T))
      - (S_0 * Phi (bsd1 S_0 K₂ r σ T) - K₂ * Real.exp (-r * T) * Phi (bsd2 S_0 K₂ r σ T)) :=
  sorry

end MathFin.Contracts
```

- [ ] **Step 3: Run the probe and confirm two sorries**

```bash
./scripts/lean-check.sh <scratchpad>/probe5.lean
```

Expected: `{"success": true, ..., "sorry_count": 2}`.

- [ ] **Step 4: Prove `cappedCall_payoff_eq`**

```lean
theorem cappedCall_payoff_eq {K₁ K₂ : ℝ} (h : K₁ ≤ K₂) {T : ℝ≥0}
    (s : Scenario Unit) :
    (cappedCall K₁ K₂ T).pathPV (fun _ ↦ 1) s
      = min (max (s () T - K₁) 0) (K₂ - K₁) := by
  simp only [cappedCall, Contract.pathPV_both, Contract.pathPV_scale,
    Contract.pathPV, Contract.cashflows, europeanCall, Payoff.eval,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero]
  linarith [MathFin.cappedCall_eq_bull_spread (s () T) K₁ K₂ h]
```

Adjust the final step to the exact orientation Step 1 recorded: if `cappedCall_eq_bull_spread` already states the goal modulo `a + (-1) * b = a - b`, close with `simpa using MathFin.cappedCall_eq_bull_spread (s () T) K₁ K₂ h` and drop the `linarith`.

- [ ] **Step 5: Prove `value_cappedCall` by composition**

```lean
theorem value_cappedCall … := by
  rw [cappedCall, Contract.value_both _ _ _ _ _ hi₁ hi₂,
    Contract.value_scale, value_europeanCall h₁, value_europeanCall h₂]
  ring
```

If the `-1` scaling leaves `-1 * x` rather than `-x`, `ring` closes it. This proof must contain **no integral manipulation at all** — if it does, the composition is not doing the work and Task 3's `value_both`/`value_scale` are the wrong shape.

- [ ] **Step 6: Try to discharge the integrability hypotheses**

`hi₁` and `hi₂` are ugly. Try to derive them from `h₁`/`h₂`: `BSCallHyp` carries `HasLaw Z (gaussianReal 0 1) Q`, and the call payoff is dominated by `bsTerminal`, whose exponential moment the library already has (`MathFin/Foundations/BrownianExpMoment.lean`). If a clean derivation exists, remove `hi₁`/`hi₂` from the statement. If it does not, keep them and say so in the docstring — an unnecessary hypothesis and an undischargeable one are different failures, and only the first is slop.

- [ ] **Step 7: Run the probe, create the module, build, commit**

```bash
./scripts/lean-check.sh <scratchpad>/probe5.lean          # sorry_count: 0
# create MathFin/Contracts/CappedCall.lean (docstring MUST end with the ## Source block), append umbrella import
docker exec -i docker-lean-repl-1 sh -c 'cat > /app/MathFin.lean' < MathFin.lean
./scripts/lean-check.sh MathFin/Contracts/CappedCall.lean
docker compose -f docker/docker-compose.yml down lean-repl
docker compose -f docker/docker-compose.yml run --rm --entrypoint lake verify build MathFin
git add MathFin/Contracts/CappedCall.lean MathFin.lean
git commit -m "feat(contracts): the capped call priced by composing two European calls"
```

---

## Task 6: Corpus, ledger, axiom audit, gates

**Files:**
- Modify: `benchmarks/mathematical_finance.json` (8 new entries)
- Regenerate: `MathFin/AxiomAuditGen.lean`
- Modify: `verification_ledger.json` (by tool, never by hand)

**Interfaces:**
- Consumes: every public theorem from Tasks 1–5.
- Produces: 8 corpus entries with ids `mf-contract-pathpv-both`, `mf-contract-eval-adapted`, `mf-contract-value-linear`, `mf-contract-value-deliver-asset`, `mf-contract-european-call`, `mf-contract-european-put`, `mf-contract-digital-cash-or-nothing`, `mf-contract-capped-call`.

- [ ] **Step 1: Write the eight entries**

Each entry has `id`, `name`, `description`, `domain: "mathematical_finance"`, `code.lean`, and `metadata` with `chapter`, `reference`, `difficulty`, `formalization_status`, `formalization_scope`. **Every one of the eight `reference` fields names the source paper** in the form shown below — the corpus ships in the HF dataset, so the citation must travel with the claim, not sit only in the Lean source. Model on the existing `mf-bs-put-formula` entry. The snippet imports the MathFin module and re-exports the lemma — it does **not** `import Mathlib` (the module's `public import Mathlib` re-exports it).

The headline entry, in full:

```json
{
  "id": "mf-contract-capped-call",
  "name": "Capped Call as a Composed Contract",
  "description": "The capped call, defined as a long call at K1 plus a short call at K2, pays min(max(S_T - K1, 0), K2 - K1) in every scenario, and its Black-Scholes value is the difference of the two European call values -- obtained by linearity of the value functional, with no third integral evaluated.",
  "domain": "mathematical_finance",
  "code": {
    "lean": "import MathFin.Contracts.CappedCall\n\nopen MeasureTheory ProbabilityTheory Real\nopen scoped NNReal\nopen MathFin MathFin.Contracts\n\nvariable {Ω : Type*} {mΩ : MeasurableSpace Ω}\n\n/-- The composed contract really pays the capped-call payoff. -/\ntheorem cappedCall_payoff_eq' {K₁ K₂ : ℝ} (h : K₁ ≤ K₂) {T : ℝ≥0}\n    (s : Scenario Unit) :\n    (cappedCall K₁ K₂ T).pathPV (fun _ ↦ 1) s\n      = min (max (s () T - K₁) 0) (K₂ - K₁) :=\n  MathFin.Contracts.cappedCall_payoff_eq h s\n"
  },
  "metadata": {
    "chapter": 9,
    "reference": "Capped call / bull spread decomposition (Hull 12.3). Contract-reification framing after P. Bilokon, The Contract Is Not the Model (working paper, 2026), github.com/thalesians/lean_contracts (Apache-2.0); no code copied.",
    "difficulty": "advanced",
    "formalization_status": "full",
    "formalization_scope": "Full formal proof. Two theorems in MathFin/Contracts/CappedCall.lean: cappedCall_payoff_eq identifies the composed contract's pathwise payoff with the capped-call payoff, and value_cappedCall prices it as the difference of two European call values via linearity of the value functional. The value theorem carries explicit integrability hypotheses on each leg. The contract observes the underlying only at T; calendars, business-day conventions and early exercise are outside the language. Axioms-clean."
  }
}
```


The eight entries, each re-exporting exactly one theorem:

| id | re-exports | import |
|---|---|---|
| `mf-contract-pathpv-both` | `Contract.pathPV_both` | `MathFin.Contracts.Core` |
| `mf-contract-eval-adapted` | `Payoff.measurable_eval_of_obsTimes_le` | `MathFin.Contracts.Adapted` |
| `mf-contract-value-linear` | `Contract.value_both` | `MathFin.Contracts.Pricing` |
| `mf-contract-value-deliver-asset` | `Contract.value_deliverAsset` | `MathFin.Contracts.Pricing` |
| `mf-contract-european-call` | `value_europeanCall` | `MathFin.Contracts.BlackScholes` |
| `mf-contract-european-put` | `value_europeanPut` | `MathFin.Contracts.BlackScholes` |
| `mf-contract-digital-cash-or-nothing` | `value_digitalCall` | `MathFin.Contracts.BlackScholes` |
| `mf-contract-capped-call` | `cappedCall_payoff_eq` | `MathFin.Contracts.CappedCall` |

Each snippet restates the theorem's full signature and closes with the bare
qualified term (`MathFin.Contracts.<name> <args>`), never `by exact`. Copy each
signature from the module you wrote it in — do not retype it from memory.

**The `description` states what the entry proves, not the textbook theorem it is named after.** It ships in the HF dataset, so it is an outward-facing claim.

- [ ] **Step 2: Verify each snippet elaborates**

```bash
docker compose -f docker/docker-compose.yml up -d lean-repl
for id in mf-contract-pathpv-both mf-contract-eval-adapted mf-contract-value-linear \
          mf-contract-value-deliver-asset mf-contract-european-call \
          mf-contract-european-put mf-contract-digital-cash-or-nothing \
          mf-contract-capped-call; do
  echo "=== $id"; ./scripts/bench-check.sh benchmarks/mathematical_finance.json "$id"
done
```

Expected: eight `{"success": true, ..., "sorry_count": 0}`. Library-green is not corpus-green — only this loop catches a snippet that does not elaborate.

- [ ] **Step 3: Regenerate the exhaustive axiom audit**

```bash
docker compose -f docker/docker-compose.yml down lean-repl
python3 -m tools.verify.axiom_audit_gen --write
```

This pins every proof-position MathFin constant the corpus cites. `tests/test_values.py` enforces its byte-freshness after any benchmark edit. Note that the generator only catches **qualified** `:= MathFin.X` bodies — a snippet whose body is a tactic proof contributes nothing, which is fine here since all eight re-export.

- [ ] **Step 4: Run the full gate suite**

```bash
docker compose -f docker/docker-compose.yml run --rm \
  --entrypoint python3 verify -m pytest tests/ -q
python3 -m tools.verify.ledger status
```

Expected: pytest green; `ledger status` reports the eight new entries as `missing`.

- [ ] **Step 5: Verify the new ledger rows**

```bash
docker compose -f docker/docker-compose.yml up -d lean-repl
python3 -m tools.verify.ledger verify
python3 -m tools.verify.ledger status      # must exit 0
```

- [ ] **Step 6: Write the attribution gate**

Attribution that depends on remembering to write it is attribution that will be
dropped by the first refactor. Add to `tests/test_values.py`:

```python
CONTRACTS_DIR = REPO_ROOT / "MathFin" / "Contracts"
SOURCE_MARKERS = (
    "Bilokon",
    "The Contract Is Not the Model",
    "github.com/thalesians/lean_contracts",
    "Apache-2.0",
    "No code is copied",
)


def test_contracts_cite_source() -> None:
    # Every Contracts/ module credits the work it derives from.
    #
    # The tower's design is Bilokon's (working paper, 9 August 2026); the Lean
    # is ours. A module that carries the design without the credit line is the
    # exact failure this gate exists to prevent, and a reader of one file must
    # not have to find the credit in a different one.
    modules = sorted(CONTRACTS_DIR.glob("*.lean"))
    assert modules, "no modules found under MathFin/Contracts/"
    for path in modules:
        text = path.read_text()
        missing = [m for m in SOURCE_MARKERS if m not in text]
        assert not missing, (
            f"{path.relative_to(REPO_ROOT)} is missing its source attribution: "
            f"{missing}. Every MathFin/Contracts/*.lean docstring must end with "
            "the ## Source block (see the plan's Global Constraints and "
            "docs/specs/2026-08-16-contracts-tower-design.md section 6)."
        )


def test_contracts_corpus_entries_cite_source() -> None:
    # The citation ships with the claim in the HF dataset, not only in the Lean.
    for entry in iter_entries():
        if not entry["id"].startswith("mf-contract-"):
            continue
        ref = entry.get("metadata", {}).get("reference", "")
        assert "Bilokon" in ref, (
            f"{entry['id']}: metadata.reference must name the source paper - "
            "the corpus is published, so the credit must travel with the claim"
        )
```

Run it red first, by temporarily deleting the `## Source` block from one module:

```bash
docker compose -f docker/docker-compose.yml run --rm \
  --entrypoint python3 verify -m pytest tests/test_values.py -k contracts -q
```

Expected: FAIL naming that module. Restore the block, re-run, expect PASS. A gate
never seen to fail is not known to work.

- [ ] **Step 7: Add the curated headliner**

Add `MathFin/Contracts/CappedCall.lean`'s two theorems to the curated `MathFin/AxiomAudit.lean` with a `#guard_msgs`-pinned `#print axioms`, alongside a short prose paragraph in the file's existing register explaining what the tower buys. `MathFin/AxiomAuditGen.lean` is generated and must never be hand-edited; `AxiomAudit.lean` is the storied file and is hand-written.

- [ ] **Step 8: Build and commit**

```bash
docker compose -f docker/docker-compose.yml down lean-repl
docker compose -f docker/docker-compose.yml run --rm --entrypoint lake verify build MathFin
docker compose -f docker/docker-compose.yml run --rm --entrypoint lake verify lint
git add benchmarks/mathematical_finance.json MathFin/AxiomAuditGen.lean \
        MathFin/AxiomAudit.lean verification_ledger.json
git commit -m "feat(corpus): eight entries for the contracts tower"
```

`lake lint` runs in CI but not in `lake build`. Run both before pushing.

---

## Task 7: Documentation, and the prose-vs-statement pass

**Files:**
- Modify: `docs/bridges.md`, `docs/coverage.md`, `docs/patterns.md`, `docs/roadmap.md`, `docs/mathematical-architecture.md`, `README.md`

Every phase is a complete repo upgrade, not just the Lean.

- [ ] **Step 1: `docs/bridges.md`**

Add a row for the Contracts→BlackScholes bridge: which two modules it joins, which theorem is the join (`value_europeanCall`), and what it buys (a reified instrument whose price is a proved closed form). Add a second row for Contracts→Foundations via `value_deliverAsset`.

- [ ] **Step 2: `docs/coverage.md`**

Add the eight entries with their `formalization_status`, and state the ceiling in the same paragraph: payoff kernels over a finite observation grid, single-asset, no calendars, no lifecycle.

- [ ] **Step 3: `docs/patterns.md`**

Add a dated batch with the two patterns this phase produced:

1. **Statement-first probing in a scratch file** as the Lean substitute for a failing test, and why `sorry_count: 1` is the green light rather than a failure.
2. **Reify-then-reduce**: to price a reified instrument, `simp only` the contract semantics until the integrand is syntactically the existing theorem's, then `exact` it. Include the `value_pay_eq` helper from Task 4 Step 7 as the reusable form.

`patterns.md` is a first-class citizen: consult it before proofs, update it in the same flow.

- [ ] **Step 4: `docs/roadmap.md` and `docs/mathematical-architecture.md`**

Record the tower as delivered, and record the two deferred rungs with their forcing cases: **branching contracts + the lifecycle state machine** (forced by the first autocall entry) and **path-dependent instances** (forced by wiring `bsAssets` to the full GBM path rather than the terminal value).

- [ ] **Step 5: `README.md` landmark table**

Add one row. Render the theorem as what it *is*: "a reified capped call whose Black–Scholes value is the difference of two European call values, by linearity". Do not render it as "structured products formally verified".

The row's reference column names the source paper (Bilokon 2026) and links `docs/sources.md`. The landmark table is the most-read surface in the repository; a credit that appears everywhere except there is a credit most readers never see.

- [ ] **Step 6: Create `docs/sources.md`**

The library has consulted external formalisations twice now and recorded it
nowhere central. Create the catalogue, seeded with both:

````markdown
# External sources

Formalisations and papers this library has learned from. For each: what was
taken, what was not, and where the credit lives in the code.

**The rule.** An external formalisation is a *source*, not a template. We design
in our own idiom and cite by name. We do not copy code; if we ever do, the copied
region is marked in-file, its licence header is retained, and a `NOTICE` entry is
added.

## Bilokon, *The Contract Is Not the Model* (2026)

Paul Bilokon, *The Contract Is Not the Model: Proof-Carrying Exotic Derivatives
and the Economics of Model Risk*, working paper, 9 August 2026. Mathematical
Finance, Department of Mathematics, Imperial College London.
Code: <https://github.com/thalesians/lean_contracts>, Apache-2.0.

**Taken** (as ideas, credited in every `MathFin/Contracts/*.lean` docstring): the
"contract is not the model" thesis; the five-layer decomposition; contract-semantic
risk as a named category; unmodelled clauses as first-class data; the
lifecycle-as-state-machine design — not yet built, and when it is, it is built as
his design.

**Not taken:** no code. Our type design (typed underlying index, `ℝ≥0` time, a
single inductive), the measurability and adaptedness theorems, and the reduction
of reified instruments to our existing Black–Scholes closed forms have no
counterpart in the source.

**Onward credit:** that paper builds on Peyton Jones, Eber and Seward (2000);
Bahr, Berthold and Elsman (2015); Annenkov (2018); and Arusoaie et al. (Findel).
Cite the tradition, not only the nearest author.

**In the code:** the `## Source` blocks in `MathFin/Contracts/*.lean` (gated by
`tests/test_values.py::test_contracts_cite_source`); `metadata.reference` on every
`mf-contract-*` corpus entry (gated by
`test_contracts_corpus_entries_cite_source`);
`docs/specs/2026-08-16-contracts-tower-design.md` section 6.

## AFP `Survival_Model`

Consulted for the actuarial survival layer (2026-07-11). Our design, our Lean; the
AFP entry was a source for the mathematical content, not a port. See the
`MathFin/Actuarial/` module docstrings.
````

- [ ] **Step 7: The prose-vs-statement pass — the last step before anything is called done**

For every docstring, corpus `description`, and doc paragraph this phase touched, open it beside the Lean statement and ask whether the prose claims more than the Lean proves. Specific traps in this phase:

- "contract semantics" must not be read as "legal terms". Nothing here reads a term sheet.
- "priced under Black–Scholes" is true only under `BSCallHyp`, which is a hypothesis, not a proved model.
- "the value process is a martingale" must not be attached to `IsEMM` (Task 3's trap).
- "capped call" must be earned by `cappedCall_payoff_eq`, not asserted by the definition's name.
- `value_cappedCall`'s integrability hypotheses must appear in the `formalization_scope`, not be silently dropped.

```bash
docker compose -f docker/docker-compose.yml run --rm \
  --entrypoint python3 verify -m pytest tests/test_values.py -q
```

The mechanical slice is `test_prose_does_not_outrun_statement`; the rest is judgment and it is done **before** the values review's lenses, not after.

- [ ] **Step 8: Values review cadence check**

```bash
python3 -m tools.verify.coverage_report
```

`REVIEW_SLACK_ENTRIES = 12`; the newest recorded review covers corpus **351** against a live corpus of **353**. Eight entries reaches 361 — inside slack, so this phase does not trip the gate, but the next one will. If `test_values_review_is_current` fails, run the multi-agent panel per `docs/values-review.md` and record a ranked backlog plus the upgrades executed — never an "8/8 PASS".

- [ ] **Step 9: Commit**

```bash
git add docs/bridges.md docs/coverage.md docs/patterns.md docs/roadmap.md \
        docs/mathematical-architecture.md docs/sources.md README.md
git commit -m "docs(contracts): record the tower, its ceiling, and the two patterns it produced"
```

---

## Task 8 *(optional, and the one a reviewer may reasonably cut)*: in-Lean scope disclosure

**Files:**
- Create: `MathFin/Contracts/Scope.lean`
- Modify: `tests/test_values.py`, `MathFin.lean`

**Interfaces:**
- Consumes: `Contract` (Task 1).
- Produces: `ContractSpec` with `name`, `contract`, `scope`, `unmodelled`; the specs for the four instruments; `test_contract_scope_matches_corpus`.

**Why, and the honest caveat.** The source paper puts `scope` and `unmodelled` inside the Lean `ContractSpec`, so a well-formedness certificate cannot be read as covering clauses nobody encoded. We carry the same disclosure as `metadata.formalization_scope` — one file away from the theorem, which is the gap `test_prose_does_not_outrun_statement` exists to patrol.

A `String` field no theorem reads is a wrapper that wins a name and loses a fact. **This task is only worth doing with Step 3**, the gate that makes the two copies unable to drift. Without the gate, skip the task.

- [ ] **Step 1: Define the spec structure**

```lean
/-- A contract together with its declared modelling scope. `unmodelled` is
first-class data: a theorem about `contract` is a theorem about the payoff
kernel, never about the clauses listed here. -/
structure ContractSpec (ι : Type*) where
  name : String
  contract : Contract ι
  scope : String
  unmodelled : List String
```

Then one `ContractSpec` per instrument from Tasks 4–5, each `unmodelled` listing at minimum `"business-day conventions"`, `"market disruption"`, `"corporate actions"`, `"issuer credit"`.

- [ ] **Step 2: Check and build**

```bash
./scripts/lean-check.sh MathFin/Contracts/Scope.lean
docker compose -f docker/docker-compose.yml down lean-repl
docker compose -f docker/docker-compose.yml run --rm --entrypoint lake verify build MathFin
```

- [ ] **Step 3: Write the drift gate**

Add to `tests/test_values.py`:

```python
CONTRACT_SCOPE_RE = re.compile(
    r'name\s*:=\s*"(?P<name>[^"]+)"[\s\S]*?scope\s*:=\s*"(?P<scope>[^"]+)"'
)

def test_contract_scope_matches_corpus() -> None:
    """The in-Lean scope disclosure and the corpus formalization_scope are two
    copies of one claim. Neither may drift from the other."""
    src = (REPO_ROOT / "MathFin/Contracts/Scope.lean").read_text()
    lean_scopes = {m["name"]: m["scope"] for m in CONTRACT_SCOPE_RE.finditer(src)}
    assert lean_scopes, "no ContractSpec parsed from Contracts/Scope.lean"
    for entry in iter_entries():
        name = entry.get("metadata", {}).get("contract_spec")
        if name is None:
            continue
        assert name in lean_scopes, (
            f"{entry['id']} names contract_spec {name!r}, absent from "
            "MathFin/Contracts/Scope.lean"
        )
        assert lean_scopes[name] in entry["metadata"]["formalization_scope"], (
            f"{entry['id']}: the Lean scope for {name!r} is not contained in "
            "its corpus formalization_scope — the two disclosures have drifted"
        )
```

Then add `"contract_spec": "<name>"` to the `metadata` of the four instrument entries from Task 6.

- [ ] **Step 4: Run the gate red, then green**

```bash
# First with a deliberately mismatched scope string in the Lean file:
docker compose -f docker/docker-compose.yml run --rm \
  --entrypoint python3 verify -m pytest tests/test_values.py::test_contract_scope_matches_corpus -q
# Expected: FAIL, naming the drifted entry.
# Then restore the correct string and re-run. Expected: PASS.
```

Running it red first is the only evidence the gate can actually fail.

- [ ] **Step 5: Regenerate the derived state the benchmark edit staled**

Adding `metadata.contract_spec` to four entries is a benchmark edit, so both
derived artifacts go stale:

```bash
python3 -m tools.verify.axiom_audit_gen --write
python3 -m tools.verify.ledger status      # expect the four entries stale
docker compose -f docker/docker-compose.yml up -d lean-repl
python3 -m tools.verify.ledger verify
python3 -m tools.verify.ledger status      # must exit 0
docker compose -f docker/docker-compose.yml down lean-repl
docker compose -f docker/docker-compose.yml run --rm \
  --entrypoint python3 verify -m pytest tests/ -q
```

Without this the task lands red: `test_values.py` enforces byte-freshness of
`MathFin/AxiomAuditGen.lean` after ANY benchmark edit, and `test_ledger.py`
requires a fresh row per entry.

- [ ] **Step 6: Commit**

```bash
git add MathFin/Contracts/Scope.lean tests/test_values.py \
        benchmarks/mathematical_finance.json MathFin/AxiomAuditGen.lean \
        verification_ledger.json MathFin.lean
git commit -m "feat(contracts): the modelling scope travels with the Lean object, gated against drift"
```

---

## Closing the branch

- [ ] Run the full suite one last time from a clean state:

```bash
docker compose -f docker/docker-compose.yml down lean-repl
docker compose -f docker/docker-compose.yml run --rm --entrypoint lake verify build MathFin
docker compose -f docker/docker-compose.yml run --rm --entrypoint lake verify lint
docker compose -f docker/docker-compose.yml run --rm --entrypoint python3 verify -m pytest tests/ -q
python3 -m tools.verify.ledger status
```

- [ ] Push and open the PR. `main` has no branch protection, so a locally-created merge commit reaches it with no pre-merge CI — the `pre-push` hook configured in Task 1 Step 1 is what covers that gap. Do not merge locally; open the PR and let CI run.
- [ ] Remove the worktree once merged: `git worktree remove ../formal-mathfin-contracts`.
- [ ] Update `~/.claude/projects/.../memory/` with the phase memory and its `MEMORY.md` pointer line.
