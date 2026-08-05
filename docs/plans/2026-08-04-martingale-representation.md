# Martingale Representation & Continuous Market Completeness — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that the continuous Itô integral is surjective onto centered `L²(𝓕_T^B)` — the martingale representation theorem — and read it as completeness of the continuous-time market and uniqueness of the equivalent martingale measure.

**Architecture:** `itoIntegralCLM_T` is already a `LinearIsometry` out of a complete space, so its range is closed. The theorem is that this closed range plus the constants exhausts `L²(𝓕_T)`, proved by showing the orthogonal complement is trivial: orthogonality to every Doléans exponential of a deterministic step integrand forces every finite-dimensional conditional expectation to vanish, and Lévy's upward theorem finishes.

**Tech Stack:** Lean 4 (v4.32.0), Mathlib @81a5d257, Degenne's BrownianMotion @4d52fa77, the MathFin Itô tower. Iteration through the `lean-repl` daemon; canonical gate is `lake build MathFin`.

**Design spec:** `docs/specs/2026-08-04-martingale-representation-completeness-design.md`. Where this plan and the spec disagree, the spec wins on scope and this plan wins on mechanics.

## Global Constraints

- **No `sorry`, `admit`, `native_decide`, `polyrith`, `hammer`, `loogle`, `leansearch` in `MathFin/`.** Enforced by `tests/test_values.py`. Sorried statements are permitted *only* transiently, and only in an untracked scratch file outside `MathFin/`. A file is committed only when it is sorry-free.
- **Every `MathFin/` file uses the module system:** `module` header, `public import`s, and `@[expose] public section` immediately after the module docstring. Without the last one, declarations are module-private, `lake build` stays green, and importers break.
- **Copyright header** on every new file: `Copyright (c) 2026 Raphael Coelho. All rights reserved. / Released under Apache 2.0 license as described in the file LICENSE. / Authors: Raphael Coelho`.
- **One Lean process at a time.** The `lean-repl` daemon owns the slot. `lake build` and `lake lint` require `docker compose -f docker/docker-compose.yml down lean-repl` first. Never run both.
- **Daemon lifecycle belongs to the controller, not to implementers.** An implementer runs `./scripts/lean-check.sh` and nothing else Lean-related: never `docker compose up/down`, never `lake build`, never `lake lint`. The controller runs the down/build/lint/up gate after each Lean-producing task. Two Lean-loaded processes on this 10 GB box is the event behind every historical freeze.
- **`lean-check` only the small module you are authoring.** The daemon's elaboration timeout is 180s and exceeding it *kills the Lean server*, costing a ~5-minute Mathlib reload for everyone. Checking a large foundational file (`ItoIntegralL2.lean`, `ItoIntegralCLM.lean`, `DoobLpMaximalInequality.lean`) will trip it. Verified by hitting it on 2026-08-04.
- **Bind ∀-variables in the `have` signature, not with `intro`.** Write `have h (M : ℕ) : P M := by …`, never `have h : ∀ M : ℕ, P M := by intro M …`. This is house style and it has now been flagged on two consecutive tasks (Task 2 at `:521`/`:528`, Task 3 at nine sites); treat it as binding rather than as a review nit to absorb each time.
- **`lake lint` is a CI gate that `lake build` does not run.** An unused hypothesis is a lint *error*, not a warning — it pushes CI red. If a hypothesis is kept for interface fidelity, name it `_foo`: that preserves arity, type and position, so positional callers are untouched. Task 3's build gate failed on exactly this.
- **The scratch statement file persists.** `scratch_mrt_statements.lean` is created in Task 0 and is the program's signature reference through Task 6; Task 9 deletes it. It stays untracked — never `git add` it.
- **`MathFin.lean` is a single-file bind mount.** After editing it, re-sync into the running daemon or the daemon keeps serving the old import list: `docker exec -i docker-lean-repl-1 sh -c 'cat > /app/MathFin.lean' < MathFin.lean`.
- **Never `| tail` a build log under diagnosis** — the first error is the diagnostic one.
- **No Claude/assistant attribution** anywhere: commits, PR bodies, CITATION.
- **Specific `git add` paths only.** Never `git add -A` or `git add .`.
- Branch is `feat/martingale-representation`, already created. The design spec is present and untracked; it is committed with Task 1.

## Task 0 findings — binding amendments

Task 0 ran on 2026-08-04 and type-checked every statement below. **Its output supersedes the drafted signatures in Tasks 1–6.** The authoritative signature source is now, in order of precedence:

1. `scratch_mrt_statements.lean` (repo root, untracked) — Tasks 1–4 and the `ItoIntegralCLM`-only half of Task 5.
2. `scratch_mrt_statements_b.lean` — Task 5's process form and all of Task 6.
3. `.superpowers/sdd/2026-08-04-martingale-representation/task-0-report.md` — the rationale for every amendment.

Implementers: **copy your statements from the scratch files, not from the task text below.** The task text carries strategy and the lemmas to consume; the scratch files carry the types.

Structural corrections that apply to every module in this program:

- The variable block is `variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)`. `mΩ` is an **instance** binder, not implicit — the drafted `{mΩ : MeasurableSpace Ω}` fails everywhere.
- Everything lives inside `namespace MathFin`, and `open MeasureTheory ProbabilityTheory Filter ItoIntegralCLM` — outside the namespace, `open ItoIntegralCLM` does not resolve.
- `⇑` coercions on `Lp` elements are mandatory in the a.e. statements; do not drop them.
- `stepDoleansExp` takes `B` **explicitly**. With `B` implicit it leaves an unresolvable metavariable in Task 4's `hFperp`.

Scope added by Task 0, not in the original estimate:

- **Task 1** must also produce the bundled `cylinderFiltration : Filtration ℕ mΩ` plus `dyadicGrid_le` and `dyadicGrid_mono`. Lévy's upward theorem is stated for `ℱ : Filtration ℕ m0`, not a bare `ℕ → MeasurableSpace Ω`, so the bare `iSup_cylinderSigma_eq_natFiltration` alone cannot feed Task 4.
- **Task 2** must also produce `coeFn_smulAdapted`, the characterising a.e. identity. Without it `smulAdapted` is opaque and the density step has nothing to rewrite through.
- **Task 3** must prove the *named-integrand* `constDoleans_sub_one_eq_itoIntegral` and the *shifted* `constDoleans_shift_sub_one_mem_range`, not merely the existential `constDoleans_sub_one_mem_range`. Reason: Task 2's unbounded corollary needs `MemLp (fun p ↦ Z p.2 * φ p) 2 trim_T`, and `discountedGBM_eq_itoIntegral` is purely existential — an existential `φ` carries no information with which to discharge that hypothesis.
- **Task 5 Step 3 is not one line.** `Submodule.orthogonal_eq_bot_iff` is ambient-relative, and the range lives in `Lp ℝ 2 μ` whose `⊤` is all of `L²(μ)`, not the `𝓕_T`-measurable part. The argument runs inside `↥(lpMeas ℝ ℝ (𝓕 T) 2 μ)` with the range transported by `comap`. `CompleteSpace (lpMeas …)` is an instance, so this works — budget the transport.

Decision on Task 0's concern 6 (`emm_unique_of_complete` never links `S` to `B`), made by the controller and binding on Task 6: **do not link them.** Split the result in two, following the layering `ContinuousMarket` already uses (model-agnostic frame, instantiated by `ContinuousFTAP`):

- an abstract `emm_unique_of_complete` on the `ContinuousMarket` frame, taking completeness as a *hypothesis about `S`* — no `B`, no Brownian filtration, no martingale representation;
- a separate `bs_market_complete` discharging that hypothesis for the Black–Scholes instance, which is where `B` and the representation theorem enter.

This is strictly cleaner than a single fused statement: uniqueness is a fact about complete markets in general, and tying it to a Brownian driver would understate it.

## What "test-first" means here

Lean's analogue of a failing test is a **statement that elaborates but is unproved**. Each task therefore runs:

1. state the theorem with `sorry` in a scratch file, `lean-check` it — this proves the *signature* is well-typed against real Mathlib/MathFin types (the "watch it fail" step);
2. move the statement into its `MathFin/` module and prove it;
3. `lean-check` the module — zero errors, zero sorries;
4. `lake build MathFin` + `lake lint` with the daemon down;
5. commit.

Proof *bodies* are not pre-written in this plan, and any plan that pretended to pre-write them would be lying: these are research-level proofs discovered at the daemon. What is specified per task is the exact statement, the named existing lemmas the proof consumes, and the strategy. Task 0 exists to convert the drafted signatures below into verified ones before any proof effort is spent.

---

### Task 0: Verify every signature before proving anything

**Files:**
- Create (untracked, deleted at end of task): `scratch_mrt_statements.lean` at repo root

**Interfaces:**
- Produces: a verified, corrected version of every theorem signature used by Tasks 1–6. **Where Task 0's output differs from the drafts below, Task 0's output is authoritative** and the later tasks are amended to match.

- [ ] **Step 1: Confirm the daemon is up**

Run: `./scripts/lean-check.sh MathFin/Foundations/ItoIntegralCovariation.lean`
Expected: `{"success": true, ... "sorry_count": 0}`. This is the only sound readiness probe — log-grep and port-probe both give false positives.

If it fails, bring the daemon up and re-probe:
`docker compose -f docker/docker-compose.yml up -d lean-repl`

- [ ] **Step 2: Write the scratch statement file**

Create `scratch_mrt_statements.lean` at repo root with the imports and every target statement stubbed by `sorry`. Start from:

```lean
import MathFin.Foundations.ItoIntegralCovariation
import MathFin.Foundations.ItoIntegralProcessGeneral
import MathFin.Foundations.ItoFormulaGBM
import MathFin.Foundations.ItoIntegralBrownian
import MathFin.Foundations.SimpleDoleansExponential

open MeasureTheory ProbabilityTheory Filter ItoIntegralCLM
open scoped NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
```

then paste, in order, the statement of every theorem named in Tasks 1–6 below, each with `:= sorry`.

- [ ] **Step 3: Check it, and iterate until every signature elaborates**

Run: `./scripts/lean-check.sh scratch_mrt_statements.lean`
Expected on the first run: FAILURES. Universe/implicit-argument/coercion mismatches are the norm here, not the exception.

The success criterion is **`"errors": []` plus the expected `sorry_count`** — *not* `success: true`. The daemon defines `success = (no errors) ∧ (sorry_count == 0)`, so a file of deliberately-unproved statements always reports `success: false`. Reading that as failure is a trap; check the `errors` array.

Two known friction points to expect:
- `lpMeas` takes its type and scalar arguments explicitly: the usage form is `lpMeas ℝ ℝ (natFiltration hBmeas T) 2 μ`, a `Submodule ℝ (Lp ℝ 2 μ)`.
- The daemon elaborates with `autoImplicit true` while `lake build` uses `false`. A statement that checks at the daemon can still fail the build on a typo'd identifier silently bound as an auto-implicit. Every task's `lake build` step exists to catch exactly this.

- [ ] **Step 4: Record the corrected signatures**

Amend Tasks 1–6 in this plan file with the verified statements. This is a plan edit, not a code edit.

- [ ] **Step 5: Leave the scratch file in place**

Do **not** delete it. It is the program's signature reference through Task 6, and Tasks 1–5 each add their statements to it before moving them into a `MathFin/` module. Task 9 deletes it. It stays untracked — never `git add` it.

No commit — this task produces a corrected plan, not code.

---

### Task 1: Countable generation of the Brownian σ-algebra

**Files:**
- Create: `MathFin/Foundations/BrownianCylinderGeneration.lean`
- Modify: `MathFin.lean` (add the import)

**Interfaces:**
- Consumes: `ItoIntegralL2.natFiltration hBmeas : Filtration ℝ≥0 mΩ`, which is `Filtration.natural B _` with `seq i = ⨆ j ≤ i, MeasurableSpace.comap (u j) mβ`.
- Produces: `dyadicGrid : ℝ≥0 → ℕ → Finset ℝ≥0`, `cylinderSigma : (ℝ≥0 → Ω → ℝ) → ℝ≥0 → ℕ → MeasurableSpace Ω`, and `iSup_cylinderSigma_eq_natFiltration`, consumed by Task 4.

- [ ] **Step 1: State it in the scratch file and check it fails**

```lean
/-- The dyadic grid `{k·T/2^n : k ≤ 2^n}` on `[0,T]`. Increasing in `n`,
contains `T`, and its union is dense in `[0,T]`. -/
noncomputable def dyadicGrid (T : ℝ≥0) (n : ℕ) : Finset ℝ≥0 :=
  (Finset.range (2 ^ n + 1)).image fun k ↦ (k : ℝ≥0) * T / (2 ^ n)

/-- The σ-algebra generated by the process at the `n`-th dyadic grid. -/
noncomputable def cylinderSigma (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) :
    MeasurableSpace Ω :=
  ⨆ q ∈ dyadicGrid T n, MeasurableSpace.comap (B q) inferInstance

theorem iSup_cylinderSigma_eq_natFiltration (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (T : ℝ≥0) :
    (⨆ n : ℕ, cylinderSigma B T n)
      = (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas) T := sorry
```

Run: `./scripts/lean-check.sh scratch_mrt_statements.lean` — expect the signature to elaborate with one sorry.

- [ ] **Step 2: Create the module with the docstring and the two definitions**

File skeleton (the header pattern every `MathFin/` file uses):

```lean
/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralL2

/-! # Countable generation of the Brownian σ-algebra
... (docstring: why path continuity is the whole content) ...
-/

@[expose] public section

namespace MathFin
```

- [ ] **Step 3: Prove the easy inclusion `⨆ₙ cylinderSigma ≤ 𝓕_T`**

Each grid point `q ∈ dyadicGrid T n` satisfies `q ≤ T`, so `comap (B q) ≤ ⨆ j ≤ T, comap (B j)` by `le_iSup₂`. Requires a `dyadicGrid_le` lemma (`q ∈ dyadicGrid T n → q ≤ T`), proved from `k ≤ 2^n`.

- [ ] **Step 4: Prove the hard inclusion `𝓕_T ≤ ⨆ₙ cylinderSigma`**

This is where `hBcont` enters and it is the only place it does. For `s ≤ T`, exhibit `B s` as a pointwise limit of grid evaluations: choose `qₙ ∈ dyadicGrid T n` with `qₙ → s` (nearest grid point below `s`, plus `T` itself when `s = T`), then `B qₙ ω → B s ω` by `hBcont ω`. Each `B qₙ` is `⨆ₙ cylinderSigma`-measurable, so `B s` is too, by `measurable_of_tendsto_metrizable`. Then `comap (B s) ≤ ⨆ₙ cylinderSigma` by `MeasurableSpace.comap_le_iff_le_map` / `Measurable.comap_le`.

- [ ] **Step 5: Assemble by `le_antisymm` and check the module**

Run: `./scripts/lean-check.sh MathFin/Foundations/BrownianCylinderGeneration.lean`
Expected: `{"success": true, "errors": [], "sorry_count": 0}`

- [ ] **Step 6: Wire into the umbrella**

Add `public import MathFin.Foundations.BrownianCylinderGeneration` to `MathFin.lean`, then re-sync it into the daemon (single-file bind mount — see Global Constraints):

```bash
docker exec -i docker-lean-repl-1 sh -c 'cat > /app/MathFin.lean' < MathFin.lean
```

Do **not** run `lake build` or `lake lint` yourself, and do not stop the daemon. The controller runs that gate after this task. This is the same for every task in this plan; where later tasks say "build and lint", they mean the controller does it.

- [ ] **Step 7: Commit (this is the first commit on the branch — include the spec and this plan)**

```bash
git add docs/specs/2026-08-04-martingale-representation-completeness-design.md \
        docs/plans/2026-08-04-martingale-representation.md \
        MathFin/Foundations/BrownianCylinderGeneration.lean MathFin.lean
git commit -m "feat(foundations): countable generation of the Brownian sigma-algebra"
```

---

### Task 2: `𝓕_a`-linearity of the Itô integral

**Files:**
- Create: `MathFin/Foundations/ItoIntegralLocality.lean`
- Modify: `MathFin.lean`

**Interfaces:**
- Consumes: `ItoIntegralCLM.itoIntegralCLM_T hB T hBmeas : Lp ℝ 2 (trimMeasure_T T hBmeas) →L[ℝ] Lp ℝ 2 μ`; `ItoIntegralCLM.simpleAssembly_T`, `simpleAssembly_T_denseRange`, `TBoundedSP`; `ItoIntegralBrownian.clampM`.
- Produces: `smulAdapted` and `itoIntegralCLM_T_smulAdapted`, consumed by Task 3.

This is the crux task. Budget accordingly.

- [ ] **Step 1: Settle the definitional wrinkle first**

`Z : Ω → ℝ` and `φ : Lp ℝ 2 (trimMeasure_T T hBmeas)` live on different spaces; their product `(t,ω) ↦ Z ω · φ (t,ω)` must be shown to land back in `Lp ℝ 2 (trimMeasure_T T hBmeas)`. For **bounded** `Z` this is `MemLp.const_mul`-shaped, but the measurability side needs `Z ∘ Prod.snd` to be predictable, which holds because `Z` is `𝓕_a`-measurable and constant in `t`.

Define, in the scratch file first:

```lean
/-- Scaling a predictable `L²` integrand by a bounded `𝓕_a`-measurable factor. -/
noncomputable def smulAdapted (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ItoIntegralL2.natFiltration hBmeas a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) := sorry
```

Run `./scripts/lean-check.sh scratch_mrt_statements.lean` and iterate until it elaborates.

- [ ] **Step 2: State the locality theorem and check it fails**

```lean
/-- **`𝓕_a`-linearity of the Itô integral.** A bounded `𝓕_a`-measurable factor
passes through the stochastic integral of an integrand supported on `(a, T]`. -/
theorem itoIntegralCLM_T_smulAdapted (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ItoIntegralL2.natFiltration hBmeas a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (hφ : ∀ᵐ p ∂(trimMeasure_T (μ := μ) T hBmeas), p.1 ≤ a → φ p = 0) :
    itoIntegralCLM_T hB T hBmeas (smulAdapted T a hBmeas Z hZm C hZb φ)
      =ᵐ[μ] fun ω ↦ Z ω * itoIntegralCLM_T hB T hBmeas φ ω := sorry
```

- [ ] **Step 3: Prove it on simple processes**

For `V : TBoundedSP T hBmeas` supported on `(a, T]`, the integral is the finite sum `Σ V(p) · (B p.2 − B p.1)`. Multiplying by `Z` distributes over the sum, and `Z · V(p)` is still `𝓕_{p.1}`-measurable because `a ≤ p.1`. This step is bookkeeping, and it is where the support hypothesis `hφ` is genuinely used.

- [ ] **Step 4: Extend by density**

Both sides are continuous in `φ`: the left by `(itoIntegralCLM_T ...).continuous` composed with continuity of `smulAdapted` in `φ` (it is bounded-linear, operator norm `≤ C`), the right by multiplication by a bounded function being continuous on `L²`. Conclude with `DenseRange.equalizer (simpleAssembly_T_denseRange T hBmeas)` — the same closing move `itoProcessCLM_eq_condExpL2` and `itoProcessCLM_terminal_eq` use in `ItoIntegralProcessGeneral.lean:144,223`. Read those two proofs before writing this one; they are the template.

- [ ] **Step 5: Add the unbounded-`Z` corollary by truncation**

`E_k` in Task 3 is lognormal, not bounded. Provide:

```lean
theorem itoIntegralCLM_T_smulAdapted_of_memLp (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[ItoIntegralL2.natFiltration hBmeas a] Z) ...
```

using `ItoIntegralBrownian.clampM` to truncate `Z` at level `M`, applying Step 2's result at each `M`, and passing `M → ∞` by dominated convergence. State the integrability hypothesis as whatever Task 3 actually needs — a fourth moment on `Z` is the expected form, since the product must stay in `L²`.

- [ ] **Step 6: Check, build, lint, commit**

```bash
./scripts/lean-check.sh MathFin/Foundations/ItoIntegralLocality.lean
```
then the daemon-down `lake build MathFin && lake lint` from Task 1 Step 6, then:

```bash
git add MathFin/Foundations/ItoIntegralLocality.lean MathFin.lean
git commit -m "feat(foundations): F_a-linearity of the Ito integral"
```

**If Step 3–4 resist for more than a working session**, switch to the spec's §5 fallback: generalize `ito_formula_itoProcess` from constant to piecewise-constant coefficients and read Task 3 off directly. That is a scope swap, not a dead end — record the switch in the plan before making it.

---

### Task 3: The step-integrand Doléans exponential is an Itô integral

**Files:**
- Create: `MathFin/Foundations/DoleansStepRepresentation.lean`
- Modify: `MathFin.lean`

**Interfaces:**
- Consumes: `ItoFormulaGBM.discountedGBM_eq_itoIntegral hB hBmeas hBcont T S₀ σ` (the constant-`σ` case), `ItoIntegralBrownian.eval_zero_ae hBmeas : B 0 =ᵐ[μ] 0`, Task 2's `itoIntegralCLM_T_smulAdapted_of_memLp`.
- Produces: `stepDoleansExp` and `stepDoleans_sub_one_mem_range`, consumed by Task 4.

- [ ] **Step 1: State the constant case as a named lemma and check it**

The constant case is a rewrite of an existing theorem, not new mathematics:

```lean
/-- **Constant-`σ` Doléans exponential as an Itô integral.** `discountedGBM_eq_itoIntegral`
at `S₀ = 1`, with `B 0 =ᵐ 0`. -/
theorem constDoleans_sub_one_mem_range (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (T : ℝ≥0) (σ : ℝ) :
    ∃ φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (fun ω ↦ Real.exp (σ * B T ω - σ ^ 2 / 2 * (T : ℝ)) - 1)
        =ᵐ[μ] itoIntegralCLM_T hB T hBmeas φ := sorry
```

Proof: `obtain ⟨gfx, hgfx⟩ := discountedGBM_eq_itoIntegral hB hBmeas hBcont T 1 σ`, then rewrite the `S₀ * exp (σ * B 0 ω)` term to `1` using `eval_zero_ae` and `one_mul`, and reconcile `-(σ^2/2) * T + σ * B T ω` with `σ * B T ω - σ^2/2 * T` by `ring_nf`.

- [ ] **Step 2: Define the step Doléans exponential**

```lean
/-- The Doléans exponential of a deterministic step integrand
`h = Σ hₖ·1_{(sₖ, sₖ₊₁]}` over a monotone partition, evaluated at the horizon. -/
noncomputable def stepDoleansExp (s : ℕ → ℝ≥0) (h : ℕ → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ∏ k ∈ Finset.range N,
    Real.exp (h k * (B (s (k + 1)) ω - B (s k) ω)
      - h k ^ 2 / 2 * ((s (k + 1) : ℝ) - (s k : ℝ)))
```

Match the shape of `SimpleDoleansExponential.simpleDoleansExp` (`MathFin/Foundations/SimpleDoleansExponential.lean:505`) so the two files' conventions agree; read that definition before writing this one.

- [ ] **Step 3: State the main theorem and check it fails**

```lean
theorem stepDoleans_sub_one_mem_range (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (T : ℝ≥0)
    (s : ℕ → ℝ≥0) (hs : Monotone s) (h : ℕ → ℝ) (N : ℕ)
    (hsN : s N = T) (hs0 : s 0 = 0) :
    ∃ φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (fun ω ↦ stepDoleansExp s h N ω - 1) =ᵐ[μ] itoIntegralCLM_T hB T hBmeas φ := sorry
```

- [ ] **Step 4: Prove it by induction on `N`**

`stepDoleansExp s h (N+1) − stepDoleansExp s h N = E_N · (exp(h_N ΔB_N − ½h_N²Δs_N) − 1)`, where `E_N := stepDoleansExp s h N` is `𝓕_{s N}`-measurable. Step 1 supplies the parenthesis as an Itô integral over `(s N, s (N+1)]` (shift the constant case to start at `s N`); Task 2's corollary pulls `E_N` inside. The range is a submodule, so the telescoped sum stays in it.

`E_N` has all moments (it is a product of independent lognormals), which is what Task 2 Step 5's integrability hypothesis needs; prove it as a private lemma via `GaussianMoments` / `StandardGaussianMGF`.

- [ ] **Step 5: Check, build, lint, commit**

```bash
git add MathFin/Foundations/DoleansStepRepresentation.lean MathFin.lean
git commit -m "feat(foundations): step-integrand Doleans exponential as an Ito integral"
```

---

### Task 4: Totality of the Wiener exponentials

**Files:**
- Create: `MathFin/Foundations/WienerExponentialTotality.lean`
- Modify: `MathFin.lean`

**Interfaces:**
- Consumes: Task 1's `iSup_cylinderSigma_eq_natFiltration`, Task 3's `stepDoleans_sub_one_mem_range`; Mathlib's `Measure.ext_of_charFun`, `Probability/Moments/ComplexMGF.lean` (`eqOn_complexMGF_of_mgf`, `ext_of_complexMGF_eq`), `Integrable.tendsto_eLpNorm_condExp`.
- Produces: `eq_zero_of_orthogonal_stepDoleans`, consumed by Task 5.

- [ ] **Step 1: State the target and check it fails**

```lean
/-- **Totality.** An `L²` variable measurable for `𝓕_T`, orthogonal to `1` and to
every step-integrand Doléans exponential, is zero. -/
theorem eq_zero_of_orthogonal_stepDoleans (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (T : ℝ≥0)
    (F : Lp ℝ 2 μ)
    (hFmeas : AEStronglyMeasurable[ItoIntegralL2.natFiltration hBmeas T] F μ)
    (hF1 : ∫ ω, F ω ∂μ = 0)
    (hFperp : ∀ (s : ℕ → ℝ≥0), Monotone s → ∀ (h : ℕ → ℝ) (N : ℕ),
      s 0 = 0 → s N = T → ∫ ω, F ω * stepDoleansExp s h N ω ∂μ = 0) :
    F = 0 := sorry
```

- [ ] **Step 2: Reduce to the exponential of a linear combination (S3)**

`stepDoleansExp s h N ω = exp(Σₖ hₖ ΔBₖ ω) · exp(−½ Σₖ hₖ² Δsₖ)`, the second factor a positive constant that divides out. Abel-summing `Σₖ hₖ (B_{sₖ₊₁} − B_{sₖ})` into `Σⱼ λⱼ B_{sⱼ}` shows every real coefficient vector `λ` is reachable by choosing `h`. Deliver:

```lean
private lemma integral_mul_exp_linear_eq_zero ... :
    ∀ (n : ℕ) (t : Fin n → ℝ≥0) (_ : ∀ i, t i ≤ T) (lam : Fin n → ℝ),
      ∫ ω, F ω * Real.exp (∑ i, lam i * B (t i) ω) ∂μ = 0
```

- [ ] **Step 3: Conditional expectation on a cylinder vanishes (S4)**

Split `F = F⁺ − F⁻` (`Lp.pos_part` / `Lp.neg_part`, or `MeasureTheory.Function.posPart`). Push forward: `ν± := ((μ.withDensity (fun ω ↦ ENNReal.ofReal (F± ω))).map (fun ω ↦ (B (t ·) ω)))` on `EuclideanSpace ℝ (Fin n)`. Both are finite because `F ∈ L² ⊆ L¹`. Step 2 says their moment generating functions agree on all of `ℝⁿ`; `F ∈ L²` with `exp⟨λ,X⟩` Gaussian-tailed gives `integrableExpSet = univ`, which is open, so the `ComplexMGF` chain applies and `ν⁺ = ν⁻`. Conclude `∫ F · g(X) = 0` for bounded measurable `g`, hence `μ[F | cylinderSigma B T n] =ᵐ 0`.

Read the analogous chain in `MathFin/Foundations/GirsanovConstantTheta.lean` before writing this; if the shared content is real, extract it to one root there and consume it here rather than writing a second copy (spec §7).

- [ ] **Step 4: Lévy upward (S5)**

`Integrable.tendsto_eLpNorm_condExp (hg : Integrable g μ) (hgmeas : StronglyMeasurable[⨆ n, ℱ n] g)` gives `μ[F | 𝓖ₙ] → F` in `L¹`. Task 1 supplies `⨆ₙ cylinderSigma B T n = 𝓕_T`, and `hFmeas` plus `AEStronglyMeasurable.mk` supplies the strongly-measurable representative the hypothesis wants. With every `μ[F | 𝓖ₙ] =ᵐ 0` the limit is `0`, so `F =ᵐ 0`, so `F = 0` in `Lp` by `Lp.ext`.

- [ ] **Step 5: Check, build, lint, commit**

```bash
git add MathFin/Foundations/WienerExponentialTotality.lean MathFin.lean
git commit -m "feat(foundations): totality of the Wiener exponentials in L2 of the Brownian sigma-algebra"
```

---

### Task 5: The martingale representation theorem

**Files:**
- Create: `MathFin/Foundations/MartingaleRepresentation.lean`
- Modify: `MathFin.lean`

**Interfaces:**
- Consumes: Task 3, Task 4, `ItoIntegralCovariation.itoIsometry_T hB T hBmeas : Lp ℝ 2 (trimMeasure_T T hBmeas) →ₗᵢ[ℝ] Lp ℝ 2 μ`, `ItoIntegralProcessGeneral.itoProcessCLM_eq_condExpL2` and `.itoProcessCLM_terminal_eq`.
- Produces: `itoIntegralCLM_T_surjective_onto_centered`, `itoIsometryEquiv_T`, `exists_itoIntegral_representation`, `martingale_representation` — consumed by Task 6.

- [ ] **Step 1: State the four results and check they elaborate**

```lean
/-- **Martingale representation, terminal form.** Every square-integrable
`𝓕_T`-measurable variable is its mean plus an Itô integral. -/
theorem exists_itoIntegral_representation (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (T : ℝ≥0)
    (F : Lp ℝ 2 μ)
    (hFmeas : AEStronglyMeasurable[ItoIntegralL2.natFiltration hBmeas T] F μ) :
    ∃! φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (F : Ω → ℝ) =ᵐ[μ] fun ω ↦ (∫ x, F x ∂μ) + itoIntegralCLM_T hB T hBmeas φ ω := sorry

/-- **Martingale representation, process form.** Corpus entry `gir-thm-9.3.4`. -/
theorem martingale_representation (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (T : ℝ≥0)
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M (ItoIntegralL2.natFiltration hBmeas) μ)
    (hMT : MemLp (M T) 2 μ) :
    ∃ φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      ∀ t ≤ T, M t =ᵐ[μ] fun ω ↦ M 0 ω + itoProcessCLM hB T t hBmeas φ ω := sorry
```

Also state the submodule form (`range ⊔ span{1} = lpMeas ...`) and the bundled `itoIsometryEquiv_T`; the exact spelling of the latter depends on which `LinearIsometryEquiv.of*` constructor fits, so settle it in Task 0.

- [ ] **Step 2: Prove `range I` is closed**

`(itoIsometry_T hB T hBmeas).isometry.isClosed_range`, or via `LinearIsometry.isComplete_range` from completeness of `Lp`. One line; do not rebuild the isometry.

- [ ] **Step 3: Prove surjectivity onto the centered subspace**

Let `V := (LinearMap.range (itoIntegralCLM_T ...).toLinearMap)`, closed by Step 2. In the Hilbert space `lpMeas ℝ ℝ (𝓕 T) 2 μ`, a closed subspace equals the whole space iff its orthogonal complement is trivial (`Submodule.orthogonal_eq_bot_iff` for complete subspaces). Take `F` in the complement with `∫F = 0`; Task 3 puts every `stepDoleansExp − 1` in `V`, so `F ⊥ (stepDoleansExp − 1)`, and with `∫F = 0` also `F ⊥ stepDoleansExp`; Task 4 concludes `F = 0`.

- [ ] **Step 4: Derive the terminal form and uniqueness**

Existence is Step 3 applied to `F − ∫F`. Uniqueness is injectivity of an isometry (`LinearIsometry.injective`).

- [ ] **Step 5: Derive the process form**

Apply the terminal form to `M T`. For `t ≤ T`, `M t =ᵐ μ[M T | 𝓕_t]` by the martingale property, and `μ[itoIntegralCLM_T φ | 𝓕_t] = itoProcessCLM T t φ` is exactly `itoProcessCLM_eq_condExpL2` (`ItoIntegralProcessGeneral.lean:144`), with `itoProcessCLM_terminal_eq` reconciling `t = T`. The constant passes through `condExp_const`.

- [ ] **Step 6: Check, build, lint, commit**

```bash
git add MathFin/Foundations/MartingaleRepresentation.lean MathFin.lean
git commit -m "feat(foundations): martingale representation on the Brownian filtration"
```

---

### Task 6: Market completeness and EMM uniqueness

**Files:**
- Create: `MathFin/Foundations/MarketCompleteness.lean`
- Modify: `MathFin.lean`, and `MathFin/Foundations/ContinuousMarket.lean` (docstring only — the companion scope paragraph)

**Interfaces:**
- Consumes: Task 5's `martingale_representation` and `exists_itoIntegral_representation`; `ContinuousMarket.IsEMM`; `Foundations/Girsanov`, `Foundations/ContinuousFTAP`.
- Produces: `exists_replicating_strategy`, `emm_unique_of_complete`, `superReplication_eq_emm_price`.

- [ ] **Step 1: Define the replicating-strategy predicate**

The strategy class is the Itô-integrable predictable class, wider than `ContinuousMarket.SimpleStrategy` (spec §3). Define `Replicates` as: initial wealth `x` plus the Itô integral of `φ` against the discounted price reaches the claim at `T`, a.e. Do **not** modify `SimpleStrategy` or `NoArbitrageSimple`; this is additive.

- [ ] **Step 2: State and prove completeness**

Every `L²` claim `H` measurable for `𝓕_T` is replicated: apply `martingale_representation` to `t ↦ 𝔼_Q[H | 𝓕_t]`, and read the integrand as the hedge.

- [ ] **Step 3: State and prove EMM uniqueness**

If every claim is replicable, two EMMs assign the same value to every claim, hence agree. Land it on `ContinuousMarket.IsEMM`. State the *one direction only* — `complete ⟹ unique` — and say in the docstring that the converse is out of scope, in the idiom `ContinuousMarket.lean` already uses for its Delbaen–Schachermayer boundary.

- [ ] **Step 4: State and prove the superreplication equality**

Replication makes the superreplication price equal the EMM price. The docstring must record what the spec §6.3 records: this is the continuous-time analogue reached by a different route, and it does **not** close issue #39, whose finite-state Farkas gap is untouched.

- [ ] **Step 5: Add the companion paragraph to `ContinuousMarket.lean`**

Its "Scope: meaning-1 vs meaning-2" section needs one paragraph noting that completeness lives on a wider strategy class, and why that widening is forced rather than chosen.

- [ ] **Step 6: Check, build, lint, commit**

```bash
git add MathFin/Foundations/MarketCompleteness.lean MathFin/Foundations/ContinuousMarket.lean MathFin.lean
git commit -m "feat(foundations): continuous-time market completeness and EMM uniqueness"
```

---

### Task 7: Corpus, audit, and ledger

**Files:**
- Modify: `benchmarks/girsanov_finance.json` (`gir-thm-9.3.4`), `MathFin/AxiomAudit.lean`, `MathFin/AxiomAuditGen.lean` (generated), `MathFin/Blueprint.lean`, `verification_ledger.json`

- [ ] **Step 1: Rewrite `gir-thm-9.3.4` as a real snippet**

Replace the structure-spec with a 5–25 line snippet that imports `MathFin.Foundations.MartingaleRepresentation` and re-exports `martingale_representation`. Set `metadata.formalization_status` to `full` and rewrite `formalization_scope` to describe the derivation. The snippet must **not** carry `import Mathlib` — the MathFin module's `public import Mathlib` re-exports it.

- [ ] **Step 2: Add new corpus entries**

One for the surjectivity theorem, one for market completeness, one for EMM uniqueness. Globally unique ids; every entry needs a `formalization_status`.

- [ ] **Step 3: Pin axioms**

Add `#guard_msgs`-pinned `#print axioms` lines to `MathFin/AxiomAudit.lean` for the headline theorems, then regenerate the exhaustive audit:

```bash
python3 -m tools.verify.axiom_audit_gen --write
```

- [ ] **Step 4: Blueprint tags**

Add post-hoc `@[blueprint]` tags, then regenerate: `lake exe blueprint_export` + `tools/blueprint_render.py`. Never hand-edit the generated block in `docs/blueprint.md`.

- [ ] **Step 5: Re-verify the ledger**

```bash
python3 -m tools.verify.ledger status
python3 -m tools.verify.ledger verify
```
De-privatising or adding a module stales all transitive importers, so expect more stale rows than the files you touched.

- [ ] **Step 6: Run the full gate set**

```bash
docker compose -f docker/docker-compose.yml run --rm --entrypoint python3 verify -m pytest tests/ -q
docker compose -f docker/docker-compose.yml run --rm --entrypoint python3 verify -m tools.verify.coverage_report
```
Expected: all green, and the coverage split shows `gir-thm-9.3.4` moved out of `reduced_core`.

- [ ] **Step 7: Commit**

```bash
git add benchmarks/girsanov_finance.json MathFin/AxiomAudit.lean MathFin/AxiomAuditGen.lean \
        MathFin/Blueprint.lean docs/blueprint.md verification_ledger.json
git commit -m "feat(corpus): martingale representation and completeness entries; gir-thm-9.3.4 to full"
```

---

### Task 8: Documentation and the repo-complete upgrade

**Files:**
- Modify: `docs/coverage.md`, `docs/bridges.md`, `docs/mathematical-architecture.md`, `docs/roadmap.md`, `docs/leaps.md`, `docs/patterns.md`, `README.md`

A phase is not done until the whole repo reflects it.

- [ ] **Step 1: `docs/mathematical-architecture.md` — the bridge row**

Add the row and state the architectural claim from spec §7: Girsanov wired pillar I ↔ II in the direction of existence; martingale representation wires it in the direction of uniqueness and attainability. Update the coherence verdict.

- [ ] **Step 2: `docs/leaps.md` — Leap 5**

The narrative entry, in the register of Leaps 1–4: what was assumed, what is now derived.

- [ ] **Step 3: `docs/coverage.md`** — dated pass entry, the status flip, new entries, and the honest scope note (one direction of the second FTAP, not the equivalence).

- [ ] **Step 4: `docs/bridges.md`** — the new bridge rows in the existing table format.

- [ ] **Step 5: `docs/patterns.md`** — dated batch. At minimum: `𝓕_a`-linearity by simple-process density + `DenseRange.equalizer`; the MGF-comparison route from orthogonality to a vanishing conditional expectation; countable generation of a natural filtration from path continuity.

- [ ] **Step 6: `docs/roadmap.md`** — phase-log entry.

- [ ] **Step 7: `README.md`** — refresh corpus counts from `coverage_report`.

- [ ] **Step 8: Commit**

```bash
git add docs/coverage.md docs/bridges.md docs/mathematical-architecture.md \
        docs/roadmap.md docs/leaps.md docs/patterns.md README.md
git commit -m "docs: record the martingale-representation phase across the doc set"
```

---

### Task 9: Issues, values review, close-out

- [ ] **Step 1: Split issue #49**

It bundles Lévy's characterization with martingale representation under "adapted-integrand Itô consequences", a framing this program disproves for the representation half. Close the representation half against the new modules; leave a new issue for `sc-thm-9.1.1` alone, describing what it actually needs (continuous local martingales with pathwise quadratic variation).

- [ ] **Step 2: Open follow-up issues**

Multi-dimensional representation (gated on `sc-thm-7.5.2`); the converse direction of the second FTAP; `L¹`/`H¹` representation and Clark–Ocone.

- [ ] **Step 3: Run the values review**

Eight lenses as gradients, per `docs/values-review.md`. Output a ranked backlog plus the upgrades executed this session. Not a verdict, and never "8/8 PASS". `test_values_review_is_current` fails once the corpus outgrows the last recorded review by more than 12 entries, so this is also a machine-enforced gate.

- [ ] **Step 4: Final full-gate run and PR**

Daemon down, `lake build MathFin && lake lint`, full pytest, `ledger status` all fresh. Then open the PR. PR body style: lowercase, "i", short sentences, no marketing, no em-dashes, no Claude attribution.

- [ ] **Step 5: Tear down**

```bash
docker compose -f docker/docker-compose.yml down lean-repl
```

---

## Self-review

**Spec coverage.** S0 → Task 5 Step 2. S1 → Task 3 Step 1. S2 → Tasks 2 and 3. S3 → Task 4 Step 2. S4 → Task 4 Step 3. S5 → Tasks 1 and 4 Step 4. S6 → Task 5 Step 5. S7 → Task 6. Spec §7's consume-don't-reprove table is enforced at Task 2 Step 4 (`DenseRange.equalizer` template), Task 3 Step 1 (reuse `discountedGBM_eq_itoIntegral`), Task 4 Step 3 (extract the shared root from `GirsanovConstantTheta`), Task 5 Step 2 (reuse `itoIsometry_T`). Spec §7's integration tail → Tasks 7–9. Spec §3's out-of-scope items → Task 9 Step 2 as follow-up issues.

**Known gap, stated rather than hidden:** the spec names a `LinearIsometryEquiv` bundling as the headline artifact; Task 5 Step 1 defers its exact spelling to Task 0 because the right constructor depends on how the centered subspace is expressed. If Task 0 shows the bundling is awkward, ship the surjectivity theorem and record the bundling as a follow-up — the mathematics is identical either way.

**Placeholder scan.** No "TBD"/"handle edge cases"/"similar to Task N". Proof bodies are deliberately absent and the reason is stated in "What test-first means here"; every task instead names the exact lemmas its proof consumes and the file:line of the template proof to imitate.

**Type consistency.** `hBmeas : ∀ t, Measurable (B t)` and `hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω` are spelled identically in every task. `stepDoleansExp` is defined once (Task 3 Step 2) and used with the same argument order in Task 4. `itoIntegralCLM_T hB T hBmeas` and `itoProcessCLM hB T t hBmeas` keep the argument order they have in `ItoIntegralCLM.lean:717` and `ItoIntegralProcessGeneral.lean:102`. `smulAdapted`'s argument list in Task 2 Step 1 matches its use in Task 2 Step 2.
