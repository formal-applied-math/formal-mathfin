# Documentation

| File | One-line | When to read |
|---|---|---|
| [`status.md`](status.md) | One page: the scope, the four pillars, the rules that keep the library one graph, and the backlog (the issue tracker, by area). | **Start here** to see where the program stands and where the work is. |
| [`onboarding.md`](onboarding.md) | Step-by-step first-contribution walkthrough: environment, fast REPL loop, module anatomy, PR checklist. | **Start here** if you are making your first contribution. |
| [`issue-labels.md`](issue-labels.md) | Suggested `area:*`, `type:*`, `difficulty:*`, and `status:*` labels plus bootstrap commands. | When triaging issues or preparing a contributor-friendly task. |
| [`troubleshooting.md`](troubleshooting.md) | Common build/environment failures — symptom → cause → fix. | When something breaks (GHCR login, OOM, inode staleness, daemon slot contention, stale ledger). |
| [`blueprint.md`](blueprint.md) | The deductive spine — a dependency graph from Brownian motion to Black–Scholes, each node linked to its Lean proof. | To see the BM → Black-Scholes deductive arc and what's proved vs gated. |
| [`coverage.md`](coverage.md) | Per-theorem audit with faithfulness status and verification evidence. | Before claiming any specific theorem is "proved." Source of truth for what's `full` vs `library_wrapper` vs `reduced_core`. |
| [`american-put-boundary.md`](american-put-boundary.md) | Continuous-time American put option log-boundary convexity: exact statements, stopping-value definitions, proof sketch, and port provenance. | When reviewing issue #175 or checking the geometric theorem's scope. |
| [`architecture.md`](architecture.md) | Design principles: the seven structural-principle modules, the three-tier honesty model, the bridge methodology. | When deciding where a new theorem belongs, or to understand why the library is shaped the way it is. |
| [`leaps.md`](leaps.md) | The 2026-05-23 "leaps": static Girsanov (the risk-neutral measure *derived*, `BSCallHyp` made a theorem), the genesis cascade (physical→EMM→pricing spine), and Margrabe's multivariate exchange option. Includes the honest abstraction boundary and what stays gated. | To understand how the EMM stops being an axiom, and how the multivariate / change-of-measure results compose. |
| [`bridges.md`](bridges.md) | Catalogue of bridges from `Foundations/` to pricing modules — the additive constructors that connect BM/martingale infra to BS/Bachelier/binomial. | When extending Foundations and wanting to make it usable from a pricing module without breaking existing consumers. |
| [`patterns.md`](patterns.md) | Distilled Lean / Mathlib proof patterns + technical idioms + workflow notes + anti-patterns. | Before writing a non-trivial proof, especially if it touches gaussian / martingale / convexity / Lp machinery. |
| [`roadmap.md`](roadmap.md) | Strategy: what the library is for, depth before breadth, how breadth is admitted, the next rungs. | When picking the next theorem to formalise, or judging whether a proposed area fits. |
| [`mathematical-architecture.md`](mathematical-architecture.md) | The field's spine: the four pillars, the bridges between them, and which seams are closed. | To see how the towers fit together and what is still open between them. |
| [`hjm-program.md`](hjm-program.md) | The ratified design for the HJM interest-rate program and its keystone, a stochastic Fubini theorem. | Before working on any HJM or stochastic-Fubini issue (#138–#158). |
| [`sources.md`](sources.md) | External formalisations and papers the library has learned from, and what was taken from each. | When crediting or comparing with outside work. |
| [`palomar.md`](palomar.md) | The Palomar registry submission. | When updating the registry entry. |
| [`research-problems/`](research-problems/README.md) | Research catalogue with stable IDs, precise questions, source provenance, dated reviews, and separate mathematical and Lean statuses; includes JSON records and linked issues. | When proposing a research problem or checking its recorded status and evidence. |
| [`open-problems.md`](open-problems.md) | Earlier survey and candidate pool, with dated corrections and links to the maintained catalogue. Entries outside the latest audit have not all been revalidated. | When searching for additional research leads or reviewing earlier assessments. |
| [`program-architecture.md`](program-architecture.md) | How the repos should be shaped across more than one field: four layers mapped onto four repos (apparatus anchored here, commons as `ForMathlib/` on a deletion clock, one retargetable foundry), the tier-promotion ladder that keeps throughput from eroding architecture, and the genericize-exactly-once timing rule. | When contemplating a second corpus, extracting shared tooling, or deciding whether the library is drifting from a theory toward a catalogue. |
| [`applied-areas.md`](applied-areas.md) | Scouting study for a *sibling* library in another applied field (econometrics / economics): who already holds what, a declaration-level Mathlib substrate audit at our exact pin, and a ranked set of open territories with a pillar/bridge architecture. | Before starting — or arguing against — a second corpus in an adjacent field; and at any pin bump, to re-check the "absent from Mathlib" list. |
| [`plans/2026-08-09-program-execution/`](plans/2026-08-09-program-execution/README.md) | Executable runbooks for the program the two docs above design: measure the architecture ratios, make the foundry's domain content data, open the second library, then genericize the apparatus and stand up `ForMathlib/` on their triggers. | When executing any step of the multi-field program — each file is a self-contained session prompt ending in machine-checkable acceptance criteria. |
| [`upstreaming.md`](upstreaming.md) | Log + playbook for contributing MathFin results upstream to brownian-motion / Mathlib (live: issue #440 → PR #446). | When submitting a `Foundations/` result upstream, or checking a contribution's status. |
| [`hammer-pilot-2026-06-06.md`](hammer-pilot-2026-06-06.md) | LeanHammer: the 2026-06-06 pilot evidence (0/10 kernel-accepted), why its verdict is **expired** rather than settled — it ran one Lean version off hammer's target and blamed the skew — and a runnable re-test against the current pin that names the three goals which actually decide adoption. | Before re-testing hammer, or when asked why the repo does not use it. Read the status block first: the answer is "unblocked but low priority", not "rejected". |
| [`values-review.md`](values-review.md) | The eight judgment lenses and the per-round verdict log — the review panel that closes every proof-content session. | To see the quality bar and what each round found, fixed, and deferred. |

## Archive

[`archive/`](archive/) keeps documents whose work is done or superseded, as a record:

- [`archive/roadmap-history.md`](archive/roadmap-history.md): the phase log, from May 2026 on.
- [`archive/upstream-consumption-review-2026-07-27.md`](archive/upstream-consumption-review-2026-07-27.md):
  the v4.31.0 → v4.32.0 bump. Its drift-sweep method is meant to be re-run at every pin bump.
- The dated reviews of 2026-05-28 to 2026-07-04 and the two superseded `*-deferred` notes.

## Cross-references

- For an overview of the library and its main results, see [`../README.md`](../README.md).
- For the contributor workflow (how to add a theorem, run the build, open a PR), see [`../CONTRIBUTING.md`](../CONTRIBUTING.md).
- For upstream-PR drafts targeting Mathlib / BrownianMotion, see [`../upstream/`](../upstream/).

## Provenance

The four core docs (`coverage.md`, `bridges.md`, `patterns.md`,
and the roadmap, now `archive/roadmap-history.md`) were promoted from root-level `FORMALIZATION_STATUS.md`,
`BRIDGE_AUDIT.md`, `LEARNINGS.md`, and a merge of `MATH_DEPTH_ROADMAP.md` +
`QUANTFIN_ROADMAP.md` during the 2026-05-23 reorganization.
