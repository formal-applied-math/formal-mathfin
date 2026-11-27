# Mathematical-finance research problems

This catalogue records precise research questions in mathematical finance, each with a
self-contained statement, dated sources and a resolution search. It is written for a researcher
choosing a problem and for an agent looking for well-posed open questions. The records are in
[problems.json](problems.json); the table below summarises them. The
[issue index](https://github.com/formal-applied-math/formal-mathfin/issues/177) is the discussion
entry point.

## Which artefact owns what

Four artefacts concern mathematics the library has not proved. Each has one job.

| Artefact | What it holds | Owns |
|---|---|---|
| [problems.json](problems.json) (`MF-OP-NNN`) | Open problems of the field, as dated records | the question, its mathematical status, its sources |
| [`docs/blueprint_frontier.toml`](../blueprint_frontier.toml) | The [frontier](../glossary.md#frontier): results and definitions the library intends to prove or build, stated in words | the plan for the library |
| [`MathFinFrontier/`](../../MathFinFrontier.lean) | Lean statements of either kind, each closed by `sorry` | the formal statement |
| [open-problems.md](../open-problems.md) | The earlier survey and the pool of unverified candidates | leads not yet admitted |

The links run as follows. A record's `formalization.lean_statement` carries `blueprint`, the label
of the frontier node that names the question; `needs`, the labels of frontier definitions that
must exist before the question can be stated in Lean; and, once it is stated, `lean`, the name of
the theorem in `MathFinFrontier/`. The frontier node carries the same name in its own `lean`
field. `tests/test_research_problems.py` checks every link in both directions.
`MathFinFrontier` is a library target of `lakefile.lean` and a default target, so a plain
`lake build` elaborates it and prints one `declaration uses 'sorry'` warning per statement. The
umbrella `MathFin` does not import it, and the axiom audits do not see it.

## How a problem is admitted

A problem enters as a record with these parts.

- A statement that stands alone: the objects, the hypotheses and the question, with
  `statement_origin` saying whether it is a source's own question or a formulation of a stated
  extension or residual case.
- Sources, each with a locator, a role and a finding. The newest source that treats the question
  as open is dated in `review.latest_openness_evidence_date`.
- A resolution search: the queries run, the nearby results checked, and the conclusion. The
  search date `review.checked_at` never refreshes the date of the evidence.
- A `blueprint` node on the frontier. A question the frontier does not yet name gets a frontier
  entry first.

A question without a proof-or-counterexample form, such as a debate or a programme, is not
admitted. A question whose Lean statement is not yet possible is admitted all the same:
`lean_statement.status` records that, and it never decides whether a problem is catalogued.

## What the statuses mean

`mathematical_status` is a claim about the field:

- `open`: a scoped question with dated supporting evidence and a resolution search.
- `resolution_reported`: a paper claims to settle it and this catalogue has not checked the
  proof. The record says so and stays at this status until the claim is checked.
- `solved`: a resolution supported by the recorded evidence. A faithful kernel-checked proof
  qualifies.

`formalization.status` and `formalization.lean_statement.status` are claims about this
repository, independent of the first. A known theorem can need formalization, and an open
conjecture can have a formal statement. `lean_statement.status` is one of:

- `stated`: a `sorry`-closed theorem in `MathFinFrontier/`, named in `lean` and by the record's
  `blueprint` node. A proof of the theorem, or of its negation where the record says so, settles
  the problem.
- `statable`: every object exists in the library and the statement is not yet written.
- `blocked`: the frontier definitions in `needs` do not exist yet. They are what the library
  builds next; `python3 -m tools.verify.research_problems needs` ranks them.
- `not_a_proposition`: the question asks for a theory, hypotheses or a criterion. `needs` lists
  the objects candidate answers use.
- `proved`: the record is solved and the proof is in `MathFin/`, named in `declarations`.

## How to propose a problem

Open an issue labelled `open-problem` and `status:research`, with the statement, the sources and
the searches run, and a body line `Blueprint: <label>` naming the frontier node it advances. The
`status:research` label keeps it outside the `status:ready` implementation queue. The
maintainers add the record to `problems.json` after review. A lead that has no source asserting
openness belongs in the earlier survey until it has one. When a formalization task is scoped,
open a linked `type:proof` issue.

## How a solution is recorded

A solution to a stated problem is a proof of the `MathFinFrontier` theorem. It moves into
`MathFin/`, is tagged in `MathFin/Blueprint.lean` under the frontier label, and the frontier
entry is deleted. The pinned statement moves unchanged to `Catedra/<ID>/Challenge.lean`, beside
`Catedra/<ID>/Solution.lean`, which restates it and proves it from the `MathFin` theorem:
`lake comparator` (`comparator/<ID>.json`, `.github/workflows/comparator.yml`) checks that the two
state the same theorem, every month as well as at delivery. The record then becomes `solved` with its
Lean declarations listed, its `history` gains the date and reason, and the record is never
removed. A solution that arrives as a paper without a Lean proof is recorded as
`resolution_reported` until it is checked. IDs are permanent. The record and its issue are
updated together.

## Catalogue

Last literature review: 2026-11-19 (round 6, [audit](audit-2026-11-19.md)): eighteen records.
Fourteen are open questions, two are formal resolutions proved here, and two are reported
resolutions not yet checked. Three are stated in Lean, closed by `sorry`, in
`MathFinFrontier/OpenProblems/`: MF-OP-008, MF-OP-016 and MF-OP-017. An `open` status records a
sourced assessment as of its review date. The [first audit](audit-2026-10-21.md) explains the
first batch.

| Stable ID | Problem | Mathematics | Lean in this repository | Needs | Issue |
|---|---|---|---|---|---|
| MF-OP-001 | Pathwise uniqueness for the square-root rough-Heston variance equation | open | blocked | `def:stochastic-volterra-equation` | [#326](https://github.com/formal-applied-math/formal-mathfin/issues/326) |
| MF-OP-002 | Physical Stefan uniqueness when jumps accumulate at time zero | open | blocked | `def:supercooled-stefan-solution` | [#327](https://github.com/formal-applied-math/formal-mathfin/issues/327) |
| MF-OP-003 | Relaxed equilibrium existence with action-dependent diffusion under time inconsistency | open | not one proposition | `def:relaxed-controlled-diffusion` | [#328](https://github.com/formal-applied-math/formal-mathfin/issues/328) |
| MF-OP-004 | Integrable Schrödinger potentials for continuum SPX/VIX calibration | open | not one proposition | `def:calibrated-martingale-measures` | [#329](https://github.com/formal-applied-math/formal-mathfin/issues/329) |
| MF-OP-005 | A semistatic FTAP for calibrated equivalent martingale measures with finite entropy | open | not one proposition | `def:calibrated-martingale-measures`, `def:semistatic-strategy` | [#330](https://github.com/formal-applied-math/formal-mathfin/issues/330) |
| MF-OP-006 | Convexity of the American-put exercise boundary for 0 <= q <= r | solved | proved | — | [#175](https://github.com/formal-applied-math/formal-mathfin/issues/175) |
| MF-OP-007 | Explicit semialgebraic certificate for the full SVI no-butterfly domain | solved | proved | — | [#174](https://github.com/formal-applied-math/formal-mathfin/issues/174) |
| MF-OP-008 | Uniqueness of the one-period Gaussian Kyle equilibrium | resolution reported | stated (`sorry`) | — | [#537](https://github.com/formal-applied-math/formal-mathfin/issues/537) |
| MF-OP-009 | Does the expected signature determine the law of the signature of Brownian motion stopped at a domain exit time? | open | blocked | `def:path-signature` | [#545](https://github.com/formal-applied-math/formal-mathfin/issues/545) |
| MF-OP-010 | Robust American hedging duality for non-càdlàg payoffs under semimartingale-characteristic uncertainty | open | blocked | `def:nondominated-model` | [#546](https://github.com/formal-applied-math/formal-mathfin/issues/546) |
| MF-OP-011 | A mimicking Markov martingale for every peacock, Markov for the raw filtration | open | blocked | `def:convex-order`, `def:markov-martingale` | [#547](https://github.com/formal-applied-math/formal-mathfin/issues/547) |
| MF-OP-012 | Uniqueness for the Zakai equation of singular-control filtering when control jumps accumulate | open | blocked | `def:zakai-equation` | [#548](https://github.com/formal-applied-math/formal-mathfin/issues/548) |
| MF-OP-013 | The optimal local control on the free boundary of the dividend problem for n ≥ 2 insurers | open | not one proposition | `def:optimal-dividend-problem` | [#549](https://github.com/formal-applied-math/formal-mathfin/issues/549) |
| MF-OP-014 | The duality l(L^∞) = E' for the robust multi-period binomial model | open | blocked | `def:nondominated-model` | [#550](https://github.com/formal-applied-math/formal-mathfin/issues/550) |
| MF-OP-015 | The k^{3/2} correction to the right tail of absorbed SABR for ρ < 0 | open | blocked | `def:sabr-model` | [#551](https://github.com/formal-applied-math/formal-mathfin/issues/551) |
| MF-OP-016 | Complete mixability of the uniform law on a convex body of ℝ^d for n ≥ d + 1 | open | stated (`sorry`) | — | [#552](https://github.com/formal-applied-math/formal-mathfin/issues/552) |
| MF-OP-017 | Complete mixability of absolutely continuous laws on a bounded interval for all large n | resolution reported | stated (`sorry`) | — | [#553](https://github.com/formal-applied-math/formal-mathfin/issues/553) |
| MF-OP-018 | When do the sums with given marginals have a smallest element in convex order? | open | not one proposition | `def:convex-order` | [#554](https://github.com/formal-applied-math/formal-mathfin/issues/554) |

## Record conventions

- IDs are permanent. Reordering, a revised title, or a solution never changes an ID.
- `statement` contains Markdown and LaTeX; `statement_origin` distinguishes an
  author's question from a formulation of a stated extension or residual case.
- `area` and `tags` describe the subject. `difficulty` stays `unassessed` unless
  a named assessment supports it. The GitHub `difficulty:hard` label describes
  the expertise required, not a calibrated estimate of how hard the problem is.
- `mathematical_status` and `formalization.status` answer different questions.
  A known theorem can need formalization; an open conjecture can have a formal statement.
- Every source has a locator, role, and finding. `review.checked_at` is the search
  date; `latest_openness_evidence_date` is the date of the actual source. A new
  search never silently refreshes an old openness assertion.
- `known_results`, `nearby_results_checked`, and `resolution_searches` record the
  boundary of the claim and make later reviews reproducible.
- `history` retains status changes. Solved entries remain in the catalogue.
  `resolution_reported` records an unchecked claim, regardless of how it was produced.
  A faithful kernel-checked proof qualifies as solved.
- `formalization.lean_statement` says whether the question can be stated in Lean against the
  library: `stated` (a `sorry`-closed theorem in `MathFinFrontier/`, named in `lean` and by the
  record's `blueprint` node), `statable`, `blocked` (by the frontier nodes in `needs`),
  `not_a_proposition` (the question asks for a theory, hypotheses or a criterion; `needs` lists
  the objects candidate answers use), or `proved`. It never decides whether a problem is
  catalogued. A blocked problem stays, and its `needs` are what the library builds next:
  `python3 -m tools.verify.research_problems needs` ranks them, and
  `tests/test_research_problems.py` keeps the links real.
- The cátedra's fields (`docs/specs/2026-11-20-catedra-design.md`, `tools/verify/catedra.py`):
  `formalization.lean_statement.pinned` is the merge that pinned a statement (`commit`, `pr`) and
  `statement_sha256`, the hash of its text, so a statement changes only through a pull request
  that says why and updates the hash; `review.referee` is the Referee's verdict on faithfulness
  (`verdict`, `date`, `comment`); `attempts` counts each chair's runs. Every stated problem has a
  comparator config `comparator/<ID>.json`. `python3 -m tools.verify.catedra check` holds them.
- `issue_number` and `issue_url` connect records to GitHub. This table is a summary of the JSON.

The organization draws on [Ulam AI's UnsolvedMath](https://huggingface.co/datasets/ulamai/UnsolvedMath):
stable IDs, mathematical statements, subject metadata, provenance, and dated reviews.
The records here were researched independently; no Ulam problem text was imported.

The [older survey](../open-problems.md) retains additional leads. Its unreviewed entries are not
part of this dated batch.
