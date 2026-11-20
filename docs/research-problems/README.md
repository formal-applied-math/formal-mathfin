# Mathematical-finance research problems

This catalogue records precise research questions across mathematical finance,
including topics whose Lean prerequisites have not yet been built. The
[issue index](https://github.com/formal-applied-math/formal-mathfin/issues/177)
is the discussion entry point; [problems.json](problems.json) stores the structured
records. The [2026-10-21 audit](audit-2026-10-21.md) explains the first batch.

Last literature review: **2026-11-19** (round 6, [audit](audit-2026-11-19.md)): eighteen
records, of which fourteen are open questions, two are formal resolutions proved here, and two
are reported resolutions not yet checked. Three are stated in Lean, closed by `sorry`, in
`MathFinFrontier/OpenProblems/`.
An `open` status records a sourced assessment as of its review date.

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
- `issue_number` and `issue_url` connect records to GitHub. Update the record and
  issue together when a result changes status. This table is a summary of the JSON.

The organization draws on [Ulam AI's UnsolvedMath](https://huggingface.co/datasets/ulamai/UnsolvedMath):
stable IDs, mathematical statements, subject metadata, provenance, and dated reviews.
The records here were researched independently; no Ulam problem text was imported.

The [older survey](../open-problems.md) retains additional leads. Its unreviewed
entries are not part of this dated batch. Research issues use `open-problem` and
`status:research`; the latter keeps them outside the `status:ready` implementation
queue. When a formalization task is scoped, open a linked `type:proof` issue.
