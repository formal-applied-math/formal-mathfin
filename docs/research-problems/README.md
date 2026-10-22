# Mathematical-finance research problems

This catalogue records precise research questions across mathematical finance,
including topics whose Lean prerequisites have not yet been built. The
[issue index](https://github.com/formal-applied-math/formal-mathfin/issues/177)
is the discussion entry point; [problems.json](problems.json) stores the structured
records. The [2026-10-21 audit](audit-2026-10-21.md) explains the first batch.

Last literature review: **2026-10-21**. Five new open questions, two existing
formal resolutions, and one reported literature resolution are recorded below.
An `open` status records a sourced assessment as of its review date.

| Stable ID | Problem | Mathematics | Lean in this repository | Issue |
|---|---|---|---|---|
| MF-OP-001 | Pathwise uniqueness for the square-root rough-Heston variance equation | open | not started | [#326](https://github.com/formal-applied-math/formal-mathfin/issues/326) |
| MF-OP-002 | Physical Stefan uniqueness when jumps accumulate at time zero | open | not started | [#327](https://github.com/formal-applied-math/formal-mathfin/issues/327) |
| MF-OP-003 | Relaxed equilibrium existence with action-dependent diffusion under time inconsistency | open | not started | [#328](https://github.com/formal-applied-math/formal-mathfin/issues/328) |
| MF-OP-004 | Integrable Schrödinger potentials for continuum SPX/VIX calibration | open | not started | [#329](https://github.com/formal-applied-math/formal-mathfin/issues/329) |
| MF-OP-005 | A semistatic FTAP for calibrated equivalent martingale measures with finite entropy | open | not started | [#330](https://github.com/formal-applied-math/formal-mathfin/issues/330) |
| MF-OP-006 | Convexity of the American-put exercise boundary for 0 <= q <= r | solved | proved | [#175](https://github.com/formal-applied-math/formal-mathfin/issues/175) |
| MF-OP-007 | Explicit semialgebraic certificate for the full SVI no-butterfly domain | solved | proved | [#174](https://github.com/formal-applied-math/formal-mathfin/issues/174) |
| MF-OP-008 | Uniqueness of the one-period Gaussian Kyle equilibrium | resolution reported | not started | — |

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
- `issue_number` and `issue_url` connect records to GitHub. Update the record and
  issue together when a result changes status. This table is a summary of the JSON.

The organization draws on [Ulam AI's UnsolvedMath](https://huggingface.co/datasets/ulamai/UnsolvedMath):
stable IDs, mathematical statements, subject metadata, provenance, and dated reviews.
The records here were researched independently; no Ulam problem text was imported.

The [older survey](../open-problems.md) retains additional leads. Its unreviewed
entries are not part of this dated batch. Research issues use `open-problem` and
`status:research`; the latter keeps them outside the `status:ready` implementation
queue. When a formalization task is scoped, open a linked `type:proof` issue.
