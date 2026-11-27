# The cátedra: agents that work the open-problem catalogue

Status: adopted 2026-11-20, decisions below. Phase 0 built 2026-11-26: the chairs in
`.claude/agents/`, the skill `.claude/skills/catedra/`, the catalogue fields and the comparator
configs (`tools/verify/catedra.py`), the shared daemon (`docker/docker-compose.shared.yml`,
`scripts/lean-check-shared.sh`).

## Why, and the one thing to copy

alphaXiv's *A Society of AI Scientists* (November 2026) let 936 agents in 35 labs publish 936
empirical studies on a shared preprint server for twelve weeks. Their weak point was checking.
Text-only reviewers flagged 11 of 16 flawed drafts, and also 10 of 16 drafts that had fixed and
disclosed the flaw. Once an editor's objections were turned into scripts and run on the data, the
major ones overturned the headline conclusion in 49% of cases. The claims were as good as the
checking.

Mathematics has a perfect checker. In a cátedra working in Lean, peer review does not decide
whether a proof is right; the kernel does. What review still has to decide is whether the Lean
statement says what the source asks. That is the failure this library already knows best: the
statement quietly says less than the prose (CLAUDE.md, "the last step of every session").
So the cátedra puts its review effort on faithfulness, and leaves correctness to Lean.

## What it is built from

The cátedra is Claude Code, run the way this library is already built, with agents and a
maintainer in the loop. It is not the foundry. The foundry merged three pull requests into the
library (#123, #124, #500), all textbook-sized, and its shape (one headless session, 60 turns,
500k tokens per issue) suits unattended easy work. Open problems need reading papers, judging
definitions, long iteration and a human decision at two points. Three of the foundry's practices
carry over as checks, not as infrastructure: the vacuity probe (the hypotheses do not prove
`False`), the disproof probe (`¬ conclusion` is not provable), and a notebook of failed attempts.

Everything the cátedra shares already exists:

| Shared object | Where | Role |
|---|---|---|
| The catalogue | `docs/research-problems/problems.json` | the archive: one record per problem, its evidence, its Lean status |
| The statements | `MathFinFrontier/OpenProblems/` | each problem stated in Lean, closed by `sorry` |
| The rooms | one GitHub issue per problem, and one per missing object | discussion, attempt notes, decisions |
| The map | `docs/blueprint_frontier.toml`, `MathFin/Blueprint.lean` | what each problem builds on, and what it needs |
| The library | `MathFin/` | where a solved problem lands, proved and tagged |
| The corpus | the local literature corpus: the q-fin arXiv papers and the field's open-access papers outside arXiv, built by the private `mathfin-corpus` repo, never committed | what the Scout reads |
| The pin | `lake comparator` (`.github/workflows/comparator.yml`) | proof that a delivered theorem states exactly the frontier statement |

## The chairs

Each chair is an agent definition in `.claude/agents/<chair>.md`. Its brief carries the library's
rules: survey the library first, never claim more than the statement proves, no parallel objects,
no aliases. The model defaults to Sonnet (the maintainer's standing preference). A chair's output is
always a file, a pull request or an issue comment, never just a chat message.

### 1. Scout: finds problems

- **Input:** passages from the local literature corpus, each with a paper id and a page (the
  openness scan and the full-text search of the private `mathfin-corpus` repo), plus explicit
  lists (surveys, problem sessions, book chapters).
- **Work:**
  1. **Triage each passage:** is it a precise mathematical question, is it stated as open, what
     exactly is open? Drop roadmap sentences ("we conclude with open questions").
  2. **Merge duplicates**, including the same question asked in several papers. Every source
     stays attached.
  3. **Search for a resolution.** Read the papers citing the source after its date (OpenAlex), the relevant abstracts, and the full PDF whenever a candidate seems to close it.
- **Output:** catalogue records in the existing schema. A record whose openness evidence is the
  author's own sentence is class A by construction. Records it cannot settle go to the dated
  candidates file as leads, never into the catalogue.
- **Gate:** an adversarial pass. A second Scout run gets only the record and tries to kill it,
  as in round 6.
- **Lean:** none.

### 2. Formalizer: states problems

- **Input:** a catalogue record whose Lean status is `statable`, plus the source's text.
- **Work:**
  - Write the statement in `MathFinFrontier/OpenProblems/`, consuming library objects wherever
    they exist.
  - Quote the source passage in the module docstring.
  - Write a faithfulness note arguing each hypothesis and the conclusion from the source.
- **Anchors (kernel-grade evidence that the statement is not misstated):**
  1. Prove at least one known case from the record's `known_results` against the same
     hypotheses: for MF-OP-016 the case `d = 1`, for MF-OP-008 the converse.
  2. A vacuity probe: the hypotheses are satisfiable, shown by a proved instance.
  3. A disproof probe, where cheap.
- **Output:** a pull request with the statement and its anchors. Each anchor is a theorem in
  `MathFinFrontier/` with a real proof.
- **Lean:** CI (`lean-build.yml`), or the shared daemon.

### 3. Referee: the faithfulness review

- **Input:** the source passage, the Lean statement, and the docstrings of the declarations it
  uses. Not the Formalizer's note or its reasoning. The Referee forms its view first and reads
  the note only after.
- **Work:**
  - List every difference between the question and the statement: dropped or added hypotheses,
    a weakened conclusion, a junk value hiding a case, a different object.
  - Give a verdict: faithful / faithful with a disclosed narrowing / not faithful.
- **Gate:** a not-faithful verdict goes back to the Formalizer, at most twice, then to the
  maintainer. A narrowing must be written into the record and the docstring.
- **Output:** a PR review comment.
- **Lean:** none.
- **The human step:** the maintainer merges the statement PR. That merge pins the statement.
  From then on it changes only through a new PR that says why.

### 4. Prover: proves stated problems

- **Input:** a pinned statement, the issue's notes from earlier attempts, and the source's proof
  if one is claimed (MF-OP-008, MF-OP-017).
- **Work:**
  - Plan the proof as a list of lemmas, posted to the issue first.
  - Prove the lemmas in `MathFin/` modules, each where the library's layers say it belongs,
    generalized when that is the right lemma.
  - Assemble the main theorem in `MathFin/`, under a name of its own.
- **Gate (all kernel-grade, all existing tools):**
  - the build is green;
  - the axiom audit passes;
  - `lake comparator` holds, with the frontier statement as challenge and the `MathFin`
    theorem as solution;
  - the values gates and the ratchets pass.
- **Delivery:** delete the frontier theorem, tag the `MathFin` theorem in `MathFin/Blueprint.lean`
  under the node's label, delete the frontier node, set the record to `solved` with its
  declarations, add a corpus entry, and close the issue. The merge is the maintainer's.
- **On failure:** append what was tried, what blocked it and the lemmas already proved to the
  issue. The next attempt starts from that comment.
- **Lean:** the shared daemon (fast iteration), confirmed on CI.

### 5. Disprover: looks for counterexamples

- **Input:** a pinned statement whose conjectured direction is in doubt.
- **Work:** numerics first, in Python, in a scratch directory: a linear program over couplings
  for mixability, simulation for SABR tails, a parameter sweep for an inequality. A numerical
  counterexample is a lead, not a result. The Formalizer then states `¬ statement` for the
  specific instance, and the Prover proves it.
- **Output:** an issue comment with the numerics, then a pull request if a Lean counterexample
  follows.

### 6. Builder: builds what blocked problems need

- **Input:** `python3 -m tools.verify.research_problems needs`, the missing objects ranked by how
  many problems each blocks (convex order, nondominated models, …).
- **Work:**
  - Propose the definition on its issue: what it is built on and what it replaces, with no
    parallel object.
  - After the maintainer accepts the design, write it with its basic API and one bridge
    theorem tying it to an existing object.
- **Output:** a pull request. Once merged, the records it blocked move from `blocked` to
  `statable`, which `test_research_problems` enforces.

## The life of a problem

```
passage ──Scout──▶ candidate ──adversarial pass──▶ record (open | resolution_reported)
                                                      │
                     ┌──── blocked ◀── needs ─────────┤
                     │      Builder                   ▼
                     └────────────────────────▶ statable ──Formalizer + anchors──▶ statement PR
                                                                    │
                                                         Referee ◀──┘
                                                            │  maintainer merges = pinned
                                                            ▼
                              Disprover ◀──── stated ────▶ Prover
                                 │                          │
                     ¬statement proved ──▶ disproved    comparator ✓ ──▶ solved (maintainer merges)
```

A record never leaves the catalogue. Solved, disproved and stalled records keep their history, as
MF-OP-006 and MF-OP-007 do. A blocked record is kept: its `needs` are the Builder's queue.

## Phases

Each phase ends at an exit criterion that can be checked, not at a date.

**Phase 0: scaffolding (about one session).**
- The six agent definitions, and the skill `/catedra <MF-OP-id>`, which reads a record's Lean
  status and runs the next chair.
- Three catalogue fields:
  - `formalization.lean_statement.pinned` (the merge commit);
  - `review.referee` (the verdict and its comment link);
  - `attempts` (counts by chair).
- A comparator config per frontier problem (`comparator/<MF-OP-id>.json`, read by
  `comparator.yml`).
- The shared-daemon setup from memory, made a script: a mem-override file and a flock wrapper.

Exit: `/catedra MF-OP-016` runs end to end on the existing statement and produces a Referee
comment.

**Phase 1: one solved problem (MF-OP-017, complete mixability).**
- Why this one: the statement is already pinned, so it needs only a Referee pass. A 6-page
  claimed proof exists (Shmalo, November 2026). The mathematics is elementary probability
  (quantile grids, linear tilts, pairing). A kernel-checked proof settles a conflict between
  two unrefereed claims.
- Order:
  1. A Referee pass on the existing statement.
  2. The Prover reads Shmalo's proof and posts the lemma plan.
  3. The lemmas go in `MathFin/Risk/` next to the aggregation results.
  4. The comparator check, then delivery.
- If the proof breaks, the place it breaks is the result. The record then says the reported
  resolution has a gap there.
- In parallel: the Referee on MF-OP-008 and MF-OP-016.

Exit: MF-OP-017 is `solved` with a kernel-checked theorem that the comparator matches to the
pinned statement, or the record names the gap in the claimed proof.

**Phase 2: a catalogue of a hundred (the Scout at scale).**
- Run the scan over the local corpus.
- Triage in batches of about 50 passages per agent.
- Search for resolutions through citing papers.
- An adversarial pass on every survivor.
- Mine explicit lists alongside: the rest of Wang's survey, the open-question sections of
  *Peacocks* and the rough-volatility book, Obłój's Skorokhod survey,
  Embrechts–Puccetti–Rüschendorf, and Oberwolfach problem sessions.

Exit: at least 100 records with class A or B evidence, each with its Lean status set, and its
`needs` set when blocked. A dated audit gives the attrition at each step.

**Phase 3: statements at scale.** The Formalizer and the Referee on every `statable` record.

Exit: every statable record is stated and pinned, or its PR names what stopped it, and the
Referee's agreement rate is reported.

**Phase 4: attack.**
- The Prover and Disprover on pinned statements, ordered by:
  1. claimed resolutions first (proof-guided);
  2. then elementary problems;
  3. then the rest.
- A per-problem budget, with notes after each attempt.

Exit: reported per month as problems solved, disproved and attempted, tokens per problem, and
the gaps found in claimed proofs.

**Phase 5: the Builder.** It runs continuously from Phase 2 on, in the order of the `needs`
ranking.

## Budget

These are estimates to be replaced by measurements in Phase 0–1.

| Work | Volume | Tokens |
|---|---|---|
| Scout triage | ~2,500 passages (6 of 60 sampled papers had hits, ~2 passages each) | ~5M |
| Resolution checks | ~400 candidates × ~40k | ~16M |
| Adversarial pass | ~200 survivors × ~40k | ~8M |
| Formalizer + Referee | per statement ~200k + ~50k | ~25M for 100 statements |
| Prover | per problem, capped | MF-OP-017 cap 5M; others set per problem |

Lean capacity is the binding constraint on this box: one Lean process. The Prover uses the shared
daemon, behind a queue. Everyone else checks on CI, with no limit on parallel runs and 10–20
minutes per check. A bigger remote machine behind the daemon's TCP port is the next step if
proving queues up.

## Honesty rules

1. **Solved means a kernel-checked proof of a pinned statement**, plus a comparator pass. A proof
   of anything else is not reported against the record.
2. **Open means a dated source says so.** Absence of a resolution is a lead, never a record.
3. **Credit:** a formalized proof from a paper names its author in the module header (a port: the
   attribution rule sends that to the maintainer) and in the record. A resolution the cátedra
   finds itself says which chairs, which model and which session produced it.
4. **Failures are recorded:** attempts, gaps found in claimed proofs and Referee rejections are
   counted and published with the successes.
5. **The two human steps stay human:** pinning a statement and merging a result. A chair never
   merges its own work.

## Measures

- Catalogue size by status and by Lean status.
- The share of records that are statable.
- The Referee's rejection rate, and the share of rejections the maintainer upholds.
- Problems solved and disproved per month.
- Gaps found in claimed proofs.
- Tokens per solved problem.
- False opens: records later found closed. The round-1 baseline was 16 of 36 wrong.

## Decisions (2026-11-20)

The maintainer delegated the five open decisions; they were taken as follows.

1. **Citations come from OpenAlex**, which needs no key, with Semantic Scholar's unauthenticated
   API as a fallback. No key is requested, since requesting one would mean registering the
   maintainer's email with a third party.
2. **The Referee runs on Sonnet**, like every chair (the standing preference). Its independence
   comes from what it is not shown (the Formalizer's note and reasoning) and from the
   kernel-checked anchors, not from a different model. Revisit this if the Referee's
   rejections are rarely upheld, or if anchors catch what the Referee missed.
3. **Budget:**
   - 30M tokens a month while the cátedra runs.
   - Prover caps: MF-OP-017 5M; other problems 3M by default, raised to 10M only when the
     issue notes show lemmas proved since the last attempt.
   - Phase 1 measures real costs, and these numbers are revised against them.
4. **The definition issues leave the foundry's queue.** #532–#536 and #538–#544 are
   `status:blocked-design` until the maintainer accepts the Builder's design on each. They
   then return to `status:ready`.
5. **No publishing before results.** When Phase 2 reaches 100 records, the catalogue joins the
   existing Hugging Face export (`tools/verify/hf_dataset.py`): open problems with their Lean
   statements and evidence. alphaXiv's agent server waits until kernel-checked resolutions
   exist to show.
