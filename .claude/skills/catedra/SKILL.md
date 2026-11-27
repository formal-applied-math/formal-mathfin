---
name: catedra
description: Run the next chair of the cátedra on one open problem of the catalogue (docs/research-problems/problems.json). Usage `/catedra MF-OP-017`, or `/catedra MF-OP-017 disprover` to name the chair. Reads the record's state, runs the chair as a sub-agent, and records what it produced.
---

# /catedra <MF-OP-id> [chair]

The cátedra is the six chairs of `docs/specs/2026-11-20-catedra-design.md`, each an agent in
`.claude/agents/`: `scout`, `formalizer`, `referee`, `prover`, `disprover`, `builder`. This skill
moves one problem one step.

## 1. Read the state

```bash
python3 -m tools.verify.catedra status <id>
```

It prints the record's statuses, the Lean statement and its file, the pin, the Referee's verdict,
the attempts, and `next`: the chair the rule in `tools/verify/catedra.py` (`next_chair`) picks,
with `why`. A chair named in the arguments overrides it (the rule never picks the Disprover by
itself: name it when the conjectured direction is in doubt). If `next` is null, say why and stop.

## 2. Run the chair

Start the chair as a sub-agent (`subagent_type` = the chair's name; the definitions set Sonnet).
Give it, and only it:

- the record id and the issue URL;
- an output path in the session's scratchpad, `catedra-<id>-<chair>.md`;
- for the **Referee**: nothing else. Do not paste the record, the module docstring, the node
  prose or an earlier comment. It reads the source and the statement itself, and its
  independence is what it is not shown;
- for the **Prover**: the Lean slot. Bring the daemon up shared first (`docker compose -f
  docker/docker-compose.yml -f docker/docker-compose.shared.yml up -d --force-recreate
  lean-repl`, wait for READY in its logs) unless another session holds the slot, and say that it
  checks only through `scripts/lean-check-shared.sh`;
- for the **Formalizer**, **Prover**, **Disprover**, **Builder**: a worktree of its own
  (`isolation: worktree`), since they edit the repo.

## 3. Record what it produced

- **Every chair:** add one to `attempts.<chair>` in the record.
- **Referee:** set `review.referee` to `{"verdict", "date", "comment"}` once the comment is posted.
  Before posting, show the maintainer the comment text (it goes out under their account). The
  comment opens with one line saying it is the cátedra's Referee pass, by a Sonnet agent that saw
  the source and the statement and not the Formalizer's note. A `faithful_with_narrowing`
  verdict means the narrowing is written into the record (`formalization.lean_statement.note`)
  and the module docstring, in the same pull request.
- **Formalizer:** its pull request; after the maintainer merges it, set
  `formalization.lean_statement.pinned` to the merge commit, the PR number and
  `python3 -m tools.verify.catedra hash <id>`.
- **Prover:** its lemma plan and failure notes go on the issue; its delivery is a pull request
  that the maintainer merges, never the chair.
- **Disprover:** its numerics go on the issue, shown to the maintainer first like the Referee's.

Then run `python3 -m tools.verify.catedra check` and `python3 -m tools.verify.research_problems
check`, and put the record changes on a branch and in a pull request.

## Rules that do not bend

- Solved means a kernel-checked proof of the pinned statement and a comparator pass.
- Pinning a statement and merging a result are the maintainer's two steps.
- Failures are recorded as carefully as successes: attempts, gaps found in claimed proofs,
  Referee rejections.
