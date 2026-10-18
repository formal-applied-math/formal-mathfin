## Summary

<!-- One paragraph: what theorem / doc / tooling change does this add, and why. -->

## Checklist

### Attribution

- [ ] New files name you on both the `Copyright` and the `Authors:` line, not a name copied from another module's header.
- [ ] Commits are authored under your own name, and you are listed under Contributors in `README.md`.

### For Lean proof contributions

- [ ] Proof lives in `MathFin/<Section>/<Module>.lean`, not inlined in JSON (unless it's a single-line library wrapper).
- [ ] `@[expose] public section` present in the module after the docstring.
- [ ] `#print axioms <myTheorem>` shows only `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.
- [ ] **`lake build && lake lint`** both exit cleanly. CI runs the linter and `lake build` does
      not — a green build alone will still go red on a missing `def` docstring or an unused
      argument. Every `def`, `structure` and `inductive` needs a doc comment.
- [ ] `./scripts/lean-check.sh MathFin/<Section>/<Module>.lean` returns `"success": true`.
- [ ] Benchmark re-export shim added (or updated) in `benchmarks/*.json`.
- [ ] `metadata.formalization_status` set to `full` / `library_wrapper` / `reduced_core` (never `placeholder` to merge).
- [ ] `description` states what the entry **proves**, not the textbook theorem it is named after,
      and carries any narrowing in that same field — `description` and `formalization_scope` are
      the only fields published to the HF dataset, so a limit stated only in the PR body or in
      `metadata.provenance` does not ship.
- [ ] If the result bears on an entry in `docs/open-problems.md`, that entry is reconciled in the
      same PR — the repo must not list a problem as open and prove it in the same tree.
- [ ] `docs/coverage.md` row added / updated.
- [ ] `python3 -m tools.verify.axiom_audit_gen --write` re-run (regenerates `MathFin/AxiomAuditGen.lean`).
- [ ] `python3 -m tools.verify.ledger status` exits 0 (all entries fresh).
- [ ] `docker compose -f docker/docker-compose.yml run --rm --entrypoint python3 verify -m pytest tests/ -q` passes.

### For documentation contributions

- [ ] No dead relative links introduced.
- [ ] File referenced from `docs/README.md` or the appropriate index if it is new.

### For Python tooling contributions

- [ ] Host-side, Python stdlib only (no new deps unless discussed).
- [ ] `pytest tests/` passes.

## Related issues

Closes #
