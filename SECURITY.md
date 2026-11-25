# Security policy

MathFin is a library of machine-checked mathematics. A security concern here is either a way to
make a false statement pass the checks, or a weakness in how the repository builds and publishes.

## Reporting a concern

Please do not open a public issue for a security concern. Email the maintainer at
**raphaelrrcoelho@gmail.com**, the address given in [`CODE_OF_CONDUCT.md`](CODE_OF_CONDUCT.md).
GitHub private vulnerability reporting is not enabled for this repository.

Say what you found, which files or workflows it touches, and how to reproduce it.

Ordinary mistakes in a statement, a docstring or a corpus entry are not security concerns. Open a
normal issue for those.

## What the library guarantees

The canonical check is a plain `lake build` from the repository root, as
[`CONTRIBUTING.md`](CONTRIBUTING.md) says. On top of it, the axiom audit
(`python3 -m tools.verify.axiom_audit_gen --write`, which regenerates
`MathFin/AxiomAuditGen.lean`) pins every theorem the corpus cites to `propext`,
`Classical.choice` and `Quot.sound`. A theorem that shows `sorryAx` or any other axiom has a gap.

The guarantee covers the Lean statements and their proofs. It does not cover the prose around
them: a docstring, a corpus `description` or a documentation page can say more than the statement
proves. [`AGENTS.md`](AGENTS.md) explains how to check a statement before citing it.

## The trust boundary

A result is only as trustworthy as what the build depends on:

- **The Lean toolchain** is fixed by [`lean-toolchain`](lean-toolchain).
- **Mathlib, BrownianMotion and the other Lake packages** are fixed to exact commits in
  [`lake-manifest.json`](lake-manifest.json). Changing a pin changes what is trusted.
- **BrownianMotion contains `sorry`s of its own.** A MathFin theorem that depends on one of them
  shows `sorryAx` in the axiom audit, which is why the audit exists.

Do not rely on a result if you cannot rebuild it at the pinned revisions.

## Tokens and secrets in CI

- `hf-publish.yml` refreshes the public Hugging Face dataset and uses the repository secret
  `HF_TOKEN`, a Hugging Face write token. It runs on pushes to `main` and by manual dispatch,
  never on `pull_request`.
- `publish-image.yml` pushes the `mathfin-verify` Docker image to GHCR with the workflow's
  `GITHUB_TOKEN` (`packages: write`), again on pushes to `main` and by manual dispatch. The image
  is public.
- `hammer-retest.yml` can log in to GHCR with an optional `GHCR_TOKEN`. Without it the job pulls
  the public image anonymously. It runs only by manual dispatch.
- `ledger-sweep.yml`, `import-shake.yml` and `release.yml` push to the repository with the
  workflow's `GITHUB_TOKEN` (`contents: write`). The ledger sweep also runs on pull requests that
  change a pin file; on a pull request from a fork GitHub gives that token read access only, so it
  cannot push there. The other two run only by manual dispatch.
- No workflow runs on `pull_request_target`, so code from a fork never runs with the repository's
  secrets. A first-time contributor's workflow runs wait for the maintainer's approval.

Never commit a token or key. If you find one in the history or in a workflow log, report it as
described above and do not use it.
