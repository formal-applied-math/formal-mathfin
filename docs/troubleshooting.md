# Troubleshooting

Each entry reads symptom, cause, fix. General failures come first. The last section covers the
Docker image, the REPL daemon and one maintainer machine. For the setup itself see
[onboarding.md](onboarding.md); the rules are in [CONTRIBUTING.md](../CONTRIBUTING.md).

## The toolchain does not match

Symptom: errors such as "failed to read file ... incompatible header" or "unknown package", or
Mathlib rebuilds from source.

Cause: the Lean version in use differs from `lean-toolchain`, or `.lake/` holds packages from an
earlier `lake-manifest.json`.

Fix: use the elan-managed toolchain the repository pins (run `lean --version` inside the
repository and compare with `lean-toolchain`). After a pull that changes `lean-toolchain` or
`lake-manifest.json`, run `lake exe cache get` and `lake build` again. If `.lake/` is corrupt, delete it and repeat.

## `lake exe cache get` fails

Symptom: the command errors on a download, or reports files it could not fetch.

Cause: a transient failure of the cache mirror, or a network proxy.

Fix: retry; CI retries it with a pause. If it keeps failing, `lake build` still works and builds
Mathlib from source, which takes hours, so retry the cache first.

## The first build is slow

Symptom: `lake build` runs for a long time on a fresh clone.

Cause: without the Mathlib cache, Mathlib compiles from source, and BrownianMotion and `MathFin`
always compile from source.

Fix: run `lake exe cache get` before `lake build`. Later builds are incremental. Check a single
module with `lake build MathFin.Models.Binomial.Model`. A fast edit-check loop is the REPL daemon
(see the last section).

## Out of memory

Symptom: a build or a check is killed (exit code 137, "Killed"), or the machine freezes.

Cause: a Lean process with Mathlib loaded needs several gigabytes, and two of them at once
overcommit a small machine.

Fix: run one Lean-loaded process at a time. Stop the REPL daemon before a `lake build`, and do not
run two builds together. Lower the Lake job count with `lake build -j 2` on a machine with little
memory, or run the build on a larger machine.

## Importers do not see my declarations

Symptom: `lake build` is green, but a benchmark snippet or another module reports an unknown
identifier or constant for a declaration in your new module.

Cause: the module lacks `@[expose] public section` after its docstring, so every declaration in it
is module-private. `tests/test_router.py` fails on this.

Fix: add `@[expose] public section` right after the module docstring, as in
`MathFin/Models/Binomial/Model.lean`. Also check that the module is listed in `MathFin.lean` and
that the importing file uses `public import`.

## The ledger shows stale or missing entries

Symptom: `python3 -m tools.verify.ledger status` prints STALE or MISSING, or
`tests/test_ledger.py` fails.

Cause: the ledger records, per entry, a hash of the snippet code, the transitive `MathFin` modules
it imports and the toolchain pins. Any change to those inputs makes the entry stale. A merge can
also drop a row, because git's text merge combines changes to a flat map without a conflict.

Fix: with the REPL daemon up, run `python3 -m tools.verify.ledger verify`, which re-verifies only
the stale entries, then `status` again. Do not edit `MathFin/` while it runs: rows verified after
the edit record the earlier hash and are stale again. Set up the merge driver and hook once per
clone so merges do not drop rows:

```bash
git config merge.mathfin-ledger.name "semantic merge for verification_ledger.json"
git config merge.mathfin-ledger.driver "python3 tools/verify/ledger_merge.py %O %A %B %L %P"
git config core.hooksPath .githooks
```

The driver unions disjoint verifications and drops an entry the two sides verified under
different inputs, so it re-verifies. If the driver was not set up, re-derive the ledger with
`status` and `verify` and do not resolve it by hand.

## A gate fails

Symptom: a file in `tests/` fails, or CI is red before the Lean build.

Fix by test:

- `tests/test_values.py`, stale `AxiomAuditGen.lean`: run
  `python3 -m tools.verify.axiom_audit_gen --write`.
- `tests/test_values.py`, forbidden text: remove `sorry`, `admit`, `native_decide`, `polyrith`,
  `?`-suggestion tactics, `hammer`, `loogle` or `leansearch` from `MathFin/`. Comments are
  exempt.
- `tests/test_values.py`, `rfl`-backed `full` entry: a definition closed by `rfl` is `reduced_core`,
  not `full`; the proof must do real work, or the status changes.
- `tests/test_doc_standard.py`: a module docstring lacks a section or cites a key missing from
  `docs/references.bib`; run `python3 -m tools.verify.doc_standard`.
- `tests/test_ratchet.py`: a debt count rose. The failure names the count; fix the cause rather
  than raising the baseline in `ratchet.json`.
- `tests/test_architecture.py`: a module is not in a layer, an import points against the layers,
  or a module is not connected to the library. See CONTRIBUTING, section 2.
- `tests/test_blueprint_issues.py`: an open math issue lacks its `Blueprint: <label>` line, or a
  frontier node has no issue. Run `python3 -m tools.verify.blueprint_issues check`.
- `tests/test_attribution.py`: a module header names someone other than its author, or the author
  is missing from Contributors in `README.md`.

## `docker compose pull verify` is denied or rate-limited

Symptom: the pull returns `denied` or `toomanyrequests`.

Cause: the image `ghcr.io/formal-applied-math/mathfin-verify` is public and needs no login, so
this is a rate limit on anonymous pulls or a stale credential in your Docker configuration.

Fix: retry later, or log in to `ghcr.io` with a personal access token that has the
`read:packages` scope (`docker login ghcr.io`), or run `docker logout ghcr.io` if a stale
credential is the cause.

---

## Maintainer's machine and Docker notes

The notes below concern the Docker image, the persistent REPL daemon (`scripts/lean-check.sh`,
`scripts/bench-check.sh`) and the memory limits of the maintainer's machine. They do not apply to
a plain `lake build`.

### Memory settings

The compose services default to four CPUs (`VERIFY_CPUSET`) and a 6 GB memory limit, so that a
runaway elaboration is killed in the container (exit code 137) and not on the host. The
maintainer's machine has about 15 GB of memory and runs a single Lean-loaded process at a time:
the daemon is the usual occupant, and `verify` runs, `leanchecker` and builds run with the
daemon down (`docker compose -f docker/docker-compose.yml down lean-repl`). Do not run
`docker compose build` locally: it repeats the whole Mathlib layer. The image is published by the
`publish-image.yml` workflow, and locally you only pull it. Corpus-scale sweeps and the
kernel replay run on CI runners, which have more memory.

### "unknown constant" after editing a single-file bind mount

Symptom: `lean-check.sh` or a benchmark run reports an unknown constant for a declaration that
exists and builds.

Cause: compose mounts some single files (`MathFin.lean`, `lakefile.lean`, `lake-manifest.json`,
`lean-toolchain`, `mathfin.toml`). A single-file mount pins the inode, and a rename-based write
(an editor save, `sed -i`, `mv`) replaces the host file, so a running container keeps the old
content. Directory mounts (`MathFin/`, `benchmarks/`) are not affected.

Fix: restart the service (`docker compose -f docker/docker-compose.yml restart lean-repl`), or
copy the file into the running container with `docker exec -i <container> sh -c 'cat >
/app/MathFin.lean' < MathFin.lean`, where `<container>` is the name `docker compose ps` shows.

### `lean-check.sh` is slow or falls back to the cold path

Symptom: the script reports that the daemon is unreachable and takes minutes.

Cause: the daemon is not running, or has not finished loading. The first load takes several
minutes.

Fix: start it and poll its log until READY appears (a streaming `logs -f | grep -m1` can hang, so
poll instead). A timeout right after a restart is usually a cold start; retry once it is warm.

```bash
docker compose -f docker/docker-compose.yml up -d lean-repl
docker compose -f docker/docker-compose.yml logs lean-repl | grep READY
```

### The daemon and `lake build` contend

Symptom: one of them stalls or is killed when both run.

Cause: both load the Mathlib environment, and they share the build-cache volume with one Lake
writer at a time.

Fix: stop the daemon before a build and restart it afterwards.

### The daemon reports errors the build does not

Symptom: `lake build` is clean, but `lean-check.sh` reports errors in a file that imports a
module you changed.

Cause: the daemon does not write `.olean` files for downstream imports.

Fix: run `lake build` or restart the daemon after changing a module that other files import.

### Timeouts on entry after entry during `ledger verify`

Symptom: a corpus-scale `ledger verify` fails on timeouts just above the cap, and keeps failing.

Cause: `LEAN_ELAB_TIMEOUT` defaults to 180 seconds in the compose file, enough to author one file
and too tight for a sweep. A timeout kills the REPL, the next entry pays the reload out of its own
budget and times out too, and the failure repeats.

Fix: stop the sweep, raise the cap, restart the daemon and rerun.

```bash
docker compose -f docker/docker-compose.yml down lean-repl
LEAN_ELAB_TIMEOUT=600 docker compose -f docker/docker-compose.yml up -d lean-repl
python3 -m tools.verify.ledger verify
```

For a large sweep use the `ledger-sweep.yml` workflow on a runner instead
(`gh workflow run ledger-sweep.yml --ref <branch> -f scope=stale`).

### The daemon stops answering after a long session

Symptom: `lean-check.sh` returns nothing, and the log shows the request but no result.

Cause: the daemon's memory grows over many checks until it sits at the container limit. An empty
response, not an error, is the sign.

Diagnosis: `docker stats --no-stream` shows memory at the `mem_limit`.

Fix: restart the daemon. On a long session, restart it before it wedges.

### "Read-only file system" when a container step writes to `docs/`

Symptom: a command inside the container fails writing a file under `docs/`.

Cause: compose mounts `tools/`, `benchmarks/`, `tests/`, `mathfin.toml` and the Lake files, but not
`docs/`.

Fix: write the output on the host, for example
`docker compose -f docker/docker-compose.yml run --rm -T --entrypoint sh verify -c 'lake exe blueprint_export MathFin.Blueprint' > docs/blueprint_nodes.json`.
Check that the captured output parses before overwriting a tracked file, because compose may print
lifecycle messages. `blueprint_export` loads the environment, so run it with the daemon down.
