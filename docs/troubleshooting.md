# Build & environment troubleshooting

Quick reference for common failures. Each entry follows: **symptom → cause → fix**.

---

## GHCR `docker pull` fails with "unauthorized"

**Symptom:** `docker compose pull verify` returns `unauthorized: unauthenticated`.

**Cause:** You are not logged in to the GitHub Container Registry, or your
OAuth token does not have the `read:packages` scope.

**Fix:**
```bash
# Refresh the gh auth scope first if needed:
gh auth refresh -h github.com -s read:packages

# Then log in:
TOKEN=$(grep -E '^[[:space:]]+oauth_token:' ~/.config/gh/hosts.yml | head -1 | awk '{print $2}')
echo "$TOKEN" | docker login ghcr.io -u raphaelrrcoelho --password-stdin

# Retry the pull:
docker compose -f docker/docker-compose.yml pull verify
```

---

## "unknown constant" after editing a single-file bind mount

**Symptom:** `lean-check.sh` or a benchmark run returns `unknown constant
'MathFin.SomeModule.someDecl'` — even though `lake build` succeeds and the
file looks correct.

**Cause:** Single-file bind mounts (`MathFin.lean`, `lakefile.lean`,
`lake-manifest.json`, `lean-toolchain`, `mathfin.toml`) pin the inode at
container start. Rename-based writes — Claude's Edit/Write tools, `sed -i`,
`mv` — replace the host inode, so a running container silently reads the old
content.

**Fix:** Re-sync the file into the running container:
```bash
docker exec -i docker-lean-repl-1 sh -c 'cat > /app/MathFin.lean' < MathFin.lean
# Or restart the service:
docker compose -f docker/docker-compose.yml restart lean-repl
```

Directory-mounted trees (`MathFin/`, `benchmarks/`, etc.) are not affected —
edits to files inside those directories are visible immediately.

---

## Container exits with code 137 (OOM kill)

**Symptom:** A `docker compose run` or the `lean-repl` service exits with
`exit code 137` and nothing in the logs after "Checking …".

**Cause:** Two Lean-loaded processes ran simultaneously, overcommitting
available RAM. The library is ~4–5 GB when loaded; two processes exceed the
WSL/host cap and the kernel OOM-kills the container.

**Fix:**
1. Check whether the `lean-repl` daemon is already running:
   ```bash
   docker compose -f docker/docker-compose.yml ps
   ```
2. If the daemon is up, **stop it** before running `lake build` or `verify`:
   ```bash
   docker compose -f docker/docker-compose.yml down lean-repl
   # Now run the build:
   docker compose -f docker/docker-compose.yml run --rm --entrypoint bash verify -lc 'lake build'
   ```
3. Never run `leanchecker`, a `verify` run, and the `lean-repl` daemon at the same time.

If you need parallel heavy work, use a remote machine via SSH tunnel:
```bash
ssh -L 7878:localhost:7878 <bigger-box>
# lean-check.sh / bench-check.sh speak to the remote daemon transparently.
```

---

## Daemon up but `lean-check.sh` is slow (falls back to cold path)

**Symptom:** `lean-check.sh` prints "daemon not reachable, falling back to
`lake env lean`" and takes 5–15 min instead of 5–30 s.

**Cause:** The daemon is not running, or its TCP port is not yet bound.

**Fix:**
```bash
# Start the daemon and wait for READY:
docker compose -f docker/docker-compose.yml up -d lean-repl
docker compose -f docker/docker-compose.yml logs -f lean-repl | grep -m1 READY
# Now re-run lean-check.sh — it will use the fast path.
```

The daemon takes ~5 min to start (Mathlib + BrownianMotion + MathFin olean
load). You pay that cost once per session.

---

## `lake build` and `lean-repl` slot contention

**Symptom:** Running `lake build` while the daemon is up causes one of them
to stall or OOM.

**Cause:** Both `lake build` and the daemon load the Mathlib environment
into memory. Two simultaneous loads overcommit RAM.

**Fix:** The `lean_interact_cache` Docker volume and the `lake_build_cache`
named volume are shared; never run a build in one service while the other is
up.

```bash
# Take down the daemon before a manual build:
docker compose -f docker/docker-compose.yml down lean-repl
docker compose -f docker/docker-compose.yml run --rm --entrypoint bash verify -lc 'lake build'
# Bring the daemon back up after:
docker compose -f docker/docker-compose.yml up -d lean-repl
```

---

## `lake build` succeeds but the daemon still reports errors for a file

**Symptom:** `lake build` exits clean, but `lean-check.sh` reports errors for
a file that imports a module you just changed.

**Cause:** The daemon does not write `.olean`s for downstream imports. Once a
proof works in the daemon, the oleans are not updated until `lake build` (or a
daemon restart) runs.

**Fix:** After editing a module that other files import, restart the daemon or
run a quick `lake build` to regenerate the oleans, then re-probe.

---

## Ledger shows stale entries after an edit

**Symptom:** `python3 -m tools.verify.ledger status` prints `STALE` for one
or more entries after you edited a `MathFin/` file or benchmark snippet.

**Cause:** The ledger hashes the snippet code + transitive imports + toolchain
pins; any change to those inputs marks the entry stale.

**Fix:**
```bash
# With the daemon running:
python3 -m tools.verify.ledger verify   # re-verifies only the stale entries

# Check afterwards:
python3 -m tools.verify.ledger status   # should show all FRESH
```

Do not push with stale ledger entries — the CI `ledger status` gate will fail.

---

## `ledger verify` times out on entry after entry (the timeout spiral)

**Symptom:** a corpus-scale `python3 -m tools.verify.ledger verify` starts failing on
timeouts and then keeps failing, with each entry reported at just over the cap.
Entries you know are cheap take as long as ones you know are hard.

**Cause:** `LEAN_ELAB_TIMEOUT` defaults to `180` (`docker/docker-compose.yml:137`),
which is fine for authoring a single file and too tight for a sweep. The failure
mode is a **spiral**, not an isolated timeout: a timeout kills the REPL, so the next
entry pays a ~120s reload out of its own budget and times out too, killing the REPL
again. Measured on 2026-08-07: entries reported at 182–201s under the 180s cap ran at
27–47s at `LEAN_ELAB_TIMEOUT=600`, and a warm entry in the same sweep ran at 31.7s.
The entries were never the problem; the cap interacting with the restart cost was.

**Fix:** raise the cap and restart the daemon before the sweep.
```bash
docker compose -f docker/docker-compose.yml down lean-repl
LEAN_ELAB_TIMEOUT=600 docker compose -f docker/docker-compose.yml up -d lean-repl
# wait for the daemon to answer a real lean-check (log-grep and port probes both lie),
# then:
python3 -m tools.verify.ledger verify
```

Once a sweep has spiralled, re-running it without raising the cap reproduces it. Stop
the sweep, fix the cap, and re-run rather than grinding through the remaining entries.

---

## The daemon stops answering after a long session (the memory wedge)

**Symptom:** `lean-check.sh` returns **nothing at all** and the request never completes.
The container is up, the log shows the request arriving, and no result line follows. An
agent driving the daemon looks like it has hung.

**Cause:** the daemon accumulates memory across many check/gate cycles and eventually
sits at its `mem_limit`. Measured on 2026-08-06 after ~15h uptime: `docker stats`
showed `5.861GiB / 6GiB` at 31% CPU, with a request logged at 02:30:01 and no result
ever emitted. This is not the two-Lean-processes hazard the memory doctrine warns
about; it is one long-lived process reaching the ceiling on its own.

**Diagnosis:** `docker stats --no-stream | grep lean` and compare against the compose
`mem_limit`. An **empty** `lean-check` response is the tell. An *error* means the daemon
answered; silence means it could not.

**Fix:** restart it. There is nothing to salvage.
```bash
docker compose -f docker/docker-compose.yml down lean-repl
LEAN_ELAB_TIMEOUT=600 docker compose -f docker/docker-compose.yml up -d lean-repl
```
Memory after a restart sat at ~939MiB, so the headroom is real once reclaimed. On a long
session, restart proactively rather than waiting for the wedge.

---

## An in-container step fails with "Read-only file system" writing to `docs/`

**Symptom:** something like
`sh: 1: cannot create /app/docs/blueprint_nodes.json: Read-only file system`, while the
same command's Lean work succeeded.

**Cause:** compose bind-mounts `tools/`, `benchmarks/`, `tests/`, `mathfin.toml` and the
Lake pieces. **`docs/` is not mounted.** Anything run inside the container that writes
there fails, even though reading the repo works.

**Fix:** capture the container's stdout on the host instead of redirecting inside it.
```bash
docker compose -f docker/docker-compose.yml run --rm -T --entrypoint sh verify \
  -c 'lake exe blueprint_export MathFin.Blueprint' > docs/blueprint_nodes.json
```
Validate the captured output before overwriting a tracked file — compose can print
container-lifecycle noise, so write to a scratch path first and check it parses.

Note `lake exe blueprint_export` loads the MathFin environment, so it is a Lean process
and needs the daemon **down** under the memory doctrine.

---

## CI fails on `test_values.py` after a benchmark edit

**Symptom:** `tests/test_values.py` fails with "stale AxiomAuditGen" or a
forbidden-text/rfl-backed-full violation.

**Fix:**
1. For stale audit: regenerate with `python3 -m tools.verify.axiom_audit_gen --write`.
2. For forbidden text (`sorry`/`admit`/`native_decide`/`polyrith`/`?`-tactics/
   `hammer`/`loogle`/`leansearch` in `MathFin/` source): remove the tactic.
   Comments are exempt.
3. For `rfl`-backed `full`: the proof must do real work — a definition +
   single `rfl` is `reduced_core`, not `full`.
