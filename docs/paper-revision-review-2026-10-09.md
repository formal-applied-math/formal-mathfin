# What the October 2026 paper revision showed about the repo

In October 2026 the three arXiv papers that describe this library (the fundamental theorem of
asset pricing, the Itô calculus, and the library overview) were rewritten against release
`v1.5.0` (`main` at `c0180c8`). Every claim was read against its Lean statement, and the
area tables were audited claim by claim. This file records what that exercise found about the
repository itself, as a backlog of improvements. Most items are prose that said more than the
Lean, or Lean that says less than it easily could, so that the papers had to narrow their
wording.

Each item gives where it lives, what is wrong or missing, and a suggested route. Items within a
section are ordered by value for cost. Section 1 lists what was fixed alongside this file;
everything after it is open.

## 1. Fixed alongside this file

- **Garman normal form instances.** The table in `MathFin/BlackScholes/GarmanNormalForm.lean`
  and the docstring in `MathFin/BlackScholes/ExchangeOption.lean` presented Garman–Kohlhagen,
  KMV–Merton and the quanto call as instances of `bsVGarman` with no theorem saying so. The
  table now names the instance theorem for each row: Garman–Kohlhagen and the KMV–Merton
  equity value are instances through the BS–Merton and standard rows, and the quanto call is
  marked as having the same shape only.
- **Survival "unification".** `MathFin/Bridges/SurvivalUnification.lean` described an `rfl`
  identity as one between independently developed modules. It now says that the shared
  definition `survivalFromIntensity` records the unification.
- **"Esscher" on the d-asset FTAP.** The equivalent martingale measure of
  `ftap_one_period_vector` is the logistic, softplus-potential measure: the softplus analogue
  of the Esscher measure, not the Esscher or minimal-entropy measure. Fixed in the
  `mf-ftap-one-period-vector` name and reference, the `MathFin.lean` comment,
  `MathFin/AxiomAudit.lean` (which also wrongly said "non-redundant"),
  `MathFin/Foundations/EquivMeasure.lean`, and two `docs/coverage.md` passages.
- **`sc-ito-formula-td-process`.** The description wrote the stochastic term as
  `(f_x(·,B) ● B)_t`, but `ito_formula_td_process` only asserts `∃ F`. It now says that `F` is
  existentially quantified. The `gate-gap` item in section 4 is why the gate missed it.
- **`sde-picard-existence-uniqueness`.** The scope note said the solution was "not yet realized
  as a pointwise ℝ-time process" and that `sc-thm-8.2.5` "remains reduced_core". Both are out
  of date (`sde_pathwise_decomposition`, `driftContinuousMod_eq_setIntegral`; `sc-thm-8.2.5`
  is `full` for uniqueness).
- **A deleted theorem name in benchmark prose.** `ito_formula_td_L2_bddDeriv_explicit` no
  longer exists; the naming conjunct now lives in `ito_formula_td_L2_bddDeriv`.
- **`docs/upstreaming.md`** did not record the second merged BrownianMotion contribution.

The prose fixes in `MathFin/` change file bytes. The verification ledger hashes raw bytes, so
23 entries restaled and had to be re-verified on runners by the ledger-sweep workflow, although
no statement or proof changed. See the `ledger-bytes` item in section 4.

## 2. Small prose and metadata fixes still open

1. **Issue #39 was closed in error.** "Superhedging strong duality" was closed as completed on
   2026-08-07 through PR #188. That PR proved the continuous-time superreplication duality
   (`superReplication_eq_emm_price`), which by its own module docstring
   (`MathFin/Foundations/MarketCompleteness.lean`) does not close the finite-state gap. In the
   finite-state model only weak duality exists (`emm_le_superReplication`), so the issue should
   be reopened. Its blocker is stated precisely in `MathFin/Foundations/SuperhedgingDuality.lean`:
   closedness of a finitely generated cone, absent at the pin (see section 3).
2. **Theorem names in benchmark prose that resolve to nothing in `MathFin/` or BrownianMotion:**
   - `cml_decomposition_unique` (`mf-cml-mean-at-stdev`)
   - `processToLp_of_bdd_adapted_cont` (`sc-thm-9.1.8`)
   - `square_minus_time_is_martingale` (`bm-rmk-5.1.6-square`)

   Find the current names. The same scan also flags six Mathlib names
   (`ext_of_complexMGF_eq`, …), which need checking against the Mathlib pin.
3. **Quanto parameter naming.** In `quantoForward_of_gaussian`
   (`MathFin/BlackScholes/QuantoGrounding.lean`) the asset's drift under the foreign measure is
   named `r_dom`. The textbook quanto forward uses the foreign rate there. Rename it, or say
   which model is meant.
4. **`formalization.yaml`** says `wall_time: continuous over 2026-05 to 2026-08`, but work
   continued into October.
5. **History that agents read as current.** Dated entries in `docs/coverage.md` and
   `docs/roadmap.md` keep mathematical descriptions that later turned out wrong (two Esscher
   passages were corrected here). Choose a policy and apply it: annotate corrections in place,
   or keep a "superseded descriptions" list at the top.

## 3. Statements to strengthen, so the prose can say more

These are short Lean changes that would remove a narrowing from the papers.

1. **Name the integrand of the keystone `∫B dB`.** `itoIntegralCLM_T_brownian` asserts
   `∃ gB, ito_T gB = ½(B_T² − B_0² − T)` without saying `gB = B`. The named form is
   `ito_formula_td_localized` at `f(t,x) = x²/2` (`f_x = x`, `f_xx = 1`). State it, for example
   as `itoIntegralCLM_T_brownian_named` with `⇑gB =ᵐ fun z ↦ B z.1 z.2`.
2. **Name `F` in `ito_formula_td_process`.** The proof already builds
   `F = 1_(0,T] · [f_x(·,B)]`; add the conjunct, then restore the description's
   `(f_x(·,B) ● B)_t`.
3. **Price the physical model with its drift.** `bs_call_formula_of_physical` holds for every
   tilt `c` and never mentions the physical drift `μ`. Only the discounted asset is composed
   with `bsTerminal_physical_eq_riskNeutral` (`discounted_physical_terminal_eq_S0`). Compose
   the call too, so the formula reads as a statement about
   `S_0·exp((μ − σ²/2)T + σ√T·W)` under `P`.
4. **Margrabe by change of numéraire, for real.** `exchangeOption_numeraire_price` is the
   payoff identity under `numeraireMeasure`. `margrabe_price_via_call` assumes the price ratio
   is lognormal under an abstract `Q`, and `margrabe_price_of_gaussian` only asserts that some
   `Q` and `Z` exist. Prove that the ratio of two correlated geometric Brownian motions is
   lognormal under the second-asset numéraire measure; then the closed form follows by change
   of numéraire, and the grounding names its drivers.
5. **One-line Garman instances.** Garman–Kohlhagen is `bs_dividends_RHS_eq_bsVGarman` at
   `q = r_f`, and the KMV equity value is `bsV_eq_bsVGarman_standard` at
   `(V, F, σ_V)`. State both, and the table needs no "through" column. The quanto call needs
   its price first.
6. **One survival calculus.** Constant-hazard `survivalProbability`
   (`MathFin/FixedIncome/Credit.lean`) and actuarial `survivalFunction`
   (`MathFin/Actuarial/SurvivalModel.lean`) are separate from `survivalFromIntensity`. Make the
   first an instance (constant intensity) and relate the second to `survivalFromForce` where a
   force of mortality exists.
7. **The contract layer.** Value reduction to closed forms is proved for four contracts (call,
   put, digital, capped call) in single-asset Black–Scholes. Extend it to the exchange option,
   the geometric Asian call and the other closed forms the pricing layer proves.
8. **The finite FTAP.**
   - `ftap_discrete` covers one risky asset; add the d-asset multi-period finite theorem. The
     one-period d-asset case is already `hasEMM_multi_iff_not_hasArbitrage`.
   - Prove the converse of coercivity (coercive potential implies no arbitrage), which the FTAP
     paper records as unformalized.
9. **Superhedging strong duality** (issue #39). Prove that a finitely generated cone in
   `Fin n → ℝ` is closed; it is a good Mathlib contribution. Strong duality then follows from
   `exists_separating_of_not_mem_cone`.

## 4. The apparatus

Gaps in the gates themselves, each found by something no gate caught.

1. **Non-vacuity gate.** The CRR convergence theorems once carried a hypothesis that held for
   no market (`∀ n` including `n = 0`). Every gate passed them; reading the statement found
   it. The Comparator pair already shows the fix for one theorem: `Challenge.lean` pairs the
   coherent-risk representation with a witness that its hypothesis is satisfiable. Generalize
   it: every headline theorem whose hypotheses include a structure or a `∀`-family gets a
   satisfiability witness lemma, and a test checks that the pair exists.
2. **Name-resolution gate.** Prose cited a theorem that had been deleted (section 1), and three
   more such names are open (section 2). Add a test that resolves every identifier-shaped token
   in benchmark text and module docstrings against the declarations of `MathFin/`, the pinned
   BrownianMotion and a Mathlib name index at the pin.
3. **gate-gap: `test_prose_does_not_outrun_statement` missed a named witness.**
   `sc-ito-formula-td-process` wrote `(f_x(·,B) ● B)_t` over an `∃ F` statement, and the gate
   only knows the `∫₀ᵀ f_x … dB` spelling. Teach it the `●` notation and the bare
   `f_x(·,B)` integrand.
4. **Instance claims.** "X is an instance of Y" in a docstring should point to a theorem. A
   targeted check is cheap where the claims are tabular (the Garman table): each row's last
   column must name an existing declaration.
5. **ledger-bytes: comment-only edits restale entries.** The ledger hashes raw module bytes, so
   correcting a docstring re-verifies every entry downstream (23 here). Hashing a normal form
   with comments and docstrings stripped would make prose fixes free. Caveat: `#guard_msgs`
   reads its expected output from a doc comment, so files that use it must keep their doc
   comments in the hash. Snippets do not import `AxiomAudit*.lean`, which keeps this simple.
6. **Comparator is not in CI.** `Challenge.lean` and `Solution.lean` build with every
   `lake build`, but the Comparator comparison that defines the Mathlib-only check does not
   rerun. Add a job, or a scheduled run at the pin.
7. **Kernel replay never completes.** `kernel-replay.yml` runs out of memory on a 16 GB hosted
   runner. Either shard by module closure or use a larger runner. Until then the papers have
   to say that it has never completed.
8. **Unpinned theorems.** Library theorems that no benchmark cites and the curated audit omits
   are not axiom-pinned. Consider generating pins for every public `theorem` in `MathFin/`.
9. **Provenance is not published.** The Hugging Face export carries `description` and
   `formalization_scope` but not `metadata.provenance`, so ports and machine-drafted entries
   are invisible to dataset users.

## 5. Mathematics the papers had to narrow around

Larger items, each a stated limitation in at least one paper.

- **Itô calculus.**
  - The unrestricted C² formula for `f(t,B_t)`.
  - Itô's formula for Itô processes beyond bounded coefficients, bounded `f'`, `f''` and a
    fixed time: time-dependent `f`, `eˣ`, `x²`, random initial values, SDE coefficients.
  - The multi-dimensional formula, Lévy's characterisation, Novikov and the general Girsanov
    theorem (all reduced cores).
  - Pathwise quadratic variation; the localized integrand class `∫₀ᵀφ² < ∞` a.s.;
    Clark–Ocone.
  - Girsanov's theorem states finite-dimensional laws only: path continuity and independence
    from the past are not stated.
- **SDEs.**
  - Existence on arbitrary horizons, which needs a weighted (Bielecki) norm.
  - Uniqueness against the concrete Itô integral rather than an abstract isometric operator.
  - The Vasicek integrated rate derived from the SDE solution rather than defined through its
    Wiener representation.
- **Martingale convergence.** Right-continuous `L^p`-bounded martingales converge almost
  surely along the integers and in measure along the reals. The real-time almost-sure and
  `L^p` limits are missing.
- **Pricing.**
  - Breeden–Litzenberger in second-order form for general laws with a density. It is proved
    for Black–Scholes and for jump-diffusions with a Gaussian part.
  - A forward measure for stochastic rates; today `Q^T = Q`, in a constant-rate model.
  - CDS legs valued from a hazard curve, instead of an assumed leg balance.
  - A jump-diffusion actually constructed, so that `JumpDiffusionProcess` is inhabited with
    jumps.
- **Portfolio and risk.**
  - The Bayesian derivation of the Black–Litterman posterior (Gaussian conjugacy); the library
    defines it by its normal equation.
  - The full Basel IRB capital formula (loss given default, expected-loss subtraction, maturity
    adjustment) on top of the asymptotic single-risk-factor quantile.
  - The multi-asset Bergault–Evangelista–Guéant–Vieira coefficients and value-function
    verification.
  - Life annuities weighted by survival.
- **No-arbitrage.** The Dalang–Morton–Willinger theorem in general, and the
  continuous-time converse (no free lunch with vanishing risk).
- **Reduced cores** (13): the reflection principle, nowhere differentiability and the law of
  the iterated logarithm; Novikov, the general Girsanov theorem, Lévy's characterisation and
  the two-dimensional Itô formula; five Markov-chain theorems; and the Poisson interarrival
  law, proved as a special case.

## 6. Upstream

Staged and not submitted, per `docs/upstreaming.md`:
- the square and Wald exponential martingales of Brownian motion
  (`upstream/brownian-motion/Martingale.lean`);
- the Gaussian tail and completing-the-square lemmas (`upstream/mathlib/RealTail.lean`).

Also candidates for Mathlib: Doob's `L^p` maximal inequality (`maximal_ineq_Lp`), and the
closedness of finitely generated cones from section 3, item 9.
