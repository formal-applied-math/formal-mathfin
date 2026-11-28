# When the prose says more than the Lean

Lean checks that a proof proves its statement. It does not check that the statement is the
theorem the prose names. In this library that second gap is the one that has actually opened,
again and again, and never on purpose: the author describes the theorem they had in mind, the
statement says less, and the build stays green *because* the statement is weaker. This page
records how often it happened, what kinds of gap occurred, and what now catches them.

## The record

The library's git history since May 2026 contains 336 commits in which a corpus entry's prose
(its `description`) changed while its Lean did not. Those are the candidates. Each candidate was
read against the Lean statement it describes, by a triage pass and an independent audit pass;
where they disagreed, further audits decided by majority. **107 of them are confirmed cases in
which the earlier prose claimed more than the statement proves**, on 100 distinct entries, each
paired with the corrected prose. The remaining candidates were rewordings of prose that was
already faithful.

| Kind of gap | Pairs | What it looks like |
|---|---:|---|
| stronger conclusion | 44 | the prose states a conclusion the statement does not contain |
| textbook overreach | 25 | the prose names the textbook theorem; the statement proves a piece of it, or reads it off a hypothesis |
| wrong object | 14 | the prose describes a different quantity from the one the statement is about |
| hidden hypothesis | 14 | the statement carries an assumption the prose does not mention |
| more general scope | 10 | the prose claims a general case; the statement proves a special one |

The 107 pairs are mined from the history of a public repository, so each one can be checked
against its commit.

## Five examples

**Stronger conclusion.** Newton–Raphson (`mf-newton-raphson-fixed-at-root`): the prose said the
error halves at every step, giving geometric decay. The statement proves the one-step quadratic
bound and convergence `newtonSeq → r`; the geometric bound is proved in the module but is not
part of the entry's statement. Fixed in
[4397e2aa](https://github.com/formal-applied-math/formal-mathfin/commit/4397e2aa).

**More general scope.** Quadratic variation of an Itô process (`sc-thm-7.4.5`): the prose said
⟨X⟩ₜ = ∫₀ᵗ σ(s)² ds for an Itô process. The statement is the constant-σ case, X = X₀ + A + σB
with a Lipschitz drift A, and proves that the squared-increment sums converge in L² to σ²t.
Fixed in [9966f6c0](https://github.com/formal-applied-math/formal-mathfin/commit/9966f6c0).

**Textbook overreach.** The recurrence criterion for Markov chains (`mc-thm-1.3.12`): the prose
said a state is recurrent if and only if Σ Pⁿ(i,i) = ∞. The statement takes a structure whose
recurrence predicate and return probabilities are not defined from the transition matrix, and
whose field is the criterion itself; the theorem reads the field off. The entry is now a
`reduced_core` and says so. Fixed in
[4397e2aa](https://github.com/formal-applied-math/formal-mathfin/commit/4397e2aa).

**Wrong object.** The Kelly fraction (`mf-kelly-fraction-pos-iff`): the prose said f\* > 0
exactly when the bet has positive expected log-growth. The statement is `0 < kellyFraction p b ↔
1 < p * (b + 1)`, which is positive *edge*, p·b − (1 − p) > 0, a different quantity. Fixed in
[4397e2aa](https://github.com/formal-applied-math/formal-mathfin/commit/4397e2aa).

**Hidden hypothesis.** The Vasicek bond price (`mf-vasicek-bond-price`): the prose explained
that the integrated short rate is Gaussian because the rate solves the Vasicek SDE. The
statement carries the short rate in its Wiener-integral representation; that it solves the SDE,
and the exchange of time integrals behind the integrated rate, are not proved in the entry. Fixed
in [6e142599](https://github.com/formal-applied-math/formal-mathfin/commit/6e142599).

The largest single sweep, on 2026-08-07
([#190](https://github.com/formal-applied-math/formal-mathfin/pull/190),
[#191](https://github.com/formal-applied-math/formal-mathfin/pull/191)), found five entries
whose prose wrote the Itô integral ∫₀ᵀ f_x(s, B_s) dB_s where the statement said only `∃ gfx`,
that *some* process with the stated properties exists, and the README rendering
`ito_formula_unrestricted` as an integral identity where the theorem proves that a residual is a
continuous local martingale.

## Do models catch it?

A pilot run gave Claude Sonnet 5.5 each Lean statement with one version of its prose, and asked
whether the prose is faithful. Of the 107 unfaithful versions it flagged 60 and called 47
faithful; of the 107 faithful versions it called 104 faithful. A model reviewer that rarely
raises a false alarm and passes almost half of the real gaps is the failure that matters here:
the gap is silent in the build, and silent in the review. This is one model on one pilot; the
items and the harness are the faithfulness task (T2) of the benchmark built on this library.

## What catches it now

None of the gates below decides faithfulness; they narrow where a gap can hide.

- Every entry declares a status: `full`, `library_wrapper`, `reduced_core` or `placeholder`.
  A reduced core proves less than the theorem it is named after, and its description says so in
  the same field (`tests/test_values.py::test_reduced_core_description_discloses_scope`).
- `tests/test_values.py::test_prose_does_not_outrun_statement` checks the mechanical slice of the
  2026-08-07 failure: an `∃`-statement whose prose writes the stochastic integral that would pin
  the witness down.
- A `full` entry whose proof is a definitional `rfl` fails the values gate: that is a reduced core
  in disguise.
- Each entry publishes, beside its `description`, a `metadata.formalization_scope` saying what it
  leaves out. Both ship in the Hugging Face dataset.
- The README's [summary of known gaps](../README.md#how-it-is-kept-honest) and the scope line of every card on the
  [landmarks page](https://formal-applied-math.github.io/formal-mathfin/landmarks.html) say what
  each headline theorem does not prove.
- The last step of every working session is to read the touched prose against its statement
  ([CLAUDE.md](../CLAUDE.md)); the values review ([values-review.md](values-review.md)) repeats it
  as its standing first pass.
- For open problems, the cátedra ([design](specs/2026-11-20-catedra-design.md)) spends its
  review on faithfulness and leaves correctness to the kernel: a Referee reads each Lean
  statement against its source before a result is recorded.
