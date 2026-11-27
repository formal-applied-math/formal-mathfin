# External sources

The one place for external credit: the formalisations, packages and texts this library depends on
or has learned from. For each, what was taken, how (a dependency, a port, a design idea, an
alignment of the corpus) and where it lives in the library.

**The rule.** An external formalisation is a source, not a template. Where the library designs in
its own idiom it cites by name and takes no code. Where it ports code, the module header names the
original author and the licence is kept (see Martin below).

## Mathlib and BrownianMotion

The library is built on Mathlib and on BrownianMotion, the formalization of Brownian motion and
stochastic integration led by Rémy Degenne. Both are dependencies, pinned in `lake-manifest.json`,
not ported code. Mathlib supplies measure theory, conditional expectation, martingales and convex
analysis; BrownianMotion supplies the Brownian motion, filtrations and the stochastic-integration
infrastructure that `MathFin/Probability/Brownian/` extends. Where a statement is already in
either, the library uses it rather than restating it.

## Saporito, *Stochastic Processes*

Yuri F. Saporito, *Stochastic Processes*. The stochastic-processes part of the benchmark
(for example `martingales.json`, `continuous_martingales.json`, `brownian_motion.json` and
`stochastic_calculus.json`) follows its chapters; each entry's `reference` names the source. This is an alignment of statements to a textbook, not a port; the proofs are in
`MathFin/Probability/`.

## Martin, AmericanPutConvexity and ButterflyFreeSVI

Robert Martin's [AmericanPutConvexity](https://github.com/robertmartin8/AmericanPutConvexity)
(Apache-2.0) and the manuscript *Log-convexity of the exercise boundary of an American put option*
are ported into `MathFin/Models/BlackScholes/American/`, with the module headers naming him as
author. The result, its statements and its provenance are on
[`american-put-boundary.md`](american-put-boundary.md).

His [ButterflyFreeSVI](https://github.com/robertmartin8/ButterflyFreeSVI) is ported into
`MathFin/Models/ModelFree/SVI/`: the polynomial-sign certificate that characterises when the
Black–Scholes call with a raw SVI volatility is convex in the strike. The modules carry his name
and the landmark `MathFin.SVI.extendedCertificateFormula_iff_bsSmile_convex` records its scope.

**Licence.** The upstream ButterflyFreeSVI repository carries no licence file. The grant is
Robert Martin's reply on [#174](https://github.com/formal-applied-math/formal-mathfin/issues/174),
in answer to the maintainer's offer to port the certificate under this repository's Apache-2.0
licence: "Apache-2.0 is fine with me." The port is therefore Apache-2.0, and the headers keep his
copyright. A LICENSE file upstream would make the grant self-standing, but the library does not
wait on one.

## Bilokon, *The Contract Is Not the Model* (2026)

Paul Bilokon, *The Contract Is Not the Model: Proof-Carrying Exotic Derivatives
and the Economics of Model Risk*, working paper, 9 August 2026. Mathematical
Finance, Department of Mathematics, Imperial College London.
Code: <https://github.com/thalesians/lean_contracts>, Apache-2.0.

**Taken** (as ideas, credited in every `MathFin/Contracts/*.lean` docstring): the
"contract is not the model" thesis; the five-layer decomposition; contract-semantic
risk as a named category; unmodelled clauses as first-class data; the
lifecycle-as-state-machine design — not yet built, and when it is, it is built as
his design.

**Not taken:** no code. Our type design (typed underlying index, `ℝ≥0` time, a
single inductive), the measurability and adaptedness theorems, and the reduction
of reified instruments to our existing Black–Scholes closed forms have no
counterpart in the source.

**Onward credit:** that paper builds on Peyton Jones, Eber and Seward (2000);
Bahr, Berthold and Elsman (2015); Annenkov (2018); and Arusoaie et al. (Findel).
Cite the tradition, not only the nearest author.

**In the code:** the `## Source` blocks in `MathFin/Contracts/*.lean` (gated by
`tests/test_values.py::test_contracts_cite_source`); `metadata.reference` on every
`mf-contract-*` corpus entry (gated by
`test_contracts_corpus_entries_cite_source`);
`docs/specs/2026-08-16-contracts-tower-design.md` section 6.

## Ito, AFP `Actuarial Mathematics`

Yosuke Ito's entry in the Archive of Formal Proofs, in particular its `Survival_Model` theory, is
the source for the classical result set of the actuarial survival layer. It is not a port: the
design and the Lean are the library's, and `MathFin/Insurance/SurvivalModel.lean` lines its
declarations up with the AFP names for readers coming from Isabelle. See the module docstrings in
`MathFin/Insurance/`.
