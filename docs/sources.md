# External sources

Formalisations and papers this library has learned from. For each: what was
taken, what was not, and where the credit lives in the code.

**The rule.** An external formalisation is a *source*, not a template. We design
in our own idiom and cite by name. We do not copy code; if we ever do, the copied
region is marked in-file, its licence header is retained, and a `NOTICE` entry is
added.

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

## AFP `Survival_Model`

Consulted for the actuarial survival layer (2026-07-11). Our design, our Lean; the
AFP entry was a source for the mathematical content, not a port. See the
`MathFin/Actuarial/` module docstrings.
