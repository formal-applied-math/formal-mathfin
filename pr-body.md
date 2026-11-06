## Summary

Adds `MathFin/Binomial/WillowTree.lean` and one `full` benchmark entry formalizing the
mathematical core of Curran's willow tree lattice: the de-correlation identity and the
moment/marginal preservation induction showing that *any* family of transition matrices
satisfying the construction's row constraints keeps the chain's marginals on the Brownian
moments.

## The construction and what is proved

The willow tree prices against a Brownian motion with a discrete-time Markov chain on a
**fixed** node set carrying a **fixed** discrete marginal `q` — a constant node count per
time step, the lattice widening like `√t` only through the scaling `X_k = √(t_k) Z_k`.
Recombination is replaced by a time-inhomogeneous family of transition matrices `P_k`
whose rows are chosen (in the original construction, by linear programming) to satisfy:

- row stochasticity `∑_j P_k(i,j) = 1`;
- conditional first moment `∑_j P_k(i,j) z_j = β_k z_i`;
- conditional second moment `∑_j P_k(i,j) z_j² = β_k² z_i² + (1 − β_k²)`;
- the marginal constraint `∑_i q_i P_k(i,j) = q_j`,

with `β_k = √(t_k / t_{k+1})`. The module proves:

1. **The β identity** — for `t′ = (1+α)t`, `1/√(1+α) = √(t/t′)`, the correlation of a
   Brownian motion at the two grid times (`willowBeta_eq_sqrt_div`, and its grid
   instantiation `willowBeta_eq_sqrt_div′`).
2. **Moment propagation** — any row-stochastic family satisfying the two moment rows
   keeps a chain started at a marginal of mass 1, mean 0 and unit second moment at mass
   1, mean 0 and unit second moment at every step: an induction needing neither the
   marginal constraint nor non-negative entries (`willowMarginal_mass`,
   `willowMarginal_mean`, `willowMarginal_secondMoment`).
3. **Marginal preservation** — under `qP = q`, the marginal at every step is the same
   discrete law `q` (`willowMarginal_eq`).
4. **Cross moments** — `E[Z_k Z_{k+1}] = β_k`; in the unstandardized variables the second
   moment is `t_k` and `E[X_k X_{k+1}] = t_k`, the Brownian covariance across
   `[t_k, t_{k+1}]` that the constraint system encodes (`willowMarginal_crossMoment`,
   `willowScaled_secondMoment`, `willowScaled_crossMoment`).
5. **Feasibility** — an honest (non-negative, summing-to-one) transition row forces
   `β_k² ≤ 1` by Cauchy–Schwarz on the row, which instantiates the standard bivariate
   normal law at the willow coefficient with unit variances and covariance `β_k`
   (`willowBeta_sq_le_one`, `willowBeta_bivariateNormal_moments`).

## Scope

The linear program that produces admissible transition matrices (feasibility of the full
system, the objective, entry non-negativity) is out of scope; every statement is
unconditional in `P`, which is what makes them usable against any solver output. Nothing
is claimed about prices computed on the lattice.

## Corpus

- `benchmarks/binomial.json`: `mf-willow-tree-moment-marginal-constraints` (`full`);
  corpus 781 → 782 (782 theorems, 765 delivery-ready); counts, README and the
  machine-generated axiom audit regenerated; verification ledger re-verified at the new
  pin.
- `docs/references.bib`: Curran 2001 and Ho 2000 added.

## Primary sources

- M. Curran, *Willow Power: Optimizing Derivative Pricing Trees*, ALGO Research
  Quarterly 4(4) (December 2001).
- A. C. T. Ho, *Willow Tree*, MSc thesis in Mathematics, University of British Columbia
  (2000) — the constraint system as stated.
- The constraint set as implemented in the open-source `willowtree` package
  (`willowtree/lp.py`).

All new declarations are axioms-clean (`propext`, `Classical.choice`, `Quot.sound`).

🤖 Generated with [Claude Code](https://claude.com/claude-code)
