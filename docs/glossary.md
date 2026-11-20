# Glossary

The words the library, its documentation and its site use in a sense of their own. Mathematical
terms keep their usual meaning and are not listed.

## The corpus

### corpus
The benchmark of results from the literature in [`benchmarks/`](../benchmarks), one JSON file per
area. Each **entry** restates one result as a short Lean snippet and proves it by citing the
library. The corpus is published as a
[Hugging Face dataset](https://huggingface.co/datasets/formal-applied-math/formal-mathfin-theorems);
`python3 -m tools.verify.coverage_report` prints its current size and split.

### entry
One result of the corpus: an `id`, a `name`, a `domain`, the Lean `code`, a `description` and
`metadata` (source, status, scope).

### status
How faithful an entry's statement is to the result it is named after, recorded as
`metadata.formalization_status`:

- **full**: the statement is the result itself, at the generality of its source or more;
- **library_wrapper**: the entry restates a theorem of Mathlib or BrownianMotion;
- **reduced_core**: the entry proves less than the result it is named after, and its description
  says what it leaves out.

Only `full` and `library_wrapper` entries may be cited as the named theorem.

### description and formalization_scope
An entry's `description` says what its Lean statement proves, not what the textbook theorem says;
`metadata.formalization_scope` says in detail what the statement covers and what it leaves out.
Both are published with the dataset.

## The map

### blueprint
The map of the program: the results the library proves, the results it intends to prove, and the
dependencies between them. The proved nodes are tagged in
[`MathFin/Blueprint.lean`](../MathFin/Blueprint.lean) and their dependencies are read off the proof
terms; the page is [`blueprint.md`](blueprint.md) and the site's
[blueprint](https://formal-applied-math.github.io/formal-mathfin/blueprint.html).

### node
A result or definition on the blueprint, with a label such as `thm:ito-formula-c2` or
`def:emm`. A node is a landmark, a joint, a market statement or a shared definition, never a step
inside a proof.

### landmark
A result with a textbook name, proved at the generality the library reaches, which may be less
than the textbook's: Itô's formula, Girsanov's theorem (for bounded predictable θ), the
fundamental theorems of asset pricing. The headline landmarks, with their
exact statements and scope, are on the site's
[landmarks page](https://formal-applied-math.github.io/formal-mathfin/landmarks.html) and in
[`landmarks.toml`](landmarks.toml).

### spine
The proved part of the blueprint.

### frontier
The results the library states and does not yet prove, listed in
[`blueprint_frontier.toml`](blueprint_frontier.toml). Each frontier node is carried by an open
issue whose body names it (`Blueprint: <label>`), and builds on proved nodes through its `uses`.
When the result is proved, the declaration is tagged with the same label and the entry is deleted.

### ground
A frontier node's `ground` field names the Mathlib material it would build on when no proved node
of the library leads to it.

### core
A frontier node's `core` field lists corpus entries that already prove part of it.

### frontier connector
A frontier result written as a Lean statement, closed by `sorry`, in
[`MathFinFrontier/`](../MathFinFrontier). This library is not imported by `MathFin` and is not
part of its verified claims; a frontier node points to its connector by its `lean` field.

### retired label
A label that was once a node and was folded into another, recorded in
[`blueprint_retired.toml`](blueprint_retired.toml) so that closed issues naming it stay valid.

### island
A group of proved nodes that no recorded dependency ties to the part of the blueprint that holds
Brownian motion. The library keeps their number at zero: an island is joined by a shared object
or a theorem that uses both sides.

### open problem
A problem of the field, outside what the library intends to prove as a matter of course, recorded
with a stable id `MF-OP-NNN` in [`research-problems/`](research-problems/README.md).

## The organization

[`organization.md`](organization.md) gives the account these terms come from.

### trunk
Positions, markets and pricing measures: the payoff language (`Contract`), the market (`Market`),
pricing measures (`Market.IsPricingMeasure`), prices, and the fundamental theorems that relate
them.

### limb
One of the three questions asked of a position: **valuation** (what is it worth), **risk** (how
dangerous is it), **choice** (whether to hold it).

### root
The tools the trunk and limbs are built from: probability and statistics.

### cell
A place in the organization: a root, the trunk, a limb, or a branch inside one (for example
`valuation/term`, `risk/measures`). Every module belongs to exactly one cell, assigned in
[`taxonomy.toml`](taxonomy.toml). An issue's `area:` label names a cell.

### model family
A kind of randomness: trees, Gaussian diffusions, volatility, jumps, term structures, default,
mortality and claims, market mechanisms, model-free. A family is a second axis across the limbs;
an issue's `family:` label names one.

### joint
A theorem whose statement involves two limbs, such as marginal utility at an optimum being a
state-price density (choice and valuation). The site calls these bridges between limbs.

### market statement
A theorem stating that a measure prices a model family as a `Market`. A family with such a
theorem is **priced in a market**; the site's markets page lists them.

### socket
A model family's socket is its theorem stating that a measure prices it as a market (a market
statement). A cluster that stands apart from the trunk on purpose (a law functional, an algebraic
certificate, a convex programme) is declared in `taxonomy.toml` with the market-side result that
reads it as its socket.

### program tree
The site's [drawing](https://formal-applied-math.github.io/formal-mathfin/tree.html) of the whole
library: roots, trunk and limbs, with each result placed at its distance from the trunk, measured
from what its statement mentions.

### layer
A directory level of the source tree. Imports point one way: `Probability/` → `Contracts/` →
`Pricing/` → the limbs `Models/`, `Risk/`, `Choice/`, `Insurance/`, `Markets/`
([`architecture.md`](architecture.md)).

### methods
The four techniques the joints and families are proved with: convex duality, Itô calculus, the
generator and its PDE, intensities and exponential families
([`mathematical-architecture.md`](mathematical-architecture.md)).

## Checking

### axiom pin
A `#print axioms` output fixed in [`MathFin/AxiomAudit.lean`](../MathFin/AxiomAudit.lean) or the
generated [`MathFin/AxiomAuditGen.lean`](../MathFin/AxiomAuditGen.lean). The build fails if a
pinned theorem comes to depend on anything beyond `propext`, `Classical.choice` and `Quot.sound`.

### ledger
[`verification_ledger.json`](../verification_ledger.json): for each entry, a hash of the inputs it
was last checked under (its snippet, the modules it imports, the toolchain pins). CI fails when
the inputs change without a re-check.

### declaration index
A JSON record of every declaration of the library, with its statement, docstring and uses, built
by `lake exe mathfin_index` on every build of `main`. `python3 -m tools.verify.find` searches it.

### ratchet
A count of a kind of debt (whole-Mathlib imports, long files, unconnected results, …) recorded in
[`ratchet.json`](../ratchet.json). The build fails when a count rises; a baseline is only ever
lowered.

### values review
The judgment review that closes a session adding proof content, recorded in
[`values-review.md`](values-review.md): eight lenses, each read as the next upgrade it asks for.
