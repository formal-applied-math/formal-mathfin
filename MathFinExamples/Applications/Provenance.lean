/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin

/-!
# Using the library: where an example's numbers come from

Every worked example records its inputs as data, together with where they come from and what the
example leaves out. `Provenance` is that shared record: each example's sheet extends it, so the
`sources` and `unmodelled` fields read the same in every file.

## Main definitions

* `MathFin.Examples.Provenance`: the sources of an example's inputs and the features it does not
  model.

## Source

The shape of the file follows the capped-call example
(`MathFinExamples/Applications/CappedCall.lean`), whose sheet first carried the `unmodelled` list.
-/

@[expose] public section

namespace MathFin.Examples

/-- Where an example's inputs come from, and what it does not model. The sources are plain strings
for most sheets, and structured clauses for a term sheet (`Source`). The `unmodelled` list is part
of the record, not a disclaimer. -/
structure Provenance (Source : Type) where
  /-- Where the numbers come from. -/
  sources : List Source
  /-- What the example does not model. -/
  unmodelled : List String

end MathFin.Examples
