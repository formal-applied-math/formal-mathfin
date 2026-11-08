/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
-- NOT a `module`-header file: exe tooling that loads the built library at run time, like
-- `MathFinTools/Blueprint.lean`. It imports no MathFin module at compile time, so building it
-- compiles only core Lean and Batteries.
import Lean
import Batteries.Tactic.Lint.Basic

/-!
# `mathfin_index` — the environment's account of every MathFin declaration

Loads the environment of the umbrella `MathFin` and writes one JSON record per declaration made
in a `MathFin.*` module (auto-generated and internal declarations excluded): its kind, module and
line, privacy, docstring, statement (pretty-printed, and the hash of its `Expr`, which does not
depend on binder names), the library declarations it uses, whether its statement mentions any
MathFin constant, and its core attributes (`simp`, `instance`).

`tools/verify/decl_index.py` reads the file; `find`, `decl_diff` and the ratchet's index metrics
are built on it (`docs/specs/2026-11-05-library-practices-design.md` §2).

Uses look through the compiler's auxiliary constants (`foo._proof_1`, `foo.match_1`, …): an edge
`a → b` means `b` occurs in `a`'s statement or value, directly or inside an auxiliary constant
that `a` refers to.

Run on the runner after `lake build` (the load is the same as `lake lint`'s), or locally with
the daemon down:

  `lake exe mathfin_index decl-index.json`
-/

open Lean Meta

namespace MathFinTools.Index

/-- The aggregators restate the library (`#guard_msgs` pins, blueprint tags) and declare
nothing of their own worth indexing. -/
def aggregators : List Name := [`MathFin.AxiomAudit, `MathFin.AxiomAuditGen, `MathFin.Blueprint]

/-- The module that declares `n`, if it is imported. -/
def moduleOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx]?

/-- Declared in a library module (aggregators included: their auxiliary constants are still
library constants, only not indexed). -/
def inLibrary (env : Environment) (n : Name) : Bool :=
  match moduleOf env n with
  | some m => (`MathFin).isPrefixOf m
  | none => false

/-- The declaration a reader would name: not compiler-generated, not a constructor or recursor,
declared in a non-aggregator library module. A private name is judged by its user-facing part. -/
def indexed (env : Environment) (n : Name) (ci : ConstantInfo) : Bool :=
  inLibrary env n && !(aggregators.contains ((moduleOf env n).getD .anonymous)) &&
    !(ci matches .ctorInfo _ | .recInfo _ | .quotInfo _) &&
    !env.isAutoDecl (privateToUserName n)

def kindOf (env : Environment) (n : Name) : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => if isInstanceCore env n then "instance" else "def"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => if isStructure env n then "structure" else "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"

/-- The indexed declarations `ci` refers to, looking through auxiliary library constants. -/
def usesOf (env : Environment) (isIndexed : Name → Bool) (self : Name) (ci : ConstantInfo) :
    NameSet := Id.run do
  let mut out : NameSet := {}
  let mut seen : NameSet := {}
  let mut stack : Array Name := ci.getUsedConstantsAsSet.toArray
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    if isIndexed c then
      if c != self then out := out.insert c
    else if inLibrary env c then
      if let some ci' := env.find? c then
        stack := stack ++ ci'.getUsedConstantsAsSet.toArray
  return out

/-- The statement on one line, or the raw `Expr` if the delaborator fails. -/
def ppType (t : Expr) : MetaM String := do
  try
    return (← ppExpr t).pretty 100000
  catch _ =>
    return toString t

def record (env : Environment) (simps : SimpTheorems) (isIndexed : Name → Bool)
    (n : Name) (ci : ConstantInfo) : MetaM Json := do
  let doc ← findDocString? env n
  let line := (← findDeclarationRanges? n).map (·.range.pos.line) |>.getD 0
  let uses := usesOf env isIndexed n ci
  let typeUsesLib := ci.type.getUsedConstants.any (inLibrary env)
  let mut attrs : Array Json := #[]
  if simps.isLemma (.decl n) then attrs := attrs.push "simp"
  if isInstanceCore env n then attrs := attrs.push "instance"
  return Json.mkObj [
    ("name", toJson n),
    ("kind", kindOf env n ci),
    ("module", toJson ((moduleOf env n).getD .anonymous)),
    ("line", line),
    ("private", isPrivateName n),
    ("doc", match doc with | some d => Json.str d | none => Json.null),
    ("type", ← ppType ci.type),
    ("type_hash", toString ci.type.hash),
    ("type_uses_mathfin", typeUsesLib),
    ("uses", toJson (uses.toArray.qsort Name.lt)),
    ("attrs", Json.arr attrs)]

/-- The indexed declarations, sorted. -/
def indexedNames (env : Environment) : Array Name :=
  (env.constants.map₁.fold (init := #[]) fun acc n ci =>
    if indexed env n ci then acc.push n else acc).qsort Name.lt

/-- The records of one slice of the declarations. -/
def records (names : Array Name) (isIndexed : Name → Bool) : MetaM (Array Json) := do
  let env ← getEnv
  let simps := simpExtension.getState env
  names.filterMapM fun n => do
    let some ci := env.find? n | return none
    return some (← record env simps isIndexed n ci)

end MathFinTools.Index

open MathFinTools.Index in
/-- `lake exe mathfin_index OUT.json [JOBS]`: pretty-printing the statements is the cost, so
the declarations are split into `JOBS` slices (default 4) elaborated on separate threads over
the same, immutable environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  let some outPath := args.head?
    | IO.eprintln "usage: lake exe mathfin_index OUT.json [JOBS]"; return 2
  let jobs := max 1 ((args[1]?.bind String.toNat?).getD 4)
  initSearchPath (← findSysroot)
  Lean.enableInitializersExecution
  let env ← importModules #[{ module := `MathFin }] {} (trustLevel := 1024) (loadExts := true)
  let ctx : Core.Context := {
    fileName := "<mathfin_index>", fileMap := default, maxHeartbeats := 0,
    options := ({} : Options).setBool `pp.universes false }
  let names := indexedNames env
  let set : NameHashSet := names.foldl (·.insert ·) {}
  let size := (names.size + jobs - 1) / jobs
  let tasks ← (List.range jobs).toArray.mapM fun j =>
    IO.asTask (prio := .dedicated) do
      let slice := names.extract (j * size) ((j + 1) * size)
      return (← ((records slice set.contains).run' {} {}).toIO ctx { env }).1
  let mut out : Array Json := #[]
  for t in tasks do
    out := out ++ (← IO.ofExcept (← IO.wait t))
  let json := Json.mkObj [("toolchain", Lean.versionString), ("decls", Json.arr out)]
  IO.FS.writeFile outPath (json.compress ++ "\n")
  return 0
