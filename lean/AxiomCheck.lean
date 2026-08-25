import Lean
import MassGap
import MassGapChecks

/-!
The axiom read over the whole tree.  Every constant declared by
the two libraries `MassGap` and `MassGapChecks` — the definitions,
the theorems, the structures and inductives with their generated
recursors and projections, the instances, and the private tier —
is walked with `Lean.collectAxioms`, and the run prints the count
of constants read and every constant depending on any axiom.  The
expected output is the count with the vacant list; a constant
depending on an axiom (`propext`, `Quot.sound`, `Classical.choice`,
`sorryAx`, or any other) is printed with its axiom list and the
run ends in an error, so the exit status is the read.

Run from this directory, after `lake build`:

    lake env lean AxiomCheck.lean

The batteries of `MassGapChecks` are `example` declarations,
kernel-checked at `lake build` and not constants of the
environment; the build refuses a `sorry` anywhere in either
library outright, `lakefile.toml` setting `warningAsError`, so
the `declaration uses sorry` diagnostic is a build error and
`lake build` completing is the read that no `sorry` exists.
-/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.allImportedModuleNames
  let mut total := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (c, _) in env.constants.toList do
    match env.getModuleIdxFor? c with
    | some idx =>
      let m := mods[idx.toNat]!
      if (`MassGap).isPrefixOf m || (`MassGapChecks).isPrefixOf m then
        total := total + 1
        let axs ← collectAxioms c
        if !axs.isEmpty then
          bad := bad.push (c, axs)
    | none => pure ()
  IO.println s!"constants read: {total}"
  IO.println s!"constants depending on axioms: {bad.size}"
  for (c, axs) in bad do
    IO.println s!"  {c}: {axs}"
  if !bad.isEmpty then
    throwError "the admitted axiom set is empty; {bad.size} constant(s) depend on axioms"
