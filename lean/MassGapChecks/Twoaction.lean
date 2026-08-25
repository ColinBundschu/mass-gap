import MassGap.Twoaction
/-!
The check module for `thm:twoaction`'s invariant clause: the
bridge's coefficient `2 d_f` at committed residues fixes the two
ends and moves every interior pair, each read routed through the
characterization's member instance. -/

open ground segment twoaction

example : rayEq .free (unitschain.bridgeMap (2 * posOfSucc 1) .free) := by
  decide +kernel
example : rayEq .free (unitschain.bridgeMap (2 * posOfSucc 1) .free) :=
  (ends_fixed 1 .free).mpr (Or.inl rfl)
example : rayEq .contact
    (unitschain.bridgeMap (2 * posOfSucc 2) .contact) := by
  decide +kernel
example : rayEq .contact
    (unitschain.bridgeMap (2 * posOfSucc 2) .contact) :=
  (ends_fixed 2 .contact).mpr (Or.inr rfl)
example : ¬ rayEq (.mid 3 7)
    (unitschain.bridgeMap (2 * posOfSucc 1) (.mid 3 7)) := by
  decide +kernel
example : ¬ rayEq (.mid 3 7)
    (unitschain.bridgeMap (2 * posOfSucc 1) (.mid 3 7)) :=
  fun h => ((ends_fixed 1 (.mid 3 7)).mp h).elim
    (fun h1 => Coupling.noConfusion h1)
    (fun h2 => Coupling.noConfusion h2)
