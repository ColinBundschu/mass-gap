import MassGap.Xfusion
/-!
The check module for `con:xfusion`: the batteries re-read the
walk's base — `c₁ = 1` at `r = 1` and `c₁ = 2` beyond, the
adjoint's multiplicity in its own square — and the vacuum's
multiplicity at the unit channel, decided at the low residues and
read through the module's general theorems at the generic ones
(`c1_eq`, `c1_one`, `vacMult_eq`), each generic pin the theorem's
route beside a decided anchor; the refusal records isolate the
width floors, the base off two at `r = 1` and both counts at the
sum's unit below the sector's widths; the structural identities
are `lem:channels`' closure reads, pinned in its own battery.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open xfusion

/-! The walk's base: the decided anchors, the theorem's routes at
the generic residues, and the width records — the `r = 1` refusal
of the generic value with the below-width vacancy. -/

example : c1 2 = 1 := by decide +kernel
example : c1 2 = 1 := c1_one
example : c1 3 = 2 := by decide +kernel
example : c1 3 = 2 := c1_eq 3 (by decide +kernel)
example : c1 4 = 2 := by decide +kernel
example : c1 6 = 2 := c1_eq 6 (by decide +kernel)
example : c1 9 = 2 := c1_eq 9 (by decide +kernel)
example : ¬ (c1 2 = 2) := by decide +kernel
example : c1 1 = 0 := by decide +kernel

/-! The vacuum's multiplicity at the unit channel: the decided
anchors, the theorem's routes, and the width records. -/

example : vacMult 2 = 1 := by decide +kernel
example : vacMult 2 = 1 := vacMult_eq 2 (by decide +kernel)
example : vacMult 3 = 1 := by decide +kernel
example : vacMult 6 = 1 := vacMult_eq 6 (by decide +kernel)
example : vacMult 9 = 1 := vacMult_eq 9 (by decide +kernel)
example : ¬ (vacMult 1 = 1) := by decide +kernel
example : vacMult 1 = 0 := by decide +kernel
