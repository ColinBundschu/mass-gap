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

namespace xfusion
set_option maxHeartbeats 4000000


/-! The walk's base: the decided anchors, the theorem's routes at
the generic residues, and the width records — the `r = 1` refusal
of the generic value with the below-width vacancy. -/

theorem pin1 : c1 2 = 1 := by decide +kernel
theorem pin2 : c1 2 = 1 := c1_one
theorem pin3 : c1 3 = 2 := by decide +kernel
theorem pin4 : c1 3 = 2 := c1_eq 3 (by decide +kernel)
theorem pin5 : c1 4 = 2 := by decide +kernel
theorem pin6 : c1 6 = 2 := c1_eq 6 (by decide +kernel)
theorem pin7 : c1 9 = 2 := c1_eq 9 (by decide +kernel)
theorem pin8 : ¬ (c1 2 = 2) := by decide +kernel
theorem pin9 : c1 1 = 0 := by decide +kernel

/-! The vacuum's multiplicity at the unit channel: the decided
anchors, the theorem's routes, and the width records. -/

theorem pin10 : vacMult 2 = 1 := by decide +kernel
theorem pin11 : vacMult 2 = 1 := vacMult_eq 2 (by decide +kernel)
theorem pin12 : vacMult 3 = 1 := by decide +kernel
theorem pin13 : vacMult 6 = 1 := vacMult_eq 6 (by decide +kernel)
theorem pin14 : vacMult 9 = 1 := vacMult_eq 9 (by decide +kernel)
theorem pin15 : ¬ (vacMult 1 = 1) := by decide +kernel
theorem pin16 : vacMult 1 = 0 := by decide +kernel

end xfusion
