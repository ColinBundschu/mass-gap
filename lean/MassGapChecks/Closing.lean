import MassGap.Closing
import MassGap.Sertables
import MassGap.Row
/-!
The check module for `thm:closing`: the batteries re-read the
constant's assembly by kernel `decide` at every committed member,
the lattice point `(3, H_r)` instantiated off the tables
themselves — the base the member's support count and the residue
the member's derived fold (`prop:row`; `con:sertables`) — and at
the first table across the `A`-series' regimes.
-/

namespace closing
set_option maxHeartbeats 4000000

open ground gentable sertables row

/-! The pair at every committed member, the base and residue read
off the tables. -/

theorem pin1 : closing.read (supportCount (tableB 2)) (residue (tableB 2)) := by
  decide +kernel
theorem pin2 : closing.read (supportCount (tableB 3)) (residue (tableB 3)) := by
  decide +kernel
theorem pin3 : closing.read (supportCount (tableB 4)) (residue (tableB 4)) := by
  decide +kernel
theorem pin4 : closing.read (supportCount (tableC 3)) (residue (tableC 3)) := by
  decide +kernel
theorem pin5 : closing.read (supportCount (tableC 4)) (residue (tableC 4)) := by
  decide +kernel
theorem pin6 : closing.read (supportCount (tableD 4)) (residue (tableD 4)) := by
  decide +kernel
theorem pin7 : closing.read (supportCount (tableD 5)) (residue (tableD 5)) := by
  decide +kernel
theorem pin8 : closing.read (supportCount tableG2) (residue tableG2) := by decide +kernel
theorem pin9 : closing.read (supportCount tableF4) (residue tableF4) := by decide +kernel
theorem pin10 : closing.read (supportCount tableE6) (residue tableE6) := by decide +kernel
theorem pin11 : closing.read (supportCount tableE7) (residue tableE7) := by decide +kernel
theorem pin12 : closing.read (supportCount tableE8) (residue tableE8) := by decide +kernel

/-! The first table across the `A`-series' regimes: the base one
at the first member and two beyond. -/

theorem pin13 : closing.read (supportCount (tableA 1)) (residue (tableA 1)) := by
  decide +kernel
theorem pin14 : closing.read (supportCount (tableA 2)) (residue (tableA 2)) := by
  decide +kernel
theorem pin15 : closing.read (supportCount (tableA 5)) (residue (tableA 5)) := by
  decide +kernel

/-! The read's two occupancy binders, isolated: a vacant base and
a vacant residue each refuse the read outright, the match's
falsum arms. -/

theorem pin16 : ¬ closing.read 0 3 := by decide +kernel
theorem pin17 : ¬ closing.read 3 0 := by decide +kernel

/-! The universal read at an uncommitted point, the theorem route
beside the kernel's own read at a committed one. -/

theorem pin18 : closing.read 2 30 := closing.read_all 1 29
theorem pin19 : closing.read 2 5 := by decide +kernel
theorem pin20 : closing.read 2 5 := closing.read_all 1 4

end closing
