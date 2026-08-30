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
set_option maxHeartbeats 4000000

open ground gentable sertables row closing

/-! The pair at every committed member, the base and residue read
off the tables. -/

example : closing.read (supportCount (tableB 2)) (residue (tableB 2)) := by
  decide +kernel
example : closing.read (supportCount (tableB 3)) (residue (tableB 3)) := by
  decide +kernel
example : closing.read (supportCount (tableB 4)) (residue (tableB 4)) := by
  decide +kernel
example : closing.read (supportCount (tableC 3)) (residue (tableC 3)) := by
  decide +kernel
example : closing.read (supportCount (tableC 4)) (residue (tableC 4)) := by
  decide +kernel
example : closing.read (supportCount (tableD 4)) (residue (tableD 4)) := by
  decide +kernel
example : closing.read (supportCount (tableD 5)) (residue (tableD 5)) := by
  decide +kernel
example : closing.read (supportCount tableG2) (residue tableG2) := by decide +kernel
example : closing.read (supportCount tableF4) (residue tableF4) := by decide +kernel
example : closing.read (supportCount tableE6) (residue tableE6) := by decide +kernel
example : closing.read (supportCount tableE7) (residue tableE7) := by decide +kernel
example : closing.read (supportCount tableE8) (residue tableE8) := by decide +kernel

/-! The first table across the `A`-series' regimes: the base one
at the first member and two beyond. -/

example : closing.read (supportCount (tableA 1)) (residue (tableA 1)) := by
  decide +kernel
example : closing.read (supportCount (tableA 2)) (residue (tableA 2)) := by
  decide +kernel
example : closing.read (supportCount (tableA 5)) (residue (tableA 5)) := by
  decide +kernel

/-! The read's two occupancy binders, isolated: a vacant base and
a vacant residue each refuse the read outright, the match's
falsum arms. -/

example : ¬ closing.read 0 3 := by decide +kernel
example : ¬ closing.read 3 0 := by decide +kernel

/-! The universal read at an uncommitted point, the theorem route
beside the kernel's own read at a committed one. -/

example : closing.read 2 30 := closing.read_all 1 29
example : closing.read 2 5 := by decide +kernel
example : closing.read 2 5 := closing.read_all 1 4
