import MassGap.Leastwindow
import MassGap.Algebra
/-!
The check module for `prop:leastwindow`: the batteries re-read the
index supports by kernel `decide` at the label calculus's
instantiation — a configuration's support links, an element's window
links and touched vertices over its members, the members' largest
content, and the multiplication window bound's instances: the
plaquette row's targets sit in the union region at the fused
content, the far row at the two contents' sum and the shared-link
row at its computed largest.
-/

namespace leastwindow
set_option maxHeartbeats 16000000

open ground lattice fusion

private def twoSq : Region :=
  ⟨8, 8, [0, 1, 2, 3, 4, 5, 6, 7], [1, 2, 3, 0, 5, 6, 7, 4],
   [[(0, true), (1, true), (2, true), (3, true)],
    [(4, true), (5, true), (6, true), (7, true)]],
   [true, false, true, false, true, false, true, false], rfl, rfl⟩

private def plaqB : List (Nat × Bool) :=
  [(4, true), (5, true), (6, true), (7, true)]

private def plaqBT : List (Nat × Bool) :=
  [(4, true), (5, true), (6, true), (3, false)]

private def fLoop8 : List places.Shape :=
  List.replicate 4 [1, 0] ++ List.replicate 4 (labels.unitL 2)

private def fLoop7 : List places.Shape :=
  List.replicate 4 [1, 0] ++ List.replicate 3 (labels.unitL 2)

/-! The index supports: the support links, the window links and
vertices over an element's members, and the largest content. -/

theorem pin1 : suppLinks (dataA 2) fLoop8 = [0, 1, 2, 3] := by decide +kernel
theorem pin2 : windowLinks (dataA 2) twoSq [fLoop8] = [0, 1, 2, 3] := by decide +kernel
theorem pin3 : windowVerts (dataA 2) twoSq [fLoop8] = [0, 1, 2, 3] := by decide +kernel
theorem pin4 : windowVerts (dataA 2) thetaG [fLoop7] = [0, 1, 2, 3] := by decide +kernel
theorem pin5 : windowContent (dataA 2)
    [List.replicate 4 [1, 0], List.replicate 4 [2, 0]] = 32 := by decide +kernel

/-! The multiplication window bound's instances at the plaquette
row: the far row's target at the two contents' sum on the union
region, and the shared-link row at its computed largest. -/

theorem pin6 : windowContent (dataA 2)
    (algebra.plaqRow (dataA 2) twoSq plaqB fLoop8) = 44 := by decide +kernel
theorem pin7 : windowLinks (dataA 2) twoSq
    (algebra.plaqRow (dataA 2) twoSq plaqB fLoop8)
    = [0, 1, 2, 3, 4, 5, 6, 7] := by decide +kernel
theorem pin8 : windowContent (dataA 2)
    (algebra.plaqRow (dataA 2) thetaG plaqBT fLoop7) = 48 := by decide +kernel
theorem pin9 : windowLinks (dataA 2) thetaG
    (algebra.plaqRow (dataA 2) thetaG plaqBT fLoop7)
    = [0, 1, 2, 3, 4, 5, 6] := by decide +kernel

end leastwindow
