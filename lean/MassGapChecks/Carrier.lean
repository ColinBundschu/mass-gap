import MassGap.Carrier
/-!
The check module for `def:carrier`: the batteries re-read the
index layer by kernel `decide` at the label calculus's
instantiation — the invariant count's row fold (the unit's one,
the single nonunit label's refusal, the pair at the dual, the
adjoint triple at the base `c₁`), the content fold, the vertex
multiplicities at the square's corners, the occupied reads (the
fundamental loop occupied, the single link and the all-`f` theta
assignment refused — the degree-one endpoint and the odd parity),
and the window index's members at stated cutoffs.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground places lattice fusion carrier

/-! The invariant count's row fold. -/

example : invCount (dataA 2) [] = 1 := by decide +kernel
example : invCount (dataA 2) [[1, 0]] = 0 := by decide +kernel
example : invCount (dataA 2) [[1, 0], [1, 0]] = 1 := by decide +kernel
example : invCount (dataA 3) [[1, 0, 0], [0, 1, 0]] = 1 := by decide +kernel
example : invCount (dataA 3) [[1, 0, 0], [1, 0, 0]] = 0 := by decide +kernel
example : invCount (dataA 3) [[1, 0, 0], [1, 0, 0], [1, 0, 0]] = 1 := by
  decide +kernel
example : invCount (dataA 3) [[1, 1, 0], [1, 1, 0], [1, 1, 0]] = 2 := by
  decide +kernel
example : invCount (dataA 3) [[1, 1, 0], [1, 1, 0], [1, 1, 0]]
    = (dataA 3).c1 := by decide +kernel

/-! The content fold at the cleared second member. -/

example : contentN (dataA 2) [[1, 0], [1, 0], [1, 0], [1, 0]] = 12 := by
  decide +kernel
example : contentN (dataA 2) [[1, 0], [0, 0], [2, 0], [0, 0]] = 11 := by
  decide +kernel

/-! The vertex multiplicities and the occupied reads at the
square: the fundamental loop occupied at every corner's unit
multiplicity, the single link refused at its degree-one ends. -/

example : vmult (dataA 2) square [[1, 0], [1, 0], [1, 0], [1, 0]] 0
    = 1 := by decide +kernel
example : occupied (dataA 2) square [[1, 0], [1, 0], [1, 0], [1, 0]]
    = true := by decide +kernel
example : occupied (dataA 2) square [[1, 0], [0, 0], [0, 0], [0, 0]]
    = false := by decide +kernel
example : occupied (dataA 2) square
    [[2, 0], [2, 0], [2, 0], [2, 0]] = true := by decide +kernel

/-! The incoming dualization at three letters: the constant
fundamental loop occupied (each corner `f` against the incoming
dual's dual), the alternating `f`, `f̄` assignment refused at the
corners' matched pair. -/

example : occupied (dataA 3) square
    [[1, 0, 0], [1, 0, 0], [1, 0, 0], [1, 0, 0]] = true := by decide +kernel
example : occupied (dataA 3) square
    [[1, 0, 0], [0, 1, 0], [1, 0, 0], [0, 1, 0]] = false := by decide +kernel

/-! The all-`f` theta assignment refused at the shared ends' odd
parity. -/

example : occupied (tabulate (dataA 2) 3) thetaG
    [[1, 0], [1, 0], [1, 0], [1, 0], [1, 0], [1, 0], [1, 0]]
    = false := by decide +kernel

/-! The window index's members at stated cutoffs: the fundamental
loop alone below the next label's loop. -/

example : (idx (dataA 2) square 12).length = 1 := by
  rw [← idxA_eq]; decide +kernel
example : (idx (dataA 2) square 32).length = 2 := by
  rw [← idxA_eq]; decide +kernel

/-! The pruned walk reads the enumeration itself
(`prop:windowfinite`'s per-link cutoff read, `idxA_eq`), pinned at
the committed windows and at a window where the refusal bites at
depth. -/

example : idxA (dataA 2) square 12
    = idx (dataA 2) square 12 := by decide +kernel
example : idxA (tabulate (dataA 2) 12) thetaG 12
    = idx (tabulate (dataA 2) 12) thetaG 12 := by decide +kernel

/-! The tabulated route's coherence with the interface at stated
reads. -/

example : (tabulate (dataA 2) 12).count [1, 0] [1, 0] [2, 0]
    = (dataA 2).count [1, 0] [1, 0] [2, 0] := by decide +kernel
example : (tabulate (dataA 2) 12).count [1, 0] [1, 0] (labels.unitL 2)
    = (dataA 2).count [1, 0] [1, 0] (labels.unitL 2) := by decide +kernel
example : (tabulate (dataA 2) 12).row [1, 0] [1, 0]
    = (dataA 2).row [1, 0] [1, 0] := by decide +kernel

/-! The committed window enumerations, the tier's shared fixtures:
each a stated value of `def:carrier`'s index at a committed window,
its pin `prop:windowfinite`'s content-pruned walk (`idxA_eq`), the
consuming modules' reads the named displays' applications. -/

namespace carrier

/-- The square window at two letters, cutoff 32: the fundamental
loop with the two-box loop. -/
def sqIx2 : List (List places.Shape) :=
  [[[1, 0], [1, 0], [1, 0], [1, 0]],
   [[2, 0], [2, 0], [2, 0], [2, 0]]]

theorem sqIx2_pin : idx (dataA 2) square 32 = sqIx2 := by
  rw [← idxA_eq]; decide +kernel

/-- The square window at three letters, cutoff 32: the fundamental
loop with the anti-fundamental's. -/
def sqIx3 : List (List places.Shape) :=
  [[[1, 0, 0], [1, 0, 0], [1, 0, 0], [1, 0, 0]],
   [[0, 1, 0], [0, 1, 0], [0, 1, 0], [0, 1, 0]]]

theorem sqIx3_pin : idx (dataA 3) square 32 = sqIx3 := by
  rw [← idxA_eq]; decide +kernel

/-- The theta window at two letters, cutoff 18: the two plaquette
loops with the hexagon. -/
def thIx18 : List (List places.Shape) :=
  [[[1, 0], [1, 0], [1, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [1, 0], [1, 0], [0, 0], [1, 0], [1, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [1, 0], [1, 0], [1, 0]]]

theorem thIx18_pin :
    idx (tabulate (dataA 2) 18) thetaG 18 = thIx18 := by
  rw [← idxA_eq]; decide +kernel

/-- The theta window at two letters, cutoff 12: the two plaquette
loops, the hexagon beyond the cutoff. -/
def thIx12 : List (List places.Shape) :=
  [[[1, 0], [1, 0], [1, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [1, 0], [1, 0], [1, 0]]]

theorem thIx12_pin :
    idx (tabulate (dataA 2) 12) thetaG 12 = thIx12 := by
  rw [← idxA_eq]; decide +kernel

end carrier
