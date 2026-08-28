import MassGap.Lowerspan
import MassGapChecks.Blockcount
/-!
The check module for `lem:lowerspan`'s structural tier: the two
discharge theorems read at committed shapes beside their decided
values — the top content's occupancy one at the head's line, the
occupied contents' dominance reads, and the height fold's
instances — the `d = 2` symmetric square and the `d = 3` adjoint
the committed blocks.
-/
set_option maxHeartbeats 4000000

open ground places blockcount lowerspan

/-! The discharges' theorem instances at the committed shapes. -/

example : weylchar.topRead [1, 1, 0]
    ((blockSpan [1, 1, 0]).map HVec.content) := topRead_def [1, 1, 0]
example : weylchar.topRead [2, 0]
    ((blockSpan [2, 0]).map HVec.content) := topRead_def [2, 0]
example : weylchar.supportRead [2, 0]
    ((blockSpan [2, 0]).map HVec.content) := supportRead_def [2, 0]
example : weylchar.supportRead [1, 1, 0]
    ((blockSpan [1, 1, 0]).map HVec.content) := supportRead_def [1, 1, 0]

/-! The reads decided outright beside the theorem instances: the
four hypothesis displays at the `d = 2` square's own family. -/

example : weylchar.topRead [2, 0]
    ((blockSpan [2, 0]).map HVec.content) := by decide +kernel
example : weylchar.supportRead [2, 0]
    ((blockSpan [2, 0]).map HVec.content) := by decide +kernel
example : weylchar.symRead 2
    ((blockSpan [2, 0]).map HVec.content) := by decide +kernel
example : weylchar.recRead [2, 0]
    ((blockSpan [2, 0]).map HVec.content) := by decide +kernel

/-! The identity end to end: `thm:weylchar`'s conclusion composed
from the four discharged hypothesis reads at the span's own
family, every key at once. -/

example : ∀ y : List Nat,
    weylchar.identityAt
      (fun chi => ground.countOf chi
        ((blockSpan [2, 0]).map HVec.content)) [2, 0] y :=
  weylchar.identityRead [2, 0] ((blockSpan [2, 0]).map HVec.content)
    (by decide +kernel) (by decide +kernel)
    (supportRead_def [2, 0]) (topRead_def [2, 0])

/-! The decided values beside them: the top's occupancy one, the
adjoint's interior content at two, the dominance reads, and a
non-dominated content unoccupied. -/

example : occupancyAt (blockSpan [1, 1, 0]) (rowList [1, 1, 0]) = 1 := by
  rw [blockcount.span110_pin]; decide +kernel
example : occupancyAt (blockSpan [1, 1, 0]) [1, 1, 1] = 2 := by
  rw [blockcount.span110_pin]; decide +kernel
example : occupancyAt (blockSpan [2, 0]) [1, 1] = 1 := by decide +kernel
example : occupancyAt (blockSpan [1, 1, 0]) [3, 0, 0] = 0 := by
  rw [blockcount.span110_pin]; decide +kernel
example : weylchar.domBy [1, 1, 1] (rowList [1, 1, 0]) := by decide +kernel
example : weylchar.domBy [1, 1] (rowList [2, 0]) := by decide +kernel

/-! The height fold's reads: the top's value with the drop at an
occupied lowering. -/

example : ht (rowList [1, 1, 0]) = 5 := by decide +kernel
example : ht (units.moveDn 0 (rowList [1, 1, 0])) + 1
    = ht (rowList [1, 1, 0]) := by decide +kernel

/-! The raise's reads: the general move strictly raises the height
fold at an interior pair, the occupied and the unoccupied source
alike, with the theorem applied whole beside them. -/

example : lowerspan.ht [1, 1] < lowerspan.ht (blockcount.moveAt 0 1 [1, 1])
    ∧ lowerspan.ht [2, 0] < lowerspan.ht (blockcount.moveAt 0 1 [2, 0])
    ∧ lowerspan.ht [2, 1, 0] < lowerspan.ht (blockcount.moveAt 0 2 [2, 1, 0])
    ∧ lowerspan.ht [1, 0, 1] < lowerspan.ht (blockcount.moveAt 0 1 [1, 0, 1])
    := by decide +kernel

example : lowerspan.ht [1, 1] < lowerspan.ht (blockcount.moveAt 0 1 [1, 1]) :=
  lowerspan.ht_moveAt_raise 0 1 [1, 1] (by decide +kernel) (by decide +kernel)

/-! The semantic tier's theorem instances at the committed shapes:
the span sized, its content groups independent, and every occupied
interior lowering image inside its group's span (`spanReads`). -/

example : (∀ v ∈ blockSpan [1, 1, 0], blockcount.sized v)
    ∧ blockcount.indepAll (blockSpan [1, 1, 0])
    ∧ blockcount.closedAt (blockSpan [1, 1, 0]) 3 :=
  spanReads [1, 1, 0]
example : (∀ v ∈ blockSpan [2, 0], blockcount.sized v)
    ∧ blockcount.indepAll (blockSpan [2, 0])
    ∧ blockcount.closedAt (blockSpan [2, 0]) 2 :=
  spanReads [2, 0]
