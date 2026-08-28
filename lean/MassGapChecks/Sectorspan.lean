import MassGap.Sectorspan
/-!
The check module for `lem:sectorspan`: the batteries re-read the
sector's span at three window matrices by kernel `decide` — the
rotation `rot3`, whose pivot count is the window's dimension, the
singular `sing3`, whose first two keys carry one row, so the pivot
count falls one short, and the rectangular `rect32`, three rows of
the product window's list over two window keys at the full pivot
count.

The span read is decided at the rotation and at the rectangular
window, refused at the singular matrix — the shape conjunct held
beside the refusal, the pivot count the isolated conjunct — and
the pivot product sits off the sum's unit at each matrix through
the universal read, `def:elim`'s pivot fold.

The adjoint display rides at a two-key window whose transpose is a
different matrix — the frame below decides the two apart, so the
transposed multiplication is load-bearing in the pairing — and at
the rectangular window, the product window's rows against the
window's keys, with the display's instance decided raw beside the
theorem's own route each time.

The involution's ground read rides at a gap with two kernel
coordinates and the permutation exchanging them: the two matrices
commute, the first coordinate's unit vector is a ground, and its
image under the permutation is a ground again.  The refusal moves
one kernel coordinate onto an occupied one — the commutation fails
and the image leaves the sum's unit — the commutation the isolated
binder.

The filling reads at the three matrices: the perpendicular element
enters at its pairing reads (`perp_kernel`, the kernel membership
decided raw beside the route), at the rotation's and the
rectangle's full pivot counts a perpendicular element of the order
is at the sum's unit, and at the singular matrix the kernel list's
first member is a perpendicular element off the unit family, the
fill's refusal at the pivot count and `occupied_off`'s own
witness.  The perpendicularity refusal holds the further binders
and refuses the conclusion at an element off every word image's
perpendicular set.

The shape binders (`rowsLen`, the vector lengths) are the
certificate Props' standing shape convention and carry no refusal
of their own.
-/

open ground elim sectorspan

private def u : BPair := BPair.unit

/-- The three-key rotation: one pivot per key, the full count. -/
private def rot3 : Mat :=
  [[u, ⟨2, 1⟩, u], [u, u, ⟨2, 1⟩], [⟨2, 1⟩, u, u]]

/-- The singular three-key window: the first two rows are one row,
so the pivot count falls one short of the order. -/
private def sing3 : Mat :=
  [[⟨2, 1⟩, ⟨2, 1⟩, u], [⟨2, 1⟩, ⟨2, 1⟩, u], [u, u, ⟨2, 1⟩]]

/-- The rectangular window: three rows of the product window's
list over two window keys, the full pivot count at the width. -/
private def rect32 : Mat :=
  [[⟨2, 1⟩, u], [u, ⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]]

/-! The span read at the three windows, and the pivot fold off the
sum's unit through the universal read. -/

private theorem rankRot : elim.rank rot3 = 3 := by decide +kernel
private theorem rankSing : elim.rank sing3 = 2 := by decide +kernel
private theorem rankRect : elim.rank rect32 = 2 := by decide +kernel

example : spanRead 3 rot3 := ⟨by decide +kernel, rankRot⟩
example : spanRead 2 rect32 := ⟨by decide +kernel, rankRect⟩

/-- The refusal isolating the pivot count: the shape holds at the
order while the count falls one short. -/
example : elim.rowsLen 3 sing3 := by decide +kernel
example : ¬ spanRead 3 sing3 := fun h =>
  absurd (rankSing.symm.trans h.2) (by decide +kernel)

example : ¬ (elim.pivotProd rot3).oneValue BPair.unit :=
  elim.pivotProd_off rot3
example : ¬ (elim.pivotProd sing3).oneValue BPair.unit :=
  elim.pivotProd_off sing3

/-! The adjoint display at a two-key window and at the rectangular
one. -/

/-- The two-key window whose transpose is a different matrix. -/
private def P2 : Mat := [[⟨2, 1⟩, ⟨3, 1⟩], [u, ⟨2, 1⟩]]

private def w2 : List BPair := [⟨2, 1⟩, ⟨3, 1⟩]

private def x2 : List BPair := [⟨4, 1⟩, u]

/-- The fixture's frame: the transpose is off the matrix, so the
transposed multiplication is load-bearing in the pairing below. -/
example : ¬ matOneValue (transposeM P2) P2 := by decide +kernel

example : (dotP w2 (matVec P2 x2)).oneValue
    (dotP (matVec (transposeM P2) w2) x2) := by decide +kernel

example : (dotP w2 (matVec P2 x2)).oneValue
    (dotP (matVec (transposeM P2) w2) x2) :=
  adj_read 2 2 P2 (by decide +kernel) (by decide +kernel) w2 x2
    (by decide +kernel) (by decide +kernel)

private def w3 : List BPair := [⟨2, 1⟩, u, ⟨3, 1⟩]

example : (dotP w3 (matVec rect32 x2)).oneValue
    (dotP (matVec (transposeM rect32) w3) x2) := by decide +kernel

example : (dotP w3 (matVec rect32 x2)).oneValue
    (dotP (matVec (transposeM rect32) w3) x2) :=
  adj_read 3 2 rect32 (by decide +kernel) (by decide +kernel) w3 x2
    (by decide +kernel) (by decide +kernel)

/-! The involution's ground read at a gap with two kernel
coordinates. -/

/-- The gap at two kernel coordinates: the third key alone is
occupied. -/
private def Et3 : Mat := [[u, u, u], [u, u, u], [u, u, ⟨6, 1⟩]]

/-- The permutation exchanging the first two coordinates. -/
private def J3 : Mat := [[u, ⟨2, 1⟩, u], [⟨2, 1⟩, u, u], [u, u, ⟨2, 1⟩]]

/-- The first coordinate's unit vector. -/
private def e0 : List BPair := [⟨2, 1⟩, u, u]

example : matOneValue (matMul Et3 J3) (matMul J3 Et3) := by decide +kernel
example : poly.unitTail (matVec Et3 e0) := by decide +kernel

example : poly.unitTail (matVec Et3 (matVec J3 e0)) := by decide +kernel

example : poly.unitTail (matVec Et3 (matVec J3 e0)) :=
  invol_ground 3 Et3 J3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) e0
    (by decide +kernel) (by decide +kernel)

/-- The refusal isolating `hcomm`: at one kernel coordinate the
permutation moves it onto the occupied key, the two matrices no
longer commute, and the image leaves the sum's unit while the
ground read at the vector itself still holds. -/
private def Et3o : Mat := [[u, u, u], [u, ⟨6, 1⟩, u], [u, u, ⟨8, 1⟩]]

example : ¬ matOneValue (matMul Et3o J3) (matMul J3 Et3o) := by decide +kernel
example : poly.unitTail (matVec Et3o e0) := by decide +kernel
example : ¬ poly.unitTail (matVec Et3o (matVec J3 e0)) := by decide +kernel

/-! The filling at the full pivot count, and the perpendicular
element off the unit family below it. -/

/-- The unit family at the order. -/
private def vU : List BPair := [u, u, u]

example : (∀ i, i < rot3.length →
    (dotP vU (ground.getAt ([] : List BPair) rot3 i)).oneValue
      BPair.unit) := by decide +kernel

example : poly.unitTail (matVec rot3 vU) :=
  perp_kernel rot3 vU (by decide +kernel)

example : poly.unitTail (matVec rot3 vU) := by decide +kernel

example : poly.unitTail vU :=
  fills 3 rot3 ⟨by decide +kernel, rankRot⟩ vU
    (by decide +kernel) (by decide +kernel)

private def vU2 : List BPair := [u, u]

example : poly.unitTail vU2 :=
  fills 2 rect32 ⟨by decide +kernel, rankRect⟩ vU2
    (by decide +kernel) (by decide +kernel)

/-- The refusal isolating the perpendicularity: an element off the
word images' perpendicular set at the full pivot count, the
conclusion off with it. -/
private def v1 : List BPair := [⟨2, 1⟩, u, u]

example : ¬ (∀ i, i < rot3.length →
    (dotP v1 (ground.getAt ([] : List BPair) rot3 i)).oneValue
      BPair.unit) := by decide +kernel
example : ¬ poly.unitTail v1 := by decide +kernel

/-- The kernel list's first member at the singular window: a
perpendicular element of the order whose pivot-free coordinate is
the crossed pivots' product. -/
private def wK : List BPair :=
  ground.getAt ([] : List BPair) (elim.kernelList 3 sing3) 0

/-- The refusal isolating the pivot count in the fill: the shape
holds, the member is of the order and perpendicular, and the count
alone fails — the member sits off the unit family. -/
example : ¬ (elim.rank sing3 = 3) := fun h =>
  absurd (rankSing.symm.trans h) (by decide +kernel)
example : wK.length = 3 := by decide +kernel
example : poly.unitTail (matVec sing3 wK) := by decide +kernel
example : ¬ poly.unitTail wK := by decide +kernel

example : ∃ v : List BPair, v.length = 3
    ∧ poly.unitTail (matVec sing3 v) ∧ ¬ poly.unitTail v :=
  occupied_off 3 sing3 (by decide +kernel)
    (by rw [rankSing]; exact Nat.lt_succ_self 2)
