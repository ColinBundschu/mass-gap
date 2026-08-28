import MassGap.Adjchar
/-!
The check module for `lem:adjchar`: the batteries re-read the
adjoint's shape and content list by kernel `decide` — the reduced
column multisets, the content formula's instances (the
unit-monomial content at the residue's count, a letter-pair move at
one, a further family at the fold's unit), and the formula's
coherence with the adjoint span's content occupancy over every
content at the degree.  The occupied content's two reads close the
module — the entrywise cap with the boxes at the fundamental
count, and the two arms applied whole at a unit content and at a
letter-pair move — with the occupancy binder isolated at the
off-list content.  The coherence with the adjoint span's occupancy
is swept by kernel `decide` over every content of the degree at the
su(2), su(3) and su(4) instances, and the general theorem
`occupancy` runs its route at three contents of the width three.
Its residue binder is load-bearing at its committed refusal, the
width one where the adjoint's shape collapses onto the single
column; its width binder is a frame, the identity standing at the
junk widths.
-/
set_option maxHeartbeats 4000000

open ground places adjchar

/-! The adjoint's column multisets, the two columns joining at
`d_f = 2`. -/

example : theta 2 = [2, 0] := rfl
example : theta 3 = [1, 1, 0] := rfl
example : theta 4 = [1, 0, 1, 0] := rfl

/-! The content formula's instances. -/

example : multRead 2 [1, 1] = 1 := rfl
example : multRead 3 [1, 1, 1] = 2 := rfl
example : multRead 3 [2, 1, 0] = 1 := rfl
example : multRead 3 [2, 0, 1] = 1 := rfl
example : multRead 3 [3, 0, 0] = 0 := rfl
example : multRead 3 [2, 2, 2] = 0 := rfl
example : multRead 6 [1, 1, 1, 1, 1, 1] = 5 := rfl

/-! The coherence with `def:blockcount`'s carrier at the su(2),
su(3) and su(4) instances, every content of the degree swept — the
su(4) sweep the formula's check at the first fully generic
residue. -/

example : ((places.allContents 2 2).all (fun m =>
    adjchar.multRead 2 m
      == blockcount.occupancyAt
        (blockcount.blockSpan (adjchar.theta 2)) m)) = true := by decide +kernel

example : ((places.allContents 3 3).all (fun m =>
    adjchar.multRead 3 m
      == blockcount.occupancyAt
        (blockcount.blockSpan (adjchar.theta 3)) m)) = true := by decide +kernel

set_option maxHeartbeats 16000000 in
example : ((places.allContents 4 4).all (fun m =>
    adjchar.multRead 4 m
      == blockcount.occupancyAt
        (blockcount.blockSpan (adjchar.theta 4)) m)) = true := by decide +kernel

/-! The adjoint shape's length and rows, the promoted reads. -/

example : (adjchar.theta 6).length = 6 := adjchar.length_theta 6
example : places.rowList (adjchar.theta (4 + 2))
    = 2 :: (List.replicate 4 1 ++ [0]) := adjchar.rowList_theta 4

/-! The occupied content's flat read: the entrywise cap at two with
the boxes at the fundamental count. -/

example : (∀ i, ground.getAt 0 [2, 0, 1] i ≤ 2)
    ∧ ground.sumNat [2, 0, 1] = 3 :=
  multRead_flat 3 [2, 0, 1] (by decide +kernel)

/-! The content read's two arms, applied whole.  The unit content
`[1, 1, 1]` at `d = 3` takes the left arm at the residue's count,
the move `[2, 0, 1]` the right at the raised place `0` against the
lowered place `1`. -/

example : ∀ k, k < 3 → ground.getAt 0 [1, 1, 1] k = 1 := by decide +kernel

example : (([1, 1, 1] : List Nat).length = 3
      ∧ (∀ k, k < 3 → ground.getAt 0 [1, 1, 1] k = 1)
      ∧ multRead 3 [1, 1, 1] = 3 - 1)
    ∨ (([1, 1, 1] : List Nat).length = 3
      ∧ (∃ i, i < 3 ∧ ∃ j, j < 3 ∧ ¬ i = j
          ∧ ground.getAt 0 [1, 1, 1] i = 2
          ∧ ground.getAt 0 [1, 1, 1] j = 0
          ∧ (∀ k, k < 3 → ¬ k = i → ¬ k = j
              → ground.getAt 0 [1, 1, 1] k = 1))
      ∧ multRead 3 [1, 1, 1] = 1) :=
  multRead_cases 3 [1, 1, 1] (by decide +kernel)

example : ground.getAt 0 [2, 0, 1] 0 = 2 := by decide +kernel
example : ground.getAt 0 [2, 0, 1] 1 = 0 := by decide +kernel
example : ground.getAt 0 [2, 0, 1] 2 = 1 := by decide +kernel

example : (([2, 0, 1] : List Nat).length = 3
      ∧ (∀ k, k < 3 → ground.getAt 0 [2, 0, 1] k = 1)
      ∧ multRead 3 [2, 0, 1] = 3 - 1)
    ∨ (([2, 0, 1] : List Nat).length = 3
      ∧ (∃ i, i < 3 ∧ ∃ j, j < 3 ∧ ¬ i = j
          ∧ ground.getAt 0 [2, 0, 1] i = 2
          ∧ ground.getAt 0 [2, 0, 1] j = 0
          ∧ (∀ k, k < 3 → ¬ k = i → ¬ k = j
              → ground.getAt 0 [2, 0, 1] k = 1))
      ∧ multRead 3 [2, 0, 1] = 1) :=
  multRead_cases 3 [2, 0, 1] (by decide +kernel)

/-- Refusal isolating `hpos`: the content `[3, 0, 0]` reads off the
list — a letter beyond two — so the read is the fold's unit and
neither arm is available. -/
example : ¬ 0 < multRead 3 [3, 0, 0] := by decide +kernel

/-! The content read's two arms at their own instances: the
letter-pair move at the explicit counts, and the unit-monomial
content at the residue's count — each decided beside the theorem's
route. -/

example : adjchar.multRead 4 [0, 2, 1, 1] = 1 := by decide +kernel

example : adjchar.multRead 4 [0, 2, 1, 1] = 1 :=
  adjchar.multRead_move 4 [0, 2, 1, 1] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

example : adjchar.multRead 5 (List.replicate 5 1) = 5 - 1 := by decide +kernel

example : adjchar.multRead 5 (List.replicate 5 1) = 5 - 1 :=
  adjchar.multRead_ones 5

/-! `lem:adjchar`'s general theorem at `d_f = 3`: the adjoint span's
content occupancy against the formula at three contents — the
unit-monomial content at the residue's count, a letter-pair move at
one, and an off-list content at the fold's unit — each read by the
theorem's route and by the kernel beside it. -/

example : blockcount.occupancyAt
    (blockcount.blockSpan (adjchar.theta 3)) [1, 1, 1] = 2 := by decide +kernel

example : blockcount.occupancyAt
      (blockcount.blockSpan (adjchar.theta 3)) [1, 1, 1]
    = adjchar.multRead 3 [1, 1, 1] :=
  adjchar.occupancy 3 (by decide +kernel) [1, 1, 1] (by decide +kernel)

example : blockcount.occupancyAt
    (blockcount.blockSpan (adjchar.theta 3)) [2, 0, 1] = 1 := by decide +kernel

example : blockcount.occupancyAt
      (blockcount.blockSpan (adjchar.theta 3)) [2, 0, 1]
    = adjchar.multRead 3 [2, 0, 1] :=
  adjchar.occupancy 3 (by decide +kernel) [2, 0, 1] (by decide +kernel)

example : blockcount.occupancyAt
    (blockcount.blockSpan (adjchar.theta 3)) [3, 0, 0] = 0 := by decide +kernel

example : blockcount.occupancyAt
      (blockcount.blockSpan (adjchar.theta 3)) [3, 0, 0]
    = adjchar.multRead 3 [3, 0, 0] :=
  adjchar.occupancy 3 (by decide +kernel) [3, 0, 0] (by decide +kernel)

/-- Held binders of `occupancy`.  `hd` is load-bearing at its
committed refusal: at the width one the adjoint's shape collapses
onto the single column `[2]`, whose block is the one line at the
content `[2]`, while the formula reads the fold's unit at every
content of that width, so the identity refuses with the width
binder holding. -/
example : ¬ (blockcount.occupancyAt
      (blockcount.blockSpan (adjchar.theta 1)) [2]
    = adjchar.multRead 1 [2]) := by decide +kernel

example : ([2] : List Nat).length = 1 := by decide +kernel

/-- `hm` is the width frame: off the stated width both sides read
the fold's unit, the span's members carrying the width throughout,
so the identity holds at the junk widths and no refusal is
constructible. -/
example : blockcount.occupancyAt
      (blockcount.blockSpan (adjchar.theta 3)) [1, 1]
    = adjchar.multRead 3 [1, 1] := by decide +kernel

example : blockcount.occupancyAt
      (blockcount.blockSpan (adjchar.theta 3)) [1, 1, 1, 1]
    = adjchar.multRead 3 [1, 1, 1, 1] := by decide +kernel
