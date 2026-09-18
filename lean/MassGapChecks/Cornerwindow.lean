import MassGap.Cornerwindow
/-!
The check module for `con:cornerwindow`: the batteries re-read the
square window's data by kernel `decide` at two, three and four
directions at small sides.  The census: the links', plaquettes' and
cubes' counts at `(d, L)` in `(2, 1)`, `(2, 2)`, `(2, 3)`, `(3, 2)`,
`(3, 3)`, `(4, 1)`, `(4, 2)`, the region's plaquette, coloring,
shape and simplicity reads, the boundaries' fold `Kᵀ N ≡ 0` at
three and four directions, and the kernel dimensions `0`, `8` and
`27`, the kernel list at `(3, 2)` at eight members with its Gram
determinant, and the range projector's four reads by kernel at
`(3, 1)` and through the theorems at `(3, 2)`; at two directions
the kernel list is vacant, the clearing one and the projector the
identity.  The roots' bracket: the row and column
reads, the Gram's form at the swap-signed vector `(1, -1, -1, 1)` at
`(2, 2)` reading `24` at or below `8 · 4` through `gramCap` and
refused at `4 · 4`.  The profile: the mode read `e_W` at `(2, 1)`,
`(2, 2)` and `(2, 3)` by kernel and, with the column read, at
`(3, 2)`, `(3, 3)` and `(4, 2)` through the theorems, refused at the second member's successor, the
range read at three directions, the link list's key read at a place
and the profile's column read at two links of `(2, 3)`.  The counts: the
root paths' counts at `(3, 2)`, and the region cap, the cover and
the regions' fold at `(2, 2)` and `(3, 2)`.  The Hodge identity by
kernel at two directions and at `(3, 1)` and through the theorem at
`(3, 2)`, `(3, 3)` and `(4, 2)`; the Poincaré read at the profile
through the theorem at `(3, 2)` and by kernel at `(2, 2)`, refused at
a cube's boundary at `(3, 1)`; and one line of the Dirichlet
telescope at the side three.  The kernel: two cubes' boundaries'
join at `(3, 2)` sits in the cubes' boundaries' span and a scaled
join in the kernel list's span through the descent theorem, a
plaquette's unit vector at `(3, 1)` refused at both spans by
kernel, the frame of the kernel binder, and a kernel vector padded
by one entry refused at the kernel list's span, the frame of the
length binder; the kernel list's count
reads the kernel dimension through the theorem at `(3, 2)`, `(3, 3)`
and `(4, 1)`; and the projector's four reads hold through the
theorems at `(3, 2)`, `(3, 3)` and `(4, 1)`, at the literals
generalized, and by kernel at `(3, 1)`.  The cubes' Poincaré read:
the four-cells' boundaries' fold `N N₄ ≡ 0` by kernel at `(4, 1)` and
through the theorem at `(4, 2)`, the Hodge identity at cubes by kernel at `(3, 1)` and
`(4, 1)` and through the theorem at `(3, 2)` and `(4, 2)`, the read
through the theorem at a stated chain of `(3, 2)` and at two cubes'
join of `(4, 1)`, refused at a four-cell's boundary at `(4, 1)`, a
chain off the cubes' range, with that chain refused at the range
read, the frame of the range binder, and refused at the stated chain
padded by one entry at `(3, 2)`, the frame of the length binder; and
one cube type's telescope at `(3, 2)` by kernel.
-/

namespace cornerwindow
set_option maxHeartbeats 4000000

open ground elim lattice inertia

/-! The census. -/

theorem pin1 : plaqCount 2 1 = 1 ∧ linkCount 2 1 = 4 ∧ cubeCount 2 1 = 0
    ∧ (boxRegion 2 1).verts = 4 := by decide +kernel
theorem pin2 : plaqCount 2 2 = 4 ∧ linkCount 2 2 = 12 ∧ cubeCount 2 2 = 0 := by decide +kernel
theorem pin3 : plaqCount 2 3 = 9 ∧ linkCount 2 3 = 24 := by decide +kernel
theorem pin4 : plaqCount 3 2 = 36 ∧ linkCount 3 2 = 54 ∧ cubeCount 3 2 = 8 := by decide +kernel
theorem pin5 : plaqCount 3 3 = 108 ∧ linkCount 3 3 = 144 ∧ cubeCount 3 3 = 27 := by
  decide +kernel
theorem pin6 : plaqCount 4 1 = 24 ∧ linkCount 4 1 = 32 ∧ cubeCount 4 1 = 8 := by decide +kernel
theorem pin7 : plaqCount 4 2 = 216 ∧ linkCount 4 2 = 216 ∧ cubeCount 4 2 = 96 := by
  decide +kernel

/-! The region's reads. -/

theorem pin8 : plaqRead (boxRegion 2 2) ∧ colorRead (boxRegion 2 2)
    ∧ wellRead (boxRegion 2 2) ∧ simpleRead (boxRegion 2 2) := by decide +kernel
theorem pin9 : plaqRead (boxRegion 3 2) ∧ colorRead (boxRegion 3 2)
    ∧ wellRead (boxRegion 3 2) := by decide +kernel
theorem pin10 : simpleRead (boxRegion 3 2) := by decide +kernel

/-! The boundaries and the kernel. -/

theorem pin11 : bdRead 3 2 := by decide +kernel
theorem pin12 : bdRead 4 1 := bdRead_all 4 1
theorem pin13 : kerDim 2 2 = 0 := by decide +kernel
theorem pin14 : kerDim 3 2 = 8 := by decide +kernel
theorem pin15 : kerDim 3 3 = 27 := by decide +kernel
theorem pin16 : (kerList 3 2).length = 8 := by decide +kernel
theorem pin17 : (kerList 2 2).length = 0 ∧ (projDen 2 2).oneValue (BPair.ofNat 1)
    ∧ matOneValue (proj 2 2) (idMat 4) := by decide +kernel
theorem pin18 : (projDen 3 2).oneValue (BPair.ofNat 1157625) := by decide +kernel
theorem pin19 : projSymRead 3 2 := by
  generalize 3 = d
  generalize 2 = L
  exact projSymRead_all d L
theorem pin20 : projKerRead 3 2 := by
  generalize 3 = d
  generalize 2 = L
  exact projKerRead_all d L
theorem pin21 : projGramRead 3 2 := by
  generalize 3 = d
  generalize 2 = L
  exact projGramRead_all d L
theorem pin22 : projIdemRead 3 2 := by
  generalize 3 = d
  generalize 2 = L
  exact projIdemRead_all d L

/-! The roots' bracket. -/

theorem pin23 : rowSqRead 2 2 ∧ colCountRead 2 2 := by decide +kernel
theorem pin24 : rowSqRead 3 2 ∧ colCountRead 3 2 := ⟨rowSqRead_all 3 2, colCountRead_all 3 2⟩

private def uSw : List BPair :=
  [BPair.ofNat 1, (BPair.ofNat 1).swap, (BPair.ofNat 1).swap, BPair.ofNat 1]

theorem pin25 : (quadForm (gram 2 2) uSw).oneValue (BPair.ofNat 24) := by decide +kernel
theorem pin26 : quadForm (gram 2 2) uSw ≤ BPair.ofNat (8 * dirGap 2) * dotN uSw uSw :=
  gramCap 2 2 uSw (by decide +kernel)
theorem pin27 : ¬ (quadForm (gram 2 2) uSw ≤ BPair.ofNat 4 * dotN uSw uSw) := by decide +kernel

/-! The profile. -/

theorem pin28 : modeRead 2 1 ∧ modeRead 2 2 ∧ modeRead 2 3 := by decide +kernel
theorem pin29 : modeRead 3 2 := modeRead_all 3 2
theorem pin30 : ¬ (BPair.ofNat (2 * 2 + 2 * 2 + 3) * quadForm (gram 2 2) (profile 2 2)).oneValue
    (BPair.ofNat 20 * dotN (profile 2 2) (profile 2 2)) := by decide +kernel
theorem pin31 : profRangeRead 3 2 := by decide +kernel

/-! The counts. -/

theorem pin32 : (sites 3 2).all (fun s =>
    (rootPath 3 2 s).length ≤ (dirGap 3 + 1) * 2) = true := by decide +kernel
theorem pin33 : (rootPath 3 2 26).length = 6 := by decide +kernel
theorem pin34 : regionCapRead 2 2 ∧ coverRead 2 2 ∧ regionSumRead 2 2 := by decide +kernel
theorem pin35 : regionCapRead 3 2 ∧ coverRead 3 2 ∧ regionSumRead 3 2 := by decide +kernel

/-! The counts' displays at three directions and side two, the
theorems at the census. -/

theorem pin36 : linkCount 3 2 = 3 * (2 * 3 ^ 2) := linkCount_read 2 2
theorem pin37 : 2 * plaqCount 3 2 = 2 * 3 * (2 * 2 * 3 ^ 1) := plaqCount_read 1 2
theorem pin38 : 6 * cubeCount 3 2 = 1 * 2 * 3 * (2 * 2 * 2 * 3 ^ 0) := cubeCount_read 0 2

/-! The keys at three directions and side two: the link list and the
plaquette list read their members at the members' keys, the far
corner's step's link and the plane `(0, 2)` at the corner `4`. -/

theorem pin39 : ground.getAt (0, 0) (linkList 3 2) (linkKey 3 2 1 4) = (1, 4)
    ∧ linkKey 3 2 1 4 < linkCount 3 2 := by decide +kernel
theorem pin40 : ground.getAt (0, 0, 0) (plaqList 3 2) (plaqKey 3 2 0 2 4) = (0, 2, 4)
    ∧ plaqKey 3 2 0 2 4 < plaqCount 3 2 := by decide +kernel

/-! The row read through the theorem at `(3, 2)`'s fifth plaquette,
and at every plaquette of `(2, 2)` by kernel. -/

theorem pin41 : (dotP (getAt [] (incid 3 2) 5) (getAt [] (incid 3 2) 5)).oneValue
    (BPair.ofNat 4) := rowSq_read 3 2 5 (by decide +kernel)

/-! The mode read and the column read through the theorems at
`(3, 3)` and `(4, 2)`, the link list's key read at a place, and the
profile's column read at `(2, 3)`: the first-direction link at the
corner `(1, 1)` by kernel and the second-direction link at the corner
`(2, 1)` through the theorem, refused at one direction, the frame of
the theorem's direction binder. -/

theorem pin42 : modeRead 3 3 := modeRead_all 3 3
theorem pin43 : modeRead 4 2 := modeRead_all 4 2
theorem pin44 : colCountRead 3 3 := colCountRead_all 3 3
theorem pin45 : colCountRead 4 2 := colCountRead_all 4 2
theorem pin46 : linkKey 3 2 (ground.getAt (0, 0) (linkList 3 2) 7).1
    (ground.getAt (0, 0) (linkList 3 2) 7).2 = 7 :=
  linkKey_of_getAt 3 2 7 (by decide +kernel)
theorem pin47 : (ground.getAt BPair.unit (matVec (transposeM (incid 2 3)) (profile 2 3))
    (linkKey 2 3 0 5)).oneValue
    (BPair.ofCounts (wAt 3 (coordAt 3 0 5 + 1) * wAt 3 (coordAt 3 1 5 + 1))
      (wAt 3 (coordAt 3 0 5 + 1) * wAt 3 (coordAt 3 1 5))) := by decide +kernel
theorem pin48 : (ground.getAt BPair.unit (matVec (transposeM (incid 2 3)) (profile 2 3))
    (linkKey 2 3 1 6)).oneValue
    (BPair.ofCounts (wAt 3 (coordAt 3 0 6) * wAt 3 (coordAt 3 1 6 + 1))
      (wAt 3 (coordAt 3 0 6 + 1) * wAt 3 (coordAt 3 1 6 + 1))) :=
  profCol_read 2 3 1 6 (by decide) (by decide) (by decide) (by decide +kernel)
theorem pin49 : ¬ (ground.getAt BPair.unit (matVec (transposeM (incid 1 1)) (profile 1 1))
    (linkKey 1 1 0 0)).oneValue
    (if (0 : Nat) == 0 then
      BPair.ofCounts (wAt 1 (coordAt 1 0 0 + 1) * wAt 1 (coordAt 1 1 0 + 1))
        (wAt 1 (coordAt 1 0 0 + 1) * wAt 1 (coordAt 1 1 0))
    else if (0 : Nat) == 1 then
      BPair.ofCounts (wAt 1 (coordAt 1 0 0) * wAt 1 (coordAt 1 1 0 + 1))
        (wAt 1 (coordAt 1 0 0 + 1) * wAt 1 (coordAt 1 1 0 + 1))
    else BPair.unit) := by decide +kernel

/-! The Hodge identity: the Gram joined to the cubes' boundaries'
Gram reads the Hodge fold's matrix entrywise, by kernel at `(2, 1)`,
`(2, 2)`, `(2, 3)` and `(3, 1)` and through the theorem at `(3, 2)`,
`(3, 3)` and `(4, 2)`; the Poincaré read at the profile through the
theorem at `(3, 2)` and by kernel at `(2, 2)`, refused at a cube's
boundary at `(3, 1)`, a vector off the range, the frame of the range
binder; and one line of the Dirichlet telescope by kernel at the side
three. -/

theorem pin50 : hodgeRead 2 1 ∧ hodgeRead 2 2 := by decide +kernel
theorem pin51 : hodgeRead 2 3 := by decide +kernel
theorem pin52 : hodgeRead 3 1 := by decide +kernel
theorem pin53 : hodgeRead 3 2 := hodgeRead_all 3 2
theorem pin54 : hodgeRead 3 3 := by
  generalize 3 = d
  exact hodgeRead_all d d
theorem pin55 : hodgeRead 4 2 := by
  generalize 4 = d
  generalize 2 = L
  exact hodgeRead_all d L
theorem pin56 : BPair.ofNat 2 * dotN (profile 3 2) (profile 3 2)
    ≤ BPair.ofNat (2 * 2) * quadForm (gram 3 2) (profile 3 2) :=
  poincare_read 3 2 (profile 3 2) (profile_length 3 2) (profRangeRead_all 3 2)
theorem pin57 : BPair.ofNat 2 * dotN (profile 2 2) (profile 2 2)
    ≤ BPair.ofNat (2 * 2) * quadForm (gram 2 2) (profile 2 2) := by decide +kernel
theorem pin58 : ¬ (BPair.ofNat 2 * dotN (getAt [] (transposeM (cubeBd 3 1)) 0)
      (getAt [] (transposeM (cubeBd 3 1)) 0)
    ≤ BPair.ofNat (1 * 1) * quadForm (gram 3 1) (getAt [] (transposeM (cubeBd 3 1)) 0)) := by
  decide +kernel
theorem pin59 : bsum (fun x => if true && decide (x < 3)
      then BPair.ofNat (x + 1) * BPair.ofNat (x + 1) else BPair.unit) (List.range 4)
    ≤ BPair.ofNat 9 * bsum (fun x => lineDiff 3 (fun y => BPair.ofNat (y + 1)) true x
      * lineDiff 3 (fun y => BPair.ofNat (y + 1)) true x) (List.range 4) := by decide +kernel

/-! The kernel and the range: the descent's span reads through the
theorems at kernel vectors of `(3, 2)`, refused by kernel at a
plaquette's unit vector at `(3, 1)`, a vector off the kernel; the
kernel list's count at the kernel dimension through the theorem; and
the projector's four reads through the theorems at `(3, 3)` and
`(4, 1)`. -/

theorem pin60 : spanRel (plaqCount 3 2) (transposeM (cubeBd 3 2))
    (vecAdd (getAt [] (transposeM (cubeBd 3 2)) 0) (getAt [] (transposeM (cubeBd 3 2)) 5)) :=
  kernel_bd_span 3 2 _ (by decide +kernel) (by decide +kernel)
theorem pin61 : spanRel (plaqCount 3 2) (kerList 3 2)
    (vecAdd (vecScale (BPair.ofNat 2) (getAt [] (transposeM (cubeBd 3 2)) 2))
      (getAt [] (transposeM (cubeBd 3 2)) 7)) :=
  kerList_span 3 2 _ (by decide +kernel) (by decide +kernel)
theorem pin62 : ¬ spanRel (plaqCount 3 1) (transposeM (cubeBd 3 1)) (idRow (plaqCount 3 1) 0)
    ∧ ¬ spanRel (plaqCount 3 1) (kerList 3 1) (idRow (plaqCount 3 1) 0) := by decide +kernel
theorem pin63 : ¬ poly.unitTail (matVec (transposeM (incid 3 1)) (idRow (plaqCount 3 1) 0)) := by
  decide +kernel
theorem pin64 : (kerList 3 2).length = kerDim 3 2 := kerList_length 3 2
theorem pin65 : (kerList 3 3).length = kerDim 3 3 := kerList_length 3 3
theorem pin66 : (kerList 4 1).length = kerDim 4 1 := kerList_length 4 1
theorem pin67 : projSymRead 3 3 := by
  generalize 3 = d
  exact projSymRead_all d d
theorem pin68 : projKerRead 3 3 := by
  generalize 3 = d
  exact projKerRead_all d d
theorem pin69 : projGramRead 3 3 := by
  generalize 3 = d
  exact projGramRead_all d d
theorem pin70 : projIdemRead 3 3 := by
  generalize 3 = d
  exact projIdemRead_all d d
theorem pin71 : projSymRead 4 1 ∧ projKerRead 4 1 ∧ projGramRead 4 1 ∧ projIdemRead 4 1 := by
  generalize 4 = d
  generalize 1 = L
  exact ⟨projSymRead_all d L, projKerRead_all d L, projGramRead_all d L, projIdemRead_all d L⟩
theorem pin72 : projSymRead 3 1 ∧ projKerRead 3 1 ∧ projGramRead 3 1 ∧ projIdemRead 3 1 := by
  decide +kernel
theorem pin73 : ¬ spanRel (plaqCount 3 1) (kerList 3 1)
    (getAt [] (transposeM (cubeBd 3 1)) 0 ++ [BPair.unit]) := by decide +kernel

/-! The cubes' Poincaré read: the four-cells' boundaries' fold `N N₄ ≡ 0`
by kernel at `(4, 1)` and through the theorem at `(4, 2)`, the Hodge
identity at cubes by kernel at `(3, 1)` and `(4, 1)` and through the
theorem at `(3, 2)` and `(4, 2)`, the Poincaré read through the theorem
at a stated chain of `(3, 2)` and at two cubes' join of `(4, 1)`, refused
at a four-cell's boundary at `(4, 1)`, a chain off the cubes' range, the
frame of the range binder, with that chain refused at the range read,
and refused at the stated chain padded by one entry at `(3, 2)`, the
frame of the length binder; and one cube type's telescope at `(3, 2)` by
kernel. -/

theorem pin74 : bdRead4 4 1 := by decide +kernel
theorem pin75 : bdRead4 4 2 := by
  generalize 4 = d
  generalize 2 = L
  exact bdRead4_all d L
theorem pin76 : hodgeRead3 3 1 ∧ hodgeRead3 4 1 := by decide +kernel
theorem pin77 : hodgeRead3 3 2 := by
  generalize 3 = d
  generalize 2 = L
  exact hodgeRead3_all d L
theorem pin78 : hodgeRead3 4 2 := by
  generalize 4 = d
  generalize 2 = L
  exact hodgeRead3_all d L
private def chain32 : List BPair :=
  [BPair.ofNat 1, BPair.ofNat 3, (BPair.ofNat 2).swap, BPair.unit, BPair.ofNat 5, BPair.ofNat 1,
   (BPair.ofNat 4).swap, BPair.ofNat 2]
theorem pin79 : BPair.ofNat 3 * dotN chain32 chain32
    ≤ BPair.ofNat (2 * 2) * quadForm (cubesGram 3 2) chain32 :=
  cubePoincare_read 3 2 chain32 (by decide +kernel) (by decide +kernel)
theorem pin80 : BPair.ofNat 3 * dotN (vecAdd (idRow 8 0) (idRow 8 1)) (vecAdd (idRow 8 0) (idRow 8 1))
    ≤ BPair.ofNat (1 * 1) * quadForm (cubesGram 4 1) (vecAdd (idRow 8 0) (idRow 8 1)) :=
  cubePoincare_read 4 1 _ (by decide +kernel) (by decide +kernel)
theorem pin81 : ¬ (BPair.ofNat 3 * dotN (getAt [] (transposeM (fourCellBd 4 1)) 0)
      (getAt [] (transposeM (fourCellBd 4 1)) 0)
    ≤ BPair.ofNat (1 * 1) * quadForm (cubesGram 4 1) (getAt [] (transposeM (fourCellBd 4 1)) 0))
    ∧ ¬ poly.unitTail (matVec (transposeM (fourCellBd 4 1)) (getAt [] (transposeM (fourCellBd 4 1)) 0)) := by
  decide +kernel
private def chain32pad : List BPair := chain32 ++ [BPair.ofNat 100]
theorem pin82 : ¬ (BPair.ofNat 3 * dotN chain32pad chain32pad
      ≤ BPair.ofNat (2 * 2) * quadForm (cubesGram 3 2) chain32pad)
    ∧ poly.unitTail (matVec (transposeM (fourCellBd 3 2)) chain32pad) := by
  decide +kernel
theorem pin83 : bsum (fun s => if coordAt 2 0 s < 2 && coordAt 2 1 s < 2 && coordAt 2 2 s < 2
      then getAt BPair.unit chain32 (cubeKey 3 2 0 1 2 s) * getAt BPair.unit chain32 (cubeKey 3 2 0 1 2 s)
      else BPair.unit) (List.range ((2 + 1) ^ 3))
    ≤ BPair.ofNat (2 * 2) * diffFold3 3 2 0 1 2 1 chain32 := by decide +kernel

end cornerwindow
