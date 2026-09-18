import MassGap.Gentable
/-!
The check module for `con:gentable`: the batteries re-read the
derived reads at the first table's instances — the `A`-series'
tables at the matrix units' data (`con:gentable`'s closing read),
the residue the declared scalar (`con:places`) — by kernel
`decide`: the derived residue with its naming identity, the highest
root's form read, the form's simple symmetry, and the root fold's
coroot reads.
-/

namespace gentable
set_option maxHeartbeats 4000000

open ground

/-! The derived residue at the declared scalar, with its naming
identity, the first table's instances (`con:gentable`'s closing
read at the matrix units). -/

theorem pin1 : residue (tableA 1) = 1 := by decide +kernel
theorem pin2 : residue (tableA 2) = 2 := by decide +kernel
theorem pin3 : residue (tableA 4) = 4 := by decide +kernel
theorem pin4 : residueRead (tableA 1) := by decide +kernel
theorem pin5 : residueRead (tableA 4) := by decide +kernel

/-! The positive count `r (r + 1) / 2` at instances, the interval
folds. -/

theorem pin6 : posCount (tableA 1) = 1 := by decide +kernel
theorem pin7 : posCount (tableA 4) = 10 := by decide +kernel

/-! The highest root's form read, the form's simple symmetry, and
the root fold's coroot reads at the first table. -/

theorem pin8 : thetaNormRead (tableA 1) := by decide +kernel
theorem pin9 : thetaNormRead (tableA 4) := by decide +kernel
theorem pin10 : symRead (tableA 4) := by decide +kernel
theorem pin11 : shapeRead (tableA 1) := by decide +kernel
theorem pin12 : shapeRead (tableA 4) := by decide +kernel
theorem pin13 : occRead (tableA 1) := by decide +kernel
theorem pin14 : occRead (tableA 4) := by decide +kernel
theorem pin15 : rhoRead (tableA 1) := by decide +kernel
theorem pin16 : rhoRead (tableA 2) := by decide +kernel
theorem pin17 : rhoRead (tableA 4) := by decide +kernel

/-! The one-hot fold's coroot read at its own conclusion: the fold
occupied at one simple key alone reads that row's Cartan entry, at
the diagonal key and off it. -/

theorem pin18 : BPair.oneValue
    (corootAt (tableA 4) ((List.range (tableA 4).rank).map
      (fun k => if k == 1 then 1 else 0)) 2)
    (getAt BPair.unit (getAt [] (tableA 4).cartan 1) 2) :=
  corootAt_oneHot (tableA 4) 1 2 (by decide +kernel)

theorem pin19 : BPair.oneValue
    (corootAt (tableA 4) ((List.range (tableA 4).rank).map
      (fun k => if k == 1 then 1 else 0)) 1)
    (getAt BPair.unit (getAt [] (tableA 4).cartan 1) 1) :=
  corootAt_oneHot (tableA 4) 1 1 (by decide +kernel)

theorem pin20 : BPair.oneValue
    (corootAt (tableA 4) ((List.range (tableA 4).rank).map
      (fun k => if k == 1 then 1 else 0)) 1) (BPair.ofNat 2) := by
  decide +kernel
theorem pin21 : BPair.oneValue
    (corootAt (tableA 4) ((List.range (tableA 4).rank).map
      (fun k => if k == 1 then 1 else 0)) 2)
    ((BPair.ofNat 1).swap) := by decide +kernel

/-! The `A` occupancy reads' binders, isolated: at the vacant rank
the θ-coroot's first-key read is the unit and the residue is
vacant, so `corootA_head_off`'s and `residue_tableA_pos`'s rank
binders bind. -/

theorem pin22 : (corootAt (tableA 0) (tableA 0).thetaFold 0).oneValue
    BPair.unit := by decide +kernel
theorem pin23 : ¬ 0 < residue (tableA 0) := by decide +kernel

/-! The residue's value read, the theorem route beside the kernel's
own at a committed rank and at a fresh one. -/

theorem pin24 : residue (tableA 4) = 4 := residue_tableA 4
theorem pin25 : residue (tableA 7) = 7 := residue_tableA 7
theorem pin26 : residue (tableA 7) = 7 := by decide +kernel

end gentable
