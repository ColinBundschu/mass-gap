import MassGap.Contactcell
/-!
`lem:freecell` — the free cell's carrier and the free end's own
evaluation.

The pencil at the `α = 1` representative is the pair `(E : τ²M)`'s
site datum `H([1 : τ²])`, affine in `τ²`: `freePMat` is that
carrier, the level datum at the constant key and the magnetic
member's balance partner at the `τ²` key, with the middle key at the
sum's unit — the contact cell's construction at this end
(`lem:contactcell`; `lem:cellcount`'s cell function over
`(t, τ, r)`).

`endEval` is the free end's own read: at the coupling's unit point
the cleared evaluation (`cellcount.evalPC`) keeps the constant key
alone, rescaled by the clearing's stated power, so the cell's matrix
there is the electric level datum at that positive rescaling — the
pencil is its electric member `E`, diagonal at the free reads, one
diagonal computation at every window (`lem:freeend`).
-/

namespace freecell
open ground poly elim inertia

/-- `lem:freecell`'s carrier: the free cell's site datum at the
`α = 1` representative, the level datum at the constant key and the
magnetic member's balance partner at the `τ²` key, the middle key at
the sum's unit — the affine-in-`τ²` list. -/
def freePMat (E M G : Mat) (x y : Pos) : split.PMat :=
  cellcount.levelPMat E (elim.matSwap M) G x y [BPair.unit]

/-- The carrier's display read entrywise: an entry inside the order
is the one polynomial list — the level datum's entry at the constant
key (`def:pencil`'s join at `thm:certconstruct`'s cross-added
level), the sum's unit at the middle key, and the magnetic member's
balance partner at the `τ²` key. -/
theorem freePMat_entry (E M G : Mat) (x y : Pos) (o : Nat)
    (hE : sqAt E o) (hM : sqAt M o) (hG : sqAt G o) (i j : Nat)
    (hi : i < o) (hj : j < o) :
    ground.getAt [] (ground.getAt [] (freePMat E M G x y) i) j
      = ground.getAt BPair.unit (ground.getAt []
          (inertia.siteDatum (elim.matAdd E (inertia.matScale y G))
            (inertia.matScale x G)) i) j
        :: ([BPair.unit] ++ [(ground.getAt BPair.unit
            (ground.getAt [] M i) j).swap]) := by
  show ground.getAt [] (ground.getAt [] (cellcount.levelPMat E
      (elim.matSwap M) G x y [BPair.unit]) i) j = _
  rw [cellcount.levelPMat_entry E (elim.matSwap M) G x y [BPair.unit]
      o hE (elim.sqAt_matSwap o M hM) hG i j hi hj,
    elim.entry_matSwap M o (elim.rowsLen_of_sqAt hM) i j
      (by rw [elim.sqAt_len hM]; exact hi) hj]

/-- The carrier's shape at the stated order, the affine list's own
clearing degree. -/
theorem pShapeAt_freePMat (E M G : Mat) (x y : Pos) (o : Nat)
    (hE : sqAt E o) (hM : sqAt M o) (hG : sqAt G o) :
    cellcount.pShapeAt (freePMat E M G x y) o 2 :=
  cellcount.pShapeAt_levelPMat E (elim.matSwap M) G x y [BPair.unit]
    o hE (elim.sqAt_matSwap o M hM) hG

theorem endEval (E M G : Mat) (x y c : Pos) (o : Nat)
    (hE : sqAt E o) (hM : sqAt M o) (hG : sqAt G o) :
    elim.matOneValue
      (cellcount.evalPC (freePMat E M G x y) BPair.unit c 2)
      (inertia.matScaleB (ground.bpow (BPair.ofPos c) 2)
        (inertia.siteDatum (elim.matAdd E (inertia.matScale y G))
          (inertia.matScale x G))) :=
  cellcount.levelPMat_endEval E (elim.matSwap M) G x y c
    [BPair.unit] o hE (elim.sqAt_matSwap o M hM) hG

end freecell
