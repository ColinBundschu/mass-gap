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
