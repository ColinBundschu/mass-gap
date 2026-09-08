import MassGap.Contactcell
import MassGap.Pencil
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

`freePMat_eval` is the carrier's cleared evaluation at a
root-coordinate point `[n : c]`: the ray `[c² : n²]`'s pencil
(`pencil.rayH`) at the level scaled by the clearing, the site datum
`c²(E + yG) − c²xG − n²M` (`def:pencil`'s root coordinate at
`lem:cellcount`'s cleared evaluation), and `freePMat_sym` its
symmetry at symmetric members, the level datum's entry and the
magnetic member's swap each one value at the exchanged keys
(`thm:pairpencil`'s symmetric site datum).
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

/-- The carrier's cleared evaluation at a root-coordinate point
`[n : c]` is the ray `[c² : n²]`'s pencil at the level scaled by the
clearing: `c²(E + yG − xG) − n²M` read as the site datum of the ray
pencil at the level `⟨c²x : c²y⟩` (`def:pencil`'s root coordinate at
`lem:cellcount`'s cleared evaluation). -/
theorem freePMat_eval (E M G : Mat) (x y : Pos) (o : Nat)
    (hE : sqAt E o) (hM : sqAt M o) (hG : sqAt G o) (n c : Pos) :
    matOneValue (cellcount.evalPC (freePMat E M G x y) (BPair.ofPos n) c 2)
      (siteDatum (matAdd (pencil.rayH E M (c * c) (n * n))
        (matScale (c * c * y) G)) (matScale (c * c * x) G)) := by
  have hMs : sqAt (matSwap M) o := sqAt_matSwap o M hM
  have h0 := cellcount.levelPMat_eval E (matSwap M) G x y [BPair.unit] o
    hE hMs hG (poly.unitTail_replicate 1) (BPair.ofPos n) c
  have hA : sqAt (siteDatum (matAdd E (matScale y G)) (matScale x G)) o :=
    sqAt_siteDatum o _ _
      (sqAt_matAdd o E _ hE (sqAt_matScale o y G hG))
      (sqAt_matScale o x G hG)
  have hc2 : (bpow (BPair.ofPos c) 2).oneValue (BPair.ofPos (c * c)) := by
    have e := ofPos_pow c 2
    rw [Pos.pow_two] at e
    exact BPair.oneValue_symm e
  have hn2 : (bpow (BPair.ofPos n) 2).oneValue (BPair.ofPos (n * n)) := by
    have e := ofPos_pow n 2
    rw [Pos.pow_two] at e
    exact BPair.oneValue_symm e
  have h1 : matOneValue
      (matScaleB (bpow (BPair.ofPos c) 2)
        (siteDatum (matAdd E (matScale y G)) (matScale x G)))
      (matScale (c * c) (siteDatum (matAdd E (matScale y G)) (matScale x G))) :=
    matOne_trans (matScaleB_congr hc2 _)
      (matOne_symm (matScale_scaleB (c * c) _))
  have h2 : matOneValue (matScaleB (bpow (BPair.ofPos n) 2) (matSwap M))
      (matSwap (matScale (n * n) M)) := by
    refine matOne_trans (matScaleB_congr hn2 _) ?_
    rw [← matScale_matSwap (n * n) M]
    exact matOne_symm (matScale_scaleB (n * n) (matSwap M))
  have h12 := matAdd_cong2 o _ _ _ _
    (rowsLen_scaleB _ o _ (rowsLen_of_sqAt hA))
    (rowsLen_scaleB _ o _ (rowsLen_of_sqAt hMs))
    (rowsLen_of_sqAt (sqAt_matScale o (c * c) _ hA))
    (rowsLen_of_sqAt (sqAt_matSwap o _ (sqAt_matScale o (n * n) M hM))) h1 h2
  refine matOne_trans h0 (matOne_trans h12 ?_)
  show matOneValue
    (matAdd (matScale (c * c) (matAdd (matAdd E (matScale y G))
      (matSwap (matScale x G)))) (matSwap (matScale (n * n) M)))
    (matAdd (matAdd (matAdd (matScale (c * c) E) (matSwap (matScale (n * n) M)))
      (matScale (c * c * y) G)) (matSwap (matScale (c * c * x) G)))
  rw [matScale_matAdd (c * c) (matAdd E (matScale y G)) (matSwap (matScale x G)),
    matScale_matAdd (c * c) E (matScale y G),
    matScale_matSwap (c * c) (matScale x G),
    matScale_matScale y (c * c) G, matScale_matScale x (c * c) G,
    matAdd_right_comm (matAdd (matScale (c * c) E) (matScale (c * c * y) G))
      (matSwap (matScale (c * c * x) G)) (matSwap (matScale (n * n) M)),
    matAdd_right_comm (matScale (c * c) E) (matScale (c * c * y) G)
      (matSwap (matScale (n * n) M))]
  exact matOne_refl _

/-- The carrier is symmetric at symmetric members: the level datum's
entry and the magnetic member's swap each read one value at the
exchanged keys (`thm:pairpencil`'s symmetric site datum at
`lem:freecell`'s carrier). -/
theorem freePMat_sym (E M G : Mat) (x y : Pos) (o : Nat)
    (hE : sqAt E o) (hM : sqAt M o) (hG : sqAt G o)
    (hEs : symmRead E) (hMs : symmRead M) (hGs : symmRead G) :
    split.pSymAt (freePMat E M G x y) o := by
  have hEl : E.length = o := sqAt_len hE
  have hMl : M.length = o := sqAt_len hM
  have hGl : G.length = o := sqAt_len hG
  have hGrow : ∀ i, i < o → ∀ w : Pos,
      (getAt ([] : List BPair) G i).length = o := fun i hi _ =>
    rowsLen_getAt _ i (rowsLen_of_sqAt hG) (by rw [hGl]; exact hi)
  have hScY : sqAt (matScale y G) o := sqAt_matScale o y G hG
  have hScX : sqAt (matScale x G) o := sqAt_matScale o x G hG
  have hAdd : sqAt (matAdd E (matScale y G)) o :=
    sqAt_matAdd o _ _ hE hScY
  have hsite : ∀ i j, i < o → j < o →
      getAt BPair.unit (getAt []
          (siteDatum (matAdd E (matScale y G)) (matScale x G)) i) j
        = (getAt BPair.unit (getAt [] E i) j
            + (getAt BPair.unit (getAt [] G i) j).scale y)
          + ((getAt BPair.unit (getAt [] G i) j).scale x).swap := by
    intro i j hi hj
    rw [siteDatum_entry _ _ o (rowsLen_of_sqAt hAdd) (rowsLen_of_sqAt hScX)
        i j (by rw [sqAt_len hAdd]; exact hi) (by rw [sqAt_len hScX]; exact hi) hj,
      entry_matAdd E (matScale y G) o (rowsLen_of_sqAt hE) (rowsLen_of_sqAt hScY)
        i j (by rw [hEl]; exact hi) (by rw [sqAt_len hScY]; exact hi) hj,
      matScale_entry y G i j (by rw [hGl]; exact hi)
        (by rw [hGrow i hi y]; exact hj),
      matScale_entry x G i j (by rw [hGl]; exact hi)
        (by rw [hGrow i hi x]; exact hj)]
  refine split.pSymAt_of _ o (fun i j hi hj => ?_)
  rw [freePMat_entry E M G x y o hE hM hG i j hi hj,
    freePMat_entry E M G x y o hE hM hG j i hj hi, hsite i j hi hj,
    hsite j i hj hi]
  exact ⟨BPair.add_congr
      (BPair.add_congr (symmRead_entry E hE hEs i j hi hj)
        (BPair.scale_congr y (symmRead_entry G hG hGs i j hi hj)))
      (ground.swap_congr (BPair.scale_congr x (symmRead_entry G hG hGs i j hi hj))),
    BPair.oneValue_refl _,
    ground.swap_congr (symmRead_entry M hM hMs i j hi hj), trivial⟩

end freecell
