import MassGapChecks.Contactcell
import MassGap.Divisorid
import MassGap.Freecell
/-!
The check module for `lem:freecell`: the batteries re-read the free
cell's carrier and the free end's own evaluation by kernel `decide`
at the `d = 2` `X`-sector record of `lem:contactcell` — the electric
diagonal `4ĉ₂ = (0, 4, 12)` at the same clearing, the walk matrix as
the magnetic member, and the unit gram.

`freePMat` is the affine-in-`τ²` list: the level datum at the
constant key, the sum's unit at the middle key and the magnetic
member's balance partner at the `τ²` key.  At the level one it
displays entrywise as `⟨-1 : 0 : 0⟩`, `⟨0 : 0 : -1⟩`, `⟨3 : 0 : -1⟩`,
`⟨11 : 0 : -1⟩` over the record's index pairs, and at `τ² = 1` it
reads the near-contact head's own site — the two cells' one
carrier.

`endEval`'s route at the record: at the coupling's unit point the
cleared evaluation keeps the constant key alone at the clearing's
stated power, so the cell's matrix is the electric level datum
`diag(-λ, 4-λ, 12-λ)` rescaled there, the free end's diagonal read.

The free end is interior to its cell.  The content list is the
electric diagonal's own `(0, 4, 12)`.  At the level one, off that
list, the cell's determinant reads `−33`, unequal members, so the
free end sits inside its cell and its counts are the cell's direct
reads.  At the levels nought and four, on the list, the determinant
reads equal members and the boundary clause takes over: at nought
the evaluated cell is positive semidefinite with its kernel block
trailing, the closed endpoint's own split, and at four the closed
endpoint carries one reversal, the cell's count there.
`thm:divisorid`(iii)'s transport reads at the record: covers for
the pencil's two level carriers over the bracket `[0, 1/4]` in
`τ²` from the free end — the level `+1` carrier's certificate two
pieces chained at `1/8` — carry the pair (psd, count one) across
the bracket, decided and through `divisorid.groundMult`.

The extent certificate at a one-site free record — electric four,
magnetic one, level one — the divisor `3 − τ²` at its own squarefree
part, the Bézout `2(3 − τ²) − τ(−2τ) = 6`, and the cleared monic
`y² − 3` at the unit magnitude: the segment from the unit to `τ = 1`
carries a vacant root count and the bracket `[1, 2]` carries one,
the extent `τ₁` at the tie `τ₁² = 3` located there.  Its two refusals: the rootless
bracket `[2, 3]` refusing the occupied count, and the straddle
`[0, 2]` refusing the vacant one.
-/
set_option maxHeartbeats 4000000

open ground poly elim inertia certconstruct contactcell freecell

namespace freecell

/-! The permuted three-order certificates the free record's diagonal
cells clear at: the kernel key sent to the trailing block. -/

def spLead (a b : BPair) : Split 3 :=
  ⟨⟨[[u, u, ⟨2, 1⟩], [⟨2, 1⟩, u, u], [u, ⟨2, 1⟩, u]], rfl⟩,
   ⟨[[u, ⟨2, 1⟩, u], [u, u, ⟨2, 1⟩], [⟨2, 1⟩, u, u]], rfl⟩,
   [.one a, .one b], 1, rfl⟩
def spMid (a b : BPair) : Split 3 :=
  ⟨⟨[[⟨2, 1⟩, u, u], [u, u, ⟨2, 1⟩], [u, ⟨2, 1⟩, u]], rfl⟩,
   ⟨[[⟨1, 2⟩, u, u], [u, u, ⟨1, 2⟩], [u, ⟨1, 2⟩, u]], rfl⟩,
   [.one a, .one b], 1, rfl⟩

/-! The one-site free record and its divisor's certificate: the
squarefree part is the divisor itself at the Bézout constant six. -/

def eOne : Mat := [[⟨5, 1⟩]]
def mOne : Mat := [[⟨2, 1⟩]]
def gOne : Mat := [[⟨2, 1⟩]]
def dFree : Poly := split.pminor (freePMat eOne mOne gOne 2 1)
def ctF : cellcount.DivCert :=
  ⟨[], [⟨4, 1⟩, u, ⟨1, 2⟩], [u, ⟨1, 3⟩], [⟨3, 1⟩], [u, ⟨1, 2⟩],
   [⟨4, 1⟩, u, ⟨1, 2⟩], [⟨3, 1⟩], [u, ⟨1, 2⟩],
   1, 1, 1, 1, ⟨7, 1⟩, ⟨7, 1⟩⟩

def spHerm : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, u], [u, ⟨3, 1⟩]], rfl⟩, ⟨[[⟨3, 1⟩, u], [u, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨3, 1⟩, .one ⟨25, 1⟩], 0, rfl⟩
def spBr (t a b : BPair) : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, t], [u, a]], rfl⟩, ⟨[[a, t.swap], [u, ⟨2, 1⟩]], rfl⟩,
   [.one a, .one b], 0, rfl⟩

end freecell

/-! The free cell's carrier at the record, level one: the level
datum at the constant key, the sum's unit at the middle key and the
magnetic member's balance partner at the `τ²` key. -/

example : split.pmatOneValue (freePMat eWalk mWalk gK2 2 1)
    [[[⟨1, 2⟩, u, u], [u, u, ⟨1, 2⟩], [u, u, u]],
     [[u, u, ⟨1, 2⟩], [⟨4, 1⟩, u, ⟨1, 2⟩], [u, u, ⟨1, 2⟩]],
     [[u, u, u], [u, u, ⟨1, 2⟩], [⟨12, 1⟩, u, ⟨1, 2⟩]]] := by decide +kernel

/-! The carrier's entry read at the record, decided and through
`freePMat_entry`: the level datum's entry at the constant key, the
unit middle, and the magnetic member's balance partner at the top
key.  Each shape binder refuses at its own ragged member — the
componentwise walk truncates at the shorter operand — with the
beyond-order row and column keys refused at the vacant read, and
the shape read decided, through `pShapeAt_freePMat`, and refused at
the ragged magnetic member. -/

private def eWr : Mat := [[u, u], [u, ⟨5, 1⟩, u], [u, u, ⟨13, 1⟩]]
private def mWr : Mat :=
  [[u, ⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩], [u, ⟨2, 1⟩, ⟨2, 1⟩]]
private def gWr : Mat := [[⟨2, 1⟩], [u, ⟨2, 1⟩, u], [u, u, ⟨2, 1⟩]]

example : getAt [] (getAt [] (freePMat eWalk mWalk gK2 2 1) 1) 2
    = getAt u (getAt [] (siteDatum (matAdd eWalk (matScale 1 gK2))
        (matScale 2 gK2)) 1) 2
      :: ([u] ++ [(getAt u (getAt [] mWalk 1) 2).swap]) := by
  decide +kernel
example : getAt [] (getAt [] (freePMat eWalk mWalk gK2 2 1) 1) 2
    = getAt u (getAt [] (siteDatum (matAdd eWalk (matScale 1 gK2))
        (matScale 2 gK2)) 1) 2
      :: ([u] ++ [(getAt u (getAt [] mWalk 1) 2).swap]) :=
  freecell.freePMat_entry eWalk mWalk gK2 2 1 3 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 1 2 (by decide +kernel)
    (by decide +kernel)
example : ¬ (getAt [] (getAt [] (freePMat eWr mWalk gK2 2 1) 0) 2
    = getAt u (getAt [] (siteDatum (matAdd eWr (matScale 1 gK2))
        (matScale 2 gK2)) 0) 2
      :: ([u] ++ [(getAt u (getAt [] mWalk 0) 2).swap])) := by
  decide +kernel
example : ¬ (getAt [] (getAt [] (freePMat eWalk mWr gK2 2 1) 0) 2
    = getAt u (getAt [] (siteDatum (matAdd eWalk (matScale 1 gK2))
        (matScale 2 gK2)) 0) 2
      :: ([u] ++ [(getAt u (getAt [] mWr 0) 2).swap])) := by
  decide +kernel
example : ¬ (getAt [] (getAt [] (freePMat eWalk mWalk gWr 2 1) 0) 2
    = getAt u (getAt [] (siteDatum (matAdd eWalk (matScale 1 gWr))
        (matScale 2 gWr)) 0) 2
      :: ([u] ++ [(getAt u (getAt [] mWalk 0) 2).swap])) := by
  decide +kernel
example : ¬ (getAt [] (getAt [] (freePMat eWalk mWalk gK2 2 1) 3) 1
    = getAt u (getAt [] (siteDatum (matAdd eWalk (matScale 1 gK2))
        (matScale 2 gK2)) 3) 1
      :: ([u] ++ [(getAt u (getAt [] mWalk 3) 1).swap])) := by
  decide +kernel
example : ¬ (getAt [] (getAt [] (freePMat eWalk mWalk gK2 2 1) 1) 3
    = getAt u (getAt [] (siteDatum (matAdd eWalk (matScale 1 gK2))
        (matScale 2 gK2)) 1) 3
      :: ([u] ++ [(getAt u (getAt [] mWalk 1) 3).swap])) := by
  decide +kernel

example : cellcount.pShapeAt (freePMat eWalk mWalk gK2 2 1) 3 2 := by
  decide +kernel
example : cellcount.pShapeAt (freePMat eWalk mWalk gK2 2 1) 3 2 :=
  freecell.pShapeAt_freePMat eWalk mWalk gK2 2 1 3 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
example : ¬ cellcount.pShapeAt (freePMat eWalk mWr gK2 2 1) 3 2 := by
  decide +kernel

/-! `endEval`'s route at the record: at the coupling's unit point the
cell's matrix is the electric level datum at the clearing's
rescaling, the free end's diagonal read. -/

example : matOneValue
    (cellcount.evalPC (freePMat eWalk mWalk gK2 2 1) BPair.unit 1 2)
    (matScaleB (ground.bpow (BPair.ofPos 1) 2)
      (siteDatum (matAdd eWalk (matScale 1 gK2)) (matScale 2 gK2))) :=
  freecell.endEval eWalk mWalk gK2 2 1 1 3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : matOneValue
    (cellcount.evalPC (freePMat eWalk mWalk gK2 2 1) BPair.unit 1 2)
    [[⟨1, 2⟩, u, u], [u, ⟨4, 1⟩, u], [u, u, ⟨12, 1⟩]] := by decide +kernel

/-! The order binders isolated: at a magnetic member truncated to
two rows the `zipWith` carrier shortens and the length-strict read
parts — the stated order is what keeps the carrier whole. -/

example : ¬ matOneValue
    (cellcount.evalPC
      (freePMat eWalk [[u, ⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]] gK2 2 1)
      BPair.unit 1 2)
    (matScaleB (ground.bpow (BPair.ofPos 1) 2)
      (siteDatum (matAdd eWalk (matScale 1 gK2))
        (matScale 2 gK2))) := by decide +kernel

/-! The two cells' one carrier: at `τ² = 1` the free cell reads the
near-contact head's own site at the same level. -/

example : matOneValue
    (cellcount.evalPC (freePMat eWalk mWalk gK2 2 1) ⟨2, 1⟩ 1 2)
    (siteDatum (matAdd hK2 (matScale 1 gK2)) (matScale 2 gK2)) := by
  decide +kernel

/-! The free end is interior to its cell: at the level one, off the
content list `(0, 4, 12)`, the cell's determinant reads unequal
members. -/

example : (elim.minor
    (cellcount.evalPC (freePMat eWalk mWalk gK2 2 1) BPair.unit 1 2)).offUnit
  := by decide +kernel
example : (elim.minor
    (cellcount.evalPC (freePMat eWalk mWalk gK2 6 1) BPair.unit 1 2)).offUnit
  := by decide +kernel

/-! At the levels on the content list the determinant reads equal
members and the boundary clause takes over: at nought the evaluated
cell is positive semidefinite with its kernel block trailing, and at
four the closed endpoint carries one reversal. -/

example : (elim.minor
    (cellcount.evalPC (freePMat eWalk mWalk gK2 1 1) BPair.unit 1 2)).oneValue
    BPair.unit := by decide +kernel
example : splitRead
    (cellcount.evalPC (freePMat eWalk mWalk gK2 1 1) BPair.unit 1 2)
    (spLead ⟨5, 1⟩ ⟨13, 1⟩) := by decide +kernel
example : psdAt (spLead ⟨5, 1⟩ ⟨13, 1⟩) := by decide +kernel

example : (elim.minor
    (cellcount.evalPC (freePMat eWalk mWalk gK2 5 1) BPair.unit 1 2)).oneValue
    BPair.unit := by decide +kernel
example : splitRead
    (cellcount.evalPC (freePMat eWalk mWalk gK2 5 1) BPair.unit 1 2)
    (spMid ⟨1, 5⟩ ⟨9, 1⟩) := by decide +kernel
example : revAt (spMid ⟨1, 5⟩ ⟨9, 1⟩) = 1 := by decide +kernel
example : ¬ psdAt (spMid ⟨1, 5⟩ ⟨9, 1⟩) := by decide +kernel

/-! The extent certificate at the one-site free record: the divisor
`3 − τ²` at its own squarefree part, the cleared monic `y² − 3` at
the unit magnitude, the vacant segment up to `τ = 1` and the bracket
`[1, 2]` holding the extent. -/

example : split.pmatOneValue (freePMat eOne mOne gOne 2 1)
    [[[⟨4, 1⟩, u, ⟨1, 2⟩]]] := by decide +kernel
example : poly.oneValue dFree [⟨4, 1⟩, u, ⟨1, 2⟩] := by decide +kernel
example : cellcount.divRead dFree ctF := by decide +kernel
example : poly.oneValue (deckfactor.clearVarBT ctF.sq) [⟨1, 4⟩, u] := by
  decide +kernel
example : (deckfactor.clearAt ctF.sq ⟨2, 1⟩).oneValue ⟨2, 1⟩ := by decide +kernel
example : extRead dFree ctF ⟨2, 1⟩ ⟨3, 1⟩ 1
    spHerm (spBr ⟨7, 1⟩ ⟨7, 1⟩ ⟨433, 1⟩)
    spHerm (spBr ⟨19, 1⟩ ⟨11, 1⟩ ⟨1, 241⟩) := by decide +kernel

/-! The bracket's two conjuncts refused: the rootless bracket
`[2, 3]` carries a vacant count where the extent read wants one, and
the straddle `[0, 2]` carries one where the leading segment wants
none. -/

example : hermitesign.segCountRead (deckfactor.clearVarBT ctF.sq)
    (deckfactor.clearAt ctF.sq ⟨3, 1⟩) (deckfactor.clearAt ctF.sq ⟨4, 1⟩)
    1 0 spHerm (spBr ⟨31, 1⟩ ⟨19, 1⟩ ⟨1297, 1⟩) := by decide +kernel
example : ¬ hermitesign.segCountRead (deckfactor.clearVarBT ctF.sq)
    (deckfactor.clearAt ctF.sq ⟨3, 1⟩) (deckfactor.clearAt ctF.sq ⟨4, 1⟩)
    1 1 spHerm (spBr ⟨31, 1⟩ ⟨19, 1⟩ ⟨1297, 1⟩) := by decide +kernel
example : hermitesign.segCountRead (deckfactor.clearVarBT ctF.sq)
    (deckfactor.clearAt ctF.sq BPair.unit)
    (deckfactor.clearAt ctF.sq ⟨3, 1⟩)
    1 1 spHerm (spBr ⟨13, 1⟩ ⟨7, 1⟩ ⟨1, 217⟩) := by decide +kernel
example : ¬ hermitesign.segCountRead (deckfactor.clearVarBT ctF.sq)
    (deckfactor.clearAt ctF.sq BPair.unit)
    (deckfactor.clearAt ctF.sq ⟨3, 1⟩)
    1 0 spHerm (spBr ⟨13, 1⟩ ⟨7, 1⟩ ⟨1, 217⟩) := by decide +kernel
example : ¬ extRead dFree ctF ⟨3, 1⟩ ⟨4, 1⟩ 1
    spHerm (spBr ⟨13, 1⟩ ⟨7, 1⟩ ⟨1, 217⟩)
    spHerm (spBr ⟨31, 1⟩ ⟨19, 1⟩ ⟨1297, 1⟩) := by decide +kernel

/-! `thm:divisorid`(iii)'s free-end read at the record: the one
pencil's two level carriers — the level `-1` cell positive
semidefinite and the level `+1` cell at one reversal — are covered
from the free end to `τ² = 1/4`, the first by three chained
order-one designations in the deflations and the second by two
pieces chained at `τ² = 1/8` with the same designations per piece,
so the pair (psd, count one) read at the free end is every bracket
point's, decided and through the cell theorem. -/

private def sFl : split.PMat := freecell.freePMat eWalk mWalk gK2 1 2
private def sFh : split.PMat := freecell.freePMat eWalk mWalk gK2 2 1
private def loF : CPair := ⟨⟨1, 1⟩, 1⟩
private def hi8 : CPair := ⟨⟨2, 1⟩, 8⟩
private def hi4 : CPair := ⟨⟨2, 1⟩, 4⟩
private def cvFl : cellcount.Cover :=
  cellcount.diagNest hi4 ⟨2, 1⟩ ⟨2, 1⟩ 3
private def cvFh : cellcount.Cover :=
  cellcount.Cover.one hi8 0 false ⟨2, 1⟩ ⟨2, 1⟩
    (cellcount.diagNest hi8 ⟨2, 1⟩ ⟨2, 1⟩ 2)
    (cellcount.diagCover hi4 ⟨2, 1⟩ ⟨2, 1⟩ 2)

private theorem covFlr : cellcount.coverRead sFl 3 2 loF hi4 cvFl := by
  decide +kernel
private theorem covFhr : cellcount.coverRead sFh 3 2 loF hi4 cvFh := by
  decide +kernel

example :
    inertia.psdAt (inertia.mkSplit 3 (cellcount.evalPC sFl ⟨2, 1⟩ 4 2))
    ∧ inertia.revAt (inertia.mkSplit 3 (cellcount.evalPC sFh ⟨2, 1⟩ 4 2))
      = 1 := by decide +kernel

example :
    inertia.psdAt (inertia.mkSplit 3 (cellcount.evalPC sFl ⟨2, 1⟩ 4 2))
    ∧ inertia.revAt (inertia.mkSplit 3 (cellcount.evalPC sFh ⟨2, 1⟩ 4 2))
      = 1 :=
  divisorid.groundMult eWalk (elim.matSwap mWalk) gK2 [BPair.unit]
    1 2 2 1 (by decide +kernel) loF hi4 cvFl cvFh covFlr covFhr
    ⟨1, 1⟩ 1 ⟨2, 1⟩ 4 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 1
    (inertia.mkSplit 3 (cellcount.evalPC sFl ⟨1, 1⟩ 1 2))
    (inertia.mkSplit 3 (cellcount.evalPC sFh ⟨1, 1⟩ 1 2))
    (by decide +kernel) (by decide +kernel)
    (inertia.mkSplit 3 (cellcount.evalPC sFl ⟨2, 1⟩ 4 2))
    (inertia.mkSplit 3 (cellcount.evalPC sFh ⟨2, 1⟩ 4 2))
    (inertia.mkSplit_read 3 _ (by decide +kernel) (by decide +kernel))
    (inertia.mkSplit_read 3 _ (by decide +kernel) (by decide +kernel))
