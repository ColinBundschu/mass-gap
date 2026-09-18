import MassGap.Contactcell
/-!
The check module for `lem:contactcell`: the batteries re-read the
truncation pair by kernel `decide` at the `A`-series' `d = 2`
instantiation, the vacuum sector's one-plaquette chain under the
fundamental, self-dual there, the closure `{f}` at the self-dual
member alone.

The committed record.  The unit class ladder is
`𝟏, f = [1,0], θ = [2,0], [3,0], [4,0]` at the cleared Casimirs
`0, 3, 8, 15, 24` over `2d² = 8`, the dimension fold `d_L = 2`.  The
cutoffs are `K = 8` (the window `𝟏, f, θ`) and `K' = 24` (the window
grown by `[3,0], [4,0]`), the sector at either cutoff the whole
window, the head at `K` inside the window at `K'` the three labels
and the excluded block the two beyond.  One head label leaves the
cutoff, `θ` at the position two (`cutPos`), its one target `[3,0]`;
the coupling's row and column sums read one, so the border cap is one.
The window reads are decided at the joined window: the symmetry and
eigen-row reads at the closure's member, the dimensions positive,
the excluded block beyond the cutoff (beside the theorem route
`exclAt_beyond`, the tie `exclAt = ex2` the theorem's own binder),
distinct, and the row law at every closure member, head label and
excluded label.

The level `⟨1 : 1⟩` at the scale `σ = 1`, the clearing `8 = 1 · 2d²`, sits
below the seed floor `F = ⟨4·8 : 2⟩` at the gap sixteen, the join
`(1 + 2)·8 + 16 = 4·1·8 + 1·8` decided.  The three counts are
decided at the produced splits — the head's one, the chain's one and
the bordered pencil's one — and `truncPair` reads the sandwich
`1 ≤ 1 ≤ 1` through the theorem beside the decided anchors, with
`pinned` locating the chain's count at one.  The level binder's
refusal: at the level `⟨9 : 1⟩`, beyond the floor (no gap at
`(9 + 2)·8` against `4·8 + 8`), the chain's count is four against
the bordered pencil's three at the gap one, the conclusion parting.

`bord_schur` is read at an abstract one-auxiliary-row join, the aux
pivot nine positive and the join's count the deflation's, with the
aux pivot's positivity isolated at the forged diagonal `−8`, the
join's count two against the deflation's one.  The contact end's
reads: `endEval` at the record's electric diagonal and closure fold
reads the magnetic member's balance partner at the level, the
theorem route beside the decided display; `dualPMat` at a one-site
instance is the affine list `⟨-4 : 3σ⟩`, its evaluation at `σ = 2`
reading two and refusing at `σ = 1`; and at a level on the divisor
the boundary clause's endpoint split is positive semidefinite at the
kernel block.  `extRead` closes the extent at a two-key dual pencil
at the level four: the divisor `19 − 16σ`, its own squarefree part
at the Bézout `−16` and the cleared monic `y − 19` at `y = 16σ`, the
segment from the unit to `σ = 1` at a vacant root count and the
bracket `[1, 2]` holding the extent `σ₁` at the tie `16 σ₁ = 19`,
its two refusals the rootless bracket `[2, 3]` against the occupied
count and the straddle `[0, 2]` against the vacant one.
-/

namespace contactcell
open ground poly elim inertia certconstruct fusion

def u : BPair := BPair.unit

/-! The `d = 2` record: the interface, the fundamental, the head and
the excluded block at the cutoffs `8` and `24`, the level's data. -/

def F2 : Data (List Nat) := dataA 2
def f2 : List Nat := [1, 0]
def hd2 : List (List Nat) := [[0, 0], [1, 0], [2, 0]]
def ex2 : List (List Nat) := [[3, 0], [4, 0]]
def sn1 : Pos := posOfNat 1
def c8 : Pos := posOfNat 8
def x1 : Pos := posOfNat 1
def y1 : Pos := posOfNat 1
def x9 : Pos := posOfNat 9
def g16 : Pos := posOfNat 16
def g1 : Pos := posOfNat 1
def kB1 : Pos := posOfNat 1

/-! The window and the sector: the below-cutoff lists, the Casimirs,
the fundamental self-dual, the dimension fold, the sector at both
cutoffs, the head and the excluded block, the cutoff label with its
position and target, and the border cap. -/

theorem pin1 : F2.below 8 = [[1, 0], [2, 0]] := by decide +kernel
theorem pin2 : F2.below 24 = [[1, 0], [2, 0], [3, 0], [4, 0]] := by decide +kernel
theorem pin3 : (F2.c2N [1, 0], F2.c2N [2, 0], F2.c2N [3, 0], F2.c2N [4, 0], F2.c2D)
    = (3, 8, 15, 24, 8) := by decide +kernel
theorem pin4 : labels.dualL f2 = f2 := by decide +kernel
theorem pin5 : fpcap.dimFold F2 [f2] [] = 2 := by decide +kernel
theorem pin6 : sectorIdx F2 [f2] [] 8 = hd2 := by decide +kernel
theorem pin7 : sectorIdx F2 [f2] [] 24 = hd2 ++ ex2 := by decide +kernel
theorem pin8 : headAt F2 [f2] [] 8 24 = hd2 := by decide +kernel
theorem pin9 : exclAt F2 [f2] [] 8 24 = ex2 := by decide +kernel
theorem pin10 : cutPos F2 [f2] [] 8 hd2 = [2] := by decide +kernel
theorem pin11 : targets F2 [f2] [] 8 hd2 = [[3, 0]] := by decide +kernel
theorem pin12 : (rowMax F2 [f2] [] (targets F2 [f2] [] 8 hd2) hd2,
    colMax F2 [f2] [] hd2 (targets F2 [f2] [] 8 hd2), borderCap F2 [f2] [] 8 hd2)
    = (1, 1, 1) := by decide +kernel

/-! The window reads at the joined window, each decided. -/

theorem pin13 : fpcap.symAll F2 [f2] (hd2 ++ ex2) := by decide +kernel
theorem pin14 : fpcap.involAll F2 [] (hd2 ++ ex2) := by decide +kernel
theorem pin15 : fpcap.rowAll F2 [f2] (hd2 ++ ex2) := by decide +kernel
theorem pin16 : fpcap.dualRowAll F2 [] (hd2 ++ ex2) := by decide +kernel
theorem pin17 : fpcap.dimPos F2 (hd2 ++ ex2) := by decide +kernel
theorem pin18 : beyondAt F2 8 ex2 := by decide +kernel
theorem pin19 : beyondAt F2 8 (exclAt F2 [f2] [] 8 24) := exclAt_beyond F2 [f2] [] 8 24
theorem pin20 : ground.distinctList ex2 := by decide +kernel
theorem pin21 : rowLawAll F2 [f2] [] hd2 ex2 := by decide +kernel
theorem pin22 : (posVal x1 + fpcap.dimFold F2 [f2] []) * posVal c8 + posVal g16
    = 4 * posVal sn1 * 8 + posVal y1 * posVal c8 := by decide +kernel
theorem pin23 : borderCap F2 [f2] [] 8 hd2 ≤ posVal kB1 := by decide +kernel

/-! The three counts at the level `⟨1 : 1⟩`, each at its produced
split, and the sandwich through the theorem. -/

theorem pin24 : countAtPair (dualH F2 [f2] [] hd2 sn1 c8) (dualG c8 hd2.length) x1 y1 1
    (mkSplit hd2.length (levelSite F2 [f2] [] hd2 sn1 c8 x1 y1)) := by decide +kernel
theorem pin25 : countAtPair (dualH F2 [f2] [] (hd2 ++ ex2) sn1 c8) (dualG c8 (hd2 ++ ex2).length)
    x1 y1 1 (mkSplit (hd2.length + ex2.length) (levelSite F2 [f2] [] (hd2 ++ ex2) sn1 c8 x1 y1)) := by
  decide +kernel
theorem pin26 : splitRead (bordPencil F2 [f2] [] 8 hd2 sn1 c8 x1 y1 g16 kB1)
    (mkSplit ((cutPos F2 [f2] [] 8 hd2).length + hd2.length)
      (bordPencil F2 [f2] [] 8 hd2 sn1 c8 x1 y1 g16 kB1)) := by decide +kernel
theorem pin27 : revAt (mkSplit ((cutPos F2 [f2] [] 8 hd2).length + hd2.length)
    (bordPencil F2 [f2] [] 8 hd2 sn1 c8 x1 y1 g16 kB1)) = 1 := by decide +kernel

theorem pin28 : 1 ≤ 1 ∧ 1 ≤ revAt (mkSplit ((cutPos F2 [f2] [] 8 hd2).length + hd2.length)
    (bordPencil F2 [f2] [] 8 hd2 sn1 c8 x1 y1 g16 kB1)) :=
  truncPair F2 [f2] [] hd2 ex2 8 24 sn1 c8 x1 y1 g16 kB1 pin9 (by decide +kernel) pin13 pin14 pin15
    pin16 pin17 pin20 pin21 pin22 pin23 1 1 _ _ _ pin24 pin25 pin26

theorem pin29 : (1 : Nat) = 1 := pinned pin28 pin27.symm

/-! The level binder's refusal: at `⟨9 : 1⟩`, beyond the floor, the
chain's count four parts from the bordered pencil's three. -/

theorem pin30 : ¬ ((9 + 2) * 8 ≤ 4 * 1 * 8 + 1 * 8) := by decide +kernel
theorem pin31 : revAt (mkSplit (hd2.length + ex2.length)
    (levelSite F2 [f2] [] (hd2 ++ ex2) sn1 c8 x9 y1)) = 4 := by decide +kernel
theorem pin32 : revAt (mkSplit ((cutPos F2 [f2] [] 8 hd2).length + hd2.length)
    (bordPencil F2 [f2] [] 8 hd2 sn1 c8 x9 y1 g1 kB1)) = 3 := by decide +kernel
theorem pin33 : ¬ ((4 : Nat) ≤ 3) := by decide +kernel

/-! The `K₁` head's dual pencil at the level four and its divisor's
certificate: the squarefree part is the divisor itself at the
Bézout constant `−16`. -/

def eK1 : Mat := [[u, u], [u, ⟨5, 1⟩]]
def mK1 : Mat := [[u, ⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]]
def gK1 : Mat := idMat 2
def dDiv : Poly := split.pminor (dualPMat eK1 mK1 gK1 5 1)
def ctD : cellcount.DivCert :=
  ⟨[], [⟨20, 1⟩, ⟨1, 17⟩], [⟨1, 17⟩], [], [⟨2, 1⟩],
   [⟨20, 1⟩, ⟨1, 17⟩], [], [⟨2, 1⟩],
   1, 1, 1, 1, ⟨1, 17⟩, ⟨1, 17⟩⟩

/-! The one-auxiliary-row bordered join at abstract data: the aux
pivot `9`, the coupling one on the second head key, the head site
and the solve witness. -/

def dAux : Mat := [[⟨9, 1⟩]]
def bBord : Mat := [[u, ⟨2, 1⟩]]
def pSite : Mat := [[⟨1, 2⟩, ⟨1, 2⟩], [⟨1, 2⟩, ⟨3, 1⟩]]
def spJ : Split 3 :=
  ⟨⟨[[⟨2, 1⟩, u, ⟨2, 1⟩], [u, ⟨9, 1⟩, ⟨9, 1⟩], [u, u, ⟨1, 9⟩]], rfl⟩,
   ⟨[[⟨1, 65⟩, u, ⟨1, 9⟩], [u, ⟨1, 9⟩, ⟨1, 9⟩], [u, u, ⟨9, 1⟩]], rfl⟩,
   [.one ⟨9, 1⟩, .one ⟨1, 65⟩, .one ⟨185, 1⟩], 0, rfl⟩
def spSch : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨65, 1⟩], [u, ⟨1, 65⟩]], rfl⟩,
   ⟨[[⟨1, 65⟩, ⟨1, 65⟩], [u, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨1, 65⟩, .one ⟨753665, 1⟩], 0, rfl⟩

/-! `bord_schur`'s route at the one-auxiliary-row bordered join: the
aux pivot is positive at the level below the floor, so the join's
reversal count is the deflation's alone. -/

theorem pin34 : splitRead (inertia.blockJoin dAux bBord pSite) spJ := by decide +kernel
theorem pin35 : splitRead (deflMat dAux bBord pSite bBord) spSch := by decide +kernel
theorem pin36 : matOneValue (matMul dAux bBord)
    (matScaleB (minor dAux) bBord) := by decide +kernel

theorem pin37 : revAt spJ = revAt spSch :=
  bord_schur (k := 1) (m := 2) dAux bBord pSite bBord spJ
    (inertia.oneSplit [⟨9, 1⟩]) spSch
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The auxiliary pivot's refusal, isolating `bord_schur`'s
positive-pivot binder: at the forged auxiliary diagonal `-8` every
co-binder holds while the pivot's split reads one reversal, and
the conclusion parts — the join's count two against the
deflation's one. -/

def dAuxN : Mat := [[⟨1, 9⟩]]
def spJN : Split 3 :=
  ⟨⟨[[⟨2, 1⟩, u, ⟨2, 1⟩], [u, ⟨2, 1⟩, ⟨1, 9⟩], [u, u, ⟨9, 1⟩]],
     rfl⟩,
   ⟨[[⟨9, 1⟩, u, ⟨1, 2⟩], [u, ⟨9, 1⟩, ⟨9, 1⟩], [u, u, ⟨2, 1⟩]],
     rfl⟩,
   [.one ⟨1, 9⟩, .one ⟨1, 2⟩, .one ⟨201, 1⟩], 0, rfl⟩
def spSchN : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 2⟩], [u, ⟨2, 1⟩]], rfl⟩,
   ⟨[[⟨2, 1⟩, ⟨2, 1⟩], [u, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨1, 65⟩, .one ⟨201, 1⟩], 0, rfl⟩

theorem pin38 : splitRead (inertia.blockJoin dAuxN bBord pSite) spJN := by
  decide +kernel
theorem pin39 : splitRead (deflMat dAuxN bBord pSite bBord) spSchN := by
  decide +kernel
theorem pin40 : matOneValue (matMul dAuxN bBord)
    (matScaleB (minor dAuxN) bBord) := by decide +kernel
theorem pin41 : ¬ psdAt (inertia.oneSplit [⟨1, 9⟩]) := by decide +kernel
theorem pin42 : ¬ (revAt spJN = revAt spSchN) := by decide +kernel

/-! The contact end's own evaluation at the record: at the
coupling's unit point the dual cell's matrix is the magnetic
member's balance partner at the level datum, the theorem route
beside the decided display. -/

theorem pin43 : matOneValue
    (cellcount.evalPC (dualPMat (elecMat F2 hd2) (fpcap.closureMat F2 [f2] [] hd2) (idMat 3) 2 1)
      BPair.unit 1 1)
    (inertia.matScaleB (ground.bpow (BPair.ofPos 1) 1)
      (siteDatum
        (elim.matAdd (elim.matSwap (fpcap.closureMat F2 [f2] [] hd2)) (inertia.matScale 1 (idMat 3)))
        (inertia.matScale 2 (idMat 3)))) :=
  contactcell.endEval (elecMat F2 hd2) (fpcap.closureMat F2 [f2] [] hd2) (idMat 3) 2 1 1 3
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem pin44 : matOneValue
    (cellcount.evalPC (dualPMat (elecMat F2 hd2) (fpcap.closureMat F2 [f2] [] hd2) (idMat 3) 2 1)
      BPair.unit 1 1)
    (siteDatum (matAdd (matSwap (fpcap.closureMat F2 [f2] [] hd2)) (matScale 1 (idMat 3)))
      (matScale 2 (idMat 3))) := by decide +kernel

/-! `dualPMat` at a one-site instance: the affine list `⟨-4 : 3σ⟩`,
its cleared evaluation reading two at `σ = 2` and refusing there at
`σ = 1`. -/

theorem pin45 : split.pmatOneValue (dualPMat [[⟨4, 1⟩]] [[⟨3, 1⟩]] [[⟨2, 1⟩]] 3 1)
    [[[⟨1, 5⟩, ⟨4, 1⟩]]] := by decide +kernel
theorem pin46 : matOneValue
    (cellcount.evalPC (dualPMat [[⟨4, 1⟩]] [[⟨3, 1⟩]] [[⟨2, 1⟩]] 3 1)
      ⟨3, 1⟩ 1 1) [[⟨3, 1⟩]] := by decide +kernel
theorem pin47 : ¬ matOneValue
    (cellcount.evalPC (dualPMat [[⟨4, 1⟩]] [[⟨3, 1⟩]] [[⟨2, 1⟩]] 3 1)
      ⟨2, 1⟩ 1 1) [[⟨3, 1⟩]] := by decide +kernel

/-! At a level on the divisor the boundary clause extends the
positive-semidefinite cell into the closed endpoint: the one-site
carrier `3σ` reads its determinant at equal members at the contact
end, the endpoint's own split positive semidefinite at the kernel
block, and the adjacent cell's count the vacant read. -/

theorem pin48 : split.pmatOneValue
    (dualPMat [[⟨4, 1⟩]] [[⟨3, 1⟩]] [[⟨2, 1⟩]] 1 3)
    [[[BPair.unit, ⟨4, 1⟩]]] := by decide +kernel
theorem pin49 : (elim.minor
    (cellcount.evalPC (dualPMat [[⟨4, 1⟩]] [[⟨3, 1⟩]] [[⟨2, 1⟩]] 1 3)
      BPair.unit 1 1)).oneValue BPair.unit := by decide +kernel
theorem pin50 : psdAt (mkSplit 1
    (cellcount.evalPC (dualPMat [[⟨4, 1⟩]] [[⟨3, 1⟩]] [[⟨2, 1⟩]] 1 3)
      BPair.unit 1 1)) := by decide +kernel
theorem pin51 : psdAt (mkSplit 1
    (cellcount.evalPC (dualPMat [[⟨4, 1⟩]] [[⟨3, 1⟩]] [[⟨2, 1⟩]] 1 3)
      ⟨2, 1⟩ 1 1)) := by decide +kernel

/-! The extent certificate at the `K₁` head's dual pencil, level
four: the divisor `19 − 16σ` at its own squarefree part, the cleared
monic `y − 19` at `y = 16σ`, the vacant segment up to `σ = 1` and the
bracket `[1, 2]` holding the extent. -/

theorem pin52 : poly.oneValue dDiv [⟨20, 1⟩, ⟨1, 17⟩] := by decide +kernel
theorem pin53 : cellcount.divRead dDiv ctD := by decide +kernel
theorem pin54 : poly.oneValue (deckfactor.clearVarBT ctD.sq) [⟨1, 20⟩] := by
  decide +kernel
theorem pin55 : (deckfactor.clearAt ctD.sq ⟨2, 1⟩).oneValue ⟨17, 1⟩ := by decide +kernel
theorem pin56 : (deckfactor.clearAt ctD.sq ⟨3, 1⟩).oneValue ⟨33, 1⟩ := by decide +kernel
theorem pin57 : extRead dDiv ctD ⟨2, 1⟩ ⟨3, 1⟩ 1
    (inertia.oneSplit [⟨2, 1⟩]) (inertia.oneSplit [⟨58, 1⟩]) (inertia.oneSplit [⟨2, 1⟩]) (inertia.oneSplit [⟨1, 40⟩]) := by
  decide +kernel

/-! The bracket's two conjuncts refused: the rootless bracket
`[2, 3]` carries a vacant count where the extent read wants one, and
the straddle `[0, 2]` carries one where the leading segment wants
none. -/

theorem pin58 : hermitesign.segCountRead (deckfactor.clearVarBT ctD.sq)
    (deckfactor.clearAt ctD.sq ⟨3, 1⟩) (deckfactor.clearAt ctD.sq ⟨4, 1⟩)
    1 0 (inertia.oneSplit [⟨2, 1⟩]) (inertia.oneSplit [⟨378, 1⟩]) := by decide +kernel
theorem pin59 : ¬ hermitesign.segCountRead (deckfactor.clearVarBT ctD.sq)
    (deckfactor.clearAt ctD.sq ⟨3, 1⟩) (deckfactor.clearAt ctD.sq ⟨4, 1⟩)
    1 1 (inertia.oneSplit [⟨2, 1⟩]) (inertia.oneSplit [⟨378, 1⟩]) := by decide +kernel
theorem pin60 : hermitesign.segCountRead (deckfactor.clearVarBT ctD.sq)
    (deckfactor.clearAt ctD.sq BPair.unit)
    (deckfactor.clearAt ctD.sq ⟨3, 1⟩)
    1 1 (inertia.oneSplit [⟨2, 1⟩]) (inertia.oneSplit [⟨1, 248⟩]) := by decide +kernel
theorem pin61 : ¬ hermitesign.segCountRead (deckfactor.clearVarBT ctD.sq)
    (deckfactor.clearAt ctD.sq BPair.unit)
    (deckfactor.clearAt ctD.sq ⟨3, 1⟩)
    1 0 (inertia.oneSplit [⟨2, 1⟩]) (inertia.oneSplit [⟨1, 248⟩]) := by decide +kernel
theorem pin62 : ¬ extRead dDiv ctD ⟨3, 1⟩ ⟨4, 1⟩ 1
    (inertia.oneSplit [⟨2, 1⟩]) (inertia.oneSplit [⟨1, 248⟩]) (inertia.oneSplit [⟨2, 1⟩]) (inertia.oneSplit [⟨378, 1⟩]) := by
  decide +kernel

/-! The extent's bracket sits above the sum's unit, read through its
theorem at the certified bracket. -/

theorem pin63 : BPair.unit < ⟨2, 1⟩ :=
  extRead_pos dDiv ctD ⟨2, 1⟩ ⟨3, 1⟩ 1
    (inertia.oneSplit [⟨2, 1⟩]) (inertia.oneSplit [⟨58, 1⟩])
    (inertia.oneSplit [⟨2, 1⟩]) (inertia.oneSplit [⟨1, 40⟩]) pin57

/-! The bracket's foot binder: at the foot `−1` the segment read from
the sum's unit refuses, the two cleared points out of order at the
Hermite pairings' own splits. -/

theorem pin64 : ¬ extRead dDiv ctD ⟨1, 2⟩ ⟨3, 1⟩ 1
    (inertia.mkSplit 1 (hermitesign.hermite (deckfactor.clearVarBT ctD.sq) poly.one))
    (inertia.mkSplit 1 (hermitesign.pencilB (deckfactor.clearVarBT ctD.sq) poly.one
      (deckfactor.clearAt ctD.sq BPair.unit) (deckfactor.clearAt ctD.sq ⟨1, 2⟩) 1))
    (inertia.mkSplit 1 (hermitesign.hermite (deckfactor.clearVarBT ctD.sq) poly.one))
    (inertia.mkSplit 1 (hermitesign.pencilB (deckfactor.clearVarBT ctD.sq) poly.one
      (deckfactor.clearAt ctD.sq ⟨1, 2⟩) (deckfactor.clearAt ctD.sq ⟨3, 1⟩) 1)) := by
  decide +kernel

end contactcell
