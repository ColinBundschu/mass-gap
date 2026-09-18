import MassGap.Deckfactor
import MassGap.Truncation
import MassGap.Cellcount
import MassGap.Fusion
import MassGap.Depthchain
/-!
`lem:contactcell` — the near-contact cell's truncation pair on the
vacuum sector's one-plaquette chain, and the contact end's reads.

The chain is the unit label's fusion closure under the magnetic
list's closure (`con:depthchain`), one label per index entry at the
electric read `4 ĉ₂`, the magnetic member the closure fold `N_L`
(`lem:fpcap`'s `fpcap.closureMat`) and the gram the identity at the
orthonormal characters.  The window at a cutoff on the labels'
Casimir is the unit with the below-cutoff labels (`winIdx`), the
sector its positions reached from the unit under the closure fold's
joins (`sectorPos`, `sectorIdx`), and two cutoffs `K ≤ K'` split the
sector at `K'` into the head at `K` (`headAt`) and the excluded block
(`exclAt`).  The dual pencil `P(σ) = σE − M` enters cleared, the
scale `σ = [sn · c2D : c]` at a positive clearing `c` with the tex's
`σ = [sn : sdn]` its instance at `c = sdn · c2D` (`dualH`, `dualG`),
and the pencil at a level `⟨x : y⟩` is the level
site `levelSite`, the level's two members cross-added on the cleared
gram (`thm:certconstruct`'s levels).

The seed floor `F = ⟨4σΛ : d_L⟩` at the cutoff `Λ` enters as the
level's gap `g` at the join `(x + d_L) c + g = 4 σ Λ + y c`.  The
excluded block sits at or above the floor (`exclFloor`): every
excluded label's Casimir is beyond the cutoff (`beyondAt`), so the
electric read clears `4Λ`, and the magnetic form cap `d_L` is kept by
the excluded principal block, the closure fold's cap at the joined
window read at the vectors vacant on the head (`capBlock`,
`lem:fpcap`; `lem:inertia`'s compression).

The cutoff labels are the head labels whose fusion by a closure
member leaves the cutoff (`leaves`, their positions
    `cutPos`), and the border cap `ϰ_B` is the product of the coupling's
largest row and column sums at the head's excluded targets
(`targets`, `rowSum`, `colSum`, `rowMax`, `colMax`, `borderCap`); the
two-sided Schur read `B Bᵀ ⪯ ϰ_B` on the cutoff labels' support is
`schur_psd`, the Schur site `[ϰ_B D₁, s B; s Bᵀ, s² 1]` positive
semidefinite at row sums under the largest row sum on the support
and column sums under the largest column sum, the entry's doubled
cross product priced by two squares.  The coupling's sums at the
excluded block read the cap (`rowRead`, `colRead`, `capRead`): a row
off the support is vacant and a row on it sits under the largest row
sum over the targets, the excluded block a distinct family inside
the targets at its occupied members (`fusion.rowLaw` at every closure
member, head label and excluded label, `rowLawAll`), and the two
factors are occupied together.

The truncation pair (`truncPair`): the head's count sits at or below
the chain's, the plain truncation a compression at the head-first
order (`head_le_chain`, the level site at the joined window the block
join of the two windows' sites with the coupling's balance partner,
`levelSite_join`); and the chain's count sits at or below the
cutoff-bordered pencil's (`bordPencil`, the auxiliary block at the
gap down its diagonal, the coupling `c ϰ_B` on the cutoff positions
and the head site at `ϰ_B`, the pencil cleared by the auxiliary
diagonal's second member).  The bordered arm runs in two reads: the
chain scaled by the gap dominates the shifted block diagonal, the
head site less the border cap on the support (`shiftHead`) beside the
excluded site less the gap's square (`shiftExcl`), the difference
site the Schur site (`diffTie`) and the removed block's shifted site
positive semidefinite at the floor, so the chain's count sits at or
below the shifted head's (`chain_le_shift`, `thm:truncation`'s
monotone read); and the bordered pencil's count is the shifted
head's, the auxiliary pivots positive with inertia additive and the
deflation the shifted head at a positive scale (`bord_read`,
`bord_schur`, `lem:inertia`'s addition clause), the head site itself
at vacant cutoff positions.  Two agreeing counts locate the chain's
count (`pinned`, `lem:dualtrunc`).

The pair carrier's identities enter as one-value reads at the
atoms: every intermediate datum is symmetric, so `inertia.mkSplit`
reads it (`lem:inertia`: every symmetric datum has a split), and the
consumed counts are certificate data, one split per pencil.

`extRead` is the contact cell's extent certificate: the `σ`-extent
`σ₁` is the divisor's first positive root, committed as a bracket
over the divisor's squarefree witness (`lem:cellcount`'s `divRead`),
the segment from the unit up to the bracket's bottom holding a vacant
root count and the bracket itself holding one, the two segment
counts of `lem:hermitesign`'s bracket pencil at `lem:deckfactor`'s
cleared variable.  `dualPMat` carries the dual pencil over the
coupling coordinate, the pair `(σE : M)`'s site datum affine in
`σ`, its constant key the level datum's magnetic partner and its
linear key the electric member, and `endEval` is the contact end's
own read: at the coupling's unit point the cell's matrix is the
magnetic member's balance partner at the level, the counts the
closure fold's reads.
-/

namespace contactcell
open ground poly elim inertia certconstruct truncation

/-- `lem:contactcell`'s bordered pencil at positive auxiliary
pivots: the assembled datum's reversal count is its deflation's
alone, the auxiliary block's count vacant at the level below the seed
floor `F`, so the bordered read is the Schur complement's own
(`lem:inertia`'s addition clause at the solve witness, the pivot's
count the positive-semidefinite split's). -/
theorem bord_schur {k m : Nat} (Daux Bc P' Cw : Mat)
    (spJ : Split (k + m)) (spA : Split k) (spD : Split m)
    (hA : sqAt Daux k) (hBl : Bc.length = k) (hBr : rowsLen m Bc)
    (hP : sqAt P' m) (hCl : Cw.length = k) (hCr : rowsLen m Cw)
    (hAs : matOneValue (transposeM Daux) Daux)
    (hAw : matOneValue (matMul Daux Cw) (matScaleB (minor Daux) Bc))
    (hAnz : ¬ (minor Daux).oneValue BPair.unit)
    (hJ : splitRead (blockJoin Daux Bc P') spJ)
    (ha : splitRead Daux spA) (hpa : psdAt spA)
    (hd : splitRead (deflMat Daux Bc P' Cw) spD) :
    revAt spJ = revAt spD := by
  have hzero : revAt spA = 0 := hpa
  have hsum := inertia.rev_add Daux Bc P' Cw hA hBl hBr hP hCl hCr
    hAs hAw hAnz spJ hJ spA ha spD hd
  rw [hzero, Nat.zero_add] at hsum
  exact hsum

/-- `lem:contactcell`'s extent certificate: the contact cell's
`σ`-extent `σ₁` is the divisor's first positive root, committed as
the bracket `[lo, hi]` over the divisor's squarefree witness — the
segment from the unit up to the bracket's bottom at a vacant root
count and the bracket itself at one, the two segment counts of the
squarefree part's cleared variable with the endpoints rescaled by the
top's magnitude (`lem:hermitesign`'s bracket pencil at
`deckfactor.clearVarBT`, `lem:deckfactor`'s clearing at the value's
representative). -/
def extRead {o1 o2 o3 o4 : Nat} (D : Poly) (ct : cellcount.DivCert)
    (lo hi : BPair) (c : Pos)
    (spH1 : Split o1) (spB1 : Split o2)
    (spH2 : Split o3) (spB2 : Split o4) : Prop :=
  cellcount.divRead D ct
  ∧ hermitesign.segCountRead (deckfactor.clearVarBT ct.sq)
      (deckfactor.clearAt ct.sq BPair.unit)
      (deckfactor.clearAt ct.sq lo) c 0 spH1 spB1
  ∧ hermitesign.segCountRead (deckfactor.clearVarBT ct.sq)
      (deckfactor.clearAt ct.sq lo)
      (deckfactor.clearAt ct.sq hi) c 1 spH2 spB2

instance instContactcell1 {o1 o2 o3 o4 : Nat} (D : Poly) (ct : cellcount.DivCert)
    (lo hi : BPair) (c : Pos) (spH1 : Split o1) (spB1 : Split o2)
    (spH2 : Split o3) (spB2 : Split o4) :
    Decidable (extRead D ct lo hi c spH1 spB1 spH2 spB2) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The extent's bracket sits above the sum's unit: the segment count
from the unit to the bracket's lower end reads the two cleared points
in order, and the clearing's positive factor reads the order back
(the extent's positivity at the bracket's foot). -/
theorem extRead_pos {o1 o2 o3 o4 : Nat} (D : Poly) (ct : cellcount.DivCert)
    (lo hi : BPair) (c : Pos) (spH1 : Split o1) (spB1 : Split o2)
    (spH2 : Split o3) (spB2 : Split o4)
    (h : extRead D ct lo hi c spH1 spB1 spH2 spB2) :
    BPair.unit < lo := by
  have hlt : deckfactor.clearAt ct.sq BPair.unit
      < deckfactor.clearAt ct.sq lo := h.2.1.1
  refine if hc : BPair.unit < lo then hc else absurd hlt ?_
  have hle : lo ≤ BPair.unit := ground.leB_of_not_lt hc
  refine ground.leB_not_lt ?_
  show lo * windowsep.radiusD ct.sq ≤ BPair.unit * windowsep.radiusD ct.sq
  refine ground.leB_congr_left
    (BPair.oneValue_of_eq (BPair.mul_comm (windowsep.radiusD ct.sq) lo)) ?_
  refine ground.leB_congr_right
    (BPair.oneValue_of_eq
      (BPair.mul_comm (windowsep.radiusD ct.sq) BPair.unit)) ?_
  exact ground.leB_mulR (windowsep.unitLe_radiusD ct.sq) hle

/-- The extension read is one value across the divisor's
representatives: the certificate conjunct carries
(`cellcount.divRead_congr`) and the two counts read the
certificate's own squarefree part. -/
theorem extRead_congr {o1 o2 o3 o4 : Nat} {D D' : Poly}
    (h : poly.oneValue D D') (ct : cellcount.DivCert)
    (lo hi : BPair) (c : Pos) (spH1 : Split o1) (spB1 : Split o2)
    (spH2 : Split o3) (spB2 : Split o4) :
    extRead D ct lo hi c spH1 spB1 spH2 spB2
      ↔ extRead D' ct lo hi c spH1 spB1 spH2 spB2 :=
  ⟨fun hr => ⟨(cellcount.divRead_congr h ct).mp hr.1, hr.2⟩,
   fun hr => ⟨(cellcount.divRead_congr h ct).mpr hr.1, hr.2⟩⟩


/-- A divisor's first positive root, the extent's certificate: the
divisor's vacant leading keys withdrawn at the origin's least
occupied degree, the cofactor's constant occupied, and the bracket
at the cofactor (`extRead`, `lem:contactcell`'s bracket shape at
the withdrawn cofactor). -/
def extentRead {o1 o2 o3 o4 : Nat} (D : Poly) (k : Nat)
    (ct : cellcount.DivCert) (lo hi : BPair)
    (c : Pos) (spH1 : Split o1)
    (spB1 : Split o2) (spH2 : Split o3)
    (spB2 : Split o4) : Prop :=
  poly.unitTail (D.take k)
  ∧ ¬ (ground.getAt BPair.unit D k).oneValue
      BPair.unit
  ∧ extRead (D.drop k) ct lo hi c spH1 spB1 spH2 spB2

instance instContactcell2 {o1 o2 o3 o4 : Nat} (D : Poly) (k : Nat)
    (ct : cellcount.DivCert) (lo hi : BPair)
    (c : Pos) (spH1 : Split o1)
    (spB1 : Split o2) (spH2 : Split o3)
    (spB2 : Split o4) :
    Decidable (extentRead D k ct lo hi c spH1 spB1 spH2 spB2) :=
  inferInstanceAs (Decidable (_ ∧ ¬ _ ∧ _))

/-- The extent read is one value across the divisor's
representatives: the withdrawal's two conjuncts move across the
leading part and the key read, and the located read carries at the
dropped part (`extRead_congr`). -/
theorem extentRead_congr {o1 o2 o3 o4 : Nat} {D D' : Poly}
    (h : poly.oneValue D D') (k : Nat) (ct : cellcount.DivCert)
    (lo hi : BPair) (c : Pos)
    (spH1 : Split o1) (spB1 : Split o2)
    (spH2 : Split o3) (spB2 : Split o4) :
    extentRead D k ct lo hi c spH1 spB1 spH2 spB2
      ↔ extentRead D' k ct lo hi c spH1 spB1 spH2 spB2 := by
  constructor
  · intro ⟨h1, h2, h3⟩
    exact ⟨poly.unitTail_oneValue_right h1 (poly.take_congr k h),
      fun hx => h2 (BPair.oneValue_trans
        (poly.oneValue_getAt k h) hx),
      (extRead_congr (poly.drop_congr k h)
        ct lo hi c spH1 spB1 spH2 spB2).mp h3⟩
  · intro ⟨h1, h2, h3⟩
    exact ⟨poly.unitTail_oneValue_right h1
        (poly.take_congr k (poly.oneValue_symm h)),
      fun hx => h2 (BPair.oneValue_trans
        (poly.oneValue_getAt k (poly.oneValue_symm h)) hx),
      (extRead_congr (poly.drop_congr k h)
        ct lo hi c spH1 spB1 spH2 spB2).mpr h3⟩

/-- The extent's bracket sits above the sum's unit, the dropped
part's bracket read (`extRead_pos`). -/
theorem extentRead_pos {o1 o2 o3 o4 : Nat} (D : Poly) (k : Nat)
    (ct : cellcount.DivCert) (lo hi : BPair) (c : Pos)
    (spH1 : Split o1) (spB1 : Split o2) (spH2 : Split o3)
    (spB2 : Split o4)
    (h : extentRead D k ct lo hi c spH1 spB1 spH2 spB2) :
    BPair.unit < lo :=
  extRead_pos _ _ _ _ _ _ _ _ _ h.2.2
/-! ## The vacuum sector's one-plaquette chain at a cutoff

The chain is the unit label's fusion closure under the magnetic
list's closure (`con:depthchain`), one label per index entry at the
electric read `4 ĉ₂` and the magnetic member the closure fold `N_L`
(`lem:fpcap`'s `fpcap.closureMat`), the gram the identity at the
orthonormal characters; the window at a cutoff on the labels'
Casimir is the unit with the below-cutoff labels, the sector's
members its positions reached from the unit under the closure fold's
joins. -/

/-- Each window position its own list: the one-plaquette window's
positions, one label per index entry (`con:depthchain`). -/
def singles (n : Nat) : List (List Nat) := (List.range n).map (fun i => [i])

/-- The window at a cutoff on the labels' Casimir: the unit label
with the below-cutoff labels (`prop:windowfinite`'s window). -/
def winIdx {L : Type} (F : fusion.Data L) (K : Nat) : List L :=
  F.unit :: F.below K

/-- The vacuum sector's positions at the cutoff: the unit's reach
under the closure fold's joins over the window, the base's fusion
closure at the one-plaquette window (`con:depthchain`). -/
def sectorPos {L : Type} (F : fusion.Data L) (sd pr : List L) (K : Nat) :
    List Nat :=
  depthchain.reach [fpcap.closureMat F sd pr (winIdx F K)]
    (singles (winIdx F K).length) (winIdx F K).length [0]
    (winIdx F K).length

/-- The sector's labels, its positions read at the window. -/
def sectorIdx {L : Type} (F : fusion.Data L) (sd pr : List L) (K : Nat) :
    List L :=
  (sectorPos F sd pr K).map (fun i => ground.getAt F.unit (winIdx F K) i)

/-- The head at the cutoff `K` inside the window at `K'`: the
sector's members at Casimir at or below `K`. -/
def headAt {L : Type} (F : fusion.Data L) (sd pr : List L) (K K' : Nat) :
    List L :=
  (sectorIdx F sd pr K').filter (fun l => decide (F.c2N l ≤ K))

/-- The excluded block at the cutoff `K` inside the window at `K'`:
the sector's members at Casimir beyond `K`. -/
def exclAt {L : Type} (F : fusion.Data L) (sd pr : List L) (K K' : Nat) :
    List L :=
  (sectorIdx F sd pr K').filter (fun l => decide (K < F.c2N l))

/-- The diagonal at an index family: the family's naturals down the
diagonal, the sum's unit off it. -/
def diagN (dd : Nat → Nat) (k : Nat) : Mat :=
  elim.diagO ground.bpairOps ((List.range k).map (fun i => BPair.ofNat (dd i)))

/-- The electric diagonal at a label list: the loop's content
`4 ĉ₂` at the Casimir's cleared member (`prop:E0`; `def:pencil`). -/
def elecMat {L : Type} (F : fusion.Data L) (ls : List L) : Mat :=
  diagN (fun i => 4 * F.c2N (ground.getAt F.unit ls i)) ls.length

/-- The dual pencil `P(σ) = σE - M` at a label list, cleared:
`sn · E - c · M` at the clearing `c` (`pencil.rayH`). -/
def dualH {L : Type} (F : fusion.Data L) (sd pr ls : List L) (sn c : Pos) :
    Mat :=
  pencil.rayH (elecMat F ls) (fpcap.closureMat F sd pr ls) sn c

/-- The gram at the clearing: the identity at the orthonormal
characters, cleared with the pencil. -/
def dualG (c : Pos) (n : Nat) : Mat := inertia.matScale c (elim.idMat n)

/-- A head label whose fusion by a closure member leaves the cutoff:
some closure member's row at the label holds a target at Casimir
beyond `K` (`prop:fusionfinite`). -/
def leaves {L : Type} (F : fusion.Data L) (sd pr : List L) (K : Nat)
    (l : L) : Bool :=
  (fpcap.closureList F sd pr).any (fun lam =>
    (F.row lam l).any (fun c => decide (K < F.c2N c)))

/-- The cutoff labels' support diagonal over the head: one at a
cutoff label, the sum's unit elsewhere. -/
def suppDiag {L : Type} (F : fusion.Data L) (sd pr : List L) (K : Nat)
    (hd : List L) : Mat :=
  diagN (fun i => if leaves F sd pr K (ground.getAt F.unit hd i) then 1 else 0)
    hd.length

/-- The head's excluded targets: every closure member's row target
beyond the cutoff at a head label, each label once. -/
def targets {L : Type} [DecidableEq L] (F : fusion.Data L) (sd pr : List L)
    (K : Nat) (hd : List L) : List L :=
  ground.dedupF (hd.flatMap (fun l => (fpcap.closureList F sd pr).flatMap
    (fun lam => (F.row lam l).filter (fun c => decide (K < F.c2N c)))))

/-- The coupling's row sum at a head label over a target list: the
closure fold's entries `Σ_c N_L[l, c]`. -/
def rowSum {L : Type} (F : fusion.Data L) (sd pr : List L) (T : List L)
    (l : L) : Nat :=
  ground.famFold Nat.add 0 (fun c => fpcap.closureCount F sd pr c l) T

/-- The coupling's column sum at a target over the head. -/
def colSum {L : Type} (F : fusion.Data L) (sd pr : List L) (hd : List L)
    (c : L) : Nat :=
  ground.famFold Nat.add 0 (fun l => fpcap.closureCount F sd pr c l) hd

/-- The coupling's largest row sum over the head. -/
def rowMax {L : Type} (F : fusion.Data L) (sd pr : List L) (T hd : List L) :
    Nat :=
  hd.foldl (fun a l => Nat.max a (rowSum F sd pr T l)) 0

/-- The coupling's largest column sum over the targets. -/
def colMax {L : Type} (F : fusion.Data L) (sd pr : List L) (hd T : List L) :
    Nat :=
  T.foldl (fun a c => Nat.max a (colSum F sd pr hd c)) 0

/-- The border cap `ϰ_B`: the product of the coupling's largest row
and column sums at the head's excluded targets (`lem:contactcell`). -/
def borderCap {L : Type} [DecidableEq L] (F : fusion.Data L) (sd pr : List L)
    (K : Nat) (hd : List L) : Nat :=
  rowMax F sd pr (targets F sd pr K hd) hd
    * colMax F sd pr hd (targets F sd pr K hd)

/-- The variable atom of a pair-carrier cast. -/
private def pv (i : Nat) : Pol := Pol.mon (Mon.var i)

/-! The border cap's two-sided Schur read at index folds: an entry's
doubled cross product is priced by the two squares `(C x)² + (s y)²`
at the count's weight, the squares collect by rows and by columns to
the row and column sums, and the sums sit under the largest row sum
on the support and the largest column sum. -/

/-- The entry's cross read at the column weight is the pricing's
cross product. -/
private theorem crossCast (C s b x y : BPair) :
    (C * (s * (b * (x * y)) + s * (b * (x * y)))).oneValue
      (b * ((C * x) * (s * y) + (C * x) * (s * y))) :=
  polEqB [C, s, b, x, y]
    (Pol.mul (pv 0) (Pol.add (Pol.mul (pv 1) (Pol.mul (pv 2) (Pol.mul (pv 3) (pv 4))))
      (Pol.mul (pv 1) (Pol.mul (pv 2) (Pol.mul (pv 3) (pv 4))))))
    (Pol.mul (pv 2) (Pol.add (Pol.mul (Pol.mul (pv 0) (pv 3)) (Pol.mul (pv 1) (pv 4)))
      (Pol.mul (Pol.mul (pv 0) (pv 3)) (Pol.mul (pv 1) (pv 4)))))
    (by decide +kernel)

/-- The entry's two weighted squares are the pricing's squares. -/
private theorem sqCast (C s b x y : BPair) :
    (C * C * (b * (x * x)) + s * s * (b * (y * y))).oneValue
      (b * ((C * x) * (C * x) + (s * y) * (s * y))) :=
  polEqB [C, s, b, x, y]
    (Pol.add (Pol.mul (Pol.mul (pv 0) (pv 0)) (Pol.mul (pv 2) (Pol.mul (pv 3) (pv 3))))
      (Pol.mul (Pol.mul (pv 1) (pv 1)) (Pol.mul (pv 2) (Pol.mul (pv 4) (pv 4)))))
    (Pol.mul (pv 2) (Pol.add (Pol.mul (Pol.mul (pv 0) (pv 3)) (Pol.mul (pv 0) (pv 3)))
      (Pol.mul (Pol.mul (pv 1) (pv 4)) (Pol.mul (pv 1) (pv 4)))))
    (by decide +kernel)

/-- The entry priced: the column weight times the doubled cross
read sits at or below the two weighted squares. -/
private theorem entryPriced (C s : Pos) (b : Nat) (x y : BPair) :
    BPair.ofPos C * (BPair.ofPos s * (BPair.ofNat b * (x * y))
        + BPair.ofPos s * (BPair.ofNat b * (x * y)))
      ≤ BPair.ofPos (C * C) * (BPair.ofNat b * (x * x))
        + BPair.ofPos (s * s) * (BPair.ofNat b * (y * y)) := by
  refine leB_congr (BPair.oneValue_symm (crossCast _ _ _ x y)) ?_
    (ground.leB_crossSq (ground.unitLeOfNat b) _ _)
  refine BPair.oneValue_trans (BPair.oneValue_symm (sqCast _ _ _ x y)) ?_
  exact BPair.add_congr
    (BPair.mul_congr_left (BPair.ofPos_mul C C))
    (BPair.mul_congr_left (BPair.ofPos_mul s s))

/-- The squares' fold at a count family sits under the count sum's
cap against the square. -/
private theorem sqFoldCap (cap : Nat) (bb : Nat → Nat) (z : BPair) (l : List Nat)
    (h : ground.famFold Nat.add 0 bb l ≤ cap) :
    bsum (fun j => BPair.ofNat (bb j) * (z * z)) l ≤ BPair.ofNat cap * (z * z) :=
  leB_congr_left (BPair.oneValue_symm (bsum_scalar bb (z * z) l))
    (leB_scale_mono h (ground.unitLeSq z))

/-- The Schur read's core at index folds: at row sums under the
largest row sum on the support and column sums under the largest
column sum, the diagonal's fold at the border cap and the squares'
fold at the gap's square sit at or above the doubled cross fold's
balance partner. -/
private theorem schurCore (k m R : Nat) (C s : Pos)
    (bb : Nat → Nat → Nat) (dd : Nat → Nat) (xx yy : Nat → BPair)
    (hrow : ∀ i, i < k →
      ground.famFold Nat.add 0 (fun j => bb i j) (List.range m) ≤ R * dd i)
    (hcol : ∀ j, j < m →
      ground.famFold Nat.add 0 (fun i => bb i j) (List.range k) ≤ posVal C) :
    BPair.unit ≤
      BPair.ofNat (R * posVal C)
          * bsum (fun i => BPair.ofNat (dd i) * (xx i * xx i)) (List.range k)
        + BPair.ofPos (s * s) * bsum (fun j => yy j * yy j) (List.range m)
        + bsum (fun i => bsum (fun j =>
            (BPair.ofPos s * (BPair.ofNat (bb i j) * (xx i * yy j))
              + BPair.ofPos s * (BPair.ofNat (bb i j) * (xx i * yy j))).swap)
            (List.range m)) (List.range k) := by
  -- the cross fold and its swap
  have hswap : bsum (fun i => bsum (fun j =>
        (BPair.ofPos s * (BPair.ofNat (bb i j) * (xx i * yy j))
          + BPair.ofPos s * (BPair.ofNat (bb i j) * (xx i * yy j))).swap)
        (List.range m)) (List.range k)
      = (bsum (fun i => bsum (fun j =>
        BPair.ofPos s * (BPair.ofNat (bb i j) * (xx i * yy j))
          + BPair.ofPos s * (BPair.ofNat (bb i j) * (xx i * yy j)))
        (List.range m)) (List.range k)).swap :=
    (ground.famFold_congr_all BPair.add BPair.unit _ _
      (fun i => fold_swap (fun j =>
        BPair.ofPos s * (BPair.ofNat (bb i j) * (xx i * yy j))
          + BPair.ofPos s * (BPair.ofNat (bb i j) * (xx i * yy j))) (List.range m))
      (List.range k)).trans (fold_swap _ (List.range k))
  refine leB_unit_add ?_
  rw [hswap, BPair.swap_swap]
  -- the priced sum: C times the cross fold under the two squares' folds
  have hpriced : BPair.ofPos C * bsum (fun i => bsum (fun j =>
        BPair.ofPos s * (BPair.ofNat (bb i j) * (xx i * yy j))
          + BPair.ofPos s * (BPair.ofNat (bb i j) * (xx i * yy j)))
        (List.range m)) (List.range k)
      ≤ bsum (fun i => bsum (fun j =>
        BPair.ofPos (C * C) * (BPair.ofNat (bb i j) * (xx i * xx i))
          + BPair.ofPos (s * s) * (BPair.ofNat (bb i j) * (yy j * yy j)))
        (List.range m)) (List.range k) := by
    refine leB_congr_left (foldB_mul_left _ _ (List.range k)) ?_
    refine bsum_le_of_mem _ _ (List.range k) (fun i _ => ?_)
    refine leB_congr_left (foldB_mul_left _ _ (List.range m)) ?_
    exact bsum_le_of_mem _ _ (List.range m) (fun j _ => entryPriced C s (bb i j) (xx i) (yy j))
  -- the squares' folds collect by rows and by columns
  have hsplit : (bsum (fun i => bsum (fun j =>
        BPair.ofPos (C * C) * (BPair.ofNat (bb i j) * (xx i * xx i))
          + BPair.ofPos (s * s) * (BPair.ofNat (bb i j) * (yy j * yy j)))
        (List.range m)) (List.range k)).oneValue
      (BPair.ofPos (C * C) * bsum (fun i => bsum (fun j =>
          BPair.ofNat (bb i j) * (xx i * xx i)) (List.range m)) (List.range k)
        + BPair.ofPos (s * s) * bsum (fun j => bsum (fun i =>
          BPair.ofNat (bb i j) * (yy j * yy j)) (List.range k)) (List.range m)) := by
    refine BPair.oneValue_trans (foldB_congr_members _ _ (List.range k)
      (fun i _ => foldB_add _ _ (List.range m))) ?_
    refine BPair.oneValue_trans (foldB_add _ _ (List.range k)) ?_
    refine BPair.add_congr ?_ ?_
    · refine BPair.oneValue_trans (foldB_congr_members _ _ (List.range k)
        (fun i _ => foldB_mul_left _ _ (List.range m))) ?_
      exact foldB_mul_left _ _ (List.range k)
    · refine BPair.oneValue_trans (foldB_congr_members _ _ (List.range k)
        (fun i _ => foldB_mul_left _ _ (List.range m))) ?_
      refine BPair.oneValue_trans (foldB_mul_left _ _ (List.range k)) ?_
      exact BPair.mul_congr (BPair.oneValue_refl _)
        (bsum_swap (fun i j => BPair.ofNat (bb i j) * (yy j * yy j))
          (List.range k) (List.range m))
  -- the row and column caps
  have hrows : bsum (fun i => bsum (fun j =>
        BPair.ofNat (bb i j) * (xx i * xx i)) (List.range m)) (List.range k)
      ≤ BPair.ofNat R * bsum (fun i => BPair.ofNat (dd i) * (xx i * xx i)) (List.range k) := by
    refine leB_congr_right (foldB_mul_left _ _ (List.range k)) ?_
    refine bsum_le_of_mem _ _ (List.range k) (fun i hi => ?_)
    refine leB_congr_right ?_ (sqFoldCap (R * dd i) (fun j => bb i j) (xx i) (List.range m)
      (hrow i (ground.ltOfMemRange hi)))
    refine BPair.oneValue_trans (BPair.mul_congr_left (BPair.ofNat_mul R (dd i))) ?_
    exact BPair.oneValue_of_eq (BPair.mul_assoc _ _ _)
  have hcols : bsum (fun j => bsum (fun i =>
        BPair.ofNat (bb i j) * (yy j * yy j)) (List.range k)) (List.range m)
      ≤ BPair.ofPos C * bsum (fun j => yy j * yy j) (List.range m) := by
    refine leB_congr_right (foldB_mul_left _ _ (List.range m)) ?_
    exact bsum_le_of_mem _ _ (List.range m) (fun j hj =>
      sqFoldCap (posVal C) (fun i => bb i j) (yy j) (List.range k)
        (hcol j (ground.ltOfMemRange hj)))
  -- assemble at the column weight and cancel it
  have hcast : (BPair.ofPos (C * C)
        * (BPair.ofNat R * bsum (fun i => BPair.ofNat (dd i) * (xx i * xx i)) (List.range k))
      + BPair.ofPos (s * s) * (BPair.ofPos C * bsum (fun j => yy j * yy j) (List.range m))).oneValue
      (BPair.ofPos C * (BPair.ofNat (R * posVal C)
          * bsum (fun i => BPair.ofNat (dd i) * (xx i * xx i)) (List.range k)
        + BPair.ofPos (s * s) * bsum (fun j => yy j * yy j) (List.range m))) := by
    refine BPair.oneValue_trans (BPair.add_congr
      (BPair.mul_congr_left (BPair.oneValue_symm (BPair.ofPos_mul C C)))
      (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans ?_ (BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.add_congr (BPair.mul_congr_left
        (show (BPair.ofNat R * BPair.ofPos C).oneValue (BPair.ofNat (R * posVal C)) from
          BPair.oneValue_symm (BPair.ofNat_mul R (posVal C))))
        (BPair.oneValue_refl _)))
    exact polEqB [BPair.ofPos C, BPair.ofNat R,
        bsum (fun i => BPair.ofNat (dd i) * (xx i * xx i)) (List.range k),
        BPair.ofPos (s * s), bsum (fun j => yy j * yy j) (List.range m)]
      (Pol.add (Pol.mul (Pol.mul (pv 0) (pv 0)) (Pol.mul (pv 1) (pv 2)))
        (Pol.mul (pv 3) (Pol.mul (pv 0) (pv 4))))
      (Pol.mul (pv 0) (Pol.add (Pol.mul (Pol.mul (pv 1) (pv 0)) (pv 2))
        (Pol.mul (pv 3) (pv 4))))
      (by decide +kernel)
  have hall : BPair.ofPos C * bsum (fun i => bsum (fun j =>
        BPair.ofPos s * (BPair.ofNat (bb i j) * (xx i * yy j))
          + BPair.ofPos s * (BPair.ofNat (bb i j) * (xx i * yy j)))
        (List.range m)) (List.range k)
      ≤ BPair.ofPos C * (BPair.ofNat (R * posVal C)
          * bsum (fun i => BPair.ofNat (dd i) * (xx i * xx i)) (List.range k)
        + BPair.ofPos (s * s) * bsum (fun j => yy j * yy j) (List.range m)) := by
    refine leB_trans hpriced (leB_congr_left (BPair.oneValue_symm hsplit)
      (leB_congr_right hcast ?_))
    exact leB_add (ground.leB_mulR (Or.inr (ground.unitLtOfPos _)) hrows)
      (ground.leB_mulR (Or.inr (ground.unitLtOfPos _)) hcols)
  exact leB_of_scale (leB_congr (BPair.ofPos_scale C _) (BPair.ofPos_scale C _) hall)

/-! The Schur site and its form: the border cap on the cutoff
labels' support diagonal, the gap-scaled coupling, and the gap's
square on the excluded block's identity, the form read at a joined
vector the core's three folds. -/

/-- The coupling's balance partner at an index family: the counts'
swaps, rows over the head and columns over the excluded block. -/
def coupN (bb : Nat → Nat → Nat) (k m : Nat) : Mat :=
  (List.range k).map (fun i => (List.range m).map (fun j => (BPair.ofNat (bb i j)).swap))

/-- The Schur site at a border cap, a gap, a support diagonal and a
coupling: `[ϰ D₁, s B; s Bᵀ, s² 1]`. -/
def schurSite (kB : Nat) (s : Pos) (D1 B : Mat) (m : Nat) : Mat :=
  inertia.blockJoin (inertia.matScaleB (BPair.ofNat kB) D1) (inertia.matScale s B)
    (inertia.matScale (s * s) (elim.idMat m))

/-- The support diagonal's order. -/
private theorem diagN_len (dd : Nat → Nat) (k : Nat) : (diagN dd k).length = k :=
  (elim.diagO_len _ _).trans (ground.length_mapRange _ k)

private theorem diagN_rows (dd : Nat → Nat) (k : Nat) : rowsLen k (diagN dd k) :=
  rowsLen_cast (ground.length_mapRange _ k) (elim.diagO_rows _ _)

/-- The diagonal's entry at a key pair. -/
private theorem diagN_entry (dd : Nat → Nat) (k i j : Nat) (hi : i < k) (hj : j < k) :
    ground.getAt BPair.unit (ground.getAt [] (diagN dd k) i) j
      = if j = i then BPair.ofNat (dd i) else BPair.unit := by
  have hl : ((List.range k).map (fun i => BPair.ofNat (dd i))).length = k :=
    ground.length_mapRange _ k
  refine (elim.diagO_entry ground.bpairOps _ i j (by rw [hl]; exact hi)
    (by rw [hl]; exact hj)).trans ?_
  show (if j = i then ground.getAt BPair.unit ((List.range k).map (fun i => BPair.ofNat (dd i))) i
    else BPair.unit) = _
  rw [ground.getAt_map_range BPair.unit _ k i, if_pos hi]

/-- The support diagonal's form: the weighted squares' fold. -/
private theorem quadDiagN (dd : Nat → Nat) (k : Nat) (x : List BPair)
    (hx : x.length = k) :
    (dotN x (matVec (diagN dd k) x)).oneValue
      (bsum (fun i => BPair.ofNat (dd i)
        * (ground.getAt BPair.unit x i * ground.getAt BPair.unit x i)) (List.range k)) := by
  have hml : (matVec (diagN dd k) x).length = k :=
    (matVec_length _ x).trans (diagN_len dd k)
  refine BPair.oneValue_trans (dotN_read _ _) ?_
  rw [dotP_fold k x _ hx hml]
  refine foldB_congr_members _ _ (List.range k) (fun i hi => ?_)
  have hin : i < k := ground.ltOfMemRange (ground.mem_of_countOf_pos i _ hi)
  rw [getAt_matVec _ x i (by rw [diagN_len]; exact hin)]
  refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
    (elim.diagO_row _ x i (by rw [ground.length_mapRange]; exact hin)
      (hx.trans (ground.length_mapRange _ k).symm))) ?_
  rw [ground.getAt_map_range BPair.unit (fun i => BPair.ofNat (dd i)) k i, if_pos hin]
  exact BPair.oneValue_of_eq (BPair.mul_left_comm _ _ _)

/-- The coupling's row count and width. -/
private theorem coupN_len (bb : Nat → Nat → Nat) (k m : Nat) : (coupN bb k m).length = k :=
  ground.length_mapRange _ k

private theorem coupN_rows (bb : Nat → Nat → Nat) (k m : Nat) : rowsLen m (coupN bb k m) :=
  rowsLen_map _ m (List.range k) (fun _ _ => ground.length_mapRange _ m)

/-- The gap-scaled coupling's form at a head vector against an
excluded vector: the swapped cross fold. -/
private theorem quadCoupN (bb : Nat → Nat → Nat) (k m : Nat) (s : Pos)
    (x y : List BPair) (hx : x.length = k) (hy : y.length = m) :
    (dotN x (matVec (inertia.matScale s (coupN bb k m)) y)).oneValue
      (bsum (fun i => bsum (fun j =>
        (BPair.ofPos s * (BPair.ofNat (bb i j)
          * (ground.getAt BPair.unit x i * ground.getAt BPair.unit y j))).swap)
        (List.range m)) (List.range k)) := by
  have hBl : (inertia.matScale s (coupN bb k m)).length = k :=
    (inertia.length_matScale s _).trans (coupN_len bb k m)
  have hml : (matVec (inertia.matScale s (coupN bb k m)) y).length = k :=
    (matVec_length _ y).trans hBl
  refine BPair.oneValue_trans (dotN_read _ _) ?_
  rw [dotP_fold k x _ hx hml]
  refine foldB_congr_members _ _ (List.range k) (fun i hi => ?_)
  have hin : i < k := ground.ltOfMemRange (ground.mem_of_countOf_pos i _ hi)
  rw [getAt_matVec _ y i (by rw [hBl]; exact hin)]
  have hrow : ground.getAt [] (inertia.matScale s (coupN bb k m)) i
      = ((List.range m).map (fun j => (BPair.ofNat (bb i j)).swap)).map
          (fun z => z.scale s) := by
    show ground.getAt [] ((coupN bb k m).map (fun r => r.map (fun z => z.scale s))) i = _
    rw [ground.getAt_map [] [] _ (coupN bb k m) i (by rw [coupN_len]; exact hin)]
    show (ground.getAt [] ((List.range k).map (fun i =>
      (List.range m).map (fun j => (BPair.ofNat (bb i j)).swap))) i).map _ = _
    rw [ground.getAt_map_range [] _ k i, if_pos hin]
  rw [hrow]
  have hrl : (((List.range m).map (fun j => (BPair.ofNat (bb i j)).swap)).map
      (fun z => z.scale s)).length = m := by
    rw [ground.length_map, ground.length_mapRange]
  refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) (dotN_read _ y)) ?_
  rw [dotP_fold m _ y hrl hy]
  refine BPair.oneValue_trans (BPair.oneValue_symm (foldB_mul_left _ _ (List.range m))) ?_
  refine foldB_congr_members _ _ (List.range m) (fun j hj => ?_)
  have hjm : j < m := ground.ltOfMemRange (ground.mem_of_countOf_pos j _ hj)
  rw [ground.getAt_map BPair.unit BPair.unit _ _ j (by rw [ground.length_mapRange]; exact hjm),
    ground.getAt_map_range BPair.unit _ m j, if_pos hjm]
  refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
    (BPair.mul_congr_left (BPair.oneValue_symm (BPair.ofPos_scale s _)))) ?_
  rw [BPair.mul_swap, BPair.swap_mul, BPair.mul_swap]
  refine ground.swap_congr ?_
  exact polEqB [ground.getAt BPair.unit x i, BPair.ofPos s, BPair.ofNat (bb i j),
      ground.getAt BPair.unit y j]
    (Pol.mul (pv 0) (Pol.mul (Pol.mul (pv 1) (pv 2)) (pv 3)))
    (Pol.mul (pv 1) (Pol.mul (pv 2) (Pol.mul (pv 0) (pv 3))))
    (by decide +kernel)

/-- The scaled identity's form: the gap's square against the
self-pairing. -/
private theorem quadIdN (s : Pos) (m : Nat) (y : List BPair) (hy : y.length = m) :
    (dotN y (matVec (inertia.matScale (s * s) (elim.idMat m)) y)).oneValue
      (BPair.ofPos (s * s) * dotN y y) :=
  BPair.oneValue_trans (dotN_congrR _ _ _ (inertia.matVec_matScale (s * s) _ y))
    (BPair.oneValue_trans (elim.dotN_scaleV _ y _)
      (BPair.mul_congr (BPair.oneValue_refl _)
        (dotN_congrR _ _ _ (matVec_idMat m y hy))))

/-- The joined form's regrouping: the two cross reads collect. -/
private theorem joinRe (A X D : BPair) :
    (A + X + (X + D)).oneValue (A + D + (X + X)) :=
  BPair.oneValue_of_eq (by rw [BPair.add_comm X D, BPair.add_add_comm])

/-- The Schur site's form at a joined vector: the core's three
folds. -/
private theorem quadSchur (kB : Nat) (s : Pos) (bb : Nat → Nat → Nat) (dd : Nat → Nat)
    (k m : Nat) (hk : 0 < k) (x y : List BPair) (hx : x.length = k) (hy : y.length = m) :
    (dotN (x ++ y) (matVec (schurSite kB s (diagN dd k) (coupN bb k m) m) (x ++ y))).oneValue
      (BPair.ofNat kB * bsum (fun i => BPair.ofNat (dd i)
          * (ground.getAt BPair.unit x i * ground.getAt BPair.unit x i)) (List.range k)
        + BPair.ofPos (s * s) * dotN y y
        + bsum (fun i => bsum (fun j =>
            (BPair.ofPos s * (BPair.ofNat (bb i j)
              * (ground.getAt BPair.unit x i * ground.getAt BPair.unit y j))
            + BPair.ofPos s * (BPair.ofNat (bb i j)
              * (ground.getAt BPair.unit x i * ground.getAt BPair.unit y j))).swap)
          (List.range m)) (List.range k)) := by
  have hPl : (inertia.matScaleB (BPair.ofNat kB) (diagN dd k)).length = k :=
    (inertia.length_scaleB _ _).trans (diagN_len dd k)
  have hPr : rowsLen k (inertia.matScaleB (BPair.ofNat kB) (diagN dd k)) :=
    inertia.rowsLen_scaleB _ k _
      (elim.rowsLen_cast (ground.length_mapRange _ k) (elim.diagO_rows _ _))
  have hBl : (inertia.matScale s (coupN bb k m)).length = k :=
    (inertia.length_matScale s _).trans (coupN_len bb k m)
  have hBr : rowsLen m (inertia.matScale s (coupN bb k m)) :=
    rowsLen_mapRows _ _ m (coupN_rows bb k m)
  have hBt : (transposeM (inertia.matScale s (coupN bb k m))).length = m :=
    length_transposeM _ hBr (by rw [hBl]; exact hk)
  have hBtr : rowsLen k (transposeM (inertia.matScale s (coupN bb k m))) :=
    rowsLen_cast hBl (rowsLen_transposeM _)
  have hQl : (inertia.matScale (s * s) (elim.idMat m)).length = m :=
    (inertia.length_matScale _ _).trans (length_idMat m)
  refine BPair.oneValue_trans (inertia.quadJoin _ _ _ k m hPr hPl hBl hBt hBtr hQl
    x y x y hx hy hx) ?_
  have h1 : (dotN x (matVec (inertia.matScaleB (BPair.ofNat kB) (diagN dd k)) x)).oneValue
      (BPair.ofNat kB * bsum (fun i => BPair.ofNat (dd i)
        * (ground.getAt BPair.unit x i * ground.getAt BPair.unit x i)) (List.range k)) :=
    BPair.oneValue_trans (dotN_congrR _ _ _ (inertia.matVec_scaleB _ _ x))
      (BPair.oneValue_trans (elim.dotN_scaleV _ x _)
        (BPair.mul_congr (BPair.oneValue_refl _) (quadDiagN dd k x hx)))
  have h2 := quadCoupN bb k m s x y hx hy
  have h3 : (dotN y (matVec (transposeM (inertia.matScale s (coupN bb k m))) x)).oneValue
      (dotN x (matVec (inertia.matScale s (coupN bb k m)) y)) :=
    dotN_transpose_flip _ m hBr y x hy (hx.trans hBl.symm)
  have h4 := quadIdN s m y hy
  refine BPair.oneValue_trans (BPair.add_congr (BPair.add_congr h1 h2)
    (BPair.add_congr (BPair.oneValue_trans h3 h2) h4)) ?_
  have hcross : (bsum (fun i => bsum (fun j =>
        (BPair.ofPos s * (BPair.ofNat (bb i j)
          * (ground.getAt BPair.unit x i * ground.getAt BPair.unit y j))).swap)
        (List.range m)) (List.range k)
      + bsum (fun i => bsum (fun j =>
        (BPair.ofPos s * (BPair.ofNat (bb i j)
          * (ground.getAt BPair.unit x i * ground.getAt BPair.unit y j))).swap)
        (List.range m)) (List.range k)).oneValue
      (bsum (fun i => bsum (fun j =>
        (BPair.ofPos s * (BPair.ofNat (bb i j)
          * (ground.getAt BPair.unit x i * ground.getAt BPair.unit y j))
        + BPair.ofPos s * (BPair.ofNat (bb i j)
          * (ground.getAt BPair.unit x i * ground.getAt BPair.unit y j))).swap)
        (List.range m)) (List.range k)) := by
    refine BPair.oneValue_trans (BPair.oneValue_symm (foldB_add _ _ (List.range k))) ?_
    refine foldB_congr_members _ _ (List.range k) (fun i _ => ?_)
    refine BPair.oneValue_trans (BPair.oneValue_symm (foldB_add _ _ (List.range m))) ?_
    refine foldB_congr_members _ _ (List.range m) (fun j _ => ?_)
    rw [BPair.swap_add]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (joinRe _ _ _) ?_
  exact BPair.add_congr (BPair.oneValue_refl _) hcross

/-- The border cap's two-sided Schur read: at row sums under the
largest row sum on the support and column sums under the largest
column sum, the Schur site is positive semidefinite,
`B Bᵀ ⪯ ϰ_B` on the cutoff labels' support (`lem:contactcell`). -/
theorem schur_psd (k m R kB : Nat) (C s : Pos) (bb : Nat → Nat → Nat) (dd : Nat → Nat)
    (hrow : ∀ i, i < k →
      ground.famFold Nat.add 0 (fun j => bb i j) (List.range m) ≤ R * dd i)
    (hcol : ∀ j, j < m →
      ground.famFold Nat.add 0 (fun i => bb i j) (List.range k) ≤ posVal C)
    (hkB : R * posVal C ≤ kB)
    (sp : Split (k + m))
    (h : splitRead (schurSite kB s (diagN dd k) (coupN bb k m) m) sp) :
    psdAt sp := by
  cases Nat.eq_zero_or_pos k with
  | inl hk =>
    subst hk
    have h0 : (schurSite kB s (diagN dd 0) (coupN bb 0 m) m).length = 0 := by
      show (List.zipWith (· ++ ·) (inertia.matScaleB (BPair.ofNat kB) (diagN dd 0))
          (inertia.matScale s (coupN bb 0 m))
        ++ List.zipWith (· ++ ·) (transposeM (inertia.matScale s (coupN bb 0 m)))
          (inertia.matScale (s * s) (elim.idMat m))).length = 0
      have hc : inertia.matScale s (coupN bb 0 m) = [] := rfl
      rw [hc, ground.zipWith_nil_right (· ++ ·)]
      rfl
    have hm : m = 0 := by
      have h1 : (0 : Nat) = 0 + m := h0.symm.trans (elim.sqAt_len h.1)
      rw [Nat.zero_add] at h1
      exact h1.symm
    subst hm
    exact inertia.revAt_zero sp
  | inr hk =>
    refine inertia.psd_of_all _ sp h (fun u hu => ?_)
    obtain ⟨x, y, hxy, hx⟩ := ground.listSplit u k (by rw [hu]; exact Nat.le_add_right k m)
    rw [hxy] at hu ⊢
    have hy : y.length = m := by
      have h2 := ground.length_append x y
      rw [hx] at h2
      exact ground.addCancelL k (h2.symm.trans hu)
    intro hlt
    have hnn : BPair.unit ≤ bsum (fun i => BPair.ofNat (dd i)
        * (ground.getAt BPair.unit x i * ground.getAt BPair.unit x i)) (List.range k) :=
      foldB_nonneg_mem _ _ (fun i _ => ground.unitLeMul (ground.unitLeOfNat _) (ground.unitLeSq _))
    refine leB_not_lt (leB_trans (schurCore k m R C s bb dd
      (fun i => ground.getAt BPair.unit x i) (fun j => ground.getAt BPair.unit y j)
      hrow hcol) (leB_add (leB_add (leB_scale_mono hkB hnn) (leB_refl _)) (leB_refl _))) ?_
    refine BPair.lt_congr (BPair.oneValue_trans
      (quadSchur kB s bb dd k m hk x y hx hy)
      (BPair.add_congr (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.mul_congr (BPair.oneValue_refl _) (selfFold y m hy)))
        (BPair.oneValue_refl _))) (BPair.oneValue_refl _) hlt

/-! ## The level site and its block split -/

/-- The level site of the cleared dual pencil at a label list: the
pencil with the level's two members cross-added on the gram,
`P(σ) + y G − x G` at the level `⟨x : y⟩`. -/
def levelSite {L : Type} (F : fusion.Data L) (sd pr ls : List L) (sn c x y : Pos) :
    Mat :=
  inertia.siteDatum (matAdd (dualH F sd pr ls sn c) (inertia.matScale y (dualG c ls.length)))
    (inertia.matScale x (dualG c ls.length))

/-- The electric diagonal's order. -/
private theorem elecMat_len {L : Type} (F : fusion.Data L) (ls : List L) :
    (elecMat F ls).length = ls.length :=
  diagN_len _ _

private theorem elecMat_rows {L : Type} (F : fusion.Data L) (ls : List L) :
    rowsLen ls.length (elecMat F ls) :=
  diagN_rows _ _

/-- The closure fold's order. -/
private theorem closureMat_len {L : Type} (F : fusion.Data L) (sd pr ls : List L) :
    (fpcap.closureMat F sd pr ls).length = ls.length :=
  ground.length_map _ ls

private theorem closureMat_rows {L : Type} (F : fusion.Data L) (sd pr ls : List L) :
    rowsLen ls.length (fpcap.closureMat F sd pr ls) :=
  rowsLen_map _ ls.length ls (fun _ _ => ground.length_map _ ls)

/-- The dual pencil's square read. -/
theorem dualH_sq {L : Type} (F : fusion.Data L) (sd pr ls : List L) (sn c : Pos) :
    sqAt (dualH F sd pr ls sn c) ls.length :=
  pencil.sqAt_rayH _ _ ls.length (sqAt_of (elecMat_len F ls) (elecMat_rows F ls))
    (sqAt_of (closureMat_len F sd pr ls) (closureMat_rows F sd pr ls)) sn c

/-- The gram's square read. -/
theorem dualG_sq (c : Pos) (n : Nat) : sqAt (dualG c n) n :=
  inertia.sqAt_matScale n c _ (sqAt_idMat n)

/-- The level site's square read. -/
theorem levelSite_sq {L : Type} (F : fusion.Data L) (sd pr ls : List L) (sn c x y : Pos) :
    sqAt (levelSite F sd pr ls sn c x y) ls.length :=
  inertia.sqAt_siteDatum _ _ _
    (sqAt_matAdd _ _ _ (dualH_sq F sd pr ls sn c)
      (inertia.sqAt_matScale _ y _ (dualG_sq c ls.length)))
    (inertia.sqAt_matScale _ x _ (dualG_sq c ls.length))

/-- The closure fold's entry at a window key pair. -/
private theorem closureMat_entry {L : Type} (F : fusion.Data L) (sd pr ls : List L)
    (i j : Nat) (hi : i < ls.length) (hj : j < ls.length) :
    ground.getAt BPair.unit (ground.getAt [] (fpcap.closureMat F sd pr ls) i) j
      = BPair.ofNat (fpcap.closureCount F sd pr (ground.getAt F.unit ls j)
          (ground.getAt F.unit ls i)) := by
  show ground.getAt BPair.unit (ground.getAt [] (ls.map (fun x => ls.map (fun y =>
    BPair.ofNat (fpcap.closureCount F sd pr y x)))) i) j = _
  rw [ground.getAt_map F.unit [] _ ls i hi, ground.getAt_map F.unit BPair.unit _ ls j hj]

/-- The electric diagonal's entry at a window key pair. -/
private theorem elecMat_entry {L : Type} (F : fusion.Data L) (ls : List L)
    (i j : Nat) (hi : i < ls.length) (hj : j < ls.length) :
    ground.getAt BPair.unit (ground.getAt [] (elecMat F ls) i) j
      = if j = i then BPair.ofNat (4 * F.c2N (ground.getAt F.unit ls i)) else BPair.unit :=
  diagN_entry _ ls.length i j hi hj

/-- The gram's entry at a window key pair. -/
private theorem dualG_entry (c : Pos) (n i j : Nat) (hi : i < n) (hj : j < n) :
    ground.getAt BPair.unit (ground.getAt [] (dualG c n) i) j
      = (if j = i then BPair.ofNat 1 else BPair.unit).scale c := by
  show ground.getAt BPair.unit (ground.getAt [] (inertia.matScale c (idMat n)) i) j = _
  rw [inertia.matScale_entry c _ i j (by rw [length_idMat]; exact hi)
    (by rw [rowsLen_getAt _ i (rowsLen_idMat n) (by rw [length_idMat]; exact hi)]; exact hj),
    getAt_idMat n i j hi hj]

/-- The level site's entry at a window key pair: the electric read
at the diagonal against the count, the level's two members on the
gram. -/
theorem levelSite_entry {L : Type} (F : fusion.Data L) (sd pr ls : List L)
    (sn c x y : Pos) (i j : Nat) (hi : i < ls.length) (hj : j < ls.length) :
    ground.getAt BPair.unit (ground.getAt [] (levelSite F sd pr ls sn c x y) i) j
      = ((if j = i then BPair.ofNat (4 * F.c2N (ground.getAt F.unit ls i)) else BPair.unit).scale sn
          + ((BPair.ofNat (fpcap.closureCount F sd pr (ground.getAt F.unit ls j)
              (ground.getAt F.unit ls i))).scale c).swap
        + ((if j = i then BPair.ofNat 1 else BPair.unit).scale c).scale y)
        + (((if j = i then BPair.ofNat 1 else BPair.unit).scale c).scale x).swap := by
  have hH : sqAt (dualH F sd pr ls sn c) ls.length := dualH_sq F sd pr ls sn c
  have hGy : sqAt (inertia.matScale y (dualG c ls.length)) ls.length :=
    inertia.sqAt_matScale _ y _ (dualG_sq c ls.length)
  have hGx : sqAt (inertia.matScale x (dualG c ls.length)) ls.length :=
    inertia.sqAt_matScale _ x _ (dualG_sq c ls.length)
  have hA : sqAt (matAdd (dualH F sd pr ls sn c) (inertia.matScale y (dualG c ls.length)))
      ls.length := sqAt_matAdd _ _ _ hH hGy
  show ground.getAt BPair.unit (ground.getAt [] (inertia.siteDatum
    (matAdd (dualH F sd pr ls sn c) (inertia.matScale y (dualG c ls.length)))
    (inertia.matScale x (dualG c ls.length))) i) j = _
  rw [inertia.siteDatum_entry _ _ ls.length (rowsLen_of_sqAt hA) (rowsLen_of_sqAt hGx) i j
    (by rw [sqAt_len hA]; exact hi) (by rw [sqAt_len hGx]; exact hi) hj]
  rw [getAt_matAdd _ _ i (by rw [sqAt_len hH]; exact hi) (by rw [sqAt_len hGy]; exact hi),
    getAt_vecAdd _ _ j
      (by rw [rowsLen_getAt _ i (rowsLen_of_sqAt hH) (by rw [sqAt_len hH]; exact hi)]; exact hj)
      (by rw [rowsLen_getAt _ i (rowsLen_of_sqAt hGy) (by rw [sqAt_len hGy]; exact hi)]; exact hj)]
  have hE : sqAt (inertia.matScale sn (elecMat F ls)) ls.length :=
    inertia.sqAt_matScale _ sn _ (sqAt_of (elecMat_len F ls) (elecMat_rows F ls))
  have hM : sqAt (inertia.matScale c (fpcap.closureMat F sd pr ls)) ls.length :=
    inertia.sqAt_matScale _ c _ (sqAt_of (closureMat_len F sd pr ls) (closureMat_rows F sd pr ls))
  rw [show dualH F sd pr ls sn c = inertia.siteDatum (inertia.matScale sn (elecMat F ls))
      (inertia.matScale c (fpcap.closureMat F sd pr ls)) from rfl,
    inertia.siteDatum_entry _ _ ls.length (rowsLen_of_sqAt hE) (rowsLen_of_sqAt hM) i j
      (by rw [sqAt_len hE]; exact hi) (by rw [sqAt_len hM]; exact hi) hj,
    inertia.matScale_entry sn _ i j (by rw [elecMat_len]; exact hi)
      (by rw [rowsLen_getAt _ i (elecMat_rows F ls) (by rw [elecMat_len]; exact hi)]; exact hj),
    inertia.matScale_entry c _ i j (by rw [closureMat_len]; exact hi)
      (by rw [rowsLen_getAt _ i (closureMat_rows F sd pr ls)
        (by rw [closureMat_len]; exact hi)]; exact hj),
    elecMat_entry F ls i j hi hj, closureMat_entry F sd pr ls i j hi hj,
    inertia.matScale_entry y _ i j (by rw [sqAt_len (dualG_sq c ls.length)]; exact hi)
      (by rw [rowsLen_getAt _ i (rowsLen_of_sqAt (dualG_sq c ls.length))
        (by rw [sqAt_len (dualG_sq c ls.length)]; exact hi)]; exact hj),
    inertia.matScale_entry x _ i j (by rw [sqAt_len (dualG_sq c ls.length)]; exact hi)
      (by rw [rowsLen_getAt _ i (rowsLen_of_sqAt (dualG_sq c ls.length))
        (by rw [sqAt_len (dualG_sq c ls.length)]; exact hi)]; exact hj),
    dualG_entry c ls.length i j hi hj]


/-- The coupling's entry at an index pair: the swapped count. -/
private theorem coupN_entry (bb : Nat → Nat → Nat) (k m i j : Nat) (hi : i < k) (hj : j < m) :
    ground.getAt BPair.unit (ground.getAt [] (coupN bb k m) i) j = (BPair.ofNat (bb i j)).swap := by
  show ground.getAt BPair.unit (ground.getAt [] ((List.range k).map (fun i =>
    (List.range m).map (fun j => (BPair.ofNat (bb i j)).swap))) i) j = _
  rw [ground.getAt_map_range [] _ k i, if_pos hi, ground.getAt_map_range BPair.unit _ m j, if_pos hj]

/-- The coupling's balance partner at a head and an excluded list:
the closure fold's cross block at the clearing, swapped with the
pencil's magnetic member, rows over the head and columns over the
excluded block. -/
def coupSwap {L : Type} (F : fusion.Data L) (sd pr hd ex : List L) (c : Pos) : Mat :=
  coupN (fun i j => posVal c * fpcap.closureCount F sd pr (ground.getAt F.unit ex j)
    (ground.getAt F.unit hd i)) hd.length ex.length

private theorem coupSwap_len {L : Type} (F : fusion.Data L) (sd pr hd ex : List L) (c : Pos) :
    (coupSwap F sd pr hd ex c).length = hd.length :=
  coupN_len _ _ _

private theorem coupSwap_rows {L : Type} (F : fusion.Data L) (sd pr hd ex : List L) (c : Pos) :
    rowsLen ex.length (coupSwap F sd pr hd ex c) :=
  coupN_rows _ _ _

/-- The coupling's entry: the swapped cleared count. -/
private theorem coupSwap_entry {L : Type} (F : fusion.Data L) (sd pr hd ex : List L)
    (c : Pos) (i j : Nat) (hi : i < hd.length) (hj : j < ex.length) :
    ground.getAt BPair.unit (ground.getAt [] (coupSwap F sd pr hd ex c) i) j
      = (BPair.ofNat (posVal c * fpcap.closureCount F sd pr (ground.getAt F.unit ex j)
          (ground.getAt F.unit hd i))).swap :=
  coupN_entry _ hd.length ex.length i j hi hj

/-- The cleared count at the clearing's weighting. -/
private theorem clearedCount (c : Pos) (n : Nat) :
    ((BPair.ofNat n).scale c).swap.oneValue (BPair.ofNat (posVal c * n)).swap :=
  ground.swap_congr (BPair.oneValue_symm (BPair.oneValue_trans (BPair.ofNat_mul _ _)
    (BPair.ofPos_scale c _)))

/-- A unit-padded read: the unit-valued summands withdraw. -/
private theorem padUnit (X U1 U2 U3 : BPair) (h1 : U1.oneValue BPair.unit)
    (h2 : U2.oneValue BPair.unit) (h3 : U3.oneValue BPair.unit) :
    (U1 + X + U2 + U3.swap).oneValue X := by
  refine BPair.oneValue_trans (BPair.add_congr (BPair.add_congr
    (BPair.add_congr h1 (BPair.oneValue_refl X)) h2) (ground.swap_congr h3)) ?_
  show (BPair.unit + X + BPair.unit + BPair.unit).oneValue X
  refine BPair.oneValue_trans (BPair.add_unit _) ?_
  refine BPair.oneValue_trans (BPair.add_unit _) ?_
  exact BPair.unit_add X

/-- The level site at a joined window splits into the two windows'
sites with the coupling's balance partner at the block join, the
count symmetric at the joined window. -/
theorem levelSite_join {L : Type} (F : fusion.Data L) (sd pr hd ex : List L)
    (sn c x y : Pos) (hk : 0 < hd.length)
    (hsym : fpcap.symAtC F (fpcap.closureCount F sd pr) (hd ++ ex)) :
    matOneValue (levelSite F sd pr (hd ++ ex) sn c x y)
      (inertia.blockJoin (levelSite F sd pr hd sn c x y) (coupSwap F sd pr hd ex c)
        (levelSite F sd pr ex sn c x y)) := by
  have hlen : (hd ++ ex).length = hd.length + ex.length := ground.length_append hd ex
  have hL : sqAt (levelSite F sd pr (hd ++ ex) sn c x y) (hd.length + ex.length) :=
    sqAt_of ((sqAt_len (levelSite_sq F sd pr (hd ++ ex) sn c x y)).trans hlen)
      (rowsLen_cast hlen (rowsLen_of_sqAt (levelSite_sq F sd pr (hd ++ ex) sn c x y)))
  have hH := levelSite_sq F sd pr hd sn c x y
  have hE := levelSite_sq F sd pr ex sn c x y
  have hBl := coupSwap_len F sd pr hd ex c
  have hBr := coupSwap_rows F sd pr hd ex c
  have hBt : (transposeM (coupSwap F sd pr hd ex c)).length = ex.length :=
    length_transposeM _ hBr (by rw [hBl]; exact hk)
  have hBtr : rowsLen hd.length (transposeM (coupSwap F sd pr hd ex c)) :=
    rowsLen_cast hBl (rowsLen_transposeM _)
  refine matOne_of_entries _ _ (hd.length + ex.length) (sqAt_len hL) (rowsLen_of_sqAt hL)
    (inertia.length_blockJoin _ _ _ _ _ (sqAt_len hH) hBl hBt (sqAt_len hE))
    (inertia.rowsLen_blockJoin _ _ _ _ _ (rowsLen_of_sqAt hH) hBr hBtr (rowsLen_of_sqAt hE))
    (fun i j hi hj => ?_)
  rw [inertia.entry_blockJoin _ _ _ hk (sqAt_len hH) (rowsLen_of_sqAt hH) hBl hBr (sqAt_len hE) i j
      hi,
    levelSite_entry F sd pr (hd ++ ex) sn c x y i j (by rw [hlen]; exact hi) (by rw [hlen]; exact
        hj)]
  cases Nat.lt_or_ge i hd.length with
  | inl hik =>
    rw [if_pos hik]
    cases Nat.lt_or_ge j hd.length with
    | inl hjk =>
      rw [if_pos hjk, levelSite_entry F sd pr hd sn c x y i j hik hjk,
        ground.getAt_append F.unit hd ex i, if_pos hik,
        ground.getAt_append F.unit hd ex j, if_pos hjk]
      exact BPair.oneValue_refl _
    | inr hjk =>
      rw [if_neg (Nat.not_lt.mpr hjk)]
      have hjm : j - hd.length < ex.length := by
        have h1 : j - hd.length + hd.length < ex.length + hd.length := by
          rw [ground.subAdd hjk, Nat.add_comm ex.length hd.length]
          exact hj
        exact Nat.lt_of_add_lt_add_right h1
      have hne : ¬ (j = i) := fun h => absurd (h ▸ hjk) (Nat.not_le.mpr hik)
      rw [coupSwap_entry F sd pr hd ex c i (j - hd.length) hik hjm, if_neg hne, if_neg hne,
        ground.getAt_append F.unit hd ex i, if_pos hik,
        ground.getAt_append F.unit hd ex j, if_neg (Nat.not_lt.mpr hjk)]
      exact BPair.oneValue_trans (padUnit _ _ _ _ (BPair.unit_scale sn)
        (BPair.oneValue_trans (BPair.scale_congr y (BPair.unit_scale c)) (BPair.unit_scale y))
        (BPair.oneValue_trans (BPair.scale_congr x (BPair.unit_scale c)) (BPair.unit_scale x)))
        (clearedCount c _)
  | inr hik =>
    rw [if_neg (Nat.not_lt.mpr hik)]
    have him : i - hd.length < ex.length := by
      have h1 : i - hd.length + hd.length < ex.length + hd.length := by
        rw [ground.subAdd hik, Nat.add_comm ex.length hd.length]
        exact hi
      exact Nat.lt_of_add_lt_add_right h1
    cases Nat.lt_or_ge j hd.length with
    | inl hjk =>
      rw [if_pos hjk]
      have hne : ¬ (j = i) := fun h => absurd hjk (Nat.not_lt.mpr (by rw [h]; exact hik))
      have hsw := ground.beqEqOf (ground.all_range_read (hd ++ ex).length
        (ground.all_range_read (hd ++ ex).length hsym j (by rw [hlen]; exact hj)) i
        (by rw [hlen]; exact hi))
      rw [ground.getAt_append F.unit hd ex i, if_neg (Nat.not_lt.mpr hik),
        ground.getAt_append F.unit hd ex j, if_pos hjk] at hsw
      rw [coupSwap_entry F sd pr hd ex c j (i - hd.length) hjk him, if_neg hne, if_neg hne,
        ground.getAt_append F.unit hd ex i, if_neg (Nat.not_lt.mpr hik),
        ground.getAt_append F.unit hd ex j, if_pos hjk, hsw]
      exact BPair.oneValue_trans (padUnit _ _ _ _ (BPair.unit_scale sn)
        (BPair.oneValue_trans (BPair.scale_congr y (BPair.unit_scale c)) (BPair.unit_scale y))
        (BPair.oneValue_trans (BPair.scale_congr x (BPair.unit_scale c)) (BPair.unit_scale x)))
        (clearedCount c _)
    | inr hjk =>
      rw [if_neg (Nat.not_lt.mpr hjk)]
      have hjm : j - hd.length < ex.length := by
        have h1 : j - hd.length + hd.length < ex.length + hd.length := by
          rw [ground.subAdd hjk, Nat.add_comm ex.length hd.length]
          exact hj
        exact Nat.lt_of_add_lt_add_right h1
      rw [levelSite_entry F sd pr ex sn c x y (i - hd.length) (j - hd.length) him hjm,
        ground.getAt_append F.unit hd ex i, if_neg (Nat.not_lt.mpr hik),
        ground.getAt_append F.unit hd ex j, if_neg (Nat.not_lt.mpr hjk)]
      have hiff : (j = i) ↔ (j - hd.length = i - hd.length) := by
        constructor
        · intro h; rw [h]
        · intro h
          have h2 : j - hd.length + hd.length = i - hd.length + hd.length := by rw [h]
          rw [ground.subAdd hjk, ground.subAdd hik] at h2
          exact h2
      by_cases hji : j = i
      · rw [if_pos hji, if_pos (hiff.mp hji), if_pos hji, if_pos (hiff.mp hji)]
        exact BPair.oneValue_refl _
      · rw [if_neg hji, if_neg (fun h => hji (hiff.mpr h)), if_neg hji,
          if_neg (fun h => hji (hiff.mpr h))]
        exact BPair.oneValue_refl _

/-! ## The difference site's block reads -/

/-- A site datum's rows keep their widths. -/
private theorem rowsLen_site (n : Nat) (A B : Mat) (hA : rowsLen n A) (hB : rowsLen n B) :
    rowsLen n (inertia.siteDatum A B) :=
  rowsLen_matAdd n A (matSwap B) hA (rowsLen_matSwap n B hB)

/-- A site datum's row count at matched frames. -/
private theorem length_site (A B : Mat) (h : A.length = B.length) :
    (inertia.siteDatum A B).length = A.length :=
  length_matAdd A (matSwap B) (h.trans (length_matSwap B).symm)

/-- The site datum of two block joins is the block join of the
blockwise site data. -/
private theorem siteDatum_blockJoin {k m : Nat} (P B Q P' B' Q' : Mat) (hk : 0 < k)
    (hPl : P.length = k) (hPr : rowsLen k P) (hBl : B.length = k) (hBr : rowsLen m B)
    (hQl : Q.length = m) (hQr : rowsLen m Q)
    (hPl' : P'.length = k) (hPr' : rowsLen k P') (hBl' : B'.length = k) (hBr' : rowsLen m B')
    (hQl' : Q'.length = m) (hQr' : rowsLen m Q') :
    matOneValue (inertia.siteDatum (inertia.blockJoin P B Q) (inertia.blockJoin P' B' Q'))
      (inertia.blockJoin (inertia.siteDatum P P') (inertia.siteDatum B B')
        (inertia.siteDatum Q Q')) := by
  have hBt : (transposeM B).length = m := length_transposeM B hBr (by rw [hBl]; exact hk)
  have hBt' : (transposeM B').length = m := length_transposeM B' hBr' (by rw [hBl']; exact hk)
  have hJl : (inertia.blockJoin P B Q).length = k + m :=
    inertia.length_blockJoin _ _ _ _ _ hPl hBl hBt hQl
  have hJr : rowsLen (k + m) (inertia.blockJoin P B Q) :=
    inertia.rowsLen_blockJoin _ _ _ _ _ hPr hBr (rowsLen_cast hBl (rowsLen_transposeM B)) hQr
  have hJl' : (inertia.blockJoin P' B' Q').length = k + m :=
    inertia.length_blockJoin _ _ _ _ _ hPl' hBl' hBt' hQl'
  have hJr' : rowsLen (k + m) (inertia.blockJoin P' B' Q') :=
    inertia.rowsLen_blockJoin _ _ _ _ _ hPr' hBr' (rowsLen_cast hBl' (rowsLen_transposeM B')) hQr'
  have hSPl : (inertia.siteDatum P P').length = k := (length_site P P' (hPl.trans
      hPl'.symm)).trans hPl
  have hSPr : rowsLen k (inertia.siteDatum P P') := rowsLen_site k P P' hPr hPr'
  have hSBl : (inertia.siteDatum B B').length = k := (length_site B B' (hBl.trans
      hBl'.symm)).trans hBl
  have hSBr : rowsLen m (inertia.siteDatum B B') := rowsLen_site m B B' hBr hBr'
  have hSQl : (inertia.siteDatum Q Q').length = m := (length_site Q Q' (hQl.trans
      hQl'.symm)).trans hQl
  have hSQr : rowsLen m (inertia.siteDatum Q Q') := rowsLen_site m Q Q' hQr hQr'
  have hSBt : (transposeM (inertia.siteDatum B B')).length = m :=
    length_transposeM _ hSBr (by rw [hSBl]; exact hk)
  refine matOne_of_entries _ _ (k + m)
    ((length_site _ _ (hJl.trans hJl'.symm)).trans hJl) (rowsLen_site _ _ _ hJr hJr')
    (inertia.length_blockJoin _ _ _ _ _ hSPl hSBl hSBt hSQl)
    (inertia.rowsLen_blockJoin _ _ _ _ _ hSPr hSBr (rowsLen_cast hSBl (rowsLen_transposeM _)) hSQr)
    (fun i j hi hj => ?_)
  rw [inertia.siteDatum_entry _ _ (k + m) hJr hJr' i j (by rw [hJl]; exact hi)
      (by rw [hJl']; exact hi) hj,
    inertia.entry_blockJoin P B Q hk hPl hPr hBl hBr hQl i j hi,
    inertia.entry_blockJoin P' B' Q' hk hPl' hPr' hBl' hBr' hQl' i j hi,
    inertia.entry_blockJoin _ _ _ hk hSPl hSPr hSBl hSBr hSQl i j hi]
  cases Nat.lt_or_ge i k with
  | inl hik =>
    rw [if_pos hik, if_pos hik, if_pos hik]
    cases Nat.lt_or_ge j k with
    | inl hjk =>
      rw [if_pos hjk, if_pos hjk, if_pos hjk,
        inertia.siteDatum_entry P P' k hPr hPr' i j (by rw [hPl]; exact hik)
          (by rw [hPl']; exact hik) hjk]
      exact BPair.oneValue_refl _
    | inr hjk =>
      have hjm : j - k < m := by
        have h1 : j - k + k < m + k := by
          rw [ground.subAdd hjk, Nat.add_comm m k]
          exact hj
        exact Nat.lt_of_add_lt_add_right h1
      rw [if_neg (Nat.not_lt.mpr hjk), if_neg (Nat.not_lt.mpr hjk), if_neg (Nat.not_lt.mpr hjk),
        inertia.siteDatum_entry B B' m hBr hBr' i (j - k) (by rw [hBl]; exact hik)
          (by rw [hBl']; exact hik) hjm]
      exact BPair.oneValue_refl _
  | inr hik =>
    have him : i - k < m := by
      have h1 : i - k + k < m + k := by
        rw [ground.subAdd hik, Nat.add_comm m k]
        exact hi
      exact Nat.lt_of_add_lt_add_right h1
    rw [if_neg (Nat.not_lt.mpr hik), if_neg (Nat.not_lt.mpr hik), if_neg (Nat.not_lt.mpr hik)]
    cases Nat.lt_or_ge j k with
    | inl hjk =>
      rw [if_pos hjk, if_pos hjk, if_pos hjk,
        inertia.siteDatum_entry B B' m hBr hBr' j (i - k) (by rw [hBl]; exact hjk)
          (by rw [hBl']; exact hjk) him]
      exact BPair.oneValue_refl _
    | inr hjk =>
      have hjm : j - k < m := by
        have h1 : j - k + k < m + k := by
          rw [ground.subAdd hjk, Nat.add_comm m k]
          exact hj
        exact Nat.lt_of_add_lt_add_right h1
      rw [if_neg (Nat.not_lt.mpr hjk), if_neg (Nat.not_lt.mpr hjk), if_neg (Nat.not_lt.mpr hjk),
        inertia.siteDatum_entry Q Q' m hQr hQr' (i - k) (j - k) (by rw [hQl]; exact him)
          (by rw [hQl']; exact him) hjm]
      exact BPair.oneValue_refl _

/-- A datum against its own withdrawal reads the withdrawn part:
`X − (X − Y)` is `Y`. -/
private theorem siteDiff_read (X Y : Mat) (n : Nat) (hX : sqAt X n) (hY : sqAt Y n) :
    matOneValue (inertia.siteDatum X (inertia.siteDatum X Y)) Y := by
  have hXY : sqAt (inertia.siteDatum X Y) n := inertia.sqAt_siteDatum n X Y hX hY
  refine matOne_of_entries _ _ n
    ((length_site _ _ ((sqAt_len hX).trans (sqAt_len hXY).symm)).trans (sqAt_len hX))
    (rowsLen_site n _ _ (rowsLen_of_sqAt hX) (rowsLen_of_sqAt hXY))
    (sqAt_len hY) (rowsLen_of_sqAt hY) (fun i j hi hj => ?_)
  rw [inertia.siteDatum_entry _ _ n (rowsLen_of_sqAt hX) (rowsLen_of_sqAt hXY) i j
      (by rw [sqAt_len hX]; exact hi) (by rw [sqAt_len hXY]; exact hi) hj,
    inertia.siteDatum_entry X Y n (rowsLen_of_sqAt hX) (rowsLen_of_sqAt hY) i j
      (by rw [sqAt_len hX]; exact hi) (by rw [sqAt_len hY]; exact hi) hj,
    ← BPair.swap_add, BPair.swap_swap, ← BPair.add_assoc]
  exact BPair.oneValue_trans (BPair.add_congr (BPair.add_swap_null _) (BPair.oneValue_refl _))
    (BPair.unit_add _)

/-- A datum padded by a scaled identity on both sides of its site
reads itself. -/
private theorem sitePad_read (P : Mat) (n : Nat) (a : Pos) (hP : sqAt P n) :
    matOneValue (inertia.siteDatum (matAdd P (inertia.matScale a (idMat n)))
      (inertia.matScale a (idMat n))) P := by
  have hI : sqAt (inertia.matScale a (idMat n)) n := inertia.sqAt_matScale n a _ (sqAt_idMat n)
  have hA : sqAt (matAdd P (inertia.matScale a (idMat n))) n := sqAt_matAdd n _ _ hP hI
  refine matOne_of_entries _ _ n
    ((length_site _ _ ((sqAt_len hA).trans (sqAt_len hI).symm)).trans (sqAt_len hA))
    (rowsLen_site n _ _ (rowsLen_of_sqAt hA) (rowsLen_of_sqAt hI))
    (sqAt_len hP) (rowsLen_of_sqAt hP) (fun i j hi hj => ?_)
  rw [inertia.siteDatum_entry _ _ n (rowsLen_of_sqAt hA) (rowsLen_of_sqAt hI) i j
      (by rw [sqAt_len hA]; exact hi) (by rw [sqAt_len hI]; exact hi) hj,
    getAt_matAdd _ _ i (by rw [sqAt_len hP]; exact hi) (by rw [sqAt_len hI]; exact hi),
    getAt_vecAdd _ _ j
      (by rw [rowsLen_getAt _ i (rowsLen_of_sqAt hP) (by rw [sqAt_len hP]; exact hi)]; exact hj)
      (by rw [rowsLen_getAt _ i (rowsLen_of_sqAt hI) (by rw [sqAt_len hI]; exact hi)]; exact hj),
    BPair.add_assoc]
  exact BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_swap_null _))
    (BPair.add_unit _)

/-- A datum against the null block reads itself. -/
private theorem siteNull_read {k m : Nat} (B : Mat) (hBl : B.length = k) (hBr : rowsLen m B) :
    matOneValue (inertia.siteDatum B (nullMat k m)) B := by
  show matOneValue (matAdd B (matSwap (nullMat k m))) B
  rw [matAdd_comm]
  exact matAdd_nullL (matSwap (nullMat k m)) B (matNull_matSwap _ (matNull_nullMat m k))
    ((length_matSwap _).trans ((length_nullMat k m).trans hBl.symm))
    (rowsLen_matSwap m _ (rowsLen_nullMat k m)) hBr

/-! ## The symmetry reads of the sandwich's own data: every
intermediate datum is symmetric, so `inertia.mkSplit` reads it
(`lem:inertia`: every symmetric datum has a split), the generic reads
`elim.symmRead_matSwap`, `inertia.symmRead_siteDatum`,
`inertia.symmRead_matScale`, `inertia.symmRead_matScaleB` and
`elim.symmRead_idMat` bridged at `matOne_symm`. -/

private theorem sym_diagN (dd : Nat → Nat) (k : Nat) :
    matOneValue (transposeM (diagN dd k)) (diagN dd k) := by
  have hl := diagN_len dd k
  have hr := diagN_rows dd k
  refine matOne_of_entries _ _ k (length_transposeM_sq _ (sqAt_of hl hr))
    (rowsLen_cast hl (rowsLen_transposeM _)) hl hr (fun i j hi hj => ?_)
  rw [getAt_transposeM BPair.unit _ hr i j hi (by rw [hl]; exact hj),
    diagN_entry dd k j i hj hi, diagN_entry dd k i j hi hj]
  by_cases hij : i = j
  · subst hij
    exact BPair.oneValue_refl _
  · rw [if_neg hij, if_neg (fun h => hij h.symm)]
    exact BPair.oneValue_refl _

private theorem sym_closureMat {L : Type} (F : fusion.Data L) (sd pr ls : List L)
    (hsym : fpcap.symAtC F (fpcap.closureCount F sd pr) ls) :
    matOneValue (transposeM (fpcap.closureMat F sd pr ls)) (fpcap.closureMat F sd pr ls) := by
  have hl := closureMat_len F sd pr ls
  have hr := closureMat_rows F sd pr ls
  refine matOne_of_entries _ _ ls.length (length_transposeM_sq _ (sqAt_of hl hr))
    (rowsLen_cast hl (rowsLen_transposeM _)) hl hr (fun i j hi hj => ?_)
  rw [getAt_transposeM BPair.unit _ hr i j hi (by rw [hl]; exact hj),
    closureMat_entry F sd pr ls j i hj hi, closureMat_entry F sd pr ls i j hi hj,
    fpcap.symRead hsym i j hi hj]
  exact BPair.oneValue_refl _

/-- The level site is symmetric at the closure fold's symmetry. -/
theorem levelSite_sym {L : Type} (F : fusion.Data L) (sd pr ls : List L) (sn c x y : Pos)
    (hsym : fpcap.symAtC F (fpcap.closureCount F sd pr) ls) :
    matOneValue (transposeM (levelSite F sd pr ls sn c x y)) (levelSite F sd pr ls sn c x y) := by
  have hE : sqAt (elecMat F ls) ls.length := sqAt_of (elecMat_len F ls) (elecMat_rows F ls)
  have hM : sqAt (fpcap.closureMat F sd pr ls) ls.length :=
    sqAt_of (closureMat_len F sd pr ls) (closureMat_rows F sd pr ls)
  have hG := dualG_sq c ls.length
  have hH : sqAt (dualH F sd pr ls sn c) ls.length := dualH_sq F sd pr ls sn c
  have hsG : matOneValue (transposeM (dualG c ls.length)) (dualG c ls.length) :=
    (matOne_symm (inertia.symmRead_matScale c _ _ (sqAt_idMat _) (symmRead_idMat _)))
  have hsH : matOneValue (transposeM (dualH F sd pr ls sn c)) (dualH F sd pr ls sn c) :=
    (matOne_symm (inertia.symmRead_siteDatum _ _ _ (inertia.sqAt_matScale _ sn _ hE)
        (inertia.sqAt_matScale _ c _ hM) (inertia.symmRead_matScale sn _ _ hE (matOne_symm
        (sym_diagN _ _))) (inertia.symmRead_matScale c _ _ hM (matOne_symm (sym_closureMat F sd pr
        ls hsym)))))
  exact (matOne_symm (inertia.symmRead_siteDatum _ _ _ (sqAt_matAdd _ _ _ hH (inertia.sqAt_matScale
      _ y _ hG)) (inertia.sqAt_matScale _ x _ hG) (matOne_symm (transposeM_matAdd_sym _ _ hH
      (inertia.sqAt_matScale _ y _ hG) hsH ((matOne_symm (inertia.symmRead_matScale y _ _ hG
      (matOne_symm hsG)))))) (inertia.symmRead_matScale x _ _ hG (matOne_symm hsG))))

/-! ## The forms -/

/-- The site datum's form: the two forms at the balance partner. -/
private theorem quadSite {n : Nat} (A B : Mat) (hA : sqAt A n) (hB : sqAt B n)
    (u : List BPair) (hu : u.length = n) :
    (inertia.quadForm (inertia.siteDatum A B) u).oneValue
      (inertia.quadForm A u + (inertia.quadForm B u).swap) := by
  refine BPair.oneValue_trans (inertia.quadForm_add A (matSwap B) u
    ((sqAt_len hA).trans hu.symm) (rowsLen_cast hu.symm (rowsLen_of_sqAt hA))
    ((length_matSwap B).trans ((sqAt_len hB).trans hu.symm))
    (rowsLen_cast hu.symm (rowsLen_mapRows BPair.swap B n (rowsLen_of_sqAt hB)))) ?_
  exact BPair.add_congr (BPair.oneValue_refl _) (inertia.quadForm_swap B u)

/-- The level site's form: the electric form at the scale, the
closure fold's form at the clearing on the balance side, and the
level's two members at the cleared self-pairing. -/
theorem quadLevel {L : Type} (F : fusion.Data L) (sd pr ls : List L) (sn c x y : Pos)
    (u : List BPair) (hu : u.length = ls.length) :
    (inertia.quadForm (levelSite F sd pr ls sn c x y) u).oneValue
      ((inertia.quadForm (elecMat F ls) u).scale sn
        + ((inertia.quadForm (fpcap.closureMat F sd pr ls) u).scale c).swap
        + (dotN u u).scale (y * c) + ((dotN u u).scale (x * c)).swap) := by
  have hE : sqAt (elecMat F ls) ls.length := sqAt_of (elecMat_len F ls) (elecMat_rows F ls)
  have hM : sqAt (fpcap.closureMat F sd pr ls) ls.length :=
    sqAt_of (closureMat_len F sd pr ls) (closureMat_rows F sd pr ls)
  have hG := dualG_sq c ls.length
  have hH := dualH_sq F sd pr ls sn c
  have hGy : sqAt (inertia.matScale y (dualG c ls.length)) ls.length :=
    inertia.sqAt_matScale _ y _ hG
  have hGx : sqAt (inertia.matScale x (dualG c ls.length)) ls.length :=
    inertia.sqAt_matScale _ x _ hG
  have hidG : ∀ w : Pos, (inertia.quadForm (inertia.matScale w (dualG c ls.length)) u).oneValue
      ((dotN u u).scale (w * c)) := by
    intro w
    show (inertia.quadForm (inertia.matScale w (inertia.matScale c (idMat ls.length))) u).oneValue _
    rw [inertia.matScale_matScale]
    exact BPair.oneValue_trans (inertia.quadForm_scale _ _ u)
      (BPair.scale_congr _ (inertia.quadForm_idMat _ u hu))
  refine BPair.oneValue_trans (quadSite _ _ (sqAt_matAdd _ _ _ hH hGy) hGx u hu) ?_
  refine BPair.add_congr ?_ (ground.swap_congr (hidG x))
  refine BPair.oneValue_trans (inertia.quadForm_add _ _ u ((sqAt_len hH).trans hu.symm)
    (rowsLen_cast hu.symm (rowsLen_of_sqAt hH)) ((sqAt_len hGy).trans hu.symm)
    (rowsLen_cast hu.symm (rowsLen_of_sqAt hGy))) ?_
  refine BPair.add_congr ?_ (hidG y)
  show (inertia.quadForm (inertia.siteDatum (inertia.matScale sn (elecMat F ls))
    (inertia.matScale c (fpcap.closureMat F sd pr ls))) u).oneValue _
  refine BPair.oneValue_trans (quadSite _ _ (inertia.sqAt_matScale _ sn _ hE)
    (inertia.sqAt_matScale _ c _ hM) u hu) ?_
  exact BPair.add_congr (inertia.quadForm_scale sn _ u)
    (ground.swap_congr (inertia.quadForm_scale c _ u))

/-! ## The excluded block's floor -/

/-- The excluded block's read: every member's Casimir beyond the
cutoff, the cutoff's own read (`lem:contactcell`). -/
def beyondAt {L : Type} (F : fusion.Data L) (K : Nat) (ex : List L) : Prop :=
  (ex.all (fun l => decide (K < F.c2N l))) = true

instance instContactcellB {L : Type} (F : fusion.Data L) (K : Nat) (ex : List L) :
    Decidable (beyondAt F K ex) :=
  inferInstanceAs (Decidable (_ = _))

/-- The excluded block at two cutoffs is beyond the first, the
cutoff's own read. -/
theorem exclAt_beyond {L : Type} (F : fusion.Data L) (sd pr : List L) (K K' : Nat) :
    beyondAt F K (exclAt F sd pr K K') :=
  ground.all_of_mem_intro _ _ (fun l hl => (ground.mem_filter_of _ _ l hl).2)

/-- The closure fold's cross block at a head and an excluded list:
the counts at the head's rows and the excluded block's columns. -/
def crossMat {L : Type} (F : fusion.Data L) (sd pr hd ex : List L) : Mat :=
  hd.map (fun a => ex.map (fun b => BPair.ofNat (fpcap.closureCount F sd pr b a)))

private theorem crossMat_len {L : Type} (F : fusion.Data L) (sd pr hd ex : List L) :
    (crossMat F sd pr hd ex).length = hd.length := ground.length_map _ hd

private theorem crossMat_rows {L : Type} (F : fusion.Data L) (sd pr hd ex : List L) :
    rowsLen ex.length (crossMat F sd pr hd ex) :=
  rowsLen_map _ ex.length hd (fun _ _ => ground.length_map _ ex)

private theorem crossMat_entry {L : Type} (F : fusion.Data L) (sd pr hd ex : List L)
    (i j : Nat) (hi : i < hd.length) (hj : j < ex.length) :
    ground.getAt BPair.unit (ground.getAt [] (crossMat F sd pr hd ex) i) j
      = BPair.ofNat (fpcap.closureCount F sd pr (ground.getAt F.unit ex j)
          (ground.getAt F.unit hd i)) := by
  show ground.getAt BPair.unit (ground.getAt [] (hd.map (fun a => ex.map (fun b =>
    BPair.ofNat (fpcap.closureCount F sd pr b a)))) i) j = _
  rw [ground.getAt_map F.unit [] _ hd i hi, ground.getAt_map F.unit BPair.unit _ ex j hj]

/-- The closure fold at a joined window splits into the two windows'
folds with the cross block, the count symmetric at the joined
window. -/
theorem closureMat_join {L : Type} (F : fusion.Data L) (sd pr hd ex : List L)
    (hk : 0 < hd.length)
    (hsym : fpcap.symAtC F (fpcap.closureCount F sd pr) (hd ++ ex)) :
    matOneValue (fpcap.closureMat F sd pr (hd ++ ex))
      (inertia.blockJoin (fpcap.closureMat F sd pr hd) (crossMat F sd pr hd ex)
        (fpcap.closureMat F sd pr ex)) := by
  have hlen : (hd ++ ex).length = hd.length + ex.length := ground.length_append hd ex
  have hAl : (fpcap.closureMat F sd pr (hd ++ ex)).length = hd.length + ex.length :=
    (closureMat_len F sd pr _).trans hlen
  have hAr : rowsLen (hd.length + ex.length) (fpcap.closureMat F sd pr (hd ++ ex)) :=
    rowsLen_cast hlen (closureMat_rows F sd pr _)
  have hBl := crossMat_len F sd pr hd ex
  have hBr := crossMat_rows F sd pr hd ex
  have hBt : (transposeM (crossMat F sd pr hd ex)).length = ex.length :=
    length_transposeM _ hBr (by rw [hBl]; exact hk)
  refine matOne_of_entries _ _ (hd.length + ex.length) hAl hAr
    (inertia.length_blockJoin _ _ _ _ _ (closureMat_len F sd pr hd) hBl hBt (closureMat_len F sd pr
        ex))
    (inertia.rowsLen_blockJoin _ _ _ _ _ (closureMat_rows F sd pr hd) hBr
      (rowsLen_cast hBl (rowsLen_transposeM _)) (closureMat_rows F sd pr ex))
    (fun i j hi hj => ?_)
  rw [inertia.entry_blockJoin _ _ _ hk (closureMat_len F sd pr hd) (closureMat_rows F sd pr hd) hBl
      hBr (closureMat_len F sd pr ex) i j hi,
    closureMat_entry F sd pr (hd ++ ex) i j (by rw [hlen]; exact hi) (by rw [hlen]; exact hj)]
  cases Nat.lt_or_ge i hd.length with
  | inl hik =>
    rw [if_pos hik]
    cases Nat.lt_or_ge j hd.length with
    | inl hjk =>
      rw [if_pos hjk, closureMat_entry F sd pr hd i j hik hjk,
        ground.getAt_append F.unit hd ex i, if_pos hik,
        ground.getAt_append F.unit hd ex j, if_pos hjk]
      exact BPair.oneValue_refl _
    | inr hjk =>
      rw [if_neg (Nat.not_lt.mpr hjk)]
      have hjm : j - hd.length < ex.length := by
        have h1 : j - hd.length + hd.length < ex.length + hd.length := by
          rw [ground.subAdd hjk, Nat.add_comm ex.length hd.length]
          exact hj
        exact Nat.lt_of_add_lt_add_right h1
      rw [crossMat_entry F sd pr hd ex i (j - hd.length) hik hjm,
        ground.getAt_append F.unit hd ex i, if_pos hik,
        ground.getAt_append F.unit hd ex j, if_neg (Nat.not_lt.mpr hjk)]
      exact BPair.oneValue_refl _
  | inr hik =>
    rw [if_neg (Nat.not_lt.mpr hik)]
    have him : i - hd.length < ex.length := by
      have h1 : i - hd.length + hd.length < ex.length + hd.length := by
        rw [ground.subAdd hik, Nat.add_comm ex.length hd.length]
        exact hi
      exact Nat.lt_of_add_lt_add_right h1
    cases Nat.lt_or_ge j hd.length with
    | inl hjk =>
      rw [if_pos hjk]
      have hsw := fpcap.symRead hsym j i (by rw [hlen]; exact hj) (by rw [hlen]; exact hi)
      rw [ground.getAt_append F.unit hd ex i, if_neg (Nat.not_lt.mpr hik),
        ground.getAt_append F.unit hd ex j, if_pos hjk] at hsw
      rw [crossMat_entry F sd pr hd ex j (i - hd.length) hjk him,
        ground.getAt_append F.unit hd ex i, if_neg (Nat.not_lt.mpr hik),
        ground.getAt_append F.unit hd ex j, if_pos hjk, hsw]
      exact BPair.oneValue_refl _
    | inr hjk =>
      rw [if_neg (Nat.not_lt.mpr hjk)]
      have hjm : j - hd.length < ex.length := by
        have h1 : j - hd.length + hd.length < ex.length + hd.length := by
          rw [ground.subAdd hjk, Nat.add_comm ex.length hd.length]
          exact hj
        exact Nat.lt_of_add_lt_add_right h1
      rw [closureMat_entry F sd pr ex (i - hd.length) (j - hd.length) him hjm,
        ground.getAt_append F.unit hd ex i, if_neg (Nat.not_lt.mpr hik),
        ground.getAt_append F.unit hd ex j, if_neg (Nat.not_lt.mpr hjk)]
      exact BPair.oneValue_refl _

/-- A block join's form at a vector vacant on the head is the
trailing block's form. -/
private theorem quadPadL {k m : Nat} (P B Q : Mat) (hk : 0 < k) (hP : sqAt P k)
    (hBl : B.length = k) (hBr : rowsLen m B) (hQ : sqAt Q m)
    (u : List BPair) (hu : u.length = m) :
    (inertia.quadForm (inertia.blockJoin P B Q) (List.replicate k BPair.unit ++ u)).oneValue
      (inertia.quadForm Q u) := by
  have hBt : (transposeM B).length = m := length_transposeM B hBr (by rw [hBl]; exact hk)
  have hBtr : rowsLen k (transposeM B) := rowsLen_cast hBl (rowsLen_transposeM B)
  have hz : (List.replicate k BPair.unit).length = k := ground.length_replicate _ k
  have hU := poly.unitTail_replicate k
  refine BPair.oneValue_trans (inertia.quadJoin P B Q k m (rowsLen_of_sqAt hP) (sqAt_len hP)
    hBl hBt hBtr (sqAt_len hQ) _ u _ u hz hu hz) ?_
  refine BPair.oneValue_trans (BPair.add_congr
    (BPair.add_congr (dotN_nullL _ _ hU) (dotN_nullL _ _ hU))
    (BPair.add_congr (dotN_nullR _ _ (matVec_null _ _ hU)) (BPair.oneValue_refl _))) ?_
  exact BPair.oneValue_trans (BPair.add_congr (BPair.unit_add _) (BPair.unit_add _))
    (BPair.unit_add _)

/-- The self-pairing at a vector vacant on the head. -/
private theorem dotNPad (k : Nat) (u : List BPair) :
    (dotN (List.replicate k BPair.unit ++ u) (List.replicate k BPair.unit ++ u)).oneValue
      (dotN u u) := by
  refine BPair.oneValue_trans (dotN_read _ _) ?_
  refine BPair.oneValue_trans (dotP_append _ _ _ _ rfl) ?_
  refine BPair.oneValue_trans (BPair.add_congr
    (dotP_null_tail_left _ _ (poly.unitTail_replicate k)) (BPair.oneValue_refl _)) ?_
  exact BPair.oneValue_trans (BPair.unit_add _) (BPair.oneValue_symm (dotN_read u u))

/-- The magnetic form cap is kept by the excluded principal block:
the closure fold's cap at the joined window, read at the vectors
vacant on the head (`lem:fpcap`; `lem:inertia`'s compression). -/
theorem capBlock {L : Type} (F : fusion.Data L) (sd pr hd ex : List L) (hk : 0 < hd.length)
    (hsym : fpcap.symAtC F (fpcap.closureCount F sd pr) (hd ++ ex))
    (hcap : ∀ u : List BPair, u.length = (hd ++ ex).length →
      ¬ (BPair.ofNat (fpcap.dimFold F sd pr) * dotN u u
          < inertia.quadForm (fpcap.closureMat F sd pr (hd ++ ex)) u))
    (u : List BPair) (hu : u.length = ex.length) :
    ¬ (BPair.ofNat (fpcap.dimFold F sd pr) * dotN u u
        < inertia.quadForm (fpcap.closureMat F sd pr ex) u) := by
  intro hlt
  have hlen : (List.replicate hd.length BPair.unit ++ u).length = (hd ++ ex).length := by
    rw [ground.length_append, ground.length_replicate, hu, ground.length_append]
  refine hcap _ hlen ?_
  refine BPair.lt_congr (BPair.mul_congr (BPair.oneValue_refl _)
    (BPair.oneValue_symm (dotNPad hd.length u))) ?_ hlt
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans (quadForm_matOne _ _ _ (closureMat_join F sd pr hd ex hk hsym)) ?_
  exact quadPadL _ _ _ hk (sqAt_of (closureMat_len F sd pr hd) (closureMat_rows F sd pr hd))
    (crossMat_len F sd pr hd ex) (crossMat_rows F sd pr hd ex)
    (sqAt_of (closureMat_len F sd pr ex) (closureMat_rows F sd pr ex)) u hu

/-- The excluded block sits at or above the seed floor: at a level
below `F`, the scale times the block's Casimir floor against the
magnetic cap clears the level's gap on the self-pairing
(`lem:contactcell`). -/
theorem exclFloor {L : Type} (F : fusion.Data L) (sd pr ex : List L) (K : Nat)
    (sn c x y g : Pos) (hex : beyondAt F K ex)
    (hcap : ∀ u : List BPair, u.length = ex.length →
      ¬ (BPair.ofNat (fpcap.dimFold F sd pr) * dotN u u
          < inertia.quadForm (fpcap.closureMat F sd pr ex) u))
    (hg : (posVal x + fpcap.dimFold F sd pr) * posVal c + posVal g
      = 4 * posVal sn * K + posVal y * posVal c)
    (u : List BPair) (hu : u.length = ex.length) :
    (dotN u u).scale g ≤ inertia.quadForm (levelSite F sd pr ex sn c x y) u := by
  have hA : BPair.ofNat (4 * K) * dotN u u ≤ inertia.quadForm (elecMat F ex) u := by
    refine leB_congr (BPair.oneValue_symm (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _) (selfFold u ex.length hu))
        (BPair.oneValue_symm (foldB_mul_left _ _ (List.range ex.length)))))
      (BPair.oneValue_symm (quadDiagN _ ex.length u hu)) ?_
    refine bsum_le_of_mem _ _ (List.range ex.length) (fun i hi => ?_)
    have hin : i < ex.length := ground.ltOfMemRange hi
    have hK : K < F.c2N (ground.getAt F.unit ex i) :=
      of_decide_eq_true (ground.all_of_mem _ ex hex _ (ground.mem_getAt F.unit ex i hin))
    exact leB_scale_mono (Nat.mul_le_mul_left 4 (Nat.le_of_lt hK)) (ground.unitLeSq _)
  have hM : inertia.quadForm (fpcap.closureMat F sd pr ex) u
      ≤ BPair.ofNat (fpcap.dimFold F sd pr) * dotN u u := leB_of_not_lt (hcap u hu)
  -- the join identity cast to the pair carrier
  have hid : ((BPair.ofNat (posVal x) + BPair.ofNat (fpcap.dimFold F sd pr)) * BPair.ofNat (posVal
      c)
        + BPair.ofNat (posVal g)).oneValue
      (BPair.ofNat (posVal sn) * BPair.ofNat (4 * K)
        + BPair.ofNat (posVal y) * BPair.ofNat (posVal c)) := by
    have hcast : BPair.ofNat ((posVal x + fpcap.dimFold F sd pr) * posVal c + posVal g)
        = BPair.ofNat (4 * posVal sn * K + posVal y * posVal c) := congrArg BPair.ofNat hg
    refine BPair.oneValue_trans (BPair.oneValue_symm (BPair.oneValue_trans (BPair.ofNat_add _ _)
      (BPair.add_congr (BPair.oneValue_trans (BPair.ofNat_mul _ _)
        (BPair.mul_congr_left (BPair.ofNat_add _ _))) (BPair.oneValue_refl _)))) ?_
    rw [hcast]
    refine BPair.oneValue_trans (BPair.ofNat_add _ _) ?_
    refine BPair.add_congr ?_ (BPair.ofNat_mul _ _)
    refine BPair.oneValue_trans (BPair.ofNat_mul _ _) ?_
    refine BPair.oneValue_trans (BPair.mul_congr_left (BPair.ofNat_mul _ _)) ?_
    refine BPair.oneValue_trans ?_ (BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (BPair.ofNat_mul 4 K)))
    exact polEqB [BPair.ofNat 4, BPair.ofNat (posVal sn), BPair.ofNat K]
      (Pol.mul (Pol.mul (pv 0) (pv 1)) (pv 2)) (Pol.mul (pv 1) (Pol.mul (pv 0) (pv 2)))
      (by decide +kernel)
  -- the moved comparison
  have hmain : BPair.ofPos g * dotN u u
      + ((BPair.ofPos x * BPair.ofPos c) * dotN u u
        + BPair.ofPos c * inertia.quadForm (fpcap.closureMat F sd pr ex) u)
      ≤ BPair.ofPos sn * inertia.quadForm (elecMat F ex) u
        + (BPair.ofPos y * BPair.ofPos c) * dotN u u := by
    refine leB_trans (leB_add (leB_refl _) (leB_add (leB_refl _)
      (ground.leB_mulR (Or.inr (ground.unitLtOfPos c)) hM))) ?_
    refine leB_congr_left ?_ (leB_add (ground.leB_mulR (Or.inr (ground.unitLtOfPos sn)) hA)
      (leB_refl ((BPair.ofPos y * BPair.ofPos c) * dotN u u)))
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans (polEqB [BPair.ofPos g, dotN u u, BPair.ofPos x, BPair.ofPos c,
        BPair.ofNat (fpcap.dimFold F sd pr)]
      (Pol.add (Pol.mul (pv 0) (pv 1)) (Pol.add (Pol.mul (Pol.mul (pv 2) (pv 3)) (pv 1))
        (Pol.mul (pv 3) (Pol.mul (pv 4) (pv 1)))))
      (Pol.mul (Pol.add (Pol.mul (Pol.add (pv 2) (pv 4)) (pv 3)) (pv 0)) (pv 1))
      (by decide +kernel)) ?_
    refine BPair.oneValue_trans (BPair.mul_congr_left hid) ?_
    exact polEqB [BPair.ofPos sn, BPair.ofNat (4 * K), BPair.ofPos y, BPair.ofPos c, dotN u u]
      (Pol.mul (Pol.add (Pol.mul (pv 0) (pv 1)) (Pol.mul (pv 2) (pv 3))) (pv 4))
      (Pol.add (Pol.mul (pv 0) (Pol.mul (pv 1) (pv 4))) (Pol.mul (Pol.mul (pv 2) (pv 3)) (pv 4)))
      (by decide +kernel)
  have hmoved := ground.leB_swapL (Y := (BPair.ofPos x * BPair.ofPos c * dotN u u
    + BPair.ofPos c * inertia.quadForm (fpcap.closureMat F sd pr ex) u).swap) hmain
  refine leB_congr (BPair.ofPos_scale g _) ?_ hmoved
  refine BPair.oneValue_trans ?_ (BPair.oneValue_symm (quadLevel F sd pr ex sn c x y u hu))
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.oneValue_of_eq (BPair.swap_add _ _).symm)) ?_
  refine BPair.oneValue_trans (show
      (BPair.ofPos sn * inertia.quadForm (elecMat F ex) u
        + (BPair.ofPos y * BPair.ofPos c) * dotN u u
        + (((BPair.ofPos x * BPair.ofPos c) * dotN u u).swap
          + (BPair.ofPos c * inertia.quadForm (fpcap.closureMat F sd pr ex) u).swap)).oneValue
      (BPair.ofPos sn * inertia.quadForm (elecMat F ex) u
        + (BPair.ofPos c * inertia.quadForm (fpcap.closureMat F sd pr ex) u).swap
        + (BPair.ofPos y * BPair.ofPos c) * dotN u u
        + ((BPair.ofPos x * BPair.ofPos c) * dotN u u).swap) from
    polEqB [BPair.ofPos sn * inertia.quadForm (elecMat F ex) u,
      (BPair.ofPos y * BPair.ofPos c) * dotN u u,
      ((BPair.ofPos x * BPair.ofPos c) * dotN u u).swap,
      (BPair.ofPos c * inertia.quadForm (fpcap.closureMat F sd pr ex) u).swap]
    (Pol.add (Pol.add (pv 0) (pv 1)) (Pol.add (pv 2) (pv 3)))
    (Pol.add (Pol.add (Pol.add (pv 0) (pv 3)) (pv 1)) (pv 2))
    (by decide +kernel)) ?_
  refine BPair.add_congr (BPair.add_congr (BPair.add_congr (BPair.ofPos_scale sn _)
    (ground.swap_congr (BPair.ofPos_scale c _))) ?_) (ground.swap_congr ?_)
  · exact BPair.oneValue_trans (BPair.mul_congr_left (BPair.ofPos_mul y c)) (BPair.ofPos_scale _ _)
  · exact BPair.oneValue_trans (BPair.mul_congr_left (BPair.ofPos_mul x c)) (BPair.ofPos_scale _ _)

/-- The removed block's shifted site is positive semidefinite at every
level below the seed floor: the block scaled by the gap against the
gap's square on the identity. -/
theorem qPrime_nonneg {L : Type} (F : fusion.Data L) (sd pr ex : List L) (K : Nat)
    (sn c x y g : Pos) (hex : beyondAt F K ex)
    (hcap : ∀ u : List BPair, u.length = ex.length →
      ¬ (BPair.ofNat (fpcap.dimFold F sd pr) * dotN u u
          < inertia.quadForm (fpcap.closureMat F sd pr ex) u))
    (hg : (posVal x + fpcap.dimFold F sd pr) * posVal c + posVal g
      = 4 * posVal sn * K + posVal y * posVal c)
    (u : List BPair) (hu : u.length = ex.length) :
    ¬ (inertia.quadForm (inertia.siteDatum (inertia.matScale g (levelSite F sd pr ex sn c x y))
        (inertia.matScale (g * g) (idMat ex.length))) u < BPair.unit) := by
  refine leB_not_lt ?_
  have hQ := levelSite_sq F sd pr ex sn c x y
  refine leB_congr_right (BPair.oneValue_symm (quadSite _ _ (inertia.sqAt_matScale _ g _ hQ)
    (inertia.sqAt_matScale _ (g * g) _ (sqAt_idMat _)) u hu)) ?_
  refine leB_unit_add ?_
  rw [BPair.swap_swap]
  refine leB_congr (BPair.oneValue_symm (BPair.oneValue_trans (inertia.quadForm_scale (g * g) _ u)
      (BPair.scale_congr _ (inertia.quadForm_idMat _ u hu))))
    (BPair.oneValue_symm (inertia.quadForm_scale g _ u)) ?_
  rw [← BPair.scale_scale]
  exact leB_scale (exclFloor F sd pr ex K sn c x y g hex hcap hg u hu) g


/-! ## The difference site -/

/-- The symmetry read at the joined window restricts to its head. -/
private theorem symAtC_head {L : Type} {F : fusion.Data L} {c : L → L → Nat} {hd ex : List L}
    (h : fpcap.symAtC F c (hd ++ ex)) : fpcap.symAtC F c hd := by
  refine fpcap.symIntro F c hd (fun i j hi hj => ?_)
  have hlen : (hd ++ ex).length = hd.length + ex.length := ground.length_append hd ex
  have hs := fpcap.symRead h i j (by rw [hlen]; exact Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _))
    (by rw [hlen]; exact Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _))
  rw [ground.getAt_append F.unit hd ex i, if_pos hi, ground.getAt_append F.unit hd ex j,
    if_pos hj] at hs
  exact hs

/-- The symmetry read at the joined window restricts to its excluded
block. -/
private theorem symAtC_tail {L : Type} {F : fusion.Data L} {c : L → L → Nat} {hd ex : List L}
    (h : fpcap.symAtC F c (hd ++ ex)) : fpcap.symAtC F c ex := by
  refine fpcap.symIntro F c ex (fun i j hi hj => ?_)
  have hlen : (hd ++ ex).length = hd.length + ex.length := ground.length_append hd ex
  have hs := fpcap.symRead h (hd.length + i) (hd.length + j)
    (by rw [hlen]; exact Nat.add_lt_add_left hi _) (by rw [hlen]; exact Nat.add_lt_add_left hj _)
  rw [ground.getAt_append F.unit hd ex (hd.length + i), if_neg (Nat.not_lt.mpr (Nat.le_add_right _
      _)),
    ground.getAt_append F.unit hd ex (hd.length + j), if_neg (Nat.not_lt.mpr (Nat.le_add_right _
        _)),
    ground.addSubSelfL, ground.addSubSelfL] at hs
  exact hs

/-- The four summands of a level entry at the gap's scaling. -/
private theorem scaleS1 (E : BPair) (sn g : Pos) :
    ((E.scale sn).scale g).oneValue (E.scale (g * sn)) := by
  rw [BPair.scale_scale, ground.mul_comm sn g]
  exact BPair.oneValue_refl _

private theorem scaleS2 (M : BPair) (c g : Pos) :
    (((M.scale c).swap).scale g).oneValue ((M.scale (g * c)).swap) := by
  rw [BPair.scale_swap, BPair.scale_scale, ground.mul_comm c g]
  exact BPair.oneValue_refl _

private theorem scaleS3 (I : BPair) (c y g : Pos) :
    (((I.scale c).scale y).scale g).oneValue ((I.scale (g * c)).scale y) := by
  rw [BPair.scale_scale, BPair.scale_scale, BPair.scale_scale,
    show c * (y * g) = g * c * y from by
      rw [← ground.mul_assoc, ground.mul_comm (c * y) g, ← ground.mul_assoc]]
  exact BPair.oneValue_refl _

private theorem scaleS4 (I : BPair) (c x g : Pos) :
    ((((I.scale c).scale x).swap).scale g).oneValue (((I.scale (g * c)).scale x).swap) := by
  rw [BPair.scale_swap, BPair.scale_scale, BPair.scale_scale, BPair.scale_scale,
    show c * (x * g) = g * c * x from by
      rw [← ground.mul_assoc, ground.mul_comm (c * x) g, ← ground.mul_assoc]]
  exact BPair.oneValue_refl _

/-- The level site scaled by the gap is the site at the scaled scale
and clearing. -/
theorem levelSite_scale {L : Type} (F : fusion.Data L) (sd pr ls : List L) (sn c x y g : Pos) :
    matOneValue (inertia.matScale g (levelSite F sd pr ls sn c x y))
      (levelSite F sd pr ls (g * sn) (g * c) x y) := by
  have hS := levelSite_sq F sd pr ls sn c x y
  have hS' := levelSite_sq F sd pr ls (g * sn) (g * c) x y
  refine matOne_of_entries _ _ ls.length ((inertia.length_matScale g _).trans (sqAt_len hS))
    (rowsLen_mapRows _ _ _ (rowsLen_of_sqAt hS)) (sqAt_len hS') (rowsLen_of_sqAt hS')
    (fun i j hi hj => ?_)
  rw [inertia.matScale_entry g _ i j (by rw [sqAt_len hS]; exact hi)
      (by rw [rowsLen_getAt _ i (rowsLen_of_sqAt hS) (by rw [sqAt_len hS]; exact hi)]; exact hj),
    levelSite_entry F sd pr ls sn c x y i j hi hj,
    levelSite_entry F sd pr ls (g * sn) (g * c) x y i j hi hj,
    BPair.scale_add, BPair.scale_add, BPair.scale_add]
  exact BPair.add_congr (BPair.add_congr (BPair.add_congr (scaleS1 _ _ _) (scaleS2 _ _ _))
    (scaleS3 _ _ _ _)) (scaleS4 _ _ _ _)

/-- The coupling at the scaled clearing is the coupling scaled. -/
private theorem coupSwap_scale {L : Type} (F : fusion.Data L) (sd pr hd ex : List L) (c g : Pos) :
    matOneValue (coupSwap F sd pr hd ex (g * c)) (inertia.matScale g (coupSwap F sd pr hd ex
        c)) := by
  have hCl : (inertia.matScale g (coupSwap F sd pr hd ex c)).length = hd.length :=
    (inertia.length_matScale _ _).trans (coupSwap_len _ _ _ _ _ _)
  have hCr : rowsLen ex.length (inertia.matScale g (coupSwap F sd pr hd ex c)) :=
    rowsLen_mapRows _ _ _ (coupSwap_rows _ _ _ _ _ _)
  refine matOne_getAt _ _ ((coupSwap_len _ _ _ _ _ _).trans hCl.symm) (fun i hi => ?_)
  have hik : i < hd.length := by rw [coupSwap_len] at hi; exact hi
  refine poly.oneValue_of_entries _ _ ?_ (fun j hj => ?_)
  · rw [rowsLen_getAt _ i (coupSwap_rows F sd pr hd ex (g * c)) (by rw [coupSwap_len]; exact hik),
      rowsLen_getAt _ i hCr (by rw [hCl]; exact hik)]
  · rw [rowsLen_getAt _ i (coupSwap_rows F sd pr hd ex (g * c)) (by rw [coupSwap_len]; exact
      hik)] at hj
    rw [inertia.matScale_entry g _ i j (by rw [coupSwap_len]; exact hik)
        (by rw [rowsLen_getAt _ i (coupSwap_rows F sd pr hd ex c) (by rw [coupSwap_len]; exact
            hik)]; exact hj),
      coupSwap_entry F sd pr hd ex (g * c) i j hik hj, coupSwap_entry F sd pr hd ex c i j hik hj,
      BPair.scale_swap]
    refine ground.swap_congr ?_
    refine BPair.oneValue_trans (BPair.ofNat_mul _ _) ?_
    refine BPair.oneValue_trans (BPair.mul_congr_left (BPair.oneValue_symm (BPair.ofPos_mul g
        c))) ?_
    refine BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _)) ?_
    refine BPair.oneValue_trans (BPair.ofPos_scale g _) ?_
    exact BPair.scale_congr g (BPair.oneValue_symm (BPair.ofNat_mul _ _))

/-- The site datum's congruence at both arguments. -/
private theorem site_congr {n : Nat} (A B A' B' : Mat) (hA : rowsLen n A) (hB : rowsLen n B)
    (hA' : rowsLen n A') (hB' : rowsLen n B') (h1 : matOneValue A A') (h2 : matOneValue B B') :
    matOneValue (inertia.siteDatum A B) (inertia.siteDatum A' B') :=
  matAdd_cong2 n A (matSwap B) A' (matSwap B') hA (rowsLen_mapRows _ _ _ hB) hA'
    (rowsLen_mapRows _ _ _ hB') h1 (matSwap_congr h2)

/-- The head's shifted site: the head site scaled by the gap less the
border cap on the cutoff labels' support (`lem:contactcell`'s Schur
complement at the cleared bordered pencil). -/
def shiftHead {L : Type} (F : fusion.Data L) (sd pr : List L) (K : Nat) (hd : List L)
    (sn c x y g : Pos) (kB : Nat) : Mat :=
  inertia.siteDatum (inertia.matScale g (levelSite F sd pr hd sn c x y))
    (inertia.matScaleB (BPair.ofNat kB) (suppDiag F sd pr K hd))

/-- The removed block's shifted site: the excluded block's site
scaled by the gap less the gap's square on the identity. -/
def shiftExcl {L : Type} (F : fusion.Data L) (sd pr ex : List L) (sn c x y g : Pos) : Mat :=
  inertia.siteDatum (inertia.matScale g (levelSite F sd pr ex sn c x y))
    (inertia.matScale (g * g) (idMat ex.length))

/-- A datum padded by the identity on both sides of its site, the
count's level `⟨1 : 1⟩`. -/
def padSite (P : Mat) (n : Nat) : Mat :=
  inertia.siteDatum (matAdd P (inertia.matScale Pos.one (idMat n))) (inertia.matScale Pos.one (idMat
      n))

private theorem padSite_read (P : Mat) (n : Nat) (hP : sqAt P n) : matOneValue (padSite P n) P :=
  sitePad_read P n Pos.one hP

private theorem padSite_sq (P : Mat) (n : Nat) (hP : sqAt P n) : sqAt (padSite P n) n :=
  inertia.sqAt_siteDatum n _ _ (sqAt_matAdd n _ _ hP (inertia.sqAt_matScale n _ _ (sqAt_idMat n)))
    (inertia.sqAt_matScale n _ _ (sqAt_idMat n))

private theorem padSite_sym (P : Mat) (n : Nat) (hP : sqAt P n)
    (hs : matOneValue (transposeM P) P) :
    matOneValue (transposeM (padSite P n)) (padSite P n) :=
  (matOne_symm (inertia.symmRead_siteDatum _ _ _ (sqAt_matAdd n _ _ hP (inertia.sqAt_matScale n _ _
      (sqAt_idMat n))) (inertia.sqAt_matScale n _ _ (sqAt_idMat n)) (matOne_symm
      (transposeM_matAdd_sym _ _ hP (inertia.sqAt_matScale n _ _ (sqAt_idMat n)) hs
      ((matOne_symm (inertia.symmRead_matScale _ _ _ (sqAt_idMat n) (symmRead_idMat
          n)))))) (inertia.symmRead_matScale _ _ _ (sqAt_idMat n) (symmRead_idMat n))))

private theorem suppDiag_sq {L : Type} (F : fusion.Data L) (sd pr : List L) (K : Nat) (hd : List
    L) :
    sqAt (suppDiag F sd pr K hd) hd.length :=
  sqAt_of (diagN_len _ _) (diagN_rows _ _)

private theorem shiftHead_sq {L : Type} (F : fusion.Data L) (sd pr : List L) (K : Nat) (hd : List L)
    (sn c x y g : Pos) (kB : Nat) : sqAt (shiftHead F sd pr K hd sn c x y g kB) hd.length :=
  inertia.sqAt_siteDatum _ _ _ (inertia.sqAt_matScale _ g _ (levelSite_sq F sd pr hd sn c x y))
    (inertia.sqAt_scaleB _ _ _ (suppDiag_sq F sd pr K hd))

private theorem shiftHead_sym {L : Type} (F : fusion.Data L) (sd pr : List L) (K : Nat) (hd : List
    L)
    (sn c x y g : Pos) (kB : Nat) (hsym : fpcap.symAtC F (fpcap.closureCount F sd pr) hd) :
    matOneValue (transposeM (shiftHead F sd pr K hd sn c x y g kB)) (shiftHead F sd pr K hd sn c x y
        g kB) :=
  (matOne_symm (inertia.symmRead_siteDatum _ _ _ (inertia.sqAt_matScale _ g _ (levelSite_sq F sd pr
      hd sn c x y)) (inertia.sqAt_scaleB _ _ _ (suppDiag_sq F sd pr K hd))
      (inertia.symmRead_matScale g _ _ (levelSite_sq F sd pr hd sn c x y) (matOne_symm
      (levelSite_sym F sd pr hd sn c x y hsym))) (inertia.symmRead_matScaleB _ _ _ (suppDiag_sq F sd
      pr K hd) (matOne_symm (sym_diagN _ _)))))

private theorem shiftExcl_sq {L : Type} (F : fusion.Data L) (sd pr ex : List L) (sn c x y g : Pos) :
    sqAt (shiftExcl F sd pr ex sn c x y g) ex.length :=
  inertia.sqAt_siteDatum _ _ _ (inertia.sqAt_matScale _ g _ (levelSite_sq F sd pr ex sn c x y))
    (inertia.sqAt_matScale _ _ _ (sqAt_idMat _))

private theorem shiftExcl_sym {L : Type} (F : fusion.Data L) (sd pr ex : List L) (sn c x y g : Pos)
    (hsym : fpcap.symAtC F (fpcap.closureCount F sd pr) ex) :
    matOneValue (transposeM (shiftExcl F sd pr ex sn c x y g)) (shiftExcl F sd pr ex sn c x y g) :=
  (matOne_symm (inertia.symmRead_siteDatum _ _ _ (inertia.sqAt_matScale _ g _ (levelSite_sq F sd pr
      ex sn c x y)) (inertia.sqAt_matScale _ _ _ (sqAt_idMat _)) (inertia.symmRead_matScale g _ _
      (levelSite_sq F sd pr ex sn c x y) (matOne_symm (levelSite_sym F sd pr ex sn c x y hsym)))
      (inertia.symmRead_matScale _ _ _ (sqAt_idMat _) (symmRead_idMat _))))

/-- The difference site assembled at abstract blocks: the whole a
block join, the padded shifts reading their shifts, and each
diagonal difference its stated read; the coupling's difference
against the null block is the coupling itself. -/
private theorem siteJoin_assemble {k m : Nat} (A gP gC gQ sP sQ P' Q' X Y : Mat) (hk : 0 < k)
    (hgP : sqAt gP k) (hgQ : sqAt gQ m) (hCl : gC.length = k) (hCr : rowsLen m gC)
    (hsP : sqAt sP k) (hsQ : sqAt sQ m) (hP' : sqAt P' k) (hQ' : sqAt Q' m)
    (hXr : rowsLen k X)
    (hA : rowsLen (k + m) A) (hwhole : matOneValue A (inertia.blockJoin gP gC gQ))
    (hsPr : matOneValue sP P') (hsQr : matOneValue sQ Q')
    (hPd : matOneValue (inertia.siteDatum gP P') X)
    (hQd : matOneValue (inertia.siteDatum gQ Q') Y) :
    matOneValue (inertia.siteDatum A (inertia.blockJoin sP (nullMat k m) sQ))
      (inertia.blockJoin X gC Y) := by
  have hCt : (transposeM gC).length = m := length_transposeM _ hCr (by rw [hCl]; exact hk)
  have hNl := length_nullMat k m
  have hNr := rowsLen_nullMat k m
  have hJr : rowsLen (k + m) (inertia.blockJoin gP gC gQ) :=
    inertia.rowsLen_blockJoin _ _ _ _ _ (rowsLen_of_sqAt hgP) hCr (rowsLen_cast hCl
        (rowsLen_transposeM _))
      (rowsLen_of_sqAt hgQ)
  have hDr : rowsLen (k + m) (inertia.blockJoin sP (nullMat k m) sQ) :=
    inertia.rowsLen_blockJoin _ _ _ _ _ (rowsLen_of_sqAt hsP) hNr (rowsLen_cast hNl
        (rowsLen_transposeM _))
      (rowsLen_of_sqAt hsQ)
  have h1 := site_congr _ _ _ _ hA hDr hJr hDr hwhole (matOne_refl _)
  have h2 := siteDatum_blockJoin gP gC gQ sP (nullMat k m) sQ hk (sqAt_len hgP) (rowsLen_of_sqAt
      hgP)
    hCl hCr (sqAt_len hgQ) (rowsLen_of_sqAt hgQ) (sqAt_len hsP) (rowsLen_of_sqAt hsP) hNl hNr
    (sqAt_len hsQ) (rowsLen_of_sqAt hsQ)
  have h3P : matOneValue (inertia.siteDatum gP sP) X :=
    matOne_trans (site_congr _ _ _ _ (rowsLen_of_sqAt hgP) (rowsLen_of_sqAt hsP)
      (rowsLen_of_sqAt hgP) (rowsLen_of_sqAt hP') (matOne_refl _) hsPr) hPd
  have h3Q : matOneValue (inertia.siteDatum gQ sQ) Y :=
    matOne_trans (site_congr _ _ _ _ (rowsLen_of_sqAt hgQ) (rowsLen_of_sqAt hsQ)
      (rowsLen_of_sqAt hgQ) (rowsLen_of_sqAt hQ') (matOne_refl _) hsQr) hQd
  have h3 := inertia.blockJoin_congr _ _ _ _ _ _ (rowsLen_site _ _ _ (rowsLen_of_sqAt hgP)
      (rowsLen_of_sqAt hsP))
    hXr ((length_site _ _ (hCl.trans hNl.symm)).trans hCl) hCl (rowsLen_site _ _ _ hCr hNr) hCr
    h3P (siteNull_read gC hCl hCr) h3Q
  exact matOne_trans h1 (matOne_trans h2 h3)

/-- The difference site over stated blocks: the scaled whole against
the shifted split's block diagonal is the Schur site. -/
private theorem diff_core {k m : Nat} (S gP gC gQ D1 : Mat) (g : Pos) (kB : Nat) (hk : 0 < k)
    (hP : sqAt gP k) (hQ : sqAt gQ m) (hCl : gC.length = k) (hCr : rowsLen m gC) (hD1 : sqAt D1 k)
    (hS : rowsLen (k + m) S)
    (hwhole : matOneValue S (inertia.blockJoin (inertia.matScale g gP) (inertia.matScale g gC)
      (inertia.matScale g gQ))) :
    matOneValue
      (inertia.siteDatum S
        (inertia.blockJoin
          (padSite (inertia.siteDatum (inertia.matScale g gP) (inertia.matScaleB (BPair.ofNat kB)
              D1)) k)
          (nullMat k m)
          (padSite (inertia.siteDatum (inertia.matScale g gQ) (inertia.matScale (g * g) (idMat m)))
              m)))
      (schurSite kB g D1 gC m) := by
  have hgP : sqAt (inertia.matScale g gP) k := inertia.sqAt_matScale _ g _ hP
  have hgQ : sqAt (inertia.matScale g gQ) m := inertia.sqAt_matScale _ g _ hQ
  have hgCl : (inertia.matScale g gC).length = k := (inertia.length_matScale _ _).trans hCl
  have hgCr : rowsLen m (inertia.matScale g gC) := rowsLen_mapRows _ _ _ hCr
  have hP' : sqAt (inertia.siteDatum (inertia.matScale g gP) (inertia.matScaleB (BPair.ofNat kB)
      D1)) k :=
    inertia.sqAt_siteDatum k _ _ hgP (inertia.sqAt_scaleB _ _ _ hD1)
  have hQ' : sqAt (inertia.siteDatum (inertia.matScale g gQ) (inertia.matScale (g * g) (idMat
      m))) m :=
    inertia.sqAt_siteDatum m _ _ hgQ (inertia.sqAt_matScale _ _ _ (sqAt_idMat _))
  exact siteJoin_assemble _ _ _ _ _ _ _ _ _ _ hk hgP hgQ hgCl hgCr (padSite_sq _ _ hP') (padSite_sq
      _ _ hQ')
    hP' hQ' (inertia.rowsLen_scaleB _ _ _ (rowsLen_of_sqAt hD1)) hS hwhole
    (padSite_read _ _ hP') (padSite_read _ _ hQ')
    (siteDiff_read _ _ k hgP (inertia.sqAt_scaleB _ _ _ hD1))
    (siteDiff_read _ _ m hgQ (inertia.sqAt_matScale _ _ _ (sqAt_idMat _)))

/-- The difference site of the scaled whole against the shifted
block diagonal is the Schur site at the border cap, the gap and the
coupling. -/
theorem diffTie {L : Type} (F : fusion.Data L) (sd pr : List L) (K : Nat) (hd ex : List L)
    (sn c x y g : Pos) (kB : Nat) (hk : 0 < hd.length)
    (hsym : fpcap.symAtC F (fpcap.closureCount F sd pr) (hd ++ ex)) :
    matOneValue
      (inertia.siteDatum (levelSite F sd pr (hd ++ ex) (g * sn) (g * c) x y)
        (inertia.blockJoin (padSite (shiftHead F sd pr K hd sn c x y g kB) hd.length)
          (nullMat hd.length ex.length)
          (padSite (shiftExcl F sd pr ex sn c x y g) ex.length)))
      (schurSite kB g (suppDiag F sd pr K hd) (coupSwap F sd pr hd ex c) ex.length) := by
  have hlen : (hd ++ ex).length = hd.length + ex.length := ground.length_append hd ex
  have hgP : sqAt (inertia.matScale g (levelSite F sd pr hd sn c x y)) hd.length :=
    inertia.sqAt_matScale _ g _ (levelSite_sq F sd pr hd sn c x y)
  have hCl : (inertia.matScale g (coupSwap F sd pr hd ex c)).length = hd.length :=
    (inertia.length_matScale _ _).trans (coupSwap_len _ _ _ _ _ _)
  have hCr : rowsLen ex.length (inertia.matScale g (coupSwap F sd pr hd ex c)) :=
    rowsLen_mapRows _ _ _ (coupSwap_rows _ _ _ _ _ _)
  exact diff_core _ _ _ _ _ g kB hk (levelSite_sq F sd pr hd sn c x y) (levelSite_sq F sd pr ex sn c
      x y)
    (coupSwap_len _ _ _ _ _ _) (coupSwap_rows _ _ _ _ _ _) (suppDiag_sq F sd pr K hd)
    (rowsLen_cast hlen (rowsLen_of_sqAt (levelSite_sq F sd pr (hd ++ ex) (g * sn) (g * c) x y)))
    (matOne_trans (levelSite_join F sd pr hd ex (g * sn) (g * c) x y hk hsym)
      (inertia.blockJoin_congr _ _ _ _ _ _ (rowsLen_of_sqAt (levelSite_sq F sd pr hd _ _ x y))
        (rowsLen_of_sqAt hgP) (coupSwap_len _ _ _ _ _ _) hCl (coupSwap_rows _ _ _ _ _ _) hCr
        (matOne_symm (levelSite_scale F sd pr hd sn c x y g))
        (coupSwap_scale F sd pr hd ex c g)
        (matOne_symm (levelSite_scale F sd pr ex sn c x y g))))

/-! ## The chain against the shifted head -/

/-- The shift comparison at abstract blocks: the whole at its level
against the padded shifted head and the padded removed block, the
removed block's form at or above the sum's unit, the difference site
reading a positive-semidefinite datum (`thm:truncation`'s monotone
read, `lem:inertia`'s addition at the block diagonal). -/
private theorem shift_le_core {k m : Nat} (H G P Q Sch : Mat) (x y : Pos) (nc : Nat)
    (spF : Split (k + m)) (hk : 0 < k)
    (hf : countAtPair H G x y nc spF)
    (hSsym : matOneValue
      (transposeM (inertia.siteDatum (matAdd H (inertia.matScale y G)) (inertia.matScale x G)))
      (inertia.siteDatum (matAdd H (inertia.matScale y G)) (inertia.matScale x G)))
    (hP : sqAt P k) (hPsym : matOneValue (transposeM P) P)
    (hQ : sqAt Q m) (hQsym : matOneValue (transposeM Q) Q)
    (hQnn : ∀ u : List BPair, u.length = m → ¬ (inertia.quadForm Q u < BPair.unit))
    (hSch : sqAt Sch (k + m))
    (hdiff : matOneValue
      (inertia.siteDatum (inertia.siteDatum (matAdd H (inertia.matScale y G)) (inertia.matScale x
          G))
        (inertia.blockJoin (padSite P k) (nullMat k m) (padSite Q m))) Sch)
    (hSchPsd : ∀ sp : Split (k + m), splitRead Sch sp → psdAt sp) :
    nc ≤ revAt (inertia.mkSplit k (padSite P k)) := by
  have hS2 : sqAt (inertia.siteDatum (matAdd H (inertia.matScale y G)) (inertia.matScale x G)) (k +
      m) :=
    hf.2.2.1.1
  have hsP := padSite_sq P k hP
  have hsPsym := padSite_sym P k hP hPsym
  have hB := inertia.mkSplit_read k (padSite P k) hsP hsPsym
  have hh : countAtPair P (idMat k) Pos.one Pos.one (revAt (inertia.mkSplit k (padSite P k)))
      (inertia.mkSplit k (padSite P k)) :=
    ⟨hP, sqAt_idMat _, hB, rfl⟩
  have hsQ := padSite_sq Q m hQ
  have hsQsym := padSite_sym Q m hQ hQsym
  have hR := inertia.mkSplit_read m (padSite Q m) hsQ hsQsym
  have hpsdR : psdAt (inertia.mkSplit m (padSite Q m)) :=
    inertia.psd_of_all _ _ hR (fun u hu hlt =>
      hQnn u hu (BPair.lt_congr (quadForm_matOne _ _ u (padSite_read Q m hQ)) (BPair.oneValue_refl
          _) hlt))
  have hr : countAtPair Q (idMat m) Pos.one Pos.one 0 (inertia.mkSplit m (padSite Q m)) :=
    ⟨hQ, sqAt_idMat _, hR, hpsdR⟩
  have hNl : (nullMat k m).length = k := length_nullMat _ _
  have hNr : rowsLen m (nullMat k m) := rowsLen_nullMat _ _
  have hNt : (transposeM (nullMat k m)).length = m :=
    length_transposeM _ hNr (by rw [hNl]; exact hk)
  have hDsq : sqAt (inertia.blockJoin (padSite P k) (nullMat k m) (padSite Q m)) (k + m) :=
    sqAt_of (inertia.length_blockJoin _ _ _ _ _ (sqAt_len hsP) hNl hNt (sqAt_len hsQ))
      (inertia.rowsLen_blockJoin _ _ _ _ _ (rowsLen_of_sqAt hsP) hNr
        (rowsLen_cast hNl (rowsLen_transposeM _)) (rowsLen_of_sqAt hsQ))
  have hDsym := matOne_symm (inertia.symmRead_blockJoin (padSite P k) (nullMat k m) (padSite Q
      m) hk hsP hsQ hNl hNr (matOne_symm hsPsym) (matOne_symm hsQsym))
  have hD := inertia.mkSplit_read (k + m) _ hDsq hDsym
  have hdsq := inertia.sqAt_siteDatum (k + m) _ _ hS2 hDsq
  have hdsym := (matOne_symm (inertia.symmRead_siteDatum _ _ _ hS2 hDsq (matOne_symm hSsym)
      (matOne_symm hDsym)))
  have hd := inertia.mkSplit_read (k + m) _ hdsq hdsym
  have hpsd : psdAt (inertia.mkSplit (k + m)
      (inertia.siteDatum (inertia.siteDatum (matAdd H (inertia.matScale y G)) (inertia.matScale x
          G))
        (inertia.blockJoin (padSite P k) (nullMat k m) (padSite Q m)))) :=
    hSchPsd _ (inertia.splitRead_congr _ _ hSch hdiff _ hd)
  exact truncation.count_full_le H G P (idMat k) Q (idMat
      m) x y Pos.one Pos.one Pos.one Pos.one nc _
    spF _ _ _ _ hf hh hr hD hd hpsd

/-- The chain's count sits at or below the shifted head's: at a level
below the seed floor the whole datum scaled by the gap dominates the
shifted block diagonal by the Schur site, the removed block's shifted
site vacant at the floor (`lem:contactcell`; `thm:truncation`'s
monotone read, `lem:inertia`'s addition at the block diagonal). -/
theorem chain_le_shift {L : Type} (F : fusion.Data L) (sd pr : List L) (K : Nat) (hd ex : List L)
    (sn c x y g : Pos) (R kB : Nat) (C : Pos)
    (hk : 0 < hd.length)
    (hsym : fpcap.symAtC F (fpcap.closureCount F sd pr) (hd ++ ex))
    (hcap : ∀ u : List BPair, u.length = (hd ++ ex).length →
      ¬ (BPair.ofNat (fpcap.dimFold F sd pr) * dotN u u
          < inertia.quadForm (fpcap.closureMat F sd pr (hd ++ ex)) u))
    (hex : beyondAt F K ex)
    (hg : (posVal x + fpcap.dimFold F sd pr) * posVal c + posVal g
      = 4 * posVal sn * K + posVal y * posVal c)
    (hrow : ∀ i, i < hd.length →
      ground.famFold Nat.add 0 (fun j => posVal c * fpcap.closureCount F sd pr
        (ground.getAt F.unit ex j) (ground.getAt F.unit hd i)) (List.range ex.length)
        ≤ R * (if leaves F sd pr K (ground.getAt F.unit hd i) then 1 else 0))
    (hcol : ∀ j, j < ex.length →
      ground.famFold Nat.add 0 (fun i => posVal c * fpcap.closureCount F sd pr
        (ground.getAt F.unit ex j) (ground.getAt F.unit hd i)) (List.range hd.length)
        ≤ posVal C)
    (hkB : R * posVal C ≤ kB)
    (nc : Nat) (spC : Split (hd.length + ex.length))
    (hC : countAtPair (dualH F sd pr (hd ++ ex) sn c) (dualG c (hd ++ ex).length) x y nc spC) :
    nc ≤ revAt (inertia.mkSplit hd.length
      (padSite (shiftHead F sd pr K hd sn c x y g kB) hd.length)) := by
  have hlen : (hd ++ ex).length = hd.length + ex.length := ground.length_append hd ex
  have hS : sqAt (levelSite F sd pr (hd ++ ex) sn c x y) (hd.length + ex.length) :=
    sqAt_of ((sqAt_len (levelSite_sq F sd pr (hd ++ ex) sn c x y)).trans hlen)
      (rowsLen_cast hlen (rowsLen_of_sqAt (levelSite_sq F sd pr (hd ++ ex) sn c x y)))
  have hS2 : sqAt (levelSite F sd pr (hd ++ ex) (g * sn) (g * c) x y) (hd.length + ex.length) :=
    sqAt_of ((sqAt_len (levelSite_sq F sd pr (hd ++ ex) (g * sn) (g * c) x y)).trans hlen)
      (rowsLen_cast hlen (rowsLen_of_sqAt (levelSite_sq F sd pr (hd ++ ex) (g * sn) (g * c) x y)))
  have hsymS2 := levelSite_sym F sd pr (hd ++ ex) (g * sn) (g * c) x y hsym
  have hF : splitRead (levelSite F sd pr (hd ++ ex) (g * sn) (g * c) x y)
      (inertia.mkSplit (hd.length + ex.length) (levelSite F sd pr (hd ++ ex) (g * sn) (g * c) x
          y)) :=
    inertia.mkSplit_read _ _ hS2 hsymS2
  have hCread : splitRead (levelSite F sd pr (hd ++ ex) sn c x y) spC := hC.2.2.1
  have hrevF : revAt (inertia.mkSplit (hd.length + ex.length)
      (levelSite F sd pr (hd ++ ex) (g * sn) (g * c) x y)) = nc :=
    (inertia.rev_scalePos g (levelSite F sd pr (hd ++ ex) sn c x y) spC _ hCread
      (inertia.splitRead_congr _ _ (inertia.sqAt_matScale _ g _ hS)
        (matOne_symm (levelSite_scale F sd pr (hd ++ ex) sn c x y g)) _ hF)).trans hC.2.2.2
  have hf : countAtPair (dualH F sd pr (hd ++ ex) (g * sn) (g * c)) (dualG (g * c) (hd ++
      ex).length)
      x y nc (inertia.mkSplit (hd.length + ex.length) (levelSite F sd pr (hd ++ ex) (g * sn) (g * c)
          x y)) :=
    ⟨sqAt_of ((sqAt_len (dualH_sq F sd pr (hd ++ ex) (g * sn) (g * c))).trans hlen)
        (rowsLen_cast hlen (rowsLen_of_sqAt (dualH_sq F sd pr (hd ++ ex) (g * sn) (g * c)))),
      sqAt_of ((sqAt_len (dualG_sq (g * c) (hd ++ ex).length)).trans hlen)
        (rowsLen_cast hlen (rowsLen_of_sqAt (dualG_sq (g * c) (hd ++ ex).length))),
      hF, hrevF⟩
  have hSch : sqAt (schurSite kB g (suppDiag F sd pr K hd) (coupSwap F sd pr hd ex c) ex.length)
      (hd.length + ex.length) := by
    have hCl : (inertia.matScale g (coupSwap F sd pr hd ex c)).length = hd.length :=
      (inertia.length_matScale _ _).trans (coupSwap_len _ _ _ _ _ _)
    have hCr : rowsLen ex.length (inertia.matScale g (coupSwap F sd pr hd ex c)) :=
      rowsLen_mapRows _ _ _ (coupSwap_rows _ _ _ _ _ _)
    exact sqAt_of (inertia.length_blockJoin _ _ _ _ _
        ((inertia.length_scaleB _ _).trans (diagN_len _ _)) hCl
        (length_transposeM _ hCr (by rw [hCl]; exact hk))
        ((inertia.length_matScale _ _).trans (length_idMat _)))
      (inertia.rowsLen_blockJoin _ _ _ _ _ (inertia.rowsLen_scaleB _ _ _ (diagN_rows _ _)) hCr
        (rowsLen_cast hCl (rowsLen_transposeM _))
        (rowsLen_mapRows _ _ _ (rowsLen_idMat _)))
  exact shift_le_core _ _ _ _ _ x y nc _ hk hf
    hsymS2 (shiftHead_sq F sd pr K hd sn c x y g kB)
    (shiftHead_sym F sd pr K hd sn c x y g kB (symAtC_head hsym))
    (shiftExcl_sq F sd pr ex sn c x y g) (shiftExcl_sym F sd pr ex sn c x y g (symAtC_tail hsym))
    (fun u hu => qPrime_nonneg F sd pr ex K sn c x y g hex (capBlock F sd pr hd ex hk hsym hcap) hg
        u hu)
    hSch (diffTie F sd pr K hd ex sn c x y g kB hk hsym)
    (fun sp h => schur_psd hd.length ex.length R kB C g
      (fun i j => posVal c * fpcap.closureCount F sd pr (ground.getAt F.unit ex j) (ground.getAt
          F.unit hd i))
      (fun i => if leaves F sd pr K (ground.getAt F.unit hd i) then 1 else 0) hrow hcol hkB sp h)

/-! ## The bordered pencil -/

/-- The cutoff positions: the head's positions whose label leaves the
cutoff, one auxiliary row each. -/
def cutPos {L : Type} (F : fusion.Data L) (sd pr : List L) (K : Nat) (hd : List L) : List Nat :=
  (List.range hd.length).filter (fun i => leaves F sd pr K (ground.getAt F.unit hd i))

/-- The coupling's indicator: one auxiliary row per cutoff position,
one at the position and the sum's unit elsewhere. -/
def indC (cl : List Nat) (k : Nat) : Mat :=
  cl.map (elim.idRow k)

/-- The indicator's transpose at the head's positions. -/
def indCt (cl : List Nat) (k : Nat) : Mat :=
  (List.range k).map (fun i => cl.map (fun a => if i = a then BPair.ofNat 1 else BPair.unit))

/-- The cutoff-bordered pencil, cleared by the border cap's
clearing: the auxiliary block at the gap, the coupling at `c ϰ_B` on
the cutoff positions, and the head site at `ϰ_B`; the auxiliary
diagonal `[⟨4σΛ : d_L + λ⟩ : ϰ_B]` at the cutoff `Λ` reads the gap
against the clearing `c ϰ_B` (`lem:contactcell`): the pencil is the
tex's at the one positive factor `c ϰ_B`, the gap `g = c (F − λ)` at
the level's join, and a positive rescaling fixes every count
(`lem:inertia`'s `rev(qS) = rev(S)`). -/
def bordPencil {L : Type} (F : fusion.Data L) (sd pr : List L) (K : Nat) (hd : List L)
    (sn c x y g kB : Pos) : Mat :=
  rowJoin (diagN (fun _ => posVal g) (cutPos F sd pr K hd).length)
      (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)) (indC (cutPos F sd pr K hd)
          hd.length))
    ++ rowJoin (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)) (indCt (cutPos F sd pr K hd)
        hd.length))
      (inertia.matScale kB (levelSite F sd pr hd sn c x y))


/-! ## The coupling's support: the fold over a distinct family -/

/-- A fold over a distinct family sits at or below the fold over a
family holding every occupied member. -/
private theorem famFold_le_of_support {α : Type} [DecidableEq α] (f : α → Nat) :
    ∀ (l T : List α), ground.distinctList l →
      (∀ x ∈ l, 0 < f x → 0 < ground.countOf x T) →
      ground.famFold Nat.add 0 f l ≤ ground.famFold Nat.add 0 f T
  | [], _, _, _ => Nat.zero_le _
  | a :: t, T, hdist, hsup => by
    show f a + ground.famFold Nat.add 0 f t ≤ ground.famFold Nat.add 0 f T
    have hdt : ground.distinctList t := fun x hx =>
      Nat.le_trans (Nat.le_of_lt_succ (Nat.lt_succ_of_le (Nat.le_refl _)))
        (by
          have h1 := hdist x (List.Mem.tail a hx)
          rw [ground.countOf_cons] at h1
          exact Nat.le_trans (Nat.le_add_left _ _) h1)
    cases Nat.eq_zero_or_pos (f a) with
    | inl hz =>
      rw [hz, Nat.zero_add]
      exact famFold_le_of_support f t T hdt (fun x hx hf => hsup x (List.Mem.tail a hx) hf)
    | inr hp =>
      have haT : 0 < ground.countOf a T := hsup a (List.Mem.head t) hp
      rw [ground.famFold_eraseFirst Nat.add 0 Nat.add_comm Nat.add_assoc f T a haT]
      refine Nat.add_le_add (Nat.le_refl _)
        (famFold_le_of_support f t (ground.eraseFirst a T) hdt (fun x hx hf => ?_))
      have hxa : x ≠ a := fun h => by
        subst h
        have h1 := hdist x (List.Mem.head t)
        rw [ground.countOf_head] at h1
        exact absurd (Nat.lt_of_lt_of_le (Nat.succ_lt_succ (ground.countOf_pos_of_mem hx)) h1)
          (Nat.lt_irrefl _)
      rw [ground.countOf_eraseFirst_ne T a x hxa]
      exact hsup x (List.Mem.tail a hx) hf

/-! ## The indicator coupling -/

private theorem indC_len (cl : List Nat) (k : Nat) : (indC cl k).length = cl.length :=
  ground.length_map _ cl

private theorem indC_rows (cl : List Nat) (k : Nat) : rowsLen k (indC cl k) :=
  rowsLen_map _ k cl (fun _ _ => elim.length_idRow k _)

private theorem indC_entry (cl : List Nat) (k a i : Nat) (ha : a < cl.length) (hi : i < k) :
    ground.getAt BPair.unit (ground.getAt [] (indC cl k) a) i
      = if i = ground.getAt 0 cl a then BPair.ofNat 1 else BPair.unit := by
  show ground.getAt BPair.unit (ground.getAt [] (cl.map (elim.idRow k)) a) i = _
  rw [ground.getAt_map 0 [] _ cl a ha]
  exact elim.getAt_idRow k _ i hi

private theorem indCt_len (cl : List Nat) (k : Nat) : (indCt cl k).length = k :=
  ground.length_mapRange _ k

private theorem indCt_rows (cl : List Nat) (k : Nat) : rowsLen cl.length (indCt cl k) :=
  rowsLen_map _ cl.length (List.range k) (fun _ _ => ground.length_map _ cl)

private theorem indCt_entry (cl : List Nat) (k i a : Nat) (hi : i < k) (ha : a < cl.length) :
    ground.getAt BPair.unit (ground.getAt [] (indCt cl k) i) a
      = if i = ground.getAt 0 cl a then BPair.ofNat 1 else BPair.unit := by
  show ground.getAt BPair.unit (ground.getAt [] ((List.range k).map (fun i => cl.map
    (fun a => if i = a then BPair.ofNat 1 else BPair.unit))) i) a = _
  rw [ground.getAt_map_range [] _ k i, if_pos hi, ground.getAt_map 0 BPair.unit _ cl a ha]

/-- The indicator's stated transpose is its transpose. -/
private theorem indCt_transpose (cl : List Nat) (k : Nat) (hj : 0 < cl.length) :
    matOneValue (indCt cl k) (transposeM (indC cl k)) := by
  have hTl : (transposeM (indC cl k)).length = k :=
    length_transposeM _ (indC_rows cl k) (by rw [indC_len]; exact hj)
  refine matOne_getAt _ _ ((indCt_len cl k).trans hTl.symm) (fun i hi => ?_)
  have hik : i < k := by rw [indCt_len] at hi; exact hi
  refine poly.oneValue_of_entries _ _ ?_ (fun a ha => ?_)
  · rw [rowsLen_getAt _ i (indCt_rows cl k) (by rw [indCt_len]; exact hik),
      rowsLen_getAt _ i (rowsLen_cast (indC_len cl k) (rowsLen_transposeM _)) (by rw [hTl]; exact
          hik)]
  · rw [rowsLen_getAt _ i (indCt_rows cl k) (by rw [indCt_len]; exact hik)] at ha
    rw [getAt_transposeM BPair.unit _ (indC_rows cl k) i a hik (by rw [indC_len]; exact ha),
      indCt_entry cl k i a hik ha, indC_entry cl k a i ha hik]
    exact BPair.oneValue_refl _

/-- The bordered pencil at occupied cutoff positions is the block
join of the auxiliary block, the coupling and the head site. -/
theorem bordPencil_join {L : Type} (F : fusion.Data L) (sd pr : List L) (K : Nat) (hd : List L)
    (sn c x y g kB : Pos) (hj : 0 < (cutPos F sd pr K hd).length) :
    matOneValue (bordPencil F sd pr K hd sn c x y g kB)
      (inertia.blockJoin (diagN (fun _ => posVal g) (cutPos F sd pr K hd).length)
        (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)) (indC (cutPos F sd pr K hd)
            hd.length))
        (inertia.matScale kB (levelSite F sd pr hd sn c x y))) := by
  refine matOne_append _ _ _ _ (matOne_refl _) ?_
  refine matOne_rowJoin _ _ _ _ (inertia.rowsLen_scaleB _ _ _ (indCt_rows _ _))
    (rowsLen_cast ((inertia.length_scaleB _ _).trans (indC_len _ _)) (rowsLen_transposeM _)) ?_
    (matOne_refl _)
  exact matOne_trans (inertia.matOne_scaleB _ (indCt_transpose _ _ hj))
    (matOne_symm (inertia.transposeM_scaleB _ hd.length _ (indC_rows _ _)))

/-- The constant product fold at a power. -/
private theorem foldMulConst {α : Type} (z : BPair) :
    ∀ (l : List α) (a : BPair),
      ((l.map (fun _ => z)).foldl (fun b d => b * d) a).oneValue (a * ground.bpow z l.length)
  | [], a => BPair.oneValue_symm (BPair.mul_one_read a)
  | _ :: t, a => by
    show ((t.map (fun _ => z)).foldl (fun b d => b * d) (a * z)).oneValue (a * ground.bpow z
        (t.length + 1))
    refine BPair.oneValue_trans (foldMulConst z t (a * z)) ?_
    refine BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _)) ?_
    exact BPair.mul_congr (BPair.oneValue_refl _) (BPair.oneValue_symm (ground.bpow_succ_read z _))

/-- The auxiliary block's minor is the gap's power at the cutoff
count. -/
private theorem auxMinor (g : Pos) (j : Nat) :
    (minor (diagN (fun _ => posVal g) j)).oneValue (ground.bpow (BPair.ofPos g) j) := by
  refine BPair.oneValue_trans (minor_detL _ (by rw [diagN_len]; exact diagN_rows _ _)) ?_
  refine BPair.oneValue_trans (detL_diag _) ?_
  refine BPair.oneValue_trans (foldMulConst (BPair.ofPos g) (List.range j) (BPair.ofNat 1)) ?_
  rw [ground.length_range]
  exact BPair.ofPos_one_mul _


/-! ## The head against the chain -/

/-- The head's count sits at or below the chain's: the plain
truncation is a compression, the head the leading block of the chain
at the head-first order (`lem:contactcell`; `lem:inertia`). -/
theorem head_le_chain {L : Type} (F : fusion.Data L) (sd pr hd ex : List L) (sn c x y : Pos)
    (hk : 0 < hd.length) (hsym : fpcap.symAtC F (fpcap.closureCount F sd pr) (hd ++ ex))
    (nh nc : Nat) (spH : Split hd.length) (spC : Split (hd.length + ex.length))
    (hH : countAtPair (dualH F sd pr hd sn c) (dualG c hd.length) x y nh spH)
    (hC : countAtPair (dualH F sd pr (hd ++ ex) sn c) (dualG c (hd ++ ex).length) x y nc spC) :
    nh ≤ nc :=
  truncation.count_head_le (dualH F sd pr (hd ++ ex) sn c) (dualG c (hd ++ ex).length)
    (dualH F sd pr hd sn c) (dualG c hd.length) (coupSwap F sd pr hd ex c)
    (dualH F sd pr ex sn c) (dualG c ex.length) x y nh nc spH spC (coupSwap_len _ _ _ _ _ _)
    (levelSite_join F sd pr hd ex sn c x y hk hsym) hH hC

/-! ## The coupling's row and column sums -/

/-- The row law at every closure member, head label and excluded
label (`fusion.rowLaw`: a label is a constituent exactly where it
sits on the row, the row reading it once). -/
def rowLawAll {L : Type} [DecidableEq L] (F : fusion.Data L) (sd pr hd ex : List L) : Prop :=
  ((fpcap.closureList F sd pr).all (fun lam => hd.all (fun l => ex.all (fun e =>
    decide (fusion.rowLaw F lam l e))))) = true

instance instContactcellR {L : Type} [DecidableEq L] (F : fusion.Data L) (sd pr hd ex : List L) :
    Decidable (rowLawAll F sd pr hd ex) :=
  inferInstanceAs (Decidable (_ = _))

/-- An occupied closure count from a head label to an excluded label
names a closure member whose row holds the excluded label. -/
private theorem rowMember_of_count {L : Type} [DecidableEq L] (F : fusion.Data L)
    (sd pr hd ex : List L) (hlaw : rowLawAll F sd pr hd ex) {l e : L} (hl : l ∈ hd) (he : e ∈ ex)
    (hpos : 0 < fpcap.closureCount F sd pr l e) :
    ∃ lam, lam ∈ fpcap.closureList F sd pr ∧ e ∈ F.row lam l := by
  rw [fpcap.closureCount_list] at hpos
  obtain ⟨lam, hlam, hc⟩ := ground.famFold_pos_mem _ _ hpos
  have hrl : fusion.rowLaw F lam l e := of_decide_eq_true (ground.all_of_mem _ ex
    (ground.all_of_mem _ hd (ground.all_of_mem _ _ hlaw lam hlam) l hl) e he)
  exact ⟨lam, hlam, ground.mem_of_countOf_pos e _ (hrl.1.mp hc)⟩

/-- A head label with an occupied count to an excluded label leaves
the cutoff. -/
private theorem leaves_of_count {L : Type} [DecidableEq L] (F : fusion.Data L)
    (sd pr hd ex : List L) (K : Nat) (hlaw : rowLawAll F sd pr hd ex) (hex : beyondAt F K ex)
    {l e : L} (hl : l ∈ hd) (he : e ∈ ex) (hpos : 0 < fpcap.closureCount F sd pr l e) :
    leaves F sd pr K l = true := by
  obtain ⟨lam, hlam, hmem⟩ := rowMember_of_count F sd pr hd ex hlaw hl he hpos
  have hK : K < F.c2N e := of_decide_eq_true (ground.all_of_mem _ ex hex e he)
  exact ground.any_of_mem _ hlam (ground.any_of_mem _ hmem (decide_eq_true hK))

/-- An excluded label with an occupied count from a head label is a
target of the head. -/
private theorem mem_targets_of_count {L : Type} [DecidableEq L] (F : fusion.Data L)
    (sd pr hd ex : List L) (K : Nat) (hlaw : rowLawAll F sd pr hd ex) (hex : beyondAt F K ex)
    {l e : L} (hl : l ∈ hd) (he : e ∈ ex) (hpos : 0 < fpcap.closureCount F sd pr l e) :
    e ∈ targets F sd pr K hd := by
  obtain ⟨lam, hlam, hmem⟩ := rowMember_of_count F sd pr hd ex hlaw hl he hpos
  have hK : K < F.c2N e := of_decide_eq_true (ground.all_of_mem _ ex hex e he)
  exact ground.mem_dedupF (ground.mem_flatMap_to _ hl (ground.mem_flatMap_to _ hlam
    (ground.mem_filter_to _ hmem (decide_eq_true hK))))

/-- The coupling's entry flips at the joined window's symmetry. -/
private theorem symFlip {L : Type} {F : fusion.Data L} {sd pr hd ex : List L}
    (hsym : fpcap.symAtC F (fpcap.closureCount F sd pr) (hd ++ ex)) (i j : Nat)
    (hi : i < hd.length) (hj : j < ex.length) :
    fpcap.closureCount F sd pr (ground.getAt F.unit ex j) (ground.getAt F.unit hd i)
      = fpcap.closureCount F sd pr (ground.getAt F.unit hd i) (ground.getAt F.unit ex j) := by
  have hlen : (hd ++ ex).length = hd.length + ex.length := ground.length_append hd ex
  have hs := fpcap.symRead hsym (hd.length + j) i (by rw [hlen]; exact Nat.add_lt_add_left hj _)
    (by rw [hlen]; exact Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _))
  rw [ground.getAt_append F.unit hd ex (hd.length + j), if_neg (Nat.not_lt.mpr (Nat.le_add_right _
      _)),
    ground.addSubSelfL, ground.getAt_append F.unit hd ex i, if_pos hi] at hs
  exact hs

/-- An occupied largest row sum names an occupied column sum: the
border cap's two factors are occupied together. -/
private theorem colMax_pos {L : Type} [DecidableEq L] (F : fusion.Data L) (sd pr : List L) (K : Nat)
    (hd : List L) (h : 0 < rowMax F sd pr (targets F sd pr K hd) hd) :
    0 < colMax F sd pr hd (targets F sd pr K hd) := by
  obtain ⟨l, hl, hpos⟩ := ground.foldMax_pos _ hd h
  obtain ⟨t, ht, hct⟩ := ground.famFold_pos_mem _ _ hpos
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hct (ground.famFold_mem_le _ hd l hl))
    (ground.foldMax_mem (colSum F sd pr hd) (targets F sd pr K hd) 0 t ht)

/-- A natural sits at or below its positive read. -/
private theorem le_posOfNat (n : Nat) : n ≤ posVal (posOfNat n) := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ m => exact Nat.le_refl _

/-- An occupied natural is its positive read. -/
private theorem posVal_posOfNat {n : Nat} (hn : 0 < n) : posVal (posOfNat n) = n := by
  cases n with
  | zero => exact absurd hn (Nat.lt_irrefl 0)
  | succ m => rfl

/-- The coupling's row sums at the excluded block sit under the
largest row sum on the cutoff labels' support: a row off the support
is vacant, and a row on it sits under the head's largest row sum
over the targets, the excluded block a distinct family inside the
targets at its occupied members. -/
theorem rowRead {L : Type} [DecidableEq L] (F : fusion.Data L) (sd pr hd ex : List L) (K : Nat)
    (c : Pos) (hlaw : rowLawAll F sd pr hd ex) (hex : beyondAt F K ex)
    (hdist : ground.distinctList ex)
    (hsym : fpcap.symAtC F (fpcap.closureCount F sd pr) (hd ++ ex)) :
    ∀ i, i < hd.length →
      ground.famFold Nat.add 0 (fun j => posVal c * fpcap.closureCount F sd pr
        (ground.getAt F.unit ex j) (ground.getAt F.unit hd i)) (List.range ex.length)
        ≤ (posVal c * rowMax F sd pr (targets F sd pr K hd) hd)
          * (if leaves F sd pr K (ground.getAt F.unit hd i) then 1 else 0) := by
  intro i hi
  have hl : ground.getAt F.unit hd i ∈ hd := ground.mem_getAt F.unit hd i hi
  have hfold : ground.famFold Nat.add 0 (fun j => posVal c * fpcap.closureCount F sd pr
      (ground.getAt F.unit ex j) (ground.getAt F.unit hd i)) (List.range ex.length)
      = posVal c * ground.famFold Nat.add 0 (fun e => fpcap.closureCount F sd pr e
        (ground.getAt F.unit hd i)) ex := by
    rw [ground.famFold_mul]
    exact ground.famFold_getAt Nat.add 0 (fun e => posVal c * fpcap.closureCount F sd pr e
      (ground.getAt F.unit hd i)) F.unit ex ex.length rfl
  rw [hfold]
  by_cases hlv : leaves F sd pr K (ground.getAt F.unit hd i) = true
  · rw [if_pos hlv, Nat.mul_one]
    refine Nat.mul_le_mul_left _ (Nat.le_trans (famFold_le_of_support _ ex (targets F sd pr K hd)
      hdist (fun e he hpos => ground.countOf_pos_of_mem ?_))
      (ground.foldMax_mem (rowSum F sd pr (targets F sd pr K hd)) hd 0 _ hl))
    obtain ⟨j, hj, hej⟩ := ground.getAt_of_mem F.unit he
    rw [← hej] at hpos ⊢
    rw [symFlip hsym i j hi hj] at hpos
    exact mem_targets_of_count F sd pr hd ex K hlaw hex hl (ground.mem_getAt F.unit ex j hj) hpos
  · rw [if_neg hlv, Nat.mul_zero]
    have hz : ground.famFold Nat.add 0 (fun e => fpcap.closureCount F sd pr e
        (ground.getAt F.unit hd i)) ex = 0 := by
      refine Nat.eq_zero_of_le_zero (Nat.le_trans (ground.famFold_le _ (fun _ => 0) ex
        (fun e he => ?_)) (Nat.le_of_eq (ground.famFold_zero _ (fun _ => rfl) ex)))
      obtain ⟨j, hj, hej⟩ := ground.getAt_of_mem F.unit he
      rw [← hej, symFlip hsym i j hi hj]
      refine Nat.le_of_eq (Nat.eq_zero_of_not_pos (fun hpos => hlv ?_))
      exact leaves_of_count F sd pr hd ex K hlaw hex hl (ground.mem_getAt F.unit ex j hj) hpos
    rw [hz, Nat.mul_zero]
    exact Nat.le_refl 0

/-- The coupling's column sums sit under the largest column sum over
the targets: a column off the targets is vacant. -/
theorem colRead {L : Type} [DecidableEq L] (F : fusion.Data L) (sd pr hd ex : List L) (K : Nat)
    (c : Pos) (hlaw : rowLawAll F sd pr hd ex) (hex : beyondAt F K ex)
    (hsym : fpcap.symAtC F (fpcap.closureCount F sd pr) (hd ++ ex)) :
    ∀ j, j < ex.length →
      ground.famFold Nat.add 0 (fun i => posVal c * fpcap.closureCount F sd pr
        (ground.getAt F.unit ex j) (ground.getAt F.unit hd i)) (List.range hd.length)
        ≤ posVal (posOfNat (posVal c * colMax F sd pr hd (targets F sd pr K hd))) := by
  intro j hj
  have he : ground.getAt F.unit ex j ∈ ex := ground.mem_getAt F.unit ex j hj
  have hfold : ground.famFold Nat.add 0 (fun i => posVal c * fpcap.closureCount F sd pr
      (ground.getAt F.unit ex j) (ground.getAt F.unit hd i)) (List.range hd.length)
      = posVal c * colSum F sd pr hd (ground.getAt F.unit ex j) := by
    show _ = posVal c * ground.famFold Nat.add 0 (fun l => fpcap.closureCount F sd pr
      (ground.getAt F.unit ex j) l) hd
    rw [ground.famFold_mul]
    exact ground.famFold_getAt Nat.add 0 (fun l => posVal c * fpcap.closureCount F sd pr
      (ground.getAt F.unit ex j) l) F.unit hd hd.length rfl
  rw [hfold]
  refine Nat.le_trans ?_ (le_posOfNat _)
  refine Nat.mul_le_mul_left _ ?_
  cases Nat.eq_zero_or_pos (ground.countOf (ground.getAt F.unit ex j) (targets F sd pr K hd)) with
  | inr hmem =>
    exact ground.foldMax_mem _ (targets F sd pr K hd) 0 _ (ground.mem_of_countOf_pos _ _ hmem)
  | inl hoff =>
    refine Nat.le_trans (Nat.le_of_eq ?_) (Nat.zero_le _)
    refine Nat.eq_zero_of_le_zero (Nat.le_trans (ground.famFold_le _ (fun _ => 0) hd
      (fun l hl => ?_)) (Nat.le_of_eq (ground.famFold_zero _ (fun _ => rfl) hd)))
    obtain ⟨i, hi, hli⟩ := ground.getAt_of_mem F.unit hl
    rw [← hli, symFlip hsym i j hi hj]
    refine Nat.le_of_eq (Nat.eq_zero_of_not_pos (fun hpos => ?_))
    have hm := ground.countOf_pos_of_mem
      (mem_targets_of_count F sd pr hd ex K hlaw hex (ground.mem_getAt F.unit hd i hi) he hpos)
    rw [hoff] at hm
    exact Nat.lt_irrefl 0 hm

/-- The Schur read's product sits under the cleared border cap:
`c·rowMax` against `c·colMax` is `c²ϰ_B`, and at a vacant column
sum the row sums are vacant with it. -/
theorem capRead {L : Type} [DecidableEq L] (F : fusion.Data L) (sd pr hd : List L) (K : Nat)
    (c kB : Pos) (hkB : borderCap F sd pr K hd ≤ posVal kB) :
    (posVal c * rowMax F sd pr (targets F sd pr K hd) hd)
        * posVal (posOfNat (posVal c * colMax F sd pr hd (targets F sd pr K hd)))
      ≤ posVal c * posVal c * posVal kB := by
  cases Nat.eq_zero_or_pos (colMax F sd pr hd (targets F sd pr K hd)) with
  | inl hz =>
    have hr : rowMax F sd pr (targets F sd pr K hd) hd = 0 := by
      cases Nat.eq_zero_or_pos (rowMax F sd pr (targets F sd pr K hd) hd) with
      | inl h => exact h
      | inr h => exact absurd (colMax_pos F sd pr K hd h) (by rw [hz]; exact Nat.lt_irrefl 0)
    rw [hr, Nat.mul_zero, Nat.zero_mul]
    exact Nat.zero_le _
  | inr hp =>
    rw [posVal_posOfNat (Nat.mul_pos (posVal_pos c) hp)]
    have h1 : posVal c * rowMax F sd pr (targets F sd pr K hd) hd
        * (posVal c * colMax F sd pr hd (targets F sd pr K hd))
        = posVal c * posVal c * borderCap F sd pr K hd := by
      show _ = posVal c * posVal c * (rowMax F sd pr (targets F sd pr K hd) hd
        * colMax F sd pr hd (targets F sd pr K hd))
      rw [ground.mulAssoc (posVal c) (rowMax _ _ _ _ _), ← ground.mulAssoc (rowMax _ _ _ _ _),
        Nat.mul_comm (rowMax _ _ _ _ _) (posVal c), ground.mulAssoc (posVal c) (rowMax _ _ _ _ _),
        ← ground.mulAssoc]
    rw [h1]
    exact Nat.mul_le_mul_left _ hkB

/-! ## Scaled entries and the vacant diagonal -/

/-- The balance weighting's entry. -/
private theorem scaleB_entry (w : BPair) (M : Mat) (i j : Nat) (hi : i < M.length)
    (hj : j < (ground.getAt [] M i).length) :
    (ground.getAt BPair.unit (ground.getAt [] (inertia.matScaleB w M) i) j).oneValue
      (w * ground.getAt BPair.unit (ground.getAt [] M i) j) := by
  show (ground.getAt BPair.unit (ground.getAt [] (M.map (fun r => r.map (fun x => (w * x).norm))) i)
      j).oneValue _
  rw [ground.getAt_map [] [] _ M i hi, ground.getAt_map BPair.unit BPair.unit _ _ j hj]
  exact BPair.norm_oneValue _

/-- The null block's entry. -/
private theorem nullMat_entry (k m i j : Nat) (hi : i < k) :
    ground.getAt BPair.unit (ground.getAt [] (nullMat k m) i) j = BPair.unit := by
  show ground.getAt BPair.unit (ground.getAt [] (List.replicate k (List.replicate m BPair.unit))
      i) j = _
  rw [ground.getAt_replicate [] _ k i hi, ground.getAt_replicate_self]

/-- The diagonal at a vacant family is the null block. -/
private theorem diagN_null (dd : Nat → Nat) (k : Nat) (h : ∀ i, i < k → dd i = 0) :
    matOneValue (diagN dd k) (nullMat k k) := by
  refine matOne_of_entries _ _ k (diagN_len _ _) (diagN_rows _ _) (length_nullMat _ _)
    (rowsLen_nullMat _ _) (fun i j hi hj => ?_)
  rw [diagN_entry dd k i j hi hj, nullMat_entry k k i j hi]
  by_cases hji : j = i
  · rw [if_pos hji, h i hi]
    exact BPair.ofNat_zero
  · rw [if_neg hji]
    exact BPair.oneValue_refl _

/-- A fold whose members off one key read the sum's unit is that key's
count against its read. -/
private theorem bsum_off {α : Type} [DecidableEq α] (f : α → BPair) (x0 : α) :
    ∀ W : List α, (∀ x ∈ W, x ≠ x0 → (f x).oneValue BPair.unit) →
      (bsum f W).oneValue (BPair.ofNat (ground.countOf x0 W) * f x0)
  | [], _ => by
    show BPair.unit.oneValue (BPair.ofNat 0 * f x0)
    exact BPair.oneValue_symm (BPair.oneValue_trans (BPair.mul_congr_left BPair.ofNat_zero)
      (BPair.unit_mul _))
  | a :: W, h => by
    show (f a + bsum f W).oneValue (BPair.ofNat (ground.countOf x0 (a :: W)) * f x0)
    have ih := bsum_off f x0 W (fun x hx hne => h x (List.Mem.tail a hx) hne)
    by_cases hax : a = x0
    · subst hax
      rw [ground.countOf_head]
      refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) ih) ?_
      refine BPair.oneValue_symm ?_
      refine BPair.oneValue_trans (BPair.mul_congr_left (BPair.ofNat_add _ 1)) ?_
      refine BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.right_distrib _ _ _)) ?_
      refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) (BPair.ofPos_one_mul
          _)) ?_
      exact BPair.oneValue_of_eq (BPair.add_comm _ _)
    · rw [ground.countOf_head_ne (fun h' => hax h'.symm)]
      refine BPair.oneValue_trans (BPair.add_congr (h a (List.Mem.head W) hax) ih) ?_
      exact BPair.unit_add _

/-! ## The auxiliary block's action and the indicator's Gram -/

/-- The diagonal block against a scaled matrix: the product reads the
gap's multiple entrywise, the diagonal's minor at the gap against
the scale. -/
private theorem diagMul_read {j k : Nat} (g : Pos) (w : BPair) (B : Mat) (hj : 0 < j)
    (hBl : B.length = j) (hBr : rowsLen k B)
    (hminor : (minor (diagN (fun _ => posVal g) j)).oneValue (BPair.ofPos g * w)) :
    matOneValue (matMul (diagN (fun _ => posVal g) j) (inertia.matScaleB w B))
      (inertia.matScaleB (minor (diagN (fun _ => posVal g) j)) B) := by
  have hDl := diagN_len (fun _ => posVal g) j
  have hCl : (inertia.matScaleB w B).length = j := (inertia.length_scaleB _ _).trans hBl
  have hCr : rowsLen k (inertia.matScaleB w B) := inertia.rowsLen_scaleB _ _ _ hBr
  have hCt : (transposeM (inertia.matScaleB w B)).length = k :=
    length_transposeM _ hCr (by rw [hCl]; exact hj)
  have hCtr : rowsLen j (transposeM (inertia.matScaleB w B)) :=
    rowsLen_cast hCl (rowsLen_transposeM _)
  refine matOne_getAt _ _ ((length_matMul _ _).trans
    (hDl.trans ((inertia.length_scaleB _ _).trans hBl).symm)) (fun p hp => ?_)
  have hpj : p < j := by rw [length_matMul, hDl] at hp; exact hp
  rw [getAt_matMul _ _ p (by rw [hDl]; exact hpj)]
  refine poly.oneValue_of_entries _ _ ?_ (fun q hq => ?_)
  · rw [ground.length_map, hCt, rowsLen_getAt _ p (inertia.rowsLen_scaleB _ _ _ hBr)
      (by rw [inertia.length_scaleB, hBl]; exact hpj)]
  · rw [ground.length_map, hCt] at hq
    rw [ground.getAt_map [] BPair.unit _ _ q (by rw [hCt]; exact hq)]
    have hcol : (ground.getAt [] (transposeM (inertia.matScaleB w B)) q).length = j :=
      rowsLen_getAt _ q hCtr (by rw [hCt]; exact hq)
    refine BPair.oneValue_trans (elim.diagO_row _ _ p (by rw [ground.length_mapRange]; exact hpj)
      (hcol.trans (ground.length_mapRange _ j).symm)) ?_
    rw [ground.getAt_map_range BPair.unit _ j p, if_pos hpj,
      getAt_transposeM BPair.unit _ hCr q p hq (by rw [hCl]; exact hpj)]
    refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
      (scaleB_entry w B p q (by rw [hBl]; exact hpj)
        (by rw [rowsLen_getAt _ p hBr (by rw [hBl]; exact hpj)]; exact hq))) ?_
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans (scaleB_entry _ B p q (by rw [hBl]; exact hpj)
      (by rw [rowsLen_getAt _ p hBr (by rw [hBl]; exact hpj)]; exact hq)) ?_
    refine BPair.oneValue_trans (BPair.mul_congr_left hminor) ?_
    exact BPair.oneValue_of_eq (BPair.mul_assoc _ _ _)

/-- The indicator's Gram: the cutoff positions' counts down the
diagonal. -/
private theorem indC_gram (cl : List Nat) (k : Nat) (hj : 0 < cl.length) :
    matOneValue (matMul (transposeM (indC cl k)) (indC cl k))
      (diagN (fun i => ground.countOf i cl) k) := by
  have hTl : (transposeM (indC cl k)).length = k :=
    length_transposeM _ (indC_rows cl k) (by rw [indC_len]; exact hj)
  have hTr : rowsLen cl.length (transposeM (indC cl k)) := rowsLen_cast (indC_len cl
      k) (rowsLen_transposeM _)
  have hMl : (matMul (transposeM (indC cl k)) (indC cl k)).length = k :=
    (ground.length_map _ _).trans hTl
  have hMr : rowsLen k (matMul (transposeM (indC cl k)) (indC cl k)) :=
    rowsLen_map _ k _ (fun _ _ => (ground.length_map _ _).trans hTl)
  refine matOne_of_entries _ _ k hMl hMr (diagN_len _ _) (diagN_rows _ _) (fun p q hp hq => ?_)
  rw [getAt_matMul _ _ p (by rw [hTl]; exact hp),
    ground.getAt_map [] BPair.unit _ _ q (by rw [hTl]; exact hq),
    diagN_entry _ k p q hp hq]
  have hrp : (ground.getAt [] (transposeM (indC cl k)) p).length = cl.length :=
    rowsLen_getAt _ p hTr (by rw [hTl]; exact hp)
  have hrq : (ground.getAt [] (transposeM (indC cl k)) q).length = cl.length :=
    rowsLen_getAt _ q hTr (by rw [hTl]; exact hq)
  refine BPair.oneValue_trans (dotN_read _ _) ?_
  rw [dotP_fold cl.length _ _ hrp hrq]
  have hent : ∀ a, a < cl.length → ∀ r, r < k →
      ground.getAt BPair.unit (ground.getAt [] (transposeM (indC cl k)) r) a
        = if r = ground.getAt 0 cl a then BPair.ofNat 1 else BPair.unit := fun a ha r hr => by
    rw [getAt_transposeM BPair.unit _ (indC_rows cl k) r a hr (by rw [indC_len]; exact ha),
      indC_entry cl k a r ha hr]
  have hfold : bsum (fun a => ground.getAt BPair.unit (ground.getAt [] (transposeM (indC cl k)) p) a
        * ground.getAt BPair.unit (ground.getAt [] (transposeM (indC cl k))
            q) a) (List.range cl.length)
      = bsum (fun x => (if p = x then BPair.ofNat 1 else BPair.unit)
        * (if q = x then BPair.ofNat 1 else BPair.unit)) cl := by
    refine Eq.trans (ground.famFold_congr_mem BPair.add BPair.unit _ _ (List.range cl.length)
      (fun a ha => ?_)) (ground.famFold_getAt BPair.add BPair.unit
        (fun x => (if p = x then BPair.ofNat 1 else BPair.unit) * (if q = x then BPair.ofNat 1 else
            BPair.unit))
        0 cl cl.length rfl)
    have hal : a < cl.length := ground.ltOfMemRange ha
    rw [hent a hal p hp, hent a hal q hq]
  rw [hfold]
  refine BPair.oneValue_trans (bsum_off _ p cl (fun x _ hne => ?_)) ?_
  · rw [if_neg (fun h => hne h.symm)]
    exact BPair.unit_mul _
  · rw [if_pos rfl]
    by_cases hqp : q = p
    · rw [if_pos hqp, if_pos hqp]
      exact BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) (BPair.mul_one_read _))
        (BPair.mul_one_read _)
    · rw [if_neg hqp, if_neg hqp]
      exact BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) (BPair.mul_unit _))
        (BPair.mul_unit _)


/-! ## The bordered pencil's count -/

/-- The deflation of the bordered pencil at its auxiliary pivot, at
abstract blocks: the head site at the gap less the border cap on the
indicator's Gram, scaled by the minor's product with the gap's lower
power and the cap. -/
private theorem defl_core {j k : Nat} (P D1 I0 : Mat) (g kB c : Pos) (w : BPair) (hj : 0 < j)
    (hI0l : I0.length = j) (hI0r : rowsLen k I0) (hP : sqAt P k) (hD1 : sqAt D1 k)
    (hgram : matOneValue (matMul (transposeM I0) I0) D1)
    (hminor : (minor (diagN (fun _ => posVal g) j)).oneValue (BPair.ofPos g * w)) :
    matOneValue
      (inertia.deflMat (diagN (fun _ => posVal g) j)
        (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)) I0) (inertia.matScale kB P)
        (inertia.matScaleB w (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)) I0)))
      (inertia.matScaleB (minor (diagN (fun _ => posVal g) j) * w * BPair.ofPos kB)
        (inertia.siteDatum (inertia.matScale g P)
          (inertia.matScaleB (BPair.ofNat (posVal c * posVal c * posVal kB)) D1))) := by
  have hBcl : (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)) I0).length = j :=
    (inertia.length_scaleB _ _).trans hI0l
  have hBcr : rowsLen k (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)) I0) :=
    inertia.rowsLen_scaleB _ _ _ hI0r
  have hBt : (transposeM (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)) I0)).length = k :=
    length_transposeM _ hBcr (by rw [hBcl]; exact hj)
  have hCwl : (inertia.matScaleB w (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB))
      I0)).length = j :=
    (inertia.length_scaleB _ _).trans hBcl
  have hCwr : rowsLen k (inertia.matScaleB w (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB))
      I0)) :=
    inertia.rowsLen_scaleB _ _ _ hBcr
  have hCwt : (transposeM (inertia.matScaleB w
      (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)) I0))).length = k :=
    length_transposeM _ hCwr (by rw [hCwl]; exact hj)
  have hM : matOneValue
      (matMul (transposeM (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)) I0))
        (inertia.matScaleB w (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)) I0)))
      (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)
        * (w * BPair.ofNat (posVal c * posVal kB))) D1) := by
    refine matOne_trans (matMul_congrL _ _ _ (inertia.transposeM_scaleB _ k I0 hI0r)) ?_
    refine matOne_trans (inertia.matMul_scaleL _ _ _) ?_
    refine matOne_trans (inertia.matOne_scaleB _ ?_) (inertia.scaleB_scaleB _ _ D1)
    refine matOne_trans (matMul_congrR (n := j) (k := k) _ _ _ hCwr
      (inertia.rowsLen_scaleB _ _ _ hI0r) hCwl ((inertia.length_scaleB _ _).trans hI0l)
      (inertia.scaleB_scaleB w _ I0)) ?_
    refine matOne_trans (inertia.matMul_scaleR _ k _ _ hI0r) ?_
    exact inertia.matOne_scaleB _ hgram
  have hMsq : sqAt (matMul (transposeM (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)) I0))
      (inertia.matScaleB w (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)) I0))) k :=
    sqAt_of ((length_matMul _ _).trans hBt) (rowsLen_cast hCwt (rowsLen_matMul _ _))
  have hs1 : ((minor (diagN (fun _ => posVal g) j) * w * BPair.ofPos kB) * BPair.ofPos g).oneValue
      (minor (diagN (fun _ => posVal g) j) * minor (diagN (fun _ => posVal g) j) * BPair.ofPos
          kB) := by
    refine BPair.oneValue_trans (BPair.mul_congr_left (BPair.mul_congr_left
      (BPair.mul_congr_left hminor))) ?_
    refine BPair.oneValue_trans ?_ (BPair.oneValue_symm (BPair.mul_congr_left
      (BPair.mul_congr hminor hminor)))
    exact polEqB [BPair.ofPos g, w, BPair.ofPos kB]
      (Pol.mul (Pol.mul (Pol.mul (Pol.mul (pv 0) (pv 1)) (pv 1)) (pv 2)) (pv 0))
      (Pol.mul (Pol.mul (Pol.mul (pv 0) (pv 1)) (Pol.mul (pv 0) (pv 1))) (pv 2))
      (by decide +kernel)
  have hcK : (BPair.ofNat (posVal c * posVal kB)).oneValue (BPair.ofPos c * BPair.ofPos kB) :=
    BPair.ofNat_mul _ _
  have hkB' : (BPair.ofNat (posVal c * posVal c * posVal kB)).oneValue
      (BPair.ofPos c * BPair.ofPos c * BPair.ofPos kB) :=
    BPair.oneValue_trans (BPair.ofNat_mul _ _) (BPair.mul_congr_left (BPair.ofNat_mul _ _))
  have hs2 : ((minor (diagN (fun _ => posVal g) j) * w * BPair.ofPos kB)
        * BPair.ofNat (posVal c * posVal c * posVal kB)).oneValue
      (minor (diagN (fun _ => posVal g) j) * (BPair.ofNat (posVal c * posVal kB)
        * (w * BPair.ofNat (posVal c * posVal kB)))) := by
    refine BPair.oneValue_trans (BPair.mul_congr (BPair.mul_congr_left
      (BPair.mul_congr_left hminor)) hkB') ?_
    refine BPair.oneValue_trans ?_ (BPair.oneValue_symm (BPair.mul_congr hminor
      (BPair.mul_congr hcK (BPair.mul_congr (BPair.oneValue_refl _) hcK))))
    exact polEqB [BPair.ofPos g, w, BPair.ofPos kB, BPair.ofPos c]
      (Pol.mul (Pol.mul (Pol.mul (Pol.mul (pv 0) (pv 1)) (pv 1)) (pv 2))
        (Pol.mul (Pol.mul (pv 3) (pv 3)) (pv 2)))
      (Pol.mul (Pol.mul (pv 0) (pv 1)) (Pol.mul (Pol.mul (pv 3) (pv 2))
        (Pol.mul (pv 1) (Pol.mul (pv 3) (pv 2)))))
      (by decide +kernel)
  refine matOne_trans (site_congr _ _ _ _
    (rowsLen_of_sqAt (inertia.sqAt_scaleB _ _ _ (inertia.sqAt_matScale _ _ _ hP)))
    (rowsLen_of_sqAt (inertia.sqAt_scaleB _ _ _ hMsq))
    (rowsLen_of_sqAt (inertia.sqAt_scaleB _ _ _ hP)) (rowsLen_of_sqAt (inertia.sqAt_scaleB _ _ _
        hD1))
    (matOne_trans (inertia.matOne_scaleB _ (inertia.matScale_scaleB kB P)) (inertia.scaleB_scaleB _
        _ P))
    (matOne_trans (inertia.matOne_scaleB _ hM) (inertia.scaleB_scaleB _ _ D1))) ?_
  refine matOne_symm ?_
  refine matOne_trans (inertia.matScaleB_sum _ _ _) ?_
  refine matAdd_cong2 k _ _ _ _
    (rowsLen_of_sqAt (inertia.sqAt_scaleB _ _ _ (inertia.sqAt_matScale _ _ _ hP)))
    (rowsLen_of_sqAt (inertia.sqAt_scaleB _ _ _ (sqAt_matSwap _ _ (inertia.sqAt_scaleB _ _ _ hD1))))
    (rowsLen_of_sqAt (inertia.sqAt_scaleB _ _ _ hP))
    (rowsLen_of_sqAt (sqAt_matSwap _ _ (inertia.sqAt_scaleB _ _ _ hD1))) ?_ ?_
  · exact matOne_trans (inertia.matOne_scaleB _ (inertia.matScale_scaleB g P))
      (matOne_trans (inertia.scaleB_scaleB _ _ P) (inertia.matScaleB_congr hs1 P))
  · exact matOne_trans (inertia.matScaleB_neg _ _)
      (matSwap_congr (matOne_trans (inertia.scaleB_scaleB _ _ D1) (inertia.matScaleB_congr hs2 D1)))

/-- The cutoff positions are distinct and read the cutoff labels'
support: a position's count in the list is one at a leaving label
and the sum's unit otherwise. -/
private theorem cutPos_count {L : Type} (F : fusion.Data L) (sd pr : List L) (K : Nat) (hd : List L)
    (i : Nat) (hi : i < hd.length) :
    ground.countOf i (cutPos F sd pr K hd)
      = if leaves F sd pr K (ground.getAt F.unit hd i) then 1 else 0 := by
  show ground.countOf i ((List.range hd.length).filter (fun i => leaves F sd pr K (ground.getAt
      F.unit hd i))) = _
  rw [ground.countOf_filter, ground.countOf_range_one hi]

/-- The auxiliary block is positive semidefinite at every split. -/
private theorem aux_psd (g : Pos) (j : Nat) (sp : Split j)
    (h : splitRead (diagN (fun _ => posVal g) j) sp) : psdAt sp :=
  inertia.psd_of_all _ sp h (fun u hu => leB_not_lt (leB_congr_right
    (BPair.oneValue_symm (quadDiagN _ j u hu))
    (foldB_nonneg_mem _ _ (fun _ _ => ground.unitLeMul (ground.unitLeOfNat _) (ground.unitLeSq
        _)))))

/-- The bordered join's count at occupied auxiliary positions over
stated blocks: the auxiliary pivots are positive and inertia adds, the
deflation the shifted head at a positive scale (`lem:inertia`;
`bord_schur`). -/
private theorem bord_pos_core {j k : Nat} (Bp P D1 I0 : Mat) (g kB c : Pos) (hj : 0 < j)
    (hP : sqAt P k) (hPsym : matOneValue (transposeM P) P)
    (hD1 : sqAt D1 k) (hD1sym : matOneValue (transposeM D1) D1)
    (hI0l : I0.length = j) (hI0r : rowsLen k I0)
    (hgram : matOneValue (matMul (transposeM I0) I0) D1)
    (hBp : matOneValue Bp (inertia.blockJoin (diagN (fun _ => posVal g) j)
      (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)) I0) (inertia.matScale kB P)))
    (spJ : Split (j + k)) (hJ : splitRead Bp spJ) :
    revAt spJ = revAt (inertia.mkSplit k (padSite (inertia.siteDatum (inertia.matScale g P)
      (inertia.matScaleB (BPair.ofNat (posVal c * posVal c * posVal kB)) D1)) k)) := by
  have hjs : j = (j - 1) + 1 := (Nat.succ_pred_eq_of_pos hj).symm
  have hminor : (minor (diagN (fun _ => posVal g) j)).oneValue
      (BPair.ofPos g * ground.bpow (BPair.ofPos g) (j - 1)) := by
    refine BPair.oneValue_trans (auxMinor g _) ?_
    rw [hjs]
    exact ground.bpow_succ_read _ _
  have hdefl := defl_core P D1 I0 g kB c (ground.bpow (BPair.ofPos g) (j - 1)) hj hI0l hI0r hP hD1
    hgram hminor
  have hDsq : sqAt (diagN (fun _ => posVal g) j) j := sqAt_of (diagN_len _ _) (diagN_rows _ _)
  have hBcl : (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)) I0).length = j :=
    (inertia.length_scaleB _ _).trans hI0l
  have hBcr : rowsLen k (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)) I0) :=
    inertia.rowsLen_scaleB _ _ _ hI0r
  have hBt : (transposeM (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)) I0)).length = k :=
    length_transposeM _ hBcr (by rw [hBcl]; exact hj)
  have hCwl : (inertia.matScaleB (ground.bpow (BPair.ofPos g) (j - 1))
      (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)) I0)).length = j :=
    (inertia.length_scaleB _ _).trans hBcl
  have hCwr : rowsLen k (inertia.matScaleB (ground.bpow (BPair.ofPos g) (j - 1))
      (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)) I0)) :=
    inertia.rowsLen_scaleB _ _ _ hBcr
  have hCwt : (transposeM (inertia.matScaleB (ground.bpow (BPair.ofPos g) (j - 1))
      (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)) I0))).length = k :=
    length_transposeM _ hCwr (by rw [hCwl]; exact hj)
  have hQ : sqAt (inertia.matScale kB P) k := inertia.sqAt_matScale _ _ _ hP
  have hJsq : sqAt (inertia.blockJoin (diagN (fun _ => posVal g) j)
      (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)) I0) (inertia.matScale kB
          P)) (j + k) :=
    sqAt_of (inertia.length_blockJoin _ _ _ _ _ (sqAt_len hDsq) hBcl hBt (sqAt_len hQ))
      (inertia.rowsLen_blockJoin _ _ _ _ _ (rowsLen_of_sqAt hDsq) hBcr
        (rowsLen_cast hBcl (rowsLen_transposeM _)) (rowsLen_of_sqAt hQ))
  have hJ' := inertia.splitRead_congr _ _ hJsq hBp spJ hJ
  have hgP : sqAt (inertia.matScale g P) k := inertia.sqAt_matScale _ _ _ hP
  have hP' : sqAt (inertia.siteDatum (inertia.matScale g P)
      (inertia.matScaleB (BPair.ofNat (posVal c * posVal c * posVal kB)) D1)) k :=
    inertia.sqAt_siteDatum k _ _ hgP (inertia.sqAt_scaleB _ _ _ hD1)
  have hP'sym := (matOne_symm (inertia.symmRead_siteDatum _ _ _ hgP (inertia.sqAt_scaleB
      (BPair.ofNat (posVal c * posVal c * posVal kB)) _ _ hD1) (inertia.symmRead_matScale _ _ _ hP
      (matOne_symm hPsym)) (inertia.symmRead_matScaleB (BPair.ofNat (posVal c * posVal c * posVal
      kB)) _ _ hD1 (matOne_symm hD1sym))))
  have hspos : BPair.unit < minor (diagN (fun _ => posVal g) j)
      * ground.bpow (BPair.ofPos g) (j - 1) * BPair.ofPos kB :=
    ground.unitLtMul (ground.unitLtMul (BPair.lt_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (auxMinor g _)) (ground.unitLtBpow (ground.unitLtOfPos g) _))
      (ground.unitLtBpow (ground.unitLtOfPos g) _)) (ground.unitLtOfPos kB)
  have hSsq : sqAt (inertia.matScaleB (minor (diagN (fun _ => posVal g) j)
      * ground.bpow (BPair.ofPos g) (j - 1) * BPair.ofPos kB)
      (inertia.siteDatum (inertia.matScale g P)
        (inertia.matScaleB (BPair.ofNat (posVal c * posVal c * posVal kB)) D1))) k :=
    inertia.sqAt_scaleB _ _ _ hP'
  have hS := inertia.mkSplit_read k _ hSsq ((matOne_symm (inertia.symmRead_matScaleB _ _ _ hP'
      (matOne_symm hP'sym))))
  have hDflsq := inertia.sqAt_deflMat (diagN (fun _ => posVal g) j)
    (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)) I0) (inertia.matScale kB P)
    (inertia.matScaleB (ground.bpow (BPair.ofPos g) (j - 1))
      (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)) I0))
    k hBt hCwt (sqAt_len hQ) (rowsLen_of_sqAt hQ)
  have hDfl := inertia.splitRead_congr _ _ hDflsq (matOne_symm hdefl) _ hS
  have hA := inertia.mkSplit_read _ _ hDsq (sym_diagN _ _)
  have hadd := bord_schur _ _ _ _ spJ _ _ hDsq hBcl hBcr hQ hCwl hCwr (sym_diagN _ _)
    (diagMul_read g _ _ hj hBcl hBcr hminor)
    (fun h => ground.offOfUnitLt (ground.unitLtBpow (ground.unitLtOfPos g) _)
      (BPair.oneValue_trans (BPair.oneValue_symm (auxMinor g _)) h))
    hJ' hA (aux_psd g _ _ hA) hDfl
  rw [hadd]
  exact inertia.rev_scale _ hspos _ _ _
    (inertia.splitRead_congr _ _ hP' (padSite_read _ _ hP') _
      (inertia.mkSplit_read _ _ (padSite_sq _ _ hP') (padSite_sym _ _ hP' hP'sym))) hS

/-- The bordered pencil's count at occupied cutoff positions is the
shifted head's: the auxiliary pivots are positive at every level
below the seed floor and inertia adds, the deflation the shifted
head at a positive scale (`lem:contactcell`; `lem:inertia`;
`bord_schur`). -/
theorem bord_read_pos {L : Type} (F : fusion.Data L) (sd pr : List L) (K : Nat) (hd : List L)
    (sn c x y g kB : Pos) (hj : 0 < (cutPos F sd pr K hd).length)
    (hsym : fpcap.symAtC F (fpcap.closureCount F sd pr) hd)
    (spJ : Split ((cutPos F sd pr K hd).length + hd.length))
    (hJ : splitRead (bordPencil F sd pr K hd sn c x y g kB) spJ) :
    revAt spJ = revAt (inertia.mkSplit hd.length
      (padSite (shiftHead F sd pr K hd sn c x y g (posVal c * posVal c * posVal kB))
          hd.length)) := by
  have hgram : matOneValue (matMul (transposeM (indC (cutPos F sd pr K hd) hd.length))
      (indC (cutPos F sd pr K hd) hd.length)) (suppDiag F sd pr K hd) := by
    refine matOne_trans (indC_gram _ _ hj) ?_
    show matOneValue (diagN (fun i => ground.countOf i (cutPos F sd pr K hd)) hd.length)
      (diagN (fun i => if leaves F sd pr K (ground.getAt F.unit hd i) then 1 else 0) hd.length)
    refine matOne_of_entries _ _ hd.length (diagN_len _ _) (diagN_rows _ _) (diagN_len _ _)
      (diagN_rows _ _) (fun p q hp hq => ?_)
    rw [diagN_entry _ _ p q hp hq, diagN_entry _ _ p q hp hq, cutPos_count F sd pr K hd p hp]
    exact BPair.oneValue_refl _
  exact bord_pos_core _ _ _ _ g kB c hj (levelSite_sq F sd pr hd sn c x y)
    (levelSite_sym F sd pr hd sn c x y hsym) (suppDiag_sq F sd pr K hd) (sym_diagN _ _)
    (indC_len _ _) (indC_rows _ _) hgram (bordPencil_join F sd pr K hd sn c x y g kB hj) spJ hJ

/-- The rows of vacant width joined to a list read the list. -/
private theorem zipWith_nilRows {α : Type} : ∀ (L : List α) (M : Mat), L.length = M.length →
    List.zipWith (· ++ ·) (L.map (fun _ => ([] : List BPair))) M = M
  | [], [], _ => rfl
  | [], _ :: _, h => Nat.noConfusion h
  | _ :: _, [], h => Nat.noConfusion h
  | _ :: t, r :: M, h => by
    show r :: List.zipWith (· ++ ·) (t.map (fun _ => ([] : List BPair))) M = r :: M
    rw [zipWith_nilRows t M (Nat.succ.inj h)]

/-- The balance weighting of vacant rows. -/
private theorem scaleB_nilRows {α : Type} (w : BPair) : ∀ (L : List α),
    inertia.matScaleB w (L.map (fun _ => ([] : List BPair))) = L.map (fun _ => ([] : List BPair))
  | [] => rfl
  | _ :: t => by
    show ([] : List BPair) :: inertia.matScaleB w (t.map (fun _ => ([] : List BPair))) = [] :: _
    rw [scaleB_nilRows w t]

/-- At vacant cutoff positions the bordered pencil is the head site
at the cap. -/
private theorem bordPencil_nil {L : Type} (F : fusion.Data L) (sd pr : List L) (K : Nat) (hd : List
    L)
    (sn c x y g kB : Pos) (hnil : cutPos F sd pr K hd = []) :
    bordPencil F sd pr K hd sn c x y g kB = inertia.matScale kB (levelSite F sd pr hd sn c x
        y) := by
  show rowJoin (diagN (fun _ => posVal g) (cutPos F sd pr K hd).length)
      (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)) (indC (cutPos F sd pr K hd)
          hd.length))
    ++ rowJoin (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB)) (indCt (cutPos F sd pr K hd)
        hd.length))
      (inertia.matScale kB (levelSite F sd pr hd sn c x y)) = _
  rw [hnil]
  show List.zipWith (· ++ ·) (inertia.matScaleB (BPair.ofNat (posVal c * posVal kB))
      ((List.range hd.length).map (fun _ => ([] : List BPair))))
      (inertia.matScale kB (levelSite F sd pr hd sn c x y)) = _
  rw [scaleB_nilRows, zipWith_nilRows _ _ ((ground.length_range _).trans
    ((inertia.length_matScale _ _).trans (sqAt_len (levelSite_sq F sd pr hd sn c x y))).symm)]

/-- At vacant cutoff positions every head label keeps the cutoff. -/
private theorem leaves_nil {L : Type} (F : fusion.Data L) (sd pr : List L) (K : Nat) (hd : List L)
    (hnil : cutPos F sd pr K hd = []) (i : Nat) (hi : i < hd.length) :
    (if leaves F sd pr K (ground.getAt F.unit hd i) then 1 else 0) = 0 := by
  by_cases hlv : leaves F sd pr K (ground.getAt F.unit hd i) = true
  · have hmem : i ∈ cutPos F sd pr K hd := ground.mem_filter_to _ (ground.memRange hi) hlv
    rw [hnil] at hmem
    exact nomatch hmem
  · rw [if_neg hlv]

/-- The bordered join's count at vacant auxiliary positions over
stated blocks: the head site at the cap, its count the shifted head's
at the vacant support. -/
private theorem bord_nil_core {j k : Nat} (Bp P D1 : Mat) (g kB c : Pos) (hj : j = 0)
    (hP : sqAt P k) (hPsym : matOneValue (transposeM P) P)
    (hD1 : sqAt D1 k) (hD1sym : matOneValue (transposeM D1) D1)
    (hnull : matOneValue (inertia.matScaleB (BPair.ofNat (posVal c * posVal c * posVal kB)) D1)
      (nullMat k k))
    (hBp : Bp = inertia.matScale kB P)
    (spJ : Split (j + k)) (hJ : splitRead Bp spJ) :
    revAt spJ = revAt (inertia.mkSplit k (padSite (inertia.siteDatum (inertia.matScale g P)
      (inertia.matScaleB (BPair.ofNat (posVal c * posVal c * posVal kB)) D1)) k)) := by
  subst hBp
  have hn : j + k = k := by
    rw [hj]
    exact Nat.zero_add _
  have hPn : sqAt P (j + k) := by
    rw [hn]
    exact hP
  have h1 : revAt spJ = revAt (inertia.mkSplit _ P) :=
    inertia.rev_scalePos kB _ _ spJ (inertia.mkSplit_read _ _ hPn hPsym) hJ
  have h2 : revAt (inertia.mkSplit (j + k) P) = revAt (inertia.mkSplit k P) := by
    rw [hn]
  have hgP : sqAt (inertia.matScale g P) k := inertia.sqAt_matScale _ _ _ hP
  have hSh : sqAt (inertia.siteDatum (inertia.matScale g P)
      (inertia.matScaleB (BPair.ofNat (posVal c * posVal c * posVal kB)) D1)) k :=
    inertia.sqAt_siteDatum k _ _ hgP (inertia.sqAt_scaleB _ _ _ hD1)
  have hShsym := (matOne_symm (inertia.symmRead_siteDatum _ _ _ hgP (inertia.sqAt_scaleB
      (BPair.ofNat (posVal c * posVal c * posVal kB)) _ _ hD1) (inertia.symmRead_matScale _ _ _ hP
      (matOne_symm hPsym)) (inertia.symmRead_matScaleB (BPair.ofNat (posVal c * posVal c * posVal
      kB)) _ _ hD1 (matOne_symm hD1sym))))
  have hread : matOneValue (inertia.siteDatum (inertia.matScale g P)
      (inertia.matScaleB (BPair.ofNat (posVal c * posVal c * posVal kB))
          D1)) (inertia.matScale g P) :=
    matOne_trans (site_congr _ _ _ _ (rowsLen_of_sqAt hgP)
      (rowsLen_of_sqAt (inertia.sqAt_scaleB _ _ _ hD1))
      (rowsLen_of_sqAt hgP) (rowsLen_nullMat _ _) (matOne_refl _) hnull)
      (siteNull_read _ (sqAt_len hgP) (rowsLen_of_sqAt hgP))
  have h3 : revAt (inertia.mkSplit k (padSite (inertia.siteDatum (inertia.matScale g P)
      (inertia.matScaleB (BPair.ofNat (posVal c * posVal c * posVal kB)) D1)) k))
      = revAt (inertia.mkSplit k P) :=
    inertia.rev_scalePos g _ _ _ (inertia.mkSplit_read _ _ hP hPsym)
      (inertia.splitRead_congr _ _ hgP
        (matOne_trans (padSite_read _ _ hSh) hread) _
        (inertia.mkSplit_read _ _ (padSite_sq _ _ hSh) (padSite_sym _ _ hSh hShsym)))
  rw [h1, h2, h3]

/-- The bordered pencil's count at vacant cutoff positions is the
shifted head's, the pencil the head site itself and the shift vacant
off the support. -/
theorem bord_read_nil {L : Type} (F : fusion.Data L) (sd pr : List L) (K : Nat) (hd : List L)
    (sn c x y g kB : Pos) (hnil : cutPos F sd pr K hd = [])
    (hsym : fpcap.symAtC F (fpcap.closureCount F sd pr) hd)
    (spJ : Split ((cutPos F sd pr K hd).length + hd.length))
    (hJ : splitRead (bordPencil F sd pr K hd sn c x y g kB) spJ) :
    revAt spJ = revAt (inertia.mkSplit hd.length
      (padSite (shiftHead F sd pr K hd sn c x y g (posVal c * posVal c * posVal kB)) hd.length)) :=
  bord_nil_core _ _ _ g kB c (by rw [hnil]; rfl) (levelSite_sq F sd pr hd sn c x y)
    (levelSite_sym F sd pr hd sn c x y hsym) (suppDiag_sq F sd pr K hd) (sym_diagN _ _)
    (matOne_trans (inertia.matOne_scaleB _ (diagN_null _ _ (leaves_nil F sd pr K hd hnil)))
      (matOne_of_null _ _ _ (inertia.matNull_scaleB _ _ (matNull_nullMat _ _))
        (matNull_nullMat _ _) (inertia.length_scaleB _ _)
        (inertia.rowsLen_scaleB _ _ _ (rowsLen_nullMat _ _)) (rowsLen_nullMat _ _)))
    (bordPencil_nil F sd pr K hd sn c x y g kB hnil) spJ hJ

/-- The bordered pencil's count is the shifted head's at every cutoff
position count (`lem:contactcell`). -/
theorem bord_read {L : Type} (F : fusion.Data L) (sd pr : List L) (K : Nat) (hd : List L)
    (sn c x y g kB : Pos) (hsym : fpcap.symAtC F (fpcap.closureCount F sd pr) hd)
    (spJ : Split ((cutPos F sd pr K hd).length + hd.length))
    (hJ : splitRead (bordPencil F sd pr K hd sn c x y g kB) spJ) :
    revAt spJ = revAt (inertia.mkSplit hd.length
      (padSite (shiftHead F sd pr K hd sn c x y g (posVal c * posVal c * posVal kB))
          hd.length)) := by
  cases Nat.eq_zero_or_pos (cutPos F sd pr K hd).length with
  | inl hz =>
    have hnil : cutPos F sd pr K hd = [] := by
      cases h : cutPos F sd pr K hd with
      | nil => rfl
      | cons a t => rw [h] at hz; exact Nat.noConfusion hz
    exact bord_read_nil F sd pr K hd sn c x y g kB hnil hsym spJ hJ
  | inr hj => exact bord_read_pos F sd pr K hd sn c x y g kB hj hsym spJ hJ

/-! ## The truncation pair -/

/-- `lem:contactcell`'s truncation pair: at every level below the seed
floor `F = ⟨4σΛ : d_L⟩` the chain's count sits between the head's
count and the cutoff-bordered pencil's, at every cutoff pair `K ≤ K'`.
The excluded block is the sector's at the larger cutoff (`exclAt`),
every member's Casimir beyond `K` by the cutoff's own read
(`exclAt_beyond`); the head is a list at the window reads with the
unit label in it, the sector's head (`headAt`) its instance; the
excluded list is distinct, the window index a set (`def:carrier`);
the scale is `σ = [sn · c2D : c]` at the positive clearing `c`; and
the border datum `kB` sits at or beyond the border cap, the tex's
auxiliary diagonal at the cap its instance. -/
theorem truncPair {L : Type} [DecidableEq L] (F : fusion.Data L) (sd pr hd ex : List L) (K K' : Nat)
    (sn c x y g kB : Pos) (hexl : exclAt F sd pr K K' = ex) (hk : 0 < hd.length)
    (hs : fpcap.symAll F sd (hd ++ ex)) (hi : fpcap.involAll F pr (hd ++ ex))
    (hr : fpcap.rowAll F sd (hd ++ ex)) (hp : fpcap.dualRowAll F pr (hd ++ ex))
    (hdim : fpcap.dimPos F (hd ++ ex))
    (hdist : ground.distinctList ex) (hlaw : rowLawAll F sd pr hd ex)
    (hg : (posVal x + fpcap.dimFold F sd pr) * posVal c + posVal g
      = 4 * posVal sn * K + posVal y * posVal c)
    (hkB : borderCap F sd pr K hd ≤ posVal kB)
    (nh nc : Nat) (spH : Split hd.length) (spC : Split (hd.length + ex.length))
    (spJ : Split ((cutPos F sd pr K hd).length + hd.length))
    (hH : countAtPair (dualH F sd pr hd sn c) (dualG c hd.length) x y nh spH)
    (hC : countAtPair (dualH F sd pr (hd ++ ex) sn c) (dualG c (hd ++ ex).length) x y nc spC)
    (hJ : splitRead (bordPencil F sd pr K hd sn c x y g kB) spJ) :
    nh ≤ nc ∧ nc ≤ revAt spJ := by
  have hex : beyondAt F K ex := by
    rw [← hexl]
    exact exclAt_beyond F sd pr K K'
  have hsym := fpcap.closureSym F sd pr (hd ++ ex) hs hi
  refine ⟨head_le_chain F sd pr hd ex sn c x y hk hsym nh nc spH spC hH hC, ?_⟩
  rw [bord_read F sd pr K hd sn c x y g kB (symAtC_head hsym) spJ hJ]
  exact chain_le_shift F sd pr K hd ex sn c x y g _ _ _ hk hsym
    (fun u hu => fpcap.closureCapUpper F sd pr (hd ++ ex) hs hi hr hp hdim u hu) hex hg
    (rowRead F sd pr hd ex K c hlaw hex hdist hsym) (colRead F sd pr hd ex K c hlaw hex hsym)
    (capRead F sd pr hd K c kB hkB) nc spC hC

/-- Two agreeing counts locate the chain's count: at a level whose
head and bordered counts agree the chain's count is that integer,
the count beyond every cutoff (`lem:contactcell`; `lem:dualtrunc`). -/
theorem pinned {nh nc nb : Nat} (h : nh ≤ nc ∧ nc ≤ nb) (he : nh = nb) : nc = nh :=
  Nat.le_antisymm (he ▸ h.2) h.1

/-- The dual pencil's cell carrier over the coupling coordinate: at a
stated electric matrix, magnetic matrix and level pair, the
polynomial-entried site datum in `σ` — the level datum's magnetic
partner at the constant key and the electric member at the linear
key, `lem:contactcell`'s affine list, the pair `(σE : M)`'s site
datum `P(σ)`. -/
def dualPMat (E M G : Mat) (x y : Pos) : split.PMat :=
  cellcount.levelPMat (elim.matSwap M) E G x y []

/-- The contact end's own read at the cell's carrier: at the
coupling's unit point the cleared evaluation of the dual cell keeps
the constant key alone at the clearing's stated power, so the
cell's matrix there is the magnetic member's balance partner at the
level datum, rescaled by that power — the contact end's pencil its
magnetic member alone with the reads the fusion matrix's own
(`lem:contactcell`; `lem:cellcount`'s `evalPC`). -/
theorem endEval (E M G : Mat) (x y c : Pos) (o : Nat)
    (hE : sqAt E o) (hM : sqAt M o) (hG : sqAt G o) :
    elim.matOneValue
      (cellcount.evalPC (dualPMat E M G x y) BPair.unit c 1)
      (inertia.matScaleB (ground.bpow (BPair.ofPos c) 1)
        (inertia.siteDatum
          (elim.matAdd (elim.matSwap M) (inertia.matScale y G))
          (inertia.matScale x G))) :=
  cellcount.levelPMat_endEval (elim.matSwap M) E G x y c [] o
    (elim.sqAt_matSwap o M hM) hE hG

end contactcell
