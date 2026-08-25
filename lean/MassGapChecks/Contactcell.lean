import MassGap.Contactcell
import MassGapChecks.Inertia
/-!
The check module for `lem:contactcell`: the batteries re-read the
near-contact cell's tiers by kernel `decide` at the `d = 2`
`X`-sector walk.

The committed record.  At `d = 2` the unit class ladder is
`unit, ϑ = [2,0], 2ϑ = [4,0], 3ϑ = [6,0]` at cleared Casimirs
`0, 8, 24, 48` over `2d² = 8`, so `ĉ₂` reads `0, 1, 3, 6`.  The
cutoffs are `K₁ = 8` (head `unit, ϑ`) and `K₂ = 24` (head
`unit, ϑ, 2ϑ`), the excluded block between them the single label
`2ϑ`; `frontierTargets 2 8 = [[4,0]]` and `cPlusN 2 8 = 24`, so
`c₊` reads `3` at the same clearing.  The walk matrix is
`N^b_{ϑ a}` at the index order `(unit, ϑ, 2ϑ)`, rows
`[[0,1,0],[1,1,1],[0,1,1]]`; the electric diagonal at the dual
representative `σ = 1` is `4ĉ₂ = (0, 4, 12)`, one clearing for the
whole record, and the head pencil is the dual pencil's own slice
`E − M`.  `d_ϑ = 3`, the coupling support is the `ϑ` row alone with
border coupling one and border cap `ϰ_B = 1`, and the seed floor at
`σ = 1` is `F = ⟨4·1·3 : 3⟩ = ⟨12 : 3⟩`, nine at the same clearing.
The witness gap is `ς = 2` with shift cap `c_W = 2` at the cofactor
tie `ς c_W = W² = 4`, so the removed row's own site is `9 − λ` and
the record's vacancy boundary is the floor itself.

The count tier at the level `λ = 1`, below the floor: the plain
head's count and the shifted head's agree at one, the whole datum's
count is one, and the removed block is vacant at the raised level,
so `count_bord_le` reads from above and `count_head_le` from below
and `pin_pair` closes the sandwich at one integer.  The
polarization's own display rides beside it — the difference site
`[[0,0,0],[0,2,-1],[0,-1,2]]` doubled IS the shift site
`[[0,0,0],[0,4,-2],[0,-2,4]]` — and the magnetic coupling is capped
two-sidedly at the weight `W = 2` over the supported gram
`diag(0,1,1)`.  `bord_schur` reads the bordered pencil at the same
level: one auxiliary row at the aux pivot `F − λ = 8`, coupling one
on the `ϑ` support, and the deflation `[[-64,-64],[-64,120]]`
carrying the whole reversal count, the aux pivot's own vacant.

Three refusals ride beside them.  The weighting tie: at the forged
shift cap `c_W = 4` the doubled difference site parts from the shift
site, `ς c_W = 8` against `W² = 4`.  The removed count: at the level
twelve the removed block's site reads `−3`, its count occupied and
the vacancy binder refused.  The floor: at that same level the whole
datum's count is three against the head's two, so the sandwich's
conclusion parts exactly where the removed row leaves the vacant
side — the level-below-`F` binder load-bearing.

The frontier tier.  `boxRow`'s tie form at three moves: the `d = 2`
step `[2,0] → [4,0]` at `m = [2,0]`, the `d = 3` steps
`[0,0,0] → [1,1,0]` at `m = [2,1,0]` and `[1,1,0] → [3,0,1]` at
`m = [2,0,1]`, each at an occupied adjoint fusion count.  The three
count binders are isolated one at a time by a genuine tie whose
count conjunct parts with a vacant fusion count: `hc0` at
`[0,0,0] → [1,1,1]` (`m = [3,2,1]`, no vacant place), `hc2` at
`[2,0] → [6,0]` (`m = [4,0]`, no raised place), `hc1` at
`[0,0,0] → [2,2,0]` (`m = [4,2,0]`, the fixed places short of the
width).  `excludedFloor`'s route at `(2, 8, [4,0])`, `(2, 8, [6,0])`
and `(3, 0, [1,1,0])`, with `cPlus_floors` reading the seed
floor's join at the three landings — the frontier's row is
`rankstable.adjRow`, the enumeration's own at every head label.  The class and cutoff binders
are isolated — at `(3, 0, [1,0,0])` and `(2, 24, [4,0])` every
co-binder holds and the conclusion parts — and the reduced binder
is the closure's own carrier (`con:labels`), its refutation
committed at `[1,1,1]`.

The bordered arm assembles at the record: the whole datum
reordered removed-first at the positive pivot eleven, the
cross-scaled deflations' certificate `diag(0, 264)`, and
`chain_le_bord` reading the chain's count at or below the bordered
join's; the auxiliary pivot's positivity is isolated at the forged
diagonal `-8`, the join's count two against the deflation's one.
`endEval` reads the contact end's own evaluation at the coupling's
unit point, the cell's matrix the magnetic member's balance
partner at the level datum.

The cell carrier.  `dualPMat` at a one-site instance is the affine
list `⟨-4 : 3σ⟩`, its evaluation at `σ = 2` reading two and refusing
at `σ = 1`; at the record it reads the walk's own matrix at the
coupling's unit point — the contact end's reads are the fusion
matrix's, the magnetic member's balance partner — and the head
pencil's site at `σ = 1`.  `extRead` closes the extent at the `K₁`
head's `2 × 2` dual pencil at the level four: the divisor
`19 − 16σ`, its own squarefree part at the Bézout `−16` and the
cleared monic `y − 19` at `y = 16σ`, with the segment from the unit
to `σ = 1` at a vacant root count and the bracket `[1, 2]` holding
the extent `σ₁` at the tie `16 σ₁ = 19`.  Its two refusals: the rootless bracket
`[2, 3]` refusing the occupied count, and the straddle `[0, 2]`
refusing the vacant one.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground poly elim inertia certconstruct contactcell

namespace contactcell

def u : BPair := BPair.unit

/-! The `d = 2` `X`-sector walk: the electric diagonal at the dual
representative, the walk matrix, and the head's two blocks with the
`ϑ`-support diagonal and the grams. -/

def eWalk : Mat := [[u, u, u], [u, ⟨5, 1⟩, u], [u, u, ⟨13, 1⟩]]
def mWalk : Mat :=
  [[u, ⟨2, 1⟩, u], [⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩], [u, ⟨2, 1⟩, ⟨2, 1⟩]]
def pK1 : Mat := [[u, ⟨1, 2⟩], [⟨1, 2⟩, ⟨4, 1⟩]]
def bCoup : Mat := [[u], [⟨1, 2⟩]]
def qRem : Mat := [[⟨12, 1⟩]]
def hK2 : Mat := inertia.blockJoin pK1 bCoup qRem
def dSupp : Mat := [[u, u], [u, ⟨2, 1⟩]]
def gK2 : Mat := idMat 3
def gK1 : Mat := idMat 2
def gRem : Mat := idMat 1
def mCoup : Mat :=
  inertia.blockJoin (elim.nullMat 2 2) bCoup (elim.nullMat 1 1)

/-! The split carriers: the one-order and permuted three-order
certificates, and the upper-triangular congruences the record's
sites clear at. -/

def spPerm (a b c : BPair) : Split 3 :=
  ⟨⟨[[u, u, ⟨2, 1⟩], [⟨2, 1⟩, u, u], [u, ⟨2, 1⟩, u]], rfl⟩,
   ⟨[[u, ⟨2, 1⟩, u], [u, u, ⟨2, 1⟩], [⟨2, 1⟩, u, u]], rfl⟩,
   [.two a b c], 1, rfl⟩

def spF : Split 3 :=
  ⟨⟨[[⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩], [u, ⟨1, 2⟩, ⟨1, 2⟩], [u, u, ⟨1, 4⟩]], rfl⟩,
   ⟨[[⟨4, 1⟩, ⟨4, 1⟩, u], [u, ⟨1, 4⟩, ⟨2, 1⟩], [u, u, ⟨1, 2⟩]], rfl⟩,
   [.one ⟨1, 2⟩, .one ⟨4, 1⟩, .one ⟨88, 1⟩], 0, rfl⟩
def spTwo (a b : BPair) : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨2, 1⟩], [u, ⟨1, 2⟩]], rfl⟩,
   ⟨[[⟨1, 2⟩, ⟨1, 2⟩], [u, ⟨2, 1⟩]], rfl⟩,
   [.one a, .one b], 0, rfl⟩
def spD : Split 3 :=
  ⟨⟨[[⟨2, 1⟩, ⟨2, 1⟩, u], [u, ⟨1, 2⟩, u], [u, u, ⟨1, 2⟩]], rfl⟩,
   ⟨[[⟨2, 1⟩, ⟨2, 1⟩, u], [u, ⟨1, 2⟩, u], [u, u, ⟨1, 2⟩]], rfl⟩,
   [.one ⟨1, 2⟩, .one ⟨2, 1⟩, .one ⟨9, 1⟩], 0, rfl⟩

/-! The level twelve carriers, beyond the floor. -/

def spF12 : Split 3 :=
  ⟨⟨[[⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩], [u, ⟨1, 13⟩, ⟨1, 13⟩], [u, u, ⟨108, 1⟩]],
     rfl⟩,
   ⟨[[⟨1, 1285⟩, ⟨1, 108⟩, u], [u, ⟨108, 1⟩, ⟨13, 1⟩], [u, u, ⟨1, 13⟩]],
     rfl⟩,
   [.one ⟨1, 13⟩, .one ⟨1, 1285⟩, .one ⟨1, 10166⟩], 0, rfl⟩
def spH12 : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨2, 1⟩], [u, ⟨1, 13⟩]], rfl⟩,
   ⟨[[⟨1, 13⟩, ⟨1, 2⟩], [u, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨1, 13⟩, .one ⟨1, 1285⟩], 0, rfl⟩

/-! The bordered pencil at the level one: the auxiliary diagonal at
the floor's own gap, the coupling one on the `ϑ` support, the head
site and the solve witness. -/

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

/-! The `K₁` head's dual pencil at the level four and its divisor's
certificate: the squarefree part is the divisor itself at the
Bézout constant `−16`. -/

def eK1 : Mat := [[u, u], [u, ⟨5, 1⟩]]
def mK1 : Mat := [[u, ⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]]
def dDiv : Poly := split.pminor (dualPMat eK1 mK1 gK1 5 1)
def ctD : cellcount.DivCert :=
  ⟨[], [⟨20, 1⟩, ⟨1, 17⟩], [⟨1, 17⟩], [], [⟨2, 1⟩],
   [⟨20, 1⟩, ⟨1, 17⟩], [], [⟨2, 1⟩],
   1, 1, 1, 1, ⟨1, 17⟩, ⟨1, 17⟩⟩

end contactcell

/-! The unit-class ladder and the cutoffs: the cleared Casimirs at
`2d² = 8`, the two heads' below-cutoff lists, the frontier's single
target and its least Casimir beyond the cutoff. -/

example : c2hat.dfQ [0, 0] = 0 := rfl
example : c2hat.dfQ (adjchar.theta 2) = 8 := rfl
example : c2hat.dfQ [4, 0] = 24 := rfl
example : c2hat.dfQ [6, 0] = 48 := rfl
example : adjchar.theta 2 = [2, 0] := rfl
example : (fusion.dataA 2).c2D = 8 := rfl
example : (fusion.dataA 2).below 8 = [[1, 0], [2, 0]] := rfl
example : (fusion.dataA 2).below 24 = [[1, 0], [2, 0], [3, 0], [4, 0]] :=
  rfl
example : frontierTargets 2 8 = [[4, 0]] := by decide +kernel
example : cPlusN 2 8 = 24 := by decide +kernel
example : frontierTargets 2 24 = [[6, 0]] := by decide +kernel
example : cPlusN 2 24 = 48 := by decide +kernel

/-! The walk matrix `N^b_{ϑ a}` at the index order `(unit, ϑ, 2ϑ)`,
entry by entry, and the adjoint's own dimension `d_ϑ = 3`. -/

example : (fusion.dataA 2).count [2, 0] [0, 0] [2, 0] = 1 := by decide +kernel
example : (fusion.dataA 2).count [2, 0] [0, 0] [0, 0] = 0 := by decide +kernel
example : (fusion.dataA 2).count [2, 0] [0, 0] [4, 0] = 0 := by decide +kernel
example : (fusion.dataA 2).count [2, 0] [2, 0] [0, 0] = 1 := by decide +kernel
example : (fusion.dataA 2).count [2, 0] [2, 0] [2, 0] = 1 := by decide +kernel
example : (fusion.dataA 2).count [2, 0] [2, 0] [4, 0] = 1 := by decide +kernel
example : (fusion.dataA 2).count [2, 0] [4, 0] [0, 0] = 0 := by decide +kernel
example : (fusion.dataA 2).count [2, 0] [4, 0] [2, 0] = 1 := by decide +kernel
example : (fusion.dataA 2).count [2, 0] [4, 0] [4, 0] = 1 := by decide +kernel
example : (fusion.dataA 2).dim (adjchar.theta 2) = 3 := by decide +kernel

/-! The record's head IS the dual pencil's own slice `E − M` at the
representative, split at the `K₁` head over the coupling. -/

example : matOneValue hK2 (matAdd eWalk (matSwap mWalk)) := by decide +kernel

/-! The count tier at the level one.  The plain head, the shifted
head and the whole datum all read count one; the removed block is
vacant at the level raised by the witness gap. -/

example : countAtPair pK1 gK1 2 1 1 (spTwo ⟨1, 2⟩ ⟨4, 1⟩) := by decide +kernel
example : countAtPair (siteDatum pK1 (matScale 2 dSupp)) gK1 2 1 1
    (spTwo ⟨1, 2⟩ ⟨2, 1⟩) := by decide +kernel
example : countAtPair hK2 gK2 2 1 1 spF := by decide +kernel
example : countAtPair qRem gRem 4 1 0 (inertia.spOne ⟨9, 1⟩) := by decide +kernel

/-! The polarization display: the difference site doubled IS the
shift site at the cofactor tie `ς c_W = W²`, and the magnetic
coupling is capped two-sidedly at the weight two over the supported
gram. -/

example : matOneValue
    (matScale 2 (siteDatum
      (siteDatum (matAdd hK2 (matScale 1 gK2)) (matScale 2 gK2))
      (inertia.blockJoin
        (siteDatum (matAdd (siteDatum pK1 (matScale 2 dSupp))
          (matScale 1 gK1)) (matScale 2 gK1))
        (elim.nullMat 2 1)
        (siteDatum (matAdd qRem (matScale 1 gRem))
          (matScale 4 gRem)))))
    (truncation.shiftSite 2 2 bCoup dSupp gRem) := by decide +kernel
example : capAt mCoup
    (matScale 2 (inertia.blockJoin dSupp (elim.nullMat 2 1) gRem))
    (spPerm ⟨3, 1⟩ ⟨2, 1⟩ ⟨3, 1⟩) (spPerm ⟨3, 1⟩ ⟨1, 2⟩ ⟨3, 1⟩) := by
  decide +kernel

/-! `count_bord_le`'s route: the whole datum's count sits at or below
the supported-shift head's own. -/

example : (1 : Nat) ≤ 1 :=
  count_bord_le (k := 2) (m := 1) hK2 gK2 mCoup (elim.nullMat 2 2)
    (elim.nullMat 1 1) pK1 gK1 dSupp qRem gRem bCoup 2 1 2 2 2 1 1
    (spPerm ⟨3, 1⟩ ⟨2, 1⟩ ⟨3, 1⟩) (spPerm ⟨3, 1⟩ ⟨1, 2⟩ ⟨3, 1⟩)
    spF spD (spPerm ⟨3, 1⟩ ⟨1, 2⟩ ⟨3, 1⟩)
    (spTwo ⟨1, 2⟩ ⟨2, 1⟩) (inertia.spOne ⟨9, 1⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! `pin_pair`'s route: the compression from below and the bordered
comparison from above meet at one integer, the located count of the
chain itself. -/

example : (1 : Nat) = 1 :=
  pin_pair (k := 2) (m := 1) hK2 gK2 mCoup (elim.nullMat 2 2)
    (elim.nullMat 1 1) pK1 gK1 dSupp qRem gRem bCoup bCoup
    2 1 2 2 2 1 1
    (spPerm ⟨3, 1⟩ ⟨2, 1⟩ ⟨3, 1⟩) (spPerm ⟨3, 1⟩ ⟨1, 2⟩ ⟨3, 1⟩)
    spF spD (spPerm ⟨3, 1⟩ ⟨1, 2⟩ ⟨3, 1⟩)
    (spTwo ⟨1, 2⟩ ⟨4, 1⟩) (spTwo ⟨1, 2⟩ ⟨2, 1⟩) (inertia.spOne ⟨9, 1⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-! `bord_schur`'s route at the one-auxiliary-row bordered join: the
aux pivot is positive at the level below the floor, so the join's
reversal count is the deflation's alone. -/

example : splitRead (inertia.blockJoin dAux bBord pSite) spJ := by decide +kernel
example : splitRead (deflMat dAux bBord pSite bBord) spSch := by decide +kernel
example : matOneValue (matMul dAux bBord)
    (matScaleB (minor dAux) bBord) := by decide +kernel

example : revAt spJ = revAt spSch :=
  bord_schur (k := 1) (m := 2) dAux bBord pSite bBord spJ
    (inertia.spOne ⟨9, 1⟩) spSch
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The bordered arm assembled at the record: the whole datum
reordered removed-first at the join `[[11, 0, -1], [0, -1, -1],
[-1, -1, 2]]`, its count one; the removed pivot eleven positive,
the eliminated head's cleared deflation `[[-121, -121], [-121,
231]]`; the cross-scaled certificate `64·(true) - 121·(bordered) =
diag(0, 264)` positive semidefinite with the kernel column
trailing; and the bordered join's count one — the chain's count at
or below the bordered pencil's own. -/

namespace contactcell
def qSite : Mat := [[⟨13, 2⟩]]
def btBord : Mat := [[u, ⟨1, 2⟩]]
def spWr : Split 3 :=
  ⟨⟨[[⟨2, 1⟩, u, ⟨2, 1⟩], [u, ⟨2, 1⟩, ⟨1, 12⟩], [u, u, ⟨12, 1⟩]],
     rfl⟩,
   ⟨[[⟨12, 1⟩, u, ⟨1, 2⟩], [u, ⟨12, 1⟩, ⟨12, 1⟩], [u, u, ⟨2, 1⟩]],
     rfl⟩,
   [.one ⟨12, 1⟩, .one ⟨1, 2⟩, .one ⟨353, 1⟩], 0, rfl⟩
def spTd : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 2⟩], [u, ⟨2, 1⟩]], rfl⟩,
   ⟨[[⟨2, 1⟩, ⟨2, 1⟩], [u, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨1, 122⟩, .one ⟨353, 1⟩], 0, rfl⟩
def spTd2 : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 2⟩], [u, ⟨2, 1⟩]], rfl⟩,
   ⟨[[⟨2, 1⟩, ⟨2, 1⟩], [u, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨1, 7745⟩, .one ⟨22529, 1⟩], 0, rfl⟩
def spBd2 : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 2⟩], [u, ⟨2, 1⟩]], rfl⟩,
   ⟨[[⟨2, 1⟩, ⟨2, 1⟩], [u, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨1, 7745⟩, .one ⟨22265, 1⟩], 0, rfl⟩
def spDiff : Split 2 :=
  ⟨⟨exch2, rfl⟩, ⟨exch2w, rfl⟩,
   [.one ⟨265, 1⟩], 1, rfl⟩
end contactcell

example : splitRead (inertia.blockJoin qSite btBord pSite) spWr := by
  decide +kernel
example : splitRead (deflMat qSite btBord pSite btBord) spTd := by
  decide +kernel
example : splitRead
    (inertia.matScale 64 (deflMat qSite btBord pSite btBord))
    spTd2 := by decide +kernel
example : splitRead
    (inertia.matScale 121 (deflMat dAux bBord pSite bBord))
    spBd2 := by decide +kernel
example : splitRead (siteDatum
    (inertia.matScale 64 (deflMat qSite btBord pSite btBord))
    (inertia.matScale 121 (deflMat dAux bBord pSite bBord)))
    spDiff := by decide +kernel

example : revAt spWr ≤ revAt spJ :=
  chain_le_bord qSite btBord pSite btBord dAux bBord pSite bBord
    121 64 spWr (inertia.spOne ⟨13, 2⟩) spTd spTd2 spJ
    (inertia.spOne ⟨9, 1⟩) spSch spBd2 spDiff
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-! The auxiliary pivot's refusal, isolating `bord_schur`'s
positive-pivot binder: at the forged auxiliary diagonal `-8` every
co-binder holds while the pivot's split reads one reversal, and
the conclusion parts — the join's count two against the
deflation's one. -/

namespace contactcell
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
end contactcell

example : splitRead (inertia.blockJoin dAuxN bBord pSite) spJN := by
  decide +kernel
example : splitRead (deflMat dAuxN bBord pSite bBord) spSchN := by
  decide +kernel
example : matOneValue (matMul dAuxN bBord)
    (matScaleB (minor dAuxN) bBord) := by decide +kernel
example : ¬ psdAt (inertia.spOne ⟨1, 9⟩) := by decide +kernel
example : ¬ (revAt spJN = revAt spSchN) := by decide +kernel

/-! The contact end's own evaluation at the record: at the
coupling's unit point the dual cell's matrix is the magnetic
member's balance partner at the level datum, the theorem route
beside the display. -/

example : matOneValue
    (cellcount.evalPC (dualPMat eWalk mWalk gK2 2 1) BPair.unit 1 1)
    (inertia.matScaleB (ground.bpow (BPair.ofPos 1) 1)
      (siteDatum
        (elim.matAdd (elim.matSwap mWalk) (inertia.matScale 1 gK2))
        (inertia.matScale 2 gK2))) :=
  contactcell.endEval eWalk mWalk gK2 2 1 1 3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-! The weighting tie's refusal: at the forged shift cap `c_W = 4`
the cofactor tie reads `ς c_W = 8` against `W² = 4`, and the doubled
difference site parts from the shift site — the head's own shift
moved off the supported diagonal. -/

example : ¬ matOneValue
    (matScale 2 (siteDatum
      (siteDatum (matAdd hK2 (matScale 1 gK2)) (matScale 2 gK2))
      (inertia.blockJoin
        (siteDatum (matAdd (siteDatum pK1 (matScale 4 dSupp))
          (matScale 1 gK1)) (matScale 2 gK1))
        (elim.nullMat 2 1)
        (siteDatum (matAdd qRem (matScale 1 gRem))
          (matScale 4 gRem)))))
    (truncation.shiftSite 2 2 bCoup dSupp gRem) := by decide +kernel

/-! The removed count's refusal and the floor's own: at the level
twelve the removed block's site reads `−3`, its count occupied, and
the whole datum's count is three against the head's two — the
sandwich's conclusion parts exactly where the removed row leaves the
vacant side. -/

example : ¬ countAtPair qRem gRem 15 1 0 (inertia.spOne ⟨1, 4⟩) := by decide +kernel
example : countAtPair qRem gRem 15 1 1 (inertia.spOne ⟨1, 4⟩) := by decide +kernel
example : countAtPair hK2 gK2 13 1 3 spF12 := by decide +kernel
example : countAtPair pK1 gK1 13 1 2 spH12 := by decide +kernel
example : ¬ ((3 : Nat) = 2) := by decide +kernel

/-! `boxRow`'s tie form at three moves, each at an occupied adjoint
fusion count: the `d = 2` step and the two `d = 3` steps. -/

example : ground.tieGap (places.display [4, 0]) (places.display [2, 0])
    = some [2, 0] := by decide +kernel
example : 0 < blockcount.fusionCount [2, 0] (adjchar.theta 2) [4, 0] :=
  boxRow 2 [2, 0] [4, 0] [2, 0] rfl rfl (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : 0 < blockcount.fusionCount [0, 0, 0] (adjchar.theta 3) [1, 1, 0] :=
  boxRow 3 [0, 0, 0] [1, 1, 0] [2, 1, 0] rfl rfl (by decide +kernel)
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : 0 < blockcount.fusionCount [1, 1, 0] (adjchar.theta 3) [3, 0, 1] :=
  boxRow 3 [1, 1, 0] [3, 0, 1] [2, 0, 1] rfl rfl (by decide +kernel)
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The three count binders isolated, each at a genuine tie whose one
conjunct parts with a vacant fusion count.  The vacant place: at
`[0,0,0] → [1,1,1]` the tie is `[3,2,1]`, its raised place and its
fixed places holding while no place stays put.  The raised place: at
`[2,0] → [6,0]` the tie is `[4,0]`, its vacant place and its fixed
places holding while no place rises by one.  The fixed places: at
`[0,0,0] → [2,2,0]` the tie is `[4,2,0]`, both its outer places
holding while the fixed places fall short of the width. -/

example : ground.tieGap (places.display [1, 1, 1]) (places.display [0, 0, 0])
    = some [3, 2, 1] := by decide +kernel
example : ¬ (ground.countOf 0 [3, 2, 1] = 1) := by decide +kernel
example : ground.countOf 2 [3, 2, 1] = 1 := by decide +kernel
example : ground.countOf 1 [3, 2, 1] + 2 = 3 := by decide +kernel
example : ¬ (0 < blockcount.fusionCount [0, 0, 0] (adjchar.theta 3) [1, 1, 1]) := by
  decide +kernel

example : ground.tieGap (places.display [6, 0]) (places.display [2, 0])
    = some [4, 0] := by decide +kernel
example : ground.countOf 0 [4, 0] = 1 := by decide +kernel
example : ¬ (ground.countOf 2 [4, 0] = 1) := by decide +kernel
example : ground.countOf 1 [4, 0] + 2 = 2 := by decide +kernel
example : ¬ (0 < blockcount.fusionCount [2, 0] (adjchar.theta 2) [6, 0]) := by
  decide +kernel

example : ground.tieGap (places.display [2, 2, 0]) (places.display [0, 0, 0])
    = some [4, 2, 0] := by decide +kernel
example : ground.countOf 0 [4, 2, 0] = 1 := by decide +kernel
example : ground.countOf 2 [4, 2, 0] = 1 := by decide +kernel
example : ¬ (ground.countOf 1 [4, 2, 0] + 2 = 3) := by decide +kernel
example : ¬ (0 < blockcount.fusionCount [0, 0, 0] (adjchar.theta 3) [2, 2, 0]) := by
  decide +kernel

/-! `excludedFloor`'s route at the three landings, every binder
decided. -/

example : ((frontierTargets 2 8).any
    (fun c => decide (c2hat.dfQ c ≤ c2hat.dfQ [4, 0]))) = true :=
  excludedFloor 2 8 [4, 0] (by decide +kernel) rfl rfl
    (by decide +kernel) (by decide +kernel)
example : ((frontierTargets 2 8).any
    (fun c => decide (c2hat.dfQ c ≤ c2hat.dfQ [6, 0]))) = true :=
  excludedFloor 2 8 [6, 0] (by decide +kernel) rfl rfl
    (by decide +kernel) (by decide +kernel)
example : ((frontierTargets 3 0).any
    (fun c => decide (c2hat.dfQ c ≤ c2hat.dfQ [1, 1, 0]))) = true :=
  excludedFloor 3 0 [1, 1, 0] (by decide +kernel) rfl rfl
    (by decide +kernel) (by decide +kernel)

/-! The landing's binders, each at its record.  The class binder is
isolated: at `(3, 0, [1, 0, 0])` every co-binder holds (`length`
three, the last row vacant, the Casimir eight beyond the cutoff)
while the degree one sits off the class, and the conclusion parts —
`frontierTargets 3 0 = [[1, 1, 0]]` at the Casimir eighteen beyond
eight.  The cutoff binder is isolated at `(2, 24, [4, 0])`: the
Casimir twenty-four holds the cutoff, and the conclusion parts at
the frontier's forty-eight.  The reduced binder is the closure's
own carrier (`con:labels`, one reduced shape per label), the
cleared Casimir one value across the class: its refutation is
committed at `[1, 1, 1]`, the frame the carrier's own. -/

example : ¬ (places.degree [1, 0, 0] % 3 = 0) := by decide +kernel
example : ground.getAt 0 [1, 0, 0] (3 - 1) = 0 := by decide +kernel
example : 0 < c2hat.dfQ [1, 0, 0] := by decide +kernel
example : ¬ (((frontierTargets 3 0).any
    (fun c => decide (c2hat.dfQ c ≤ c2hat.dfQ [1, 0, 0]))) = true) := by
  decide +kernel
example : ¬ (24 < c2hat.dfQ [4, 0]) := by decide +kernel
example : c2hat.dfQ [4, 0] = 24 := rfl
example : ¬ (((frontierTargets 2 24).any
    (fun c => decide (c2hat.dfQ c ≤ c2hat.dfQ [4, 0]))) = true) := by
  decide +kernel
example : ¬ (ground.getAt 0 [1, 1, 1] (3 - 1) = 0) := by decide +kernel

/-! The seed floor's join, the theorem route at the three landings:
`c₊` at or below every excluded label's cleared Casimir. -/

example : cPlusN 2 8 ≤ c2hat.dfQ [4, 0] :=
  cPlus_floors 2 8 [4, 0] (by decide +kernel) rfl rfl
    (by decide +kernel) (by decide +kernel)
example : cPlusN 2 8 ≤ c2hat.dfQ [6, 0] :=
  cPlus_floors 2 8 [6, 0] (by decide +kernel) rfl rfl
    (by decide +kernel) (by decide +kernel)
example : cPlusN 3 0 ≤ c2hat.dfQ [1, 1, 0] :=
  cPlus_floors 3 0 [1, 1, 0] (by decide +kernel) rfl rfl
    (by decide +kernel) (by decide +kernel)

/-! `dualPMat` at a one-site instance: the affine list `⟨-4 : 3σ⟩`,
its cleared evaluation reading two at `σ = 2` and refusing there at
`σ = 1`. -/

example : split.pmatOneValue (dualPMat [[⟨4, 1⟩]] [[⟨3, 1⟩]] [[⟨2, 1⟩]] 3 1)
    [[[⟨1, 5⟩, ⟨4, 1⟩]]] := by decide +kernel
example : matOneValue
    (cellcount.evalPC (dualPMat [[⟨4, 1⟩]] [[⟨3, 1⟩]] [[⟨2, 1⟩]] 3 1)
      ⟨3, 1⟩ 1 1) [[⟨3, 1⟩]] := by decide +kernel
example : ¬ matOneValue
    (cellcount.evalPC (dualPMat [[⟨4, 1⟩]] [[⟨3, 1⟩]] [[⟨2, 1⟩]] 3 1)
      ⟨2, 1⟩ 1 1) [[⟨3, 1⟩]] := by decide +kernel

/-! The contact end is interior to its cell: at the coupling's unit
point the record's dual pencil reads the walk's own matrix — the
magnetic member's balance partner at the level — and at the
representative `σ = 1` it reads the head pencil's own site. -/

example : matOneValue
    (cellcount.evalPC (dualPMat eWalk mWalk gK2 2 1) BPair.unit 1 1)
    (siteDatum (matAdd (matSwap mWalk) (matScale 1 gK2))
      (matScale 2 gK2)) := by decide +kernel
example : matOneValue
    (cellcount.evalPC (dualPMat eWalk mWalk gK2 2 1) ⟨2, 1⟩ 1 1)
    (siteDatum (matAdd hK2 (matScale 1 gK2)) (matScale 2 gK2)) := by
  decide +kernel

/-! At a level on the divisor the boundary clause extends the
positive-semidefinite cell into the closed endpoint: the one-site
carrier `3σ` reads its determinant at equal members at the contact
end, the endpoint's own split positive semidefinite at the kernel
block, and the adjacent cell's count the vacant read. -/

example : split.pmatOneValue
    (dualPMat [[⟨4, 1⟩]] [[⟨3, 1⟩]] [[⟨2, 1⟩]] 1 3)
    [[[BPair.unit, ⟨4, 1⟩]]] := by decide +kernel
example : (elim.minor
    (cellcount.evalPC (dualPMat [[⟨4, 1⟩]] [[⟨3, 1⟩]] [[⟨2, 1⟩]] 1 3)
      BPair.unit 1 1)).oneValue BPair.unit := by decide +kernel
example : psdAt (mkSplit 1
    (cellcount.evalPC (dualPMat [[⟨4, 1⟩]] [[⟨3, 1⟩]] [[⟨2, 1⟩]] 1 3)
      BPair.unit 1 1)) := by decide +kernel
example : psdAt (mkSplit 1
    (cellcount.evalPC (dualPMat [[⟨4, 1⟩]] [[⟨3, 1⟩]] [[⟨2, 1⟩]] 1 3)
      ⟨2, 1⟩ 1 1)) := by decide +kernel

/-! The extent certificate at the `K₁` head's dual pencil, level
four: the divisor `19 − 16σ` at its own squarefree part, the cleared
monic `y − 19` at `y = 16σ`, the vacant segment up to `σ = 1` and the
bracket `[1, 2]` holding the extent. -/

example : poly.oneValue dDiv [⟨20, 1⟩, ⟨1, 17⟩] := by decide +kernel
example : cellcount.divRead dDiv ctD := by decide +kernel
example : poly.oneValue (deckfactor.clearVarBT ctD.sq) [⟨1, 20⟩] := by
  decide +kernel
example : (deckfactor.clearAt ctD.sq ⟨2, 1⟩).oneValue ⟨17, 1⟩ := by decide +kernel
example : (deckfactor.clearAt ctD.sq ⟨3, 1⟩).oneValue ⟨33, 1⟩ := by decide +kernel
example : extRead dDiv ctD ⟨2, 1⟩ ⟨3, 1⟩ 1
    (inertia.spOne ⟨2, 1⟩) (inertia.spOne ⟨58, 1⟩) (inertia.spOne ⟨2, 1⟩) (inertia.spOne ⟨1, 40⟩) := by
  decide +kernel

/-! The bracket's two conjuncts refused: the rootless bracket
`[2, 3]` carries a vacant count where the extent read wants one, and
the straddle `[0, 2]` carries one where the leading segment wants
none. -/

example : hermitesign.segCountRead (deckfactor.clearVarBT ctD.sq)
    (deckfactor.clearAt ctD.sq ⟨3, 1⟩) (deckfactor.clearAt ctD.sq ⟨4, 1⟩)
    1 0 (inertia.spOne ⟨2, 1⟩) (inertia.spOne ⟨378, 1⟩) := by decide +kernel
example : ¬ hermitesign.segCountRead (deckfactor.clearVarBT ctD.sq)
    (deckfactor.clearAt ctD.sq ⟨3, 1⟩) (deckfactor.clearAt ctD.sq ⟨4, 1⟩)
    1 1 (inertia.spOne ⟨2, 1⟩) (inertia.spOne ⟨378, 1⟩) := by decide +kernel
example : hermitesign.segCountRead (deckfactor.clearVarBT ctD.sq)
    (deckfactor.clearAt ctD.sq BPair.unit)
    (deckfactor.clearAt ctD.sq ⟨3, 1⟩)
    1 1 (inertia.spOne ⟨2, 1⟩) (inertia.spOne ⟨1, 248⟩) := by decide +kernel
example : ¬ hermitesign.segCountRead (deckfactor.clearVarBT ctD.sq)
    (deckfactor.clearAt ctD.sq BPair.unit)
    (deckfactor.clearAt ctD.sq ⟨3, 1⟩)
    1 0 (inertia.spOne ⟨2, 1⟩) (inertia.spOne ⟨1, 248⟩) := by decide +kernel
example : ¬ extRead dDiv ctD ⟨3, 1⟩ ⟨4, 1⟩ 1
    (inertia.spOne ⟨2, 1⟩) (inertia.spOne ⟨1, 248⟩) (inertia.spOne ⟨2, 1⟩) (inertia.spOne ⟨378, 1⟩) := by
  decide +kernel
