import MassGap.Truncation
import MassGapChecks.Inertia
/-!
The check module for `thm:truncation`: the batteries re-read the
magnetic cap's transports by kernel `decide` at the order `1 + 1`
fixture — head pencil `[2]` against the unit gram, removed pencil
`[10]`, coupling `[1]`, so the full pencil is `[[2,1],[1,10]]` over
the block-diagonal gram, the magnetic part `[[-1,1],[1,-1]]` capped
two-sidedly at the weight `W = 2` (`2G + M` and `2G − M` both
positive semidefinite) and the witness gap `s = 4` at the cofactor
tie `ς c_W = W²`.

The polarization display stands first (`shiftSite`'s matrix
`[[4,4],[4,16]]` at its integer congruence, positive semidefinite),
then `polar_psd`'s theorem route with the cap's two splits committed
— the site datum `[[3,-1],[-1,3]]` and the sum `[[1,1],[1,1]]`, the
latter's kernel block trailing.  The two count reads follow at the
levels five, six and nine: the compression side (`count_head_le` at
the fiber datum's site tie, the head's count one at or below the
full pencil's own) and the monotone side (`count_full_le` at the
block diagonal of the head at six and the removed block at nine,
whose difference site `[[1,1],[1,4]]` is positive semidefinite).
`shift_psd` reads that difference site through the polarization at
the scaled tie — its fourfold rescaling IS the shift site — and
`removed_psd` closes the removed block at the cross-added level tie
`x + W + g = c + y` (`10 + 2 + 1 = 12 + 1`) with the diagonal at
twelve, the block's magnetic part capped inside it, and the removed
pencil eleven.

Four refusals ride beside them, each isolating one binder.  The cap:
a forged coupling `[5]` takes the shift site to `[[4,20],[20,16]]`
at determinant `−336`, its split occupied, and the forged magnetic
part's own cap refused at the sum's lower-side split.  The width:
the head read at one in place of six leaves the difference site
`[[-4,1],[1,4]]` at determinant `−17`, its mixed block occupied and
the conclusion parting with it, the head's count vacant at one.  The
floor: a forged removed pencil `[3]` takes the full pencil to
`[[2,1],[1,3]]`, negative definite at five and reading count two
against the head's one, the removed block's vacant count at nine
refused.  The clear bracket: a forged head pencil `[5]` reads the
sum's unit at five and one at six, the bracket occupied, while the
full pencil reads one at five.

`cap_sq` closes the module at the order-one probe
`thm:groundreads`(v)'s growth chain carries: the head pencil `[2]`
capped at `[3 : 1]` takes the vector `[1]` to the squared display
`4 ≤ 9`, and the cap forged to `[1 : 1]` — below the probe's own
value — parts the cap at its upper site datum `[-1]` and the display
at `4 ≤ 1`.
-/
set_option maxHeartbeats 4000000

open ground elim inertia certconstruct truncation

namespace truncation

def u : BPair := BPair.unit

/-! The order `1 + 1` fixture: the two diagonal blocks, their grams,
the shared coupling, and the assembled pencils. -/

def pHead : Mat := [[⟨3, 1⟩]]
def gHead : Mat := [[⟨2, 1⟩]]
def qRem : Mat := [[⟨11, 1⟩]]
def gRem : Mat := [[⟨2, 1⟩]]
def bCoup : Mat := [[⟨2, 1⟩]]
def hFull : Mat := inertia.blockJoin pHead bCoup qRem
def gFull : Mat := inertia.blockJoin gHead (elim.nullMat 1 1) gRem
private def mHead : Mat := [[⟨1, 2⟩]]
private def mRem : Mat := [[⟨1, 2⟩]]
private def mFull : Mat := inertia.blockJoin mHead bCoup mRem

/-! The split carriers: the identity congruence at one and two
orders, the mixed 2×2 block, and the three integer congruences the
fixture's data clear at — `T = [[1,1],[0,3]]` at determinant three,
the shears `[[1,-1],[0,1]]` and `[[1,-5],[0,1]]`, and
`[[1,5],[0,3]]`. -/

def spKern : Split 1 :=
  ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [], 1, rfl⟩
def spId (a b : BPair) : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.one a, .one b], 0, rfl⟩
def spMix (a b c : BPair) : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.two a b c], 0, rfl⟩

def tThree : SqMat 2 := ⟨[[⟨2, 1⟩, ⟨2, 1⟩], [u, ⟨4, 1⟩]], rfl⟩
def twThree : SqMat 2 := ⟨[[⟨4, 1⟩, ⟨1, 2⟩], [u, ⟨2, 1⟩]], rfl⟩
def spThree (a b : BPair) : Split 2 :=
  ⟨tThree, twThree, [.one a, .one b], 0, rfl⟩

def tShear : SqMat 2 := ⟨[[⟨2, 1⟩, ⟨1, 2⟩], [u, ⟨2, 1⟩]], rfl⟩
def twShear : SqMat 2 := ⟨[[⟨2, 1⟩, ⟨2, 1⟩], [u, ⟨2, 1⟩]], rfl⟩
def spShear (a b : BPair) : Split 2 :=
  ⟨tShear, twShear, [.one a, .one b], 0, rfl⟩
private def spShearK (a : BPair) : Split 2 :=
  ⟨tShear, twShear, [.one a], 1, rfl⟩

private def tWide : SqMat 2 := ⟨[[⟨2, 1⟩, ⟨1, 6⟩], [u, ⟨2, 1⟩]], rfl⟩
private def twWide : SqMat 2 := ⟨[[⟨2, 1⟩, ⟨6, 1⟩], [u, ⟨2, 1⟩]], rfl⟩
private def spWide (a b : BPair) : Split 2 :=
  ⟨tWide, twWide, [.one a, .one b], 0, rfl⟩

private def tSkew : SqMat 2 := ⟨[[⟨2, 1⟩, ⟨6, 1⟩], [u, ⟨4, 1⟩]], rfl⟩
private def twSkew : SqMat 2 := ⟨[[⟨4, 1⟩, ⟨1, 6⟩], [u, ⟨2, 1⟩]], rfl⟩
private def spSkew (a b : BPair) : Split 2 :=
  ⟨tSkew, twSkew, [.one a, .one b], 0, rfl⟩

/-! The site data at the levels the fixture reads: the full pencil's
site at five, the block diagonal of the head at six with the removed
block at nine, and the head's own site at five (the width binder's
un-shifted read). -/

private def siteFull : Mat :=
  siteDatum (matAdd hFull (matScale 1 gFull)) (matScale 6 gFull)
private def blockDiag : Mat :=
  inertia.blockJoin
    (siteDatum (matAdd pHead (matScale 1 gHead)) (matScale 7 gHead))
    (elim.nullMat 1 1)
    (siteDatum (matAdd qRem (matScale 1 gRem)) (matScale 10 gRem))
private def blockLow : Mat :=
  inertia.blockJoin
    (siteDatum (matAdd pHead (matScale 1 gHead)) (matScale 2 gHead))
    (elim.nullMat 1 1)
    (siteDatum (matAdd qRem (matScale 1 gRem)) (matScale 10 gRem))

end truncation

/-! The polarization display decided: `shiftSite 2 4` at the fixture
reads `[[4,4],[4,16]]`, split at the shear to `diag(4, 12)` and
positive semidefinite — the cofactor tie `ς c_W = W²` at `4 · 1 = 4`
riding the display. -/

example : splitRead (shiftSite 2 4 bCoup gHead gRem)
    (spShear ⟨5, 1⟩ ⟨13, 1⟩) := by decide +kernel
example : psdAt (spShear ⟨5, 1⟩ ⟨13, 1⟩) := by decide +kernel

/-! The cap at the weight two: the site datum `[[3,-1],[-1,3]]`
splits at the determinant-three congruence to `diag(3, 24)` and the
sum `[[1,1],[1,1]]` at the shear to `diag(1, 0)`, its kernel block
trailing — both counts vacant, the two-sided cap read whole. -/

example : splitRead (siteDatum (matScale 2 gFull) mFull)
    (spThree ⟨4, 1⟩ ⟨25, 1⟩) := by decide +kernel
example : splitRead (matAdd (matScale 2 gFull) mFull)
    (spShearK ⟨2, 1⟩) := by decide +kernel
example : capAt mFull (matScale 2 gFull)
    (spThree ⟨4, 1⟩ ⟨25, 1⟩) (spShearK ⟨2, 1⟩) := by decide +kernel

/-! `polar_psd`'s theorem route at the fixture: every hypothesis
discharged by the kernel — the cap, the two blocking ties, the four
order reads and the coupling's shape — and the shift site's positive
semidefiniteness the theorem's own conclusion. -/

example : psdAt (spShear ⟨5, 1⟩ ⟨13, 1⟩) :=
  polar_psd (k := 1) (m := 1) mFull gFull mHead mRem bCoup gHead gRem 2 4
    (spThree ⟨4, 1⟩ ⟨25, 1⟩) (spShearK ⟨2, 1⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (spShear ⟨5, 1⟩ ⟨13, 1⟩) (by decide +kernel)

/-! The three counts the comparison prices: the full pencil at five
reads one at the determinant-three congruence, the head reads one at
five and one at six, and the removed block reads the sum's unit at
nine — the clear bracket at the head's two ends. -/

example : countAtPair hFull gFull 6 1 1 (spThree ⟨1, 4⟩ ⟨49, 1⟩) := by
  decide +kernel
example : countAtPair pHead gHead 6 1 1 (inertia.spOne ⟨1, 4⟩) := by decide +kernel
example : countAtPair pHead gHead 7 1 1 (inertia.spOne ⟨1, 5⟩) := by decide +kernel
example : countAtPair qRem gRem 10 1 0 (inertia.spOne ⟨2, 1⟩) := by decide +kernel

/-! `count_head_le`'s route: the head block's count sits at or below
the full pencil's own, the blocking tie the fiber datum's site read
at one level — the full pencil's site at five IS the join of the two
blocks' sites over the shared coupling. -/

example : matOneValue siteFull
    (inertia.blockJoin
      (siteDatum (matAdd pHead (matScale 1 gHead)) (matScale 6 gHead))
      bCoup
      (siteDatum (matAdd qRem (matScale 1 gRem)) (matScale 6 gRem))) := by
  decide +kernel

example : (1 : Nat) ≤ 1 :=
  count_head_le (k := 1) (m := 1) hFull gFull pHead gHead bCoup qRem gRem
    6 1 1 1 (inertia.spOne ⟨1, 4⟩) (spThree ⟨1, 4⟩ ⟨49, 1⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! `count_full_le`'s route: the shifted block diagonal `[[-4],[1]]`
reads count one — the head's at six alone, the removed block's
vacant at the vacant coupling — and the difference site
`[[1,1],[1,4]]` splits at the shear to `diag(1, 3)`, positive
semidefinite, so the full pencil's count sits at or below the head's
shifted one. -/

example : splitRead blockDiag (spId ⟨1, 5⟩ ⟨2, 1⟩) := by decide +kernel
example : splitRead (siteDatum siteFull blockDiag)
    (spShear ⟨2, 1⟩ ⟨4, 1⟩) := by decide +kernel
example : psdAt (spShear ⟨2, 1⟩ ⟨4, 1⟩) := by decide +kernel

example : (1 : Nat) ≤ 1 :=
  count_full_le (k := 1) (m := 1) hFull gFull pHead gHead qRem gRem
    6 1 7 1 10 1 1 1
    (spThree ⟨1, 4⟩ ⟨49, 1⟩) (inertia.spOne ⟨1, 5⟩) (inertia.spOne ⟨2, 1⟩)
    (spId ⟨1, 5⟩ ⟨2, 1⟩) (spShear ⟨2, 1⟩ ⟨4, 1⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! `shift_psd`'s route: the difference site's fourfold rescaling IS
the shift site (`matScale 4` at the gap's own value), so the
polarization discharges the difference site's positive
semidefiniteness through the scaled tie, the reversal count blind to
the positive factor. -/

example : matOneValue (matScale 4 (siteDatum siteFull blockDiag))
    (shiftSite 2 4 bCoup gHead gRem) := by decide +kernel

example : psdAt (spShear ⟨2, 1⟩ ⟨4, 1⟩) :=
  shift_psd (k := 1) (m := 1) mFull gFull mHead mRem bCoup gHead gRem
    blockDiag siteFull 2 4 (spThree ⟨4, 1⟩ ⟨25, 1⟩) (spShearK ⟨2, 1⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (spShear ⟨2, 1⟩ ⟨4, 1⟩) (by decide +kernel)

/-! `removed_psd`'s route at the removed block: the electric diagonal
twelve sits at or above the cutoff `c = 12` (its site datum the
kernel block alone), the block's magnetic part `[-1]` is capped
inside the block at the weight two, and the level tie
`10 + 2 + 1 = 12 + 1` cross-adds the clearance one — the removed
pencil eleven then reads two at nine, positive semidefinite. -/

private def deRem : Mat := [[⟨13, 1⟩]]
private def qFloor : Mat := [[⟨12, 1⟩]]

example : matOneValue qFloor (matAdd deRem mRem) := by decide +kernel
example : splitRead (siteDatum deRem (matScale 12 gRem)) spKern := by decide +kernel
example : capAt mRem (matScale 2 gRem) (inertia.spOne ⟨4, 1⟩) (inertia.spOne ⟨2, 1⟩) := by
  decide +kernel
example : (10 : Pos) + 2 + 1 = 12 + 1 := by decide +kernel

example : psdAt (inertia.spOne ⟨3, 1⟩) :=
  removed_psd (m := 1) qFloor deRem mRem gRem 12 2 10 1 1
    spKern (inertia.spOne ⟨2, 1⟩) (inertia.spOne ⟨2, 1⟩) (inertia.spOne ⟨3, 1⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The cap binder's refusal: at the forged coupling `[5]` the shift
site reads `[[4,20],[20,16]]` at determinant `−336`, splitting at the
wide shear to `diag(4, −84)` — one lower-side block, the conclusion
refused — and the forged magnetic part's own cap refuses beside it,
its sum `[[1,5],[5,1]]` splitting to `diag(1, −24)`. -/

private def bForge : Mat := [[⟨6, 1⟩]]
private def mForge : Mat := inertia.blockJoin mHead bForge mRem

example : splitRead (shiftSite 2 4 bForge gHead gRem)
    (spWide ⟨5, 1⟩ ⟨1, 85⟩) := by decide +kernel
example : ¬ psdAt (spWide ⟨5, 1⟩ ⟨1, 85⟩) := by decide +kernel
example : splitRead (siteDatum (matScale 2 gFull) mForge)
    (spSkew ⟨4, 1⟩ ⟨1, 49⟩) := by decide +kernel
example : splitRead (matAdd (matScale 2 gFull) mForge)
    (spWide ⟨2, 1⟩ ⟨1, 25⟩) := by decide +kernel
example : ¬ capAt mForge (matScale 2 gFull)
    (spSkew ⟨4, 1⟩ ⟨1, 49⟩) (spWide ⟨2, 1⟩ ⟨1, 25⟩) := by decide +kernel

/-! `count_shift_le`'s route, the display composed: the full pencil's
count at five sits at or below the head's at six with the removed
block vacant at nine, the cap and the scaled tie the polarization's
own data — the bracket display's read whole at the fixture, the
width the cofactor's own at `4 · 1 = 2²`. -/

example : (1 : Nat) ≤ 1 :=
  count_shift_le (k := 1) (m := 1) hFull gFull mFull mHead mRem
    pHead gHead qRem gRem bCoup 6 1 1 2 4 1 1
    (spThree ⟨4, 1⟩ ⟨25, 1⟩) (spShearK ⟨2, 1⟩)
    (spThree ⟨1, 4⟩ ⟨49, 1⟩) (spId ⟨1, 5⟩ ⟨2, 1⟩)
    (spShear ⟨2, 1⟩ ⟨4, 1⟩) (inertia.spOne ⟨1, 5⟩) (inertia.spOne ⟨2, 1⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The width binder's refusal: the head read at one in place of six
leaves the difference site `[[-4,1],[1,4]]` at determinant `−17`,
one mixed block, its count occupied — and the conclusion parts with
it, the head's count vacant at one against the full pencil's one.
Every co-binder survives: the block diagonal `diag(1,1)` splits
positive semidefinite and the removed block's vacant count holds. -/

example : countAtPair pHead gHead 2 1 0 (inertia.spOne ⟨2, 1⟩) := by decide +kernel
example : splitRead blockLow (spId ⟨2, 1⟩ ⟨2, 1⟩) := by decide +kernel
example : psdAt (spId ⟨2, 1⟩ ⟨2, 1⟩) := by decide +kernel
example : splitRead (siteDatum siteFull blockLow)
    (spMix ⟨1, 5⟩ ⟨2, 1⟩ ⟨5, 1⟩) := by decide +kernel
example : ¬ psdAt (spMix ⟨1, 5⟩ ⟨2, 1⟩ ⟨5, 1⟩) := by decide +kernel
example : ¬ ((1 : Nat) ≤ 0) := by decide +kernel

/-! The floor binder's refusal: at the forged removed pencil `[3]` the
full pencil `[[2,1],[1,3]]` is negative definite at five and reads
count two against the head's one, so the monotone comparison's
conclusion fails; the removed block's own vacant count at nine is
refused beside it, its site reading `[-6]`. -/

namespace truncation
def qForge : Mat := [[⟨4, 1⟩]]
def hForge : Mat := inertia.blockJoin pHead bCoup qForge
end truncation

example : countAtPair hForge gFull 6 1 2 (spThree ⟨1, 4⟩ ⟨1, 16⟩) := by
  decide +kernel
example : countAtPair pHead gHead 6 1 1 (inertia.spOne ⟨1, 4⟩) := by decide +kernel
example : ¬ ((2 : Nat) ≤ 1) := by decide +kernel
example : ¬ countAtPair qForge gRem 10 1 0 (inertia.spOne ⟨1, 7⟩) := by decide +kernel
example : countAtPair qForge gRem 10 1 1 (inertia.spOne ⟨1, 7⟩) := by decide +kernel

/-! The clear bracket's refusal: at the forged head pencil `[5]` the
head reads the sum's unit at five and one at six, the bracket
occupied, while the full pencil `[[5,1],[1,10]]` reads one at five —
the two head counts part and the compression's transported integer
is refused. -/

namespace truncation
def pForge : Mat := [[⟨6, 1⟩]]
def hBracket : Mat := inertia.blockJoin pForge bCoup qRem
end truncation

example : countAtPair pForge gHead 6 1 0 spKern := by decide +kernel
example : countAtPair pForge gHead 7 1 1 (inertia.spOne ⟨1, 2⟩) := by decide +kernel
example : countAtPair hBracket gFull 6 1 1 (spMix u ⟨2, 1⟩ ⟨6, 1⟩) := by
  decide +kernel
example : ¬ ((1 : Nat) = 0) := by decide +kernel

/-! `thm:groundreads`(v)'s growth chain caps its probe through
`cap_sq`: the head pencil `[2]` capped at `[3 : 1]` — the upper site
datum `[1]` and the sum `[5]` both positive semidefinite — carries
the order-one vector `[1]` to the squared display `4 ≤ 9`, decided
beside the theorem route. -/

private def vOne : List BPair := [⟨2, 1⟩]

example : capAt (matScale 1 pHead) (matScale 3 (idMat 1))
    (inertia.spOne ⟨2, 1⟩) (inertia.spOne ⟨6, 1⟩) := by decide +kernel

example : (dotN (matVec pHead vOne) (matVec pHead vOne)).scale ((1 : Pos) * 1)
    ≤ (dotN vOne vOne).scale ((3 : Pos) * 3) := by decide +kernel

example : (dotN (matVec pHead vOne) (matVec pHead vOne)).scale ((1 : Pos) * 1)
    ≤ (dotN vOne vOne).scale ((3 : Pos) * 3) :=
  cap_sq pHead 3 1 (inertia.spOne ⟨2, 1⟩) (inertia.spOne ⟨6, 1⟩)
    (by decide +kernel) vOne rfl

/-- The refusal isolating `cap_sq`'s cap binder: at `[1 : 1]`, below
the probe's own value, the upper site datum reads `[-1]` at one
lower-side block, the cap refused and the display parting at `4`
against `1`. -/
example : splitRead (siteDatum (matScale 1 (idMat 1)) (matScale 1 pHead))
    (inertia.spOne ⟨1, 2⟩) := by decide +kernel
example : ¬ psdAt (inertia.spOne ⟨1, 2⟩) := by decide +kernel
example : ¬ capAt (matScale 1 pHead) (matScale 1 (idMat 1))
    (inertia.spOne ⟨1, 2⟩) (inertia.spOne ⟨4, 1⟩) := by decide +kernel
example : ¬ ((dotN (matVec pHead vOne)
      (matVec pHead vOne)).scale ((1 : Pos) * 1)
    ≤ (dotN vOne vOne).scale ((1 : Pos) * 1)) := by decide +kernel
