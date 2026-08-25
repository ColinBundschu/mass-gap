import MassGap.Grading
import MassGapChecks.Fiberdec
import MassGap.Fiberdec
/-!
The check module for `lem:grading`: the batteries re-read the
tower rows' repetition off the collar by kernel `decide`.  The
collar read pins at the deep and collar labels with the vacuum;
the deep rows read whole — over every shape at the matched degree
the count reads the content list at the tie — at the definitional
count for `d = 2`, the fast count for `d = 3`, and the
formula-side fold with its vacant odd read for `d = 4, 5`, the
deep diagonals reading the residue throughout; the theorem route
discharges every binder of `deepRow` at `d = 2` with the computed
twin beside it.  The member rows read at `B_2`: at the graded
orbit of `κ = λ + ρ` for `λ = (2,2)` against the member `θ`
content list the even fold reads the content count at the
withdrawn key and the odd fold the sum's zero, the route running
at the tower key, at its reflected image and at a key off the
row's support, with the exhaustion's own read beside them.

The binder classification.  `hd` is load-bearing with its
committed refusal: at `d = 1` the label `[0]` sits off the collar
vacuously, the `cor:steinberg` tie holds, and
the conclusion refuses — the adjoint's shape reads degree two
against the count there, the frame `con:places` declares.  `hdeep`
is load-bearing with its committed refusals: at the collar tower
`(4,2,2)` the graded fold occupies its odd side and the count
reads the walk's diagonal two (`prop:row`) against the content
formula's three, and at the vacuum, off the collar vacuously at
one row, the theorem's own conclusion refuses with every
co-binder standing, the fundamental's row against the unit
content's residue read.  `hld` and `hcd` are frame records: the probed
wrong-length forgeries read both sides at the sum's unit with the
conclusion standing, the display and tie bookkeeping the frames'
consumers.  The content formula's agreement at the adjoint's span
is no binder of the display: `lem:adjchar`'s general theorem
(`adjchar.occupancy`) reads it inside `channels.sumsWith_agree`,
and the graded-sum read enters the proof through
`steinberg.readAll` at the width frames.

`memberRows`' binders classify at the member tier, and its
retained binder set is its consumed set: every one is read in the
proof, none dropped.  `hoff` is load-bearing with its committed
refusal: at the collar's own graded orbit — the tower key
`θ + ρ`, where the top read still stands — the clearance refuses,
no positive root's doubled pairing clearing the count's successor
there.  `hmag` is load-bearing with its committed refusal: a
forged member beyond the count's multiple of the square refuses
the cap.  `htop` is load-bearing with its committed refusal: at
the orbit carrying its top twice the even fold reads four against
the content list's two, the clearance, the shape read, the cap,
the ρ-length read and the dominance all standing there.  `hlam`
and `hcV` are frame records: the probed over-long forgeries read
the shifted key and the withdrawal back at the fixture's own with
the conclusion standing, the additivity's length bookkeeping the
frames' consumer.  `hdomC` is load-bearing with its committed
refusals: a non-dominant target refuses the even conjunct — the
graded fold occupied where the withdrawal reads no content — and
a second refuses the odd, the vacant side occupied there, every
co-binder standing at both.  `hshape`, `hgsym`, `hwsh`, `hmsh`
and `hrho` are coherence binders discharged per instance by
`decide` — the shape and the Gram symmetry the pairing's split
and slot exchange, the two list shapes the members' orders, the
ρ-length read the square's positivity with the doubled ρ-dot.

The `G_2` tier reads the tex's clearance at both counts: the
`(3,3)` orbit at count three runs the display whole, while the
`(2,2)` orbit clears count two and refuses three with the cap
refusing two — `lem:grading`'s "two off `G_2` and three at
it". -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground places grading fiberdec

/-! The collar read: the deep labels refuse it, the collar tower
and the vacuum hold it. -/

example : ¬ collarAt [4, 0] := by decide +kernel
example : ¬ collarAt [2, 2, 0] := by decide +kernel
example : collarAt [2, 0, 2, 0] := by decide +kernel
example : collarAt [0, 0, 0] := by decide +kernel

/-! The deep row's read: the unit content at the residue's count,
a root move at one, the sum's unit at an absent tie. -/

example : rowRead 3 [1, 1, 0] [1, 1, 1] = 2 := by decide +kernel
example : rowRead 5 [2, 2, 2, 2, 0] [4, 1, 2, 2, 1] = 1 := by decide +kernel
example : rowRead 3 [1, 1, 0] [0, 0, 0] = 0 := by decide +kernel

/-! The whole rows at the definitional count, `d = 2`: over every
shape at the matched degree the fusion count is the content read
at the tie. -/

example : ((places.allShapes 2 (places.degree [4, 0] + 2)).all
    (fun c => blockcount.fusionCount (adjchar.theta 2) [4, 0] c
      == rowRead 2 [4, 0] c)) = true := by decide +kernel
example : ((places.allShapes 2 (places.degree [6, 0] + 2)).all
    (fun c => blockcount.fusionCount (adjchar.theta 2) [6, 0] c
      == rowRead 2 [6, 0] c)) = true := by decide +kernel

/-! The whole rows at the fast count, `d = 3`. -/

example : ((places.allShapes 3 (places.degree [2, 2, 0] + 3)).all
    (fun c => steinberg.count (adjchar.theta 3) [2, 2, 0] c
      == rowRead 3 [2, 2, 0] c)) = true := by decide +kernel
example : ((places.allShapes 3 (places.degree [3, 3, 0] + 3)).all
    (fun c => steinberg.count (adjchar.theta 3) [3, 3, 0] c
      == rowRead 3 [3, 3, 0] c)) = true := by decide +kernel

/-! The whole rows at the formula-side fold, `d = 4, 5`: the even
side reads the row and the odd side is vacant at every target. -/

example : ((places.allShapes 4 (places.degree [2, 2, 2, 0] + 4)).all
    (fun c =>
      steinberg.sumsWith (adjchar.multRead 4) 4 [2, 2, 2, 0] c
        == (rowRead 4 [2, 2, 2, 0] c, 0))) = true := by decide +kernel
example : ((places.allShapes 4 (places.degree [3, 2, 2, 0] + 4)).all
    (fun c =>
      steinberg.sumsWith (adjchar.multRead 4) 4 [3, 2, 2, 0] c
        == (rowRead 4 [3, 2, 2, 0] c, 0))) = true := by decide +kernel
example : ((places.allShapes 5
      (places.degree [2, 2, 2, 2, 0] + 5)).all
    (fun c =>
      steinberg.sumsWith (adjchar.multRead 5) 5 [2, 2, 2, 2, 0] c
        == (rowRead 5 [2, 2, 2, 2, 0] c, 0))) = true := by decide +kernel

/-! The deep diagonals read the residue. -/

example : blockcount.fusionCount (adjchar.theta 2) [4, 0] [4, 1]
    = 1 := by decide +kernel
example : steinberg.count (adjchar.theta 3) [2, 2, 0] [2, 2, 1]
    = 2 := by decide +kernel
example : steinberg.sumsWith (adjchar.multRead 4) 4
    [2, 2, 2, 0] [2, 2, 2, 1] = (3, 0) := by decide +kernel
example : steinberg.sumsWith (adjchar.multRead 5) 5
    [2, 2, 2, 2, 0] [2, 2, 2, 2, 1] = (4, 0) := by decide +kernel

/-! The theorem route at `d = 2`, every binder discharged, with
the computed twin. -/

example : blockcount.fusionCount (adjchar.theta 2) [4, 0] [4, 1]
    = rowRead 2 [4, 0] [4, 1] :=
  deepRow 2 [4, 0] [4, 1] (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
example : blockcount.fusionCount (adjchar.theta 2) [4, 0] [4, 1]
    = rowRead 2 [4, 0] [4, 1] := by decide +kernel

/-! The collar refusal, `hdeep`'s isolation: at the tower
`(4,2,2)` the graded fold occupies its odd side, the count reads
the walk's diagonal two against the content formula's three. -/

example : steinberg.sumsWith (adjchar.multRead 4) 4
    [2, 0, 2, 0] [2, 0, 2, 1] = (3, 1) := by decide +kernel
example : rowRead 4 [2, 0, 2, 0] [2, 0, 2, 1] = 3 := by decide +kernel
example : ¬ (steinberg.sumsWith (adjchar.multRead 4) 4
      [2, 0, 2, 0] [2, 0, 2, 1]
    = (rowRead 4 [2, 0, 2, 0] [2, 0, 2, 1], 0)) := by decide +kernel

/-! The frame refusal, `hd`'s isolation: at `d = 1` every further
binder holds and the conclusion refuses, the adjoint's shape at
degree two against the count. -/

example : ¬ collarAt [0] := by decide +kernel
example : ¬ (blockcount.fusionCount (adjchar.theta 1) [0] [2]
    = rowRead 1 [0] [2]) := by decide +kernel

/-! The collar refusal at the theorem's own conclusion: the vacuum
sits off the collar vacuously at one row, every co-binder holds,
and the fundamental's row refuses the unit content's read. -/

example : collarAt [0, 0] := by decide +kernel
example : ¬ (blockcount.fusionCount (adjchar.theta 2) [0, 0] [0, 1]
    = rowRead 2 [0, 0] [0, 1]) := by decide +kernel

/-! The frame records, `hld` and `hcd`: the probed wrong-length
forgeries read both sides at the sum's unit, the conclusion
standing. -/

example : blockcount.fusionCount (adjchar.theta 2) [4] [4, 1] = 0
    := by decide +kernel
example : rowRead 2 [4] [4, 1] = 0 := by decide +kernel
example : blockcount.fusionCount (adjchar.theta 2) [4, 0] [4, 1, 0]
    = 0 := by decide +kernel
example : rowRead 2 [4, 0] [4, 1, 0] = 0 := by decide +kernel

/-! The index grading at the plaquette chain of nine squares: the
support's band components, their contents, and the separation
read.  The band's coupling is the plaquette reach — two links
adjacent where one boundary meets both links' ends — so a single
square's support is one component, two squares four apart are two,
and the adjacent and the once-interposed pairs are one, the
interposed plaquette's own reach coupling them. -/

private def R9 : lattice.Region := fiberdec.chainRegion 9

/-! The support and the band adjacency: the loop occupies its
square's four links, the square's own links couple and a link four
squares along does not. -/

example : carrier.support (fusion.dataA 3) R9 (loopAt 9 0)
    = [0, 1, 9, 18] := by decide +kernel
example : bandAdj R9 0 1 = true := by decide +kernel
example : bandAdj R9 0 18 = true := by decide +kernel
example : bandAdj R9 0 4 = false := by decide +kernel

/-! The band components: one part at a single square, two at the
four-apart join, and one at the adjacent join and at the
once-interposed join alike — the interposed plaquette's boundary
meets both squares' rungs, the adjacency's own reach. -/

example : (components (fusion.dataA 3) R9 (loopAt 9 0)).length = 1
    := by decide +kernel
example : (components (fusion.dataA 3) R9
    (stableentries.joinConf (fusion.dataA 3) R9
      (loopAt 9 0) (loopAt 9 4))).length = 2 := by decide +kernel
example : (components (fusion.dataA 3) R9
    (stableentries.joinConf (fusion.dataA 3) R9
      (loopAt 9 0) (loopAt 9 1))).length = 1 := by decide +kernel
example : (components (fusion.dataA 3) R9
    (stableentries.joinConf (fusion.dataA 3) R9
      (loopAt 9 0) (loopAt 9 2))).length = 1 := by decide +kernel

/-! The components' contents: the electric diagonal's per-part
read, the loop's four fundamental labels at the cleared Casimir. -/

example : (components (fusion.dataA 3) R9 (loopAt 9 0)).map
    (compContent (fusion.dataA 3) (loopAt 9 0)) = [32] := by decide +kernel
example : (components (fusion.dataA 3) R9
      (stableentries.joinConf (fusion.dataA 3) R9
        (loopAt 9 0) (loopAt 9 4))).map
    (compContent (fusion.dataA 3)
      (stableentries.joinConf (fusion.dataA 3) R9
        (loopAt 9 0) (loopAt 9 4))) = [32, 32] := by decide +kernel

/-! The separation read: the four-apart squares' reach
neighborhoods are disjoint, the once-interposed squares' overlap. -/

example : sepBeyond (fusion.dataA 3) R9 (loopAt 9 0) (loopAt 9 4)
    := by decide +kernel
example : ¬ sepBeyond (fusion.dataA 3) R9 (loopAt 9 0) (loopAt 9 2)
    := by decide +kernel

/-! The stencil row's changed-edge read at a near plaquette: a row
target of the neighbouring square keeps the loop's label at the
rung off that boundary, the theorem's route at a stated target with
the computed twin. -/

private def rowTarget : List Shape :=
  [[1, 0, 0], [1, 2, 0], [1, 1, 0], [0, 0, 0], [0, 0, 0],
   [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 1, 0],
   [1, 1, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0],
   [0, 0, 0], [0, 0, 0], [0, 0, 0], [1, 0, 0], [1, 1, 0],
   [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0],
   [0, 0, 0], [0, 0, 0]]

example : ground.getAt (fusion.dataA 3).unit rowTarget 0
    = ground.getAt (fusion.dataA 3).unit (loopAt 9 0) 0 :=
  algebra.plaqRow_keep (fusion.dataA 3) R9
    (ground.getAt [] R9.plaqs 1) (loopAt 9 0) rowTarget
    (by decide +kernel) 0 (by decide +kernel) (by decide +kernel)
example : ground.getAt (fusion.dataA 3).unit rowTarget 0
    = ground.getAt (fusion.dataA 3).unit (loopAt 9 0) 0 := by decide +kernel

/-! The member rows at `B_2`.  The fixture is the graded orbit of
the tower key `κ = λ + ρ` at `λ = (2,2)`, generated by the
reflection letters with the letter-count parities, against the
member `θ` content list (`prop:row`'s own literal).  The two reads
pin at the fixture, every binder of `memberRows` discharges by
`decide`, and the theorem route runs at three dominant keys with
its computed twins; the deep diagonal reads the rank's two — the
unit content's count in the `θ` list — against the collar's
`θ`-support one (`prop:row`). -/

private def tB : gentable.Table := sertables.tableB 2
private def lamD : List BPair := [BPair.ofNat 2, BPair.ofNat 2]
private def zV : List BPair := [BPair.unit, BPair.unit]

private def kapD : List BPair :=
  poly.pnorm (elim.vecAdd lamD (sertables.rhoV tB))

private def wDeep : List (List BPair × Bool) :=
  [([BPair.ofNat 3, BPair.ofNat 3], false),
   ([(BPair.ofNat 3).swap, BPair.ofNat 9], true),
   ([BPair.ofNat 6, (BPair.ofNat 3).swap], true),
   ([BPair.ofNat 6, (BPair.ofNat 9).swap], false),
   ([(BPair.ofNat 6).swap, BPair.ofNat 9], false),
   ([(BPair.ofNat 6).swap, BPair.ofNat 3], true),
   ([BPair.ofNat 3, (BPair.ofNat 9).swap], true),
   ([(BPair.ofNat 3).swap, (BPair.ofNat 3).swap], false)]

private def thFamB2 : List (List BPair) :=
  [zV, zV,
   [BPair.ofNat 2, (BPair.ofNat 2).swap],
   [BPair.unit, BPair.ofNat 2],
   [BPair.ofNat 1, BPair.unit],
   [(BPair.ofNat 1).swap, BPair.ofNat 2],
   [(BPair.ofNat 2).swap, BPair.ofNat 2],
   [BPair.unit, (BPair.ofNat 2).swap],
   [(BPair.ofNat 1).swap, BPair.unit],
   [BPair.ofNat 1, (BPair.ofNat 2).swap]]

/-- The tower key's own reflection image, a further dominant key of
the row. -/
private def cR : List BPair :=
  poly.pnorm (elim.vecAdd lamD [BPair.ofNat 2, (BPair.ofNat 2).swap])

/-- A dominant key off the row's support. -/
private def cO : List BPair := [BPair.ofNat 3, BPair.ofNat 1]

/-! The two reads at the fixture beside the frame and coherence
binders `memberRows` consumes. -/

example : assembly.wTopAt wDeep kapD := by decide +kernel
example : offTopAt tB sertables.fundB2 wDeep 2 kapD := by decide +kernel
example : magAt tB sertables.fundB2 thFamB2 2 := by decide +kernel
example : sertables.fundShape tB sertables.fundB2 := by decide +kernel
example : sertables.gramSymRead sertables.fundB2 := by decide +kernel
example : row.rhoLenRead tB sertables.fundB2 := by decide +kernel
example : sertables.wShapeRead tB wDeep := by decide +kernel
example : memberchar.mShapeRead tB thFamB2 := by decide +kernel

/-! The theorem route at the tower key: the even fold reads the
content list's count at the vacant withdrawal — the rank's two —
and the odd fold reads the sum's zero. -/

example : memberchar.convCount wDeep thFamB2
      (poly.pnorm (elim.vecAdd lamD (sertables.rhoV tB))) false
    = ground.countOf
        (poly.pnorm (elim.vecAdd lamD (poly.neg lamD))) thFamB2
  ∧ memberchar.convCount wDeep thFamB2
      (poly.pnorm (elim.vecAdd lamD (sertables.rhoV tB))) true = 0 :=
  memberRows tB sertables.fundB2 wDeep thFamB2 lamD lamD 2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
example : memberchar.convCount wDeep thFamB2
    (poly.pnorm (elim.vecAdd lamD (sertables.rhoV tB))) false = 2 :=
  by decide +kernel
example : memberchar.convCount wDeep thFamB2
    (poly.pnorm (elim.vecAdd lamD (sertables.rhoV tB))) true = 0 :=
  by decide +kernel
example : ground.countOf
    (poly.pnorm (elim.vecAdd lamD (poly.neg lamD))) thFamB2 = 2 :=
  by decide +kernel

/-! The route at the reflected key, the row's one at the moved
content, and at a key off the support, the row's vacancy. -/

example : memberchar.convCount wDeep thFamB2
      (poly.pnorm (elim.vecAdd cR (sertables.rhoV tB))) false
    = ground.countOf
        (poly.pnorm (elim.vecAdd cR (poly.neg lamD))) thFamB2
  ∧ memberchar.convCount wDeep thFamB2
      (poly.pnorm (elim.vecAdd cR (sertables.rhoV tB))) true = 0 :=
  memberRows tB sertables.fundB2 wDeep thFamB2 lamD cR 2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
example : memberchar.convCount wDeep thFamB2
    (poly.pnorm (elim.vecAdd cR (sertables.rhoV tB))) false = 1 :=
  by decide +kernel
example : ground.countOf
    (poly.pnorm (elim.vecAdd cR (poly.neg lamD))) thFamB2 = 1 :=
  by decide +kernel

example : memberchar.convCount wDeep thFamB2
      (poly.pnorm (elim.vecAdd cO (sertables.rhoV tB))) false
    = ground.countOf
        (poly.pnorm (elim.vecAdd cO (poly.neg lamD))) thFamB2
  ∧ memberchar.convCount wDeep thFamB2
      (poly.pnorm (elim.vecAdd cO (sertables.rhoV tB))) true = 0 :=
  memberRows tB sertables.fundB2 wDeep thFamB2 lamD cO 2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
example : memberchar.convCount wDeep thFamB2
    (poly.pnorm (elim.vecAdd cO (sertables.rhoV tB))) false = 0 :=
  by decide +kernel
example : ground.countOf
    (poly.pnorm (elim.vecAdd cO (poly.neg lamD))) thFamB2 = 0 :=
  by decide +kernel

/-! The member row read back at the exhaustion: the tower key sits
in the stated list twice, the content list's own count. -/

private def cVsD : List (List BPair) := [lamD, lamD]

example : steinberg.memberAt tB wDeep thFamB2 cVsD lamD := by decide +kernel
example : ground.countOf lamD cVsD
    = ground.countOf
        (poly.pnorm (elim.vecAdd lamD (poly.neg lamD))) thFamB2 :=
  memberRow tB sertables.fundB2 wDeep thFamB2 lamD lamD 2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) cVsD (by decide +kernel)
example : ground.countOf lamD cVsD = 2 := by decide +kernel

/-! The binders' isolating refusals.  The clearance refuses at the
collar's own graded orbit — the tower key `θ + ρ`, where the top
read still stands — the content cap refuses at a forged member
beyond the multiple, and the top read refuses at the orbit with
its top duplicated, the even fold moving off the content count
with every co-binder standing. -/

private def wKap1B2 : List (List BPair × Bool) :=
  [([BPair.ofNat 1, BPair.ofNat 3], false),
   ([(BPair.ofNat 1).swap, BPair.ofNat 5], true),
   ([BPair.ofNat 4, (BPair.ofNat 3).swap], true),
   ([BPair.ofNat 4, (BPair.ofNat 5).swap], false),
   ([(BPair.ofNat 4).swap, BPair.ofNat 5], false),
   ([(BPair.ofNat 4).swap, BPair.ofNat 3], true),
   ([BPair.ofNat 1, (BPair.ofNat 5).swap], true),
   ([(BPair.ofNat 1).swap, (BPair.ofNat 3).swap], false)]

private def wDup : List (List BPair × Bool) :=
  ([BPair.ofNat 3, BPair.ofNat 3], false) :: wDeep

example : assembly.wTopAt wKap1B2
    (poly.pnorm (elim.vecAdd (row.thetaV tB) (sertables.rhoV tB))) :=
  by decide +kernel
example : ¬ offTopAt tB sertables.fundB2 wKap1B2 2
    (poly.pnorm (elim.vecAdd (row.thetaV tB) (sertables.rhoV tB))) :=
  by decide +kernel

example : ¬ magAt tB sertables.fundB2
    (thFamB2 ++ [[BPair.ofNat 3, BPair.unit]]) 2 := by decide +kernel

example : ¬ assembly.wTopAt wDup kapD := by decide +kernel
example : offTopAt tB sertables.fundB2 wDup 2 kapD := by decide +kernel
example : sertables.wShapeRead tB wDup := by decide +kernel
example : ¬ (memberchar.convCount wDup thFamB2
      (poly.pnorm (elim.vecAdd lamD (sertables.rhoV tB))) false
    = ground.countOf
        (poly.pnorm (elim.vecAdd lamD (poly.neg lamD))) thFamB2) :=
  by decide +kernel

/-! The dominance binder's isolating refusals: a non-dominant
target refuses the even conjunct and a second the odd, every
co-binder standing at both. -/

private def cND : List BPair :=
  [(BPair.ofNat 4).swap, (BPair.ofNat 4).swap]
private def cOdd : List BPair :=
  [BPair.ofNat 3, (BPair.ofNat 2).swap]

example : ¬ (∀ j, j < tB.posFolds.length →
    BPair.unit ≤ sertables.dotB sertables.fundB2 cND
      (sertables.posCorootV tB j)) := by decide +kernel
example : ¬ (memberchar.convCount wDeep thFamB2
      (poly.pnorm (elim.vecAdd cND (sertables.rhoV tB))) false
    = ground.countOf
        (poly.pnorm (elim.vecAdd cND (poly.neg lamD))) thFamB2) :=
  by decide +kernel
example : ¬ (∀ j, j < tB.posFolds.length →
    BPair.unit ≤ sertables.dotB sertables.fundB2 cOdd
      (sertables.posCorootV tB j)) := by decide +kernel
example : ¬ (memberchar.convCount wDeep thFamB2
      (poly.pnorm (elim.vecAdd cOdd (sertables.rhoV tB))) true
    = 0) := by decide +kernel

/-! The frame records' reads: the over-long forgeries' folds stand
at the fixture's own values, the length bookkeeping absorbing the
surplus keys. -/

private def lamF : List BPair :=
  [BPair.ofNat 2, BPair.ofNat 2, BPair.ofNat 2]

example : ground.countOf
    (poly.pnorm (elim.vecAdd lamD (poly.neg lamF))) thFamB2 = 2 :=
  by decide +kernel
example : memberchar.convCount wDeep thFamB2
    (poly.pnorm (elim.vecAdd lamF (sertables.rhoV tB))) false
    = 2 := by decide +kernel

/-! The two separation reads part at the once-interposed pair: the
supports share no vertex while the reach neighborhoods overlap,
the vertex-level read holding where the band-level refuses. -/

example : stableentries.disjSupp (fusion.dataA 3) R9
    (loopAt 9 0) (loopAt 9 2) := by decide +kernel

/-! The `G_2` tier at count three: the deep orbit of `(3,3)` runs
the display whole — the diagonal at the rank with a root move at
one — and the `(2,2)` orbit is the collar's record, clearing count
two and refusing three with the cap refusing two. -/

private def tG : gentable.Table := sertables.tableG2
private def lamG : List BPair := [BPair.ofNat 3, BPair.ofNat 3]
private def zVG : List BPair := [BPair.unit, BPair.unit]
private def kapG : List BPair :=
  poly.pnorm (elim.vecAdd lamG (sertables.rhoV tG))
private def wG : List (List BPair × Bool) :=
  [([BPair.ofNat 4, BPair.ofNat 4], false),
   ([(BPair.ofNat 4).swap, BPair.ofNat 8], true),
   ([BPair.ofNat 16, (BPair.ofNat 4).swap], true),
   ([BPair.ofNat 20, (BPair.ofNat 8).swap], false),
   ([(BPair.ofNat 16).swap, BPair.ofNat 12], false),
   ([(BPair.ofNat 20).swap, BPair.ofNat 12], true),
   ([BPair.ofNat 20, (BPair.ofNat 12).swap], true),
   ([BPair.ofNat 16, (BPair.ofNat 12).swap], false),
   ([(BPair.ofNat 20).swap, BPair.ofNat 8], false),
   ([(BPair.ofNat 16).swap, BPair.ofNat 4], true),
   ([BPair.ofNat 4, (BPair.ofNat 8).swap], true),
   ([(BPair.ofNat 4).swap, (BPair.ofNat 4).swap], false)]
private def thFamG2 : List (List BPair) :=
  [zVG, zVG,
   [BPair.ofNat 2, (BPair.ofNat 1).swap],
   [(BPair.ofNat 3).swap, BPair.ofNat 2],
   [(BPair.ofNat 1).swap, BPair.ofNat 1],
   [BPair.ofNat 1, BPair.unit],
   [BPair.ofNat 3, (BPair.ofNat 1).swap],
   [BPair.unit, BPair.ofNat 1],
   [(BPair.ofNat 2).swap, BPair.ofNat 1],
   [BPair.ofNat 3, (BPair.ofNat 2).swap],
   [BPair.ofNat 1, (BPair.ofNat 1).swap],
   [(BPair.ofNat 1).swap, BPair.unit],
   [(BPair.ofNat 3).swap, BPair.ofNat 1],
   [BPair.unit, (BPair.ofNat 1).swap]]
private def cRG : List BPair := poly.pnorm (elim.vecAdd lamG
  [BPair.ofNat 2, (BPair.ofNat 1).swap])

example : offTopAt tG sertables.fundG2 wG 3 kapG := by decide +kernel
example : magAt tG sertables.fundG2 thFamG2 3 := by decide +kernel

example : memberchar.convCount wG thFamG2
      (poly.pnorm (elim.vecAdd lamG (sertables.rhoV tG))) false
    = ground.countOf
        (poly.pnorm (elim.vecAdd lamG (poly.neg lamG))) thFamG2 :=
  (memberRows tG sertables.fundG2 wG thFamG2 lamG lamG 3
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)).1
example : memberchar.convCount wG thFamG2
      (poly.pnorm (elim.vecAdd lamG (sertables.rhoV tG))) false = 2
    ∧ memberchar.convCount wG thFamG2
      (poly.pnorm (elim.vecAdd lamG (sertables.rhoV tG))) true = 0
    ∧ ground.countOf
      (poly.pnorm (elim.vecAdd lamG (poly.neg lamG))) thFamG2 = 2 :=
  by decide +kernel
example : memberchar.convCount wG thFamG2
      (poly.pnorm (elim.vecAdd cRG (sertables.rhoV tG))) false
    = ground.countOf
        (poly.pnorm (elim.vecAdd cRG (poly.neg lamG))) thFamG2 :=
  (memberRows tG sertables.fundG2 wG thFamG2 lamG cRG 3
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)).1
example : memberchar.convCount wG thFamG2
      (poly.pnorm (elim.vecAdd cRG (sertables.rhoV tG))) false = 1
    ∧ ground.countOf
      (poly.pnorm (elim.vecAdd cRG (poly.neg lamG))) thFamG2 = 1 :=
  by decide +kernel

private def w2G : List (List BPair × Bool) :=
  [([BPair.ofNat 3, BPair.ofNat 3], false),
   ([(BPair.ofNat 3).swap, BPair.ofNat 6], true),
   ([BPair.ofNat 12, (BPair.ofNat 3).swap], true),
   ([BPair.ofNat 15, (BPair.ofNat 6).swap], false),
   ([(BPair.ofNat 12).swap, BPair.ofNat 9], false),
   ([(BPair.ofNat 15).swap, BPair.ofNat 9], true),
   ([BPair.ofNat 15, (BPair.ofNat 9).swap], true),
   ([BPair.ofNat 12, (BPair.ofNat 9).swap], false),
   ([(BPair.ofNat 15).swap, BPair.ofNat 6], false),
   ([(BPair.ofNat 12).swap, BPair.ofNat 3], true),
   ([BPair.ofNat 3, (BPair.ofNat 6).swap], true),
   ([(BPair.ofNat 3).swap, (BPair.ofNat 3).swap], false)]
private def kap2G : List BPair := [BPair.ofNat 3, BPair.ofNat 3]

example : assembly.wTopAt w2G kap2G := by decide +kernel
example : offTopAt tG sertables.fundG2 w2G 2 kap2G := by decide +kernel
example : ¬ offTopAt tG sertables.fundG2 w2G 3 kap2G := by decide +kernel
example : ¬ magAt tG sertables.fundG2 thFamG2 2 := by decide +kernel
