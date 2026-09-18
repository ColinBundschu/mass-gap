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

The index grading at the plaquette chains of nine and eleven
squares: the band components at the closures with their contents,
the band neighborhood and the separation read at both chains (every
two loops within the band on the nine-square chain, the five-apart
pair beyond it on the eleven-square one), the two direction reads
and the head at stated head bounds, the graded index's partition of
stated indices, the partition's content identity, the closures'
stationarity, the stencil row's reach and the border row's further
component, each theorem route beside its kernel twin.
`components_border`'s binders: the neighborhood read is load-bearing
with its committed refusal at the once-interposed plaquette, whose
far target keeps the loop's one component; the region binder at the
forged two-rung word off the region's plaquettes, whose far target
reads each rung as its own component; the plaquette and shape reads
are the region's frame (`con:lattice`'s plaquette words at the
region's links, the region's shape read) and the occupied `θ` the
interface's own, each read in the proof.  `contentN_components`'
width binder is load-bearing at the key adjoined beyond the region's
range; `closure_stationary`'s distinctness and count binders are the
support's own reads.

The `G_2` tier reads the tex's clearance at both counts: the
`(3,3)` orbit at count three runs the display whole, while the
`(2,2)` orbit clears count two and refuses three with the cap
refusing two — `lem:grading`'s "two off `G_2` and three at
it". -/

namespace grading
set_option maxHeartbeats 4000000

open ground places fiberdec

/-! The collar read: the deep labels refuse it, the collar tower
and the vacuum hold it. -/

theorem pin1 : ¬ collarAt [4, 0] := by decide +kernel
theorem pin2 : ¬ collarAt [2, 2, 0] := by decide +kernel
theorem pin3 : collarAt [2, 0, 2, 0] := by decide +kernel
theorem pin4 : collarAt [0, 0, 0] := by decide +kernel

/-! The deep row's read: the unit content at the residue's count,
a root move at one, the sum's unit at an absent tie. -/

theorem pin5 : rowRead 3 [1, 1, 0] [1, 1, 1] = 2 := by decide +kernel
theorem pin6 : rowRead 5 [2, 2, 2, 2, 0] [4, 1, 2, 2, 1] = 1 := by decide +kernel
theorem pin7 : rowRead 3 [1, 1, 0] [0, 0, 0] = 0 := by decide +kernel

/-! The whole rows at the definitional count, `d = 2`: over every
shape at the matched degree the fusion count is the content read
at the tie. -/

theorem pin8 : ((places.allShapes 2 (places.degree [4, 0] + 2)).all
    (fun c => blockcount.fusionCount (adjchar.theta 2) [4, 0] c
      == rowRead 2 [4, 0] c)) = true := by decide +kernel
theorem pin9 : ((places.allShapes 2 (places.degree [6, 0] + 2)).all
    (fun c => blockcount.fusionCount (adjchar.theta 2) [6, 0] c
      == rowRead 2 [6, 0] c)) = true := by decide +kernel

/-! The whole rows at the fast count, `d = 3`. -/

theorem pin10 : ((places.allShapes 3 (places.degree [2, 2, 0] + 3)).all
    (fun c => steinberg.count (adjchar.theta 3) [2, 2, 0] c
      == rowRead 3 [2, 2, 0] c)) = true := by decide +kernel
theorem pin11 : ((places.allShapes 3 (places.degree [3, 3, 0] + 3)).all
    (fun c => steinberg.count (adjchar.theta 3) [3, 3, 0] c
      == rowRead 3 [3, 3, 0] c)) = true := by decide +kernel

/-! The whole rows at the formula-side fold, `d = 4, 5`: the even
side reads the row and the odd side is vacant at every target. -/

theorem pin12 : ((places.allShapes 4 (places.degree [2, 2, 2, 0] + 4)).all
    (fun c =>
      steinberg.sumsWith (adjchar.multRead 4) 4 [2, 2, 2, 0] c
        == (rowRead 4 [2, 2, 2, 0] c, 0))) = true := by decide +kernel
theorem pin13 : ((places.allShapes 4 (places.degree [3, 2, 2, 0] + 4)).all
    (fun c =>
      steinberg.sumsWith (adjchar.multRead 4) 4 [3, 2, 2, 0] c
        == (rowRead 4 [3, 2, 2, 0] c, 0))) = true := by decide +kernel
theorem pin14 : ((places.allShapes 5
      (places.degree [2, 2, 2, 2, 0] + 5)).all
    (fun c =>
      steinberg.sumsWith (adjchar.multRead 5) 5 [2, 2, 2, 2, 0] c
        == (rowRead 5 [2, 2, 2, 2, 0] c, 0))) = true := by decide +kernel

/-! The deep diagonals read the residue. -/

theorem pin15 : blockcount.fusionCount (adjchar.theta 2) [4, 0] [4, 1]
    = 1 := by decide +kernel
theorem pin16 : steinberg.count (adjchar.theta 3) [2, 2, 0] [2, 2, 1]
    = 2 := by decide +kernel
theorem pin17 : steinberg.sumsWith (adjchar.multRead 4) 4
    [2, 2, 2, 0] [2, 2, 2, 1] = (3, 0) := by decide +kernel
theorem pin18 : steinberg.sumsWith (adjchar.multRead 5) 5
    [2, 2, 2, 2, 0] [2, 2, 2, 2, 1] = (4, 0) := by decide +kernel

/-! The theorem route at `d = 2`, every binder discharged, with
the computed twin. -/

theorem pin19 : blockcount.fusionCount (adjchar.theta 2) [4, 0] [4, 1]
    = rowRead 2 [4, 0] [4, 1] :=
  deepRow 2 [4, 0] [4, 1] (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
theorem pin20 : blockcount.fusionCount (adjchar.theta 2) [4, 0] [4, 1]
    = rowRead 2 [4, 0] [4, 1] := by decide +kernel

/-! The collar refusal, `hdeep`'s isolation: at the tower
`(4,2,2)` the graded fold occupies its odd side, the count reads
the walk's diagonal two against the content formula's three. -/

theorem pin21 : steinberg.sumsWith (adjchar.multRead 4) 4
    [2, 0, 2, 0] [2, 0, 2, 1] = (3, 1) := by decide +kernel
theorem pin22 : rowRead 4 [2, 0, 2, 0] [2, 0, 2, 1] = 3 := by decide +kernel
theorem pin23 : ¬ (steinberg.sumsWith (adjchar.multRead 4) 4
      [2, 0, 2, 0] [2, 0, 2, 1]
    = (rowRead 4 [2, 0, 2, 0] [2, 0, 2, 1], 0)) := by decide +kernel

/-! The frame refusal, `hd`'s isolation: at `d = 1` every further
binder holds and the conclusion refuses, the adjoint's shape at
degree two against the count. -/

theorem pin24 : ¬ collarAt [0] := by decide +kernel
theorem pin25 : ¬ (blockcount.fusionCount (adjchar.theta 1) [0] [2]
    = rowRead 1 [0] [2]) := by decide +kernel

/-! The collar refusal at the theorem's own conclusion: the vacuum
sits off the collar vacuously at one row, every co-binder holds,
and the fundamental's row refuses the unit content's read. -/

theorem pin26 : collarAt [0, 0] := by decide +kernel
theorem pin27 : ¬ (blockcount.fusionCount (adjchar.theta 2) [0, 0] [0, 1]
    = rowRead 2 [0, 0] [0, 1]) := by decide +kernel

/-! The frame records, `hld` and `hcd`: the probed wrong-length
forgeries read both sides at the sum's unit, the conclusion
standing. -/

theorem pin28 : blockcount.fusionCount (adjchar.theta 2) [4] [4, 1] = 0
    := by decide +kernel
theorem pin29 : rowRead 2 [4] [4, 1] = 0 := by decide +kernel
theorem pin30 : blockcount.fusionCount (adjchar.theta 2) [4, 0] [4, 1, 0]
    = 0 := by decide +kernel
theorem pin31 : rowRead 2 [4, 0] [4, 1, 0] = 0 := by decide +kernel

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

theorem pin32 : carrier.support (fusion.dataA 3) R9 (loopAt 9 0)
    = [0, 1, 9, 18] := by decide +kernel
theorem pin33 : bandAdj R9 0 1 = true := by decide +kernel
theorem pin34 : bandAdj R9 0 18 = true := by decide +kernel
theorem pin35 : bandAdj R9 0 4 = false := by decide +kernel

/-! The band components: one part at a single square, two at the
four-apart join, and one at the adjacent join and at the
once-interposed join alike — the interposed plaquette's boundary
meets both squares' rungs, the adjacency's own reach. -/

theorem pin36 : (components (fusion.dataA 3) R9 (loopAt 9 0)).length = 1
    := by decide +kernel
theorem pin37 : (components (fusion.dataA 3) R9
    (stableentries.joinConf (fusion.dataA 3) R9
      (loopAt 9 0) (loopAt 9 4))).length = 2 := by decide +kernel
theorem pin38 : (components (fusion.dataA 3) R9
    (stableentries.joinConf (fusion.dataA 3) R9
      (loopAt 9 0) (loopAt 9 1))).length = 1 := by decide +kernel
theorem pin39 : (components (fusion.dataA 3) R9
    (stableentries.joinConf (fusion.dataA 3) R9
      (loopAt 9 0) (loopAt 9 2))).length = 1 := by decide +kernel

/-! The components' contents: the electric diagonal's per-part
read, the loop's four fundamental labels at the cleared Casimir. -/

theorem pin40 : (components (fusion.dataA 3) R9 (loopAt 9 0)).map
    (compContent (fusion.dataA 3) (loopAt 9 0)) = [32] := by decide +kernel
theorem pin41 : (components (fusion.dataA 3) R9
      (stableentries.joinConf (fusion.dataA 3) R9
        (loopAt 9 0) (loopAt 9 4))).map
    (compContent (fusion.dataA 3)
      (stableentries.joinConf (fusion.dataA 3) R9
        (loopAt 9 0) (loopAt 9 4))) = [32, 32] := by decide +kernel

/-! The band neighborhood: the loop's four vertices with its two
neighboring squares', so the once-interposed square meets it at two
vertices and the twice-interposed square sits off it. -/

theorem pin91 : bandVerts (fusion.dataA 3) R9 (loopAt 9 0)
    = [0, 1, 2, 3, 4, 5, 16, 17] := by decide +kernel
theorem pin92 : offBand (fusion.dataA 3) R9 (loopAt 9 0)
    (ground.getAt [] R9.plaqs 1) = false := by decide +kernel
theorem pin93 : offBand (fusion.dataA 3) R9 (loopAt 9 0)
    (ground.getAt [] R9.plaqs 2) = false := by decide +kernel
theorem pin94 : offBand (fusion.dataA 3) R9 (loopAt 9 0)
    (ground.getAt [] R9.plaqs 3) = true := by decide +kernel
theorem pin95 : offBand (fusion.dataA 3) R9 (loopAt 9 0)
    (ground.getAt [] R9.plaqs 4) = true := by decide +kernel

/-! A component's own configuration: the four-apart join's two
components read the two loops. -/

private def FA : fusion.Data Shape := fusion.dataA 3
private def j04 : List Shape :=
  stableentries.joinConf FA R9 (loopAt 9 0) (loopAt 9 4)
private def j02 : List Shape :=
  stableentries.joinConf FA R9 (loopAt 9 0) (loopAt 9 2)
private def cfV : List Shape := (List.range R9.links).map (fun _ => [0, 0, 0])

theorem pin96 : compConf FA R9 j04 (ground.getAt [] (components FA R9 j04) 0)
    = loopAt 9 0 := by decide +kernel
theorem pin97 : compConf FA R9 j04 (ground.getAt [] (components FA R9 j04) 1)
    = loopAt 9 4 := by decide +kernel

/-! The separation read at two chains.  On the nine-square chain
every two loops sit within the band: at the four-apart pair the
square between them meets both band neighborhoods, and the far row
there joins the two components through its loop.  On the
eleven-square chain the five-apart pair is separated beyond the
band, every square meeting at most one band neighborhood, the
plaquette-level read through the theorem, and the far row at a
square meeting one neighborhood joins that component alone. -/

private def R11 : lattice.Region := fiberdec.chainRegion 11
private def k05 : List Shape :=
  stableentries.joinConf FA R11 (loopAt 11 0) (loopAt 11 5)
private def k04 : List Shape :=
  stableentries.joinConf FA R11 (loopAt 11 0) (loopAt 11 4)

theorem pin98 : ¬ sepBeyond FA R9 (loopAt 9 0) (loopAt 9 4) := by decide +kernel
theorem pin99 : ¬ sepBeyond FA R9 (loopAt 9 0) (loopAt 9 2) := by decide +kernel
theorem pin100 : meetsB R9 (bandVerts FA R9 (loopAt 9 0)) (ground.getAt [] R9.plaqs 2) = true
    ∧ meetsB R9 (bandVerts FA R9 (loopAt 9 4)) (ground.getAt [] R9.plaqs 2) = true := by
  decide +kernel
theorem pin101 : (components FA R9 (stableentries.farConf FA R9 j04
    (ground.getAt [] R9.plaqs 2))).length = 1 := by decide +kernel
theorem pin102 : sepBeyond FA R11 (loopAt 11 0) (loopAt 11 5) := by decide +kernel
theorem pin103 : bandVerts FA R11 (loopAt 11 0) = [0, 1, 2, 3, 4, 5, 20, 21]
    ∧ bandVerts FA R11 (loopAt 11 5) = [8, 9, 10, 11, 12, 13, 14, 15] := by
  decide +kernel
theorem pin104 : ¬ (meetsB R11 (bandVerts FA R11 (loopAt 11 0)) (ground.getAt [] R11.plaqs 2) = true
    ∧ meetsB R11 (bandVerts FA R11 (loopAt 11 5)) (ground.getAt [] R11.plaqs 2) = true) :=
  sepBeyond_read FA R11 (loopAt 11 0) (loopAt 11 5) (by decide +kernel) _
    (ground.mem_of_countOf_pos _ _ (by decide +kernel))
theorem pin105 : (components FA R11 (stableentries.farConf FA R11 k05
    (ground.getAt [] R11.plaqs 2))).length = 2 := by decide +kernel
theorem pin106 : (components FA R11 (stableentries.farConf FA R11 k05
    (ground.getAt [] R11.plaqs 8))).length = 3 := by decide +kernel

/-! The two direction reads and the head at a head bound: the loop
at content 32 sits in the head below the bound 33 and in the tower
direction at the bound itself; the once-interposed join is one
component at content 64, in the tower direction below 65 and in the
head at that bound; the four-apart join is two components within
the band, in the head, and the five-apart join on the longer chain
is in the slab direction. -/

theorem pin107 : towerAt FA R9 33 (loopAt 9 0) = false
    ∧ towerAt FA R9 32 (loopAt 9 0) = true := by decide +kernel
theorem pin108 : slabAt FA R11 k05 = true ∧ slabAt FA R11 k04 = false
    ∧ slabAt FA R9 j04 = false ∧ slabAt FA R9 j02 = false := by decide +kernel
theorem pin109 : headAt FA R9 33 (loopAt 9 0) := by decide +kernel
theorem pin110 : ¬ headAt FA R9 32 (loopAt 9 0) := by decide +kernel
theorem pin111 : headAt FA R9 33 j04 := by decide +kernel
theorem pin112 : ¬ headAt FA R9 33 j02 := by decide +kernel
theorem pin113 : headAt FA R9 65 j02 := by decide +kernel
theorem pin114 : ¬ headAt FA R11 33 k05 := by decide +kernel
theorem pin115 : headAt FA R11 33 k04 := by decide +kernel

/-! The head's two clauses through the theorem at the loop, and the
tower's electric floor at the tower class. -/

theorem pin116 : (∀ c, c ∈ components FA R9 (loopAt 9 0)
      → compContent FA (loopAt 9 0) c < 33)
    ∧ slabAt FA R9 (loopAt 9 0) = false :=
  (headAt_read FA R9 33 (loopAt 9 0)).1 (by decide +kernel)
theorem pin117 : 33 ≤ carrier.contentN FA j02 :=
  tower_content FA R9 33 j02 (by decide +kernel) (by decide +kernel)
theorem pin118 : carrier.contentN FA j02 = 64 := by decide +kernel

/-! The graded index at stated indices: five classes on the
nine-square chain, the vacant class, the two loops and the
four-apart join at the head with the once-interposed join in the
tail; three on the eleven-square chain, the loop and the four-apart
join at the head with the five-apart join in the tail. -/

private def ixG : List (List Shape) :=
  [cfV, loopAt 9 0, loopAt 9 4, j04, j02]
private def ixK : List (List Shape) := [loopAt 11 0, k04, k05]

theorem pin119 : (gradedIdx FA R9 33 ixG).1 = [cfV, loopAt 9 0, loopAt 9 4, j04]
    ∧ (gradedIdx FA R9 33 ixG).2 = [j02] := by decide +kernel
theorem pin120 : (gradedIdx FA R11 33 ixK).1 = [loopAt 11 0, k04]
    ∧ (gradedIdx FA R11 33 ixK).2 = [k05] := by decide +kernel
theorem pin121 : headAt FA R9 33 j04 :=
  gradedIdx_head FA R9 33 ixG j04
    (ground.mem_of_countOf_pos _ _ (by decide +kernel))
theorem pin122 : ¬ headAt FA R11 33 k05 :=
  gradedIdx_tail FA R11 33 ixK k05
    (ground.mem_of_countOf_pos _ _ (by decide +kernel))
theorem pin123 : ground.countOf j02
      ((gradedIdx FA R9 33 ixG).1 ++ (gradedIdx FA R9 33 ixG).2)
    = ground.countOf j02 ixG :=
  gradedIdx_countOf FA R9 33 ixG j02
theorem pin124 : ground.countOf j02
    ((gradedIdx FA R9 33 ixG).1 ++ (gradedIdx FA R9 33 ixG).2) = 1 := by
  decide +kernel

/-! The partition: the components' concatenation reads the support
member for member, the content is the components' contents' sum,
and each closure is stationary, through the theorems and decided;
the width binder refused at a key adjoined beyond the region's
range, whose content enters the fold while the components read the
key range alone. -/

theorem pin125 : ground.countOf 13 ((components FA R9 j04).flatMap (fun c => c))
    = ground.countOf 13 (carrier.support FA R9 j04) :=
  components_countOf FA R9 j04 13
theorem pin126 : ((carrier.support FA R9 j04).all (fun x =>
      ground.countOf x ((components FA R9 j04).flatMap (fun c => c))
        == ground.countOf x (carrier.support FA R9 j04))) = true
    ∧ ((components FA R9 j04).flatMap (fun c => c)).length
      = (carrier.support FA R9 j04).length := by decide +kernel
theorem pin127 : carrier.contentN FA j04
    = ground.famFold Nat.add 0 (compContent FA j04) (components FA R9 j04) :=
  contentN_components FA R9 j04 (by decide +kernel)
theorem pin128 : carrier.contentN FA j04 = 64
    ∧ ground.famFold Nat.add 0 (compContent FA j04) (components FA R9 j04)
      = 64 := by decide +kernel
theorem pin129 : stepAdd R9 (carrier.support FA R9 j04)
    (closure R9 (carrier.support FA R9 j04) 0) = [] :=
  closure_stationary R9 (carrier.support FA R9 j04) 0
    (ground.mem_of_countOf_pos _ _ (by decide +kernel)) (by decide +kernel)
    (by decide +kernel)
theorem pin130 : stepAdd R9 (carrier.support FA R9 j04)
    (closure R9 (carrier.support FA R9 j04) 0) = [] := by decide +kernel

private def wideA : List Shape := loopAt 9 0 ++ [[1, 0, 0]]

theorem pin131 : ¬ (wideA.length = R9.links) := by decide +kernel
theorem pin132 : ¬ (carrier.contentN FA wideA
    = ground.famFold Nat.add 0 (compContent FA wideA)
      (components FA R9 wideA)) := by decide +kernel

/-! The border row at the plaquette four squares along, off the
band neighborhood: the far target's components are the loop's with
one further component, the plaquette's links in the region's key
order, through the theorem and decided, its count one further; the
plaquette three along is off the neighborhood as well.  The
neighborhood binder's isolating refusal is the once-interposed
plaquette, whose far target keeps the one component, the loop
joining it; the region binder's is a forged two-rung word off the
region's plaquettes, its two rungs off each other's adjacency and
off the loop's band neighborhood, the far target reading each rung
as its own component. -/

theorem pin133 : lattice.plaqRead R9 := by decide +kernel
theorem pin134 : (components FA R9 (stableentries.farConf FA R9 (loopAt 9 0)
        (ground.getAt [] R9.plaqs 4))).filter (fun c =>
        c.any (fun x => !(FA.eqL (ground.getAt FA.unit (loopAt 9 0) x) FA.unit)))
      = components FA R9 (loopAt 9 0)
    ∧ (components FA R9 (stableentries.farConf FA R9 (loopAt 9 0)
        (ground.getAt [] R9.plaqs 4))).filter (fun c =>
        !(c.any (fun x => !(FA.eqL (ground.getAt FA.unit (loopAt 9 0) x) FA.unit))))
      = [(List.range R9.links).filter (fun l =>
          (ground.getAt [] R9.plaqs 4).any (fun e => e.1 == l))] :=
  components_border FA R9 (by decide +kernel) (by decide +kernel) (loopAt 9 0)
    (ground.getAt [] R9.plaqs 4) (ground.mem_of_countOf_pos _ _ (by decide +kernel))
    (by decide +kernel) (by decide +kernel)
theorem pin135 : components FA R9 (stableentries.farConf FA R9 (loopAt 9 0)
      (ground.getAt [] R9.plaqs 4))
    = [[0, 1, 9, 18], [4, 5, 13, 22]] := by decide +kernel
theorem pin136 : (components FA R9 (stableentries.farConf FA R9 (loopAt 9 0)
      (ground.getAt [] R9.plaqs 4))).length
    = (components FA R9 (loopAt 9 0)).length + 1 :=
  components_border_length FA R9 (by decide +kernel) (by decide +kernel)
    (loopAt 9 0) (ground.getAt [] R9.plaqs 4)
    (ground.mem_of_countOf_pos _ _ (by decide +kernel))
    (by decide +kernel) (by decide +kernel)
theorem pin137 : algebra.plaqRow FA R9 (ground.getAt [] R9.plaqs 4) (loopAt 9 0)
    = [stableentries.farConf FA R9 (loopAt 9 0) (ground.getAt [] R9.plaqs 4)] :=
  by decide +kernel
theorem pin138 : (components FA R9 (stableentries.farConf FA R9 (loopAt 9 0)
    (ground.getAt [] R9.plaqs 3))).length = 2 := by decide +kernel

theorem pin139 : components FA R9 (stableentries.farConf FA R9 (loopAt 9 0)
      (ground.getAt [] R9.plaqs 2))
    = [[0, 1, 2, 3, 9, 11, 18, 20]] := by decide +kernel
theorem pin140 : ¬ ((components FA R9 (stableentries.farConf FA R9 (loopAt 9 0)
        (ground.getAt [] R9.plaqs 2))).filter (fun c =>
        !(c.any (fun x => !(FA.eqL (ground.getAt FA.unit (loopAt 9 0) x) FA.unit))))
      = [(List.range R9.links).filter (fun l =>
          (ground.getAt [] R9.plaqs 2).any (fun e => e.1 == l))]) := by
  decide +kernel

private def forgedP : List (Nat × Bool) := [(5, true), (7, true)]

theorem pin141 : ground.countOf forgedP R9.plaqs = 0 := by decide +kernel
theorem pin142 : offBand FA R9 (loopAt 9 0) forgedP = true := by decide +kernel
theorem pin143 : components FA R9 (stableentries.farConf FA R9 (loopAt 9 0) forgedP)
    = [[0, 1, 9, 18], [5], [7]] := by decide +kernel
theorem pin144 : ¬ ((components FA R9 (stableentries.farConf FA R9 (loopAt 9 0)
        forgedP)).filter (fun c =>
        !(c.any (fun x => !(FA.eqL (ground.getAt FA.unit (loopAt 9 0) x) FA.unit))))
      = [(List.range R9.links).filter (fun l => forgedP.any (fun e => e.1 == l))]) := by
  decide +kernel

/-! The stencil row's reach at the neighboring plaquette: every
occupied link of a row target is the loop's own or a boundary
link, through the theorem and decided. -/

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

theorem pin44 : ground.getAt (fusion.dataA 3).unit rowTarget 0
    = ground.getAt (fusion.dataA 3).unit (loopAt 9 0) 0 :=
  algebra.plaqRow_keep (fusion.dataA 3) R9
    (ground.getAt [] R9.plaqs 1) (loopAt 9 0) rowTarget
    (by decide +kernel) 0 (by decide +kernel) (by decide +kernel)
theorem pin45 : ground.getAt (fusion.dataA 3).unit rowTarget 0
    = ground.getAt (fusion.dataA 3).unit (loopAt 9 0) 0 := by decide +kernel
theorem pin145 : ∀ l, l ∈ carrier.support FA R9 rowTarget →
    l ∈ carrier.support FA R9 (loopAt 9 0)
      ∨ ((ground.getAt [] R9.plaqs 1).any (fun e => e.1 == l)) = true :=
  support_target FA R9 (ground.getAt [] R9.plaqs 1) (loopAt 9 0) rowTarget
    (by decide +kernel)
theorem pin146 : ((carrier.support FA R9 rowTarget).all (fun l =>
    ground.containsB (carrier.support FA R9 (loopAt 9 0)) l
      || (ground.getAt [] R9.plaqs 1).any (fun e => e.1 == l))) = true := by
  decide +kernel

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

theorem pin46 : assembly.wTopAt wDeep kapD := by decide +kernel
theorem pin47 : offTopAt tB sertables.fundB2 wDeep 2 kapD := by decide +kernel
theorem pin48 : magAt tB sertables.fundB2 thFamB2 2 := by decide +kernel
theorem pin49 : sertables.fundShape tB sertables.fundB2 := by decide +kernel
theorem pin50 : sertables.gramSymRead sertables.fundB2 := by decide +kernel
theorem pin51 : row.rhoLenRead tB sertables.fundB2 := by decide +kernel
theorem pin52 : sertables.wShapeRead tB wDeep := by decide +kernel
theorem pin53 : memberchar.mShapeRead tB thFamB2 := by decide +kernel

/-! The theorem route at the tower key: the even fold reads the
content list's count at the vacant withdrawal — the rank's two —
and the odd fold reads the sum's zero. -/

theorem pin54 : memberchar.convCount wDeep thFamB2
      (poly.pnorm (elim.vecAdd lamD (sertables.rhoV tB))) false
    = ground.countOf
        (poly.pnorm (elim.vecAdd lamD (poly.neg lamD))) thFamB2
  ∧ memberchar.convCount wDeep thFamB2
      (poly.pnorm (elim.vecAdd lamD (sertables.rhoV tB))) true = 0 :=
  memberRows tB sertables.fundB2 wDeep thFamB2 lamD lamD 2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
theorem pin55 : memberchar.convCount wDeep thFamB2
    (poly.pnorm (elim.vecAdd lamD (sertables.rhoV tB))) false = 2 :=
  by decide +kernel
theorem pin56 : memberchar.convCount wDeep thFamB2
    (poly.pnorm (elim.vecAdd lamD (sertables.rhoV tB))) true = 0 :=
  by decide +kernel
theorem pin57 : ground.countOf
    (poly.pnorm (elim.vecAdd lamD (poly.neg lamD))) thFamB2 = 2 :=
  by decide +kernel

/-! The route at the reflected key, the row's one at the moved
content, and at a key off the support, the row's vacancy. -/

theorem pin58 : memberchar.convCount wDeep thFamB2
      (poly.pnorm (elim.vecAdd cR (sertables.rhoV tB))) false
    = ground.countOf
        (poly.pnorm (elim.vecAdd cR (poly.neg lamD))) thFamB2
  ∧ memberchar.convCount wDeep thFamB2
      (poly.pnorm (elim.vecAdd cR (sertables.rhoV tB))) true = 0 :=
  memberRows tB sertables.fundB2 wDeep thFamB2 lamD cR 2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
theorem pin59 : memberchar.convCount wDeep thFamB2
    (poly.pnorm (elim.vecAdd cR (sertables.rhoV tB))) false = 1 :=
  by decide +kernel
theorem pin60 : ground.countOf
    (poly.pnorm (elim.vecAdd cR (poly.neg lamD))) thFamB2 = 1 :=
  by decide +kernel

theorem pin61 : memberchar.convCount wDeep thFamB2
      (poly.pnorm (elim.vecAdd cO (sertables.rhoV tB))) false
    = ground.countOf
        (poly.pnorm (elim.vecAdd cO (poly.neg lamD))) thFamB2
  ∧ memberchar.convCount wDeep thFamB2
      (poly.pnorm (elim.vecAdd cO (sertables.rhoV tB))) true = 0 :=
  memberRows tB sertables.fundB2 wDeep thFamB2 lamD cO 2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
theorem pin62 : memberchar.convCount wDeep thFamB2
    (poly.pnorm (elim.vecAdd cO (sertables.rhoV tB))) false = 0 :=
  by decide +kernel
theorem pin63 : ground.countOf
    (poly.pnorm (elim.vecAdd cO (poly.neg lamD))) thFamB2 = 0 :=
  by decide +kernel

/-! The member row read back at the exhaustion: the tower key sits
in the stated list twice, the content list's own count. -/

private def cVsD : List (List BPair) := [lamD, lamD]

theorem pin64 : steinberg.memberAt tB wDeep thFamB2 cVsD lamD := by decide +kernel
theorem pin65 : ground.countOf lamD cVsD
    = ground.countOf
        (poly.pnorm (elim.vecAdd lamD (poly.neg lamD))) thFamB2 :=
  memberRow tB sertables.fundB2 wDeep thFamB2 lamD lamD 2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) cVsD (by decide +kernel)
theorem pin66 : ground.countOf lamD cVsD = 2 := by decide +kernel

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

theorem pin67 : assembly.wTopAt wKap1B2
    (poly.pnorm (elim.vecAdd (row.thetaV tB) (sertables.rhoV tB))) :=
  by decide +kernel
theorem pin68 : ¬ offTopAt tB sertables.fundB2 wKap1B2 2
    (poly.pnorm (elim.vecAdd (row.thetaV tB) (sertables.rhoV tB))) :=
  by decide +kernel

theorem pin69 : ¬ magAt tB sertables.fundB2
    (thFamB2 ++ [[BPair.ofNat 3, BPair.unit]]) 2 := by decide +kernel

theorem pin70 : ¬ assembly.wTopAt wDup kapD := by decide +kernel
theorem pin71 : offTopAt tB sertables.fundB2 wDup 2 kapD := by decide +kernel
theorem pin72 : sertables.wShapeRead tB wDup := by decide +kernel
theorem pin73 : ¬ (memberchar.convCount wDup thFamB2
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

theorem pin74 : ¬ (∀ j, j < tB.posFolds.length →
    BPair.unit ≤ sertables.dotB sertables.fundB2 cND
      (sertables.posCorootV tB j)) := by decide +kernel
theorem pin75 : ¬ (memberchar.convCount wDeep thFamB2
      (poly.pnorm (elim.vecAdd cND (sertables.rhoV tB))) false
    = ground.countOf
        (poly.pnorm (elim.vecAdd cND (poly.neg lamD))) thFamB2) :=
  by decide +kernel
theorem pin76 : ¬ (∀ j, j < tB.posFolds.length →
    BPair.unit ≤ sertables.dotB sertables.fundB2 cOdd
      (sertables.posCorootV tB j)) := by decide +kernel
theorem pin77 : ¬ (memberchar.convCount wDeep thFamB2
      (poly.pnorm (elim.vecAdd cOdd (sertables.rhoV tB))) true
    = 0) := by decide +kernel

/-! The frame records' reads: the over-long forgeries' folds stand
at the fixture's own values, the length bookkeeping absorbing the
surplus keys. -/

private def lamF : List BPair :=
  [BPair.ofNat 2, BPair.ofNat 2, BPair.ofNat 2]

theorem pin78 : ground.countOf
    (poly.pnorm (elim.vecAdd lamD (poly.neg lamF))) thFamB2 = 2 :=
  by decide +kernel
theorem pin79 : memberchar.convCount wDeep thFamB2
    (poly.pnorm (elim.vecAdd lamF (sertables.rhoV tB))) false
    = 2 := by decide +kernel

/-! The two separation reads part at the once-interposed pair: the
supports share no vertex while the reach neighborhoods overlap,
the vertex-level read holding where the band-level refuses. -/

theorem pin80 : stableentries.disjSupp (fusion.dataA 3) R9
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

theorem pin81 : offTopAt tG sertables.fundG2 wG 3 kapG := by decide +kernel
theorem pin82 : magAt tG sertables.fundG2 thFamG2 3 := by decide +kernel

theorem pin83 : memberchar.convCount wG thFamG2
      (poly.pnorm (elim.vecAdd lamG (sertables.rhoV tG))) false
    = ground.countOf
        (poly.pnorm (elim.vecAdd lamG (poly.neg lamG))) thFamG2 :=
  (memberRows tG sertables.fundG2 wG thFamG2 lamG lamG 3
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)).1
theorem pin84 : memberchar.convCount wG thFamG2
      (poly.pnorm (elim.vecAdd lamG (sertables.rhoV tG))) false = 2
    ∧ memberchar.convCount wG thFamG2
      (poly.pnorm (elim.vecAdd lamG (sertables.rhoV tG))) true = 0
    ∧ ground.countOf
      (poly.pnorm (elim.vecAdd lamG (poly.neg lamG))) thFamG2 = 2 :=
  by decide +kernel
theorem pin85 : memberchar.convCount wG thFamG2
      (poly.pnorm (elim.vecAdd cRG (sertables.rhoV tG))) false
    = ground.countOf
        (poly.pnorm (elim.vecAdd cRG (poly.neg lamG))) thFamG2 :=
  (memberRows tG sertables.fundG2 wG thFamG2 lamG cRG 3
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)).1
theorem pin86 : memberchar.convCount wG thFamG2
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

theorem pin87 : assembly.wTopAt w2G kap2G := by decide +kernel
theorem pin88 : offTopAt tG sertables.fundG2 w2G 2 kap2G := by decide +kernel
theorem pin89 : ¬ offTopAt tG sertables.fundG2 w2G 3 kap2G := by decide +kernel
theorem pin90 : ¬ magAt tG sertables.fundG2 thFamG2 2 := by decide +kernel

end grading
