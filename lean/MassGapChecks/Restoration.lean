import MassGap.Restoration
import MassGap.SO
/-!
The check module for `thm:restoration`'s first tier: the batteries
re-read the signed coordinate permutations' action at the
two-direction torus of side three by kernel `decide`.  Two members
are committed — the direction swap, whose flip family is vacant,
and the reflection in direction zero, whose direction permutation
is the identity — and each is read a permutation of the eighteen
link keys at itself, both being involutions, with a member off
that pair (the swap composed with the reflection, of order four)
refusing the read at its own witness.

The conjugation is the theorem's own sentence, that a lattice
symmetry maps each direction's translation to the permuted
direction's own (`fiberdec.intertwineRead`): the swap carries
direction zero's translation to direction one's and back, and the
reflection carries direction zero's to its inverse — the backward
step at the reversed traversal — while fixing the unflipped
direction's.  The refusal sits at the wrong target, the swap's
conjugate of direction zero's translation read against direction
zero's own.

The index action rides at a committed family of the window's
elementary loops, each label the fundamental or its dual: the nine
unit squares at their two orientation classes, content
`4 · 8 = 32`, and the six windings at theirs, three links each at
content `3 · 8 = 24` — the side-three window pricing a winding
below the plaquette level, the fibering's own family entering at
side five.  Over that family the three dualizing reads hold at
both members: the content fixed, the occupancy fixed and the index
closed.  The reversal family is isolated by the occupancy and the
closure together — a member's link map paired with a second
member's reversal family dualizes the labels off the reversed
traversals, so a vertex reads its incident product off the
invariant and the moved configuration leaves the family — while
the content read stays true there, the electric fold being blind
to the dualization at the interface's own Casimir read
(`fusion.casDualLaw`).

The matrix tier runs on that same family: each member's relabeling
is read as a matrix of order thirty-one, the unit line at its head
over the thirty members' indicator rows, and is orthogonal at both
members — the closure and the injectivity of the relabeling read
at the congruence.  The window's electric matrix is the diagonal
of the family's contents with the unit line at its head, eighteen
squares at the plaquette level and twelve windings at the side's
own count, and each member's congruence fixes it: `thm:restoration`'s
`E` sentence read entrywise, the dualization blind at the
interface's Casimir read.  With that pair the window carries
`thm:SO`'s character clause outright — the member commutes with
the electric matrix, is orthogonal, and reads the unit line's
ground at a scalar squaring to one.

The transform tier runs at two directions, side three and one
argument: the direction row's nine keys and the box at one
argument its own, the moved key read at both members, and the
family the two-argument read `ω(Ā T^{ks} A)`'s one-key slice at
the relative key, the first argument at the origin, read at the
free end's unit-line state — occupied exactly where the composite
shift fixes the probe.  The probes are the committed windings of the index
family — the direction-zero loop at transverse coordinate zero,
carried by the swap to the direction-one loop based at digit zero,
which the flip fixes — and the coefficient identity holds at that
pair while the diagonal at the swap is refused for the
direction-zero family, the member moving the probe so the forged
read parts from the moved family's own.

The determinant tier runs at three scales.  A committed
three-by-three square with distinct entries is relabeled at a
committed three-cycle, its literal relabeling decided against the
entrywise reading, and the two determinants read one value at
`relabel_det` with the value pinned at the balance partner of five;
a relabeling with one entry off refuses the read, and an
assignment holding a letter twice refuses the enumeration's own
count.  At the window the swap's relabeling of the thirty-one
window keys is read off the index action — the unit line fixed and
each loop's key at the moved loop's own, the two orientation
classes exchanged and the two directions' windings with them — and
the electric matrix is fixed at it entrywise, so its determinant
reads one value with itself, the theorem's `E`-fix read at
`def:elim`'s determinant.  The polynomial carrier's instance is a
committed two-by-two square at the transposition, the relabeled
square's minor reading the source's, a square one coefficient off
refusing the entrywise reading (`lem:split`'s symbol).
-/
set_option maxHeartbeats 16000000

open ground lattice fusion carrier fiberdec restoration elim inertia

/-! The committed members: the direction swap at the vacant flip
family, and the reflection in direction zero at the identity
permutation. -/

private def pSwap : Nat → Nat := fun e => 1 - e
private def fNone : Nat → Bool := fun _ => false
private def fZero : Nat → Bool := fun e => e == 0

/-! The interface the index reads run at: the label calculus at
three letters, where the fundamental and its dual are distinct. -/

private def FA : Data places.Shape := dataA 3

/-! Each member permutes the link keys at itself, and a member of
order four refuses that reading at its own witness. -/

example : permRead (torusRegion 2 3) (bdLink 2 3 pSwap fNone)
    (bdLink 2 3 pSwap fNone) := by decide +kernel
example : permRead (torusRegion 2 3) (bdLink 2 3 (fun e => e) fZero)
    (bdLink 2 3 (fun e => e) fZero) := by decide +kernel
example : ¬ permRead (torusRegion 2 3) (bdLink 2 3 pSwap fZero)
    (bdLink 2 3 pSwap fZero) := by decide +kernel

/-! The conjugation reads: each direction's translation carried to
the permuted direction's own, a flipped direction's to the
backward step. -/

example : intertwineRead (torusRegion 2 3) (bdLink 2 3 pSwap fNone)
    (torusTransl 2 3 0) (torusTransl 2 3 1) := by decide +kernel
example : intertwineRead (torusRegion 2 3) (bdLink 2 3 pSwap fNone)
    (torusTransl 2 3 1) (torusTransl 2 3 0) := by decide +kernel
example : intertwineRead (torusRegion 2 3)
    (bdLink 2 3 (fun e => e) fZero)
    (torusTransl 2 3 0) (torusTranslInv 2 3 0) := by decide +kernel
example : intertwineRead (torusRegion 2 3)
    (bdLink 2 3 (fun e => e) fZero)
    (torusTransl 2 3 1) (torusTransl 2 3 1) := by decide +kernel
example : ¬ intertwineRead (torusRegion 2 3) (bdLink 2 3 pSwap fNone)
    (torusTransl 2 3 0) (torusTransl 2 3 0) := by decide +kernel

/-! The committed family of elementary loops: one builder at the
squares, the boundary's forward entries at a stated label and the
reversed at a second, and one at the windings, a direction's links
at a fixed transverse coordinate. -/

private def torLoop (i : Nat) (fwd bwd : places.Shape) :
    List places.Shape :=
  let p := ground.getAt [] (torusRegion 2 3).plaqs i
  (List.range (torusRegion 2 3).links).map (fun l =>
    if p.any (fun e => e.1 == l && e.2) then fwd
    else if p.any (fun e => e.1 == l && !e.2) then bwd
    else [0, 0, 0])

private def torWind (e c : Nat) (lab : places.Shape) :
    List places.Shape :=
  (List.range (torusRegion 2 3).links).map (fun l =>
    if l / 9 == e && digitAt 3 (1 - e) (l % 9) == c then lab
    else [0, 0, 0])

private def twIx : List (List places.Shape) :=
  (List.range 9).map (fun i => torLoop i [1, 0, 0] [0, 1, 0])
    ++ (List.range 9).map (fun i => torLoop i [0, 1, 0] [1, 0, 0])
    ++ (List.range 2).flatMap (fun e => (List.range 3).flatMap (fun c =>
        [torWind e c [1, 0, 0], torWind e c [0, 1, 0]]))

/-! The family's own reads: thirty members, each occupied, the
squares at the plaquette level and the windings at the side's own
count. -/

example : twIx.length = 30 := by decide +kernel
example : (twIx.all (fun a => occupied FA (torusRegion 2 3) a)) = true := by
  decide +kernel
example : (twIx.map (fun a => contentN FA a)).all (fun c => c == 32 || c == 24)
    = true := by decide +kernel
example : contentN FA (ground.getAt [] twIx 0) = 32 := by decide +kernel
example : contentN FA (ground.getAt [] twIx 18) = 24 := by decide +kernel

/-! The three dualizing index reads at both members. -/

example : fiberdec.dualContentFixed FA (torusRegion 2 3) twIx
    (bdLink 2 3 pSwap fNone) (bdRev 2 3 fNone) := by
  decide +kernel
example : dualOccFixed FA (torusRegion 2 3) twIx
    (bdLink 2 3 pSwap fNone) (bdRev 2 3 fNone) := by
  decide +kernel
example : dualIdxFixed FA (torusRegion 2 3) twIx
    (bdLink 2 3 pSwap fNone) (bdRev 2 3 fNone) := by
  decide +kernel
example : fiberdec.dualContentFixed FA (torusRegion 2 3) twIx
    (bdLink 2 3 (fun e => e) fZero) (bdRev 2 3 fZero) := by
  decide +kernel
example : dualOccFixed FA (torusRegion 2 3) twIx
    (bdLink 2 3 (fun e => e) fZero) (bdRev 2 3 fZero) := by
  decide +kernel
example : dualIdxFixed FA (torusRegion 2 3) twIx
    (bdLink 2 3 (fun e => e) fZero) (bdRev 2 3 fZero) := by
  decide +kernel

/-! The reversal family isolated: a member's link map at the other
member's reversal family fails the occupancy and the closure, and
the content read stays true at both forgeries — the Casimir's own
blindness to the dualization — while a collapsing link map, every
link at the origin's own, refuses the content read itself. -/

example : ¬ dualOccFixed FA (torusRegion 2 3) twIx
    (bdLink 2 3 pSwap fNone) (bdRev 2 3 fZero) := by
  decide +kernel
example : ¬ dualIdxFixed FA (torusRegion 2 3) twIx
    (bdLink 2 3 pSwap fNone) (bdRev 2 3 fZero) := by
  decide +kernel
example : ¬ dualOccFixed FA (torusRegion 2 3) twIx
    (bdLink 2 3 (fun e => e) fZero) (bdRev 2 3 fNone) := by
  decide +kernel
example : ¬ dualIdxFixed FA (torusRegion 2 3) twIx
    (bdLink 2 3 (fun e => e) fZero) (bdRev 2 3 fNone) := by
  decide +kernel
example : fiberdec.dualContentFixed FA (torusRegion 2 3) twIx
    (bdLink 2 3 pSwap fNone) (bdRev 2 3 fZero) := by
  decide +kernel
example : fiberdec.dualContentFixed FA (torusRegion 2 3) twIx
    (bdLink 2 3 (fun e => e) fZero) (bdRev 2 3 fNone) := by
  decide +kernel
example : ¬ fiberdec.dualContentFixed FA (torusRegion 2 3) twIx
    (fun _ => 0) (bdRev 2 3 fNone) := by decide +kernel

/-! The plaquette set at the cyclic reading (`con:lattice`'s
boundary field): each member's image word a stored plaquette's own
cyclic word — the swap's images the stored words' reversals, the
flip's the moved squares' reversed rotations with the traversal
bits carried across the reversal family — a translation's literal
membership the reading's own instance, and the refusal isolating
the reversal family: the flip's map with the bits kept fails the
cyclic membership outright. -/

example : bdPlaqRead (fiberdec.torusRegion 2 3)
    (bdLink 2 3 pSwap fNone) (bdRev 2 3 fNone) := by decide +kernel
example : bdPlaqRead (fiberdec.torusRegion 2 3)
    (bdLink 2 3 (fun e => e) fZero) (bdRev 2 3 fZero) := by
  decide +kernel
example : bdPlaqRead (fiberdec.torusRegion 2 3)
    (fiberdec.torusTransl 2 3 0) (bdRev 2 3 fNone) := by
  decide +kernel
example : ¬ bdPlaqRead (fiberdec.torusRegion 2 3)
    (bdLink 2 3 (fun e => e) fZero) (bdRev 2 3 fNone) := by
  decide +kernel

/-! The index matrix at the committed family: the signed member's
relabeling read as a matrix on the thirty members with the unit
line at its head, the dualizing action's own indicator rows.  Each
member's matrix is orthogonal — the closure and the injectivity of
the relabeling read at the congruence. -/

private def bdSwapM : Mat :=
  dualMat FA twIx 18 (bdLink 2 3 pSwap fNone) (bdRev 2 3 fNone)

private def bdFlipM : Mat :=
  dualMat FA twIx 18 (bdLink 2 3 (fun e => e) fZero) (bdRev 2 3 fZero)

example : matOneValue (matMul (transposeM bdSwapM) bdSwapM) (idMat 31) := by
  decide +kernel
example : matOneValue (matMul (transposeM bdFlipM) bdFlipM) (idMat 31) := by
  decide +kernel

/-! The electric member fixed at the congruence, `thm:restoration`'s
`E` sentence read at the matrix level: the window diagonal is the
family's contents with the unit line at its head — the eighteen
squares at the plaquette level and the twelve windings at the
side's own count — and the congruence by each member's matrix
fixes it, the dualization blind at the interface's Casimir read.
The orthogonality read refuses the electric matrix itself, and the
commuting read refuses a forged diagonal holding every member's
entry apart, the swap moving a distinguished entry off itself. -/

private def bdDiag : List Nat := 0 :: twIx.map (contentN FA)

example : bdDiag = 0 :: (List.replicate 18 32 ++ List.replicate 12 24) := by
  decide +kernel

private def bdE : Mat := pairpencil.pencilE bdDiag

example : commRead bdSwapM bdE := by decide +kernel
example : commRead bdFlipM bdE := by decide +kernel
example : ¬ matOneValue (matMul (transposeM bdE) bdE) (idMat 31) := by
  decide +kernel

private def bdBadE : Mat :=
  pairpencil.pencilE (0 :: (List.range 30).map (fun i => i + 1))

example : ¬ commRead bdSwapM bdBadE := by decide +kernel

/-! The ground line at the same window (`thm:SO`'s character
clause): the electric matrix and the member's own, the member
commuting with it and orthogonal, read the unit line's ground at a
scalar squaring to one — the state's read blind to the grading —
with a state occupied at a moved member refused, the swap carrying
the occupied line off itself. -/

private def bdPsi : List BPair :=
  BPair.ofPos 1 :: twIx.map (fun _ => BPair.unit)

example : SO.symRead (⟨bdE, by decide +kernel⟩ : SqMat 31)
    (⟨bdSwapM, by decide +kernel⟩ : SqMat 31)
    (⟨bdPsi, by decide +kernel⟩ : Vec 31) := by decide +kernel
example : SO.symRead (⟨bdE, by decide +kernel⟩ : SqMat 31)
    (⟨bdFlipM, by decide +kernel⟩ : SqMat 31)
    (⟨bdPsi, by decide +kernel⟩ : Vec 31) := by decide +kernel

private def bdPsiBad : List BPair :=
  BPair.unit :: BPair.ofPos 1 :: List.replicate 29 BPair.unit

example : ¬ SO.symRead (⟨bdE, by decide +kernel⟩ : SqMat 31)
    (⟨bdSwapM, by decide +kernel⟩ : SqMat 31)
    (⟨bdPsiBad, by decide +kernel⟩ : Vec 31) := by decide +kernel

/-! The momentum transform's carrier at two directions, side three
and one argument: the direction row's nine keys, the box at one
argument its own, and the moved key at the two members — the swap
reading the exponents at the permuted directions, the flip reading
a key to its balance partner at the wrap. -/

example : (places.keyBox 2 3).length = 9 := by decide +kernel
example : (argBox 2 3 1).length = 9 := by decide +kernel
example : bdKey 2 3 (fun e => 1 - e) (fun _ => false) [1, 2] = [2, 1] := by
  decide +kernel
example : bdKey 2 3 (fun e => e) (fun e => e == 0) [1, 2] = [2, 2] := by
  decide +kernel

/-! The transform at a committed probe: the shift at a key list
composes the two directions' translations at the list's two
exponents, and the family is the two-argument read
`ω(Ā T^{ks} A)`'s one-key slice at the relative key, the first
argument at the origin, read at the free end's unit-line state —
occupied exactly where the shift fixes the probe.  The two probes are the committed windings
of the index family — the direction-zero loop at transverse
coordinate zero and the direction-one loop based at digit zero —
the first carried to the second by the swap, the second fixed by
the flip. -/

private def torShift (ks : List (List Nat)) : Nat → Nat :=
  compShift 2 3 (ground.getAt [] ks 0)

private def windD0 : List places.Shape := torWind 0 0 [1, 0, 0]
private def windD1 : List places.Shape := torWind 1 0 [1, 0, 0]

example : eqConf FA windD0 (ground.getAt [] twIx 18) = true := by
  decide +kernel
example : eqConf FA windD1 (ground.getAt [] twIx 24) = true := by
  decide +kernel
example : eqConf FA (dualConf FA (bdLink 2 3 pSwap fNone)
    (bdRev 2 3 fNone) 18 windD0) windD1 = true := by decide +kernel
example : eqConf FA (dualConf FA (bdLink 2 3 (fun e => e) fZero)
    (bdRev 2 3 fZero) 18 windD1) windD1 = true := by decide +kernel
example : eqConf FA (dualConf FA (bdLink 2 3 (fun e => e) fZero)
    (bdRev 2 3 fZero) 18 windD0) windD0 = false := by decide +kernel

private def wD0 (ks : List (List Nat)) : BPair :=
  if eqConf FA (permConf FA (torShift ks) 18 windD0) windD0 then
    BPair.ofPos 1
  else BPair.unit

private def wD1 (ks : List (List Nat)) : BPair :=
  if eqConf FA (permConf FA (torShift ks) 18 windD1) windD1 then
    BPair.ofPos 1
  else BPair.unit

/-! The moved read at the swap: the direction-one family at the
moved keys reads the direction-zero family at the keys, the
transform's coefficient identity at this pair; the flip fixes the
direction-one family outright; and the diagonal at the swap is
refused for the direction-zero family, the member moving the probe
so the forged read parts from the moved family's own. -/

example : transformMoved 2 3 1 wD0 wD1 pSwap fNone := by decide +kernel
example : transformFixed 2 3 1 wD1 (fun e => e) fZero := by decide +kernel
example : ¬ transformFixed 2 3 1 wD0 pSwap fNone := by decide +kernel

/-! The determinant at a joint relabeling of rows and columns
(`thm:restoration`'s derivation clause): a committed three-by-three
square with distinct entries against its literal relabeling at a
committed assignment, the relabeling read decided and the
determinant routed at one value; a forged relabeling with one entry
off refuses the read, and an assignment holding a letter twice
refuses the enumeration's own count. -/

private def q3 : List Nat := [1, 2, 0]

private def m3 : Mat :=
  [[BPair.ofNat 1, BPair.ofNat 2, BPair.ofNat 3],
   [BPair.ofNat 4, BPair.ofNat 5, BPair.ofNat 7],
   [BPair.ofNat 8, BPair.ofNat 6, BPair.ofNat 9]]

private def m3' : Mat :=
  [[BPair.ofNat 5, BPair.ofNat 7, BPair.ofNat 4],
   [BPair.ofNat 6, BPair.ofNat 9, BPair.ofNat 8],
   [BPair.ofNat 2, BPair.ofNat 3, BPair.ofNat 1]]

private def m3bad : Mat :=
  [[BPair.ofNat 5, BPair.ofNat 7, BPair.ofNat 4],
   [BPair.ofNat 6, BPair.ofNat 9, BPair.ofNat 8],
   [BPair.ofNat 2, BPair.ofNat 3, BPair.ofNat 2]]

example : m3' = (List.range 3).map (fun i => (List.range 3).map
    (fun j => ground.getAt BPair.unit
      (ground.getAt [] m3 (ground.getAt 0 q3 i))
      (ground.getAt 0 q3 j))) := by decide +kernel

example : relabelRead 3 m3 m3' q3 := by decide +kernel
example : ¬ relabelRead 3 m3 m3bad q3 := by decide +kernel
example : ¬ (0 < ground.countOf [0, 0, 1]
    (places.monomialsAt (List.replicate 3 1))) := by decide +kernel

example : (detL m3').oneValue (detL m3) :=
  relabel_det 3 m3 m3' q3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

example : detL m3' = detL m3 := by decide +kernel
example : (detL m3).oneValue (BPair.ofNat 5).swap := by decide +kernel

/-! The window instance at the committed data: the swap's
relabeling of the window index — the identity at the unit line,
each loop's key at the moved loop's own — read off the index
action, the electric matrix fixed at that relabeling entrywise,
and the determinant routed at one value with itself, the
theorem's `E`-fix read at `def:elim`'s determinant. -/

private def twIdx (a : List places.Shape) : Nat :=
  places.idxOf true (twIx.map (fun b => carrier.eqConf FA a b))

private def qSwap : List Nat :=
  [0, 10, 13, 16, 11, 14, 17, 12, 15, 18, 1, 4, 7, 2, 5, 8, 3, 6, 9,
    25, 26, 27, 28, 29, 30, 19, 20, 21, 22, 23, 24]

example : qSwap = 0 :: (List.range 30).map (fun i => 1 + twIdx
    (dualConf FA (bdLink 2 3 pSwap fNone) (bdRev 2 3 fNone) 18
      (ground.getAt [] twIx i))) := by decide +kernel

private theorem hqSwap : 0 < ground.countOf qSwap
    (places.monomialsAt (List.replicate 31 1)) := by
  rw [places.countOf_monomialsAt, if_pos (by decide +kernel)]
  exact Nat.succ_pos 0

example : relabelRead 31 bdE bdE qSwap := by decide +kernel

example : (detL bdE).oneValue (detL bdE) :=
  relabel_det 31 bdE bdE qSwap hqSwap (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-! The polynomial carrier's own instance (`lem:split`'s symbol):
a committed two-by-two polynomial square at the transposition, its
literal relabeling decided against the entrywise reading and the
relabeled square's minor reading the source's — decided outright
and routed at `split.pminor_reindex` — with a square one
coefficient off refusing that reading. -/

private def qT : List Nat := [1, 0]

private def pz : split.PMat :=
  [[[BPair.ofNat 1, BPair.ofNat 2], [BPair.ofNat 3]],
   [[BPair.ofNat 4, BPair.ofNat 5], [BPair.ofNat 6]]]

private def pz' : split.PMat :=
  [[[BPair.ofNat 6], [BPair.ofNat 4, BPair.ofNat 5]],
   [[BPair.ofNat 3], [BPair.ofNat 1, BPair.ofNat 2]]]

private def pzbad : split.PMat :=
  [[[BPair.ofNat 6], [BPair.ofNat 4, BPair.ofNat 5]],
   [[BPair.ofNat 3], [BPair.ofNat 1, BPair.ofNat 3]]]

example : pz' = (List.range 2).map (fun i => (List.range 2).map
    (fun j => ground.getAt []
      (ground.getAt [] pz (ground.getAt 0 qT i))
      (ground.getAt 0 qT j))) := by decide +kernel

example : ((List.range 2).all (fun i => (List.range 2).all
    (fun j => decide (poly.oneValue
      (ground.getAt [] (ground.getAt [] pzbad i) j)
      (ground.getAt []
        (ground.getAt [] pz (ground.getAt 0 qT i))
        (ground.getAt 0 qT j)))))) = false := by decide +kernel

example : poly.oneValue (split.pminor pz') (split.pminor pz) := by
  decide +kernel

example : poly.oneValue (split.pminor pz') (split.pminor pz) := by
  have hent : ((List.range 2).all (fun i => (List.range 2).all
      (fun j => decide (poly.oneValue
        (ground.getAt [] (ground.getAt [] pz' i) j)
        (ground.getAt []
          (ground.getAt [] pz (ground.getAt 0 qT i))
          (ground.getAt 0 qT j)))))) = true := by decide +kernel
  exact split.pminor_reindex 2 pz pz' qT (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (fun i j hi hj => of_decide_eq_true
      (ground.all_range_read 2
        (ground.all_range_read 2 hent i hi) j hj))

/-! The moved key's conjugation tie (`keyMoveRead`): the witness
convention discriminated — at the two-direction members the tie
decides at each member's own witness, and at a three-direction
cycle the tie holds at the cycle's witness alone, the forward map
refused. -/

example : keyMoveRead (torusRegion 2 3) 2 3
    (bdLink 2 3 pSwap fNone) pSwap fNone := by decide +kernel
example : keyMoveRead (torusRegion 2 3) 2 3
    (bdLink 2 3 (fun e => e) fZero) (fun e => e) fZero := by
  decide +kernel

private def pCyc : Nat → Nat := fun e => if e == 2 then 0 else e + 1
private def pCycInv : Nat → Nat := fun e => if e == 0 then 2 else e - 1

example : keyMoveRead (torusRegion 3 3) 3 3
    (bdLink 3 3 pCyc fNone) pCycInv fNone := by decide +kernel
example : ¬ keyMoveRead (torusRegion 3 3) 3 3
    (bdLink 3 3 pCyc fNone) pCyc fNone := by decide +kernel


/-! The momentum grids and the two settling moves, decided by
kernel.  The box is anchored at its counts — the one-argument
two-direction grids at degrees two and four, the two-argument
grids at degree two, and the empty argument list occupied at
degree zero and vacant beyond it.  The invariance read
(`bdInvAt`) is decided true at the families the theorem displays:
the pairwise inner products at one and at two arguments and at
two and at three directions, the diagonal quartic, and a product
of two inner products.  Two forged families discriminate its two
conjuncts one at a time — a family occupied at a grid of odd
coordinate total refuses the reflection while surviving the
transposition, and a family occupied at one member of a
transposition pair alone refuses the transposition while
surviving the reflection, each isolating fold decided beside its
refusal — and the two extractions (`bdInv_vanish`, `bdInv_swap`)
are run at committed instances.

The three named families' invariance is routed at one committed
instance each (`ipFam_inv` at a repeated argument over three
directions, `quFam_inv` at one argument, `prodIP_inv` at two
arguments and two directions), and the theorems' freedom in the
argument keys is covered at an out-of-range instance: with both arguments
at or beyond the argument count every named monomial falls short of
the degree, so the family reads the sum's unit at every grid of the
box and the read holds — the theorem route and the kernel's own
decision agreeing there.

The degree-two span is read at a strict combination of the three
ordered argument pairs at two arguments and two directions, each
pair's family scaled by its own count: the combination is decided
invariant at degree two, and at the box member `[[1, 0], [1, 0]]`
— the inner product's monomial at the two arguments and the first
coordinate — the span's identity is committed twice, once through
`deg2_span` and once as the kernel's own decision.  The membership
binder is isolated at a grid of degree three, decided off the box:
the combination forged occupied there is still decided invariant
at degree two, since no member of the box and no transposition of
one reaches a grid of another degree, while the span's identity at
that grid is decided false. -/

example : (momBox 1 2 2).length = 3 := by decide +kernel
example : (momBox 2 2 2).length = 10 := by decide +kernel
example : (momBox 1 2 4).length = 5 := by decide +kernel
example : momBox 0 2 0 = [[]] := by decide +kernel
example : momBox 0 2 3 = [] := by decide +kernel

example : bdInvAt 1 2 2 (ipFam 1 2 0 0) := by decide +kernel
example : bdInvAt 2 2 2 (ipFam 2 2 0 1) := by decide +kernel
example : bdInvAt 1 2 4 (quFam 1 2 0) := by decide +kernel
example : bdInvAt 1 3 4 (prodIP 1 3 0 0 0 0) := by decide +kernel
example : bdInvAt 2 3 2 (ipFam 2 3 0 1) := by decide +kernel

/-- A family forged occupied at `[[1, 1]]`, a grid of odd total at
both coordinates and fixed by the transposition. -/
private def oddForge (g : List (List Nat)) : BPair :=
  if g == [[1, 1]] then BPair.ofNat 1 else BPair.unit

/-- A family forged occupied at `[[2, 0]]` alone, a grid of even
total at both coordinates whose transposition partner `[[0, 2]]`
the family reads at the sum's unit. -/
private def swapForge (g : List (List Nat)) : BPair :=
  if g == [[2, 0]] then BPair.ofNat 1 else BPair.unit

example : ¬ bdInvAt 1 2 2 oddForge := by decide +kernel

example : ((momBox 1 2 2).all (fun g => (List.range 2).all (fun i =>
    dirTot i g % 2 == 0
      || decide ((oddForge g).oneValue BPair.unit)))) = false := by
  decide +kernel

example : ((momBox 1 2 2).all (fun g => (List.range 2).all (fun i =>
    (List.range 2).all (fun j => !decide (i < j)
      || decide ((oddForge (swapDirs i j g)).oneValue (oddForge g))))))
    = true := by decide +kernel

example : ¬ bdInvAt 1 2 2 swapForge := by decide +kernel

example : ((momBox 1 2 2).all (fun g => (List.range 2).all (fun i =>
    dirTot i g % 2 == 0
      || decide ((swapForge g).oneValue BPair.unit)))) = true := by
  decide +kernel

example : ((momBox 1 2 2).all (fun g => (List.range 2).all (fun i =>
    (List.range 2).all (fun j => !decide (i < j)
      || decide ((swapForge (swapDirs i j g)).oneValue (swapForge g))))))
    = false := by decide +kernel

example : (ipFam 1 2 0 0 [[1, 1]]).oneValue BPair.unit :=
  bdInv_vanish 1 2 2 (ipFam 1 2 0 0) (by decide +kernel) [[1, 1]]
    (by decide +kernel) 0 (by decide +kernel) (by decide +kernel)

example : (ipFam 2 2 0 1 (swapDirs 0 1 [[1, 0], [1, 0]])).oneValue
    (ipFam 2 2 0 1 [[1, 0], [1, 0]]) :=
  bdInv_swap 2 2 2 (ipFam 2 2 0 1) (by decide +kernel) [[1, 0], [1, 0]]
    (by decide +kernel) 0 1 (by decide +kernel) (by decide +kernel)

example : bdInvAt 2 3 2 (ipFam 2 3 1 1) := ipFam_inv 2 3 1 1
example : bdInvAt 1 3 4 (quFam 1 3 0) := quFam_inv 1 3 0
example : bdInvAt 2 2 4 (prodIP 2 2 0 1 0 1) := prodIP_inv 2 2 0 1 0 1

example : bdInvAt 1 2 2 (ipFam 1 2 5 7) := ipFam_inv 1 2 5 7
example : bdInvAt 1 2 2 (ipFam 1 2 5 7) := by decide +kernel

/-- A strict combination of the pairwise inner products at two
arguments and two directions: each ordered argument pair's family
scaled by its own count, so no two pairs carry one coefficient. -/
private def cDemo (g : List (List Nat)) : BPair :=
  BPair.sum ((List.range 2).flatMap (fun r =>
    (List.range 2).flatMap (fun s =>
      if r ≤ s then [BPair.ofNat (r + s + 1) * ipFam 2 2 r s g] else [])))

example : bdInvAt 2 2 2 cDemo := by decide +kernel

example : (cDemo [[1, 0], [1, 0]]).oneValue
    (BPair.sum ((List.range 2).flatMap (fun r =>
      (List.range 2).flatMap (fun s =>
        if r ≤ s then
          [cDemo (ipGrid 2 2 r s 0) * ipFam 2 2 r s [[1, 0], [1, 0]]]
        else [])))) :=
  deg2_span 2 2 cDemo (by decide +kernel) [[1, 0], [1, 0]]
    (by decide +kernel)

example : (cDemo [[1, 0], [1, 0]]).oneValue
    (BPair.sum ((List.range 2).flatMap (fun r =>
      (List.range 2).flatMap (fun s =>
        if r ≤ s then
          [cDemo (ipGrid 2 2 r s 0) * ipFam 2 2 r s [[1, 0], [1, 0]]]
        else [])))) := by decide +kernel

/-- A grid of degree three at two arguments and two directions,
off the degree-two box. -/
private def offBoxGrid : List (List Nat) := [[3, 0], [0, 0]]

/-- The combination forged occupied at that grid alone: invariant
at degree two, since the forged grid is off the box and no
transposition of a box member reaches it, and off the span's
identity there. -/
private def offBoxForge (g : List (List Nat)) : BPair :=
  if g == offBoxGrid then BPair.ofNat 5 else cDemo g

example : ground.countOf offBoxGrid (momBox 2 2 2) = 0 := by decide +kernel

example : bdInvAt 2 2 2 offBoxForge := by decide +kernel

example : ¬ (offBoxForge offBoxGrid).oneValue
    (BPair.sum ((List.range 2).flatMap (fun r =>
      (List.range 2).flatMap (fun s =>
        if r ≤ s then
          [offBoxForge (ipGrid 2 2 r s 0) * ipFam 2 2 r s offBoxGrid]
        else [])))) := by decide +kernel

/-! The degree-four span's batteries at one argument: a committed
invariant of the two degree-four families read at both classes of
the box's even members, the quartic's monomial and the cross
monomial, decided and routed through `deg4_span`; the span's
freedom in the direction count covered at one direction, where the
cross grid degenerates off the box and its coefficient withdraws
against its own swap; and the independence's direction-count guard
isolated at one direction, where the box holds the quartic's
monomial alone, the two families read alike, and a combination at
the pair's exchanged coefficients holds the hypothesis with the
conclusion refused — the routed instance and its refused
counterpart beside it. -/

/-- A strict combination of the two degree-four families at one
argument and two directions: the splitting count scaled by three
joined with the quartic family scaled by two. -/
private def cQuart (g : List (List Nat)) : BPair :=
  BPair.ofNat 3 * prodIP 1 2 0 0 0 0 g + BPair.ofNat 2 * quFam 1 2 0 g

example : bdInvAt 1 2 4 cQuart := by decide +kernel

example : ground.countOf [[2, 2]] (momBox 1 2 4) = 1 := by decide +kernel

example : ground.countOf [[4, 0]] (momBox 1 2 4) = 1 := by decide +kernel

example : (cQuart [[2, 2]] + cQuart [[2, 2]]).oneValue
    (cQuart (crossG 2 0 1)
        * prodIP 1 2 0 0 0 0 [[2, 2]]
      + (cQuart (quGrid 1 2 0 0) + cQuart (quGrid 1 2 0 0)
          + (cQuart (crossG 2 0 1)).swap)
        * quFam 1 2 0 [[2, 2]]) :=
  deg4_span 2 cQuart (by decide +kernel) [[2, 2]] (by decide +kernel)

example : (cQuart [[2, 2]] + cQuart [[2, 2]]).oneValue
    (cQuart (crossG 2 0 1)
        * prodIP 1 2 0 0 0 0 [[2, 2]]
      + (cQuart (quGrid 1 2 0 0) + cQuart (quGrid 1 2 0 0)
          + (cQuart (crossG 2 0 1)).swap)
        * quFam 1 2 0 [[2, 2]]) := by decide +kernel

example : (cQuart [[4, 0]] + cQuart [[4, 0]]).oneValue
    (cQuart (crossG 2 0 1)
        * prodIP 1 2 0 0 0 0 [[4, 0]]
      + (cQuart (quGrid 1 2 0 0) + cQuart (quGrid 1 2 0 0)
          + (cQuart (crossG 2 0 1)).swap)
        * quFam 1 2 0 [[4, 0]]) :=
  deg4_span 2 cQuart (by decide +kernel) [[4, 0]] (by decide +kernel)

example : (cQuart [[4, 0]] + cQuart [[4, 0]]).oneValue
    (cQuart (crossG 2 0 1)
        * prodIP 1 2 0 0 0 0 [[4, 0]]
      + (cQuart (quGrid 1 2 0 0) + cQuart (quGrid 1 2 0 0)
          + (cQuart (crossG 2 0 1)).swap)
        * quFam 1 2 0 [[4, 0]]) := by decide +kernel

/-- The quartic family alone at one argument and one direction,
scaled by seven. -/
private def cQuart1 (g : List (List Nat)) : BPair :=
  BPair.ofNat 7 * quFam 1 1 0 g

example : bdInvAt 1 1 4 cQuart1 := by decide +kernel

example : momBox 1 1 4 = [[[4]]] := by decide +kernel

example : crossG 1 0 1 = [[2]] := by
  decide +kernel

example : ground.countOf [[2]] (momBox 1 1 4) = 0 := by decide +kernel

example : (cQuart1 [[4]] + cQuart1 [[4]]).oneValue
    (cQuart1 (crossG 1 0 1)
        * prodIP 1 1 0 0 0 0 [[4]]
      + (cQuart1 (quGrid 1 1 0 0) + cQuart1 (quGrid 1 1 0 0)
          + (cQuart1 (crossG 1 0 1)).swap)
        * quFam 1 1 0 [[4]]) :=
  deg4_span 1 cQuart1 (by decide +kernel) [[4]] (by decide +kernel)

example : (cQuart1 [[4]] + cQuart1 [[4]]).oneValue
    (cQuart1 (crossG 1 0 1)
        * prodIP 1 1 0 0 0 0 [[4]]
      + (cQuart1 (quGrid 1 1 0 0) + cQuart1 (quGrid 1 1 0 0)
          + (cQuart1 (crossG 1 0 1)).swap)
        * quFam 1 1 0 [[4]]) := by decide +kernel

example : ∀ g : List (List Nat),
    0 < ground.countOf g (momBox 1 1 4) →
    ((BPair.ofNat 1) * quFam 1 1 0 g
      + (BPair.ofNat 1).swap * prodIP 1 1 0 0 0 0 g).oneValue
      BPair.unit := by
  intro g hg
  have hgm : g ∈ ([[[4]]] : List (List (List Nat))) :=
    ground.mem_of_countOf_pos g _ hg
  cases hgm with
  | head => decide +kernel
  | tail _ hh => cases hh

example : ¬ (BPair.ofNat 1).oneValue BPair.unit := by decide +kernel

example : ¬ (∀ g : List (List Nat),
    0 < ground.countOf g (momBox 1 2 4) →
    ((BPair.ofNat 1) * quFam 1 2 0 g
      + BPair.unit * prodIP 1 2 0 0 0 0 g).oneValue
      BPair.unit) := fun H =>
  absurd (H (quGrid 1 2 0 0) (by decide +kernel)) (by decide +kernel)

example : BPair.unit.oneValue BPair.unit
    ∧ BPair.unit.oneValue BPair.unit :=
  deg4_indep 2 (by decide +kernel) BPair.unit BPair.unit
    (fun _ _ => BPair.oneValue_trans
      (BPair.add_congr (BPair.unit_mul _) (BPair.unit_mul _))
      (BPair.add_unit BPair.unit))

example : ¬ ((BPair.ofNat 3).oneValue BPair.unit
    ∧ (BPair.ofNat 3).oneValue BPair.unit) := by decide +kernel

/-! The quartic's break at every argument count: the two witness
grids' reads decided at two arguments and two directions — the
splitting counts one and two at the first argument quadruple, the
sum's unit at the further quadruples, and the quartic family
occupied at its own monomial alone but vacant at the cross
monomial — with the quadruple display's collapse onto the first
quadruple's term committed at both witnesses.  The two guards are
isolated beside them: the argument-count guard at the vacant
argument count, where the degree-four box is [] and the identity
holds at every family through the vacuous membership, and the
direction-count guard at one direction, where the box holds the
quartic's monomial alone and the indicator family reads the
identity — each guard's read load-bearing at its refusal.  The theorem's own route
lands at two arguments and two directions and again at three of
each. -/

/-- The coefficient family occupied at the first argument
quadruple alone, the count one there and the sum's unit at every
further quadruple. -/
private def wFirst (r s t u : Nat) : BPair :=
  if r == 0 && s == 0 && t == 0 && u == 0 then BPair.ofNat 1
  else BPair.unit

example : ground.countOf (quGrid 2 2 0 0) (momBox 2 2 4) = 1 := by
  decide +kernel

example : ground.countOf (addG (ipGrid 2 2 0 0 0) (ipGrid 2 2 0 0 1))
    (momBox 2 2 4) = 1 := by decide +kernel

example : quFam 2 2 0 (quGrid 2 2 0 0) = BPair.ofNat 1 := by decide +kernel

example : quFam 2 2 0 (addG (ipGrid 2 2 0 0 0) (ipGrid 2 2 0 0 1))
    = BPair.unit := by decide +kernel

example : prodIP 2 2 0 0 0 0 (quGrid 2 2 0 0) = BPair.ofNat 1 := by
  decide +kernel

example : prodIP 2 2 0 0 0 0 (addG (ipGrid 2 2 0 0 0) (ipGrid 2 2 0 0 1))
    = BPair.ofNat 2 := by decide +kernel

example : prodIP 2 2 0 1 0 0 (quGrid 2 2 0 0) = BPair.unit := by
  decide +kernel

example : prodIP 2 2 1 1 1 1 (quGrid 2 2 0 0) = BPair.unit := by
  decide +kernel

example : prodIP 2 2 0 0 0 1 (addG (ipGrid 2 2 0 0 0) (ipGrid 2 2 0 0 1))
    = BPair.unit := by decide +kernel

example : prodIP 2 2 1 0 1 0 (addG (ipGrid 2 2 0 0 0) (ipGrid 2 2 0 0 1))
    = BPair.unit := by decide +kernel

example : (BPair.sum ((List.range 2).flatMap (fun r =>
      (List.range 2).flatMap (fun s =>
        (List.range 2).flatMap (fun t =>
          (List.range 2).map (fun u =>
            wFirst r s t u
              * prodIP 2 2 r s t u (quGrid 2 2 0 0))))))).oneValue
    (wFirst 0 0 0 0 * BPair.ofNat 1) := by decide +kernel

example : (BPair.sum ((List.range 2).flatMap (fun r =>
      (List.range 2).flatMap (fun s =>
        (List.range 2).flatMap (fun t =>
          (List.range 2).map (fun u =>
            wFirst r s t u * prodIP 2 2 r s t u
              (addG (ipGrid 2 2 0 0 0) (ipGrid 2 2 0 0 1)))))))).oneValue
    (wFirst 0 0 0 0 * BPair.ofNat 2) := by decide +kernel

example : momBox 0 2 4 = [] := by decide +kernel

example : ∀ g : List (List Nat),
    0 < ground.countOf g (momBox 0 2 4) →
    (quFam 0 2 0 g).oneValue
      (BPair.sum ((List.range 0).flatMap (fun r =>
        (List.range 0).flatMap (fun s =>
          (List.range 0).flatMap (fun t =>
            (List.range 0).map (fun u =>
              wFirst r s t u * prodIP 0 2 r s t u g)))))) :=
  fun _ hg => absurd hg (Nat.lt_irrefl 0)

example : ∀ g : List (List Nat),
    0 < ground.countOf g (momBox 1 1 4) →
    (quFam 1 1 0 g).oneValue
      (BPair.sum ((List.range 1).flatMap (fun r =>
        (List.range 1).flatMap (fun s =>
          (List.range 1).flatMap (fun t =>
            (List.range 1).map (fun u =>
              wFirst r s t u * prodIP 1 1 r s t u g)))))) := by
  intro g hg
  have hgm : g ∈ ([[[4]]] : List (List (List Nat))) :=
    ground.mem_of_countOf_pos g _ hg
  cases hgm with
  | head => decide +kernel
  | tail _ hh => cases hh

example : ¬ (∀ g : List (List Nat),
    0 < ground.countOf g (momBox 2 2 4) →
    (quFam 2 2 0 g).oneValue
      (BPair.sum ((List.range 2).flatMap (fun r =>
        (List.range 2).flatMap (fun s =>
          (List.range 2).flatMap (fun t =>
            (List.range 2).map (fun u =>
              wFirst r s t u * prodIP 2 2 r s t u g)))))))  :=
  quartic_breaks 2 2 (by decide +kernel) (by decide +kernel) wFirst

example : ¬ (∀ g : List (List Nat),
    0 < ground.countOf g (momBox 3 3 4) →
    (quFam 3 3 0 g).oneValue
      (BPair.sum ((List.range 3).flatMap (fun r =>
        (List.range 3).flatMap (fun s =>
          (List.range 3).flatMap (fun t =>
            (List.range 3).map (fun u =>
              wFirst r s t u * prodIP 3 3 r s t u g)))))))  :=
  quartic_breaks 3 3 (by decide +kernel) (by decide +kernel) wFirst

/-! The rate clause's odd-degree read: every degree-three and
degree-one grid of the committed boxes holds an odd coordinate
total, the totals fold to the degree, and the vanishing routes
through `oddDeg_vanish` at a committed invariant — the first
breaking invariant sits two even degrees above the leading term.
Beside it the two span theorems' own binders isolate: an
invariance-free family refuses each span identity at a moved
monomial, and a degree-three grid off the box refuses the
degree-four identity's membership read. -/

example : ((momBox 1 2 3).all (fun g => (List.range 2).any (fun i =>
    !(restoration.dirTot i g % 2 == 0)))) = true := by decide +kernel
example : ((momBox 2 3 3).all (fun g => (List.range 3).any (fun i =>
    !(restoration.dirTot i g % 2 == 0)))) = true := by decide +kernel
example : ((momBox 3 2 1).all (fun g => (List.range 2).any (fun i =>
    !(restoration.dirTot i g % 2 == 0)))) = true := by decide +kernel
example : ((momBox 2 3 3).all (fun g =>
    ground.sumNat ((List.range 3).map (fun i => restoration.dirTot i g))
      == 3)) = true := by decide +kernel

example : (ipFam 1 2 0 0 [[1, 2]]).oneValue BPair.unit :=
  oddDeg_vanish 1 2 3 (by decide +kernel) (ipFam 1 2 0 0)
    (by decide +kernel) [[1, 2]] (by decide +kernel)
example : (ipFam 1 2 0 0 [[1, 2]]).oneValue BPair.unit := by
  decide +kernel

example : ¬ bdInvAt 1 2 2 swapForge := by decide +kernel
example : ¬ ((swapForge [[0, 2]]).oneValue
    (BPair.sum ((List.range 1).flatMap (fun r =>
      (List.range 1).flatMap (fun s =>
        if r ≤ s then
          [swapForge (ipGrid 1 2 r s 0) * ipFam 1 2 r s [[0, 2]]]
        else []))))) := by decide +kernel

private def quartForge (g : List (List Nat)) : BPair :=
  if g == [[4, 0]] then BPair.ofNat 1 else BPair.unit

example : ¬ bdInvAt 1 2 4 quartForge := by decide +kernel
example : ¬ ((quartForge [[0, 4]] + quartForge [[0, 4]]).oneValue
    (quartForge (crossG 2 0 1) * prodIP 1 2 0 0 0 0 [[0, 4]]
      + (quartForge (quGrid 1 2 0 0) + quartForge (quGrid 1 2 0 0)
          + (quartForge (crossG 2 0 1)).swap)
        * quFam 1 2 0 [[0, 4]])) := by decide +kernel

private def cubeForge (g : List (List Nat)) : BPair :=
  if g == [[3, 0]] then BPair.ofNat 1 else BPair.unit

example : bdInvAt 1 2 4 cubeForge := by decide +kernel
example : ground.countOf ([[3, 0]] : List (List Nat))
    (momBox 1 2 4) = 0 := by decide +kernel
example : ¬ ((cubeForge [[3, 0]] + cubeForge [[3, 0]]).oneValue
    (cubeForge (crossG 2 0 1) * prodIP 1 2 0 0 0 0 [[3, 0]]
      + (cubeForge (quGrid 1 2 0 0) + cubeForge (quGrid 1 2 0 0)
          + (cubeForge (crossG 2 0 1)).swap)
        * quFam 1 2 0 [[3, 0]])) := by decide +kernel
