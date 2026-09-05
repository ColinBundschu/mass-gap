import MassGap.Lap
import MassGap.Labels
import MassGap.Slotpower
import MassGap.Mixedinv
/-!
`con:fiber` — the two-plaquette fiber, and the carrier's fibers in the
presentation. The theta-graph's invariant fiber is the span of the
permutation-presentation states in the two plaquette variables, the
holonomies read as link matrices at the keys `0` and `1`
(`con:states`' `Comb` at those factor lists), and its pairing is
`prop:algebra`'s identity through the presentation Gram, the fiber's
own read (`pairP` at `prop:wg`'s `pairFull`); the graph's operator
data are `con:twoplaq`'s displays, the recorded consumer.

The carrier's fibers (`def:carrier`) read in the presentation at the
links' variables, the fiber's stated list the vertex lists' product
and its pairing the presentation Gram of its states. A link's label
enters at its word pair (`slotpower.wordPair`), the block inside the
slot power at those degrees (`con:slotpower`); at a vertex the row
ends pair against the column ends (`linkEnds`, the incident links' row
and column ends at the vertex, an incoming link's read at the row and
column ends exchanged). A vertex list is a `VList`: per end its word
pair, the members in their presentation (`Members`: the collected
wirings' coefficient rows at the symbolic tag, a stated list of graded
vectors at the vertex's slots otherwise, `slotpower.GVec`), and the
members' shared clearing; its Gram is the members' Gram at the
clearing squared, the pair at its reduced representative (`listGram`,
`reduceGram`). A vertex of two ends reads its block's Gram-dual
coevaluation, the through pairing's projection to the fused span group
by group at the ends' weight lists (`twoEndList` at
`slotpower.throughPair` and `slotpower.projectGroups`), its
self-pairing the block's count (`twoEndGram` the count's own read at
an interface's label data, the interface's Gram where the list is
unstated). A further vertex at the symbolic tag — its row-end count at
or below the fundamental count (`lem:mixedinv`), the row and column
counts matched, every incident label once at a separated Casimir value
in the mixed power at its word pair (`interpValid` over the power's
multiplicity family at the label calculus's rows and counts) — reads
its wirings, the place permutations at the row ends against the column
ends, each link's factors projected to the label's block at the link
Casimir's interpolant through the mixed power's occupied Casimir
values (`linkCas`, `prop:lap`'s insertion display `d_f`-cleared on a
vertex wiring; `projLink` the interpolant's factors; `con:units`'
interpolant), collected at the wirings' Gram, the slot power's
coordinate pairing at the cycle counts (`mixedinv.cycleGram` at the
states' coefficient rows, `collectGram` the joined-collection read at
the Gram's leading minors): `vertListSym`, the members the collected
rows over the place permutations (`Members.wirings`, their graded
vectors the rows' combinations over the wirings' table at
`Members.list` and their Gram the rows against the cycle-count Gram at
`Members.gram`) at the interpolants' clearings' product. A further
vertex at the direct tag, or at a label off the interpolant's reach,
reads the kernel list of the stacked raisings over the fused span at
its unit weight (`vertListDirect` at `slotpower.fusedSpan` and
`slotpower.kernelAt`, `def:blockcount`'s carrier at `def:elim`'s back
solve, each member at its primitive representative in the slot power's
coordinates, `slotpower.gprim`). `vertListA` is the label calculus's
vertex list at the fundamental count, the two-end read then the tag's
route, and `vertGramA` its Gram; `Members.letters` reads the slot
power's letter count at the members. The magnetic read's link tier
sits here as well: a link's invariant list at its combined slots
with its Gram (`linkList`, the place permutations' wirings at the
cycle-count Gram where the undaggered and daggered counts match at
or below the fundamental count and the stacked raisings' kernel
list at the unit weight beyond) and the Gram-dual coevaluation's
weights, the adjugate against the determinant (`coevW`,
`lem:dualread`(i)); the window-level contraction is
`thm:pairpencil`'s magnetic field.
-/

namespace fiber
open ground places

/-- The fiber's pairing, `prop:algebra`'s identity through the
presentation Gram. -/
def pairP (Fa Fb : states.FList) (a b : states.Comb) :
    poly.PPair :=
  wg.pairFull wg.evalPhi Fa Fb a b

/-! The vertex lists at the label calculus. -/

/-- The incident links' ends at a vertex: per link its row-end
positions and its column-end values, an outgoing link at its word
pair's undaggered rows and daggered columns and an incoming link at
the exchange, the dual label's read at the head; the rows and the
columns each numbered consecutively along the incident list. -/
def linkEnds (d : Nat) : List (Shape × Bool) → Nat → Nat →
    List (List Nat × List Nat)
  | [], _, _ => []
  | e :: t, r0, c0 =>
    let w := slotpower.wordPair d e.1
    let nr := if e.2 then w.1 else w.2
    let nc := if e.2 then w.2 else w.1
    ((List.range nr).map (fun i => r0 + i),
      (List.range nc).map (fun i => c0 + i))
      :: linkEnds d t (r0 + nr) (c0 + nc)

/-- A link end's label at a stated involution: the label itself at
an outgoing end, its dual at an incoming one. -/
private def endLabel {L : Type} (dual : L → L) (e : L × Bool) : L :=
  if e.2 then e.1 else dual e.1

/-- The two-end Gram at an interface's label data, the interface's
Gram read where the vertex list is unstated: a vertex of two ends
at a label against its dual reads the block's Gram-dual
coevaluation, one member at the block's count (`lem:dualread`(i)),
a vertex of one end or of two ends off the dual pair the vacant
list, an untouched vertex the scalar one, and a vertex of three or
more ends vacant, its list the presentation's own. -/
def twoEndGram {L : Type} (eqL : L → L → Bool) (dual : L → L)
    (dim : L → Nat) (es : List (L × Bool)) : Option (elim.Mat × Pos) :=
  match es.map (endLabel dual) with
  | [] => some ([[BPair.ofNat 1]], Pos.one)
  | [_] => some ([], Pos.one)
  | [x, y] =>
    some (if eqL y (dual x) then [[BPair.ofNat (dim x)]] else [], Pos.one)
  | _ :: _ :: _ :: _ => none

/-- A vertex state, a combination of wirings at the residue's
scalars: the wirings keyed as the row ends' column values. -/
abbrev VComb := List (List Nat × BPair)

/-- A state collected at its wirings, one entry per occupied
wiring, each key's fold at the reduced representative
(`ground.joinBy`). -/
private def vcollect (c : VComb) : VComb :=
  c.foldl (fun acc e =>
    ground.joinBy (fun a b => a == b) (fun y x => (y + x).norm) e.1 e.2 acc) []

/-- A state's coefficient at a wiring, the key's fold over the
state's entries. -/
def coefAt (w : List Nat) (v : VComb) : BPair :=
  v.foldl (fun acc e => if e.1 == w then acc + e.2 else acc) BPair.unit

/-- Two states one value at every wiring's coefficient, each key's
fold read across both. -/
def vOneValue (u v : VComb) : Bool :=
  let keys := (u ++ v).map Prod.fst
  keys.all (fun w => (coefAt w u).oneValue (coefAt w v))

/-- The link Casimir's insertion on a vertex wiring, `2 d_f`-cleared
(`prop:lap`'s display at the link's row and column ends at the
vertex): the within-factor terms at `c_f`, the counting term at the
mixed pairs against the same-end pairs, the row pairs' transposition
at the places (`lap.swapIdx`) and the column pairs' at the values
(`lap.mapVals`) each at `2 d_f`, and the mixed pairs' contraction
`C_rc` withdrawn — the closed pair at the loop value and the open
pair at the witness transposition. -/
def linkCas (d : Nat) (rs cs : List Nat) (σ : List Nat) : VComb :=
  let uu := lap.pairsOf rs
  let dd := lap.pairsOf cs
  let mixed := rs.flatMap (fun i => cs.map (fun j => (i, j)))
  (σ, BPair.ofNat ((d * d - 1) * (rs.length + cs.length) + 2 * mixed.length)
        + (BPair.ofNat (2 * (uu.length + dd.length))).swap)
    :: uu.map (fun p => (lap.swapIdx p.1 p.2 σ, BPair.ofNat (2 * d)))
    ++ dd.map (fun p => (lap.mapVals p.1 p.2 σ, BPair.ofNat (2 * d)))
    ++ mixed.map (fun p =>
      if ground.getAt 0 σ p.1 == p.2 then (σ, (BPair.ofNat (2 * d * d)).swap)
      else (lap.swapIdx p.1 (places.posOf p.2 σ) σ, (BPair.ofNat (2 * d)).swap))

/-- The insertion's linear extension over a vertex state. -/
def linkCasC (d : Nat) (rs cs : List Nat) (v : VComb) : VComb :=
  vcollect (v.flatMap (fun e =>
    (linkCas d rs cs e.1).map (fun t => (t.1, e.2 * t.2))))

/-- A multiplicity family fused with one label at the label
calculus's rows and counts: every member's row at its count's
multiple joined class by class at the reduction
(`ground.joinBy`). -/
private def fuseFam (d : Nat) (b : Shape) (fam : List (Shape × Nat)) :
    List (Shape × Nat) :=
  fam.foldl (fun acc e =>
    (labels.rowL d e.1 b).foldl (fun acc2 c =>
      ground.joinBy (fun a b => labels.reduce a == labels.reduce b) Nat.add
        c (e.2 * labels.countL e.1 b c) acc2) acc) []

/-- The mixed power's multiplicity family at a word pair: the unit
fused with the fundamental at the top degree and with its dual at
the bottom degree. -/
private def mixedFam (d p q : Nat) : List (Shape × Nat) :=
  let f := ground.bumpAt 0 (labels.unitL d)
  let fam := (List.range p).foldl (fun acc _ => fuseFam d f acc)
    [(labels.unitL d, 1)]
  (List.range q).foldl (fun acc _ => fuseFam d (labels.dualL f) acc) fam

/-- The interpolant's nodes at a label: the occupied labels of the
mixed power at the label's word pair off the label's own class. -/
def interpNodes (d : Nat) (s : Shape) : List Shape :=
  let w := slotpower.wordPair d s
  (mixedFam d w.1 w.2).filterMap (fun e =>
    if labels.reduce e.1 == labels.reduce s || e.2 == 0 then none
    else some e.1)

/-- The interpolant's validity at a label: the label once in the
mixed power at its word pair, at a Casimir value separated from
every further occupied label's there. -/
def interpValid (d : Nat) (s : Shape) : Bool :=
  let w := slotpower.wordPair d s
  let fam := mixedFam d w.1 w.2
  (fam.foldl (fun acc e =>
      if labels.reduce e.1 == labels.reduce s then acc + e.2 else acc) 0 == 1)
    && (interpNodes d s).all (fun n =>
      !(c2hat.dfQ (labels.reduce n) == c2hat.dfQ (labels.reduce s)))

/-- The interpolant's clearing at a label: the product of the
label's cleared Casimir against each node's, `2 d_f` times the
Casimir gap per node. -/
private def interpClear (d : Nat) (s : Shape) : BPair :=
  (interpNodes d s).foldl (fun acc n =>
    acc * (BPair.ofNat (c2hat.dfQ (labels.reduce s))
      + (BPair.ofNat (c2hat.dfQ (labels.reduce n))).swap)) (BPair.ofNat 1)

/-- The label's projection at a link, the cleared interpolant's
factors applied in turn: per node the cleared insertion less the
node's cleared Casimir. -/
private def projLink (d : Nat) (rs cs : List Nat) (s : Shape) (v : VComb) : VComb :=
  (interpNodes d s).foldl (fun acc n =>
    vcollect (linkCasC d rs cs acc
      ++ acc.map (fun e =>
        (e.1, e.2 * (BPair.ofNat (c2hat.dfQ (labels.reduce n))).swap)))) v

/-- The vertex projection: the links' projections composed along the
incident list. -/
def projVertex (d : Nat) (es : List (Shape × Bool)) (v : VComb) : VComb :=
  (List.zipWith (fun e ends => (e, ends)) es (linkEnds d es 0 0)).foldl
    (fun acc p => projLink d p.2.1 p.2.2 p.1.1 acc) v

/-- A vertex state's coefficient row over the place permutations,
each key's fold at its permutation's position. -/
private def rowOf (k : Nat) (v : VComb) : List BPair :=
  (places.perms k).map (fun σ => coefAt σ v)

/-- The collection at a Gram: the members joined one per refusal,
a member refusing exactly where the collected list's Gram with it
reads a determinant off the sum's unit (`lem:lowerspan`'s
joined-collection read at the Gram's leading minors). -/
private def collectGram (N : elim.Mat) : List Nat :=
  (List.range N.length).foldl (fun kept i =>
    let sub := (kept ++ [i]).map (fun a =>
      (kept ++ [i]).map (fun b => ground.getAt BPair.unit (ground.getAt [] N a) b))
    if (elim.detD sub).oneValue BPair.unit then kept else kept ++ [i]) []

/-- A cleared Gram at its reduced representative: the entries and
the second member divided at their shared content, positive at the
second member's own, one value at the homogeneity principle. -/
private def reduceGram (g : elim.Mat × Pos) : elim.Mat × Pos :=
  let k := BPair.sharedCount (g.1.flatMap (fun r => r)) g.2
  (g.1.map (BPair.listPrim k), ground.posOfSucc (posVal g.2 / k - 1))

set_option genInjectivity false in
/-- A vertex list's members in their presentation: the collected
wirings' coefficient rows over the place permutations at the
vertex's signature (`con:fiber`'s symbolic tag), or a stated list
of graded vectors. -/
inductive Members
  | wirings (d : Nat) (sig : List Bool) (k : Nat) (rows : List (List BPair))
  | vecs (l : List slotpower.GVec)

/-- The members as graded vectors: the rows' combinations over the
wirings' table, one tensor per place permutation, or the stated
list. -/
def Members.list : Members → List slotpower.GVec
  | .wirings d sig k rows =>
    let table := (places.perms k).map (slotpower.wiringG d sig)
    rows.map (slotpower.combo table)
  | .vecs l => l

/-- The members' Gram: the rows against the wirings' cycle-count
Gram, the slot power's coordinate pairing at the cycle counts
(`lem:mixedinv`; `mixedinv.cycleGram`), or the stated list's
coordinate pairings. -/
def Members.gram : Members → elim.Mat
  | .wirings d _ k rows =>
    (elim.gramAt (mixedinv.cycleGram d k) rows).map (fun r =>
      r.map BPair.norm)
  | .vecs l => slotpower.gramOf l

/-- The slot power's letter count at the members: the wirings'
stated count, and at a stated list the coordinate families' width,
a content one occupancy per letter. -/
def Members.letters : Members → Nat
  | .wirings d _ _ _ => d
  | .vecs l => (getAt (⟨[], []⟩ : blockcount.HVec) (getAt [] l 0) 0).content.length

set_option genInjectivity false in
/-- A vertex list in the ends' slot power (`con:slotpower`): per end
its word pair, the members in their presentation, and the members'
shared clearing. -/
structure VList where
  ends : List (Nat × Nat)
  members : Members
  clear : Pos

/-- The Gram of a vertex list: the members' Gram at the clearing
squared, the pair at its reduced representative. -/
def listGram (l : VList) : elim.Mat × Pos :=
  reduceGram (l.members.gram,
    ground.posOfSucc (posVal l.clear * posVal l.clear - 1))

/-- The ends' word pairs at the fundamental count. -/
def endPairs (d : Nat) (es : List (Shape × Bool)) : List (Nat × Nat) :=
  es.map (fun e => slotpower.wordPair d e.1)

/-- The vertex list at the symbolic tag: the wirings' projections
as coefficient rows over the place permutations, collected at their
Gram, at the interpolants' clearings' product. -/
def vertListSym (d : Nat) (es : List (Shape × Bool)) : VList :=
  let ends := linkEnds d es 0 0
  let k := ground.sumNat (ends.map (fun e => e.1.length))
  let rows := (places.perms k).map (fun σ =>
    rowOf k (projVertex d es [(σ, BPair.ofNat 1)]))
  let kept := collectGram (elim.gramAt (mixedinv.cycleGram d k) rows)
  let D := es.foldl (fun acc e => acc * BPair.marginN (interpClear d e.1)) 1
  ⟨endPairs d es,
    .wirings d (slotpower.vertexSig d es) k (kept.map (ground.getAt [] rows)),
    ground.posOfSucc (D - 1)⟩

/-- The vertex list at the direct tag: the stacked raisings' kernel
over the fused span at the unit weight, each member read at its
coordinates in the slot power and at its primitive representative
there, the sign the back solve's own. -/
def vertListDirect (d : Nat) (es : List (Shape × Bool)) : VList :=
  let pool := slotpower.fusedSpan d es
  ⟨endPairs d es,
    .vecs ((slotpower.kernelAt d (slotpower.vertexSig d es) pool).map (fun k =>
      slotpower.gprim (slotpower.gtrim (slotpower.combo pool k)))),
    Pos.one⟩

/-- The vertex list of two ends: the through pairing's projection to
the fused span, the solve group by group at the ends' weight
lists, the block's coevaluation, at the projection's clearing
against the pairing's. -/
def twoEndList (d : Nat) (e1 e2 : Shape × Bool) : VList :=
  let tp := slotpower.throughPair d e1 e2
  match tp.1 with
  | [] => ⟨endPairs d [e1, e2], .vecs [], Pos.one⟩
  | _ :: _ =>
    let pr := slotpower.projectGroups (slotpower.fusedGroups d [e1, e2]) tp.1
    ⟨endPairs d [e1, e2], .vecs [pr.1], tp.2 * pr.2⟩

/-- The vertex list at the label calculus: an untouched vertex the
scalar one, one end the vacant list, two ends the coevaluation,
then the symbolic tag's collected wirings where the row-end count
is at or below the fundamental count with the column count matched
and every incident label at a valid interpolant, and the direct
tag's kernel list otherwise. -/
def vertListA (d : Nat) (es : List (Shape × Bool)) : VList :=
  match es with
  | [] => ⟨[], .vecs [slotpower.gunit d], Pos.one⟩
  | [e] => ⟨endPairs d [e], .vecs [], Pos.one⟩
  | [e1, e2] => twoEndList d e1 e2
  | _ :: _ :: _ :: _ =>
    let ends := linkEnds d es 0 0
    let kr := ground.sumNat (ends.map (fun e => e.1.length))
    let kc := ground.sumNat (ends.map (fun e => e.2.length))
    if kr == kc && kr ≤ d && es.all (fun e => interpValid d e.1) then
      vertListSym d es
    else
      vertListDirect d es

/-- The vertex Gram at the label calculus, the vertex list's own. -/
def vertGramA (d : Nat) (es : List (Shape × Bool)) : elim.Mat × Pos :=
  listGram (vertListA d es)

/-- The invariant list of the mixed power at a slot signature with
its Gram, a link's list at its combined slots (`con:fiber`'s
magnetic read): the place permutations' wirings at the cycle-count
Gram where the undaggered and daggered counts match at or below
the fundamental count (`lem:mixedinv`), and beyond, the stacked
raisings' kernel list at the unit weight over the power's
unit-weight monomials (`def:blockcount`; `con:slotpower`), each
member at its primitive representative, with its coordinate
Gram. -/
def linkList (d : Nat) (sig : List Bool) : List slotpower.GVec × elim.Mat :=
  let ku := (slotpower.upSlots sig).length
  let kd := (slotpower.downSlots sig).length
  if ku == kd && ku ≤ d then
    ((places.perms ku).map (slotpower.wiringG d sig), mixedinv.cycleGram d ku)
  else
    let pool := ((places.allMon d sig.length).filter (slotpower.unitWeight d sig)).map
      (fun m => slotpower.gOfMons d [(m, BPair.ofNat 1)])
    let mems := (slotpower.kernelAt d sig pool).map (fun k =>
      slotpower.gprim (slotpower.gtrim (slotpower.combo pool k)))
    (mems, slotpower.gramOf mems)

/-- The Gram-dual coevaluation's weights at an invariant list's
Gram: the adjugate against the determinant
(`lem:dualread`(i)'s display at `def:elim`'s adjugate). -/
def coevW (G : elim.Mat) : elim.Mat × BPair :=
  (elim.adjO elim.detD BPair.swap G, elim.detD G)

end fiber
