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
and its pairing the presentation Gram of its states. At the letters
a link's label enters at its word pair (`slotpower.wordPair`), the
block inside the slot power at those degrees (`con:slotpower`); at a
member's table it enters at its fundamental fold, the block the
lowering span at the fundamentals' tops' tensor in the index order
(`con:memtable`'s reach read, `fundTops` and `blockAt`); at a
vertex the row ends pair against the column ends (`linkEnds`, the
incident links' row and column ends at the vertex, an incoming
link's read at the row and column ends exchanged). A vertex list is
a `VList`: per end its columns, each at its key and length (a
column's length at the letters, a fundamental's index and degree at
a member), the members in their presentation (`Members`: the
collected wirings' coefficient rows at the symbolic tag, or a
stated list of vectors at the vertex's slots with the table whose
pairing reads them, `slotpower.SVec`), and the members' shared
clearing; its Gram is the members' Gram at the clearing squared,
the pair at its reduced representative (`listGram`, `reduceGram`).
A vertex of two ends reads its block's Gram-dual coevaluation: at
opposite orientations the through pairing's projection to the
fused span group by group at the ends' weight lists (`twoEndList`
at `slotpower.throughPair` and `slotpower.projectGroupsT` at the
letters; `slotpower.throughT` at a table), and at two ends of one
orientation, the labels dual, the star's at the letters
(`slotpower.throughPair`) and the table's dual pair carried across
the matched factors at a member (`slotpower.dualThroughT` at the
column match, `slotpower.colMatch`), its self-pairing the block's
count (`twoEndGram` the count's own read at an interface's label
data, the interface's Gram where the list is unstated). A further
vertex at the symbolic tag — its row-end count at or below the
fundamental count (`lem:mixedinv`), the row and column counts
matched, every incident label once at a separated Casimir value in
the mixed power at its word pair (`interpValid` over the power's
multiplicity family at the label calculus's rows and counts) —
reads its wirings, the place permutations at the row ends against
the column ends, each link's factors projected to the label's block
at the link Casimir's interpolant through the mixed power's
occupied Casimir values (`linkCas`, `prop:lap`'s insertion display
`d_f`-cleared on a vertex wiring; `projLink` the interpolant's
factors; `con:units`' interpolant), collected at the wirings' Gram,
the slot power's coordinate pairing at the cycle counts
(`mixedinv.cycleGram` at the states' coefficient rows,
`collectGram` the joined-collection read at the Gram's leading
minors): `vertListSym`, the members the collected rows over the
place permutations (`Members.wirings`, their vectors the rows'
combinations over the wirings' table at `Members.list` and their
Gram the rows against the cycle-count Gram at `Members.gram`) at
the interpolants' clearings' product. A further vertex at the
direct tag, or at a label off the interpolant's reach, reads the
kernel list of the stacked raisings over the fused span at its
unit weight (`vertListDirect` at `slotpower.fusedSpanT` and
`slotpower.kernelVecs`, `def:blockcount`'s carrier at `def:elim`'s
back solve, each member at its primitive representative).
`vertListA` is the label calculus's vertex list at the fundamental
count, the two-end read then the tag's route, and `vertGramA` its
Gram; `Members.letters` reads the slot power's letter count at the
members. The magnetic read's link tier sits here as well: a link's
invariant list at its combined slots with its Gram (`linkList`, the
place permutations' wirings at the cycle-count Gram where the
undaggered and daggered counts match at or below the fundamental
count and the stacked raisings' kernel list at the unit weight
beyond) and the Gram-dual coevaluation's weights, the adjugate
against the determinant (`coevW`, `lem:dualread`(i)); the
window-level contraction is `thm:pairpencil`'s magnetic field. The
presentation field (`con:fusion`) is `Pres`: the generating table
(`con:memtable`), the vertex list, the link list, the boundary
factor's word with its coevaluation tensor (`coevOf`,
`lem:dualread`(i)'s Gram-dual coevaluation of a stated list), the
unit's term read, and the column keys' dual (a column length's
complement at the letters, the fundamentals' involution at a
member); the letters' presentation `presA` at `vertListA`,
`linkList` and the mixed power's whole list at `(1,1)`, and a
member's presentation `presT` at its table, its reach list and its
fundamentals' involution: each fundamental's top the one kernel
member of the stacked raisings at its content among the table's
keys or in the stated product of two earlier fundamentals' blocks
(`fundTops`, the count one the reach read's uniqueness), a label's
top the tops' tensor in the index order and its block the lowering
span there (`blockAt`), the vertex list the kernel over the ends'
blocks' fused span at the unit weight (`slotpower.kernelVecs`;
`def:blockcount`), the link list the kernel over the combined
power's unit-weight monomials, and the boundary factor the `θ`
block's coevaluation; `presNone` the vacant field.
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
scalars: the wirings keyed as the row ends' column values, a
vector at its occupied keys (`slotpower.SVec`). -/
abbrev VComb := slotpower.SVec

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
  slotpower.collect (v.flatMap (fun e =>
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
    slotpower.collect (linkCasC d rs cs acc
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
  (places.perms k).map (fun σ => slotpower.coefAt σ v)

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
of vectors with the table whose weighted pairing reads them. -/
inductive Members
  | wirings (d : Nat) (sig : List Bool) (k : Nat) (rows : List (List BPair))
  | vecs (T : memtable.Table) (l : List slotpower.SVec)

/-- The members as vectors: the rows' combinations over the
wirings' table, one tensor per place permutation, or the stated
list. -/
def Members.list : Members → List slotpower.SVec
  | .wirings d sig k rows =>
    let table := (places.perms k).map (slotpower.wiringG d sig)
    rows.map (slotpower.comboV table)
  | .vecs _ l => l

/-- The members' Gram: the rows against the wirings' cycle-count
Gram, the slot power's coordinate pairing at the cycle counts
(`lem:mixedinv`; `mixedinv.cycleGram`), or the stated list's
pairings at the table's weight. -/
def Members.gram : Members → elim.Mat
  | .wirings d _ k rows =>
    (elim.gramAt (mixedinv.cycleGram d k) rows).map (fun r =>
      r.map BPair.norm)
  | .vecs T l => slotpower.gramT T l

/-- The slot power's letter count at the members: the wirings'
stated count, and at a stated list its table's keys. -/
def Members.letters : Members → Nat
  | .wirings d _ _ _ => d
  | .vecs T _ => T.keys

set_option genInjectivity false in
/-- A vertex list in the ends' slot power (`con:slotpower`): per end
its columns at their keys and lengths, the top word's against the
bottom word's, the members in their presentation, and the members'
shared clearing. -/
structure VList where
  ends : List (List (Nat × Nat) × List (Nat × Nat))
  members : Members
  clear : Pos

/-- The Gram of a vertex list: the members' Gram at the clearing
squared, the pair at its reduced representative. -/
def listGram (l : VList) : elim.Mat × Pos :=
  reduceGram (l.members.gram,
    ground.posOfSucc (posVal l.clear * posVal l.clear - 1))

/-- The ends' columns at the fundamental count, each label's top
columns' lengths against its bottom columns', a column's key its
length. -/
def endCols (d : Nat) (es : List (Shape × Bool)) :
    List (List (Nat × Nat) × List (Nat × Nat)) :=
  es.map (fun e => slotpower.labelCols d e.1)

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
  ⟨endCols d es,
    .wirings d (slotpower.vertexSig d es) k (kept.map (ground.getAt [] rows)),
    ground.posOfSucc (D - 1)⟩

/-- The vertex list at the direct tag: the stacked raisings' kernel
over the fused span at the unit weight at the letters' table, each
member at its primitive representative, the sign the back solve's
own. -/
def vertListDirect (d : Nat) (es : List (Shape × Bool)) : VList :=
  let T := memtable.lettersT d
  let pool := slotpower.fusedSpanT T (slotpower.endBlocks d es)
  ⟨endCols d es,
    .vecs T (slotpower.kernelVecs T (slotpower.vertexSig d es) pool),
    Pos.one⟩

/-- The vertex list of two ends at the letters: the through
pairing's projection to the fused span, the solve group by group
at the ends' weight lists, the block's coevaluation, at the
projection's clearing against the pairing's. -/
def twoEndList (d : Nat) (e1 e2 : Shape × Bool) : VList :=
  let T := memtable.lettersT d
  let tp := slotpower.throughPair d e1 e2
  match tp.1 with
  | [] => ⟨endCols d [e1, e2], .vecs T [], Pos.one⟩
  | _ :: _ =>
    let pr := slotpower.projectGroupsT T
      (slotpower.fusedGroupsT T (slotpower.endBlocks d [e1, e2])) tp.1
    ⟨endCols d [e1, e2], .vecs T [pr.1], tp.2 * pr.2⟩

/-- The vertex list at the label calculus: an untouched vertex the
scalar one, one end the vacant list, two ends the coevaluation,
then the symbolic tag's collected wirings where the row-end count
is at or below the fundamental count with the column count matched
and every incident label at a valid interpolant, and the direct
tag's kernel list otherwise. -/
def vertListA (d : Nat) (es : List (Shape × Bool)) : VList :=
  match es with
  | [] => ⟨[], .vecs (memtable.lettersT d) [slotpower.unitV], Pos.one⟩
  | [e] => ⟨endCols d [e], .vecs (memtable.lettersT d) [], Pos.one⟩
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
member at its primitive representative, with its Gram. -/
def linkList (d : Nat) (sig : List Bool) : List slotpower.SVec × elim.Mat :=
  let ku := (slotpower.upSlots sig).length
  let kd := (slotpower.downSlots sig).length
  if ku == kd && ku ≤ d then
    ((places.perms ku).map (slotpower.wiringG d sig), mixedinv.cycleGram d ku)
  else
    let T := memtable.lettersT d
    let pool := ((places.allMon d sig.length).filter (slotpower.unitWeight d sig)).map
      (fun m => [(m, BPair.ofNat 1)])
    let mems := slotpower.kernelVecs T sig pool
    (mems, slotpower.gramT T mems)

/-- The Gram-dual coevaluation's weights at an invariant list's
Gram: the adjugate against the determinant
(`lem:dualread`(i)'s display at `def:elim`'s adjugate). -/
def coevW (G : elim.Mat) : elim.Mat × BPair :=
  (elim.adjMD G, elim.detD G)

/-! The presentation field (`con:fusion`'s presentation; `con:fiber`
at the member's generating table, `con:memtable`). -/

/-- The Gram-dual coevaluation of a stated list at the weighted
pairing (`lem:dualread`(i)): the tensor `Σ_{jk} A_{jk} y_j ⊗ y_k`
at the Gram's adjugate, with the determinant its clearing, read at
the occupied monomials. -/
def coevOf (T : memtable.Table) (l : List slotpower.SVec) :
    slotpower.SVec × BPair :=
  let cw := coevW (slotpower.gramT T l)
  (slotpower.collect
    ((List.range l.length).flatMap (fun j =>
      (List.range l.length).flatMap (fun k =>
        let a := ground.getAt BPair.unit (ground.getAt [] cw.1 j) k
        if a.isUnitRep then []
        else (slotpower.tensorV (ground.getAt [] l j) (ground.getAt [] l k)).map
          (fun p => (p.1, p.2 * a))))),
   cw.2)

/-- A link's combined slot signature at its tail: the source word's
slots at the dagger reads flipped, the boundary factor's word at a
boundary link at the traversal's orientation (the dual block's
exchanged slots at a reversed traversal, the label dualized), and
the target word's slots; the head's the exchanged signature slot
for slot. -/
def linkSig (wa : Nat × Nat) (bd : Option Bool) (wb wth : Nat × Nat) : List Bool :=
  slotpower.endWordSig wa false
    ++ (match bd with
        | none => []
        | some o => slotpower.endWordSig wth o)
    ++ slotpower.wordSig wb

set_option genInjectivity false in
/-- The presentation field: the generating table, the vertex list at
an incident-end list, the link list at a link's source label, its
boundary read (the traversal's orientation, vacant off the
boundary) and its target label with its Gram, the boundary
factor's word pair with its coevaluation tensor at its clearing
(the `θ` block's, one member at each end of a boundary link; at the
letters the mixed power's whole list at the word `(1,1)`, the trace
against its dagger), the unit's term read, the states' pairing
withdrawn from the entry at the letters, and the column keys' dual
at a reversed traversal, a column length's complement at the
letters and the fundamentals' involution at a member. -/
structure Pres (L : Type) where
  table : memtable.Table
  vertList : List (L × Bool) → Option VList
  linkList : L × Option Bool × L → List slotpower.SVec × elim.Mat
  bdryWord : Nat × Nat
  bdry : slotpower.SVec × BPair
  lessUnit : Bool
  colDual : Nat → Nat

/-- The letters' presentation at a fundamental count: the vertex
lists `vertListA`, the link lists at the symbolic and direct tags,
the boundary factor the mixed power's monomials at `(1,1)`, its
coevaluation the identity's, the wiring, and a column's dual its
complement length. -/
def presA (d : Nat) : Pres Shape :=
  ⟨memtable.lettersT d, fun es => some (vertListA d es),
   fun t => linkList d (linkSig (slotpower.wordPair d t.1) t.2.1
     (slotpower.wordPair d t.2.2) (1, 1)),
   (1, 1),
   coevOf (memtable.lettersT d) ((places.allMon d 2).map (fun m => [(m, BPair.ofNat 1)])),
   true,
   fun l => d - l⟩

/-- The vacant presentation, the interface's read at a datum
without one. -/
def presNone (L : Type) : Pres L :=
  ⟨memtable.lettersT 0, fun _ => none, fun _ => ([], []), (0, 0), ([], BPair.ofNat 1),
   true, fun l => l⟩

/-- A weight list one value with a stated natural list, the
coordinates' one-value reads at every position. -/
def weightIs (w : List BPair) (u : List Nat) : Bool :=
  w.length == u.length
    && (List.zipWith (fun x n => decide (x.oneValue (BPair.ofNat n))) w u).all (fun b => b)

/-- One step of the reach read at a fundamental (`con:memtable`):
the top at a filled entry kept; at a vacant entry the one kernel
member of the stacked raisings at the fundamental's content among
the table's keys where the reach list names no product, and in the
tensor of two earlier fundamentals' blocks at their filled tops
where it names one, the kernel's count one the uniqueness read, the
member at its primitive representative with its degree. -/
def reachStep (T : memtable.Table) (reach : List (Option (Nat × Nat)))
    (acc : List (Option (slotpower.SVec × Nat))) (i : Nat) :
    Option (slotpower.SVec × Nat) :=
  match ground.getAt none acc i with
  | some t => some t
  | none =>
    match ground.getAt none reach i with
    | none =>
      let pool := (List.range T.keys).filterMap (fun k =>
        if weightIs (memtable.keyWeight T k) (unitAt T.rank i)
        then some [([k], BPair.ofNat 1)] else none)
      match slotpower.kernelT T [false] pool with
      | [k] => some (slotpower.prim (slotpower.comboV pool k), 1)
      | [] => none
      | _ :: _ :: _ => none
    | some (j, k) =>
      match ground.getAt none acc j, ground.getAt none acc k with
      | some (tj, dj), some (tk, dk) =>
        let sig := List.replicate (dj + dk) false
        let Wj := slotpower.blockSpanT T (List.replicate dj false) tj
        let Wk := slotpower.blockSpanT T (List.replicate dk false) tk
        let pool := Wj.flatMap (fun u => Wk.filterMap (fun v =>
          let t := slotpower.tensorV u v
          if weightIs (slotpower.weightV T sig t) (unitAt T.rank i) then some t
          else none))
        match slotpower.kernelT T sig pool with
        | [kv] => some (slotpower.prim (slotpower.comboV pool kv), dj + dk)
        | [] => none
        | _ :: _ :: _ => none
      | none, _ => none
      | some _, none => none

/-- The fundamentals' tops at a table and a reach list, each with
its degree: the reach read's entries filled one round per
fundamental, an entry filled once its stated product's entries
are, vacant where the uniqueness read refuses. -/
def fundTops (T : memtable.Table) (reach : List (Option (Nat × Nat))) :
    List (Option (slotpower.SVec × Nat)) :=
  (List.range T.rank).foldl (fun acc _ =>
    (List.range T.rank).map (reachStep T reach acc))
    (List.replicate T.rank none)

/-- A label's factors at the fundamentals' tops: per fundamental its
index with its degree, once per unit of the label's fold, in the
index order. -/
def factorsOf (tops : List (Option (slotpower.SVec × Nat))) (l : List Nat) :
    List (Nat × Nat) :=
  (List.range l.length).flatMap (fun i =>
    match ground.getAt none tops i with
    | some (_, dg) => List.replicate (ground.getAt 0 l i) (i, dg)
    | none => [])

/-- A label's degree at the fundamentals' tops, its factors'
degrees' sum. -/
def degOf (tops : List (Option (slotpower.SVec × Nat))) (l : List Nat) : Nat :=
  ground.sumNat ((factorsOf tops l).map Prod.snd)

/-- A label's top at the fundamentals' tops: the tops' tensor in the
index order at the label's fold, the Cartan product, vacant where
a needed top is. -/
def topOf (tops : List (Option (slotpower.SVec × Nat))) (l : List Nat) :
    Option slotpower.SVec :=
  (List.range l.length).foldl (fun acc i =>
    match acc, ground.getAt none tops i with
    | some v, some (t, _) =>
      some ((List.range (ground.getAt 0 l i)).foldl (fun a _ => slotpower.tensorV a t) v)
    | some v, none => if ground.getAt 0 l i == 0 then some v else none
    | none, _ => none) (some slotpower.unitV)

/-- A label's block at a table: the lowering span at its top in the
power at its degree, vacant where the top is. -/
def blockAt (T : memtable.Table) (tops : List (Option (slotpower.SVec × Nat)))
    (l : List Nat) : List slotpower.SVec :=
  match topOf tops l with
  | none => []
  | some t => slotpower.blockSpanT T (List.replicate (degOf tops l) false) t

/-- The dual coherence read at a label (`con:memtable`): the dual
pair carries the label's block, slot by slot at `c W`, into its
dual label's block's span, the factors matched by fundamental
index to the dual fundamental and the image relabeled along the
match (`slotpower.colMatch`; `slotpower.spanMemberT`); false at a
table without a dual pair or at factors off the match. -/
def dualCoherent (T : memtable.Table) (tops : List (Option (slotpower.SVec × Nat)))
    (dualF : Nat → Nat) (l : List Nat) : Bool :=
  match T.dual with
  | none => false
  | some (c, _) =>
    let m := memtable.smul c T.wt
    let deg := degOf tops l
    let dl := (List.range l.length).map (fun i => ground.getAt 0 l (dualF i))
    let pairs := (slotpower.colMatch dualF true
      (slotpower.layoutOf 0 (factorsOf tops l, []) 0)
      (slotpower.layoutOf 0 (factorsOf tops dl, []) 0)).flatMap (fun p =>
        List.zipWith (fun a b => (a, b)) p.1 p.2.1)
    let σ := (List.range deg).map (fun t =>
      match pairs.find? (fun p => p.2 == t) with
      | some p => p.1
      | none => t)
    let W' := blockAt T tops dl
    pairs.length == deg
      && (blockAt T tops l).all (fun v =>
        slotpower.spanMemberT T W' (slotpower.relabelV σ
          ((List.range deg).foldl (fun w s => slotpower.actT m false s w) v)))

/-- A member's presentation at its generating table
(`con:memtable`), its reach list and its fundamentals' involution
(`con:fiber`): a vertex of two ends at opposite orientations reads
the through pairing's projection to the fused span, the block's
coevaluation at its clearing (`con:slotpower`; `lem:dualread`(i)),
and at one orientation, the labels dual, the dual pair's tensor
across the matched factors projected there, the factors matched by
fundamental index to the dual fundamental (`slotpower.colMatch`),
each at the block's count; a further vertex the stacked raisings'
kernel over the ends' blocks' fused span at the unit weight, an
incoming end at the dual block's daggered slots (`def:blockcount`;
`lem:dualread`(i)); the link list the kernel over the fused span of
the source's block at its dagger reads flipped, the `θ` block at a
boundary link and the target's block, with its weighted Gram (the
invariant projection of the fused span, the blocks' coefficients
the states' factors, `con:coeff`); the boundary factor the `θ`
block's word with its coevaluation; and the column keys' dual the
fundamentals' involution. -/
def presT (T : memtable.Table) (reach : List (Option (Nat × Nat)))
    (dualF : Nat → Nat) (theta : List Nat) : Pres (List Nat) :=
  let tops := fundTops T reach
  let deg := fun (l : List Nat) => degOf tops l
  let blk := fun (l : List Nat) => blockAt T tops l
  let sigOf := fun (e : List Nat × Bool) => List.replicate (deg e.1) (!e.2)
  let colsOf := fun (e : List Nat × Bool) =>
    ((factorsOf tops e.1, ([] : List (Nat × Nat))))
  ⟨T,
   fun es =>
     let gen := fun (es : List (List Nat × Bool)) =>
       let pool := slotpower.fusedSpanT T (es.map (fun e => (sigOf e, blk e.1)))
       some ⟨es.map colsOf,
         .vecs T (slotpower.kernelVecs T (es.flatMap sigOf) pool), Pos.one⟩
     match es with
     | [] => some ⟨[], .vecs T [slotpower.unitV], Pos.one⟩
     | [e] => some ⟨[colsOf e], .vecs T [], Pos.one⟩
     | [e1, e2] =>
       let n1 := deg e1.1
       let n := n1 + deg e2.1
       let same := e1.2 == e2.2
       let pairs := (slotpower.colMatch dualF same
         (slotpower.layoutOf 0 (colsOf e1) 0)
         (slotpower.layoutOf 0 (colsOf e2) n1)).flatMap (fun p =>
           List.zipWith (fun a b => (a, b)) p.1 p.2.1)
       let tp : Option (slotpower.SVec × Pos) :=
         if pairs.length != n1 || n1 != deg e2.1 then none
         else if same then slotpower.dualThroughT T pairs n
         else some (slotpower.throughT T pairs n)
       match tp with
       | none => some ⟨[colsOf e1, colsOf e2], .vecs T [], Pos.one⟩
       | some tp =>
         let groups := slotpower.fusedGroupsT T
           [(sigOf e1, blk e1.1), (sigOf e2, blk e2.1)]
         let pr := slotpower.projectGroupsT T groups tp.1
         some ⟨[colsOf e1, colsOf e2],
           .vecs T (if pr.1.length == 0 then [] else [pr.1]), tp.2 * pr.2⟩
     | e1 :: e2 :: e3 :: t => gen (e1 :: e2 :: e3 :: t),
   fun t =>
     let ends := (List.replicate (deg t.1) true, blk t.1)
       :: (match t.2.1 with
           | none => []
           | some o => [(List.replicate (deg theta) (!o), blk theta)])
       ++ [(List.replicate (deg t.2.2) false, blk t.2.2)]
     let mems := slotpower.kernelVecs T (ends.flatMap Prod.fst)
       (slotpower.fusedSpanT T ends)
     (mems, slotpower.gramT T mems),
   (deg theta, 0),
   coevOf T (blk theta),
   false,
   dualF⟩

end fiber
