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
A vertex of two ends reads its block's Gram-dual coevaluation,
`lem:dualread`(i)'s display at the block's stated list
(`coevThrough`): at opposite orientations the second factor at the
exchanged actions on the one coordinate family, and at two ends of
one orientation, the labels dual, read through the identification
(`slotpower.identifyV` along the column match,
`slotpower.transportSlots`), the star at the tie columns at the
letters (`twoEndList`) and the table's dual pair at every slot at
a member (`presT`), its self-pairing the block's count at the
clearing (`twoEndGram` the count's own read at an interface's
label data, the interface's Gram where the list is unstated); the
through pairing's projection to the fused span reads one value with
it (`con:slotpower`), the check module's pins. A further
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
against the determinant (`coevW` at a stated Gram; at a
collection's weight grades `coevG`, the adjugate graded at the
grades, each grade's descent adjugate of its stored Gram at the
further grades' stored determinants, with `coevG_read` its
equality to the whole Gram's adjugate at the grades' own pairs and
`coevG_block` the identity at a block's own grades, and
`coevOf_display`, `coevThrough_display` and `coevOf_block` the
coevaluation tensors as the display over every pair at the adjugate,
`coevDisplay`, `lem:dualread`(i)); the
window-level contraction is `thm:pairpencil`'s magnetic field. The
presentation field (`con:fusion`) is `Pres`: the generating table
(`con:memtable`), the vertex list, the link list, the boundary
factor's word with its coevaluation tensor (`coevOf`,
`lem:dualread`(i)'s Gram-dual coevaluation over the weight grades'
own pairs; at the letters the mixed power's whole list at `(1,1)`
grouped at its collection, `slotpower.listGroupsT`), the
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
span there (`blockAt`, its weight grades `groupsAt`), the vertex
list the kernel over the ends'
blocks' fused span at the unit weight (`slotpower.kernelVecs`;
`def:blockcount`), the link list the kernel over the combined
power's unit-weight monomials, and the boundary factor the `θ`
block's coevaluation; `presNone` the vacant field.

At present fundamental tops the tensor constructor is total,
with its degree exactly the factors' degree fold (`topOf_total`,
`topOf_degree`). Occupied fundamental tops give an occupied top
(`topOf_occupied`). G2's two constructed fundamentals have their
stated weights, and every two-coroot label's tensor top is
homogeneous at that label (`topOf_weight_G2`). Its lowering span
contains that top (`blockAt_top_mem_G2`); the occupancy family
`blockWeights` lists the weight of every collected member, its
length the collected dimension. At G2 every member is a canonical
two-coroot list, and the label occurs in its family
(`blockWeights_shape_G2`, `blockWeights_top_G2`).
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
abbrev VComb (k : Nat) := slotpower.SVec k

/-- The link Casimir's insertion on a vertex wiring, `2 d_f`-cleared
(`prop:lap`'s display at the link's row and column ends at the
vertex): the within-factor terms at `c_f`, the counting term at the
mixed pairs against the same-end pairs, the row pairs' transposition
at the places (`lap.swapIdx`) and the column pairs' at the values
(`lap.mapVals`) each at `2 d_f`, and the mixed pairs' contraction
`C_rc` withdrawn — the closed pair at the loop value and the open
pair at the witness transposition. -/
def linkCas (d : Nat) (rs cs : List Nat) (σ : List Nat) : List (List Nat × BPair) :=
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

/-- The insertion's families read the wiring's slot count. -/
private theorem linkCas_widths (d : Nat) (rs cs σ : List Nat) :
    (linkCas d rs cs σ).all (fun t => t.1.length == σ.length) = true := by
  refine ground.all_of_mem_intro _ _ (fun t ht => ?_)
  cases ht with
  | head => exact decide_eq_true rfl
  | tail _ h =>
    cases ground.mem_append_of _ _ h with
    | inl h1 =>
      cases ground.mem_append_of _ _ h1 with
      | inl h2 =>
        obtain ⟨p, _, hp⟩ := ground.mem_map_of _ _ t h2
        rw [← hp]
        exact decide_eq_true (by
          show ((σ.set _ _).set _ _).length = σ.length
          rw [ground.length_set, ground.length_set])
      | inr h2 =>
        obtain ⟨p, _, hp⟩ := ground.mem_map_of _ _ t h2
        rw [← hp]
        exact decide_eq_true (ground.length_map _ σ)
    | inr h1 =>
      obtain ⟨p, _, hp⟩ := ground.mem_map_of _ _ t h1
      rw [← hp]
      by_cases hc : (ground.getAt 0 σ p.1 == p.2) = true
      · rw [if_pos hc]
        exact decide_eq_true rfl
      · rw [if_neg hc]
        exact decide_eq_true (by
          show ((σ.set _ _).set _ _).length = σ.length
          rw [ground.length_set, ground.length_set])

/-- The insertion's extension over a state reads the state's
count. -/
private theorem linkCasC_widths (d : Nat) (rs cs : List Nat) {k : Nat} (v : VComb k) :
    (v.val.flatMap (fun e => (linkCas d rs cs e.1).map (fun t => (t.1, e.2 * t.2)))).all
      (fun p => p.1.length == k) = true := by
  rw [ground.all_flatMap]
  refine ground.all_of_mem_intro _ _ (fun e he => ?_)
  rw [ground.all_map, ← slotpower.width_of_mem v e he]
  exact linkCas_widths d rs cs e.1

/-- The insertion's linear extension over a vertex state, the
families collected once. -/
def linkCasC (d : Nat) (rs cs : List Nat) {k : Nat} (v : VComb k) : VComb k :=
  slotpower.collect k (v.val.flatMap (fun e =>
    (linkCas d rs cs e.1).map (fun t => (t.1, e.2 * t.2))))
    (linkCasC_widths d rs cs v)

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
private def projLink (d : Nat) (rs cs : List Nat) (s : Shape) {k : Nat} (v : VComb k) :
    VComb k :=
  (interpNodes d s).foldl (fun acc n =>
    slotpower.addV (linkCasC d rs cs acc)
      (slotpower.scaleV (BPair.ofNat (c2hat.dfQ (labels.reduce n))).swap acc)) v

/-- The vertex projection: the links' projections composed along the
incident list. -/
def projVertex (d : Nat) (es : List (Shape × Bool)) {k : Nat} (v : VComb k) : VComb k :=
  (List.zipWith (fun e ends => (e, ends)) es (linkEnds d es 0 0)).foldl
    (fun acc p => projLink d p.2.1 p.2.2 p.1.1 acc) v

/-- A vertex state's coefficient row over the place permutations,
each key's coefficient at its permutation's position: the
permutations in the lexicographic order walked once against the
state's display (`ground.mergeWith`, the unit at a permutation the
state lacks). -/
private def rowOf (k : Nat) {w : Nat} (v : VComb w) : List BPair :=
  let ps := (places.perms k).map (fun σ => (σ, ()))
  ground.mergeWith ground.lexLt (fun a b => a == b) (fun a _ => a.map (fun _ => BPair.unit))
    (fun _ _ c r => c :: r) (fun _ r => BPair.unit :: r) (fun _ r => r)
    (ps.length + v.val.length) ps v.val

/-- The collection at a Gram: the members joined one per refusal at
one grade, a member refusing exactly where the collected list's Gram
with it reads a determinant off the sum's unit (`elim.collectK`,
`lem:lowerspan`'s joined-collection read at the Gram's leading
minors). -/
private def collectGram (N : elim.Mat) : List Nat :=
  (elim.collectK (fun _ _ : Unit => true) (fun _ => ())
    (fun a b => ground.getAt BPair.unit (ground.getAt [] N a) b) (List.range N.length)).1.reverse

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
  | vecs (T : memtable.Table) (w : Nat) (l : List (slotpower.SVec w))

/-- The members' slot count: the wirings' signature's, or the
stated list's. -/
def Members.width : Members → Nat
  | .wirings _ sig _ _ => sig.length
  | .vecs _ w _ => w

/-- The members as vectors: the rows' combinations over the
wirings' table, one tensor per place permutation, or the stated
list. -/
def Members.list : (m : Members) → List (slotpower.SVec m.width)
  | .wirings d sig k rows =>
    let table := (places.perms k).map (slotpower.wiringG d sig)
    rows.map (slotpower.comboV table)
  | .vecs _ _ l => l

/-- The members' Gram: the rows against the wirings' cycle-count
Gram, the slot power's coordinate pairing at the cycle counts
(`lem:mixedinv`; `mixedinv.cycleGram`), or the stated list's
pairings at the table's weight. -/
def Members.gram : Members → elim.Mat
  | .wirings d _ k rows =>
    (elim.gramAt (mixedinv.cycleGram d k) rows).map (fun r =>
      r.map BPair.norm)
  | .vecs T _ l => slotpower.gramT T l

/-- The slot power's letter count at the members: the wirings'
stated count, and at a stated list its table's keys. -/
def Members.letters : Members → Nat
  | .wirings d _ _ _ => d
  | .vecs T _ _ => T.keys

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
    rowOf k (projVertex d es (slotpower.monV σ.length σ rfl)))
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
  let ends := slotpower.endBlocks d es
  ⟨endCols d es,
    .vecs T _ (slotpower.kernelVecs T (slotpower.fusedSig ends) (slotpower.fusedSpanT T ends)),
    Pos.one⟩

/-- The Gram-dual coevaluation's weights at an invariant list's
Gram: the adjugate against the determinant
(`lem:dualread`(i)'s display at `def:elim`'s adjugate). -/
def coevW (G : elim.Mat) : elim.Mat × BPair :=
  (elim.adjMD G, elim.detD G)

/-- The Gram-dual coevaluation's weights at a collection's weight
grades (`lem:dualread`(i): the grading splitting the Gram at one
block per occupied content, the cross pairings of equal members, the
adjugate collecting each block's own at the further blocks'
determinants; `def:elim`'s blockwise adjugate at the partition;
`lem:lowerspan`'s collection with its Gram grown a row per join and
its determinant the descent's terminal entry,
`slotpower.blockGroupsT`): per grade its members with the descent
adjugate of its stored Gram at the further grades' stored
determinants (read at every grade at once, `ground.othersAll`), each
entry at the canonical representative, and the
grades' determinants' product, the clearing; `coevG_read` the
identity at the whole Gram's adjugate against its determinant at
the grades' own pairs. -/
def coevG {k : Nat} (gs : List (elim.GroupS (slotpower.SVec k))) :
    List (List (slotpower.SVec k) × elim.Mat) × BPair :=
  let dets := gs.map (fun g => g.det)
  let oth := ground.othersAll (fun a b : BPair => a * b) (BPair.ofNat 1) dets
  ((List.range gs.length).map (fun i =>
    let g := ground.getAt (elim.vacantG _) gs i
    let s := ground.getAt BPair.unit oth i
    (g.mems, (elim.adjMD g.gram).map (fun r => r.map (fun a => (s * a).norm)))),
   (elim.detsProd dets).norm)

/-- A grade's Gram at the weighted pairing is the whole Gram's block
at the grade's places. -/
private theorem gramT_group (T : memtable.Table) {k : Nat} (l : List (slotpower.SVec k))
    (g : List Nat) (hg : ∀ t, t < g.length → ground.getAt 0 g t < l.length) :
    slotpower.gramT T (g.map (ground.getAt (slotpower.emptyV k) l))
      = elim.selM g g (slotpower.gramT T l) := by
  rw [slotpower.gramT_eq, slotpower.gramT_eq]
  have hsl : (g.map (ground.getAt (slotpower.emptyV k) l)).length = g.length :=
    ground.length_map _ g
  refine ground.getAt_ext [] _ _ (by rw [elim.length_gramBy, hsl, elim.length_selM])
    (fun p hp => ?_)
  rw [elim.length_gramBy, hsl] at hp
  refine ground.getAt_ext BPair.unit _ _ (by
    rw [elim.rowsLen_getAt _ p (elim.rowsLen_gramBy _ _) (by rw [elim.length_gramBy, hsl]; exact hp),
      hsl, elim.rowsLen_getAt _ p (elim.rowsLen_selM _ _ _) (by rw [elim.length_selM]; exact hp)])
    (fun q hq => ?_)
  rw [elim.rowsLen_getAt _ p (elim.rowsLen_gramBy _ _) (by rw [elim.length_gramBy, hsl]; exact hp),
    hsl] at hq
  rw [elim.gramBy_entry _ (slotpower.emptyV k) _ p q (by rw [hsl]; exact hp) (by rw [hsl]; exact hq),
    elim.getAt_selM g g _ p q hp hq,
    elim.gramBy_entry _ (slotpower.emptyV k) l _ _ (hg p hp) (hg q hq),
    ground.getAt_map 0 (slotpower.emptyV k) _ g p hp, ground.getAt_map 0 (slotpower.emptyV k) _ g q hq]

/-- The graded weights at a collection's grades are the whole Gram's
adjugate against its determinant (`lem:dualread`(i);
`elim.blockAdj_read` at the weights' places, `slotpower.weightPlaces`):
the grades' members the list at the places, each Gram the members'
own at the weighted pairing, each determinant one value with the
Gram's, every leading minor off the unit (`lem:lowerspan`'s solve at
an independent list, the stored descent's read), and members of
distinct weights pairing at the sum's unit (the grading's
orthogonality at content-homogeneous members, `con:places`): a
grade's weight at two of its places is the adjugate's entry there,
the adjugate reads the unit at two places of distinct weights, and
the clearing is the determinant. -/
theorem coevG_read (T : memtable.Table) (sig : List Bool) {k : Nat}
    (l : List (slotpower.SVec k)) (gs : List (elim.GroupS (slotpower.SVec k)))
    (hlen : gs.length = (slotpower.weightPlaces T sig l).length)
    (hmem : ∀ i, i < (slotpower.weightPlaces T sig l).length →
      (ground.getAt (elim.vacantG _) gs i).mems
        = (ground.getAt [] (slotpower.weightPlaces T sig l) i).map
            (ground.getAt (slotpower.emptyV k) l))
    (hgram : ∀ i, i < (slotpower.weightPlaces T sig l).length →
      (ground.getAt (elim.vacantG _) gs i).gram
        = slotpower.gramT T (ground.getAt (elim.vacantG _) gs i).mems)
    (hdet : ∀ i, i < (slotpower.weightPlaces T sig l).length →
      ((ground.getAt (elim.vacantG _) gs i).det).oneValue
        (elim.detL (ground.getAt (elim.vacantG _) gs i).gram))
    (hlead : ∀ i, i < (slotpower.weightPlaces T sig l).length →
      ∀ t, t < (ground.getAt (elim.vacantG _) gs i).mems.length →
        ¬ (elim.leadMinor (ground.getAt (elim.vacantG _) gs i).gram (t + 1)).oneValue
          BPair.unit)
    (hw : ∀ a, a < l.length → ∀ b, b < l.length →
      ¬ slotpower.weightV T sig (ground.getAt (slotpower.emptyV k) l a)
          = slotpower.weightV T sig (ground.getAt (slotpower.emptyV k) l b) →
      (slotpower.pairT T (slotpower.unitWtRead T) (ground.getAt (slotpower.emptyV k) l a)
        (ground.getAt (slotpower.emptyV k) l b)).oneValue BPair.unit) :
    (∀ i, i < (slotpower.weightPlaces T sig l).length →
      ∀ p, p < (ground.getAt [] (slotpower.weightPlaces T sig l) i).length →
      ∀ q, q < (ground.getAt [] (slotpower.weightPlaces T sig l) i).length →
        (ground.getAt BPair.unit
          (ground.getAt [] (ground.getAt ([], []) (coevG gs).1 i).2 p) q).oneValue
        (ground.getAt BPair.unit
          (ground.getAt [] (elim.adjM (slotpower.gramT T l))
            (ground.getAt 0 (ground.getAt [] (slotpower.weightPlaces T sig l) i) p))
          (ground.getAt 0 (ground.getAt [] (slotpower.weightPlaces T sig l) i) q)))
    ∧ (∀ j, j < l.length → ∀ j', j' < l.length →
        ¬ slotpower.weightV T sig (ground.getAt (slotpower.emptyV k) l j)
          = slotpower.weightV T sig (ground.getAt (slotpower.emptyV k) l j') →
        (ground.getAt BPair.unit (ground.getAt [] (elim.adjM (slotpower.gramT T l)) j) j').oneValue
          BPair.unit)
    ∧ ((coevG gs).2).oneValue (elim.detL (slotpower.gramT T l)) := by
  have hWP : slotpower.weightPlaces T sig l
      = elim.placesBy (fun j => slotpower.weightV T sig (ground.getAt (slotpower.emptyV k) l j))
          l.length := rfl
  have hpart := elim.placesBy_partition
    (fun j => slotpower.weightV T sig (ground.getAt (slotpower.emptyV k) l j)) l.length
  rw [← hWP] at hpart
  have hsq : elim.sqAt (slotpower.gramT T l) l.length := by
    rw [slotpower.gramT_eq]
    exact elim.sqAt_of (elim.length_gramBy _ _) (elim.rowsLen_gramBy _ _)
  have hGi : ∀ i, i < (slotpower.weightPlaces T sig l).length →
      (ground.getAt (elim.vacantG _) gs i).gram
        = elim.selM (ground.getAt [] (slotpower.weightPlaces T sig l) i)
            (ground.getAt [] (slotpower.weightPlaces T sig l) i) (slotpower.gramT T l) :=
    fun i hi => by
      rw [hgram i hi, hmem i hi]
      exact gramT_group T l _ (hpart.2.2.2 i hi)
  have hGsl : ((slotpower.weightPlaces T sig l).map
      (fun g => elim.selM g g (slotpower.gramT T l))).length
      = (slotpower.weightPlaces T sig l).length := ground.length_map _ _
  have hGs : ∀ i, i < (slotpower.weightPlaces T sig l).length →
      ground.getAt [] ((slotpower.weightPlaces T sig l).map
        (fun g => elim.selM g g (slotpower.gramT T l))) i
        = (ground.getAt (elim.vacantG _) gs i).gram :=
    fun i hi => by rw [ground.getAt_map [] [] _ _ i hi, hGi i hi]
  have hgl : ∀ i, i < (slotpower.weightPlaces T sig l).length →
      (ground.getAt (elim.vacantG _) gs i).mems.length
        = (ground.getAt [] (slotpower.weightPlaces T sig l) i).length :=
    fun i hi => by rw [hmem i hi, ground.length_map]
  have hlead' : ∀ i, i < (slotpower.weightPlaces T sig l).length →
      ∀ t, t < (ground.getAt [] (slotpower.weightPlaces T sig l) i).length →
        ¬ (elim.leadMinor (elim.selM (ground.getAt [] (slotpower.weightPlaces T sig l) i)
          (ground.getAt [] (slotpower.weightPlaces T sig l) i) (slotpower.gramT T l))
          (t + 1)).oneValue BPair.unit :=
    fun i hi t ht => by
      rw [← hGi i hi]
      exact hlead i hi t (by rw [hgl i hi]; exact ht)
  have hcross : ∀ j, j < l.length → ∀ j', j' < l.length →
      ¬ elim.groupOf j (slotpower.weightPlaces T sig l)
        = elim.groupOf j' (slotpower.weightPlaces T sig l) →
      (ground.getAt BPair.unit (ground.getAt [] (slotpower.gramT T l) j) j').oneValue
        BPair.unit := fun j hj j' hj' hne => by
    rw [slotpower.gramT_eq, elim.gramBy_entry _ (slotpower.emptyV k) l j j' hj hj']
    exact hw j hj j' hj' (fun he => hne (by
      rw [hWP]
      exact elim.placesBy_groupOf_eq _ l.length j j' hj hj' he))
  have hmain := elim.blockAdj_read l.length (slotpower.gramT T l) hsq
    (slotpower.weightPlaces T sig l) hpart.1 hpart.2.1 hpart.2.2.1 hpart.2.2.2 hcross hlead'
  have hBl : (elim.blockAdj l.length (slotpower.weightPlaces T sig l)
      ((slotpower.weightPlaces T sig l).map
        (fun g => elim.selM g g (slotpower.gramT T l)))).length = l.length :=
    ground.matOf_length _ _ _
  have hdl : (gs.map (fun g => g.det)).length
      = (((slotpower.weightPlaces T sig l).map
          (fun g => elim.selM g g (slotpower.gramT T l))).map elim.detD).length := by
    rw [ground.length_map, ground.length_map, hGsl, hlen]
  have hdv : ∀ j, j < (gs.map (fun g => g.det)).length →
      (ground.getAt BPair.unit (gs.map (fun g => g.det)) j).oneValue
        (ground.getAt BPair.unit
          (((slotpower.weightPlaces T sig l).map
            (fun g => elim.selM g g (slotpower.gramT T l))).map elim.detD) j) :=
    fun j hj => by
      rw [ground.length_map] at hj
      have hj' : j < (slotpower.weightPlaces T sig l).length := by rw [← hlen]; exact hj
      rw [ground.getAt_map (elim.vacantG _) BPair.unit _ gs j hj,
        ground.getAt_map [] BPair.unit elim.detD _ j (by rw [hGsl]; exact hj'), hGs j hj']
      refine BPair.oneValue_trans (hdet j hj') (BPair.oneValue_symm (elim.detD_eq _ ?_))
      rw [hGi j hj', elim.length_selM]
      exact elim.rowsLen_selM _ _ _
  refine ⟨fun i hi p hp q hq => ?_, fun j hj j' hj' hne => ?_, ?_⟩
  · have hi' : i < gs.length := by rw [hlen]; exact hi
    have hGl : (ground.getAt (elim.vacantG _) gs i).gram.length
        = (ground.getAt [] (slotpower.weightPlaces T sig l) i).length := by
      rw [hGi i hi, elim.length_selM]
    have hAl : (elim.adjMD (ground.getAt (elim.vacantG _) gs i).gram).length
        = (ground.getAt [] (slotpower.weightPlaces T sig l) i).length := by
      rw [← hGl]
      exact ground.matOf_length _ _ _
    have hAr : elim.rowsLen (ground.getAt [] (slotpower.weightPlaces T sig l) i).length
        (elim.adjMD (ground.getAt (elim.vacantG _) gs i).gram) := by
      rw [← hGl]
      exact elim.rowsLen_matOf _ _ _
    have hE : ground.getAt BPair.unit
        (ground.getAt [] (ground.getAt ([], []) (coevG gs).1 i).2 p) q
        = (ground.getAt BPair.unit (ground.othersAll (fun a b : BPair => a * b) (BPair.ofNat 1)
               (gs.map (fun g => g.det))) i
            * ground.getAt BPair.unit
                (ground.getAt [] (elim.adjMD (ground.getAt (elim.vacantG _) gs i).gram) p)
                q).norm := by
      show ground.getAt BPair.unit (ground.getAt []
        (ground.getAt ([], []) ((List.range gs.length).map (fun i =>
          ((ground.getAt (elim.vacantG _) gs i).mems,
           (elim.adjMD (ground.getAt (elim.vacantG _) gs i).gram).map (fun r => r.map
             (fun a => (ground.getAt BPair.unit (ground.othersAll (fun a b : BPair => a * b) (BPair.ofNat 1)
               (gs.map (fun g => g.det))) i * a).norm))))) i).2 p) q = _
      rw [ground.getAt_map_range ([], []) _ gs.length i, if_pos hi']
      show ground.getAt BPair.unit (ground.getAt []
        ((elim.adjMD (ground.getAt (elim.vacantG _) gs i).gram).map (fun r => r.map
          (fun a => (ground.getAt BPair.unit (ground.othersAll (fun a b : BPair => a * b) (BPair.ofNat 1)
               (gs.map (fun g => g.det))) i * a).norm))) p) q = _
      rw [ground.getAt_map [] [] _ _ p (by rw [hAl]; exact hp),
        ground.getAt_map BPair.unit BPair.unit _ _ q
          (by rw [elim.rowsLen_getAt _ p hAr (by rw [hAl]; exact hp)]; exact hq)]
    rw [hE]
    have hj : ground.getAt 0 (ground.getAt [] (slotpower.weightPlaces T sig l) i) p < l.length :=
      hpart.2.2.2 i hi p hp
    have hk : ground.getAt 0 (ground.getAt [] (slotpower.weightPlaces T sig l) i) q < l.length :=
      hpart.2.2.2 i hi q hq
    have hgj : elim.groupOf (ground.getAt 0 (ground.getAt [] (slotpower.weightPlaces T sig l) i) p)
        (slotpower.weightPlaces T sig l) = i :=
      hpart.2.1 i hi _ (ground.countOf_getAt_pos 0 _ p hp)
    have hgk : elim.groupOf (ground.getAt 0 (ground.getAt [] (slotpower.weightPlaces T sig l) i) q)
        (slotpower.weightPlaces T sig l) = i :=
      hpart.2.1 i hi _ (ground.countOf_getAt_pos 0 _ q hq)
    have hB := elim.blockAdj_entry l.length (slotpower.weightPlaces T sig l)
      ((slotpower.weightPlaces T sig l).map (fun g => elim.selM g g (slotpower.gramT T l)))
      (ground.getAt 0 (ground.getAt [] (slotpower.weightPlaces T sig l) i) p)
      (ground.getAt 0 (ground.getAt [] (slotpower.weightPlaces T sig l) i) q)
      hj hk (by rw [hgj, hGsl]; exact hi)
    rw [hgj, hgk, if_pos (ground.countOf_getAt_pos 0 _ q hq),
      places.posOf_getAt (hpart.2.2.1 i hi) p hp, places.posOf_getAt (hpart.2.2.1 i hi) q hq,
      hGs i hi] at hB
    refine BPair.oneValue_trans (BPair.norm_oneValue _) ?_
    refine BPair.oneValue_trans ?_
      (elim.matOne_entry hmain.1 _ _ (by rw [hBl]; exact hj))
    rw [hB]
    refine BPair.mul_congr ?_ (BPair.oneValue_refl _)
    refine BPair.oneValue_trans (elim.detsOthers_ov _ i (by rw [ground.length_map, hlen]; exact hi)) ?_
    refine BPair.oneValue_trans (elim.detsOthers_congr _ _ hdl hdv i) ?_
    exact BPair.oneValue_symm (elim.blockDetOthers_ov _ i (by rw [hGsl]; exact hi))
  · have hne' : ¬ elim.groupOf j (slotpower.weightPlaces T sig l)
        = elim.groupOf j' (slotpower.weightPlaces T sig l) := fun he => by
      rw [hWP] at he
      exact hne (elim.placesBy_key_eq _ l.length j j' hj hj' he)
    have hB := elim.blockAdj_entry l.length (slotpower.weightPlaces T sig l)
      ((slotpower.weightPlaces T sig l).map (fun g => elim.selM g g (slotpower.gramT T l))) j j' hj hj'
      (by rw [hGsl]; exact hpart.1 j hj)
    have hz : ¬ 0 < ground.countOf j' (ground.getAt [] (slotpower.weightPlaces T sig l)
        (elim.groupOf j (slotpower.weightPlaces T sig l))) :=
      fun hpos => hne' (hpart.2.1 _ (hpart.1 j hj) j' hpos).symm
    rw [if_neg hz] at hB
    refine BPair.oneValue_trans (BPair.oneValue_symm ?_) (BPair.oneValue_of_eq hB)
    exact elim.matOne_entry hmain.1 j j' (by rw [hBl]; exact hj)
  · refine BPair.oneValue_trans (BPair.norm_oneValue _) ?_
    exact BPair.oneValue_trans (elim.detsProd_congr _ _ hdl hdv) hmain.2

/-- A block's weight grades at a symmetric weight read
`coevG_read`'s data at the block span: the grades' count, each
grade's members the span's at its places, its Gram the members'
own, its determinant and its leading minors off the unit
(`slotpower.blockGroupsT_reads`). -/
private theorem blockReads (T : memtable.Table) (sig : List Bool)
    (top : slotpower.SVec sig.length) (hw : memtable.symmWt T) :
    (slotpower.blockGroupsT T sig top).length
        = (slotpower.weightPlaces T sig (slotpower.blockSpanT T sig top)).length
    ∧ (∀ i, i < (slotpower.weightPlaces T sig (slotpower.blockSpanT T sig top)).length →
        (ground.getAt (elim.vacantG _) (slotpower.blockGroupsT T sig top) i).mems
          = (ground.getAt [] (slotpower.weightPlaces T sig (slotpower.blockSpanT T sig top)) i).map
              (ground.getAt (slotpower.emptyV _) (slotpower.blockSpanT T sig top)))
    ∧ (∀ i, i < (slotpower.weightPlaces T sig (slotpower.blockSpanT T sig top)).length →
        (ground.getAt (elim.vacantG _) (slotpower.blockGroupsT T sig top) i).gram
          = slotpower.gramT T
              (ground.getAt (elim.vacantG _) (slotpower.blockGroupsT T sig top) i).mems)
    ∧ (∀ i, i < (slotpower.weightPlaces T sig (slotpower.blockSpanT T sig top)).length →
        ((ground.getAt (elim.vacantG _) (slotpower.blockGroupsT T sig top) i).det).oneValue
          (elim.detL (ground.getAt (elim.vacantG _) (slotpower.blockGroupsT T sig top) i).gram))
    ∧ (∀ i, i < (slotpower.weightPlaces T sig (slotpower.blockSpanT T sig top)).length →
        ∀ t, t < (ground.getAt (elim.vacantG _) (slotpower.blockGroupsT T sig top) i).mems.length →
          ¬ (elim.leadMinor
              (ground.getAt (elim.vacantG _) (slotpower.blockGroupsT T sig top) i).gram
              (t + 1)).oneValue BPair.unit) := by
  have hpl := slotpower.weightPlaces_length T sig (slotpower.blockSpanT T sig top)
  have hlen : (slotpower.blockGroupsT T sig top).length
      = (slotpower.weightPlaces T sig (slotpower.blockSpanT T sig top)).length := by
    rw [slotpower.blockGroupsT_length T sig top hw, hpl]
  refine ⟨hlen, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [(slotpower.blockGroupsT_reads T sig top hw i (by rw [hlen]; exact hi)).1]
    exact slotpower.weightPlaces_read T sig (slotpower.blockSpanT T sig top) i
      (by rw [← hpl]; exact hi)
  · exact (slotpower.blockGroupsT_reads T sig top hw i (by rw [hlen]; exact hi)).2.1
  · exact (slotpower.blockGroupsT_reads T sig top hw i (by rw [hlen]; exact hi)).2.2.1
  · exact (slotpower.blockGroupsT_reads T sig top hw i (by rw [hlen]; exact hi)).2.2.2

/-- A block's weight grades' coevaluation weights at a symmetric
weight are the block Gram's adjugate against its determinant at the
grades' own pairs, the grades' reads the block's own
(`slotpower.blockGroupsT_reads`), at members of distinct weights
pairing at the sum's unit. -/
theorem coevG_block (T : memtable.Table) (sig : List Bool) (top : slotpower.SVec sig.length)
    (hw : memtable.symmWt T)
    (hw' : ∀ a, a < (slotpower.blockSpanT T sig top).length →
      ∀ b, b < (slotpower.blockSpanT T sig top).length →
      ¬ slotpower.weightV T sig (ground.getAt (slotpower.emptyV _) (slotpower.blockSpanT T sig top) a)
          = slotpower.weightV T sig
              (ground.getAt (slotpower.emptyV _) (slotpower.blockSpanT T sig top) b) →
      (slotpower.pairT T (slotpower.unitWtRead T)
        (ground.getAt (slotpower.emptyV _) (slotpower.blockSpanT T sig top) a)
        (ground.getAt (slotpower.emptyV _) (slotpower.blockSpanT T sig top) b)).oneValue
        BPair.unit) :
    (∀ i, i < (slotpower.weightPlaces T sig (slotpower.blockSpanT T sig top)).length →
      ∀ p, p < (ground.getAt [] (slotpower.weightPlaces T sig (slotpower.blockSpanT T sig top)) i).length →
      ∀ q, q < (ground.getAt [] (slotpower.weightPlaces T sig (slotpower.blockSpanT T sig top)) i).length →
        (ground.getAt BPair.unit (ground.getAt []
          (ground.getAt ([], []) (coevG (slotpower.blockGroupsT T sig top)).1 i).2 p) q).oneValue
        (ground.getAt BPair.unit
          (ground.getAt [] (elim.adjM (slotpower.gramT T (slotpower.blockSpanT T sig top)))
            (ground.getAt 0 (ground.getAt []
              (slotpower.weightPlaces T sig (slotpower.blockSpanT T sig top)) i) p))
          (ground.getAt 0 (ground.getAt []
            (slotpower.weightPlaces T sig (slotpower.blockSpanT T sig top)) i) q)))
    ∧ (∀ j, j < (slotpower.blockSpanT T sig top).length →
        ∀ j', j' < (slotpower.blockSpanT T sig top).length →
        ¬ slotpower.weightV T sig
            (ground.getAt (slotpower.emptyV _) (slotpower.blockSpanT T sig top) j)
          = slotpower.weightV T sig
            (ground.getAt (slotpower.emptyV _) (slotpower.blockSpanT T sig top) j') →
        (ground.getAt BPair.unit (ground.getAt []
          (elim.adjM (slotpower.gramT T (slotpower.blockSpanT T sig top))) j) j').oneValue
          BPair.unit)
    ∧ ((coevG (slotpower.blockGroupsT T sig top)).2).oneValue
        (elim.detL (slotpower.gramT T (slotpower.blockSpanT T sig top))) := by
  have h := blockReads T sig top hw
  exact coevG_read T sig _ _ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 hw'

/-- One member pair's terms at a weight: the pair's tensor at the
weight, and no term at the weight's unit representative. -/
private def pairTerms {k k' : Nat} (u : slotpower.SVec k) (v : slotpower.SVec k') (a : BPair) :
    List (List Nat × BPair) :=
  if a.isUnitRep then [] else (slotpower.tensorV u v).val.map (fun p => (p.1, p.2 * a))

/-- A pair's terms read the two counts' sum. -/
private theorem pairTerms_widths {k k' : Nat} (u : slotpower.SVec k) (v : slotpower.SVec k')
    (a : BPair) : (pairTerms u v a).all (fun p => p.1.length == k + k') = true := by
  show (if a.isUnitRep then [] else (slotpower.tensorV u v).val.map (fun p => (p.1, p.2 * a))).all
    (fun p => p.1.length == k + k') = true
  by_cases hu : a.isUnitRep = true
  · rw [if_pos hu]
    rfl
  · rw [if_neg hu, ground.all_map]
    exact (slotpower.tensorV u v).property.2

/-- A pair's terms fold one value at one key at weights one value:
at a weight at the unit either way the fold is the unit, and off it
the tensor's terms scale at the weights. -/
private theorem pairTerms_fold {k k' : Nat} (m : List Nat) (u : slotpower.SVec k)
    (v : slotpower.SVec k') (a a' : BPair) (h : a.oneValue a') :
    (ground.keyFoldB (fun a b : List Nat => a == b) m (pairTerms u v a)).oneValue
      (ground.keyFoldB (fun a b : List Nat => a == b) m (pairTerms u v a')) := by
  have hnull : ∀ b : BPair, b.oneValue BPair.unit →
      (ground.keyFoldB (fun a b : List Nat => a == b) m (pairTerms u v b)).oneValue BPair.unit :=
    fun b hb => by
      show (ground.keyFoldB (fun a b : List Nat => a == b) m
        (if b.isUnitRep then [] else (slotpower.tensorV u v).val.map (fun p => (p.1, p.2 * b)))).oneValue
        BPair.unit
      by_cases hub : b.isUnitRep = true
      · rw [if_pos hub]
        exact BPair.oneValue_refl _
      · rw [if_neg hub]
        show (ground.famFold BPair.add BPair.unit
          (fun p : List Nat × BPair => if (p.1 == m) then p.2 else BPair.unit)
          ((slotpower.tensorV u v).val.map (fun p => (p.1, p.2 * b)))).oneValue BPair.unit
        rw [ground.famFold_map]
        refine ground.foldB_null _ _ (fun p _ => ?_)
        show (if (p.1 == m) then p.2 * b else BPair.unit).oneValue BPair.unit
        by_cases hp : (p.1 == m) = true
        · rw [if_pos hp]
          exact elim.oneValue_mul_unit p.2 b hb
        · rw [if_neg hp]
          exact BPair.oneValue_refl _
  by_cases hua : a.isUnitRep = true
  · have ha : a.oneValue BPair.unit := BPair.oneValue_of_eq (BPair.unit_of_isUnitRep hua)
    exact BPair.oneValue_trans (hnull a ha)
      (BPair.oneValue_symm (hnull a' (BPair.oneValue_trans (BPair.oneValue_symm h) ha)))
  · by_cases hua' : a'.isUnitRep = true
    · have ha' : a'.oneValue BPair.unit := BPair.oneValue_of_eq (BPair.unit_of_isUnitRep hua')
      exact BPair.oneValue_trans (hnull a (BPair.oneValue_trans h ha'))
        (BPair.oneValue_symm (hnull a' ha'))
    · show (ground.keyFoldB (fun a b : List Nat => a == b) m
        (if a.isUnitRep then [] else (slotpower.tensorV u v).val.map (fun p => (p.1, p.2 * a)))).oneValue
        (ground.keyFoldB (fun a b : List Nat => a == b) m
        (if a'.isUnitRep then [] else (slotpower.tensorV u v).val.map (fun p => (p.1, p.2 * a'))))
      rw [if_neg hua, if_neg hua']
      show (ground.famFold BPair.add BPair.unit
          (fun p : List Nat × BPair => if (p.1 == m) then p.2 else BPair.unit)
          ((slotpower.tensorV u v).val.map (fun p => (p.1, p.2 * a)))).oneValue
        (ground.famFold BPair.add BPair.unit
          (fun p : List Nat × BPair => if (p.1 == m) then p.2 else BPair.unit)
          ((slotpower.tensorV u v).val.map (fun p => (p.1, p.2 * a'))))
      rw [ground.famFold_map, ground.famFold_map]
      refine ground.foldB_congr_members _ _ _ (fun p _ => ?_)
      show (if (p.1 == m) then p.2 * a else BPair.unit).oneValue
        (if (p.1 == m) then p.2 * a' else BPair.unit)
      by_cases hp : (p.1 == m) = true
      · rw [if_pos hp, if_pos hp]
        exact BPair.mul_congr (BPair.oneValue_refl _) h
      · rw [if_neg hp, if_neg hp]
        exact BPair.oneValue_refl _

/-- The weighted member pairs' tensors over grouped lists at stated
weights per grade, one term per occupied monomial of each pair's
tensor at the pair's weight, the unit-representative weights
withdrawn. -/
private def coevTerms {k k' : Nat}
    (gs : List (List (slotpower.SVec k) × List (slotpower.SVec k') × elim.Mat)) :
    List (List Nat × BPair) :=
  gs.flatMap (fun g => (List.range g.1.length).flatMap (fun j =>
    (List.range g.2.1.length).flatMap (fun i =>
      pairTerms (ground.getAt (slotpower.emptyV k) g.1 j) (ground.getAt (slotpower.emptyV k') g.2.1 i)
        (ground.getAt BPair.unit (ground.getAt [] g.2.2 j) i))))

/-- The weighted pairs' tensors over grouped lists read the two
counts' sum. -/
private theorem coevTerms_widths {k k' : Nat}
    (gs : List (List (slotpower.SVec k) × List (slotpower.SVec k') × elim.Mat)) :
    (coevTerms gs).all (fun p => p.1.length == k + k') = true := by
  show (gs.flatMap (fun g => (List.range g.1.length).flatMap (fun j =>
    (List.range g.2.1.length).flatMap (fun i =>
      pairTerms (ground.getAt (slotpower.emptyV k) g.1 j) (ground.getAt (slotpower.emptyV k') g.2.1 i)
        (ground.getAt BPair.unit (ground.getAt [] g.2.2 j) i))))).all
    (fun p => p.1.length == k + k') = true
  rw [ground.all_flatMap]
  refine ground.all_of_pointwise _ _ (fun g => ?_)
  rw [ground.all_flatMap]
  refine ground.all_of_pointwise _ _ (fun j => ?_)
  rw [ground.all_flatMap]
  exact ground.all_of_pointwise _ _ (fun i => pairTerms_widths _ _ _)

/-- The coevaluation's tensor over grouped lists at stated weights
per grade, `Σ_{jk} A_{jk} y_j ⊗ y'_k` over the grades' own pairs
(`lem:dualread`(i)'s display at the adjugate collecting each block's
own), the weighted member pairs' tensors collected. -/
private def coevAt2 {k k' : Nat}
    (gs : List (List (slotpower.SVec k) × List (slotpower.SVec k') × elim.Mat)) :
    slotpower.SVec (k + k') :=
  slotpower.collect (k + k') (coevTerms gs) (coevTerms_widths gs)

/-- The display's terms over every pair of two lists at a stated
weight matrix. -/
private def displayTerms {k k' : Nat} (l : List (slotpower.SVec k))
    (l' : List (slotpower.SVec k')) (A : elim.Mat) : List (List Nat × BPair) :=
  (List.range l.length).flatMap (fun j => (List.range l'.length).flatMap (fun i =>
    pairTerms (ground.getAt (slotpower.emptyV k) l j) (ground.getAt (slotpower.emptyV k') l' i)
      (ground.getAt BPair.unit (ground.getAt [] A j) i)))

/-- The display's terms read the two counts' sum. -/
private theorem displayTerms_widths {k k' : Nat} (l : List (slotpower.SVec k))
    (l' : List (slotpower.SVec k')) (A : elim.Mat) :
    (displayTerms l l' A).all (fun p => p.1.length == k + k') = true := by
  show ((List.range l.length).flatMap (fun j => (List.range l'.length).flatMap (fun i =>
    pairTerms (ground.getAt (slotpower.emptyV k) l j) (ground.getAt (slotpower.emptyV k') l' i)
      (ground.getAt BPair.unit (ground.getAt [] A j) i)))).all
    (fun p => p.1.length == k + k') = true
  rw [ground.all_flatMap]
  refine ground.all_of_pointwise _ _ (fun j => ?_)
  rw [ground.all_flatMap]
  exact ground.all_of_pointwise _ _ (fun i => pairTerms_widths _ _ _)

/-- The Gram-dual coevaluation's display over two lists at a stated
weight matrix, `Σ_{jk} A_{jk} y_j ⊗ y'_k` over every member pair
(`lem:dualread`(i)), the weighted pairs' tensors collected;
`coevOf_display` and `coevThrough_display` read the grades' own
pairs as the display at the Gram's adjugate. -/
def coevDisplay {k k' : Nat} (l : List (slotpower.SVec k)) (l' : List (slotpower.SVec k'))
    (A : elim.Mat) : slotpower.SVec (k + k') :=
  slotpower.collect (k + k') (displayTerms l l' A) (displayTerms_widths l l' A)

/-- A key's fold at the display's terms is the double fold over the
pairs. -/
private theorem displayTerms_fold {k k' : Nat} (m : List Nat) (l : List (slotpower.SVec k))
    (l' : List (slotpower.SVec k')) (A : elim.Mat) :
    (ground.keyFoldB (fun a b : List Nat => a == b) m (displayTerms l l' A)).oneValue
      (ground.bsum (fun j => ground.bsum (fun i =>
        ground.keyFoldB (fun a b : List Nat => a == b) m
          (pairTerms (ground.getAt (slotpower.emptyV k) l j)
            (ground.getAt (slotpower.emptyV k') l' i)
            (ground.getAt BPair.unit (ground.getAt [] A j) i))) (List.range l'.length))
        (List.range l.length)) := by
  refine BPair.oneValue_trans (ground.famFold_flatMap_ov ground.bpairFoldLaws _ _ _) ?_
  refine ground.foldB_congr_members _ _ _ (fun j _ => ?_)
  exact ground.famFold_flatMap_ov ground.bpairFoldLaws _ _ _

/-- A key's fold at the grades' terms is the triple fold over the
grades and their pairs. -/
private theorem coevTerms_fold {k k' : Nat} (m : List Nat)
    (gs : List (List (slotpower.SVec k) × List (slotpower.SVec k') × elim.Mat)) :
    (ground.keyFoldB (fun a b : List Nat => a == b) m (coevTerms gs)).oneValue
      (ground.bsum (fun t => ground.bsum (fun p => ground.bsum (fun q =>
        ground.keyFoldB (fun a b : List Nat => a == b) m
          (pairTerms (ground.getAt (slotpower.emptyV k) (ground.getAt ([], [], []) gs t).1 p)
            (ground.getAt (slotpower.emptyV k') (ground.getAt ([], [], []) gs t).2.1 q)
            (ground.getAt BPair.unit (ground.getAt [] (ground.getAt ([], [], []) gs t).2.2 p) q)))
          (List.range (ground.getAt ([], [], []) gs t).2.1.length))
        (List.range (ground.getAt ([], [], []) gs t).1.length)) (List.range gs.length)) := by
  refine BPair.oneValue_trans (ground.famFold_flatMap_ov ground.bpairFoldLaws _ _ gs) ?_
  have hmap := ground.famFold_map BPair.add BPair.unit
    (fun g : List (slotpower.SVec k) × List (slotpower.SVec k') × elim.Mat =>
      ground.famFold BPair.add BPair.unit
        (fun p : List Nat × BPair => if (p.1 == m) then p.2 else BPair.unit)
        ((List.range g.1.length).flatMap (fun j => (List.range g.2.1.length).flatMap (fun i =>
          pairTerms (ground.getAt (slotpower.emptyV k) g.1 j)
            (ground.getAt (slotpower.emptyV k') g.2.1 i)
            (ground.getAt BPair.unit (ground.getAt [] g.2.2 j) i)))))
    (ground.getAt ([], [], []) gs) (List.range gs.length)
  rw [ground.range_map_getAt ([], [], []) gs.length gs rfl] at hmap
  show (ground.famFold BPair.add BPair.unit
      (fun g : List (slotpower.SVec k) × List (slotpower.SVec k') × elim.Mat =>
        ground.famFold BPair.add BPair.unit
          (fun p : List Nat × BPair => if (p.1 == m) then p.2 else BPair.unit)
          ((List.range g.1.length).flatMap (fun j => (List.range g.2.1.length).flatMap (fun i =>
            pairTerms (ground.getAt (slotpower.emptyV k) g.1 j)
              (ground.getAt (slotpower.emptyV k') g.2.1 i)
              (ground.getAt BPair.unit (ground.getAt [] g.2.2 j) i))))) gs).oneValue _
  rw [hmap]
  refine ground.foldB_congr_members _ _ _ (fun t _ => ?_)
  refine BPair.oneValue_trans (ground.famFold_flatMap_ov ground.bpairFoldLaws _ _ _) ?_
  refine ground.foldB_congr_members _ _ _ (fun p _ => ?_)
  exact ground.famFold_flatMap_ov ground.bpairFoldLaws _ _ _

/-- The grades' own pairs collect to the display over every pair
(`lem:dualread`(i): the cross pairings of equal members, the
adjugate collecting each block's own): at index grades partitioning
the two lists' places, the grades' lists the lists at the places,
each grade's weights one value with the matrix's at the places and
the matrix's entries at the unit across grades, the two collected
tensors are one display. -/
private theorem coevAt2_display {k k' : Nat} (l : List (slotpower.SVec k))
    (l' : List (slotpower.SVec k')) (hl : l'.length = l.length) (A : elim.Mat)
    (groups : List (List Nat))
    (hgrp : ∀ j, j < l.length → elim.groupOf j groups < groups.length)
    (hdis : ∀ i, i < groups.length → ∀ j, 0 < ground.countOf j (ground.getAt [] groups i) →
      elim.groupOf j groups = i)
    (hdist : ∀ i, i < groups.length → ∀ x, ground.countOf x (ground.getAt [] groups i) ≤ 1)
    (hbelow : ∀ i, i < groups.length → ∀ t, t < (ground.getAt [] groups i).length →
      ground.getAt 0 (ground.getAt [] groups i) t < l.length)
    (gs : List (List (slotpower.SVec k) × List (slotpower.SVec k') × elim.Mat))
    (hlen : gs.length = groups.length)
    (hmem : ∀ i, i < groups.length →
      (ground.getAt ([], [], []) gs i).1
        = (ground.getAt [] groups i).map (ground.getAt (slotpower.emptyV k) l))
    (hmem' : ∀ i, i < groups.length →
      (ground.getAt ([], [], []) gs i).2.1
        = (ground.getAt [] groups i).map (ground.getAt (slotpower.emptyV k') l'))
    (hW : ∀ i, i < groups.length →
      ∀ p, p < (ground.getAt [] groups i).length →
      ∀ q, q < (ground.getAt [] groups i).length →
        (ground.getAt BPair.unit (ground.getAt [] (ground.getAt ([], [], []) gs i).2.2 p) q).oneValue
          (ground.getAt BPair.unit (ground.getAt [] A (ground.getAt 0 (ground.getAt [] groups i) p))
            (ground.getAt 0 (ground.getAt [] groups i) q)))
    (hcross : ∀ j, j < l.length → ∀ j', j' < l.length →
      ¬ elim.groupOf j groups = elim.groupOf j' groups →
      (ground.getAt BPair.unit (ground.getAt [] A j) j').oneValue BPair.unit) :
    coevAt2 gs = coevDisplay l l' A := by
  refine Subtype.ext ?_
  show ground.collectBy ground.lexLt (fun a b => a == b) (coevTerms gs)
    = ground.collectBy ground.lexLt (fun a b => a == b) (displayTerms l l' A)
  refine ground.sorted_unique ground.lexLt (fun a b => a == b) ground.lexLt_trans
    (fun _ _ h => ground.listBeqEq h) ground.lexLt_irrefl ground.listEqBeq _ _
    (ground.collectBy_sorted _ _ ground.lexLt_trans (fun _ _ h => ground.listBeqEq h)
      ground.lexLt_tri _)
    (ground.collectBy_sorted _ _ ground.lexLt_trans (fun _ _ h => ground.listBeqEq h)
      ground.lexLt_tri _)
    (fun p hp => ground.mem_normFilter _ p hp)
    (fun p hp => ground.mem_normFilter _ p hp) (fun m => ?_)
  refine BPair.oneValue_trans (ground.keyFoldB_collectBy _ _ (fun _ _ h => ground.listBeqEq h) m _)
    (BPair.oneValue_trans ?_
      (BPair.oneValue_symm
        (ground.keyFoldB_collectBy _ _ (fun _ _ h => ground.listBeqEq h) m _)))
  refine BPair.oneValue_trans (coevTerms_fold m gs) ?_
  refine BPair.oneValue_trans ?_ (BPair.oneValue_symm (displayTerms_fold m l l' A))
  rw [hl]
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans (elim.bsum_pairs_group
    (fun j i => ground.keyFoldB (fun a b : List Nat => a == b) m
      (pairTerms (ground.getAt (slotpower.emptyV k) l j) (ground.getAt (slotpower.emptyV k') l' i)
        (ground.getAt BPair.unit (ground.getAt [] A j) i)))
    l.length groups hgrp hdis hdist hbelow (fun j hj i hi hne => ?_)) ?_
  · refine BPair.oneValue_trans (pairTerms_fold m _ _ _ BPair.unit (hcross j hj i hi hne)) ?_
    exact BPair.oneValue_refl _
  · rw [← hlen]
    refine ground.bsum_congr_range_ov _ _ gs.length (fun t ht => ?_)
    have ht' : t < groups.length := by rw [← hlen]; exact ht
    have hl1 : (ground.getAt ([], [], []) gs t).1.length = (ground.getAt [] groups t).length := by
      rw [hmem t ht', ground.length_map]
    have hl2 : (ground.getAt ([], [], []) gs t).2.1.length = (ground.getAt [] groups t).length := by
      rw [hmem' t ht', ground.length_map]
    rw [hl1, hl2]
    refine ground.bsum_congr_range_ov _ _ _ (fun p hp => ?_)
    refine ground.bsum_congr_range_ov _ _ _ (fun q hq => ?_)
    rw [hmem t ht', hmem' t ht', ground.getAt_map 0 (slotpower.emptyV k) _ _ p hp,
      ground.getAt_map 0 (slotpower.emptyV k') _ _ q hq]
    exact BPair.oneValue_symm (pairTerms_fold m _ _ _ _ (hW t ht' p hp q hq))

/-- The Gram-dual coevaluation of a collection at the weighted
pairing (`lem:dualread`(i)): the tensor `Σ_{jk} A_{jk} y_j ⊗ y_k`
over the weight grades' own pairs at the Gram's adjugate graded at
the grades (`coevG`), with the determinant its clearing, read at the
occupied monomials; `coevOf_display` its read as the display over
every pair at the Gram's adjugate. -/
def coevOf {k : Nat} (gs : List (elim.GroupS (slotpower.SVec k))) :
    slotpower.SVec (k + k) × BPair :=
  let cw := coevG gs
  (coevAt2 (cw.1.map (fun g => (g.1, g.1, g.2))), cw.2)

/-- The Gram-dual coevaluation of a collection read through the
identification at its second factor (`con:fiber`'s two-end vertex;
`lem:dualread`(i)'s display): `Σ_{jk} A_{jk} y_j ⊗ ι(y_k)` over the
weight grades' own pairs at the Gram's adjugate graded at the grades
(`coevG`), `ι` the identification along a slot map with its tie
groups at the letters and its reversed groups at a member
(`slotpower.identifyV`), the clearing the determinant's margin
against the identification's (`slotpower.identifyClear`), the pair
at its primitive representative, the coefficients' shared count
withdrawn with the clearing (`slotpower.reduceV`, `thm:windowsep`'s
strip); `coevThrough_display` its read as the display over every
pair. -/
def coevThrough (d : Nat) (T : memtable.Table) {k : Nat}
    (gs : List (elim.GroupS (slotpower.SVec k)))
    (σ : List Nat) (ties : List (List Nat)) (revs : List (List Nat × Bool)) :
    slotpower.SVec (k + σ.length) × Pos :=
  let cw := coevG gs
  slotpower.reduceV
    (coevAt2 (cw.1.map (fun g => (g.1, g.1.map (slotpower.identifyV d T σ ties revs), g.2))),
     ground.posOfSucc (BPair.marginN cw.2 - 1) * slotpower.identifyClear T ties revs Pos.one)

/-- The grades' weights against a second list read the display at
the whole Gram's adjugate: at `coevG_read`'s data, the grades' pairs
at the two lists collect to `lem:dualread`(i)'s display over every
pair at the cofactor family. -/
private theorem coevG_display (T : memtable.Table) (sig : List Bool) {k k' : Nat}
    (l : List (slotpower.SVec k)) (f : slotpower.SVec k → slotpower.SVec k')
    (gs : List (elim.GroupS (slotpower.SVec k)))
    (hlen : gs.length = (slotpower.weightPlaces T sig l).length)
    (hmem : ∀ i, i < (slotpower.weightPlaces T sig l).length →
      (ground.getAt (elim.vacantG _) gs i).mems
        = (ground.getAt [] (slotpower.weightPlaces T sig l) i).map
            (ground.getAt (slotpower.emptyV k) l))
    (hgram : ∀ i, i < (slotpower.weightPlaces T sig l).length →
      (ground.getAt (elim.vacantG _) gs i).gram
        = slotpower.gramT T (ground.getAt (elim.vacantG _) gs i).mems)
    (hdet : ∀ i, i < (slotpower.weightPlaces T sig l).length →
      ((ground.getAt (elim.vacantG _) gs i).det).oneValue
        (elim.detL (ground.getAt (elim.vacantG _) gs i).gram))
    (hlead : ∀ i, i < (slotpower.weightPlaces T sig l).length →
      ∀ t, t < (ground.getAt (elim.vacantG _) gs i).mems.length →
        ¬ (elim.leadMinor (ground.getAt (elim.vacantG _) gs i).gram (t + 1)).oneValue
          BPair.unit)
    (hw : ∀ a, a < l.length → ∀ b, b < l.length →
      ¬ slotpower.weightV T sig (ground.getAt (slotpower.emptyV k) l a)
          = slotpower.weightV T sig (ground.getAt (slotpower.emptyV k) l b) →
      (slotpower.pairT T (slotpower.unitWtRead T) (ground.getAt (slotpower.emptyV k) l a)
        (ground.getAt (slotpower.emptyV k) l b)).oneValue BPair.unit) :
    coevAt2 ((coevG gs).1.map (fun g => (g.1, g.1.map f, g.2)))
      = coevDisplay l (l.map f) (elim.adjM (slotpower.gramT T l)) := by
  have hr := coevG_read T sig l gs hlen hmem hgram hdet hlead hw
  have hWP : slotpower.weightPlaces T sig l
      = elim.placesBy (fun j => slotpower.weightV T sig (ground.getAt (slotpower.emptyV k) l j))
          l.length := rfl
  have hpart := elim.placesBy_partition
    (fun j => slotpower.weightV T sig (ground.getAt (slotpower.emptyV k) l j)) l.length
  rw [← hWP] at hpart
  have hcl : ((coevG gs).1.map (fun g => (g.1, g.1.map f, g.2))).length
      = (slotpower.weightPlaces T sig l).length := by
    rw [ground.length_map]
    show ((List.range gs.length).map _).length = _
    rw [ground.length_mapRange, hlen]
  have hcg : ∀ i, i < (slotpower.weightPlaces T sig l).length →
      ground.getAt ([], [], []) ((coevG gs).1.map (fun g => (g.1, g.1.map f, g.2))) i
        = ((ground.getAt (elim.vacantG _) gs i).mems,
           (ground.getAt (elim.vacantG _) gs i).mems.map f,
           (ground.getAt ([], []) (coevG gs).1 i).2) := fun i hi => by
    have hi' : i < gs.length := by rw [hlen]; exact hi
    have h1 : (ground.getAt ([], []) (coevG gs).1 i).1
        = (ground.getAt (elim.vacantG _) gs i).mems := by
      show (ground.getAt ([], []) ((List.range gs.length).map (fun i =>
          ((ground.getAt (elim.vacantG _) gs i).mems,
           (elim.adjMD (ground.getAt (elim.vacantG _) gs i).gram).map (fun r => r.map
             (fun a => (ground.getAt BPair.unit (ground.othersAll (fun a b : BPair => a * b) (BPair.ofNat 1)
               (gs.map (fun g => g.det))) i * a).norm))))) i).1
        = (ground.getAt (elim.vacantG _) gs i).mems
      rw [ground.getAt_map_range ([], []) _ gs.length i, if_pos hi']
    rw [ground.getAt_map ([], []) ([], [], []) _ _ i (by
      show i < ((List.range gs.length).map _).length
      rw [ground.length_mapRange]; exact hi')]
    show ((ground.getAt ([], []) (coevG gs).1 i).1,
      (ground.getAt ([], []) (coevG gs).1 i).1.map f,
      (ground.getAt ([], []) (coevG gs).1 i).2) = _
    rw [h1]
  refine coevAt2_display l (l.map f) (ground.length_map f l) (elim.adjM (slotpower.gramT T l))
    (slotpower.weightPlaces T sig l) hpart.1 hpart.2.1 hpart.2.2.1 hpart.2.2.2 _ hcl
    (fun i hi => ?_) (fun i hi => ?_) (fun i hi p hp q hq => ?_)
    (fun j hj j' hj' hne => hr.2.1 j hj j' hj' (fun he => hne (by
      rw [hWP]
      exact elim.placesBy_groupOf_eq _ l.length j j' hj hj' he)))
  · rw [hcg i hi]
    exact hmem i hi
  · rw [hcg i hi]
    show (ground.getAt (elim.vacantG _) gs i).mems.map f = _
    rw [hmem i hi, ground.map_map]
    refine ground.map_congr_members _ _ _ (fun j hj => ?_)
    have hjl := hpart.2.2.2 i hi _ (places.posOf_lt j _ hj)
    rw [places.getAt_posOf j _ hj] at hjl
    show f (ground.getAt (slotpower.emptyV k) l j) = ground.getAt (slotpower.emptyV k') (l.map f) j
    rw [ground.getAt_map (slotpower.emptyV k) (slotpower.emptyV k') f l j hjl]
  · rw [hcg i hi]
    exact hr.1 i hi p hp q hq

/-- The coevaluation tensor of a collection is `lem:dualread`(i)'s
display over every pair of the list at the Gram's adjugate, with
the clearing the determinant: at `coevG_read`'s data the weight
grades' own pairs collect to the display, the cross entries at the
sum's unit. -/
theorem coevOf_display (T : memtable.Table) (sig : List Bool) {k : Nat}
    (l : List (slotpower.SVec k)) (gs : List (elim.GroupS (slotpower.SVec k)))
    (hlen : gs.length = (slotpower.weightPlaces T sig l).length)
    (hmem : ∀ i, i < (slotpower.weightPlaces T sig l).length →
      (ground.getAt (elim.vacantG _) gs i).mems
        = (ground.getAt [] (slotpower.weightPlaces T sig l) i).map
            (ground.getAt (slotpower.emptyV k) l))
    (hgram : ∀ i, i < (slotpower.weightPlaces T sig l).length →
      (ground.getAt (elim.vacantG _) gs i).gram
        = slotpower.gramT T (ground.getAt (elim.vacantG _) gs i).mems)
    (hdet : ∀ i, i < (slotpower.weightPlaces T sig l).length →
      ((ground.getAt (elim.vacantG _) gs i).det).oneValue
        (elim.detL (ground.getAt (elim.vacantG _) gs i).gram))
    (hlead : ∀ i, i < (slotpower.weightPlaces T sig l).length →
      ∀ t, t < (ground.getAt (elim.vacantG _) gs i).mems.length →
        ¬ (elim.leadMinor (ground.getAt (elim.vacantG _) gs i).gram (t + 1)).oneValue
          BPair.unit)
    (hw : ∀ a, a < l.length → ∀ b, b < l.length →
      ¬ slotpower.weightV T sig (ground.getAt (slotpower.emptyV k) l a)
          = slotpower.weightV T sig (ground.getAt (slotpower.emptyV k) l b) →
      (slotpower.pairT T (slotpower.unitWtRead T) (ground.getAt (slotpower.emptyV k) l a)
        (ground.getAt (slotpower.emptyV k) l b)).oneValue BPair.unit) :
    (coevOf gs).1 = coevDisplay l l (elim.adjM (slotpower.gramT T l))
    ∧ ((coevOf gs).2).oneValue (elim.detL (slotpower.gramT T l)) := by
  refine ⟨?_, (coevG_read T sig l gs hlen hmem hgram hdet hlead hw).2.2⟩
  have h := coevG_display T sig l (fun x => x) gs hlen hmem hgram hdet hlead hw
  rw [ground.map_id l] at h
  show coevAt2 ((coevG gs).1.map (fun g => (g.1, g.1, g.2))) = _
  rw [← h]
  refine congrArg coevAt2 (ground.map_congr_all _ _ (fun g => ?_) _)
  show (g.1, g.1, g.2) = (g.1, g.1.map (fun x => x), g.2)
  rw [ground.map_id]

/-- The coevaluation through the identification is the display over
every pair of the list against its identified image at the Gram's
adjugate, reduced with the clearing: at `coevG_read`'s data the
weight grades' own pairs collect to the display. -/
theorem coevThrough_display (d : Nat) (T : memtable.Table) (sig : List Bool) {k : Nat}
    (l : List (slotpower.SVec k)) (gs : List (elim.GroupS (slotpower.SVec k)))
    (σ : List Nat) (ties : List (List Nat)) (revs : List (List Nat × Bool))
    (hlen : gs.length = (slotpower.weightPlaces T sig l).length)
    (hmem : ∀ i, i < (slotpower.weightPlaces T sig l).length →
      (ground.getAt (elim.vacantG _) gs i).mems
        = (ground.getAt [] (slotpower.weightPlaces T sig l) i).map
            (ground.getAt (slotpower.emptyV k) l))
    (hgram : ∀ i, i < (slotpower.weightPlaces T sig l).length →
      (ground.getAt (elim.vacantG _) gs i).gram
        = slotpower.gramT T (ground.getAt (elim.vacantG _) gs i).mems)
    (hdet : ∀ i, i < (slotpower.weightPlaces T sig l).length →
      ((ground.getAt (elim.vacantG _) gs i).det).oneValue
        (elim.detL (ground.getAt (elim.vacantG _) gs i).gram))
    (hlead : ∀ i, i < (slotpower.weightPlaces T sig l).length →
      ∀ t, t < (ground.getAt (elim.vacantG _) gs i).mems.length →
        ¬ (elim.leadMinor (ground.getAt (elim.vacantG _) gs i).gram (t + 1)).oneValue
          BPair.unit)
    (hw : ∀ a, a < l.length → ∀ b, b < l.length →
      ¬ slotpower.weightV T sig (ground.getAt (slotpower.emptyV k) l a)
          = slotpower.weightV T sig (ground.getAt (slotpower.emptyV k) l b) →
      (slotpower.pairT T (slotpower.unitWtRead T) (ground.getAt (slotpower.emptyV k) l a)
        (ground.getAt (slotpower.emptyV k) l b)).oneValue BPair.unit) :
    coevThrough d T gs σ ties revs
      = slotpower.reduceV
          (coevDisplay l (l.map (slotpower.identifyV d T σ ties revs))
            (elim.adjM (slotpower.gramT T l)),
           ground.posOfSucc (BPair.marginN (coevG gs).2 - 1)
             * slotpower.identifyClear T ties revs Pos.one) := by
  show slotpower.reduceV
    (coevAt2 ((coevG gs).1.map (fun g =>
      (g.1, g.1.map (slotpower.identifyV d T σ ties revs), g.2))), _) = _
  rw [coevG_display T sig l (slotpower.identifyV d T σ ties revs) gs hlen hmem hgram hdet hlead hw]

/-- A block's coevaluation tensor at a symmetric weight is the
display over every pair of the block span at the span's Gram's
adjugate, the clearing the determinant (`coevOf_display` at the
block's own grades, `blockReads`). -/
theorem coevOf_block (T : memtable.Table) (sig : List Bool) (top : slotpower.SVec sig.length)
    (hw : memtable.symmWt T)
    (hw' : ∀ a, a < (slotpower.blockSpanT T sig top).length →
      ∀ b, b < (slotpower.blockSpanT T sig top).length →
      ¬ slotpower.weightV T sig (ground.getAt (slotpower.emptyV _) (slotpower.blockSpanT T sig top) a)
          = slotpower.weightV T sig
              (ground.getAt (slotpower.emptyV _) (slotpower.blockSpanT T sig top) b) →
      (slotpower.pairT T (slotpower.unitWtRead T)
        (ground.getAt (slotpower.emptyV _) (slotpower.blockSpanT T sig top) a)
        (ground.getAt (slotpower.emptyV _) (slotpower.blockSpanT T sig top) b)).oneValue
        BPair.unit) :
    (coevOf (slotpower.blockGroupsT T sig top)).1
      = coevDisplay (slotpower.blockSpanT T sig top) (slotpower.blockSpanT T sig top)
          (elim.adjM (slotpower.gramT T (slotpower.blockSpanT T sig top)))
    ∧ ((coevOf (slotpower.blockGroupsT T sig top)).2).oneValue
        (elim.detL (slotpower.gramT T (slotpower.blockSpanT T sig top))) :=
  have h := blockReads T sig top hw
  coevOf_display T sig _ _ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 hw'


/-- The vertex list of two ends at the letters: the block's
Gram-dual coevaluation at the first end's block's weight grades
(`coevThrough` at `slotpower.blockGroupsAt`),
the second factor at the exchanged actions at opposite
orientations, one label, and read through the identification at
one orientation, the labels dual, the columns matched to the
complement lengths with the star at the tie columns
(`slotpower.transportSlots` at the two layouts); vacant off the
pair or at a column left unmatched. -/
def twoEndList (d : Nat) (e1 e2 : Shape × Bool) : VList :=
  let T := memtable.lettersT d
  let rev := e1.2 == e2.2
  let ok := if rev then labels.reduce e2.1 == labels.reduce (labels.dualL e1.1)
    else labels.reduce e2.1 == labels.reduce e1.1
  let n1 := (slotpower.labelSig d e1.1).length
  let n2 := (slotpower.labelSig d e2.1).length
  let sm := slotpower.transportSlots (fun l => d - l) rev
    (slotpower.colLayout d e1.1 0) (slotpower.colLayout d e2.1 0)
  if ok && sm.1.length == n2 && n1 == n2 then
    let cv := coevThrough d T (slotpower.blockGroupsAt d e1.1) sm.1 sm.2 []
    ⟨endCols d [e1, e2], .vecs T _ [cv.1], cv.2⟩
  else ⟨endCols d [e1, e2], .vecs T (n1 + n2) [], Pos.one⟩

/-- The vertex list at the label calculus: an untouched vertex the
scalar one, one end the vacant list, two ends the coevaluation,
then the symbolic tag's collected wirings where the row-end count
is at or below the fundamental count with the column count matched
and every incident label at a valid interpolant, and the direct
tag's kernel list otherwise. -/
def vertListA (d : Nat) (es : List (Shape × Bool)) : VList :=
  match es with
  | [] => ⟨[], .vecs (memtable.lettersT d) 0 [slotpower.unitV], Pos.one⟩
  | [e] => ⟨endCols d [e], .vecs (memtable.lettersT d) (slotpower.endSig d e).length [], Pos.one⟩
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
def linkList (d : Nat) (sig : List Bool) : List (slotpower.SVec sig.length) × elim.Mat :=
  let ku := (slotpower.upSlots sig).length
  let kd := (slotpower.downSlots sig).length
  if ku == kd && ku ≤ d then
    ((places.perms ku).map (slotpower.wiringG d sig), mixedinv.cycleGram d ku)
  else
    let T := memtable.lettersT d
    let pool := slotpower.monsV sig.length
      ((places.allMon d sig.length).filter (slotpower.unitWeight d sig))
      (ground.all_of_mem_intro _ _ (fun m hm =>
        ground.all_of_mem _ _ (places.allMon_widths d sig.length) m
          (ground.mem_filter_of _ _ m hm).1))
    let mems := slotpower.kernelVecs T sig pool
    (mems, slotpower.gramT T mems)

/-! The presentation field (`con:fusion`'s presentation; `con:fiber`
at the member's generating table, `con:memtable`). -/

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
  linkList : L × Option Bool × L → slotpower.WList × elim.Mat
  bdryWord : Nat × Nat
  bdry : slotpower.WVec × BPair
  lessUnit : Bool
  colDual : Nat → Nat

/-- The letters' presentation at a fundamental count: the vertex
lists `vertListA`, the link lists at the symbolic and direct tags,
the boundary factor the mixed power's monomials at `(1,1)`, its
coevaluation the identity's, the wiring, and a column's dual its
complement length. -/
def presA (d : Nat) : Pres Shape :=
  ⟨memtable.lettersT d, fun es => some (vertListA d es),
   fun t =>
     let ll := linkList d (linkSig (slotpower.wordPair d t.1) t.2.1
       (slotpower.wordPair d t.2.2) (1, 1))
     (⟨_, ll.1⟩, ll.2),
   (1, 1),
   (let cv := coevOf (slotpower.listGroupsT (memtable.lettersT d) (slotpower.wordSig (1, 1))
      (slotpower.monsV 2 (places.allMon d 2) (places.allMon_widths d 2)))
    (⟨_, cv.1⟩, cv.2)),
   true,
   fun l => d - l⟩

/-- The vacant presentation, the interface's read at a datum
without one. -/
def presNone (L : Type) : Pres L :=
  ⟨memtable.lettersT 0, fun _ => none, fun _ => (⟨0, []⟩, []), (0, 0),
   (⟨0, slotpower.emptyV 0⟩, BPair.ofNat 1), true, fun l => l⟩

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
    (acc : List (Option slotpower.WVec)) (i : Nat) :
    Option slotpower.WVec :=
  match ground.getAt none acc i with
  | some t => some t
  | none =>
    match ground.getAt none reach i with
    | none =>
      let pool := (List.range T.keys).filterMap (fun k =>
        if weightIs (memtable.keyWeight T k) (unitAt T.rank i)
        then some (slotpower.monV 1 [k] rfl) else none)
      match slotpower.kernelT T [false] pool with
      | [k] => some ⟨1, slotpower.prim (slotpower.comboV pool k)⟩
      | [] => none
      | _ :: _ :: _ => none
    | some (j, k) =>
      match ground.getAt none acc j, ground.getAt none acc k with
      | some ⟨dj, tj⟩, some ⟨dk, tk⟩ =>
        let sig := List.replicate (dj + dk) false
        let Wj := slotpower.blockSpanW T dj false tj
        let Wk := slotpower.blockSpanW T dk false tk
        let pool := Wj.flatMap (fun u => Wk.filterMap (fun v =>
          let t := slotpower.tensorV u v
          if weightIs (slotpower.weightV T sig t) (unitAt T.rank i) then some t
          else none))
        match slotpower.kernelT T sig
            (pool.map (slotpower.castV (ground.length_replicate false (dj + dk)).symm)) with
        | [kv] => some ⟨dj + dk, slotpower.prim (slotpower.comboV pool kv)⟩
        | [] => none
        | _ :: _ :: _ => none
      | none, _ => none
      | some _, none => none

/-- The fundamentals' tops at a table and a reach list, each with
its degree: the reach read's entries filled one round per
fundamental, an entry filled once its stated product's entries
are, vacant where the uniqueness read refuses. -/
def fundTops (T : memtable.Table) (reach : List (Option (Nat × Nat))) :
    List (Option slotpower.WVec) :=
  (List.range T.rank).foldl (fun acc _ =>
    (List.range T.rank).map (reachStep T reach acc))
    (List.replicate T.rank none)

/-- A label's factors at the fundamentals' tops: per fundamental its
index with its degree, once per unit of the label's fold, in the
index order. -/
def factorsOf (tops : List (Option slotpower.WVec)) (l : List Nat) :
    List (Nat × Nat) :=
  (List.range l.length).flatMap (fun i =>
    match ground.getAt none tops i with
    | some t => List.replicate (ground.getAt 0 l i) (i, t.1)
    | none => [])

/-- A label's degree at the fundamentals' tops, its factors'
degrees' sum. -/
def degOf (tops : List (Option slotpower.WVec)) (l : List Nat) : Nat :=
  ground.sumNat ((factorsOf tops l).map Prod.snd)

/-- A label's top at the fundamentals' tops: the tops' tensor in the
index order at the label's fold, the Cartan product, vacant where
a needed top is. -/
def topOf (tops : List (Option slotpower.WVec)) (l : List Nat) :
    Option slotpower.WVec :=
  (List.range l.length).foldl (fun acc i =>
    match acc, ground.getAt none tops i with
    | some v, some t =>
      some ((List.range (ground.getAt 0 l i)).foldl
        (fun (a : slotpower.WVec) _ => ⟨a.1 + t.1, slotpower.tensorV a.2 t.2⟩) v)
    | some v, none => if ground.getAt 0 l i == 0 then some v else none
    | none, _ => none) (some ⟨0, slotpower.unitV⟩)

/-- The tensor top is present and keeps any property of the
fundamental tops preserved by tensoring and held at the scalar one. -/
theorem topOf_all (P : slotpower.WVec → Prop)
    (hunit : P ⟨0, slotpower.unitV⟩)
    (hmul : ∀ a b, P a → P b → P ⟨a.1 + b.1, slotpower.tensorV a.2 b.2⟩)
    (tops : List (Option slotpower.WVec)) (l : List Nat)
    (ht : ∀ i, i < l.length → ∃ v, ground.getAt none tops i = some v ∧ P v) :
    ∃ v, topOf tops l = some v ∧ P v := by
  unfold topOf
  apply ground.foldl_invariant
    (fun a : Option slotpower.WVec => ∃ v, a = some v ∧ P v)
  · exact ⟨⟨0, slotpower.unitV⟩, rfl, hunit⟩
  · intro i hi acc ha
    obtain ⟨a, ha, hak⟩ := ha
    obtain ⟨t, hit, htk⟩ := ht i (ground.ltOfMemRange hi)
    rw [ha, hit]
    refine ⟨_, rfl, ?_⟩
    apply ground.foldl_invariant P
    · exact hak
    · intro _ _ v hv
      exact hmul v t hv htk

/-- At present fundamental tops, a label's tensor top is present
and uses the fundamentals' finite key list. -/
theorem topOf_total (n : Nat) (tops : List (Option slotpower.WVec)) (l : List Nat)
    (ht : ∀ i, i < l.length → ∃ v, ground.getAt none tops i = some v ∧ slotpower.keysRead n v.2) :
    ∃ v, topOf tops l = some v ∧ slotpower.keysRead n v.2 :=
  topOf_all (fun v => slotpower.keysRead n v.2) (by rfl)
    (fun a b ha hb => slotpower.keysRead_tensorV n a.2 b.2 ha hb) tops l ht

/-- Occupied fundamental tops produce an occupied tensor top
at every label whose required fundamentals are present. -/
theorem topOf_occupied (tops : List (Option slotpower.WVec)) (l : List Nat)
    (ht : ∀ i, i < l.length → ∃ v, ground.getAt none tops i = some v ∧ v.2.val ≠ []) :
    ∃ v, topOf tops l = some v ∧ v.2.val ≠ [] :=
  topOf_all (fun v => v.2.val ≠ []) (by decide +kernel)
    (fun a b ha hb => slotpower.tensorV_occupied a.2 b.2 ha hb) tops l ht

/-- The optional top fold, when present, reads the degrees of
exactly its listed factors. -/
private theorem topFold_degree (tops : List (Option slotpower.WVec)) (l : List Nat) :
    ∀ (is : List Nat) (v t : slotpower.WVec),
    is.foldl (fun acc i =>
      match acc, ground.getAt none tops i with
      | some a, some b => some ((List.range (ground.getAt 0 l i)).foldl
          (fun (a : slotpower.WVec) _ => ⟨a.1 + b.1, slotpower.tensorV a.2 b.2⟩) a)
      | some a, none => if ground.getAt 0 l i == 0 then some a else none
      | none, _ => none) (some v) = some t →
    t.1 = v.1 + ground.sumNat ((is.flatMap (fun i =>
      match ground.getAt none tops i with
      | some b => List.replicate (ground.getAt 0 l i) (i, b.1)
      | none => [])).map Prod.snd)
  | [], v, t, h => by
    have he : v = t := Option.some.inj h
    rw [← he]
    exact (Nat.add_zero v.1).symm
  | i :: is, v, t, h => by
    cases hb : ground.getAt none tops i with
    | none =>
      change is.foldl _ (match some v, ground.getAt none tops i with
        | some a, some b => some ((List.range (ground.getAt 0 l i)).foldl
            (fun (a : slotpower.WVec) _ => ⟨a.1 + b.1, slotpower.tensorV a.2 b.2⟩) a)
        | some a, none => if ground.getAt 0 l i == 0 then some a else none
        | none, _ => none) = some t at h
      rw [hb] at h
      change is.foldl _ (if ground.getAt 0 l i == 0 then some v else none) = some t at h
      by_cases hz : (ground.getAt 0 l i == 0) = true
      · rw [if_pos hz] at h
        have ht := topFold_degree tops l is v t h
        change t.1 = v.1 + ground.sumNat
          (((match ground.getAt none tops i with
            | some b => List.replicate (ground.getAt 0 l i) (i, b.1)
            | none => []) ++ _).map Prod.snd)
        rw [hb]
        exact ht
      · rw [if_neg hz] at h
        have hn : ∀ js : List Nat,
            js.foldl (fun acc j =>
              match acc, ground.getAt none tops j with
              | some a, some b => some ((List.range (ground.getAt 0 l j)).foldl
                  (fun (a : slotpower.WVec) _ => ⟨a.1 + b.1, slotpower.tensorV a.2 b.2⟩) a)
              | some a, none => if ground.getAt 0 l j == 0 then some a else none
              | none, _ => none) none = none := by
          intro js
          induction js with
          | nil => rfl
          | cons j js ih => exact ih
        rw [hn] at h
        exact nomatch (show (none : Option slotpower.WVec) = some t from h)
    | some b =>
      change is.foldl _ (match some v, ground.getAt none tops i with
        | some a, some b => some ((List.range (ground.getAt 0 l i)).foldl
            (fun (a : slotpower.WVec) _ => ⟨a.1 + b.1, slotpower.tensorV a.2 b.2⟩) a)
        | some a, none => if ground.getAt 0 l i == 0 then some a else none
        | none, _ => none) = some t at h
      rw [hb] at h
      have ht := topFold_degree tops l is _ t h
      have hdeg := slotpower.foldW_width
        ((List.range (ground.getAt 0 l i)).map (fun _ => b)) v
      rw [ground.foldl_map, ground.map_map, ground.map_const,
        ground.sumNat_replicate, ground.length_range] at hdeg
      rw [hdeg] at ht
      change t.1 = v.1 + ground.sumNat
        (((match ground.getAt none tops i with
          | some b => List.replicate (ground.getAt 0 l i) (i, b.1)
          | none => []) ++ _).map Prod.snd)
      rw [hb, ground.map_append, ground.sumNat_append, ground.map_replicate,
        ground.sumNat_replicate]
      exact ht.trans (Nat.add_assoc _ _ _)

/-- A present tensor top has exactly the degree read from its
fundamental factors, so the block constructor's degree test holds. -/
theorem topOf_degree (tops : List (Option slotpower.WVec)) (l : List Nat)
    (t : slotpower.WVec) (ht : topOf tops l = some t) : t.1 = degOf tops l := by
  have h := topFold_degree tops l (List.range l.length) ⟨0, slotpower.unitV⟩ t ht
  exact h.trans (Nat.zero_add _)

/-- G2's two fundamental tops, at the keys and at the first
fundamental's square, are present in the eight-key carrier. -/
theorem fundTops_G2_keys :
    ((fundTops memtable.genG2 [none, some (0, 0)]).all (fun v =>
      match v with
      | none => false
      | some t => decide (slotpower.keysRead memtable.genG2.keys t.2))) = true
      ∧ (fundTops memtable.genG2 [none, some (0, 0)]).length = 2 := by
  decide +kernel

/-- G2's fundamental tops are occupied vectors at their
fundamental weights, annihilated by every simple raising. -/
theorem fundTops_G2_top :
    (List.range 2).all (fun i =>
      match ground.getAt none (fundTops memtable.genG2 [none, some (0, 0)]) i with
      | none => false
      | some t => decide (t.2.val ≠ [])
        && decide (slotpower.homogRead memtable.genG2 (List.replicate t.1 false) t.2
          ((ground.unitAt 2 i).map ground.BPair.ofNat))
        && slotpower.raisedUnit memtable.genG2 (List.replicate t.1 false)
          (slotpower.castV (ground.length_replicate false t.1).symm t.2)) = true := by
  decide +kernel

/-- The two stored fundamental tops at their carrier,
occupancy and weight reads. -/
private theorem fundTop_G2 (i : Nat) (hi : i < 2) :
    ∃ t, ground.getAt none (fundTops memtable.genG2 [none, some (0, 0)]) i = some t
      ∧ slotpower.keysRead memtable.genG2.keys t.2 ∧ t.2.val ≠ []
      ∧ slotpower.homogRead memtable.genG2 (List.replicate t.1 false) t.2
        ((ground.unitAt 2 i).map ground.BPair.ofNat) := by
  have hit : i < (fundTops memtable.genG2 [none, some (0, 0)]).length := by
    rw [fundTops_G2_keys.2]; exact hi
  have hk := ground.all_of_mem _ _ fundTops_G2_keys.1 _ (ground.mem_getAt none _ i hit)
  have ht := ground.all_of_mem _ (List.range 2) fundTops_G2_top i (ground.memRange hi)
  cases he : ground.getAt none (fundTops memtable.genG2 [none, some (0, 0)]) i with
  | none => rw [he] at ht; exact Bool.noConfusion ht
  | some t =>
    rw [he] at hk ht
    have hh := ground.andSplitB (ground.andSplitB ht).1
    exact ⟨t, rfl, of_decide_eq_true hk, of_decide_eq_true hh.1, of_decide_eq_true hh.2⟩

/-- Every G2 label of the member's width has its constructed
tensor top in the actual generating carrier. -/
theorem topOf_total_G2 (a : List Nat) (ha : a.length = 2) :
    ∃ v, topOf (fundTops memtable.genG2 [none, some (0, 0)]) a = some v
      ∧ slotpower.keysRead memtable.genG2.keys v.2 := by
  apply topOf_total
  intro i hi
  obtain ⟨t, ht, hk, _, _⟩ := fundTop_G2 i (by rw [← ha]; exact hi)
  exact ⟨t, ht, hk⟩

/-- Every G2 label's actual tensor top is occupied. -/
theorem topOf_occupied_G2 (a : List Nat) (ha : a.length = 2) :
    ∃ v, topOf (fundTops memtable.genG2 [none, some (0, 0)]) a = some v ∧ v.2.val ≠ [] := by
  apply topOf_occupied
  intro i hi
  obtain ⟨t, ht, _, ho, _⟩ := fundTop_G2 i (by rw [← ha]; exact hi)
  exact ⟨t, ht, ho⟩

/-- Every G2 label's actual tensor top is annihilated by every
simple raising at its standard slot signature. -/
theorem topOf_raisedUnit_G2 (a : List Nat) (ha : a.length = 2) :
    ∃ v, topOf (fundTops memtable.genG2 [none, some (0, 0)]) a = some v
      ∧ slotpower.raisedUnit memtable.genG2 (List.replicate v.1 false)
        (slotpower.castV (ground.length_replicate false v.1).symm v.2) = true := by
  apply topOf_all (fun v => slotpower.raisedUnit memtable.genG2 (List.replicate v.1 false)
    (slotpower.castV (ground.length_replicate false v.1).symm v.2) = true)
  · exact slotpower.raisedUnit_unitV memtable.genG2
  · intro u v hu hv
    exact slotpower.raisedUnit_tensor_standard memtable.genG2 u.2 v.2 hu hv
  · intro i hi
    have h := ground.all_range_read 2 fundTops_G2_top i (by rw [← ha]; exact hi)
    cases he : ground.getAt none (fundTops memtable.genG2 [none, some (0, 0)]) i with
    | none => rw [he] at h; exact Bool.noConfusion h
    | some v =>
      rw [he] at h
      exact ⟨v, rfl, (ground.andSplitB h).2⟩

/-- Repeated copies of a natural-weight top add its two
coroots once per copy, at the actual tensor fold. -/
private theorem tensorCopies_G2 (t : slotpower.WVec) (c d : Nat)
    (htk : slotpower.keysRead memtable.genG2.keys t.2)
    (htw : slotpower.homogRead memtable.genG2 (List.replicate t.1 false) t.2
      [ground.BPair.ofNat c, ground.BPair.ofNat d]) :
    ∀ (n : Nat) (v : slotpower.WVec) (a b : Nat),
    slotpower.keysRead memtable.genG2.keys v.2 →
    slotpower.homogRead memtable.genG2 (List.replicate v.1 false) v.2
      [ground.BPair.ofNat a, ground.BPair.ofNat b] →
    let w := (List.range n).foldl (fun (u : slotpower.WVec) _ =>
      ⟨u.1 + t.1, slotpower.tensorV u.2 t.2⟩) v
    slotpower.keysRead memtable.genG2.keys w.2 ∧
      slotpower.homogRead memtable.genG2 (List.replicate w.1 false) w.2
        [ground.BPair.ofNat (a + n * c), ground.BPair.ofNat (b + n * d)]
  | 0, v, a, b, hk, hw => by
    change slotpower.keysRead memtable.genG2.keys v.2 ∧
      slotpower.homogRead memtable.genG2 (List.replicate v.1 false) v.2
        [ground.BPair.ofNat (a + 0 * c), ground.BPair.ofNat (b + 0 * d)]
    rw [Nat.zero_mul, Nat.zero_mul, Nat.add_zero, Nat.add_zero]
    exact ⟨hk, hw⟩
  | n + 1, v, a, b, hk, hw => by
    let w := (List.range n).foldl (fun (u : slotpower.WVec) _ =>
      ⟨u.1 + t.1, slotpower.tensorV u.2 t.2⟩) v
    have ih := tensorCopies_G2 t c d htk htw n v a b hk hw
    change slotpower.keysRead memtable.genG2.keys w.2 ∧
      slotpower.homogRead memtable.genG2 (List.replicate w.1 false) w.2
        [ground.BPair.ofNat (a + n * c), ground.BPair.ofNat (b + n * d)] at ih
    rw [ground.range_succ, ground.foldl_append]
    change slotpower.keysRead memtable.genG2.keys (slotpower.tensorV w.2 t.2) ∧
      slotpower.homogRead memtable.genG2 (List.replicate (w.1 + t.1) false)
        (slotpower.tensorV w.2 t.2)
        [ground.BPair.ofNat (a + (n + 1) * c), ground.BPair.ofNat (b + (n + 1) * d)]
    refine ⟨slotpower.keysRead_tensorV _ w.2 t.2 ih.1 htk, ?_⟩
    have hadd := poly.pnorm_congr
      (elim.vecAdd ([a + n * c, b + n * d].map ground.BPair.ofNat) ([c, d].map ground.BPair.ofNat))
      ((List.zipWith Nat.add [a + n * c, b + n * d] [c, d]).map ground.BPair.ofNat)
      rfl (elim.vecAdd_ofNat [a + n * c, b + n * d] [c, d])
    change poly.pnorm (elim.vecAdd [ground.BPair.ofNat (a + n * c), ground.BPair.ofNat (b + n * d)]
      [ground.BPair.ofNat c, ground.BPair.ofNat d])
      = [(ground.BPair.ofNat (a + n * c + c)).norm, (ground.BPair.ofNat (b + n * d + d)).norm] at hadd
    rw [ground.BPair.norm_ofNat, ground.BPair.norm_ofNat] at hadd
    have h := slotpower.homogRead_tensorV memtable.genG2 (List.replicate w.1 false)
      (List.replicate t.1 false) w.2 t.2 _ _
      (ground.length_replicate _ _).symm (ground.length_replicate _ _).symm
      memtable.genG2_diagonals.1 memtable.genG2_diagonals.2 ih.1 htk ih.2 htw
    rw [hadd, ← ground.replicate_append] at h
    rw [Nat.succ_mul, Nat.succ_mul, ← Nat.add_assoc, ← Nat.add_assoc]
    exact h

/-- The G2 tensor top at its two natural coroot coordinates. -/
private theorem topOf_pair_weight_G2 (a b : Nat) :
    ∃ t, topOf (fundTops memtable.genG2 [none, some (0, 0)]) [a, b] = some t
      ∧ slotpower.keysRead memtable.genG2.keys t.2
      ∧ slotpower.homogRead memtable.genG2 (List.replicate t.1 false) t.2
        [ground.BPair.ofNat a, ground.BPair.ofNat b] := by
  obtain ⟨u, hu, huk, _, huw⟩ := fundTop_G2 0 (by decide +kernel)
  obtain ⟨v, hv, hvk, _, hvw⟩ := fundTop_G2 1 (by decide +kernel)
  let x := (List.range a).foldl (fun (t : slotpower.WVec) _ =>
    ⟨t.1 + u.1, slotpower.tensorV t.2 u.2⟩) ⟨0, slotpower.unitV⟩
  let y := (List.range b).foldl (fun (t : slotpower.WVec) _ =>
    ⟨t.1 + v.1, slotpower.tensorV t.2 v.2⟩) x
  have hx := tensorCopies_G2 u 1 0 huk huw a ⟨0, slotpower.unitV⟩ 0 0 (by rfl) (by rfl)
  change slotpower.keysRead memtable.genG2.keys x.2 ∧
    slotpower.homogRead memtable.genG2 (List.replicate x.1 false) x.2
      [ground.BPair.ofNat (0 + a * 1), ground.BPair.ofNat (0 + a * 0)] at hx
  rw [Nat.mul_one, Nat.mul_zero, Nat.zero_add] at hx
  have hy := tensorCopies_G2 v 0 1 hvk hvw b x a 0 hx.1 hx.2
  change slotpower.keysRead memtable.genG2.keys y.2 ∧
    slotpower.homogRead memtable.genG2 (List.replicate y.1 false) y.2
      [ground.BPair.ofNat (a + b * 0), ground.BPair.ofNat (0 + b * 1)] at hy
  rw [Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add] at hy
  refine ⟨y, ?_, hy.1, hy.2⟩
  unfold topOf
  change (match (match some (⟨0, slotpower.unitV⟩ : slotpower.WVec),
      ground.getAt none (fundTops memtable.genG2 [none, some (0, 0)]) 0 with
    | some t, some q => some ((List.range a).foldl
        (fun (t : slotpower.WVec) _ => ⟨t.1 + q.1, slotpower.tensorV t.2 q.2⟩) t)
    | some t, none => if a == 0 then some t else none
    | none, _ => none), ground.getAt none (fundTops memtable.genG2 [none, some (0, 0)]) 1 with
    | some t, some q => some ((List.range b).foldl
        (fun (t : slotpower.WVec) _ => ⟨t.1 + q.1, slotpower.tensorV t.2 q.2⟩) t)
    | some t, none => if b == 0 then some t else none
    | none, _ => none) = some y
  rw [hu, hv]

/-- Every G2 label's constructed top is homogeneous at that
label's natural coroot list. -/
theorem topOf_weight_G2 (a : List Nat) (ha : a.length = 2) :
    ∃ t, topOf (fundTops memtable.genG2 [none, some (0, 0)]) a = some t
      ∧ slotpower.keysRead memtable.genG2.keys t.2
      ∧ slotpower.homogRead memtable.genG2 (List.replicate t.1 false) t.2
        (a.map ground.BPair.ofNat) := by
  cases a with
  | nil => exact Nat.noConfusion ha
  | cons x xs =>
    cases xs with
    | nil => exact Nat.noConfusion (Nat.succ.inj ha)
    | cons y ys =>
      have hy : ys = [] := ground.nil_of_length_zero ys (Nat.succ.inj (Nat.succ.inj ha))
      rw [hy]
      exact topOf_pair_weight_G2 x y

/-- A label's block at a table: the lowering span at its top in the
power at its degree, vacant where the top is or sits off that
power. -/
def blockAt (T : memtable.Table) (tops : List (Option slotpower.WVec))
    (l : List Nat) : List (slotpower.SVec (degOf tops l)) :=
  match topOf tops l with
  | none => []
  | some t =>
    if h : t.1 = degOf tops l then
      (slotpower.blockSpanW T t.1 false t.2).map (slotpower.castV h)
    else []

/-- At a present tensor top the block is its actual lowering
span, with the degree read transported through its equality. -/
theorem blockAt_top (T : memtable.Table) (tops : List (Option slotpower.WVec))
    (l : List Nat) (t : slotpower.WVec) (ht : topOf tops l = some t) :
    blockAt T tops l = (slotpower.blockSpanW T t.1 false t.2).map
      (slotpower.castV (topOf_degree tops l t ht)) := by
  unfold blockAt
  rw [ht]
  change (if h : t.1 = degOf tops l then
    (slotpower.blockSpanW T t.1 false t.2).map (slotpower.castV h) else []) = _
  rw [dif_pos (topOf_degree tops l t ht)]

/-- A present G2 label top computes its actual block at every
further lowering fuel, with the degree's original transport. -/
theorem blockAt_fuel_G2 (tops : List (Option slotpower.WVec)) (a : List Nat)
    (t : slotpower.WVec) (ht : topOf tops a = some t) (extra : Nat) :
    blockAt memtable.genG2 tops a =
      ((slotpower.closeT memtable.genG2 (List.replicate t.1 false)
        ((List.replicate t.1 false).length * memtable.genG2.keys + 1 + extra)
        (slotpower.tryAddT memtable.genG2 (List.replicate t.1 false) []
          (slotpower.castV (ground.length_replicate false t.1).symm t.2))
        [slotpower.castV (ground.length_replicate false t.1).symm t.2]).map
        (slotpower.castV (ground.length_replicate false t.1))).map
          (slotpower.castV (topOf_degree tops a t ht)) := by
  rw [blockAt_top memtable.genG2 tops a t ht]
  unfold slotpower.blockSpanW
  rw [slotpower.blockSpanT_fuel_G2 _ _ extra
    (ground.all_of_mem_intro _ _ (fun b hb => by
      rw [ground.mem_replicate_eq false t.1 b hb]
      rfl))]

/-- The constructed top of every G2 label belongs to its
actual block, transported at the computed degree equality. -/
theorem blockAt_top_mem_G2 (a : List Nat) (ha : a.length = 2) (t : slotpower.WVec)
    (ht : topOf (fundTops memtable.genG2 [none, some (0, 0)]) a = some t) :
    slotpower.castV (topOf_degree _ a t ht) t.2
      ∈ blockAt memtable.genG2 (fundTops memtable.genG2 [none, some (0, 0)]) a := by
  obtain ⟨u, hu, ho⟩ := topOf_occupied_G2 a ha
  have hut : u = t := Option.some.inj (hu.symm.trans ht)
  rw [hut] at ho
  rw [blockAt_top memtable.genG2 _ a t ht]
  exact ground.mem_map_to _ (slotpower.blockSpanW_top_G2 t.1 false t.2 ho)

/-- The block's members stay in the generating key list at
its top and maps' carrier reads. -/
theorem blockAt_keys (T : memtable.Table) (tops : List (Option slotpower.WVec))
    (l : List Nat) (hw : memtable.symmWt T)
    (ht : ∀ i, i < l.length → ∃ v, ground.getAt none tops i = some v ∧ slotpower.keysRead T.keys v.2)
    (hu : ∀ i, i < T.rank → (ground.getAt [] T.raises i).all (fun e => decide (e.1 < T.keys)) = true)
    (hd : ∀ i, i < T.rank → (ground.getAt [] T.lowers i).all (fun e => decide (e.1 < T.keys)) = true) :
    ∀ v ∈ blockAt T tops l, slotpower.keysRead T.keys v := by
  obtain ⟨t, ht, hk⟩ := topOf_total T.keys tops l ht
  rw [blockAt_top T tops l t ht]
  intro v hv
  obtain ⟨w, hw', he⟩ := ground.mem_map_of _ _ v hv
  rw [← he]
  exact slotpower.blockSpanW_keys T t.1 false t.2 hw hk hu hd w hw'

/-- Every actual G2 label block uses the table's eight keys,
at every natural coroot label of width two. -/
theorem blockAt_keys_G2 (a : List Nat) (ha : a.length = 2) :
    ∀ v ∈ blockAt memtable.genG2 (fundTops memtable.genG2 [none, some (0, 0)]) a,
      slotpower.keysRead memtable.genG2.keys v := by
  obtain ⟨t, ht, hk⟩ := topOf_total_G2 a ha
  rw [blockAt_top _ _ a t ht]
  intro v hv
  obtain ⟨w, hw, he⟩ := ground.mem_map_of _ _ v hv
  rw [← he]
  exact slotpower.blockSpanW_keys memtable.genG2 t.1 false t.2 memtable.genG2_symmWt hk
    (fun i hi => (memtable.genG2_actionKeys i hi).1)
    (fun i hi => (memtable.genG2_actionKeys i hi).2) w hw

/-- Every actual G2 label block is independent in its finite
monomial coordinates, at the constructed tensor top. -/
theorem blockAt_indep_G2 (a : List Nat) (ha : a.length = 2) :
    let tops := fundTops memtable.genG2 [none, some (0, 0)]
    let ms := places.allMon memtable.genG2.keys (degOf tops a)
    elim.indepRows ms.length ((blockAt memtable.genG2 tops a).map (slotpower.coordsV ms)) := by
  let tops := fundTops memtable.genG2 [none, some (0, 0)]
  obtain ⟨t, ht, hk, hg⟩ := topOf_weight_G2 a ha
  obtain ⟨u, hu, ho⟩ := topOf_occupied_G2 a ha
  have hut : u = t := Option.some.inj (hu.symm.trans ht)
  rw [hut] at ho
  let sig := List.replicate t.1 false
  let v := slotpower.castV (ground.length_replicate false t.1).symm t.2
  have hs : sig.all (fun b => !b) = true :=
    ground.all_of_mem_intro _ _ (fun b hb => by
      rw [ground.mem_replicate_eq false t.1 b hb]
      rfl)
  have hh : slotpower.homogRead memtable.genG2 sig v (slotpower.weightV memtable.genG2 sig v) := by
    rw [slotpower.weightV_homog memtable.genG2 sig v _ hg ho]
    exact hg
  have h := slotpower.blockSpanT_indep_G2 sig v hs hk hh
  change elim.indepRows (places.allMon memtable.genG2.keys (degOf tops a)).length
    ((blockAt memtable.genG2 tops a).map
      (slotpower.coordsV (places.allMon memtable.genG2.keys (degOf tops a))))
  rw [blockAt_top memtable.genG2 tops a t ht]
  unfold slotpower.blockSpanW
  rw [ground.map_map, ground.map_map]
  change elim.indepRows (places.allMon memtable.genG2.keys (degOf tops a)).length
    ((slotpower.blockSpanT memtable.genG2 sig v).map
      (slotpower.coordsV (places.allMon memtable.genG2.keys (degOf tops a))))
  have he : places.allMon memtable.genG2.keys (degOf tops a)
      = places.allMon memtable.genG2.keys sig.length :=
    congrArg (places.allMon memtable.genG2.keys)
      ((topOf_degree tops a t ht).symm.trans (ground.length_replicate false t.1).symm)
  rw [he]
  exact h

/-- A block's occupancy family lists the weight of every
collected span member, its content multiplicities the occurrence
counts (`lem:lowerspan`; `lem:memberdata`). -/
def blockWeights (T : memtable.Table) (tops : List (Option slotpower.WVec))
    (a : List Nat) : List (List ground.BPair) :=
  (blockAt T tops a).map (slotpower.weightV T (List.replicate (degOf tops a) false))

/-- The occupancy family's length is the block's collected
dimension. -/
theorem blockWeights_length (T : memtable.Table) (tops : List (Option slotpower.WVec))
    (a : List Nat) : (blockWeights T tops a).length = (blockAt T tops a).length :=
  ground.length_map _ _

/-- Every actual G2 block-family member is a canonical
two-coroot list, at every label of the member's width. -/
theorem blockWeights_shape_G2 (a : List Nat) (ha : a.length = 2) :
    ∀ w ∈ blockWeights memtable.genG2 (fundTops memtable.genG2 [none, some (0, 0)]) a,
      w.length = 2 ∧ poly.pnorm w = w := by
  intro w hw
  obtain ⟨v, hv, he⟩ := ground.mem_map_of _ _ w hw
  rw [← he]
  have hk := blockAt_keys_G2 a ha v hv
  exact ⟨slotpower.weightV_length memtable.genG2 _ v (ground.length_replicate _ _).symm
      memtable.genG2_diagonals.1 memtable.genG2_diagonals.2 hk,
    slotpower.weightV_pnorm memtable.genG2 _ v (ground.length_replicate _ _).symm
      memtable.genG2_diagonals.1 memtable.genG2_diagonals.2 hk⟩

/-- Every label occurs in its actual G2 block family's top
content, at the occupied tensor top in the lowering span. -/
theorem blockWeights_top_G2 (a : List Nat) (ha : a.length = 2) :
    a.map ground.BPair.ofNat
      ∈ blockWeights memtable.genG2 (fundTops memtable.genG2 [none, some (0, 0)]) a := by
  let tops := fundTops memtable.genG2 [none, some (0, 0)]
  obtain ⟨t, ht, _, hw⟩ := topOf_weight_G2 a ha
  obtain ⟨u, hu, ho⟩ := topOf_occupied_G2 a ha
  have hut : u = t := Option.some.inj (hu.symm.trans ht)
  rw [hut] at ho
  have hmem := ground.mem_map_to
    (slotpower.weightV memtable.genG2 (List.replicate (degOf tops a) false))
    (blockAt_top_mem_G2 a ha t ht)
  have he : slotpower.weightV memtable.genG2 (List.replicate (degOf tops a) false)
      (slotpower.castV (topOf_degree tops a t ht) t.2) = a.map ground.BPair.ofNat := by
    change slotpower.weightV memtable.genG2 (List.replicate (degOf tops a) false) t.2 = _
    rw [← topOf_degree tops a t ht]
    exact slotpower.weightV_homog memtable.genG2 _ t.2 _ hw ho
  rw [he] at hmem
  exact hmem

/-- The actual G2 block family's collected dimension is
positive at every label of the member's width. -/
theorem blockWeights_pos_G2 (a : List Nat) (ha : a.length = 2) :
    0 < (blockWeights memtable.genG2 (fundTops memtable.genG2 [none, some (0, 0)]) a).length :=
  Nat.lt_of_lt_of_le (ground.countOf_pos_of_mem (blockWeights_top_G2 a ha))
    (ground.countOf_le_length _ _)

/-- A label's block's weight grades at a table: the lowering span's
collection at its top in the power at its degree
(`slotpower.blockGroupsW`), vacant where the top is or sits off that
power. -/
def groupsAt (T : memtable.Table) (tops : List (Option slotpower.WVec))
    (l : List Nat) : List (elim.GroupS (slotpower.SVec (degOf tops l))) :=
  match topOf tops l with
  | none => []
  | some t =>
    if h : t.1 = degOf tops l then
      (slotpower.blockGroupsW T t.1 false t.2).map
        (fun g => ⟨g.mems.map (slotpower.castV h), g.gram, g.st, g.det⟩)
    else []

/-- The dual coherence read at a label (`con:memtable`): the dual
pair carries the label's block, slot by slot at `c W`, into its
dual label's block's span, the factors matched by fundamental
index to the dual fundamental and the member read through the
identification along the match (`slotpower.transportSlots`,
`slotpower.identifyV`; `slotpower.spanMemberT`); false at a table
without a dual pair or at factors off the match. -/
def dualCoherent (T : memtable.Table) (tops : List (Option slotpower.WVec))
    (dualF : Nat → Nat) (l : List Nat) : Bool :=
  match T.dual with
  | none => false
  | some _ =>
    let deg := degOf tops l
    let dl := (List.range l.length).map (fun i => ground.getAt 0 l (dualF i))
    let sm := slotpower.transportSlots dualF true
      (slotpower.layoutOf 0 (factorsOf tops l, []) 0)
      (slotpower.layoutOf 0 (factorsOf tops dl, []) 0)
    let W' := blockAt T tops dl
    let G' := slotpower.gramT T W'
    sm.1.length == deg
      && (blockAt T tops l).all (fun v =>
        slotpower.spanMemberAtW T G' W'
          ⟨_, slotpower.identifyV 0 T sm.1 [] [(List.range deg, true)] v⟩)

/-- A member's presentation at its generating table
(`con:memtable`), its reach list and its fundamentals' involution
(`con:fiber`): a vertex of two ends reads the block's coevaluation
at its clearing (`coevThrough`; `lem:dualread`(i)), at opposite
orientations the second factor at the exchanged actions and at one
orientation, the labels dual, read through the dual pair at every
slot, the factors matched by fundamental index to the dual
fundamental (`slotpower.transportSlots`), each at the block's
count; a further vertex the stacked raisings'
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
  let grp := fun (l : List Nat) => groupsAt T tops l
  let sigOf := fun (e : List Nat × Bool) => List.replicate (deg e.1) (!e.2)
  let colsOf := fun (e : List Nat × Bool) =>
    ((factorsOf tops e.1, ([] : List (Nat × Nat))))
  let endOf := fun (e : List Nat × Bool) =>
    (⟨sigOf e, deg e.1, ground.length_replicate _ _, blk e.1⟩ : slotpower.EndBlock)
  ⟨T,
   fun es =>
     let gen := fun (es : List (List Nat × Bool)) =>
       let ends := es.map endOf
       some ⟨es.map colsOf,
         .vecs T _ (slotpower.kernelVecs T (slotpower.fusedSig ends)
           (slotpower.fusedSpanT T ends)), Pos.one⟩
     match es with
     | [] => some ⟨[], .vecs T 0 [slotpower.unitV], Pos.one⟩
     | [e] => some ⟨[colsOf e], .vecs T (deg e.1) [], Pos.one⟩
     | [e1, e2] =>
       let n1 := deg e1.1
       let n2 := deg e2.1
       let same := e1.2 == e2.2
       let sm := slotpower.transportSlots dualF same
         (slotpower.layoutOf 0 (colsOf e1) 0) (slotpower.layoutOf 0 (colsOf e2) 0)
       if sm.1.length == n2 && n1 == n2 && (!same || T.dual.isSome) then
         let cv := coevThrough 0 T (grp e1.1) sm.1 []
           (if same then [(List.range n2, e2.2)] else [])
         some ⟨[colsOf e1, colsOf e2],
           .vecs T _ (if cv.1.val.length == 0 then [] else [cv.1]), cv.2⟩
       else some ⟨[colsOf e1, colsOf e2], .vecs T (n1 + n2) [], Pos.one⟩
     | e1 :: e2 :: e3 :: t => gen (e1 :: e2 :: e3 :: t),
   fun t =>
     let ends : List slotpower.EndBlock :=
       ⟨List.replicate (deg t.1) true, deg t.1, ground.length_replicate _ _, blk t.1⟩
       :: (match t.2.1 with
           | none => []
           | some o =>
             [⟨List.replicate (deg theta) (!o), deg theta, ground.length_replicate _ _,
               blk theta⟩])
       ++ [⟨List.replicate (deg t.2.2) false, deg t.2.2, ground.length_replicate _ _,
             blk t.2.2⟩]
     let mems := slotpower.kernelVecs T (slotpower.fusedSig ends)
       (slotpower.fusedSpanT T ends)
     (⟨_, mems⟩, slotpower.gramT T mems),
   (deg theta, 0),
   (let cv := coevOf (grp theta)
    (⟨_, cv.1⟩, cv.2)),
   false,
   dualF⟩

end fiber
