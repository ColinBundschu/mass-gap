import MassGap.Blockcount
import MassGap.Labels
/-!
`con:slotpower` — the presentation's carrier.  A factor list's slot
power is the power at one slot per factor, the units acting on an
undaggered factor's slot by the standard action and on a daggered
factor's slot by the dual action, the exchanged letters' balance
partner (`lem:dualread`(i)), both read on the one coordinate
family, the power's monomials (`slotAct` the action at one slot,
`raiseS` and `lowerS` the units at a slot signature).  A label
enters at its word pair (`wordPair`: a column of the reduced shape
at a length at or below its complement's enters the top word at
that many undaggered factors, a further column the bottom word at
the complement length's daggered, the tie a column at its
complement's length), its slots the top columns' undaggered then
the bottom columns' daggered (`labelSig`, an incoming end at the
exchanged signature `endSig`).  A monomial's weight is its
undaggered letter counts against its daggered, and the unit weight
is the full columns' class (`unitWeightAt` at the two counts,
`unitWeight` at a monomial); a graded vector holds one coordinate
family per content (`GVec` over `blockcount.HVec`, the join
`gadd`, the scale, the tensor `gtensor`, the coordinate pairing
`gdot` at the graded pairing, `gOfMons` the vector at a stated
family of occupied monomials, `gprim` the primitive
representative at the coordinates' shared count), and a block
member is weight-homogeneous, every lowering moving the two counts
alike, so its weight reads at one occupied monomial (`gWeight`).
A label's block at its word pair is the lowerings' span at its top,
the top-word columns' wedge exhibits on the undaggered slots
tensored with the bottom-word columns' dual wedges on the
daggered, the wedge at the last letters of the complement's length
(`blockTop`, `dualWedge`; `blockSpanAt` the closure at the Gram's
independence read within the weight's group, `gtryAdd`).  The
fused span at a vertex is its ends' blocks' tensors at the unit
weight, the members at weights joining to it (`fusedSpan`), the
stacked raisings' kernel over it the invariants' list (`kernelAt`,
`def:elim`'s back solve; `combo` a member as a graded vector).  A
wiring's tensor reads one letter per row end, read again at the
column end it pairs (`wiringG`).  The through pairing of two ends
at dual labels pairs each column's slots with its complement
column's, a wiring at an undaggered slot against a daggered one and
the star at a tie column, the monomials at complementary letter
sets at the swap grading's side cleared at the column length's
factorial (`throughPair`, the tensor the column pairs' families'
product), and its projection to the fused span at the span's
Gram-dual solve, the back solve over the bordered Gram, is the
block's coevaluation (`projectS`).
-/

namespace slotpower
open ground places blockcount

/-- The reduced shape's columns, longest first. -/
def cols (s : Shape) : List Nat := blockcount.columnLengths (labels.reduce s)

/-- A column's side at the count: the top word where its length
sits at or below its complement's. -/
def topCol (d l : Nat) : Bool := l + l ≤ d

/-- The top-word columns, longest first. -/
def topCols (d : Nat) (s : Shape) : List Nat := (cols s).filter (topCol d)

/-- The bottom-word columns, longest first. -/
def botCols (d : Nat) (s : Shape) : List Nat :=
  (cols s).filter (fun l => !topCol d l)

/-- A label's word pair: the top columns' lengths against the
bottom columns' complement lengths. -/
def wordPair (d : Nat) (s : Shape) : Nat × Nat :=
  (sumNat (topCols d s), sumNat ((botCols d s).map (fun l => d - l)))

/-- A label's slot signature: the undaggered slots then the
daggered, `false` undaggered. -/
def labelSig (d : Nat) (s : Shape) : List Bool :=
  List.replicate (wordPair d s).1 false ++ List.replicate (wordPair d s).2 true

/-- An end's slot signature: the label's at an outgoing end, the
exchanged at an incoming, the dual block on the one coordinate
family. -/
def endSig (d : Nat) (e : Shape × Bool) : List Bool :=
  if e.2 then labelSig d e.1 else (labelSig d e.1).map not

/-- A vertex's slot signature, its ends' in the incident order. -/
def vertexSig (d : Nat) (es : List (Shape × Bool)) : List Bool :=
  es.flatMap (endSig d)

/-- The undaggered slots in order. -/
def upSlots (sig : List Bool) : List Nat :=
  (List.range sig.length).filter (fun s => !getAt false sig s)

/-- The daggered slots in order. -/
def downSlots (sig : List Bool) : List Nat :=
  (List.range sig.length).filter (fun s => getAt false sig s)

/-- The unit-weight read at an undaggered content against a
daggered: every letter's two counts at one balance, the full
columns' class. -/
def unitWeightAt (d : Nat) (up dn : List Nat) : Bool :=
  (List.range d).all (fun l =>
    getAt 0 up l + getAt 0 dn 0 == getAt 0 up 0 + getAt 0 dn l)

/-- A monomial's unit-weight read at a signature. -/
def unitWeight (d : Nat) (sig : List Bool) (m : List Nat) : Bool :=
  unitWeightAt d (content d ((upSlots sig).map (fun s => getAt 0 m s)))
    (content d ((downSlots sig).map (fun s => getAt 0 m s)))

/-! The graded vectors: one coordinate family per content. -/

/-- A graded vector, its pieces at distinct contents. -/
abbrev GVec := List HVec

/-- A piece joined at its content, a new content appended. -/
def gjoin : GVec → HVec → GVec
  | [], v => [v]
  | w :: t, v =>
    if w.content == v.content then ⟨w.content, elim.vecAdd w.coords v.coords⟩ :: t
    else w :: gjoin t v

/-- The sum of two graded vectors. -/
def gadd (g h : GVec) : GVec := h.foldl gjoin g

/-- The scale of a graded vector. -/
def gscale (c : BPair) (g : GVec) : GVec :=
  g.map (fun v => ⟨v.content, elim.vecScale c v.coords⟩)

/-- The pieces at the sum's unit withdrawn. -/
def gtrim (g : GVec) : GVec := g.filter (fun v => !allU v.coords)

/-- The coordinate pairing, the graded pairing's fold over the
piece pairs. -/
def gdot (g h : GVec) : BPair :=
  g.foldl (fun acc v => h.foldl (fun acc2 w => acc2 + dotG v w) acc) BPair.unit

/-- The tensor of two graded vectors, the pieces' tensors joined at
their contents. -/
def gtensor (g h : GVec) : GVec :=
  g.foldl (fun acc v => h.foldl (fun acc2 w => gjoin acc2 (tensorH v w)) acc) []

/-- The scalar one, the vacant power's own vector. -/
def gunit (d : Nat) : GVec := [⟨List.replicate d 0, [BPair.ofNat 1]⟩]

/-- The graded vector at a stated family of occupied monomials with
their coefficients: one piece per content, each coefficient
scattered at its monomial's arithmetic rank into the content's
coordinate family. -/
def gOfMons (d : Nat) (l : List (List Nat × BPair)) : GVec :=
  let keyed := l.map (fun p => (content d p.1, p))
  (ground.dedupF (keyed.map Prod.fst)).map (fun c =>
    ⟨c, keyed.foldl (fun acc p =>
        if p.1 == c then units.scatterAt (rankOf p.2.1 c) p.2.2 acc else acc)
      ((monomialsAt c).map (fun _ => BPair.unit))⟩)

/-- A piece's coordinates at a stated content, the unit tail off the
occupied contents. -/
def pieceAt (c : List Nat) (g : GVec) : List BPair :=
  g.foldl (fun acc v => if v.content == c then v.coords else acc)
    ((monomialsAt c).map (fun _ => BPair.unit))

/-- The contents a list of graded vectors occupies, each once at
its first occurrence. -/
def contentsOf (l : List GVec) : List (List Nat) :=
  ground.dedupF (l.flatMap (fun g => g.map (fun v => v.content)))

/-- A graded vector at its primitive representative: the
coordinates stripped at their shared count (`thm:windowsep`'s
strip). -/
def gprim (g : GVec) : GVec :=
  let k := BPair.listContent (g.flatMap (fun v => v.coords))
  g.map (fun v => ⟨v.content, BPair.listPrim k v.coords⟩)

/-- A graded vector's unit-weight read: every occupied monomial at
the unit weight. -/
def gUnitWeight (d : Nat) (sig : List Bool) (g : GVec) : Bool :=
  g.all (fun v => (List.zipWith (fun m x => (m, x)) (monomialsAt v.content)
    v.coords).all (fun p => decide (p.2.oneValue BPair.unit) || unitWeight d sig p.1))

/-- A graded vector's weight at a signature, its first occupied
monomial's undaggered content against its daggered; a block member
reads one weight at every occupied monomial. -/
def gWeight (d : Nat) (sig : List Bool) (g : GVec) : List Nat × List Nat :=
  let m := g.foldl (fun (acc : Option (List Nat)) v =>
    match acc with
    | some _ => acc
    | none => (List.zipWith (fun m x => (m, x)) (monomialsAt v.content) v.coords).foldl
        (fun acc2 p =>
          match acc2 with
          | some _ => acc2
          | none => if decide (p.2.oneValue BPair.unit) then none else some p.1)
        none) none
  match m with
  | none => (List.replicate d 0, List.replicate d 0)
  | some m => (content d ((upSlots sig).map (fun s => getAt 0 m s)),
      content d ((downSlots sig).map (fun s => getAt 0 m s)))

/-! The units at the slots. -/

/-- The unit's action at one slot: the letter `j` at the slot read
to `i`, the content moved, vacant where the letter sits off the
content. -/
def slotAct (s i j : Nat) (v : HVec) : Option HVec :=
  if 0 < getAt 0 v.content j then
    let mu := moveAt i j v.content
    some ⟨mu, (List.zipWith (fun m x => (m, x)) (monomialsAt v.content) v.coords).foldl
      (fun acc p =>
        if p.2.isUnitRep then acc
        else if getAt 0 p.1 s == j then
          units.scatterAt (rankOf (p.1.set s i) mu) p.2 acc
        else acc)
      ((monomialsAt mu).map (fun _ => BPair.unit))⟩
  else none

/-- A slot's image joined, the balance partner at a daggered slot. -/
private def joinAct (neg : Bool) (acc : GVec) : Option HVec → GVec
  | none => acc
  | some w => gjoin acc (if neg then ⟨w.content, poly.neg w.coords⟩ else w)

/-- The raising `E_{i,i+1}` at a slot signature: the letter `i+1`
read to `i` at an undaggered slot, and at a daggered slot the dual
action, the letter `i` read to `i+1` at the balance partner. -/
def raiseS (sig : List Bool) (i : Nat) (g : GVec) : GVec :=
  g.foldl (fun acc v => (List.range sig.length).foldl (fun acc2 s =>
    if getAt false sig s then joinAct true acc2 (slotAct s (i + 1) i v)
    else joinAct false acc2 (slotAct s i (i + 1) v)) acc) []

/-- The lowering `E_{i+1,i}` at a slot signature: the letter `i` read
to `i+1` at an undaggered slot, and at a daggered slot the dual
action, the letter `i+1` read to `i` at the balance partner. -/
def lowerS (sig : List Bool) (i : Nat) (g : GVec) : GVec :=
  g.foldl (fun acc v => (List.range sig.length).foldl (fun acc2 s =>
    if getAt false sig s then joinAct true acc2 (slotAct s i (i + 1) v)
    else joinAct false acc2 (slotAct s (i + 1) i v)) acc) []

/-! The blocks at the word pairs. -/

/-- The dual wedge at a complement length: the wedge on the last
letters, each arrangement on its permutation's side. -/
def dualWedge (d m : Nat) : HVec :=
  blockcount.wedgeC ((List.range d).map (fun i => if d - m ≤ i then 1 else 0))

/-- A label's top at its word pair: the top columns' wedges on the
undaggered slots tensored with the bottom columns' dual wedges on
the daggered. -/
def blockTop (d : Nat) (s : Shape) : HVec :=
  (botCols d s).foldl (fun acc l => tensorH acc (dualWedge d (d - l)))
    ((topCols d s).foldl (fun acc l => tensorH acc (wedge d l))
      ⟨List.replicate d 0, [BPair.ofNat 1]⟩)

/-- The Gram of a list of graded vectors at the coordinate
pairing. -/
def gramOf (l : List GVec) : elim.Mat :=
  elim.gramBy (fun u v => (gdot u v).norm) l

/-- A graded vector joined to a pool at the membership read within
its weight's group: the group's Gram with the vector reads a
determinant off the sum's unit (`lem:lowerspan`'s independence
read at the Gram, the pairing definite; the weight grading
orthogonal, a member's weight one at every monomial), a member of
the group's span refused. -/
def gtryAdd (d : Nat) (sig : List Bool) (pool : List GVec) (g : GVec) : List GVec :=
  let w := gWeight d sig g
  let group := pool.filter (fun h => gWeight d sig h == w)
  if (elim.detD (gramOf (group ++ [g]))).oneValue BPair.unit then pool
  else pool ++ [g]

/-- The lowering closure at a signature from stated seeds, each
round joining the frontier's lowerings at the membership read
(`ground.closeBy`). -/
def closeS (d : Nat) (sig : List Bool) : Nat → List GVec → List GVec → List GVec :=
  ground.closeBy (fun g => (List.range (d - 1)).map (fun i => gtrim (lowerS sig i g)))
    (gtryAdd d sig)

/-- A label's block at its word pair, the lowerings' span at its
top. -/
def blockSpanAt (d : Nat) (s : Shape) : List GVec :=
  let sig := labelSig d s
  closeS d sig (sig.length * d + 1) [[blockTop d s]] [[blockTop d s]]

/-! The fused span and the invariants at a vertex. -/

/-- Two weights' sum, the counts added letter by letter. -/
private def weightAdd (a b : List Nat × List Nat) : List Nat × List Nat :=
  (List.zipWith Nat.add a.1 b.1, List.zipWith Nat.add a.2 b.2)

/-- The fused span at a vertex: the ends' blocks' tensors at the
unit weight, one tensor per member family whose weights, each read
at its end's signature, join to the unit weight. -/
def fusedSpan (d : Nat) (es : List (Shape × Bool)) : List GVec :=
  let combos := es.foldl (fun (P : List (List GVec × (List Nat × List Nat))) e =>
      let blk := (blockSpanAt d e.1).map (fun g => (g, gWeight d (endSig d e) g))
      P.flatMap (fun t => blk.map (fun b => (t.1 ++ [b.1], weightAdd t.2 b.2))))
    [([], (List.replicate d 0, List.replicate d 0))]
  (combos.filter (fun t => unitWeightAt d t.2.1 t.2.2)).map (fun t =>
    t.1.foldl gtensor (gunit d))

/-- A combination over a pool, the coefficients' scaled sum. -/
def combo (pool : List GVec) (k : List BPair) : GVec :=
  (List.zipWith (fun g c => (g, c)) pool k).foldl
    (fun acc p => gadd acc (gscale p.2 p.1)) []

/-- The stacked raisings' rows over a pool: per raising and per
occupied target content, one row per monomial at the members'
image coordinates. -/
def raiseRows (d : Nat) (sig : List Bool) (pool : List GVec) : elim.Mat :=
  (List.range (d - 1)).flatMap (fun i =>
    let imgs := pool.map (fun g => raiseS sig i g)
    (contentsOf imgs).flatMap (fun c =>
      (List.range (monomialsAt c).length).map (fun t =>
        imgs.map (fun im => getAt BPair.unit (pieceAt c im) t))))

/-- The invariants over a pool: the stacked raisings' kernel list,
one member per pivot-free column at the back solve, the rows at
the sum's unit withdrawn (a row of equal members pairs every
member at that unit outright). -/
def kernelAt (d : Nat) (sig : List Bool) (pool : List GVec) : List (List BPair) :=
  elim.kernelList pool.length ((raiseRows d sig pool).filter (fun r => !allU r))

/-! The wirings and the through pairing. -/

/-- A wiring's tensor at a signature: one letter per row end, read
again at the column end it pairs, one monomial per letter
assignment. -/
def wiringG (d : Nat) (sig : List Bool) (σ : List Nat) : GVec :=
  let U := upSlots sig
  let D := downSlots sig
  gOfMons d ((allMon d U.length).map (fun ls =>
    ((List.range U.length).foldl (fun m r =>
      (m.set (getAt 0 U r) (getAt 0 ls r)).set (getAt 0 D (getAt 0 σ r))
        (getAt 0 ls r)) (List.replicate sig.length 0), BPair.ofNat 1)))

/-- An end's column layout: per column its length with its slots in
the vertex, the top columns' undaggered slots then the bottom
columns' daggered, from a stated offset. -/
def colLayout (d : Nat) (e : Shape) (off : Nat) : List (Nat × List Nat) :=
  ((topCols d e).foldl (fun acc l =>
      (acc.1 ++ [(l, (List.range l).map (fun i => acc.2 + i))], acc.2 + l))
    (([] : List (Nat × List Nat)), off)
  |> fun t => (botCols d e).foldl (fun acc l =>
      (acc.1 ++ [(l, (List.range (d - l)).map (fun i => acc.2 + i))], acc.2 + (d - l)))
    t).1

/-- The partner column read: at exchanged orientations the column
of one length, at one orientation the complement's, the first
unused match consumed. -/
private def matchCols (d : Nat) (same : Bool) :
    List (Nat × List Nat) → List (Nat × List Nat) →
    List (List Nat × List Nat × Bool)
  | [], _ => []
  | (l, A) :: t, R =>
    let want := if same then d - l else l
    match R.foldl (fun (acc : Option (Nat × List Nat) × List (Nat × List Nat)) c =>
        match acc.1 with
        | some _ => (acc.1, acc.2 ++ [c])
        | none => if c.1 == want then (some c, acc.2) else (none, acc.2 ++ [c]))
      (none, []) with
    | (some c, rest) => (A, c.2, same && (l + l == d)) :: matchCols d same t rest
    | (none, _) => []

/-- A column pair's family: at a wiring one member per letter list,
the letters at the paired slots agreeing, and at the star one
member per arrangement of the letters over the two columns, the
complementary letter sets at the swap grading's side; each member
its slot assignments with its coefficient. -/
private def pairFam (d : Nat) (p : List Nat × List Nat × Bool) :
    List (List (Nat × Nat) × BPair) :=
  if p.2.2 then
    (perms d).map (fun ls =>
      (List.zipWith (fun s l => (s, l)) (p.1 ++ p.2.1) ls,
       if parity ls then (BPair.ofNat 1).swap else BPair.ofNat 1))
  else
    (allMon d p.1.length).map (fun ls =>
      (List.zipWith (fun s l => (s, l)) p.1 ls ++ List.zipWith (fun s l => (s, l)) p.2.1 ls,
       BPair.ofNat 1))

/-- The through pairing of two ends at dual labels: each column's
slots against its complement column's, a wiring at an undaggered
slot against a daggered one and the star at a tie column, the
tensor the column pairs' families' product cleared at the tie
columns' factorials; vacant off the dual pair. -/
def throughPair (d : Nat) (e1 e2 : Shape × Bool) : GVec × Pos :=
  let same := e1.2 == e2.2
  let ok := if same then labels.reduce e2.1 == labels.reduce (labels.dualL e1.1)
    else labels.reduce e2.1 == labels.reduce e1.1
  let n1 := (labelSig d e1.1).length
  let n := n1 + (labelSig d e2.1).length
  let pairs := matchCols d same (colLayout d e1.1 0) (colLayout d e2.1 n1)
  if !ok || pairs.length != (cols e1.1).length then ([], Pos.one)
  else
    let clear := pairs.foldl (fun acc p =>
      if p.2.2 then acc * factorial p.1.length else acc) 1
    let fam := pairs.foldl (fun acc p =>
      acc.flatMap (fun a => (pairFam d p).map (fun b => (a.1 ++ b.1, a.2 * b.2))))
      [(([] : List (Nat × Nat)), BPair.ofNat 1)]
    (gOfMons d (fam.map (fun a =>
      (a.1.foldl (fun m sl => m.set sl.1 sl.2) (List.replicate n 0), a.2))),
     posOfSucc (clear - 1))

/-- The projection onto a pool's span at the pool's Gram-dual
solve: the coefficients solve the Gram against the pairings, the
solve the back solve's kernel member over the Gram bordered by the
pairings' balance partners (`def:elim`), one member at an
independent pool, its last coordinate the crossed pivots' product
on the upper side at the definite Gram, the clearing at the
coefficients' side. -/
def projectS (pool : List GVec) (g : GVec) : GVec × Pos :=
  let G := gramOf pool
  let b := pool.map (fun u => gdot u g)
  let rows := List.zipWith (fun r x => r ++ [x.swap]) G b
  let k0 := getAt [] (elim.kernelList (pool.length + 1) rows) 0
  let k := BPair.listPrim (BPair.listContent k0) k0
  (gtrim (combo pool (k.take pool.length)),
   posOfSucc (BPair.marginN (getAt BPair.unit k pool.length) - 1))

end slotpower
