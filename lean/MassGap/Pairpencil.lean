import MassGap.Pencil
import MassGap.Inertia
import MassGap.Fpcap
import MassGap.Algebra
import MassGap.Windowfinite
/-!
`thm:pairpencil` — the window pencil as a symmetric pair matrix:
`E` is diagonal in the label index with the unit line at its head
(`slotDiag`, the window list's diagonal over `def:pencil`'s
electric read), `M` is the
multiplication by the real character sum, symmetric against the
orthonormal characters — at a loop window the label-index matrix is
the fusion counts' own, `M[x, y] = N^x_{θ y}` read at the
interface's count (`loopMag`, `prop:repring`'s orthonormality the
warrant, the vacuum defect the Kronecker delta at two labels), the
loop window's two-sided cap reading at `lem:loopcap` over the
interface's counts — and
the pair
`(α E : β M)`'s site datum `H([α : β])` is symmetric with pair
entries at weights of the positive carrier (`pencilH` at the
electric member's form against the gram, the operator's own
diagonal `pencilE`, `elim.symmRead` the transpose's one-value read).  The pencil interface is the fields a window's
pencil enters every derivation through, read positionally at the
window list — the unit line at position zero, then per index member
its fiber's slot keys, one digit per vertex below the vertex's
multiplicity (`slotKeys`, `def:carrier`'s tensor product over the
touched vertices, its count the fiber's multiplicity product at
`length_slotKeys`; `slotList` over a stated index, distinct over a
distinct index at `slotList_distinct`; `posConf` the configuration
at a position): the order tie at the window list's count
(`prop:windowfinite`'s `dimSect`, `slotList_dimSect`), the electric
member the gram's form at the window list's diagonal, each row at
its slot's content with the unit line at the sum's unit (`formE`
over `slotDiag`, `def:pencil`'s operator read as a form; at unit
fiber products the index's contents outright, `slotDiag_unit`), the
gram block diagonal over the index at the fibers' pairings with the
unit line at the window's clearing and positive definite at its
split (`gramBlockRead`, `def:carrier`): the cross-member entries at
the sum's unit, and within a member each entry the fiber's
presentation Gram at the window's one positive rescaling to integer
entries — the interface's vertex Grams over the incident ends
(`fibGram`, `con:fiber`'s vertex lists at their multiplicities
through the window's vertex-list store, `vertGramAt`, read once per
member along the index at `memberBlocks`), the entry at
two slot keys the vertex Grams' entries' product against the links'
cleared block scale (`blockScale`, `def:carrier`'s `[1 : d_{a_ℓ}]`
per support link; `entryRead` the one entry's cross-multiplied read
at the member's positions), and the magnetic member the
plaquette terms' sum (`termSum`), each term symmetric, capped
two-sidedly as a form at the adjoint dimension's multiple of the
gram (`lem:loopcap`; `inertia.capAt` at the two splits) and
supported across its changed edge alone — an entry off the sum's
unit at a position pair one of whose configurations is the other's
target on the plaquette's row (`termSupport` at `def:algebra`'s
row, the far reads' factorization the vacant complement,
`lem:stableentries`) with its entries the plaquette
multiplication's read at the fibers' stated lists (`entriesRead`
at `entryAt`, `con:fiber`'s magnetic read): per position pair
across the changed edge (`rowPair`) the entry joined to the gram's
reads `Eval(x̄ |tr U_∂p|² y)`, the boundary character the trace
against its dagger less the unit, cleared by the links'
determinants and the states' clearings against the window's
clearing (`termEntry`) — per link the invariant list of the
combined slots with its Gram's adjugate and determinant
(`linkData` at the field's link list at the link's labels with its
boundary read, `fiber.linkSig` the combined signature at the
letters, and `fiber.coevW`, read once per key of the window's
labels through the store `linkKeys`, `linkDataAt` the read's own
at `linkDataAt_read`), the boundary factor's tensor at each boundary
vertex (the field's `bdry`, the `θ` block's Gram-dual coevaluation
at the two boundary ends' slots, at the letters the mixed power's
whole list at `(1,1)`, the trace against its dagger with the unit's
term, the gram, withdrawn at the field's `lessUnit`), the vertex
tensor the three
members' weighted pairing against the links' members at every tuple
of the links' member indices (`vertexTensor` at the blocks
`blocksAt` and the sub-monomials `subMon`, the pairing
`slotpower.monDotT` at the table's weight, the members
`vertexMember` through the window's vertex-list store `endsStore`,
`vertListAt` the field's own read at `vertListAt_read`), and the
contraction the fold over the vertices at the open links'
assignments (`stepVertex`, a link opening at its first end and
closing at its second at the adjugate weight), the pencil's entry
`entryAt` at a pair of two loops the loop window's read, the fusion
count at the loop labels (`loopLabel` at `loopConf`), and otherwise
the contraction `contractAt` — the
terms' reads along the region's
plaquette list (`termsRead`, the terms' count the plaquettes' and
each term square at the order, `termsRead_len` and `termsRead_sq`),
the transport field at two states across a label-graph
isomorphism (`termTransport`: the configurations moved along the
links with the labels dualized at the reversed traversals and the
unimaged keys at the unit, `dualConf`, and the members moved,
`movedMembers` at `moveMember` — the slot map column by column at
the two labels' columns, `slotMap` at `slotpower.transportSlots`
and `colsOf` at the field's column dual, the place action
`slotpower.relabelV` along it, the star `slotpower.starAt` at the
tie columns of the reversed ends with the clearing scaled at their
factorials at the letters, and the table's dual pair at every
reversed slot at a member with the clearing scaled at its clearing
squared per slot read into the standard action — the term's entry at
the moved states one value with the entry at the states,
`termTransportAt` at stated moved data and `termEntryAt` the
contraction at stated members), the region's own action's instance
over the window list in the module that owns the action, and the
whole `pencilRead` at the fields this module owns, every read at a
stated index tied to the window's own; at a loop
window the fields read off the fusion counts, `loopMag` the
magnetic term with the identity gram, the check module's pins.
-/

namespace pairpencil
open ground lattice fusion elim inertia

/-- The label-index magnetic matrix at a loop window: over the unit
with a stated label list, `M[x, y] = N^x_{θ y}` — the
multiplication's matrix at the adjoint, `fpcap.fusionMat`'s read
at the unit-headed index. -/
def loopMag {L : Type} (F : Data L) (ls : List L) : Mat :=
  fpcap.fusionMat F F.theta (F.unit :: ls)

/-- The free end's window matrix, the electric member's own read:
the diagonal at the window contents alone — `prop:segment`'s
one-member weighting, its own site with no weight pair. -/
def pencilE (diag : List Nat) : Mat :=
  ground.matOf diag.length diag.length (fun i j =>
      if i == j then BPair.ofNat (ground.getAt 0 diag i)
      else BPair.unit)

/-! The pencil interface: the fields a window's pencil enters every
derivation through, read positionally at the window list. -/

/-- The fiber's slot keys at a configuration: per vertex of the
region one digit below the vertex's multiplicity, an untouched
vertex at the product's unit — the fiber's coordinates at
`lem:fiberdec`'s window list over `def:carrier`'s product. -/
def slotKeys {L : Type} (F : Data L) (R : Region) (a : List L) :
    List (List Nat) :=
  prodLists ((List.range R.verts).map (fun v => List.range (carrier.vmult F R a v)))

/-- The slot keys' count is the fiber's multiplicity product, the
untouched vertices' unit factors withdrawn. -/
theorem length_slotKeys {L : Type} (F : Data L) (R : Region) (a : List L) :
    (slotKeys F R a).length = windowfinite.fibProd F R a := by
  show (prodLists _).length = prodOver (carrier.vmult F R a) (carrier.touched F R a)
  rw [length_prodLists,
    show prodOver List.length
        ((List.range R.verts).map (fun v => List.range (carrier.vmult F R a v)))
      = prodOver (carrier.vmult F R a) (List.range R.verts) from by
      show famFold Nat.mul 1 List.length (_ : List (List Nat))
        = famFold Nat.mul 1 (carrier.vmult F R a) _
      rw [famFold_map]
      exact famFold_congr_all Nat.mul 1 _ _ (fun v => length_range _) _]
  exact (prodOver_filter (carrier.vmult F R a) _
    (fun v hv => carrier.vmult_vacant F R a v hv) (List.range R.verts)).symm

/-- The window list over a stated index: the members with their
fibers' slot keys, the unit line's one position at the head
withheld. -/
def slotList {L : Type} (F : Data L) (R : Region) (ix : List (List L)) :
    List (List L × List Nat) :=
  ix.flatMap (fun a => (slotKeys F R a).map (fun k => (a, k)))

/-- The window list's electric diagonal with the unit line at its
head: each slot at its configuration's content, `def:pencil`'s
diagonal over the fibers' slots. -/
def slotDiag {L : Type} (F : Data L) (R : Region) (ix : List (List L)) :
    List Nat :=
  0 :: (slotList F R ix).map (fun p => carrier.contentN F p.1)

/-- The configuration at a window position: the unit configuration
at position zero, the window list's member past it, a position past
the order reading the unit configuration. -/
def posConf {L : Type} (F : Data L) (R : Region) (ix : List (List L)) :
    Nat → List L
  | 0 => carrier.unitConf F R
  | k + 1 => (getAt (carrier.unitConf F R, []) (slotList F R ix) k).1

/-- The fiber key at a window position: the vacant key at the unit
line, the window list's key past it, a position past the order
reading the vacant key. -/
def posKey {L : Type} (F : Data L) (R : Region) (ix : List (List L)) :
    Nat → List Nat
  | 0 => []
  | k + 1 => (getAt (carrier.unitConf F R, []) (slotList F R ix) k).2

/-- The window list's count is the fibers' multiplicity products'
fold over the index. -/
theorem length_slotList {L : Type} (F : Data L) (R : Region)
    (ix : List (List L)) :
    (slotList F R ix).length
      = famFold Nat.add 0 (windowfinite.fibProd F R) ix := by
  show (ix.flatMap (fun a => (slotKeys F R a).map (fun k => (a, k)))).length = _
  rw [length_flatMap]
  exact famFold_congr_all Nat.add 0 _ _
    (fun a => (length_map _ _).trans (length_slotKeys F R a)) ix

/-- The window list's count with the unit line is the window
dimension, `prop:windowfinite`'s count. -/
theorem slotList_dimSect {L : Type} (F : Data L) (R : Region) (C : Nat) :
    (slotList F R (carrier.idx F R C)).length + 1 = windowfinite.dimSect F R C := by
  show _ = 1 + (carrier.idx F R C).foldl (fun acc a => acc + windowfinite.fibProd F R a) 0
  rw [foldlSum, Nat.zero_add, length_slotList, Nat.add_comm]

/-- A window list member is an index member with one of its slot
keys. -/
theorem mem_slotList_of {L : Type} (F : Data L) (R : Region)
    (ix : List (List L)) (p : List L × List Nat) (h : p ∈ slotList F R ix) :
    p.1 ∈ ix ∧ p.2 ∈ slotKeys F R p.1 := by
  obtain ⟨a, ha, hp⟩ := mem_flatMap_of _ ix p h
  obtain ⟨k, hk, hkp⟩ := mem_map_of _ _ p hp
  rw [← hkp]
  exact ⟨ha, hk⟩

/-- The window list over a distinct index is distinct: a member's
count is its configuration's in the index against its key's in the
fiber's distinct keys. -/
theorem slotList_distinct {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (h : distinctList ix) :
    distinctList (slotList F R ix) := by
  intro p hp
  obtain ⟨ha, hk⟩ := mem_slotList_of F R ix p hp
  obtain ⟨a, k⟩ := p
  show countOf (a, k) (ix.flatMap (fun b => (slotKeys F R b).map (fun j => (b, j)))) ≤ 1
  rw [countOf_flatMap]
  refine famFold_le_one_at _ a ix (fun b _ hne => ?_) ?_ (h a ha)
  · exact countOf_map_none _ _ _ (fun j _ he => hne (congrArg Prod.fst he))
  · show countOf (a, k) ((slotKeys F R a).map (fun j => (a, j))) ≤ 1
    rw [countOf_map_inj (fun j => (a, j)) k _ (fun j _ he => congrArg Prod.snd he)]
    exact distinct_prodLists _ (fun D hD => by
      obtain ⟨v, _, hv⟩ := mem_map_of _ _ D hD
      rw [← hv]
      exact distinctList_range _) k hk

/-- At unit fiber products the window list is the index with one
vacant key per member and the slot diagonal is the index's
contents, the index's own content list at the unit line. -/
theorem slotDiag_unit {L : Type} (F : Data L) (R : Region) :
    ∀ ix : List (List L),
      (ix.all (fun a => windowfinite.fibProd F R a == 1)) = true →
      slotDiag F R ix = 0 :: ix.map (carrier.contentN F)
  | [], _ => rfl
  | a :: t, h => by
    have h1 : (slotKeys F R a).length = 1 := by
      rw [length_slotKeys]
      exact beqEqOf (all_of_mem _ _ h a (List.Mem.head t))
    have ht : (t.all (fun a => windowfinite.fibProd F R a == 1)) = true :=
      all_of_mem_intro _ t (fun b hb => all_of_mem _ _ h b (List.Mem.tail a hb))
    have hrest := slotDiag_unit F R t ht
    have hrest' : (slotList F R t).map (fun p => carrier.contentN F p.1)
        = t.map (carrier.contentN F) := List.tail_eq_of_cons_eq hrest
    show 0 :: (((slotKeys F R a).map (fun k => (a, k)) ++ slotList F R t).map
      (fun p => carrier.contentN F p.1)) = 0 :: (carrier.contentN F a :: t.map (carrier.contentN F))
    cases hs : slotKeys F R a with
    | nil => rw [hs] at h1; exact Nat.noConfusion h1
    | cons k r =>
      cases r with
      | nil =>
        show 0 :: (carrier.contentN F a :: (slotList F R t).map (fun p => carrier.contentN F p.1))
          = _
        rw [hrest']
      | cons k' r' => rw [hs] at h1; exact Nat.noConfusion (Nat.succ.inj h1)

/-- The electric member's form against the gram: each entry the
gram's at the row position's content, `def:pencil`'s operator read
as a form (`thm:pairpencil`'s electric field). -/
def formE (diag : List Nat) (G : Mat) : Mat :=
  ground.matOf diag.length diag.length (fun i j =>
    (BPair.ofNat (ground.getAt 0 diag i)
      * ground.getAt BPair.unit (ground.getAt [] G i) j).norm)

/-- The pair `(α E : β M)`'s site datum `H([α : β])` at the window:
`pencil.rayH` at the electric member's form against the gram
(`formE`, each row at its slot's content) and the magnetic matrix,
`α E = β M + H`, every entry a pair datum at pair weights. -/
def pencilH (al be : Pos) (diag : List Nat) (G M : Mat) : Mat :=
  pencil.rayH (formE diag G) M al be

/-- The vertex lists read once per incident-end list of the window:
every index member's incident ends at every vertex with the unit
line's, each list stored at its first occurrence. -/
def endsStore {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) : List (List (L × Bool) × Option fiber.VList) :=
  (carrier.unitConf F R :: ix).foldl (fun acc a =>
    (List.range R.verts).foldl (fun acc2 v =>
      let es := carrier.incidentEnds F R a v
      if acc2.any (fun e => decide (e.1 = es)) then acc2
      else acc2 ++ [(es, F.pres.vertList es)]) acc) []

/-- The vertex list at an incident-end list through the window's
store, the field's own read at every list. -/
def vertListAt {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (es : List (L × Bool)) : Option fiber.VList :=
  keyAt (fun a b => decide (a = b)) (F.pres.vertList es) es (endsStore F R ix)

/-- The stored read is the field's: every store entry holds the
field's value at its key, the store built by joins at the field's
own reads. -/
theorem vertListAt_read {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (es : List (L × Bool)) :
    vertListAt F R ix es = F.pres.vertList es := by
  have hv : ∀ (a : List L) (vs : List Nat)
      (acc : List (List (L × Bool) × Option fiber.VList)),
      (∀ e, e ∈ acc → e.2 = F.pres.vertList e.1) →
      ∀ e, e ∈ vs.foldl (fun acc2 v =>
          let es := carrier.incidentEnds F R a v
          if acc2.any (fun e => decide (e.1 = es)) then acc2
          else acc2 ++ [(es, F.pres.vertList es)]) acc →
        e.2 = F.pres.vertList e.1 := by
    intro a vs
    induction vs with
    | nil => intro acc h; exact h
    | cons v t ih =>
      intro acc h
      refine ih _ ?_
      intro e he
      have he' : e ∈ (if acc.any (fun e =>
            decide (e.1 = carrier.incidentEnds F R a v)) then acc
          else acc ++ [(carrier.incidentEnds F R a v,
            F.pres.vertList (carrier.incidentEnds F R a v))]) := he
      cases hb : acc.any (fun e => decide (e.1 = carrier.incidentEnds F R a v)) with
      | true =>
        rw [if_pos hb] at he'
        exact h e he'
      | false =>
        rw [if_neg (fun hc => Bool.noConfusion (hb.symm.trans hc))] at he'
        cases ground.mem_append_of _ _ he' with
        | inl hl => exact h e hl
        | inr hr =>
          cases hr with
          | head => rfl
          | tail _ hm => exact nomatch hm
  have hst : ∀ (l : List (List L))
      (acc : List (List (L × Bool) × Option fiber.VList)),
      (∀ e, e ∈ acc → e.2 = F.pres.vertList e.1) →
      ∀ e, e ∈ l.foldl (fun acc a =>
          (List.range R.verts).foldl (fun acc2 v =>
            let es := carrier.incidentEnds F R a v
            if acc2.any (fun e => decide (e.1 = es)) then acc2
            else acc2 ++ [(es, F.pres.vertList es)]) acc) acc →
        e.2 = F.pres.vertList e.1 := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons a t ih => intro acc h; exact ih _ (hv a _ acc h)
  exact keyAt_store (fun a b => decide (a = b)) (fun _ _ h => of_decide_eq_true h)
    F.pres.vertList es _ (hst (carrier.unitConf F R :: ix) [] (fun _ h => nomatch h))

/-- The vertex Gram at an incident-end list through the window's
vertex-list store: the list's own Gram where the list is stated,
the two-end coevaluation's count at the label data off it
(`fusion.vertGramOf` at the stored read). -/
def vertGramAt {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (es : List (L × Bool)) : Option (Mat × Pos) :=
  match vertListAt F R ix es with
  | some l => some (fiber.listGram l)
  | none => fiber.twoEndGram F.eqL F.dual F.dim es

/-- The loop configuration at a label around a plaquette: the
label at the boundary's forward entries, its dual at the reversed,
the unit off the boundary. -/
def loopConf {L : Type} (F : Data L) (R : Region) (p : List (Nat × Bool))
    (x : L) : List L :=
  p.foldl (fun acc e => acc.set e.1 (if e.2 then x else F.dual x))
    (carrier.unitConf F R)

/-- A configuration's loop label at a plaquette: the label read at
the boundary's first entry where the configuration is that
label's loop, the unit configuration the unit's. -/
def loopLabel {L : Type} (F : Data L) (R : Region) (p : List (Nat × Bool))
    (a : List L) : Option L :=
  let e := getAt (0, true) p 0
  let x := if e.2 then getAt F.unit a e.1 else F.dual (getAt F.unit a e.1)
  if carrier.eqConf F a (loopConf F R p x) then some x else none

/-- The fiber's vertex Grams at a configuration, one per vertex of
the region: at a loop configuration the two-end coevaluation's
counts at the label data (`thm:pairpencil`'s loop clause, the
orthonormal characters), and otherwise the interface's presentation
field over the incident ends (`con:fiber`) read through the
window's store, each at the vertex's multiplicity and square there,
the vacant read at a vertex off the field or off the
multiplicity. -/
def fibGram {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (a : List L) : Option (List (Mat × Pos)) :=
  let isLoop := R.plaqs.any (fun p => (loopLabel F R p a).isSome)
  (List.range R.verts).foldl (fun acc v =>
    match acc, (if isLoop then fiber.twoEndGram F.eqL F.dual F.dim
        (carrier.incidentEnds F R a v)
      else vertGramAt F R ix (carrier.incidentEnds F R a v)) with
    | none, _ => none
    | some _, none => none
    | some l, some g =>
      if g.1.length == carrier.vmult F R a v
          && g.1.all (fun r => r.length == carrier.vmult F R a v) then
        some (l ++ [g])
      else none) (some [])

/-- The links' cleared block scale at a configuration, the support
labels' dimensions' product (`def:carrier`'s `[1 : d_{a_ℓ}]` per
support link). -/
def blockScale {L : Type} (F : Data L) (R : Region) (a : List L) : Nat :=
  prodOver (fun l => F.dim (getAt F.unit a l)) (carrier.support F R a)

/-- The block entry read at two positions of one index member at
its vertex Grams and two slot keys: the gram's entry against the
block scale and the vertex Grams' second members, one value with
the clearing against the vertex Grams' entries' product at the two
keys — `con:fiber`'s pairing display, the links' cleared block
scales against the vertex lists' pairings' product. -/
def entryRead {L : Type} (F : Data L) (R : Region) (a : List L)
    (gs : List (Mat × Pos)) (c : Pos) (G : Mat) (i j : Nat)
    (k k' : List Nat) : Bool :=
  let kron := (List.range R.verts).foldl (fun acc v =>
    acc * ground.getAt BPair.unit
      (ground.getAt [] (ground.getAt ([], Pos.one) gs v).1 (ground.getAt 0 k v))
      (ground.getAt 0 k' v)) (BPair.ofNat 1)
  let den := (List.range R.verts).foldl (fun acc v =>
    acc * posVal (ground.getAt ([], Pos.one) gs v).2) 1
  decide ((ground.getAt BPair.unit (ground.getAt [] G i) j
      * BPair.ofNat (blockScale F R a) * BPair.ofNat den).oneValue
    (BPair.ofPos c * kron))

/-- The members' block reads along the index: each member's vertex
Grams read once, its slots' positions the window list's from the
running offset past the unit line, every key pair at the entry
read. -/
def memberBlocks {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (c : Pos) (G : Mat) : Bool :=
  (ix.foldl (fun (acc : Nat × Bool) a =>
    let ks := slotKeys F R a
    (acc.1 + ks.length,
     acc.2 && (match fibGram F R ix a with
       | none => false
       | some gs =>
         (List.range ks.length).all (fun p => (List.range ks.length).all (fun q =>
           entryRead F R a gs c G (acc.1 + p) (acc.1 + q)
             (ground.getAt [] ks p) (ground.getAt [] ks q)))))) (1, true)).2

/-- The gram's block read: the unit line at the clearing, two
positions at distinct index members pairing at the sum's unit — the
fibers' orthogonal sum with the unit line's pairing at one
(`def:carrier`) — and every member's block at the entry read, the
fiber's presentation Gram at the stated clearing (`con:fiber`). -/
def gramBlockRead {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (n : Nat) (ix : List (List L)) (c : Pos) (G : Mat) : Prop :=
  (ground.getAt BPair.unit (ground.getAt [] G 0) 0).oneValue (BPair.ofPos c)
  ∧ ((List.range n).all (fun i => (List.range n).all (fun j =>
      carrier.eqConf F (posConf F R ix i) (posConf F R ix j)
        || decide ((ground.getAt BPair.unit
            (ground.getAt [] G i) j).oneValue BPair.unit)))) = true
  ∧ memberBlocks F R ix c G = true

instance {L : Type} [DecidableEq L] (F : Data L) (R : Region) (n : Nat)
    (ix : List (List L)) (c : Pos) (G : Mat) : Decidable (gramBlockRead F R n ix c G) :=
  inferInstanceAs (Decidable (_ ∧ _ = _ ∧ _ = _))

/-- Two window positions across a plaquette's changed edge: one
position's configuration the other's target on the plaquette's row
(`def:algebra`), read from either side. -/
def rowPair {L : Type} (F : Data L) (R : Region) (ix : List (List L))
    (p : List (Nat × Bool)) (i j : Nat) : Bool :=
  carrier.confMem F (posConf F R ix j)
      (algebra.plaqRow F R p (posConf F R ix i))
    || carrier.confMem F (posConf F R ix i)
      (algebra.plaqRow F R p (posConf F R ix j))

/-- A plaquette term's support read: an entry off the sum's unit
sits at a position pair whose configurations meet across the
plaquette's changed edge, one the other's target on the plaquette's
row (`def:algebra`), the far reads' factorization the vacant
complement (`lem:stableentries`). -/
def termSupport {L : Type} (F : Data L) (R : Region) (n : Nat)
    (ix : List (List L)) (p : List (Nat × Bool)) (M : Mat) : Prop :=
  ((List.range n).all (fun i => (List.range n).all (fun j =>
      decide ((ground.getAt BPair.unit
          (ground.getAt [] M i) j).oneValue BPair.unit)
        || rowPair F R ix p i j))) = true

instance {L : Type} (F : Data L) (R : Region) (n : Nat) (ix : List (List L))
    (p : List (Nat × Bool)) (M : Mat) :
    Decidable (termSupport F R n ix p M) :=
  inferInstanceAs (Decidable (_ = _))

/-! The magnetic member's entries (`con:fiber`'s magnetic read): a
plaquette term's entry between two window positions reads
`Eval(x̄ χ_θ(U_∂p) y)`, the boundary character the boundary word's
trace against its dagger less the unit, the unit's term the
states' pairing; per link the Gram-dual coevaluation of the link's
invariant list at the combined slots, the source state's with the
dagger reads flipped, the boundary word's pair and the target's,
one coordinate family at both ends; and the entry the one
contraction, per vertex the three members paired against the
incident links' coevaluation members and the pairings' product
folded over the links' member pairs at the adjugate weights. -/

/-- The moved configuration at a link map's witness and a reversal
family (`thm:pairpencil`'s transport field; `con:lattice`'s two
action fields): the label at a link key is the one the witness's
key held, dualized where the witness's link traverses backwards,
the reversal family read at the source key as the boundary words
read it (`lattice.moveWord`), the unoccupied keys the interface's
unit. -/
def dualConf {L : Type} (F : Data L) (t s : Nat → Nat)
    (rev : Nat → Bool) (n : Nat) (a : List L) : List L :=
  (List.range n).map (fun l =>
    if t (s l) == l then
      (if rev (s l) then F.dual (getAt F.unit a (s l))
       else getAt F.unit a (s l))
    else F.unit)

/-- The moved configuration at the reversal-free family. -/
def permConf {L : Type} (F : Data L) (t s : Nat → Nat) (n : Nat)
    (a : List L) : List L :=
  dualConf F t s (fun _ => false) n a

/-- The slot power's letter count at the presentation field, the
unit state's vertex list's width. -/
def lettersOf {L : Type} (F : Data L) : Nat := F.pres.table.keys

/-- A label's columns at the presentation field, the one-end vertex
list's stated end: the top word's columns against the bottom
word's, each at its key and length. -/
def colsOf {L : Type} (F : Data L) (x : L) :
    List (Nat × Nat) × List (Nat × Nat) :=
  match F.pres.vertList [(x, true)] with
  | some l => getAt ([], []) l.ends 0
  | none => ([], [])

/-- A label's word pair at the presentation field: the top columns'
lengths' sum against the bottom columns' complement lengths' sum. -/
def wordOf {L : Type} (F : Data L) (x : L) : Nat × Nat :=
  let c := colsOf F x
  let d := lettersOf F
  (ground.sumNat (c.1.map Prod.snd), ground.sumNat (c.2.map (fun l => d - l.2)))

/-- The vertex member of a state at a vertex: the member at the
state's key with the list's clearing, vacant where the list is
unstated. -/
def vertexMember {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (a : List L) (k : List Nat) (v : Nat) :
    Option (slotpower.SVec × Pos) :=
  match vertListAt F R ix (carrier.incidentEnds F R a v) with
  | none => none
  | some l => some (getAt [] l.members.list (getAt 0 k v), l.clear)

/-- A state's members at its fiber key, one per vertex of the
region. -/
def stateMembers {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (a : List L) (k : List Nat) :
    List (Option (slotpower.SVec × Pos)) :=
  (List.range R.verts).map (vertexMember F R ix a k)

/-- The slot map of a moved vertex: per occupied end of the moved
configuration at the moved vertex, the source end the link witness
names, its slots matched column by column at the two labels'
columns with the traversal's reversal read at the source key
(`slotpower.transportSlots` at the presentation's column dual) —
each slot of the moved vertex's power at the source slot it reads,
with the tie columns' slot groups at the reversed ends, the star's
at the letters, and the reversed ends' slot groups each at the
source end's orientation, the dual pair's at a member. -/
def slotMap {L : Type} (F : Data L) (R R' : Region) (s : Nat → Nat)
    (rev : Nat → Bool) (a : List L) (x : Nat) (a' : List L) (x' : Nat) :
    List Nat × List (List Nat) × List (List Nat × Bool) :=
  let d := lettersOf F
  let es := carrier.occIncident F R a x
  let es' := carrier.occIncident F R' a' x'
  let cnt := fun (c : List L) (e : Nat × Bool) =>
    let w := wordOf F (getAt F.unit c e.1)
    w.1 + w.2
  let offs := (es.foldl (fun (acc : List Nat × Nat) e =>
    (acc.1 ++ [acc.2], acc.2 + cnt a e)) ([], 0)).1
  (es'.foldl (fun (acc : (List Nat × List (List Nat) × List (List Nat × Bool)) × Nat) e' =>
    let i := places.idxOf (s e'.1) (es.map Prod.fst)
    let r := rev (s e'.1)
    let ts := slotpower.transportSlots F.pres.colDual r
      (slotpower.layoutOf d (colsOf F (getAt F.unit a (s e'.1))) (getAt 0 offs i))
      (slotpower.layoutOf d (colsOf F (getAt F.unit a' e'.1)) acc.2)
    let n := cnt a' e'
    let grp := if r then [((List.range n).map (fun k => acc.2 + k),
      (getAt (0, true) es i).2)] else []
    ((acc.1.1 ++ ts.1, acc.1.2.1 ++ ts.2, acc.1.2.2 ++ grp), acc.2 + n))
    (([], [], []), 0)).1

/-- A link's coevaluation data at its combined signature: the
invariant list, the Gram's adjugate and the determinant
(`fiber.linkList`, `fiber.coevW`). -/
def linkData {L : Type} (F : Data L) (t : L × Option Bool × L) :
    List slotpower.SVec × elim.Mat × BPair :=
  let lg := F.pres.linkList t
  let cw := fiber.coevW lg.2
  (lg.1, cw.1, cw.2)

/-- The window's link keys: per pair of the window's labels, the
unit among them, a boundary link's key, and a label's own off the
boundary. -/
def linkKeys {L : Type} [DecidableEq L] (F : Data L) (ix : List (List L)) :
    List (L × Option Bool × L) :=
  let ls := ground.dedupF (F.unit :: ix.flatMap (fun a => a))
  ground.dedupF (ls.flatMap (fun a =>
    (a, none, a) :: ls.flatMap (fun b => [(a, some true, b), (a, some false, b)])))

/-- The link data read once per key of the window: the store over
the window's keys, the read itself off them. -/
def linkDataAt {L : Type} [DecidableEq L] (F : Data L) (ix : List (List L))
    (t : L × Option Bool × L) : List slotpower.SVec × elim.Mat × BPair :=
  keyAt (fun a b => decide (a = b)) (linkData F t) t
    ((linkKeys F ix).map (fun s => (s, linkData F s)))

/-- The stored read is the link data at every signature. -/
theorem linkDataAt_read {L : Type} [DecidableEq L] (F : Data L)
    (ix : List (List L)) (t : L × Option Bool × L) :
    linkDataAt F ix t = linkData F t :=
  keyAt_memo (fun a b => decide (a = b)) (fun _ _ h => of_decide_eq_true h)
    (linkData F) t (linkKeys F ix)

/-- A link's sub-monomial at a vertex from the three states'
monomials: the source's block, the boundary's and the target's at
their offsets and lengths. -/
def subMon (mi mw mj : List Nat)
    (bl : Nat × Nat × Nat × Nat × Nat × Nat) : List Nat :=
  (mi.drop bl.1).take bl.2.1 ++ (mw.drop bl.2.2.1).take bl.2.2.2.1
    ++ (mj.drop bl.2.2.2.2.1).take bl.2.2.2.2.2

/-- The incident links' blocks at a vertex: per incident end the
source's slot offset and length, the boundary pair's and the
target's, the three states' slots in the incident order. -/
def blocksAt (ws : List (Nat × Nat)) (bd : List (Option Bool)) (ws' : List (Nat × Nat))
    (bl : Nat) : List (Nat × Nat × Nat × Nat × Nat × Nat) :=
  ((List.range ws.length).foldl (fun (acc : List _ × Nat × Nat × Nat) t =>
    let li := (getAt (0, 0) ws t).1 + (getAt (0, 0) ws t).2
    let lw := if (getAt none bd t).isSome then bl else 0
    let lj := (getAt (0, 0) ws' t).1 + (getAt (0, 0) ws' t).2
    (acc.1 ++ [(acc.2.1, li, acc.2.2.1, lw, acc.2.2.2, lj)],
     acc.2.1 + li, acc.2.2.1 + lw, acc.2.2.2 + lj)) ([], 0, 0, 0)).1

/-- The vertex tensor: at every tuple of the incident links'
member indices the three members' pairing against the links'
members at the vertex's combined slots, the coordinate pairing on
the vertex's slot power — one value per tuple in the tuples'
enumeration order, the fold over the three members' monomial
triples with each link's members read once per triple at the
sub-monomial, a triple withdrawn where some link's every read is
the sum's unit (its product with every tuple's further factors the
unit) and the tuples' sums reduced once at the fold's end. -/
def vertexTensor (T : memtable.Table) (uw : Bool) (mi mw mj : slotpower.SVec)
    (blocks : List (Nat × Nat × Nat × Nat × Nat × Nat))
    (Ys : List (List slotpower.SVec)) : List BPair :=
  let triples := mi.flatMap (fun a =>
    mw.flatMap (fun w => mj.map (fun b =>
      ((a.2 * w.2 * b.2).norm, blocks.map (subMon a.1 w.1 b.1)))))
  let tuples := ground.prodLists (Ys.map (fun Y => List.range Y.length))
  (triples.foldl (fun acc tr =>
    let vecs := (List.range Ys.length).map (fun e =>
      let m := getAt [] tr.2 e
      (getAt [] Ys e).map (fun y => slotpower.monDotT T uw m y))
    if vecs.any (fun v => v.all (fun x => decide (x.oneValue BPair.unit))) then acc
    else
      List.zipWith (fun t a =>
        a + tr.1 * (List.range Ys.length).foldl (fun pr e =>
          pr * getAt BPair.unit (getAt [] vecs e) (getAt 0 t e)) (BPair.ofNat 1))
        tuples acc)
    (tuples.map (fun _ => BPair.unit))).map BPair.norm

/-- The contraction's step at a vertex: per open assignment of the
processed links' members and per tuple of the incident links'
members, a link met at its first end opens at the tuple's member
and a link met at its second end closes at the adjugate weight of
its two members, the value the vertex tensor's at the tuple; the
assignments collected at their keys in the keys' order with the
vacant terms withdrawn (`ground.collectBy`). -/
def stepVertex (es : List (Nat × Bool)) (Ys : List (List slotpower.SVec))
    (adjs : List elim.Mat) (pv : List BPair)
    (st : List (List Nat × BPair)) : List (List Nat × BPair) :=
  let tuples := ground.prodLists (Ys.map (fun Y => List.range Y.length))
  let contribs := st.flatMap (fun kv =>
    (List.zipWith (fun t x => (t, x)) tuples pv).filterMap (fun tp =>
      let r := (List.range es.length).foldl (fun (r : List Nat × BPair) e =>
        let l := (getAt (0, false) es e).1
        let i := getAt 0 tp.1 e
        match getAt 0 r.1 l with
        | 0 => (r.1.set l (i + 1), r.2)
        | j + 1 =>
          (r.1.set l 0,
           r.2 * getAt BPair.unit (getAt [] (getAt [] adjs e) j) i))
        (kv.1, kv.2 * tp.2)
      if decide (r.2.oneValue BPair.unit) then none else some (r.1, r.2.norm)))
  ground.collectBy ground.lexLt (fun a b => a == b) contribs

/-- The plaquette term's entry read between two states at stated
members, one pair per vertex: the contraction's value with the
links' determinants' product and the states' vertex clearings'
product, vacant where a member is unstated — the entry
`Eval(x̄ |tr U_∂p|² y)` the value over the determinants and the
clearings. -/
def termEntryAt {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (p : List (Nat × Bool)) (a b : List L)
    (ms : List (Option (slotpower.SVec × Pos) × Option (slotpower.SVec × Pos))) :
    Option (BPair × BPair × Pos) :=
  let T := F.pres.table
  let uw := slotpower.unitWtRead T
  let wth := F.pres.bdryWord
  if ms.all (fun q => q.1.isSome && q.2.isSome) then
    let mem := fun (o : Option (slotpower.SVec × Pos)) =>
      o.getD ([], Pos.one)
    let wa := (List.range R.links).map (fun l => wordOf F (getAt F.unit a l))
    let wb := (List.range R.links).map (fun l => wordOf F (getAt F.unit b l))
    let bd := (List.range R.links).map (fun l =>
      (p.find? (fun e => e.1 == l)).map Prod.snd)
    let ld := (List.range R.links).map (fun l =>
      linkDataAt F ix (getAt F.unit a l, getAt none bd l, getAt F.unit b l))
    let st := (List.range R.verts).foldl (fun st v =>
      let es := incident R v
      let Ys := es.map (fun e => (getAt ([], [], BPair.unit) ld e.1).1)
      let adjs := es.map (fun e => (getAt ([], [], BPair.unit) ld e.1).2.1)
      let q := getAt (none, none) ms v
      let onBd := es.any (fun e => (getAt none bd e.1).isSome)
      let pv := vertexTensor T uw (mem q.1).1
        (if onBd then F.pres.bdry.1 else slotpower.unitV) (mem q.2).1
        (blocksAt (es.map (fun e => getAt (0, 0) wa e.1))
          (es.map (fun e => getAt none bd e.1))
          (es.map (fun e => getAt (0, 0) wb e.1)) (wth.1 + wth.2)) Ys
      stepVertex es Ys adjs pv st)
      [(List.replicate R.links 0, BPair.ofNat 1)]
    some (keyAt (fun a b => a == b) BPair.unit (List.replicate R.links 0) st,
      p.foldl (fun acc _ => acc * F.pres.bdry.2)
        (ld.foldl (fun acc e => acc * e.2.2) (BPair.ofNat 1)),
      ms.foldl (fun acc q => acc * (mem q.1).2 * (mem q.2).2) Pos.one)
  else none

/-- The plaquette term's entry read between two states at their
fiber keys, the members the states' own. -/
def termEntry {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (p : List (Nat × Bool))
    (a : List L) (k : List Nat) (b : List L) (k' : List Nat) :
    Option (BPair × BPair × Pos) :=
  termEntryAt F R ix p a b
    (List.zipWith (fun m m' => (m, m')) (stateMembers F R ix a k)
      (stateMembers F R ix b k'))

/-- A member moved to a vertex: relabeled along the slot map
(`slotpower.relabelV`, the place action); at the letters the tie
columns of the reversed ends read at the star (`slotpower.starAt`)
with the clearing scaled at the columns' factorials, and at a
member every reversed end's slots read at the table's dual pair,
`c W` at a source end outgoing and `cᵀ W` at a source end incoming
with the clearing scaled at the dual pair's clearing squared per
slot (`con:memtable`'s identification of the dual block with the
dual label's block). -/
def moveMember {L : Type} (F : Data L) (R R' : Region) (s : Nat → Nat)
    (rev : Nat → Bool) (a : List L) (x : Nat) (a' : List L) (x' : Nat)
    (m : slotpower.SVec × Pos) : slotpower.SVec × Pos :=
  let d := lettersOf F
  let T := F.pres.table
  let sm := slotMap F R R' s rev a x a' x'
  let v := slotpower.relabelV sm.1 m.1
  match T.dual with
  | none =>
    (sm.2.1.foldl (fun g sl => slotpower.starAt d sl g) v,
     sm.2.1.foldl (fun c sl => c * ground.posOfSucc (ground.factorial sl.length - 1)) m.2)
  | some (c, nu) =>
    let mOut := memtable.smul c T.wt
    let mIn := memtable.smul (memtable.sT c) T.wt
    sm.2.2.foldl (fun (g : slotpower.SVec × Pos) e =>
      (e.1.foldl (fun w sl => slotpower.actT (if e.2 then mOut else mIn) false sl w) g.1,
       if e.2 then g.2 else e.1.foldl (fun cl _ => cl * nu * nu) g.2)) (v, m.2)

/-- A moved state's members: at a vertex the isomorphism reaches,
the source vertex's member moved (`moveMember`); off the image the
untouched vertex's own list's member, the scalar one. -/
def movedMembers {L : Type} (F : Data L) (R R' : Region) (s v w : Nat → Nat)
    (rev : Nat → Bool) (a a' : List L) (ms : List (Option (slotpower.SVec × Pos))) :
    List (Option (slotpower.SVec × Pos)) :=
  (List.range R'.verts).map (fun x' =>
    let x := w x'
    if x < R.verts && v x == x' then
      (getAt none ms x).map (moveMember F R R' s rev a x a' x')
    else
      match F.pres.vertList [] with
      | some l => some (getAt [] l.members.list 0, l.clear)
      | none => none)

/-- The term's transport read at stated moved data: the term's entry
at the moved plaquette between the moved states, the configurations
moved with the members relabeled, is the entry between the states,
one value at the contraction, the determinants and the clearings,
and vacant together. -/
def termTransportAt {L : Type} [DecidableEq L] (F : Data L) (R R' : Region)
    (ix ix' : List (List L)) (t : Nat → Nat) (rev : Nat → Bool)
    (p : List (Nat × Bool)) (a : List L) (k : List Nat) (b : List L)
    (k' : List Nat) (a' b' : List L)
    (ma mb : List (Option (slotpower.SVec × Pos))) : Bool :=
  match termEntry F R ix p a k b k',
    termEntryAt F R' ix' (moveWord t rev p) a' b'
      (List.zipWith (fun m m' => (m, m')) ma mb) with
  | none, none => true
  | none, some _ => false
  | some _, none => false
  | some r, some r' =>
    decide (r.1.oneValue r'.1) && decide (r.2.1.oneValue r'.2.1)
      && decide (r.2.2 = r'.2.2)

/-- The transport read at two stated entries: where the term's
entry between the states and the moved term's entry between the
moved states are stated data, the read is their comparison, the
contraction and the determinants one value and the clearings
equal. -/
theorem termTransportAt_of {L : Type} [DecidableEq L] (F : Data L) (R R' : Region)
    (ix ix' : List (List L)) (t : Nat → Nat) (rev : Nat → Bool)
    (p : List (Nat × Bool)) (a : List L) (k : List Nat) (b : List L)
    (k' : List Nat) (a' b' : List L)
    (ma mb : List (Option (slotpower.SVec × Pos))) (r r' : BPair × BPair × Pos)
    (h : termEntry F R ix p a k b k' = some r)
    (h' : termEntryAt F R' ix' (lattice.moveWord t rev p) a' b'
      (List.zipWith (fun m m' => (m, m')) ma mb) = some r')
    (hc : (decide (r.1.oneValue r'.1) && decide (r.2.1.oneValue r'.2.1)
      && decide (r.2.2 = r'.2.2)) = true) :
    termTransportAt F R R' ix ix' t rev p a k b k' a' b' ma mb = true := by
  unfold termTransportAt
  rw [h, h']
  exact hc

/-- The transport read refused at two stated entries: where the
stated entries' comparison parts, the read is false. -/
theorem termTransportAt_ne {L : Type} [DecidableEq L] (F : Data L) (R R' : Region)
    (ix ix' : List (List L)) (t : Nat → Nat) (rev : Nat → Bool)
    (p : List (Nat × Bool)) (a : List L) (k : List Nat) (b : List L)
    (k' : List Nat) (a' b' : List L)
    (ma mb : List (Option (slotpower.SVec × Pos))) (r r' : BPair × BPair × Pos)
    (h : termEntry F R ix p a k b k' = some r)
    (h' : termEntryAt F R' ix' (lattice.moveWord t rev p) a' b'
      (List.zipWith (fun m m' => (m, m')) ma mb) = some r')
    (hc : (decide (r.1.oneValue r'.1) && decide (r.2.1.oneValue r'.2.1)
      && decide (r.2.2 = r'.2.2)) = false) :
    termTransportAt F R R' ix ix' t rev p a k b k' a' b' ma mb = false := by
  unfold termTransportAt
  rw [h, h']
  exact hc

/-- The term's transport read at two states across a label-graph
isomorphism (`thm:pairpencil`'s transport field): `termTransportAt`
at the configurations moved (`dualConf`) with the states' members
moved (`movedMembers`). -/
def termTransport {L : Type} [DecidableEq L] (F : Data L) (R R' : Region)
    (ix ix' : List (List L)) (t s v w : Nat → Nat) (rev : Nat → Bool)
    (p : List (Nat × Bool)) (a : List L) (k : List Nat) (b : List L)
    (k' : List Nat) : Bool :=
  let a' := dualConf F t s rev R'.links a
  let b' := dualConf F t s rev R'.links b
  termTransportAt F R R' ix ix' t rev p a k b k' a' b'
    (movedMembers F R R' s v w rev a a' (stateMembers F R ix a k))
    (movedMembers F R R' s v w rev b b' (stateMembers F R ix b k'))

/-- The contraction read at a window position pair: at stated
vertex lists the magnetic entry joined to the gram's (the unit's
term where the character reads the trace against its dagger less
the unit), cleared by the links' determinants and the states'
clearings, one value with the window's clearing against the
contraction (`con:fiber`'s magnetic read), and refused at unstated
lists. -/
def contractAt {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (c : Pos) (G M : Mat) (p : List (Nat × Bool))
    (i j : Nat) : Bool :=
  match termEntry F R ix p (posConf F R ix i) (posKey F R ix i)
      (posConf F R ix j) (posKey F R ix j) with
  | some r =>
    decide (((ground.getAt BPair.unit (ground.getAt [] M i) j
        + (if F.pres.lessUnit then ground.getAt BPair.unit (ground.getAt [] G i) j
           else BPair.unit))
        * r.2.1 * BPair.ofPos r.2.2).oneValue (BPair.ofPos c * r.1))
  | none => false

/-- The entry read at a window position pair: at two loops of the
plaquette the loop window's read, the entry the fusion count
`N^x_{θ y}` at the two loop labels at the window's clearing
(`thm:pairpencil`'s loop clause, the orthonormal characters'
value of the contraction), and otherwise the contraction read. -/
def entryAt {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (c : Pos) (G M : Mat) (p : List (Nat × Bool))
    (i j : Nat) : Bool :=
  match loopLabel F R p (posConf F R ix i), loopLabel F R p (posConf F R ix j) with
  | some x, some y =>
    decide ((ground.getAt BPair.unit (ground.getAt [] M i) j).oneValue
      (BPair.ofPos c * BPair.ofNat (F.count F.theta y x)))
  | none, _ => contractAt F R ix c G M p i j
  | some _, none => contractAt F R ix c G M p i j

/-- A plaquette term's entries: every position pair across the
plaquette's changed edge at the entry read, the far pairs the
support read's own. -/
def entriesRead {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (n : Nat) (ix : List (List L)) (c : Pos) (G : Mat)
    (p : List (Nat × Bool)) (M : Mat) : Prop :=
  ((List.range n).all (fun i => (List.range n).all (fun j =>
      !rowPair F R ix p i j || entryAt F R ix c G M p i j))) = true

instance {L : Type} [DecidableEq L] (F : Data L) (R : Region) (n : Nat)
    (ix : List (List L)) (c : Pos) (G : Mat) (p : List (Nat × Bool)) (M : Mat) :
    Decidable (entriesRead F R n ix c G p M) :=
  inferInstanceAs (Decidable (_ = _))

/-- The plaquette terms' reads along the region's plaquette list,
each term with its two cap splits: symmetric, capped two-sidedly at
the adjoint dimension's multiple of the gram (`lem:loopcap`, the
cap reading the term's order), supported across its changed edge,
and its entries the plaquette multiplication's read at the fibers'
stated lists (`con:fiber`'s magnetic read), the loop window's
count at a pair of two loops. -/
def termsRead {L : Type} [DecidableEq L] (F : Data L) (R : Region) (n : Nat)
    (ix : List (List L)) (c : Pos) (G : Mat) :
    List (List (Nat × Bool)) → List (Mat × Split n × Split n) → Prop
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | p :: ps, t :: ts =>
    symmRead t.1
    ∧ capAt t.1 (matScaleB (BPair.ofNat (F.dim F.theta)) G) t.2.1 t.2.2
    ∧ termSupport F R n ix p t.1
    ∧ entriesRead F R n ix c G p t.1
    ∧ termsRead F R n ix c G ps ts

instance decTermsRead {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (n : Nat) (ix : List (List L)) (c : Pos) (G : Mat) :
    (ps : List (List (Nat × Bool))) →
    (ts : List (Mat × Split n × Split n)) →
    Decidable (termsRead F R n ix c G ps ts)
  | [], [] => inferInstanceAs (Decidable True)
  | [], _ :: _ => inferInstanceAs (Decidable False)
  | _ :: _, [] => inferInstanceAs (Decidable False)
  | _ :: ps, _ :: ts =>
    have : Decidable (termsRead F R n ix c G ps ts) :=
      decTermsRead F R n ix c G ps ts
    inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The terms' count is the plaquettes' at the terms' reads. -/
theorem termsRead_len {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (n : Nat) (ix : List (List L)) (c : Pos) (G : Mat) :
    ∀ (ps : List (List (Nat × Bool))) (ts : List (Mat × Split n × Split n)),
      termsRead F R n ix c G ps ts → ts.length = ps.length
  | [], [], _ => rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: ps, _ :: ts, h =>
    congrArg Nat.succ (termsRead_len F R n ix c G ps ts h.2.2.2.2)

/-- Each term is square at the order, the cap's own shape read. -/
theorem termsRead_sq {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (n : Nat) (ix : List (List L)) (c : Pos) (G : Mat) :
    ∀ (ps : List (List (Nat × Bool))) (ts : List (Mat × Split n × Split n)),
      termsRead F R n ix c G ps ts → ∀ k, k < ts.length →
        sqAt (ground.getAt [] (ts.map Prod.fst) k) n
  | [], [], _, _, hk => absurd hk (Nat.not_lt_zero _)
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim
  | _ :: _, _ :: _, h, 0, _ => h.2.1.1
  | _ :: ps, _ :: ts, h, k + 1, hk =>
    termsRead_sq F R n ix c G ps ts h.2.2.2.2 k (Nat.lt_of_succ_lt_succ hk)

/-- The plaquette terms' sum, the magnetic member assembled from
its terms at the order: `elim.msum`'s index fold over the terms'
keys. -/
def termSum (n : Nat) (terms : List (Mat × Split n × Split n)) : Mat :=
  elim.msum n (ground.getAt [] (terms.map Prod.fst)) (List.range terms.length)

/-- The pencil interface's read at a window: the stated index the
window's own, the order tie at the window list's count, the
electric member the gram's form at the window list's diagonal, the
gram's block read at a stated clearing and at its positive-definite
split (the split reading the gram's order), the plaquette terms'
reads along the region's plaquettes,
and the magnetic member square at the order and one value with
the plaquette terms' sum —
`thm:pairpencil`'s fields at a stated pencil over the stated
index. -/
def pencilRead {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (C n : Nat) (ix : List (List L)) (c : Pos) (E G M : Mat) (spG : Split n)
    (terms : List (Mat × Split n × Split n)) : Prop :=
  carrier.idx F R C = ix
  ∧ windowfinite.dimSect F R C = n
  ∧ sqAt E n
  ∧ matOneValue E (formE (slotDiag F R ix) G)
  ∧ gramBlockRead F R n ix c G ∧ splitRead G spG ∧ pdAt spG
  ∧ termsRead F R n ix c G R.plaqs terms
  ∧ sqAt M n
  ∧ matOneValue M (termSum n terms)

instance {L : Type} [DecidableEq L] (F : Data L) (R : Region) (C n : Nat)
    (ix : List (List L)) (c : Pos) (E G M : Mat) (spG : Split n)
    (terms : List (Mat × Split n × Split n)) :
    Decidable (pencilRead F R C n ix c E G M spG terms) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

end pairpencil
