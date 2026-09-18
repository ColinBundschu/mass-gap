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
`blocksAt` and the sub-monomials `subMon`, the pairing the
sub-monomial's coefficient in the link member applied at the
table's weight, `slotpower.applyWt` once per member, the members
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
and `colsOf` at the field's column dual, the member read through
the identification along it, `slotpower.identifyV` with its
clearing `slotpower.identifyClear`: the place action along the
map, the star at the tie columns of the reversed ends with the
clearing scaled at their factorials at the letters, and the
table's dual pair at every reversed slot at a member at the pair's
clearing per slot, the pairing scaled at its square — the term's
entry at
the moved states one value with the entry at the states,
`termTransportAt` at stated moved data and `termEntryAt` the
contraction at stated members), the region's own action's instance
over the window list in the module that owns the action, and the
whole `pencilRead` at the fields this module owns, every read at a
stated index tied to the window's own; at a loop
window the fields read off the fusion counts, `loopMag` the
magnetic term with the identity gram, the check module's pins.  The
window positions whose configuration reads a stated predicate are
`placesAt`, position nought at the unit configuration, and the slot
diagonal at a position is its configuration's content
(`slotDiag_posConf`).  The terms' sum at a joined term is the term
added to the further terms' sum (`termSum_cons`), square and
symmetric at the terms' reads (`termSum_read`), and
`thm:truncation`'s magnetic cap is the terms' summed
(`termSum_cap`: the terms' sum capped two-sidedly at the terms'
count times the closure's dimension fold against the gram, the fold
the adjoint dimension at the adjoint list,
`inertia.capAt_add` one term at a time); and the removed block's
floor is the electric member's read at the contents
(`removed_floor`: at stated positions whose contents sit at or beyond
a stated floor, the removed block's own among them, the electric
member less the floor's multiple of the gram reads every split
positive semidefinite,
`inertia.blockScaled_psd` at the positions grouped by configuration,
the gram's cross entries at the sum's unit across configurations at a
label domain with one spelling per label).  The pencil's nesting
read is `thm:truncation`'s projection at the window's positions: the
head places, the positions at content at or below the truncation
cutoff with the unit line among them, and the removed places, the
rest (`headPlaces`, `remPlaces`); the window list at the index
filtered at a configuration read is the window list filtered at the
read (`slotList_filter`, `slotList_places`, a member at its kept
position `slotList_head`), so the head places enumerate the
truncated index's own window list in order (`posConf_head`,
`posKey_head`, the truncated order at `length_headPlaces`); the
head and removed places partition the order (`places_perm`) at
their contents (`places_content`); the gram and the electric form
join at the places with the cross block the null matrix
(`gram_nest` at `def:carrier`'s orthogonal sum, `elec_nest`, two
positions at distinct contents at distinct configurations), the
electric form symmetric (`formE_symm`), the magnetic member joins
with its coupling (`mag_nest`), and the removed block's floor reads
the cutoff's successor (`removed_nest`).  The electric form's shape
and entries are `sqAt_formE`, `formE_entry` and `formE_entry_unit`,
the slot diagonal's count `length_slotDiag`.
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

/-- The slot diagonal's count is the window list's with the unit
line. -/
theorem length_slotDiag {L : Type} (F : Data L) (R : Region) (ix : List (List L)) :
    (slotDiag F R ix).length = (slotList F R ix).length + 1 := by
  show ((slotList F R ix).map (fun p => carrier.contentN F p.1)).length + 1 = _
  rw [length_map]

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

/-- Every position's configuration reads a label domain holding the
unit at every index member's labels: the unit configuration at
position nought, a window list member past it, and a position past
the order at the unit configuration. -/
theorem posConf_labels {L : Type} (F : Data L) (R : Region)
    (ix : List (List L)) (P : L → Bool) (hunitP : P F.unit = true)
    (hix : ∀ a, a ∈ ix → a.all P = true) :
    ∀ i, (posConf F R ix i).all P = true
  | 0 => all_of_mem_intro P _ (fun l hl => by
      rw [mem_replicate_eq F.unit R.links l hl]
      exact hunitP)
  | k + 1 => by
    show ((getAt (carrier.unitConf F R, []) (slotList F R ix) k).1).all P = true
    cases Nat.lt_or_ge k (slotList F R ix).length with
    | inl hk =>
      exact hix _ (mem_slotList_of F R ix _
        (mem_getAt (carrier.unitConf F R, []) _ k hk)).1
    | inr hk =>
      rw [getAt_over _ _ k hk]
      exact all_of_mem_intro P _ (fun l hl => by
        rw [mem_replicate_eq F.unit R.links l hl]
        exact hunitP)

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

/-- The electric form is square at its diagonal's count. -/
theorem sqAt_formE (diag : List Nat) (G : Mat) (n : Nat) (hdl : diag.length = n) :
    sqAt (formE diag G) n :=
  sqAt_of ((ground.matOf_length _ _ _).trans hdl) (rowsLen_cast hdl (rowsLen_matOf _ _ _))

/-- The electric form's entry: the row's content against the gram's
entry, at the pair's canonical read. -/
theorem formE_entry (diag : List Nat) (G : Mat) (i j : Nat)
    (hi : i < diag.length) (hj : j < diag.length) :
    ground.getAt BPair.unit (ground.getAt [] (formE diag G) i) j
      = (BPair.ofNat (ground.getAt 0 diag i)
          * ground.getAt BPair.unit (ground.getAt [] G i) j).norm :=
  ground.matOf_entry [] BPair.unit _ _ _ i j hi hj

/-- The electric form's entry reads the sum's unit where the gram's
does. -/
theorem formE_entry_unit (diag : List Nat) (G : Mat) (i j : Nat)
    (hi : i < diag.length) (hj : j < diag.length)
    (h : (ground.getAt BPair.unit (ground.getAt [] G i) j).oneValue BPair.unit) :
    (ground.getAt BPair.unit (ground.getAt [] (formE diag G) i) j).oneValue BPair.unit := by
  rw [formE_entry diag G i j hi hj]
  exact BPair.oneValue_trans (BPair.norm_oneValue _) (oneValue_mul_unit _ _ h)

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

/-- Every store entry holds the field's value at its key, the store
built by joins at the field's own reads. -/
private theorem endsStore_mem {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) :
    ∀ e, e ∈ endsStore F R ix → e.2 = F.pres.vertList e.1 := by
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
  exact hst (carrier.unitConf F R :: ix) [] (fun _ h => nomatch h)

/-- The stored read is the field's (`endsStore_mem`). -/
theorem vertListAt_read {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (es : List (L × Bool)) :
    vertListAt F R ix es = F.pres.vertList es :=
  keyAt_store (fun a b => decide (a = b)) (fun _ _ h => of_decide_eq_true h)
    F.pres.vertList es _ (endsStore_mem F R ix)

/-- The vertex Grams read once per incident-end list of the window,
the vertex-list store's lists at their Grams (`fiber.listGram`). -/
def gramStore {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) : List (List (L × Bool) × Option (Mat × Pos)) :=
  (endsStore F R ix).map (fun e => (e.1, e.2.map fiber.listGram))

/-- The vertex Gram at an incident-end list through the window's
Gram store: the list's own Gram where the list is stated, the
two-end coevaluation's count at the label data off it
(`fusion.vertGramOf` at the stored read; `vertGramAt_read` its
read as the field's list's Gram). -/
def vertGramAt {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (es : List (L × Bool)) : Option (Mat × Pos) :=
  match keyAt (fun a b => decide (a = b)) ((F.pres.vertList es).map fiber.listGram) es
      (gramStore F R ix) with
  | some g => some g
  | none => fiber.twoEndGram F.eqL F.dual F.dim es

/-- The stored Gram is the field's list's Gram at every incident-end
list, the store's entries the field's own (`endsStore_mem`). -/
theorem vertGramAt_read {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (es : List (L × Bool)) :
    vertGramAt F R ix es
      = (match (F.pres.vertList es).map fiber.listGram with
        | some g => some g
        | none => fiber.twoEndGram F.eqL F.dual F.dim es) := by
  have h : keyAt (fun a b => decide (a = b)) ((F.pres.vertList es).map fiber.listGram) es
      (gramStore F R ix) = (F.pres.vertList es).map fiber.listGram :=
    keyAt_store (fun a b => decide (a = b)) (fun _ _ h => of_decide_eq_true h)
      (fun es => (F.pres.vertList es).map fiber.listGram) es _ (fun e he => by
        obtain ⟨e', he', hee⟩ := ground.mem_map_of _ _ e he
        rw [← hee]
        show e'.2.map fiber.listGram = (F.pres.vertList e'.1).map fiber.listGram
        rw [endsStore_mem F R ix e' he'])
  show (match keyAt (fun a b => decide (a = b)) ((F.pres.vertList es).map fiber.listGram) es
      (gramStore F R ix) with
    | some g => some g
    | none => fiber.twoEndGram F.eqL F.dual F.dim es) = _
  rw [h]

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

instance instPairpencil1 {L : Type} [DecidableEq L] (F : Data L) (R : Region) (n : Nat)
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

instance instPairpencil2 {L : Type} (F : Data L) (R : Region) (n : Nat) (ix : List (List L))
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
    Option (slotpower.WVec × Pos) :=
  match vertListAt F R ix (carrier.incidentEnds F R a v) with
  | none => none
  | some l =>
    some (⟨_, getAt (slotpower.emptyV _) l.members.list (getAt 0 k v)⟩, l.clear)

/-- A state's members at its fiber key, one per vertex of the
region. -/
def stateMembers {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (a : List L) (k : List Nat) :
    List (Option (slotpower.WVec × Pos)) :=
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
invariant list, the list applied at the table's weight
(`slotpower.applyWt`, the list itself at the unit weight), the
Gram's adjugate and the determinant (`fiber.linkList`,
`fiber.coevW`). -/
def linkData {L : Type} (F : Data L) (t : L × Option Bool × L) :
    slotpower.WList × slotpower.WList × elim.Mat × BPair :=
  let lg := F.pres.linkList t
  let cw := fiber.coevW lg.2
  (lg.1,
   ⟨lg.1.1, if slotpower.unitWtRead F.pres.table then lg.1.2
     else lg.1.2.map (slotpower.applyWt F.pres.table)⟩,
   cw.1, cw.2)

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
    (t : L × Option Bool × L) : slotpower.WList × slotpower.WList × elim.Mat × BPair :=
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
enumeration order, the links' members entering applied at the
table's weight (`slotpower.applyWt` at the link data,
`slotpower.monDotT_apply`), the fold over the three members'
monomial triples with each link's members read at the triple's
sub-monomial's coefficient (`slotpower.coefAt`), a triple withdrawn
where some link's every read is the sum's unit (its product with
every tuple's further factors the unit) and the tuples' sums
reduced once at the fold's end. -/
def vertexTensor (mi mw mj : slotpower.WVec)
    (blocks : List (Nat × Nat × Nat × Nat × Nat × Nat))
    (Ys : List slotpower.WList) : List BPair :=
  let triples := mi.2.val.flatMap (fun a =>
    mw.2.val.flatMap (fun w => mj.2.val.map (fun b =>
      ((a.2 * w.2 * b.2).norm, blocks.map (subMon a.1 w.1 b.1)))))
  let tuples := ground.prodLists (Ys.map (fun Y => List.range Y.2.length))
  (triples.foldl (fun acc tr =>
    let vecs := (List.range Ys.length).map (fun e =>
      (getAt ⟨0, []⟩ Ys e).2.map (fun y => slotpower.coefAt (getAt [] tr.2 e) y))
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
def stepVertex (es : List (Nat × Bool)) (Ys : List slotpower.WList)
    (adjs : List elim.Mat) (pv : List BPair)
    (st : List (List Nat × BPair)) : List (List Nat × BPair) :=
  let tuples := ground.prodLists (Ys.map (fun Y => List.range Y.2.length))
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
    (ms : List (Option (slotpower.WVec × Pos) × Option (slotpower.WVec × Pos))) :
    Option (BPair × BPair × Pos) :=
  let wth := F.pres.bdryWord
  if ms.all (fun q => q.1.isSome && q.2.isSome) then
    let mem := fun (o : Option (slotpower.WVec × Pos)) =>
      o.getD (⟨0, slotpower.emptyV 0⟩, Pos.one)
    let wa := (List.range R.links).map (fun l => wordOf F (getAt F.unit a l))
    let wb := (List.range R.links).map (fun l => wordOf F (getAt F.unit b l))
    let bd := (List.range R.links).map (fun l =>
      (p.find? (fun e => e.1 == l)).map Prod.snd)
    let ld := (List.range R.links).map (fun l =>
      linkDataAt F ix (getAt F.unit a l, getAt none bd l, getAt F.unit b l))
    let st := (List.range R.verts).foldl (fun st v =>
      let es := incident R v
      let Ys := es.map (fun e => (getAt (⟨0, []⟩, ⟨0, []⟩, [], BPair.unit) ld e.1).2.1)
      let adjs := es.map (fun e => (getAt (⟨0, []⟩, ⟨0, []⟩, [], BPair.unit) ld e.1).2.2.1)
      let q := getAt (none, none) ms v
      let onBd := es.any (fun e => (getAt none bd e.1).isSome)
      let pv := vertexTensor (mem q.1).1
        (if onBd then F.pres.bdry.1 else ⟨0, slotpower.unitV⟩) (mem q.2).1
        (blocksAt (es.map (fun e => getAt (0, 0) wa e.1))
          (es.map (fun e => getAt none bd e.1))
          (es.map (fun e => getAt (0, 0) wb e.1)) (wth.1 + wth.2)) Ys
      stepVertex es Ys adjs pv st)
      [(List.replicate R.links 0, BPair.ofNat 1)]
    some (keyAt (fun a b => a == b) BPair.unit (List.replicate R.links 0) st,
      p.foldl (fun acc _ => acc * F.pres.bdry.2)
        (ld.foldl (fun acc e => acc * e.2.2.2) (BPair.ofNat 1)),
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
    (m : slotpower.WVec × Pos) : slotpower.WVec × Pos :=
  let d := lettersOf F
  let T := F.pres.table
  let sm := slotMap F R R' s rev a x a' x'
  (⟨_, slotpower.identifyV d T sm.1 sm.2.1 sm.2.2 m.1.2⟩,
   slotpower.identifyClear T sm.2.1 sm.2.2 m.2)

/-- A moved state's members: at a vertex the isomorphism reaches,
the source vertex's member moved (`moveMember`); off the image the
untouched vertex's own list's member, the scalar one. -/
def movedMembers {L : Type} (F : Data L) (R R' : Region) (s v w : Nat → Nat)
    (rev : Nat → Bool) (a a' : List L) (ms : List (Option (slotpower.WVec × Pos))) :
    List (Option (slotpower.WVec × Pos)) :=
  (List.range R'.verts).map (fun x' =>
    let x := w x'
    if x < R.verts && v x == x' then
      (getAt none ms x).map (moveMember F R R' s rev a x a' x')
    else
      match F.pres.vertList [] with
      | some l => some (⟨_, getAt (slotpower.emptyV _) l.members.list 0⟩, l.clear)
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
    (ma mb : List (Option (slotpower.WVec × Pos))) : Bool :=
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
    (ma mb : List (Option (slotpower.WVec × Pos))) (r r' : BPair × BPair × Pos)
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
    (ma mb : List (Option (slotpower.WVec × Pos))) (r r' : BPair × BPair × Pos)
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

/-- The entry read at two loops of the plaquette: the entry is the
fusion count `N^x_{θ y}` at the two loop labels at the window's
clearing (`thm:pairpencil`'s loop clause). -/
theorem entryAt_loop {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (c : Pos) (G M : Mat) (p : List (Nat × Bool))
    (i j : Nat) (x y : L)
    (hx : loopLabel F R p (posConf F R ix i) = some x)
    (hy : loopLabel F R p (posConf F R ix j) = some y)
    (h : entryAt F R ix c G M p i j = true) :
    (ground.getAt BPair.unit (ground.getAt [] M i) j).oneValue
      (BPair.ofPos c * BPair.ofNat (F.count F.theta y x)) := by
  unfold entryAt at h
  rw [hx, hy] at h
  exact of_decide_eq_true h

/-- A plaquette term's entries: every position pair across the
plaquette's changed edge at the entry read, the far pairs the
support read's own. -/
def entriesRead {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (n : Nat) (ix : List (List L)) (c : Pos) (G : Mat)
    (p : List (Nat × Bool)) (M : Mat) : Prop :=
  ((List.range n).all (fun i => (List.range n).all (fun j =>
      !rowPair F R ix p i j || entryAt F R ix c G M p i j))) = true

instance instPairpencil3 {L : Type} [DecidableEq L] (F : Data L) (R : Region) (n : Nat)
    (ix : List (List L)) (c : Pos) (G : Mat) (p : List (Nat × Bool)) (M : Mat) :
    Decidable (entriesRead F R n ix c G p M) :=
  inferInstanceAs (Decidable (_ = _))

/-- The plaquette terms' reads along the region's plaquette list,
each term with its two cap splits: symmetric, capped two-sidedly at
the closure's dimension fold's multiple of the gram, the fold the
adjoint dimension at the adjoint list (`lem:loopcap`, the cap
reading the term's order), supported across its changed edge,
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

/-- The terms' sum at a joined term: the term added to the further
terms' sum (`elim.msum_range_cons` at the terms' keys). -/
theorem termSum_cons (n : Nat) (t : Mat × Split n × Split n)
    (ts : List (Mat × Split n × Split n)) :
    termSum n (t :: ts) = matAdd t.1 (termSum n ts) := by
  show elim.msum n (ground.getAt [] (t.1 :: ts.map Prod.fst)) (List.range (ts.length + 1))
    = matAdd t.1 (elim.msum n (ground.getAt [] (ts.map Prod.fst)) (List.range ts.length))
  rw [elim.msum_range_cons]
  rfl

/-- The terms' sum at the terms' reads in one pass: square at the
order and symmetric (the sum's shape and symmetry the summands' own,
`elim.symmRead_matAdd`), and at a square symmetric gram capped
two-sidedly at the terms' count times the closure's dimension fold
against the gram, the terms' caps summed one at a time
(`inertia.capAt_add`), the partial sums' splits the construction's
own (`inertia.mkSplit`), and at the vacant term list the null matrix
at the vacant weight. -/
private theorem termSum_all {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (n : Nat) (ix : List (List L)) (c : Pos) (G : Mat) :
    ∀ (ps : List (List (Nat × Bool))) (ts : List (Mat × Split n × Split n)),
      termsRead F R n ix c G ps ts →
      (sqAt (termSum n ts) n ∧ symmRead (termSum n ts))
      ∧ (sqAt G n → symmRead G → ∀ (spU spL : Split n),
        splitRead (siteDatum (matScaleB (BPair.ofNat (ts.length * F.dim F.theta)) G)
          (termSum n ts)) spU →
        splitRead (matAdd (matScaleB (BPair.ofNat (ts.length * F.dim F.theta)) G)
          (termSum n ts)) spL →
        capAt (termSum n ts) (matScaleB (BPair.ofNat (ts.length * F.dim F.theta)) G) spU spL)
  | [], [], _ => by
    refine ⟨⟨elim.sqAt_of (elim.length_nullMat n n) (elim.rowsLen_nullMat n n),
      elim.symmRead_nullMat n⟩, fun hG _ spU spL hU hL => ?_⟩
    have hN : elim.matNull (matScaleB (BPair.ofNat (0 * F.dim F.theta)) G) := by
      rw [Nat.zero_mul]
      exact inertia.matNull_scaleB_unit BPair.ofNat_zero G
    have hnull : elim.matNull (termSum n []) := elim.matNull_nullMat n n
    have hform : ∀ (X : Mat), elim.matNull X → ∀ u : List BPair, u.length = n →
        BPair.unit ≤ dotN u (matVec X u) := fun X hX u _ =>
      ground.leB_congr_right (BPair.oneValue_symm
        (elim.dotN_nullR u _ (elim.matVec_matNull X u hX))) (ground.leB_refl _)
    refine ⟨elim.sqAt_of (elim.length_nullMat n n) (elim.rowsLen_nullMat n n),
      inertia.sqAt_scaleB _ n G hG, ⟨hU, ?_⟩, hL, ?_⟩
    · exact inertia.psdAt_of_form _ spU
        (hform _ (elim.matNull_matAdd hN (elim.matNull_matSwap _ hnull))) hU
    · exact inertia.psdAt_of_form _ spL (hform _ (elim.matNull_matAdd hN hnull)) hL
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: ps, t :: ts, h => by
    obtain ⟨hsym, hcap, _, _, hrest⟩ := h
    have ihAll := termSum_all F R n ix c G ps ts hrest
    obtain ⟨hS2, hS2s⟩ := ihAll.1
    refine ⟨?_, fun hG hGs spU spL hU hL => ?_⟩
    · rw [termSum_cons n t ts]
      exact ⟨elim.sqAt_matAdd n _ _ hcap.1 hS2,
        elim.symmRead_matAdd n _ _ hcap.1 hS2 hsym hS2s⟩
    have hC2 : sqAt (matScaleB (BPair.ofNat (ts.length * F.dim F.theta)) G) n :=
      inertia.sqAt_scaleB _ n G hG
    have hC2s : symmRead (matScaleB (BPair.ofNat (ts.length * F.dim F.theta)) G) :=
      inertia.symmRead_matScaleB _ n G hG hGs
    have hC1 : sqAt (matScaleB (BPair.ofNat (F.dim F.theta)) G) n :=
      inertia.sqAt_scaleB _ n G hG
    have hU2 := inertia.mkSplit_read n
      (siteDatum (matScaleB (BPair.ofNat (ts.length * F.dim F.theta)) G) (termSum n ts))
      (inertia.sqAt_siteDatum n _ _ hC2 hS2)
      (elim.matOne_symm (inertia.symmRead_siteDatum n _ _ hC2 hS2 hC2s hS2s))
    have hL2 := inertia.mkSplit_read n
      (matAdd (matScaleB (BPair.ofNat (ts.length * F.dim F.theta)) G) (termSum n ts))
      (elim.sqAt_matAdd n _ _ hC2 hS2)
      (elim.matOne_symm (elim.symmRead_matAdd n _ _ hC2 hS2 hC2s hS2s))
    have ih := ihAll.2 hG hGs _ _ hU2 hL2
    -- the caps' sum at the joined weight
    have hCsum : matOneValue
        (matAdd (matScaleB (BPair.ofNat (F.dim F.theta)) G)
          (matScaleB (BPair.ofNat (ts.length * F.dim F.theta)) G))
        (matScaleB (BPair.ofNat ((ts.length + 1) * F.dim F.theta)) G) := by
      refine elim.matOne_trans (inertia.matScaleB_add _ _ G) ?_
      refine inertia.matScaleB_congr ?_ G
      refine BPair.oneValue_symm (BPair.oneValue_trans ?_ (BPair.ofNat_add _ _))
      rw [Nat.succ_mul, Nat.add_comm]
      exact BPair.oneValue_refl _
    have hSsum : matOneValue (matAdd t.1 (termSum n ts)) (termSum n (t :: ts)) := by
      rw [termSum_cons n t ts]
      exact elim.matOne_refl _
    have hCsq : sqAt (matAdd (matScaleB (BPair.ofNat (F.dim F.theta)) G)
        (matScaleB (BPair.ofNat (ts.length * F.dim F.theta)) G)) n :=
      elim.sqAt_matAdd n _ _ hC1 hC2
    have hSsq : sqAt (matAdd t.1 (termSum n ts)) n := elim.sqAt_matAdd n _ _ hcap.1 hS2
    have hCsq' : sqAt (matScaleB (BPair.ofNat ((ts.length + 1) * F.dim F.theta)) G) n :=
      inertia.sqAt_scaleB _ n G hG
    have hSsq' : sqAt (termSum n (t :: ts)) n := by
      rw [termSum_cons n t ts]; exact hSsq
    have hsiteOV : matOneValue
        (siteDatum (matAdd (matScaleB (BPair.ofNat (F.dim F.theta)) G)
            (matScaleB (BPair.ofNat (ts.length * F.dim F.theta)) G))
          (matAdd t.1 (termSum n ts)))
        (siteDatum (matScaleB (BPair.ofNat ((ts.length + 1) * F.dim F.theta)) G)
          (termSum n (t :: ts))) :=
      elim.matAdd_cong2 n _ _ _ _ (elim.rowsLen_of_sqAt hCsq)
        (elim.rowsLen_mapRows BPair.swap _ n (elim.rowsLen_of_sqAt hSsq))
        (elim.rowsLen_of_sqAt hCsq')
        (elim.rowsLen_mapRows BPair.swap _ n (elim.rowsLen_of_sqAt hSsq'))
        hCsum (elim.matSwap_congr hSsum)
    have haddOV : matOneValue
        (matAdd (matAdd (matScaleB (BPair.ofNat (F.dim F.theta)) G)
            (matScaleB (BPair.ofNat (ts.length * F.dim F.theta)) G))
          (matAdd t.1 (termSum n ts)))
        (matAdd (matScaleB (BPair.ofNat ((ts.length + 1) * F.dim F.theta)) G)
          (termSum n (t :: ts))) :=
      elim.matAdd_cong2 n _ _ _ _ (elim.rowsLen_of_sqAt hCsq) (elim.rowsLen_of_sqAt hSsq)
        (elim.rowsLen_of_sqAt hCsq') (elim.rowsLen_of_sqAt hSsq') hCsum hSsum
    have hU' := inertia.splitRead_congr _ _ (inertia.sqAt_siteDatum n _ _ hCsq hSsq)
      (elim.matOne_symm hsiteOV) spU hU
    have hL' := inertia.splitRead_congr _ _ (elim.sqAt_matAdd n _ _ hCsq hSsq)
      (elim.matOne_symm haddOV) spL hL
    have hadd := inertia.capAt_add t.1 (matScaleB (BPair.ofNat (F.dim F.theta)) G)
      (termSum n ts) (matScaleB (BPair.ofNat (ts.length * F.dim F.theta)) G)
      t.2.1 t.2.2 _ _ spU spL hcap ih hU' hL'
    exact inertia.capAt_congr _ _ _ _ spU spL hadd hSsq' hCsq' hSsum hCsum

/-- The terms' sum is square at the order and symmetric at the terms'
reads, the sum's shape and symmetry the summands' own
(`termsRead`'s shape and symmetry conjuncts; `elim.symmRead_matAdd`). -/
theorem termSum_read {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (n : Nat) (ix : List (List L)) (c : Pos) (G : Mat) :
    ∀ (ps : List (List (Nat × Bool))) (ts : List (Mat × Split n × Split n)),
      termsRead F R n ix c G ps ts →
        sqAt (termSum n ts) n ∧ symmRead (termSum n ts) :=
  fun ps ts h => (termSum_all F R n ix c G ps ts h).1

/-- The magnetic member's cap from the terms' (`thm:truncation`: each
plaquette term capped two-sidedly as a form at the closure's
dimension fold, so the sum is capped two-sidedly, the closure's
dimension fold times the region's plaquette count): the terms' sum
is capped at the terms' count times the closure's dimension fold
against the gram, the fold the adjoint dimension at the adjoint
list, the terms' caps summed one at a time
(`inertia.capAt_add`, `lem:inertia`'s sum of two-sided caps). -/
theorem termSum_cap {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (n : Nat) (ix : List (List L)) (c : Pos) (G : Mat)
    (hG : sqAt G n) (hGs : symmRead G) :
    ∀ (ps : List (List (Nat × Bool))) (ts : List (Mat × Split n × Split n)),
      termsRead F R n ix c G ps ts →
      ∀ (spU spL : Split n),
        splitRead (siteDatum (matScaleB (BPair.ofNat (ts.length * F.dim F.theta)) G)
          (termSum n ts)) spU →
        splitRead (matAdd (matScaleB (BPair.ofNat (ts.length * F.dim F.theta)) G)
          (termSum n ts)) spL →
        capAt (termSum n ts) (matScaleB (BPair.ofNat (ts.length * F.dim F.theta)) G) spU spL :=
  fun ps ts h => (termSum_all F R n ix c G ps ts h).2 hG hGs

/-- The window positions whose configuration reads a stated
predicate, position nought read at the unit configuration. -/
def placesAt {L : Type} (F : Data L) (R : Region) (ix : List (List L))
    (n : Nat) (P : List L → Bool) : List Nat :=
  (List.range n).filter (fun i => P (posConf F R ix i))

/-- The slot diagonal at a position is its configuration's content:
the unit line at the unit configuration's, a window list member's
at its own. -/
theorem slotDiag_posConf {L : Type} (F : Data L) (R : Region) (ix : List (List L)) :
    ∀ i, i < (slotList F R ix).length + 1 →
      ground.getAt 0 (slotDiag F R ix) i = carrier.contentN F (posConf F R ix i)
  | 0, _ => by
    show 0 = carrier.contentN F (carrier.unitConf F R)
    rw [carrier.contentN_unitConf F R]
  | k + 1, hk => by
    show ground.getAt 0 ((slotList F R ix).map (fun p => carrier.contentN F p.1)) k
      = carrier.contentN F (ground.getAt (carrier.unitConf F R, []) (slotList F R ix) k).1
    exact ground.getAt_map (carrier.unitConf F R, []) 0 _ _ k (Nat.lt_of_succ_lt_succ hk)

/-- The weight `⟨a : c⟩` at a natural at or beyond the positive's value
sits on its upper side. -/
private theorem unitLe_ofNat_swap (a : Nat) (c : Pos) (h : posVal c ≤ a) :
    BPair.unit ≤ BPair.ofNat a + (BPair.ofPos c).swap := by
  have h1 : BPair.ofNat (posVal c) ≤ BPair.ofNat a := ground.leB_ofNat h
  have h1' : (BPair.ofNat (posVal c)).fst + (BPair.ofNat a).snd
      ≤ (BPair.ofNat a).fst + (BPair.ofNat (posVal c)).snd := h1
  show Pos.one + ((BPair.ofNat a).snd + (BPair.ofNat (posVal c)).fst)
    ≤ (BPair.ofNat a).fst + (BPair.ofNat (posVal c)).snd + Pos.one
  rw [ground.add_comm Pos.one, ground.add_comm ((BPair.ofNat a).snd) _]
  exact ground.posLeAdd h1' (Or.inl rfl)

/-- The removed block's floor (`thm:truncation`: the removed block's
electric diagonal sits at or above the cutoff): at the positions
whose content sits at or beyond a stated floor, the electric member
less the floor's multiple of the gram reads every split positive
semidefinite — the electric member the gram's form at the contents,
a positive-semidefinite gram scaled groupwise at the positions'
configurations (`inertia.blockScaled_psd` at the positions grouped
by configuration, `elim.placesBy`), the cross entries at the sum's
unit across configurations (`gramBlockRead` at a label domain with
one spelling per label) and the weights at the contents against the
floor on their upper side at the places. -/
theorem removed_floor {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (n : Nat) (ix : List (List L)) (c : Pos) (G : Mat)
    (hnl : (slotList F R ix).length + 1 = n)
    (hG : sqAt G n) (spG : Split n) (hGr : splitRead G spG) (hGp : psdAt spG)
    (hgram : gramBlockRead F R n ix c G)
    (P : L → Bool) (hunitP : P F.unit = true)
    (hix : ∀ a, a ∈ ix → a.all P = true)
    (hred : ∀ x y, P x = true → P y = true → F.eqL x y = true → x = y)
    (cf : Pos) (rem : List Nat) (hb : (rem.all (fun i => Nat.blt i n)) = true)
    (hk0 : 0 < rem.length)
    (hcont : ∀ i, i ∈ rem → posVal cf ≤ carrier.contentN F (posConf F R ix i))
    (sp : Split rem.length)
    (hsp : splitRead (siteDatum (selM rem rem (formE (slotDiag F R ix) G))
      (matScale cf (selM rem rem G))) sp) :
    psdAt sp := by
  have hn : 0 < n := by rw [← hnl]; exact Nat.succ_pos _
  have hdl : (slotDiag F R ix).length = n := by rw [length_slotDiag]; exact hnl
  have hE : sqAt (formE (slotDiag F R ix) G) n := sqAt_formE _ G n hdl
  have hX : sqAt (siteDatum (formE (slotDiag F R ix) G) (matScale cf G)) n :=
    inertia.sqAt_siteDatum n _ _ hE (inertia.sqAt_matScale n cf G hG)
  -- the split at the selected site datum
  have hsp' : splitRead (selM rem rem
      (siteDatum (formE (slotDiag F R ix) G) (matScale cf G))) sp :=
    inertia.splitRead_congr _ _
      (elim.sqAt_of (elim.length_selM _ _ _) (elim.rowsLen_selM _ _ _))
      (inertia.selM_site_scale _ _ G cf n hE hG hb) sp hsp
  -- the groups by configuration
  have hpart := elim.placesBy_partition (fun i => posConf F R ix i) n
  have hlab : ∀ i, (posConf F R ix i).all P = true := posConf_labels F R ix P hunitP hix
  have hcrossG := (ground.all_range_read n hgram.2.1)
  refine inertia.blockScaled_psd G _ hG hX hn spG hGr hGp
    (elim.placesBy (fun i => posConf F R ix i) n) hpart.1 hpart.2.1 hpart.2.2.1 hpart.2.2.2
    (fun j i hj hi hne => ?_)
    (fun j => BPair.ofNat (carrier.contentN F (posConf F R ix j)) + (BPair.ofPos cf).swap)
    (fun j i hj hi hg => by
      rw [elim.placesBy_key_eq (fun i => posConf F R ix i) n j i hj hi hg]
      exact BPair.oneValue_refl _)
    (fun j i hj hi => ?_) rem hb hk0 (fun i hi => ?_) sp hsp'
  · -- the cross entries at distinct configurations
    have hrow := ground.all_range_read n (hcrossG j hj) i hi
    cases hc : carrier.eqConf F (posConf F R ix j) (posConf F R ix i) with
    | true =>
      exact absurd (elim.placesBy_groupOf_eq (fun i => posConf F R ix i) n j i hj hi
        (carrier.eqConf_eq F P hred _ _ (hlab j) (hlab i) hc)) hne
    | false =>
      rw [hc] at hrow
      exact of_decide_eq_true hrow
  · -- the entry tie at the row's weight
    have hjl : j < (slotDiag F R ix).length := by rw [hdl]; exact hj
    have hil : i < (slotDiag F R ix).length := by rw [hdl]; exact hi
    have hGl : G.length = n := elim.sqAt_len hG
    have hGr' : rowsLen n G := elim.rowsLen_of_sqAt hG
    have hcG : sqAt (matScale cf G) n := inertia.sqAt_matScale n cf G hG
    have hswap : ground.getAt [] (matSwap (matScale cf G)) j
        = (ground.getAt [] (matScale cf G) j).map BPair.swap :=
      elim.getAt_matSwap _ j (by rw [inertia.length_matScale, hGl]; exact hj)
    have hrowc : (ground.getAt [] (matScale cf G) j).length = n :=
      elim.rowsLen_getAt _ j (elim.rowsLen_of_sqAt hcG) (by rw [inertia.length_matScale, hGl]; exact hj)
    have eX : ground.getAt BPair.unit
        (ground.getAt [] (siteDatum (formE (slotDiag F R ix) G) (matScale cf G)) j) i
        = (BPair.ofNat (ground.getAt 0 (slotDiag F R ix) j)
            * ground.getAt BPair.unit (ground.getAt [] G j) i).norm
          + ((ground.getAt BPair.unit (ground.getAt [] G j) i).scale cf).swap := by
      show ground.getAt BPair.unit
        (ground.getAt [] (matAdd (formE (slotDiag F R ix) G) (matSwap (matScale cf G))) j) i = _
      have hswr : rowsLen n (matSwap (matScale cf G)) :=
        elim.rowsLen_mapRows BPair.swap _ n (elim.rowsLen_of_sqAt hcG)
      have hswl : j < (matSwap (matScale cf G)).length := by
        rw [elim.length_matSwap, inertia.length_matScale, hGl]; exact hj
      rw [elim.entry_matAdd _ _ n (elim.rowsLen_of_sqAt hE) hswr j i
        (by rw [elim.sqAt_len hE]; exact hj) hswl hi,
        hswap, ground.getAt_map BPair.unit BPair.unit BPair.swap _ i (by rw [hrowc]; exact hi),
        inertia.matScale_entry cf G j i (by rw [hGl]; exact hj)
          (by rw [elim.rowsLen_getAt _ j hGr' (by rw [hGl]; exact hj)]; exact hi)]
      show ground.getAt BPair.unit
        (ground.getAt [] (ground.matOf (slotDiag F R ix).length (slotDiag F R ix).length
          (fun i j => (BPair.ofNat (ground.getAt 0 (slotDiag F R ix) i)
            * ground.getAt BPair.unit (ground.getAt [] G i) j).norm)) j) i + _ = _
      rw [ground.matOf_entry [] BPair.unit _ _ _ j i hjl hil]
    rw [eX, slotDiag_posConf F R ix j (by rw [hnl]; exact hj)]
    refine BPair.oneValue_trans (BPair.add_congr (BPair.norm_oneValue _)
      (ground.swap_congr (BPair.oneValue_symm (BPair.ofPos_scale cf _)))) ?_
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.oneValue_of_eq (BPair.swap_mul _ _).symm)) ?_
    exact BPair.oneValue_of_eq (BPair.right_distrib _ _ _).symm
  · -- the places' weights on their upper side
    exact unitLe_ofNat_swap _ cf (hcont i hi)

/-! The pencil's nesting read: `thm:truncation`'s projection `Π` at
the window's positions, the head and removed places and the pencil's
members joined at them. -/

/-- The head places at a truncation cutoff: the window positions
whose configuration's content sits at or below the cutoff, the unit
line among them (the sector's own head at a cutoff is
`contactcell.headAt`, the labels' instance one layer down). -/
def headPlaces {L : Type} (F : Data L) (R : Region) (ix : List (List L))
    (n C : Nat) : List Nat :=
  placesAt F R ix n (fun a => decide (carrier.contentN F a ≤ C))

/-- The removed places at a truncation cutoff: the window positions
whose configuration's content sits beyond the cutoff
(`contactcell.exclAt` the labels' instance). -/
def remPlaces {L : Type} (F : Data L) (R : Region) (ix : List (List L))
    (n C : Nat) : List Nat :=
  placesAt F R ix n (fun a => decide (C < carrier.contentN F a))

/-- The window list at a filtered index is the window list filtered
at the read of each member's configuration, one list in the window
list's order. -/
theorem slotList_filter {L : Type} (F : Data L) (R : Region) (ix : List (List L))
    (P : List L → Bool) :
    slotList F R (ix.filter P) = (slotList F R ix).filter (fun q => P q.1) := by
  show (ix.filter P).flatMap (fun a => (slotKeys F R a).map (fun k => (a, k)))
    = (ix.flatMap (fun a => (slotKeys F R a).map (fun k => (a, k)))).filter
        (fun q => P q.1)
  rw [flatMap_filter, filter_flatMap]
  refine flatMap_congr_all _ _ (fun a => ?_) ix
  rw [filter_map]
  cases hP : P a with
  | true =>
    rw [if_pos rfl, filter_all _ _ (fun k _ => by show P a = true; exact hP)]
  | false =>
    rw [if_neg Bool.false_ne_true,
      filter_false _ _ (fun k _ => by show P a = false; exact hP)]
    rfl

/-- The places at a read holding the unit configuration: the unit
line at the head, then the window list's positions at the read
moved past it. -/
theorem placesAt_unit {L : Type} (F : Data L) (R : Region) (ix : List (List L))
    (P : List L → Bool) (hP : P (carrier.unitConf F R) = true) :
    placesAt F R ix ((slotList F R ix).length + 1) P
      = 0 :: ((List.range (slotList F R ix).length).filter (fun r =>
          P (getAt (carrier.unitConf F R, []) (slotList F R ix) r).1)).map
            (fun j => j + 1) := by
  show (List.range ((slotList F R ix).length + 1)).filter (fun i => P (posConf F R ix i)) = _
  rw [range_cons, filter_cons_true (p := fun i => P (posConf F R ix i))
      (show P (posConf F R ix 0) = true from hP),
    filter_map]
  rfl

/-- The truncated index's window list is the window list read at
the kept positions. -/
theorem slotList_places {L : Type} (F : Data L) (R : Region) (ix : List (List L))
    (P : List L → Bool) :
    slotList F R (ix.filter P)
      = ((List.range (slotList F R ix).length).filter (fun r =>
          P (getAt (carrier.unitConf F R, []) (slotList F R ix) r).1)).map
            (getAt (carrier.unitConf F R, []) (slotList F R ix)) := by
  rw [slotList_filter, filter_map_range (carrier.unitConf F R, [])]

/-- A truncated window list member is the window list's member at
its kept position. -/
theorem slotList_head {L : Type} (F : Data L) (R : Region) (ix : List (List L))
    (P : List L → Bool) (m : Nat)
    (hm : m < ((List.range (slotList F R ix).length).filter (fun r =>
        P (getAt (carrier.unitConf F R, []) (slotList F R ix) r).1)).length) :
    getAt (carrier.unitConf F R, []) (slotList F R (ix.filter P)) m
      = getAt (carrier.unitConf F R, []) (slotList F R ix)
          (getAt 0 ((List.range (slotList F R ix).length).filter (fun r =>
            P (getAt (carrier.unitConf F R, []) (slotList F R ix) r).1)) m) := by
  rw [slotList_places, getAt_map 0 (carrier.unitConf F R, []) _ _ m hm]

/-- The head places' count is the truncated window list's with the
unit line. -/
theorem length_headPlaces {L : Type} (F : Data L) (R : Region) (ix : List (List L))
    (C : Nat) :
    (headPlaces F R ix ((slotList F R ix).length + 1) C).length
      = (slotList F R (ix.filter (fun a => decide (carrier.contentN F a ≤ C)))).length + 1 := by
  show (placesAt F R ix _ _).length = _
  rw [placesAt_unit F R ix _ (by
      rw [carrier.contentN_unitConf]
      exact decide_eq_true (Nat.zero_le C)),
    slotList_places]
  show ((List.filter _ (List.range _)).map (fun j => j + 1)).length + 1 = _
  rw [length_map, length_map]

/-- The truncated window's positions at the head places: the
truncated position is the unit line at the head and the kept
position moved past the unit line beyond it. -/
private theorem headPlaces_pos {L : Type} (F : Data L) (R : Region) (ix : List (List L))
    (C : Nat) (j : Nat)
    (hj : j < (headPlaces F R ix ((slotList F R ix).length + 1) C).length) :
    (j = 0 ∧ getAt 0 (headPlaces F R ix ((slotList F R ix).length + 1) C) 0 = 0)
    ∨ ∃ m, j = m + 1
      ∧ m < ((List.range (slotList F R ix).length).filter (fun r =>
          decide (carrier.contentN F
            (getAt (carrier.unitConf F R, []) (slotList F R ix) r).1 ≤ C))).length
      ∧ getAt 0 (headPlaces F R ix ((slotList F R ix).length + 1) C) j
        = getAt 0 ((List.range (slotList F R ix).length).filter (fun r =>
            decide (carrier.contentN F
              (getAt (carrier.unitConf F R, []) (slotList F R ix) r).1 ≤ C))) m + 1 := by
  have hu : decide (carrier.contentN F (carrier.unitConf F R) ≤ C) = true := by
    rw [carrier.contentN_unitConf]
    exact decide_eq_true (Nat.zero_le C)
  have hj' : j < (placesAt F R ix ((slotList F R ix).length + 1)
      (fun a => decide (carrier.contentN F a ≤ C))).length := hj
  show (j = 0 ∧ getAt 0 (placesAt F R ix _ _) 0 = 0) ∨ ∃ m, j = m + 1 ∧ _
    ∧ getAt 0 (placesAt F R ix _ _) j = _
  rw [placesAt_unit F R ix _ hu] at hj' ⊢
  cases j with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  | succ m =>
    have hm : m < ((List.range (slotList F R ix).length).filter (fun r =>
        decide (carrier.contentN F
          (getAt (carrier.unitConf F R, []) (slotList F R ix) r).1 ≤ C))).length := by
      have h := hj'
      rw [show ∀ l : List Nat, (0 :: l).length = l.length + 1 from fun _ => rfl,
        length_map] at h
      exact Nat.lt_of_succ_lt_succ h
    refine Or.inr ⟨m, rfl, hm, ?_⟩
    show getAt 0 (((List.range (slotList F R ix).length).filter _).map (fun j => j + 1)) m = _
    rw [getAt_map 0 0 (fun j => j + 1) _ m hm]

/-- The configuration at a truncated window position is the
configuration at its head place. -/
theorem posConf_head {L : Type} (F : Data L) (R : Region) (ix : List (List L))
    (C : Nat) :
    ∀ j, j < (headPlaces F R ix ((slotList F R ix).length + 1) C).length →
      posConf F R (ix.filter (fun a => decide (carrier.contentN F a ≤ C))) j
        = posConf F R ix
            (getAt 0 (headPlaces F R ix ((slotList F R ix).length + 1) C) j) := by
  intro j hj
  cases headPlaces_pos F R ix C j hj with
  | inl h => rw [h.1, h.2]; rfl
  | inr h =>
    obtain ⟨m, hjm, hm, hp⟩ := h
    subst hjm
    rw [hp]
    show (getAt (carrier.unitConf F R, []) (slotList F R
      (ix.filter (fun a => decide (carrier.contentN F a ≤ C)))) m).1 = _
    rw [slotList_head F R ix _ m hm]
    rfl

/-- The fiber key at a truncated window position is the key at its
head place. -/
theorem posKey_head {L : Type} (F : Data L) (R : Region) (ix : List (List L))
    (C : Nat) :
    ∀ j, j < (headPlaces F R ix ((slotList F R ix).length + 1) C).length →
      posKey F R (ix.filter (fun a => decide (carrier.contentN F a ≤ C))) j
        = posKey F R ix
            (getAt 0 (headPlaces F R ix ((slotList F R ix).length + 1) C) j) := by
  intro j hj
  cases headPlaces_pos F R ix C j hj with
  | inl h => rw [h.1, h.2]; rfl
  | inr h =>
    obtain ⟨m, hjm, hm, hp⟩ := h
    subst hjm
    rw [hp]
    show (getAt (carrier.unitConf F R, []) (slotList F R
      (ix.filter (fun a => decide (carrier.contentN F a ≤ C)))) m).2 = _
    rw [slotList_head F R ix _ m hm]
    rfl

/-- The head and removed places partition the order: distinct, at
the order's count, each list below the order, and the unit line
among the head places. -/
theorem places_perm {L : Type} (F : Data L) (R : Region) (ix : List (List L))
    (n C : Nat) (hn : 0 < n) :
    distinctList (headPlaces F R ix n C ++ remPlaces F R ix n C)
    ∧ (headPlaces F R ix n C ++ remPlaces F R ix n C).length = n
    ∧ ((headPlaces F R ix n C).all (fun i => Nat.blt i n)) = true
    ∧ ((remPlaces F R ix n C).all (fun i => Nat.blt i n)) = true
    ∧ 0 < (headPlaces F R ix n C).length := by
  have hh : headPlaces F R ix n C
      = (List.range n).filter (fun i => decide (carrier.contentN F (posConf F R ix i) ≤ C)) :=
    rfl
  have hr : remPlaces F R ix n C
      = (List.range n).filter (fun i => !(decide (carrier.contentN F (posConf F R ix i) ≤ C))) := by
    refine filter_congr _ _ (fun i => ?_) _
    show decide (C < carrier.contentN F (posConf F R ix i))
      = !(decide (carrier.contentN F (posConf F R ix i) ≤ C))
    cases hc : decide (carrier.contentN F (posConf F R ix i) ≤ C) with
    | true => exact decide_eq_false (Nat.not_lt.mpr (of_decide_eq_true hc))
    | false => exact decide_eq_true (Nat.lt_of_not_le (of_decide_eq_false hc))
  have h0 : 0 ∈ headPlaces F R ix n C := by
    rw [hh]
    refine mem_filter_to _ ?_ ?_
    · rw [← getAt_range n 0 hn]
      exact mem_getAt 0 _ 0 (by rw [length_range]; exact hn)
    · show decide (carrier.contentN F (carrier.unitConf F R) ≤ C) = true
      rw [carrier.contentN_unitConf]
      exact decide_eq_true (Nat.zero_le C)
  refine ⟨?_, ?_, ?_, ?_, List.length_pos_of_mem h0⟩
  · rw [hh, hr]
    refine distinctList_append_disjoint _ _
      (distinctList_filter (fun i => decide (carrier.contentN F (posConf F R ix i) ≤ C)) _
        (distinctList_range n))
      (distinctList_filter (fun i => !(decide (carrier.contentN F (posConf F R ix i) ≤ C))) _
        (distinctList_range n))
      (fun x hx hx' => ?_)
    have h1 := (mem_filter_of _ _ x hx).2
    have h2 := (mem_filter_of _ _ x hx').2
    rw [h1] at h2
    exact Bool.noConfusion h2
  · rw [hh, hr, length_append, length_filter_split, length_range]
  · rw [hh]
    exact all_of_mem_intro _ _ (fun x hx => ltBlt (ltOfMemRange (mem_filter_of _ _ x hx).1))
  · rw [hr]
    exact all_of_mem_intro _ _ (fun x hx => ltBlt (ltOfMemRange (mem_filter_of _ _ x hx).1))

/-- A head place's configuration reads content at or below the
cutoff, a removed place's beyond it. -/
theorem places_content {L : Type} (F : Data L) (R : Region) (ix : List (List L))
    (n C : Nat) :
    (∀ i, i ∈ headPlaces F R ix n C → carrier.contentN F (posConf F R ix i) ≤ C)
    ∧ (∀ i, i ∈ remPlaces F R ix n C → C < carrier.contentN F (posConf F R ix i)) :=
  ⟨fun i hi => of_decide_eq_true (mem_filter_of _ _ i hi).2,
   fun i hi => of_decide_eq_true (mem_filter_of _ _ i hi).2⟩

/-- The gram's cross block between the head and removed places is
the null matrix (`def:carrier`'s gram, the orthogonal sum of the
unit line's pairing and the fibers' own: two positions at distinct
contents sit at distinct configurations, whose pairing reads the
sum's unit, `gramBlockRead`'s cross clause at a label domain with
one spelling per label), and at the places' permutation the gram
joins its two diagonal selections at the null coupling. -/
theorem gram_nest {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (n : Nat) (ix : List (List L)) (c : Pos) (G : Mat) (hn : 0 < n)
    (hG : sqAt G n) (hsym : symmRead G)
    (hgram : gramBlockRead F R n ix c G)
    (P : L → Bool) (hunitP : P F.unit = true)
    (hix : ∀ a, a ∈ ix → a.all P = true)
    (hred : ∀ x y, P x = true → P y = true → F.eqL x y = true → x = y)
    (C : Nat) :
    matNull (selM (headPlaces F R ix n C) (remPlaces F R ix n C) G)
    ∧ matOneValue (selM (headPlaces F R ix n C ++ remPlaces F R ix n C)
        (headPlaces F R ix n C ++ remPlaces F R ix n C) G)
      (blockJoin (selM (headPlaces F R ix n C) (headPlaces F R ix n C) G)
        (nullMat (headPlaces F R ix n C).length (remPlaces F R ix n C).length)
        (selM (remPlaces F R ix n C) (remPlaces F R ix n C) G)) := by
  obtain ⟨_, _, hbh, hbr, hk0⟩ := places_perm F R ix n C hn
  obtain ⟨hhead, hrem⟩ := places_content F R ix n C
  have hcross : matNull (selM (headPlaces F R ix n C) (remPlaces F R ix n C) G) := by
    refine matNull_of_getAt _ (fun p hp => ?_)
    rw [length_selM] at hp
    refine poly.unitTail_of_getAt (fun q => ?_)
    cases Nat.lt_or_ge q (remPlaces F R ix n C).length with
    | inr hq =>
      rw [getAt_over _ _ q (by
        rw [rowsLen_getAt _ p (rowsLen_selM _ G _) (by rw [length_selM]; exact hp)]
        exact hq)]
      exact BPair.oneValue_refl _
    | inl hq =>
      rw [getAt_selM _ _ G p q hp hq]
      have hi : getAt 0 (headPlaces F R ix n C) p ∈ headPlaces F R ix n C :=
        mem_getAt 0 _ p hp
      have hj : getAt 0 (remPlaces F R ix n C) q ∈ remPlaces F R ix n C :=
        mem_getAt 0 _ q hq
      have hin : getAt 0 (headPlaces F R ix n C) p < n :=
        bltLt (all_of_mem _ _ hbh _ hi)
      have hjn : getAt 0 (remPlaces F R ix n C) q < n :=
        bltLt (all_of_mem _ _ hbr _ hj)
      have h2 := all_range_read n hgram.2.1 _ hin
      have h3 := all_range_read n h2 _ hjn
      cases orSplitB h3 with
      | inr hu => exact of_decide_eq_true hu
      | inl he =>
        have heq := carrier.eqConf_eq F P hred _ _
          (posConf_labels F R ix P hunitP hix _) (posConf_labels F R ix P hunitP hix _) he
        have hc1 := hhead _ hi
        have hc2 := hrem _ hj
        rw [heq] at hc1
        exact absurd (Nat.lt_of_lt_of_le hc2 hc1) (Nat.lt_irrefl _)
  refine ⟨hcross, ?_⟩
  refine matOne_trans (selM_blockJoin G _ _ n hG (matOne_symm hsym) hk0 hbh hbr) ?_
  refine blockJoin_congr _ _ _ _ _ _ (rowsLen_selM _ G _) (rowsLen_selM _ G _)
    (length_selM _ _ _) (length_nullMat _ _) (rowsLen_selM _ G _) (rowsLen_nullMat _ _)
    (matOne_refl _) ?_ (matOne_refl _)
  exact matOne_of_null _ _ _ hcross (matNull_nullMat _ _)
    ((length_selM _ _ _).trans (length_nullMat _ _).symm)
    (rowsLen_selM _ G _) (rowsLen_nullMat _ _)

/-- The electric member's form is symmetric (`thm:pairpencil`: the
electric member against the pairing identity, hence symmetric): two
positions at distinct configurations pair at the sum's unit both
ways, and two at one configuration read one content, the gram's
symmetry riding the shared scale. -/
theorem formE_symm {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (n : Nat) (ix : List (List L)) (c : Pos) (G : Mat)
    (hnl : (slotList F R ix).length + 1 = n)
    (hG : sqAt G n) (hsym : symmRead G)
    (hgram : gramBlockRead F R n ix c G)
    (P : L → Bool) (hunitP : P F.unit = true)
    (hix : ∀ a, a ∈ ix → a.all P = true)
    (hred : ∀ x y, P x = true → P y = true → F.eqL x y = true → x = y) :
    symmRead (formE (slotDiag F R ix) G) := by
  have hdl : (slotDiag F R ix).length = n := by rw [length_slotDiag]; exact hnl
  have hE : sqAt (formE (slotDiag F R ix) G) n := sqAt_formE _ G n hdl
  refine matOne_of_entries _ _ n (sqAt_len hE) (rowsLen_of_sqAt hE)
    (length_transposeM_sq _ hE) (rowsLen_cast (sqAt_len hE) (rowsLen_transposeM _))
    (fun i j hi hj => ?_)
  rw [getAt_transposeM BPair.unit _ (rowsLen_of_sqAt hE) i j hi (by rw [sqAt_len hE]; exact hj),
    formE_entry _ G i j (by rw [hdl]; exact hi) (by rw [hdl]; exact hj),
    formE_entry _ G j i (by rw [hdl]; exact hj) (by rw [hdl]; exact hi)]
  have hGs := symmRead_entry G hG hsym i j hi hj
  have h3 := all_range_read n (all_range_read n hgram.2.1 i hi) j hj
  refine BPair.oneValue_trans (BPair.norm_oneValue _)
    (BPair.oneValue_trans ?_ (BPair.oneValue_symm (BPair.norm_oneValue _)))
  cases orSplitB h3 with
  | inr hu =>
    have hu' := of_decide_eq_true hu
    refine BPair.oneValue_trans (oneValue_mul_unit _ _ hu') ?_
    refine BPair.oneValue_symm (oneValue_mul_unit _ _ ?_)
    exact BPair.oneValue_trans (BPair.oneValue_symm hGs) hu'
  | inl he =>
    have heq := carrier.eqConf_eq F P hred _ _
      (posConf_labels F R ix P hunitP hix _) (posConf_labels F R ix P hunitP hix _) he
    rw [slotDiag_posConf F R ix i (by rw [hnl]; exact hi),
      slotDiag_posConf F R ix j (by rw [hnl]; exact hj), heq]
    exact BPair.mul_congr (BPair.oneValue_refl _) hGs

/-- The electric member's cross block between the head and removed
places is the null matrix (`thm:truncation`: the diagonal electric
operator reads its off-block part at the sum's unit), the form's
entries the gram's scaled at the contents, and at the places'
permutation the electric member joins its two diagonal selections
at the null coupling. -/
theorem elec_nest {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (n : Nat) (ix : List (List L)) (c : Pos) (G : Mat)
    (hnl : (slotList F R ix).length + 1 = n)
    (hG : sqAt G n) (hsym : symmRead G)
    (hgram : gramBlockRead F R n ix c G)
    (P : L → Bool) (hunitP : P F.unit = true)
    (hix : ∀ a, a ∈ ix → a.all P = true)
    (hred : ∀ x y, P x = true → P y = true → F.eqL x y = true → x = y)
    (C : Nat) :
    matNull (selM (headPlaces F R ix n C) (remPlaces F R ix n C)
      (formE (slotDiag F R ix) G))
    ∧ matOneValue (selM (headPlaces F R ix n C ++ remPlaces F R ix n C)
        (headPlaces F R ix n C ++ remPlaces F R ix n C) (formE (slotDiag F R ix) G))
      (blockJoin (selM (headPlaces F R ix n C) (headPlaces F R ix n C)
          (formE (slotDiag F R ix) G))
        (nullMat (headPlaces F R ix n C).length (remPlaces F R ix n C).length)
        (selM (remPlaces F R ix n C) (remPlaces F R ix n C)
          (formE (slotDiag F R ix) G))) := by
  have hn : 0 < n := by rw [← hnl]; exact Nat.succ_pos _
  obtain ⟨hcross, _⟩ := gram_nest F R n ix c G hn hG hsym hgram P hunitP hix hred C
  obtain ⟨_, _, hbh, hbr, hk0⟩ := places_perm F R ix n C hn
  have hdl : (slotDiag F R ix).length = n := by rw [length_slotDiag]; exact hnl
  have hE : sqAt (formE (slotDiag F R ix) G) n := sqAt_formE _ G n hdl
  have hEsym : symmRead (formE (slotDiag F R ix) G) :=
    formE_symm F R n ix c G hnl hG hsym hgram P hunitP hix hred
  have hcrossE : matNull (selM (headPlaces F R ix n C) (remPlaces F R ix n C)
      (formE (slotDiag F R ix) G)) := by
    refine matNull_of_getAt _ (fun p hp => ?_)
    rw [length_selM] at hp
    refine poly.unitTail_of_getAt (fun q => ?_)
    cases Nat.lt_or_ge q (remPlaces F R ix n C).length with
    | inr hq =>
      rw [getAt_over _ _ q (by
        rw [rowsLen_getAt _ p (rowsLen_selM _ _ _) (by rw [length_selM]; exact hp)]
        exact hq)]
      exact BPair.oneValue_refl _
    | inl hq =>
      have hu := poly.getAt_unitTail (matNull_rowAt _ hcross p) q
      rw [getAt_selM _ _ G p q hp hq] at hu
      rw [getAt_selM _ _ _ p q hp hq]
      have hin : getAt 0 (headPlaces F R ix n C) p < n :=
        bltLt (all_of_mem _ _ hbh _ (mem_getAt 0 _ p hp))
      have hjn : getAt 0 (remPlaces F R ix n C) q < n :=
        bltLt (all_of_mem _ _ hbr _ (mem_getAt 0 _ q hq))
      exact formE_entry_unit _ G _ _ (by rw [hdl]; exact hin) (by rw [hdl]; exact hjn) hu
  refine ⟨hcrossE, ?_⟩
  refine matOne_trans (selM_blockJoin _ _ _ n hE (matOne_symm hEsym) hk0 hbh hbr) ?_
  refine blockJoin_congr _ _ _ _ _ _ (rowsLen_selM _ _ _) (rowsLen_selM _ _ _)
    (length_selM _ _ _) (length_nullMat _ _) (rowsLen_selM _ _ _) (rowsLen_nullMat _ _)
    (matOne_refl _) ?_ (matOne_refl _)
  exact matOne_of_null _ _ _ hcrossE (matNull_nullMat _ _)
    ((length_selM _ _ _).trans (length_nullMat _ _).symm)
    (rowsLen_selM _ _ _) (rowsLen_nullMat _ _)

/-- The magnetic member at the places' permutation joins its two
diagonal selections at the coupling, the selection between the head
and removed places (`thm:truncation`'s off-block coupling, the
magnetic one alone), the terms' sum symmetric at the terms' reads. -/
theorem mag_nest {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (n : Nat) (ix : List (List L)) (c : Pos) (G : Mat) (hn : 0 < n)
    (ps : List (List (Nat × Bool))) (terms : List (Mat × Split n × Split n))
    (ht : termsRead F R n ix c G ps terms) (C : Nat) :
    matOneValue (selM (headPlaces F R ix n C ++ remPlaces F R ix n C)
        (headPlaces F R ix n C ++ remPlaces F R ix n C) (termSum n terms))
      (blockJoin (selM (headPlaces F R ix n C) (headPlaces F R ix n C) (termSum n terms))
        (selM (headPlaces F R ix n C) (remPlaces F R ix n C) (termSum n terms))
        (selM (remPlaces F R ix n C) (remPlaces F R ix n C) (termSum n terms))) := by
  obtain ⟨_, _, hbh, hbr, hk0⟩ := places_perm F R ix n C hn
  obtain ⟨hMsq, hMsym⟩ := termSum_read F R n ix c G ps terms ht
  exact selM_blockJoin _ _ _ n hMsq (matOne_symm hMsym) hk0 hbh hbr

/-- The removed block's floor at the truncation cutoff
(`thm:truncation`: the removed block's electric diagonal sits at or
above the cutoff): at the removed places, whose contents sit beyond
the cutoff, the electric member less the cutoff's successor's multiple
of the gram reads every split positive semidefinite
(`removed_floor` at the removed places). -/
theorem removed_nest {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (n : Nat) (ix : List (List L)) (c : Pos) (G : Mat)
    (hnl : (slotList F R ix).length + 1 = n)
    (hG : sqAt G n) (spG : Split n) (hGr : splitRead G spG) (hGp : psdAt spG)
    (hgram : gramBlockRead F R n ix c G)
    (P : L → Bool) (hunitP : P F.unit = true)
    (hix : ∀ a, a ∈ ix → a.all P = true)
    (hred : ∀ x y, P x = true → P y = true → F.eqL x y = true → x = y)
    (C : Nat) (cf : Pos) (hcf : posVal cf ≤ C + 1)
    (hk0 : 0 < (remPlaces F R ix n C).length)
    (sp : Split (remPlaces F R ix n C).length)
    (hsp : splitRead (siteDatum
      (selM (remPlaces F R ix n C) (remPlaces F R ix n C) (formE (slotDiag F R ix) G))
      (matScale cf (selM (remPlaces F R ix n C) (remPlaces F R ix n C) G))) sp) :
    psdAt sp := by
  obtain ⟨_, _, _, hbr, _⟩ := places_perm F R ix n C (by rw [← hnl]; exact Nat.succ_pos _)
  exact removed_floor F R n ix c G hnl hG spG hGr hGp hgram P hunitP hix hred cf _
    hbr hk0 (fun i hi =>
      Nat.le_trans hcf (Nat.succ_le_of_lt ((places_content F R ix n C).2 i hi))) sp hsp

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

instance instPairpencil4 {L : Type} [DecidableEq L] (F : Data L) (R : Region) (C n : Nat)
    (ix : List (List L)) (c : Pos) (E G M : Mat) (spG : Split n)
    (terms : List (Mat × Split n × Split n)) :
    Decidable (pencilRead F R C n ix c E G M spG terms) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

end pairpencil
