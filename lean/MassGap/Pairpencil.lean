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
diagonal `pencilE`, `symmRead` the transpose's one-value read).  The pencil interface is the fields a window's
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
(`fibGram`, `con:fiber`'s vertex lists at their multiplicities, read
once per member along the index at `memberBlocks`), the entry at
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
(`linkSigAt` the source word's slots at the dagger reads flipped,
the boundary pair and the target's; `linkData` at
`fiber.linkList` and `fiber.coevW`, read once per signature of the
window's words through the store `linkSigs`, `linkDataAt` the
read's own at `linkDataAt_read`), the boundary character's wiring
at each vertex (`bdryWiring`, the wiring tensor at the boundary
layout `bdrySig` and the passes' pairing `bdryPerm`), the vertex
tensor the three
members' pairing against the links' members at every tuple of the
links' member indices (`vertexTensor` at the blocks `blocksAt` and
the sub-monomials `subMon`, the members `vertexMember` through the
window's vertex-list store `endsStore`, `vertListAt` the field's
own read at `vertListAt_read`), and the contraction the fold over
the vertices at the open links' assignments (`stepVertex`, a link
opening at its first end and closing at its second at the adjugate
weight); at unstated lists the loop window's read, the entry the
fusion count at the loop labels (`loopLabel` at `loopConf`) — the
terms' reads along the region's
plaquette list (`termsRead`, the terms' count the plaquettes' and
each term square at the order, `termsRead_len` and `termsRead_sq`),
the terms' transport along the region's action at the window list
the field's read in the module that owns the action
(`fiberdec.termsMoved`), and the whole `pencilRead` at the fields
this module owns, every read at a stated index tied to the
window's own; at a loop
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

/-- The symmetry read: the matrix one value with its transpose. -/
def symmRead (m : Mat) : Prop := matOneValue m (transposeM m)

instance (m : Mat) : Decidable (symmRead m) :=
  inferInstanceAs (Decidable (matOneValue _ _))

/-- The pair `(α E : β M)`'s site datum `H([α : β])` at
`α E = β M + H`: the electric member's form against the gram at
the first weight, each row at its slot's content, against the
magnetic matrix at the second, every entry a pair datum at pair
weights. -/
def pencilH (al be : Pos) (diag : List Nat) (G M : Mat) : Mat :=
  ground.matOf diag.length diag.length (fun i j =>
      (BPair.ofPos al * (BPair.ofNat (ground.getAt 0 diag i)
          * ground.getAt BPair.unit (ground.getAt [] G i) j)
        + (BPair.ofPos be
            * ground.getAt BPair.unit (ground.getAt [] M i) j).swap
       ).norm)

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

/-- A slot key reads one digit per vertex, each below the vertex's
multiplicity. -/
theorem slotKeys_read {L : Type} (F : Data L) (R : Region) (a : List L)
    (k : List Nat) (h : k ∈ slotKeys F R a) :
    k.length = R.verts ∧ ∀ u, u < R.verts → getAt 0 k u < carrier.vmult F R a u := by
  obtain ⟨hl, hd⟩ := mem_prodLists_of 0 _ k h
  rw [length_map, length_range] at hl hd
  refine ⟨hl, fun u hu => ?_⟩
  have := hd u hu
  rw [getAt_map_range, if_pos hu] at this
  exact ltOfMemRange this

/-- A digit list at one digit per vertex below its multiplicity is
a slot key. -/
theorem slotKeys_intro {L : Type} (F : Data L) (R : Region) (a : List L)
    (k : List Nat) (hl : k.length = R.verts)
    (hd : ∀ u, u < R.verts → getAt 0 k u < carrier.vmult F R a u) :
    k ∈ slotKeys F R a := by
  refine mem_prodLists_to 0 _ k (by rw [length_map, length_range]; exact hl)
    (fun i hi => ?_)
  rw [length_map, length_range] at hi
  rw [getAt_map_range, if_pos hi]
  exact memRange (hd i hi)

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

/-- An index member with one of its slot keys is a window list
member. -/
theorem mem_slotList_to {L : Type} (F : Data L) (R : Region)
    (ix : List (List L)) (a : List L) (k : List Nat) (ha : a ∈ ix)
    (hk : k ∈ slotKeys F R a) : (a, k) ∈ slotList F R ix :=
  mem_flatMap_to _ ha (mem_map_to _ hk)

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

/-- The fiber's vertex Grams at a configuration, one per vertex of
the region at the interface's presentation field over the incident
ends (`con:fiber`), each at the vertex's multiplicity and square
there, the vacant read at a vertex off the field or off the
multiplicity. -/
def fibGram {L : Type} (F : Data L) (R : Region) (a : List L) :
    Option (List (Mat × Pos)) :=
  (List.range R.verts).foldl (fun acc v =>
    match acc, vertGramOf F (carrier.incidentEnds F R a v) with
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
def memberBlocks {L : Type} (F : Data L) (R : Region) (ix : List (List L))
    (c : Pos) (G : Mat) : Bool :=
  (ix.foldl (fun (acc : Nat × Bool) a =>
    let ks := slotKeys F R a
    (acc.1 + ks.length,
     acc.2 && (match fibGram F R a with
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
def gramBlockRead {L : Type} (F : Data L) (R : Region) (n : Nat)
    (ix : List (List L)) (c : Pos) (G : Mat) : Prop :=
  (ground.getAt BPair.unit (ground.getAt [] G 0) 0).oneValue (BPair.ofPos c)
  ∧ ((List.range n).all (fun i => (List.range n).all (fun j =>
      carrier.eqConf F (posConf F R ix i) (posConf F R ix j)
        || decide ((ground.getAt BPair.unit
            (ground.getAt [] G i) j).oneValue BPair.unit)))) = true
  ∧ memberBlocks F R ix c G = true

instance {L : Type} (F : Data L) (R : Region) (n : Nat) (ix : List (List L))
    (c : Pos) (G : Mat) : Decidable (gramBlockRead F R n ix c G) :=
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

/-- A label's word pair at the presentation field, the one-end
vertex list's stated end. -/
def wordOf {L : Type} (F : Data L) (x : L) : Nat × Nat :=
  match F.vertList [(x, true)] with
  | some l => getAt (0, 0) l.ends 0
  | none => (0, 0)

/-- The slot power's letter count at the presentation field, the
unit state's vertex list's width. -/
def lettersOf {L : Type} (F : Data L) : Nat :=
  match F.vertList [] with
  | some l => l.members.letters
  | none => 0

/-- The vertex lists read once per incident-end list of the window:
every index member's incident ends at every vertex with the unit
line's, each list stored at its first occurrence. -/
def endsStore {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) : List (List (L × Bool) × Option fiber.VList) :=
  (carrier.unitConf F R :: ix).foldl (fun acc a =>
    (List.range R.verts).foldl (fun acc2 v =>
      let es := carrier.incidentEnds F R a v
      if acc2.any (fun e => decide (e.1 = es)) then acc2
      else acc2 ++ [(es, F.vertList es)]) acc) []

/-- The vertex list at an incident-end list through the window's
store, the field's own read at every list. -/
def vertListAt {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (es : List (L × Bool)) : Option fiber.VList :=
  keyAt (fun a b => decide (a = b)) (F.vertList es) es (endsStore F R ix)

/-- The stored read is the field's: every store entry holds the
field's value at its key, the store built by joins at the field's
own reads. -/
theorem vertListAt_read {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (es : List (L × Bool)) :
    vertListAt F R ix es = F.vertList es := by
  have hv : ∀ (a : List L) (vs : List Nat)
      (acc : List (List (L × Bool) × Option fiber.VList)),
      (∀ e, e ∈ acc → e.2 = F.vertList e.1) →
      ∀ e, e ∈ vs.foldl (fun acc2 v =>
          let es := carrier.incidentEnds F R a v
          if acc2.any (fun e => decide (e.1 = es)) then acc2
          else acc2 ++ [(es, F.vertList es)]) acc →
        e.2 = F.vertList e.1 := by
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
            F.vertList (carrier.incidentEnds F R a v))]) := he
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
      (∀ e, e ∈ acc → e.2 = F.vertList e.1) →
      ∀ e, e ∈ l.foldl (fun acc a =>
          (List.range R.verts).foldl (fun acc2 v =>
            let es := carrier.incidentEnds F R a v
            if acc2.any (fun e => decide (e.1 = es)) then acc2
            else acc2 ++ [(es, F.vertList es)]) acc) acc →
        e.2 = F.vertList e.1 := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons a t ih => intro acc h; exact ih _ (hv a _ acc h)
  exact keyAt_store (fun a b => decide (a = b)) (fun _ _ h => of_decide_eq_true h)
    F.vertList es _ (hst (carrier.unitConf F R :: ix) [] (fun _ h => nomatch h))

/-- The vertex member of a state at a vertex: the member at the
state's key with the list's clearing, vacant where the list is
unstated. -/
def vertexMember {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (a : List L) (k : List Nat) (v : Nat) :
    Option (slotpower.GVec × Pos) :=
  match vertListAt F R ix (carrier.incidentEnds F R a v) with
  | none => none
  | some l => some (getAt [] l.members.list (getAt 0 k v), l.clear)

/-- A link's combined slot signature at its tail: the source word's
slots at the dagger reads flipped, the boundary word's undaggered
and daggered pair at a boundary link, and the target word's slots;
the head's the exchanged signature slot for slot. -/
def linkSigAt (wa : Nat × Nat) (bd : Bool) (wb : Nat × Nat) : List Bool :=
  slotpower.endWordSig wa false ++ (if bd then slotpower.wordSig (1, 1) else [])
    ++ slotpower.wordSig wb

/-- A link's coevaluation data at its combined signature: the
invariant list, the Gram's adjugate and the determinant
(`fiber.linkList`, `fiber.coevW`). -/
def linkData (d : Nat) (sig : List Bool) :
    List slotpower.GVec × elim.Mat × BPair :=
  let lg := fiber.linkList d sig
  let cw := fiber.coevW lg.2
  (lg.1, cw.1, cw.2)

/-- The window's link signatures: per pair of the labels' words a
boundary link's signature, and a word's own off the boundary. -/
def linkSigs {L : Type} (F : Data L) (ix : List (List L)) : List (List Bool) :=
  let words := ground.dedupF ((F.unit :: ix.flatMap (fun a => a)).map (wordOf F))
  ground.dedupF (words.flatMap (fun wa =>
    linkSigAt wa false wa :: words.map (fun wb => linkSigAt wa true wb)))

/-- The link data read once per signature of the window: the store
over the window's signatures, the read itself off them. -/
def linkDataAt {L : Type} (F : Data L) (ix : List (List L)) (sig : List Bool) :
    List slotpower.GVec × elim.Mat × BPair :=
  keyAt (fun a b => a == b) (linkData (lettersOf F) sig) sig
    ((linkSigs F ix).map (fun s => (s, linkData (lettersOf F) s)))

/-- The stored read is the link data at every signature. -/
theorem linkDataAt_read {L : Type} (F : Data L) (ix : List (List L))
    (sig : List Bool) : linkDataAt F ix sig = linkData (lettersOf F) sig :=
  keyAt_memo (fun a b => a == b) (fun _ _ h => ground.listBeqEq h)
    (linkData (lettersOf F)) sig (linkSigs F ix)

/-- The boundary word's consecutive entry pairs, cyclic. -/
def wordPairs (p : List (Nat × Bool)) : List ((Nat × Bool) × (Nat × Bool)) :=
  List.zipWith (fun e f => (e, f)) p (p.drop 1 ++ p.take 1)

/-- The boundary ends at a vertex, the incident ends on the
plaquette in the incident order. -/
def bdryEnds (R : Region) (p : List (Nat × Bool)) (v : Nat) : List (Nat × Bool) :=
  (incident R v).filter (fun e => p.any (fun f => f.1 == e.1))

/-- The boundary word's passes through a vertex: the entering entry
with the leaving one. -/
def passesAt (R : Region) (p : List (Nat × Bool)) (v : Nat) :
    List ((Nat × Bool) × (Nat × Bool)) :=
  (wordPairs p).filter (fun q => endOf R q.1 == v)

/-- A vertex's boundary layout: the boundary character's word pair
`(1, 1)` at each boundary end's orientation in the incident order,
the undaggered slot first at a tail and the daggered first at a
head, the vertex's own signature with a head's slots exchanged. -/
def bdrySig (R : Region) (p : List (Nat × Bool)) (v : Nat) : List Bool :=
  (bdryEnds R p v).flatMap (fun e => slotpower.endWordSig (1, 1) e.2)

/-- A boundary link's position among the vertex's boundary ends. -/
def bdryPos (R : Region) (p : List (Nat × Bool)) (v : Nat) (l : Nat) : Nat :=
  places.idxOf l ((bdryEnds R p v).map Prod.fst)

/-- The boundary character's pairing at a vertex, a place
permutation of the boundary ends: at each pass the entering end's
undaggered slot pairs the leaving end's daggered and the leaving
end's undaggered the entering end's daggered, the two ends
exchanged. -/
def bdryPerm (R : Region) (p : List (Nat × Bool)) (v : Nat) : List Nat :=
  (passesAt R p v).foldl (fun σ q =>
    let a := bdryPos R p v q.1.1
    let b := bdryPos R p v q.2.1
    (σ.set a b).set b a) (List.range (bdryEnds R p v).length)

/-- The boundary character's wiring at a vertex, the wiring tensor
at the boundary layout and its pairing (`con:states`' cycle words
at the trace against its dagger; `slotpower.wiringG`). -/
def bdryWiring (d : Nat) (R : Region) (p : List (Nat × Bool)) (v : Nat) :
    slotpower.GVec :=
  slotpower.wiringG d (bdrySig R p v) (bdryPerm R p v)

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
def blocksAt (ws : List (Nat × Nat)) (bd : List Bool) (ws' : List (Nat × Nat)) :
    List (Nat × Nat × Nat × Nat × Nat × Nat) :=
  ((List.range ws.length).foldl (fun (acc : List _ × Nat × Nat × Nat) t =>
    let li := (getAt (0, 0) ws t).1 + (getAt (0, 0) ws t).2
    let lw := if getAt false bd t then 2 else 0
    let lj := (getAt (0, 0) ws' t).1 + (getAt (0, 0) ws' t).2
    (acc.1 ++ [(acc.2.1, li, acc.2.2.1, lw, acc.2.2.2, lj)],
     acc.2.1 + li, acc.2.2.1 + lw, acc.2.2.2 + lj)) ([], 0, 0, 0)).1

/-- The vertex tensor: at every tuple of the incident links'
member indices the three members' pairing against the links'
members at the vertex's combined slots, the coordinate pairing on
the vertex's slot power — one value per tuple in the tuples'
enumeration order, the fold over the three members' monomial
triples with each link's members read once per triple at the
sub-monomial's rank. -/
def vertexTensor (d : Nat) (mi mw mj : slotpower.GVec)
    (blocks : List (Nat × Nat × Nat × Nat × Nat × Nat))
    (Ys : List (List slotpower.GVec)) : List BPair :=
  let triples := (slotpower.gMons mi).flatMap (fun a =>
    (slotpower.gMons mw).flatMap (fun w => (slotpower.gMons mj).map (fun b =>
      ((a.2 * w.2 * b.2).norm, blocks.map (subMon a.1 w.1 b.1)))))
  let tuples := ground.prodLists (Ys.map (fun Y => List.range Y.length))
  triples.foldl (fun acc tr =>
    let vecs := (List.range Ys.length).map (fun e =>
      let m := getAt [] tr.2 e
      let c := places.content d m
      let r := places.rankOf m c
      (getAt [] Ys e).map (fun y => getAt BPair.unit (slotpower.pieceAt c y) r))
    List.zipWith (fun t a =>
      (a + tr.1 * (List.range Ys.length).foldl (fun pr e =>
        pr * getAt BPair.unit (getAt [] vecs e) (getAt 0 t e)) (BPair.ofNat 1)).norm)
      tuples acc)
    (tuples.map (fun _ => BPair.unit))

/-- The contraction's step at a vertex: per open assignment of the
processed links' members and per tuple of the incident links'
members, a link met at its first end opens at the tuple's member
and a link met at its second end closes at the adjugate weight of
its two members, the value the vertex tensor's at the tuple; the
assignments joined at their keys, the vacant terms withdrawn. -/
def stepVertex (es : List (Nat × Bool)) (Ys : List (List slotpower.GVec))
    (adjs : List elim.Mat) (pv : List BPair)
    (st : List (List Nat × BPair)) : List (List Nat × BPair) :=
  let tuples := ground.prodLists (Ys.map (fun Y => List.range Y.length))
  st.foldl (fun acc kv =>
    (List.zipWith (fun t x => (t, x)) tuples pv).foldl (fun acc2 tp =>
      let r := (List.range es.length).foldl (fun (r : List Nat × BPair) e =>
        let l := (getAt (0, false) es e).1
        let i := getAt 0 tp.1 e
        match getAt 0 r.1 l with
        | 0 => (r.1.set l (i + 1), r.2)
        | j + 1 =>
          (r.1.set l 0,
           r.2 * getAt BPair.unit (getAt [] (getAt [] adjs e) j) i))
        (kv.1, kv.2 * tp.2)
      if decide (r.2.oneValue BPair.unit) then acc2
      else ground.joinBy (fun a b => a == b) (fun y x => (y + x).norm)
        r.1 r.2.norm acc2) acc) []

/-- The plaquette term's entry read between two states at their
fiber keys: the contraction's value with the links' determinants'
product and the states' vertex clearings' product, vacant where a
vertex list is unstated — the entry `Eval(x̄ |tr U_∂p|² y)` the
value over the determinants and the clearings. -/
def termEntry {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (p : List (Nat × Bool))
    (a : List L) (k : List Nat) (b : List L) (k' : List Nat) :
    Option (BPair × BPair × Pos) :=
  let d := lettersOf F
  let ms := (List.range R.verts).map (fun v =>
    (vertexMember F R ix a k v, vertexMember F R ix b k' v))
  if ms.all (fun q => q.1.isSome && q.2.isSome) then
    let mem := fun (o : Option (slotpower.GVec × Pos)) =>
      o.getD ([], Pos.one)
    let wa := (List.range R.links).map (fun l => wordOf F (getAt F.unit a l))
    let wb := (List.range R.links).map (fun l => wordOf F (getAt F.unit b l))
    let bd := (List.range R.links).map (fun l => p.any (fun e => e.1 == l))
    let ld := (List.range R.links).map (fun l =>
      linkDataAt F ix (linkSigAt (getAt (0, 0) wa l) (getAt false bd l)
        (getAt (0, 0) wb l)))
    let st := (List.range R.verts).foldl (fun st v =>
      let es := incident R v
      let Ys := es.map (fun e => (getAt ([], [], BPair.unit) ld e.1).1)
      let adjs := es.map (fun e => (getAt ([], [], BPair.unit) ld e.1).2.1)
      let q := getAt (none, none) ms v
      let pv := vertexTensor d (mem q.1).1 (bdryWiring d R p v) (mem q.2).1
        (blocksAt (es.map (fun e => getAt (0, 0) wa e.1))
          (es.map (fun e => getAt false bd e.1))
          (es.map (fun e => getAt (0, 0) wb e.1))) Ys
      stepVertex es Ys adjs pv st)
      [(List.replicate R.links 0, BPair.ofNat 1)]
    some (keyAt (fun a b => a == b) BPair.unit (List.replicate R.links 0) st,
      ld.foldl (fun acc e => acc * e.2.2) (BPair.ofNat 1),
      ms.foldl (fun acc q => acc * (mem q.1).2 * (mem q.2).2) Pos.one)
  else none

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

/-- The entry read at a window position pair: at stated vertex
lists the magnetic entry joined to the gram's, cleared by the
links' determinants and the states' clearings, one value with the
window's clearing against the contraction; at unstated lists the
loop window's read, the entry the fusion count `N^x_{θ y}` at the
two loop labels at the window's clearing. -/
def entryAt {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (c : Pos) (G M : Mat) (p : List (Nat × Bool))
    (i j : Nat) : Bool :=
  match termEntry F R ix p (posConf F R ix i) (posKey F R ix i)
      (posConf F R ix j) (posKey F R ix j) with
  | some r =>
    decide (((ground.getAt BPair.unit (ground.getAt [] M i) j
        + ground.getAt BPair.unit (ground.getAt [] G i) j)
        * r.2.1 * BPair.ofPos r.2.2).oneValue (BPair.ofPos c * r.1))
  | none =>
    match loopLabel F R p (posConf F R ix i) with
    | none => false
    | some x =>
      match loopLabel F R p (posConf F R ix j) with
      | none => false
      | some y =>
        decide ((ground.getAt BPair.unit (ground.getAt [] M i) j).oneValue
          (BPair.ofPos c * BPair.ofNat (F.count F.theta y x)))

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
count where the lists are unstated. -/
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
