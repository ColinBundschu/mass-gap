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
entries at weights of the positive carrier (`pencilH`, the free end's
own diagonal read `pencilE`, `symmRead` the transpose's
one-value read).  The pencil interface is the fields a window's
pencil enters every derivation through, read positionally at the
window list — the unit line at position zero, then per index member
its fiber's slot keys, one digit per vertex below the vertex's
multiplicity (`slotKeys`, `def:carrier`'s tensor product over the
touched vertices, its count the fiber's multiplicity product at
`length_slotKeys`; `slotList` over a stated index, distinct over a
distinct index at `slotList_distinct`; `posConf` the configuration
at a position): the order tie at the window list's count
(`prop:windowfinite`'s `dimSect`, `slotList_dimSect`), the electric
member the window list's diagonal at each slot's content with the
unit line at the sum's unit (`slotDiag`, `def:pencil`; at unit fiber
products the index's contents outright, `slotDiag_unit`), the
gram block diagonal over the index at the fibers' pairings with the
unit line at one and positive definite at its split
(`gramBlockRead`, `def:carrier`), and the magnetic member the
plaquette terms' sum (`termSum`), each term symmetric, capped
two-sidedly as a form at the adjoint dimension's multiple of the
gram (`lem:loopcap`; `inertia.capAt` at the two splits) and
supported across its changed edge alone — an entry off the sum's
unit at a position pair one of whose configurations is the other's
target on the plaquette's row (`termSupport` at `def:algebra`'s
row, the far reads' factorization the vacant complement,
`lem:stableentries`) — the terms' reads along the region's
plaquette list (`termsRead`) and the whole `pencilRead`, every read
at a stated index tied to the window's own; at a loop
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
`α E = β M + H`: the electric diagonal at the first weight against
the magnetic matrix at the second, every entry a pair datum at pair
weights. -/
def pencilH (al be : Pos) (diag : List Nat) (M : Mat) : Mat :=
  ground.matOf diag.length diag.length (fun i j =>
      ((if i == j
          then BPair.ofPos al * BPair.ofNat (ground.getAt 0 diag i)
          else BPair.unit)
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

/-- The gram's block read: the unit line at one, and two positions
at distinct index members pairing at the sum's unit — the fibers'
orthogonal sum with the unit line's pairing at one
(`def:carrier`). -/
def gramBlockRead {L : Type} (F : Data L) (R : Region) (n : Nat)
    (ix : List (List L)) (G : Mat) : Prop :=
  (ground.getAt BPair.unit (ground.getAt [] G 0) 0).oneValue
      (BPair.ofPos Pos.one)
  ∧ ((List.range n).all (fun i => (List.range n).all (fun j =>
      carrier.eqConf F (posConf F R ix i) (posConf F R ix j)
        || decide ((ground.getAt BPair.unit
            (ground.getAt [] G i) j).oneValue BPair.unit)))) = true

instance {L : Type} (F : Data L) (R : Region) (n : Nat) (ix : List (List L))
    (G : Mat) : Decidable (gramBlockRead F R n ix G) :=
  inferInstanceAs (Decidable (_ ∧ _ = _))

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
        || carrier.confMem F (posConf F R ix j)
            (algebra.plaqRow F R p (posConf F R ix i))
        || carrier.confMem F (posConf F R ix i)
            (algebra.plaqRow F R p (posConf F R ix j))))) = true

instance {L : Type} (F : Data L) (R : Region) (n : Nat) (ix : List (List L))
    (p : List (Nat × Bool)) (M : Mat) :
    Decidable (termSupport F R n ix p M) :=
  inferInstanceAs (Decidable (_ = _))

/-- The plaquette terms' reads along the region's plaquette list,
each term with its two cap splits: symmetric, capped two-sidedly at
the adjoint dimension's multiple of the gram (`lem:loopcap`, the
cap reading the term's order), and supported across its changed
edge. -/
def termsRead {L : Type} (F : Data L) (R : Region) (n : Nat)
    (ix : List (List L)) (G : Mat) :
    List (List (Nat × Bool)) → List (Mat × Split n × Split n) → Prop
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | p :: ps, t :: ts =>
    symmRead t.1
    ∧ capAt t.1 (matScaleB (BPair.ofNat (F.dim F.theta)) G) t.2.1 t.2.2
    ∧ termSupport F R n ix p t.1
    ∧ termsRead F R n ix G ps ts

instance decTermsRead {L : Type} (F : Data L) (R : Region) (n : Nat)
    (ix : List (List L)) (G : Mat) :
    (ps : List (List (Nat × Bool))) →
    (ts : List (Mat × Split n × Split n)) →
    Decidable (termsRead F R n ix G ps ts)
  | [], [] => inferInstanceAs (Decidable True)
  | [], _ :: _ => inferInstanceAs (Decidable False)
  | _ :: _, [] => inferInstanceAs (Decidable False)
  | _ :: ps, _ :: ts =>
    have : Decidable (termsRead F R n ix G ps ts) :=
      decTermsRead F R n ix G ps ts
    inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The plaquette terms' sum, the magnetic member assembled from
its terms at the order. -/
def termSum (n : Nat) (terms : List (Mat × Split n × Split n)) : Mat :=
  terms.foldl (fun acc t => matAdd acc t.1) (nullMat n n)

/-- The pencil interface's read at a window: the stated index the
window's own, the order tie at the window list's count, the
electric member the window list's diagonal, the gram's block read
at its positive-definite split (the split reading the gram's
order), the magnetic member the plaquette terms' sum, and the
plaquette terms' reads along the region's plaquettes —
`thm:pairpencil`'s fields at a stated pencil over the stated
index. -/
def pencilRead {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (C n : Nat) (ix : List (List L)) (E G M : Mat) (spG : Split n)
    (terms : List (Mat × Split n × Split n)) : Prop :=
  carrier.idx F R C = ix
  ∧ windowfinite.dimSect F R C = n
  ∧ sqAt E n
  ∧ matOneValue E (pencilE (slotDiag F R ix))
  ∧ gramBlockRead F R n ix G ∧ splitRead G spG ∧ pdAt spG
  ∧ termsRead F R n ix G R.plaqs terms
  ∧ matOneValue M (termSum n terms)

instance {L : Type} [DecidableEq L] (F : Data L) (R : Region) (C n : Nat)
    (ix : List (List L)) (E G M : Mat) (spG : Split n)
    (terms : List (Mat × Split n × Split n)) :
    Decidable (pencilRead F R C n ix E G M spG terms) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

end pairpencil
