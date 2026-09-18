import MassGap.Ground
/-!
`con:lattice` — the lattice interface: the carrier's region data
are one interface, and every derivation reads the lattice through
its fields.  The fields carried here are the ones the carrier's
index layer reads: the link and vertex counts, each link's tail
and head (the orientation the labels' duality read), the
plaquettes as boundary words of four oriented links, and the
two-coloring of the vertices, the even-cycle read's witness
datum.  The reads: the incident list at a vertex with the
orientation per end; the coloring read (every link's two ends at
the two colors, so every cycle's length is even); the simplicity
read (two vertices sharing at most one link); and the plaquette
read (each boundary a closed word of four oriented links of the
region, the list one listing per plaquette at the cyclic reading
`cycEq`, a boundary word against its rotations at either
traversal).
The direction data with the transverse cuts, the translation
action and the signed coordinate permutations land
with their consumers (`lem:fiberdec`, `lem:chargedcell`,
`thm:restoration`).

The fields read at two instantiation families: the region fields
here — links, vertices, plaquettes, simplicity and the even-cycle
read with its two-coloring witness — are every carrier window's,
while the translation action and the signed coordinate
permutations are the torus family's, where a winding cycle reads
the side's parity and the even-cycle read is refused at odd side
(`fiberdec`'s batteries pin both sides of that separation).
-/

namespace lattice
open ground

set_option genInjectivity false in
/-- The region's carried fields: the link and vertex counts, the
tails and heads per link — each endpoint list at the link count,
the tie the carrier's own field, so the link family reads one way
at the count and at the lists — the plaquette boundaries as
oriented link words, and the vertices' two-coloring, the
even-cycle witness. -/
structure Region where
  links : Nat
  verts : Nat
  tail : List Nat
  head : List Nat
  plaqs : List (List (Nat × Bool))
  color : List Bool
  tailLen : tail.length = links
  headLen : head.length = links

/-- The incident list at a vertex: the link ends reading the
vertex, the outgoing read `true` at the tail and the incoming
`false` at the head — a link at both ends incident once per
end. -/
private def incidentGo (v : Nat) :
    List Nat → List Nat → Nat → List (Nat × Bool)
  | t :: ts, h :: hs, l =>
    ((if t == v then [(l, true)] else [])
      ++ (if h == v then [(l, false)] else []))
      ++ incidentGo v ts hs (l + 1)
  | [], _, _ => []
  | _ :: _, [], _ => []

def incident (R : Region) (v : Nat) : List (Nat × Bool) :=
  incidentGo v R.tail R.head 0

/-- The incident walk reads at the link keys, one entry pair per
key against the endpoint entries. -/
private theorem incidentGo_read (v : Nat) :
    ∀ (tl hd : List Nat) (k : Nat), hd.length = tl.length →
      incidentGo v tl hd k
        = (List.range tl.length).flatMap (fun i =>
            (if getAt 0 tl i == v then [(k + i, true)] else [])
              ++ (if getAt 0 hd i == v then [(k + i, false)] else []))
  | [], _, _, _ => rfl
  | _ :: _, [], _, hl => nomatch hl
  | t0 :: ts, h0 :: hs, k, hl => by
    have hIH := incidentGo_read v ts hs (k + 1) (Nat.succ.inj hl)
    show ((if t0 == v then [(k, true)] else [])
        ++ (if h0 == v then [(k, false)] else []))
        ++ incidentGo v ts hs (k + 1)
      = (List.range (ts.length + 1)).flatMap (fun i =>
          (if getAt 0 (t0 :: ts) i == v then [(k + i, true)] else [])
            ++ (if getAt 0 (h0 :: hs) i == v
              then [(k + i, false)] else []))
    rw [ground.range_cons ts.length]
    show _
      = ((if t0 == v then [(k + 0, true)] else [])
        ++ (if h0 == v then [(k + 0, false)] else []))
        ++ ((List.range ts.length).map (fun j => j + 1)).flatMap
          (fun i =>
            (if getAt 0 (t0 :: ts) i == v then [(k + i, true)] else [])
              ++ (if getAt 0 (h0 :: hs) i == v
                then [(k + i, false)] else []))
    rw [ground.flatMap_map (fun j => j + 1) _ (List.range ts.length),
      ground.flatMap_congr_all _ (fun j =>
          (if getAt 0 ts j == v then [(k + 1 + j, true)] else [])
            ++ (if getAt 0 hs j == v then [(k + 1 + j, false)] else []))
        (fun j => by
          rw [show k + (j + 1) = k + 1 + j from by
            rw [Nat.add_assoc k 1 j, Nat.add_comm 1 j]]
          rfl)
        (List.range ts.length),
      hIH]
    rfl

/-- The incident list reads at the region's link keys: the walk is
the keyed union over the link range, the key chart's own read. -/
theorem incident_read (R : Region) (v : Nat) :
    incident R v
      = (List.range R.links).flatMap (fun l =>
          (if getAt 0 R.tail l == v then [(l, true)] else [])
            ++ (if getAt 0 R.head l == v then [(l, false)] else [])) := by
  have h := incidentGo_read v R.tail R.head 0
    (R.headLen.trans R.tailLen.symm)
  rw [R.tailLen] at h
  show incidentGo v R.tail R.head 0 = _
  rw [h]
  exact ground.flatMap_congr_all _ _ (fun l => by rw [Nat.zero_add]) _

/-- An oriented entry's start: the tail at the forward read, the
head at the reversed. -/
def startOf (R : Region) (e : Nat × Bool) : Nat :=
  if e.2 then getAt 0 R.tail e.1 else getAt 0 R.head e.1

/-- An oriented entry's end, the start's partner. -/
def endOf (R : Region) (e : Nat × Bool) : Nat :=
  if e.2 then getAt 0 R.head e.1 else getAt 0 R.tail e.1

/-- An oriented entry's two ends are its link's tail and head, in
either order. -/
theorem edge_ends (R : Region) (e : Nat × Bool) :
    (startOf R e = getAt 0 R.tail e.1 ∧ endOf R e = getAt 0 R.head e.1)
      ∨ (startOf R e = getAt 0 R.head e.1
        ∧ endOf R e = getAt 0 R.tail e.1) := by
  cases he : e.2 with
  | true =>
    refine Or.inl ⟨?_, ?_⟩
    · show (if e.2 then getAt 0 R.tail e.1 else getAt 0 R.head e.1) = _
      rw [if_pos he]
    · show (if e.2 then getAt 0 R.head e.1 else getAt 0 R.tail e.1) = _
      rw [if_pos he]
  | false =>
    refine Or.inr ⟨?_, ?_⟩
    · show (if e.2 then getAt 0 R.tail e.1 else getAt 0 R.head e.1) = _
      rw [if_neg (ground.boolNe he)]
    · show (if e.2 then getAt 0 R.head e.1 else getAt 0 R.tail e.1) = _
      rw [if_neg (ground.boolNe he)]

/-- The coloring read: every link's two ends at the two colors,
the even-cycle read's witness. -/
def colorRead (R : Region) : Prop :=
  ((R.tail.zip R.head).all (fun e =>
    getAt false R.color e.1 != getAt false R.color e.2)) = true

instance instLattice1 (R : Region) : Decidable (colorRead R) :=
  inferInstanceAs (Decidable (_ = _))

/-- The simplicity read: two vertices share at most one link. -/
def simpleRead (R : Region) : Prop :=
  ((List.range R.verts).all (fun u => (List.range R.verts).all (fun v =>
    ((R.tail.zip R.head).filter (fun e =>
      (e.1 == u && e.2 == v)
        || (e.1 == v && e.2 == u))).length
      ≤ 1))) = true

instance instLattice2 (R : Region) : Decidable (simpleRead R) :=
  inferInstanceAs (Decidable (_ = _))

private def keysDistinct : List (Nat × Bool) → Bool
  | [] => true
  | e :: t => t.all (fun e' => e'.1 != e.1) && keysDistinct t

private def chainClosed (R : Region) : List (Nat × Bool) → Bool
  | [] => true
  | [_] => true
  | e :: e' :: t => (endOf R e == startOf R e') && chainClosed R (e' :: t)

/-- The boundary traversed backwards: the word reversed with every
traversal bit flipped, the field's orientation reversal. -/
def revWord (w : List (Nat × Bool)) : List (Nat × Bool) :=
  (w.reverse).map (fun e => (e.1, !e.2))

/-- Two boundary words one plaquette reading: the words equal, or
a rotation joining the first to the second or to its reversal, the
cyclic word at either traversal. -/
def cycEq (w w' : List (Nat × Bool)) : Bool :=
  decide (w = w')
    || (List.range w'.length).any (fun k => decide (w = ground.rotAt k w'))
    || (List.range w'.length).any (fun k =>
        decide (w = ground.rotAt k (revWord w')))

/-- A boundary word reads its own cyclic word. -/
theorem cycEq_self (w : List (Nat × Bool)) : cycEq w w = true := by
  show (decide (w = w) || _ || _) = true
  rw [decide_eq_true rfl]
  rfl

/-- The moved boundary word: each link at its image key with the
traversal bit carried across the reversal family, the reversal
read at the source key. -/
def moveWord (t : Nat → Nat) (rev : Nat → Bool)
    (w : List (Nat × Bool)) : List (Nat × Bool) :=
  w.map (fun e => (t e.1, xor e.2 (rev e.1)))

/-- The plaquette list at one listing per plaquette: two positions
read one cyclic word exactly where they are one position. -/
private def cycDistinct (ps : List (List (Nat × Bool))) : Bool :=
  (List.range ps.length).all (fun i => (List.range ps.length).all (fun j =>
    (i == j) || !cycEq (ground.getAt [] ps i) (ground.getAt [] ps j)))

/-- The plaquette read: each boundary a closed word of four
distinct oriented links of the region, consecutive ends joined and
the word's last end the first's start, and the list one listing
per plaquette at the cyclic reading, the plaquette set's own
count. -/
def plaqRead (R : Region) : Prop :=
  (R.plaqs.all (fun p =>
    p.length == 4
      && keysDistinct p
      && p.all (fun e => e.1 < R.links)
      && chainClosed R p
      && (match p with
          | [] => true
          | e :: _ =>
            match p.reverse with
            | [] => true
            | e' :: _ => endOf R e' == startOf R e))
    && cycDistinct R.plaqs) = true

instance instLattice3 (R : Region) : Decidable (plaqRead R) :=
  inferInstanceAs (Decidable (_ = _))

/-- The plaquette list is distinct at the plaquette read, the
cyclic reading's structural instance. -/
theorem plaqRead_distinct (R : Region) (h : plaqRead R) :
    distinctList R.plaqs := by
  have hc : cycDistinct R.plaqs = true := (andSplitB h).2
  refine distinct_of_getAt_inj [] R.plaqs (fun p q hp hq heq => ?_)
  have h1 := all_range_read _ (all_range_read _ hc p hp) q hq
  rw [heq, cycEq_self] at h1
  cases hb : (p == q) with
  | true => exact beqEqOf hb
  | false =>
    rw [hb] at h1
    exact absurd h1 (by decide)

/-- A plaquette of the region at the plaquette read: a word of four
entries at the region's link keys. -/
theorem plaqRead_word (R : Region) (h : plaqRead R) (p : List (Nat × Bool))
    (hp : p ∈ R.plaqs) :
    p.length = 4 ∧ (p.all (fun e => e.1 < R.links)) = true := by
  have h1 := (andSplitB h).1
  have hp' := all_of_mem _ R.plaqs h1 p hp
  have h2 := andSplitB hp'
  have h3 := andSplitB h2.1
  have h4 := andSplitB h3.1
  have h5 := andSplitB h4.1
  exact ⟨beqEqOf h5.1, h4.2⟩

/-- The plaquette permutation read at a link map and its reversal
family: the action's plaquette permutation enters as data with its
witness, the two composing to the identity below the count both
ways and each keeping the range, and every boundary's image word
is the moved position's plaquette at the cyclic reading — the
action field's permutation of the plaquettes, read as the induced
vertex map is (`vertIso`). -/
def plaqPermRead (R : Region) (t : Nat → Nat) (rev : Nat → Bool)
    (pm pm' : Nat → Nat) : Prop :=
  ((List.range R.plaqs.length).all (fun q =>
    (pm q < R.plaqs.length) && (pm' q < R.plaqs.length)
      && (pm' (pm q) == q) && (pm (pm' q) == q)
      && cycEq (moveWord t rev (ground.getAt [] R.plaqs q))
          (ground.getAt [] R.plaqs (pm q)))) = true

instance instLattice4 (R : Region) (t : Nat → Nat) (rev : Nat → Bool)
    (pm pm' : Nat → Nat) : Decidable (plaqPermRead R t rev pm pm') :=
  inferInstanceAs (Decidable (_ = _))

/-- The endpoint read of a link map between two regions at a
reversal family: the moved link's tail and head are the vertex
map's values at the link's own, exchanged where the traversal
reverses. -/
def endsMoved (R R' : Region) (t : Nat → Nat) (rev : Nat → Bool)
    (v : Nat → Nat) : Prop :=
  ground.pairIdxAll (fun l tl hd =>
    (getAt 0 R'.tail (t l) == v (if rev l then hd else tl))
      && (getAt 0 R'.head (t l) == v (if rev l then tl else hd)))
    R.tail R.head 0 = true

instance instLattice5 (R R' : Region) (t : Nat → Nat) (rev : Nat → Bool) (v : Nat → Nat) :
    Decidable (endsMoved R R' t rev v) :=
  inferInstanceAs (Decidable (_ = _))

/-- The endpoint read at a link: the moved link's tail and head are
the vertex map's values at the link's own, exchanged where the
traversal reverses. -/
theorem endsMoved_at (R R' : Region) (t : Nat → Nat) (rev : Nat → Bool)
    (v : Nat → Nat) (h : endsMoved R R' t rev v) (l : Nat) (hl : l < R.links) :
    getAt 0 R'.tail (t l)
        = v (if rev l then getAt 0 R.head l else getAt 0 R.tail l)
      ∧ getAt 0 R'.head (t l)
        = v (if rev l then getAt 0 R.tail l else getAt 0 R.head l) := by
  have hb := ground.pairIdxAll_at _ R.tail R.head 0 h l
    (by rw [R.tailLen]; exact hl) (by rw [R.headLen]; exact hl)
  rw [Nat.zero_add] at hb
  have hb' : ((getAt 0 R'.tail (t l)
        == v (if rev l then getAt 0 R.head l else getAt 0 R.tail l))
      && (getAt 0 R'.head (t l)
        == v (if rev l then getAt 0 R.tail l else getAt 0 R.head l)))
      = true := hb
  have h1 := andSplitB hb'
  exact ⟨beqEqOf h1.1, beqEqOf h1.2⟩

/-- A link map's isomorphism read from one region into another
(`con:lattice`'s bijection of the links onto its image): the map
keeps the target's range and its witness reads every source key
back. -/
def linkIso (R R' : Region) (t s : Nat → Nat) : Prop :=
  ((List.range R.links).all (fun l => (t l < R'.links) && (s (t l) == l))) = true

instance instLattice6 (R R' : Region) (t s : Nat → Nat) : Decidable (linkIso R R' t s) :=
  inferInstanceAs (Decidable (_ = _))

/-- A vertex map's isomorphism read from one region into another:
the map keeps the target's range and its witness reads every
source vertex back. -/
def vertIso (R R' : Region) (v w : Nat → Nat) : Prop :=
  ((List.range R.verts).all (fun x => (v x < R'.verts) && (w (v x) == x))) = true

instance instLattice7 (R R' : Region) (v w : Nat → Nat) : Decidable (vertIso R R' v w) :=
  inferInstanceAs (Decidable (_ = _))

/-- A label-graph isomorphism's carrier read from one region into
another at a reversal family (`con:lattice`): the link map and the
vertex map each keep the target's range with the witness reading
every source key back, and the incidence transports along the two,
the orientation kept off the reversal family and exchanged on
it. -/
def isoRead (R R' : Region) (t s v w : Nat → Nat) (rev : Nat → Bool) : Prop :=
  linkIso R R' t s ∧ vertIso R R' v w ∧ endsMoved R R' t rev v

instance instLattice8 (R R' : Region) (t s v w : Nat → Nat) (rev : Nat → Bool) :
    Decidable (isoRead R R' t s v w rev) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The link isomorphism read at a source key: the image below the
target's count and the witness reading the key back. -/
theorem linkIso_at (R R' : Region) (t s : Nat → Nat) (h : linkIso R R' t s)
    (l : Nat) (hl : l < R.links) : t l < R'.links ∧ s (t l) = l := by
  have h1 := andSplitB (all_range_read R.links h l hl)
  exact ⟨of_decide_eq_true h1.1, beqEqOf h1.2⟩

/-- The link isomorphism of a region onto itself reads its witness
below the count at every key with the map reading it back, the
pigeonhole at the key range (`ground.rightInv_of_leftInv`). -/
theorem linkIso_inv (R : Region) (t s : Nat → Nat) (h : linkIso R R t s)
    (l : Nat) (hl : l < R.links) : s l < R.links ∧ t (s l) = l :=
  rightInv_of_leftInv R.links t s (linkIso_at R R t s h) l hl

/-- The link isomorphism of a region onto itself at a key: the two
compositions and the two range reads together. -/
theorem linkIso_all (R : Region) (t s : Nat → Nat) (h : linkIso R R t s)
    (l : Nat) (hl : l < R.links) :
    s (t l) = l ∧ t (s l) = l ∧ t l < R.links ∧ s l < R.links :=
  ⟨(linkIso_at R R t s h l hl).2, (linkIso_inv R t s h l hl).2,
    (linkIso_at R R t s h l hl).1, (linkIso_inv R t s h l hl).1⟩

/-- The vertex isomorphism read at a source vertex. -/
theorem vertIso_at (R R' : Region) (v w : Nat → Nat) (h : vertIso R R' v w)
    (x : Nat) (hx : x < R.verts) : v x < R'.verts ∧ w (v x) = x := by
  have h1 := andSplitB (all_range_read R.verts h x hx)
  exact ⟨of_decide_eq_true h1.1, beqEqOf h1.2⟩

/-- The vertex isomorphism of a region onto itself reads its
witness below the count with the map reading it back. -/
theorem vertIso_inv (R : Region) (v w : Nat → Nat) (h : vertIso R R v w)
    (x : Nat) (hx : x < R.verts) : w x < R.verts ∧ v (w x) = x :=
  rightInv_of_leftInv R.verts v w (vertIso_at R R v w h) x hx

/-- The vertex isomorphism of a region onto itself at a vertex: the
two compositions and the two range reads together. -/
theorem vertIso_all (R : Region) (v w : Nat → Nat) (h : vertIso R R v w)
    (x : Nat) (hx : x < R.verts) :
    w (v x) = x ∧ v (w x) = x ∧ v x < R.verts ∧ w x < R.verts :=
  ⟨(vertIso_at R R v w h x hx).2, (vertIso_inv R v w h x hx).2,
    (vertIso_at R R v w h x hx).1, (vertIso_inv R v w h x hx).1⟩

/-- The vertex map's images compare as their sources below the
count, the witness reading the sources back. -/
theorem vertIso_beq (R : Region) (v w : Nat → Nat) (h : vertIso R R v w)
    (p x : Nat) (hp : p < R.verts) (hx : x < R.verts) :
    (v p == v x) = (p == x) := by
  cases hpx : (p == x) with
  | true =>
    rw [beqEqOf hpx]
    exact eqBeqOf rfl
  | false =>
    refine neBeqOf (fun he => ?_)
    have hpx' : p = x := by
      rw [← (vertIso_all R v w h p hp).1, he, (vertIso_all R v w h x hx).1]
    rw [eqBeqOf hpx'] at hpx
    exact Bool.noConfusion hpx

/-- The plaquette permutation read at a plaquette key: the image
and the witness's image below the count, the two compositions the
key, and the moved word the image's plaquette at the cyclic
reading. -/
theorem plaqPermRead_at (R : Region) (t : Nat → Nat) (rev : Nat → Bool)
    (pm pm' : Nat → Nat) (h : plaqPermRead R t rev pm pm') (q : Nat)
    (hq : q < R.plaqs.length) :
    pm q < R.plaqs.length ∧ pm' q < R.plaqs.length ∧ pm' (pm q) = q
      ∧ pm (pm' q) = q
      ∧ cycEq (moveWord t rev (getAt [] R.plaqs q)) (getAt [] R.plaqs (pm q)) = true := by
  have h1 := all_range_read _ h q hq
  have h2 := andSplitB h1
  have h3 := andSplitB h2.1
  have h4 := andSplitB h3.1
  have h5 := andSplitB h4.1
  exact ⟨of_decide_eq_true h5.1, of_decide_eq_true h5.2, beqEqOf h4.2,
    beqEqOf h3.2, h2.2⟩

/-- A boundary word's fold at its entries' keys is one value across
the cyclic readings: a rotation keeps the entries and the reversal
keeps their keys. -/
theorem cycEq_any_keys (g : Nat → Bool) (w w' : List (Nat × Bool))
    (h : cycEq w w' = true) :
    w.any (fun e => g e.1) = w'.any (fun e => g e.1) := by
  have h' : (decide (w = w')
      || (List.range w'.length).any (fun k => decide (w = rotAt k w'))
      || (List.range w'.length).any (fun k =>
        decide (w = rotAt k (revWord w')))) = true := h
  cases orSplitB h' with
  | inl h1 =>
    cases orSplitB h1 with
    | inl h2 => rw [of_decide_eq_true h2]
    | inr h2 =>
      obtain ⟨k, _, hk⟩ := mem_of_any _ _ h2
      rw [of_decide_eq_true hk, any_rotAt]
  | inr h1 =>
    obtain ⟨k, _, hk⟩ := mem_of_any _ _ h1
    rw [of_decide_eq_true hk, any_rotAt]
    show ((w'.reverse).map (fun e => (e.1, !e.2))).any (fun e => g e.1) = _
    rw [any_map, any_reverse]

/-- A fold over the plaquette list reindexed at an action's
permutation: the moved plaquette's read is the plaquette's. -/
theorem plaqPerm_any (R : Region) (t : Nat → Nat) (rev : Nat → Bool)
    (pm pm' : Nat → Nat) (hpm : plaqPermRead R t rev pm pm')
    (f f' : List (Nat × Bool) → Bool)
    (key : ∀ q, q < R.plaqs.length →
      f' (getAt [] R.plaqs (pm q)) = f (getAt [] R.plaqs q)) :
    R.plaqs.any f' = R.plaqs.any f := by
  cases hb : R.plaqs.any f with
  | true =>
    obtain ⟨p, hp, hpp⟩ := mem_of_any _ R.plaqs hb
    obtain ⟨q, hq, hpq⟩ := getAt_of_mem [] hp
    refine any_of_mem _ (mem_getAt [] R.plaqs (pm q) (plaqPermRead_at R t rev pm pm' hpm q hq).1) ?_
    rw [key q hq, hpq]
    exact hpp
  | false =>
    refine any_false_of_all_not _ _ (all_of_mem_intro _ _ (fun p hp => ?_))
    obtain ⟨q, hq, hpq⟩ := getAt_of_mem [] hp
    have hq' := plaqPermRead_at R t rev pm pm' hpm q hq
    have h3 := all_of_mem _ _ (all_not_of_any_false _ R.plaqs hb) _
      (mem_getAt [] R.plaqs (pm' q) hq'.2.1)
    have hk := key (pm' q) hq'.2.1
    rw [hq'.2.2.2.1] at hk
    rw [← hpq]
    show (!(f' (getAt [] R.plaqs q))) = true
    rw [hk]
    exact h3

/-- The all-fold over the plaquette list reindexed at an action's
permutation. -/
theorem plaqPerm_all (R : Region) (t : Nat → Nat) (rev : Nat → Bool)
    (pm pm' : Nat → Nat) (hpm : plaqPermRead R t rev pm pm')
    (f f' : List (Nat × Bool) → Bool)
    (key : ∀ q, q < R.plaqs.length →
      f' (getAt [] R.plaqs (pm q)) = f (getAt [] R.plaqs q)) :
    R.plaqs.all f' = R.plaqs.all f := by
  cases hb : R.plaqs.all f with
  | true =>
    refine all_of_mem_intro _ _ (fun p hp => ?_)
    obtain ⟨q, hq, hpq⟩ := getAt_of_mem [] hp
    have hq' := plaqPermRead_at R t rev pm pm' hpm q hq
    have hk := key (pm' q) hq'.2.1
    rw [hq'.2.2.2.1] at hk
    rw [← hpq, hk]
    exact all_of_mem _ _ hb _ (mem_getAt [] R.plaqs (pm' q) hq'.2.1)
  | false =>
    cases hb' : R.plaqs.all f' with
    | false => rfl
    | true =>
      have hnot : R.plaqs.all f = true := by
        refine all_of_mem_intro _ _ (fun p hp => ?_)
        obtain ⟨q, hq, hpq⟩ := getAt_of_mem [] hp
        rw [← hpq, ← key q hq]
        exact all_of_mem _ _ hb' _
          (mem_getAt [] R.plaqs (pm q) (plaqPermRead_at R t rev pm pm' hpm q hq).1)
      rw [hnot] at hb
      exact Bool.noConfusion hb

/-- The endpoint read at the vacant reversal family: the moved
link's tail and head are the vertex map's values at the link's
own. -/
theorem endsMoved_vac (R : Region) (t v : Nat → Nat)
    (h : endsMoved R R t (fun _ => false) v) (l : Nat) (hl : l < R.links) :
    getAt 0 R.tail (t l) = v (getAt 0 R.tail l)
      ∧ getAt 0 R.head (t l) = v (getAt 0 R.head l) :=
  endsMoved_at R R t (fun _ => false) v h l hl

/-- The region's shape read: the field lengths at the counts and
every link end below the vertex count. -/
def wellRead (R : Region) : Prop :=
  (R.color.length == R.verts
    && R.tail.all (fun v => v < R.verts)
    && R.head.all (fun v => v < R.verts)) = true

instance instLattice9 (R : Region) : Decidable (wellRead R) :=
  inferInstanceAs (Decidable (_ = _))

/-- Every link's two ends are vertices of the region at the shape
read: the endpoint lists' bounds read at the link key. -/
theorem endLt (R : Region) (hw : wellRead R) (l : Nat)
    (hl : l < R.links) :
    ground.getAt 0 R.tail l < R.verts
      ∧ ground.getAt 0 R.head l < R.verts := by
  have hb : (R.color.length == R.verts
      && R.tail.all (fun v => decide (v < R.verts))
      && R.head.all (fun v => decide (v < R.verts))) = true := hw
  have hw3 := ground.andSplitB hb
  have hw2 := ground.andSplitB hw3.1
  refine ⟨of_decide_eq_true (ground.all_getAt 0 R.tail hw2.2 l ?_),
    of_decide_eq_true (ground.all_getAt 0 R.head hw3.2 l ?_)⟩
  · rw [R.tailLen]
    exact hl
  · rw [R.headLen]
    exact hl

/-- The one-plaquette window: four links around one boundary, the
interface's fields at the unit square (`rem:dictionary`'s lattice
reading), `prop:E0`'s four-link count and `lem:freeend`'s
attainment site. -/
def square : Region :=
  ⟨4, 4, [0, 1, 2, 3], [1, 2, 3, 0],
   [[(0, true), (1, true), (2, true), (3, true)]],
   [true, false, true, false], rfl, rfl⟩

/-- The theta graph, two square plaquettes sharing one link
(`con:fiber`'s displayed definition): seven links at six vertices,
the shared link read backwards on the second boundary. -/
def thetaG : Region :=
  ⟨7, 6, [0, 1, 2, 3, 3, 4, 5], [1, 2, 3, 0, 4, 5, 0],
   [[(0, true), (1, true), (2, true), (3, true)],
    [(4, true), (5, true), (6, true), (3, false)]],
   [true, false, true, false, true, false], rfl, rfl⟩

/-- The square's one boundary, the region's plaquette field
read. -/
def sqPlaq : List (Nat × Bool) := ground.getAt [] square.plaqs 0


/-! A plaquette's pass at a vertex, read at the entries' keys: one
value across the cyclic readings, and moved along a region
action. -/

/-- A plaquette's pass at a vertex, read at the entries' keys
alone. -/
private def keyVert (R : Region) (k x : Nat) : Bool :=
  (getAt 0 R.tail k == x) || (getAt 0 R.head k == x)

private theorem plaqVert_keys (R : Region) (p : List (Nat × Bool)) (x : Nat) :
    p.any (fun e => startOf R e == x || endOf R e == x)
      = p.any (fun e => keyVert R e.1 x) := by
  refine any_congr_all _ _ (fun e => ?_) p
  cases e with
  | mk k b =>
    cases b with
    | true => rfl
    | false =>
      show ((getAt 0 R.head k == x) || (getAt 0 R.tail k == x))
        = ((getAt 0 R.tail k == x) || (getAt 0 R.head k == x))
      rw [Bool.or_comm]

/-- The pass at a vertex is one value across a plaquette's cyclic
readings. -/
theorem plaqVert_cyc (R : Region) (w w' : List (Nat × Bool))
    (hc : cycEq w w' = true) (x : Nat) :
    w.any (fun e => startOf R e == x || endOf R e == x)
      = w'.any (fun e => startOf R e == x || endOf R e == x) := by
  rw [plaqVert_keys, plaqVert_keys]
  exact cycEq_any_keys (fun k => keyVert R k x) w w' hc

/-- The pass at a vertex transports along a region action: the moved
plaquette passes at the moved vertex exactly where the plaquette
passes at the vertex. -/
theorem plaqVert_move (R : Region) (hw : wellRead R) (t s v w : Nat → Nat)
    (h : isoRead R R t s v w (fun _ => false)) (p : List (Nat × Bool))
    (hp : (p.all (fun e => e.1 < R.links)) = true) (x : Nat) (hx : x < R.verts) :
    (moveWord t (fun _ => false) p).any (fun e => startOf R e == v x || endOf R e == v x)
      = p.any (fun e => startOf R e == x || endOf R e == x) := by
  rw [plaqVert_keys, plaqVert_keys]
  show (p.map (fun e => (t e.1, xor e.2 ((fun _ => false) e.1)))).any
      (fun e => keyVert R e.1 (v x)) = _
  rw [any_map]
  refine any_congr_of_mem _ _ p (fun e he => ?_)
  have hk : e.1 < R.links := of_decide_eq_true (all_of_mem _ p hp e he)
  show ((getAt 0 R.tail (t e.1) == v x) || (getAt 0 R.head (t e.1) == v x))
    = ((getAt 0 R.tail e.1 == x) || (getAt 0 R.head e.1 == x))
  rw [(endsMoved_vac R t v h.2.2 e.1 hk).1, (endsMoved_vac R t v h.2.2 e.1 hk).2,
    vertIso_beq R v w h.2.1 _ _ (endLt R hw e.1 hk).1 hx,
    vertIso_beq R v w h.2.1 _ _ (endLt R hw e.1 hk).2 hx]

/-- The per-vertex plaquette count at the family's boxes
(`con:lattice`'s direction read): at two directions or beyond a vertex
sits on at most `2d(d − 1)` plaquettes, four in each plane at the
vertex, and at one direction on at most two, the consecutive squares
sharing one link. -/
def vertexPlaq (d : Nat) : Pos :=
  if d ≤ 1 then 2 else ground.posOfNat (2 * d * (d - 1))

end lattice
