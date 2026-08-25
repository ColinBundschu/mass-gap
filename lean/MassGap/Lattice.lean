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
read (each
boundary a closed word of four oriented links of the region).
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

/-- The coloring read: every link's two ends at the two colors,
the even-cycle read's witness. -/
def colorRead (R : Region) : Prop :=
  ((R.tail.zip R.head).all (fun e =>
    getAt false R.color e.1 != getAt false R.color e.2)) = true

instance (R : Region) : Decidable (colorRead R) :=
  inferInstanceAs (Decidable (_ = _))

/-- The simplicity read: two vertices share at most one link. -/
def simpleRead (R : Region) : Prop :=
  ((List.range R.verts).all (fun u => (List.range R.verts).all (fun v =>
    ((R.tail.zip R.head).filter (fun e =>
      (e.1 == u && e.2 == v)
        || (e.1 == v && e.2 == u))).length
      ≤ 1))) = true

instance (R : Region) : Decidable (simpleRead R) :=
  inferInstanceAs (Decidable (_ = _))

private def keysDistinct : List (Nat × Bool) → Bool
  | [] => true
  | e :: t => t.all (fun e' => e'.1 != e.1) && keysDistinct t

private def chainClosed (R : Region) : List (Nat × Bool) → Bool
  | [] => true
  | [_] => true
  | e :: e' :: t => (endOf R e == startOf R e') && chainClosed R (e' :: t)

/-- The plaquette read: each boundary a closed word of four
distinct oriented links of the region, consecutive ends joined and
the word's last end the first's start. -/
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
            | e' :: _ => endOf R e' == startOf R e))) = true

instance (R : Region) : Decidable (plaqRead R) :=
  inferInstanceAs (Decidable (_ = _))

/-- The region's shape read: the field lengths at the counts and
every link end below the vertex count. -/
def wellRead (R : Region) : Prop :=
  (R.color.length == R.verts
    && R.tail.all (fun v => v < R.verts)
    && R.head.all (fun v => v < R.verts)) = true

instance (R : Region) : Decidable (wellRead R) :=
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

end lattice
