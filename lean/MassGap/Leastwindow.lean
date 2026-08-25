import MassGap.Carrier
/-!
`prop:leastwindow` — every element has a least window, read off its
index support: the index support is representative-free (the
inclusions are summand injections, so the index is the datum
itself), and an element's window data are counts off it — the
support links over the member configurations (`windowLinks`), their
touched vertices (`windowVerts`), and the members' largest content
(`windowContent`, the max fold).  A probe is an element of the
carrier, and its window is this one.  The multiplication window
bound `A · Sect(Λ, C) ⊆ Sect(Λ_A ∪ Λ, Φ(C_A, C))` reads at the
changed edge's targets (`def:algebra`'s row), its instances the
check module's pins; the attained maximum `Φ` over a fusion row
lands at `prop:fusionfinite`'s layer with the content-ball
comparison, and the colimit's summand injections stay at the prose,
the reads the counts above.
-/

namespace leastwindow
open ground lattice fusion

/-- A configuration's support links, the occupied keys. -/
def suppLinks {L : Type} (F : Data L) (a : List L) : List Nat :=
  carrier.occKeys F a.length a

/-- An element's support links over its index members, the region's
key order. -/
def windowLinks {L : Type} (F : Data L) (R : Region)
    (as : List (List L)) : List Nat :=
  (List.range R.links).filter (fun l =>
    as.any (fun a => !(F.eqL (getAt F.unit a l) F.unit)))

/-- An element's touched vertices over its index members. -/
def windowVerts {L : Type} (F : Data L) (R : Region)
    (as : List (List L)) : List Nat :=
  (List.range R.verts).filter (fun v =>
    as.any (fun a => (carrier.incidentLabels F R a v).length != 0))

/-- The window content, the members' largest content, the max
fold. -/
def windowContent {L : Type} (F : Data L) (as : List (List L)) : Nat :=
  as.foldl (fun m a => Nat.max m (carrier.contentN F a)) 0

end leastwindow
