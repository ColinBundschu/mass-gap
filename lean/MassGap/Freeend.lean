import MassGap.Pencil
import MassGap.E0
import MassGap.Casfloor
/-!
`lem:freeend` — the free end's level is the member floor: at the
free end the pencil is its electric member, diagonal over the window
index (`def:pencil`), so the level is the least occupied content —
the read `levelRead`, the display's value at or below every index
content and attained; the window's labels read their Casimirs at or
beyond the floor (`belowFloor`, `lem:casfloor`'s read at the
below-cutoff enumeration); and the attainment is the floor's label
around one plaquette's boundary (`attainConf`, each corner at the
unit law, `prop:E0`'s module its `θ` instance).  `K = ĉ₂(f)` at the
free end: the level reads `4 · dfQ(f)` against `E₀ = 4` at the
cleared second member, the first computed value of the invariant,
pinned at `fusion.dataA`'s committed windows in the check module; at
a member the level is the member's floor, `lem:casfloor`'s
`floorRead` at the member's list, its window reads the member
instantiations' pins through `thm:main`'s wiring in the main
check module (`con:fusion`'s member tier).  A committed window's
read is its enumeration's own, `lem:casfloor`'s floors the levels'
data at the member lists.
-/

namespace freeend
open ground lattice fusion

/-- The attainment: a label around one plaquette's boundary, the
floor label's instance the level's witness, `prop:E0`'s module the
`θ` instance. -/
def attainConf {L : Type} (F : Data L) (R : Region)
    (p : List (Nat × Bool)) (w : L) : List L :=
  (List.range R.links).map (fun l =>
    if p.any (fun e => e.1 == l) then w else F.unit)

/-- `prop:E0`'s module is the attainment's `θ` instance, the two
displays' one value at every interface, region and boundary,
definitional. -/
theorem attainTheta {L : Type} (F : Data L) (R : Region)
    (p : List (Nat × Bool)) :
    attainConf F R p F.theta = E0.moduleConf F R p := rfl

/-- The level read at a window: the value at or below every occupied
content and attained, the least occupied content's display. -/
def levelRead {L : Type} (F : Data L) (R : Region) (C v : Nat) :
    Prop :=
  (let ix := carrier.idx F R C
   (ix.all (fun a => v ≤ carrier.contentN F a))
     && (ix.any (fun a => carrier.contentN F a == v))) = true

instance {L : Type} (F : Data L) (R : Region) (C v : Nat) :
    Decidable (levelRead F R C v) :=
  inferInstanceAs (Decidable (_ = _))

/-- The window's floor read: every below-cutoff label's Casimir at
or beyond the floor, `lem:casfloor`'s read at the window's own
labels. -/
def belowFloor {L : Type} (F : Data L) (K f : Nat) : Prop :=
  ((F.below K).all (fun l => f ≤ F.c2N l)) = true

instance {L : Type} (F : Data L) (K f : Nat) :
    Decidable (belowFloor F K f) :=
  inferInstanceAs (Decidable (_ = _))

/-- The level read at a stated enumeration: the value at or below
every occupied content and attained, read off the committed
index. -/
theorem levelRead_at {L : Type} (F : Data L) (R : Region) (C v : Nat)
    (l : List (List L)) (hl : carrier.idx F R C = l)
    (hv : ((l.all (fun a => v ≤ carrier.contentN F a))
      && (l.any (fun a => carrier.contentN F a == v))) = true) :
    levelRead F R C v := by
  show ((carrier.idx F R C).all (fun a => v ≤ carrier.contentN F a)
    && (carrier.idx F R C).any
      (fun a => carrier.contentN F a == v)) = true
  rw [hl]
  exact hv

end freeend
