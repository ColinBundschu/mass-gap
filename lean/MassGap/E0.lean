import MassGap.Carrier
/-!
`prop:E0` — the module at the free end: the configuration assigning
`θ` to each link of a plaquette's boundary, the unit off them
(`moduleConf`), its content the four-link fold `4 C₂(θ)`
(`contentRead`, the boundary's four distinct links `con:lattice`'s
plaquette read), the count `E₀ = 4` read against `C₂(adj)`; the
module is occupied, each corner's multiplicity the unit law's read
at the self-dual `θ` (`occRead`); and at a cutoff admitting its
content it is a member of the window index (`memberRead`), an
eigenvector of the diagonal electric member at its content's
eigenvalue (`def:pencil`'s diagonal).  The statement's second
carrier is the coefficient carrier's per-link block scaling
(`con:coeff`, a matrix coefficient of `λ` differentiating to one);
its theta-graph instance is the invariant fiber's presentation
eigen-read at the module level through `prop:lap`'s derivation
action, `con:twoplaq`'s `eAct` at `lvlE` read at the wiring keys
with the check module's pins there, `4 d_f` at the trace form
against this module's `4 C₂(θ)` at `con:twoplaq`'s conversion
clause.
-/

namespace E0
open ground lattice fusion

/-- The module's configuration: `θ` on the plaquette's links, the
unit off them. -/
def moduleConf {L : Type} (F : Data L) (R : Region)
    (p : List (Nat × Bool)) : List L :=
  (List.range R.links).map (fun l =>
    if p.any (fun e => e.1 == l) then F.theta else F.unit)

/-- The four-link content read: `4 C₂(θ)` at the cleared second
member, the count `E₀ = 4` at the weight. -/
def contentRead {L : Type} (F : Data L) (R : Region)
    (p : List (Nat × Bool)) : Prop :=
  carrier.contentN F (moduleConf F R p) = 4 * F.c2N F.theta

instance {L : Type} (F : Data L) (R : Region)
    (p : List (Nat × Bool)) : Decidable (contentRead F R p) :=
  inferInstanceAs (Decidable (_ = _))

/-- The module's occupancy: every corner at a positive multiplicity,
the unit law's read at the self-dual `θ`. -/
def occRead {L : Type} (F : Data L) (R : Region)
    (p : List (Nat × Bool)) : Prop :=
  carrier.occupied F R (moduleConf F R p) = true

instance {L : Type} (F : Data L) (R : Region)
    (p : List (Nat × Bool)) : Decidable (occRead F R p) :=
  inferInstanceAs (Decidable (_ = _))

/-- The membership read: the module a member of the window index at
a cutoff admitting its content, the eigen-read's index form at the
diagonal electric member. -/
def memberRead {L : Type} (F : Data L) (R : Region) (C : Nat)
    (p : List (Nat × Bool)) : Prop :=
  ((carrier.idx F R C).any (fun a =>
    carrier.eqConf F a (moduleConf F R p))) = true

instance {L : Type} (F : Data L) (R : Region) (C : Nat)
    (p : List (Nat × Bool)) : Decidable (memberRead F R C p) :=
  inferInstanceAs (Decidable (_ = _))

end E0
