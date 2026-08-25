import MassGap.Sertables
import MassGap.Row
import MassGap.Closing
import MassGap.Memberdata
/-!
`thm:main` — the statement over the classification's stated
domain, the member a carried datum: the `A`-series at the declared
residue, the three series at their index floors and the five fixed
members, each member once, the floors the successor spellings' own
(`Member`'s arguments read `r = g + 1`, `ℓ = g + 2`, `ℓ = g + 3`,
`ℓ = g + 4`, the domain the type).  The member's weight table is
the carried datum's read (`con:sertables`; `con:gentable`'s first
table at the `A`-series), the derived residue and the base θ's
coroot-support count its table reads (`prop:row`).  Clause (ii)
closes at every member: `clauseII` is `thm:closing`'s read at the
member's own base and residue, the lattice point `(3, H_r)`, its
member instantiations the check module's pins with the low-index
coincidence reads beside them (`Sp(1)` at `SU(2)` the one exact
table identity, `Sp(2)` at `Spin(5)` and `Spin(6)` at `SU(4)` the
derived reads' agreements across the relabelings; `Spin(3)` at
`SU(2)` is the dictionary's identification alone — the displayed
`B`-form at `ℓ = 1` reads θ short, its below-floor table
degenerate by the residue read's own refusal).  The wiring `data`
carries each member's fusion interface instantiation
(`con:fusion`'s member clause at the weight tables — every chain
derivation reads the fusion data through the fields, at every
member at once — with the label calculus's `dataA` at the
`A`-series), the pencil layer reading at every member through the
one carried datum: the free-end level is the member's floor at
the committed windows (`lem:freeend`'s member clause) with the
cut holding at every pair at or below the floor and failing
beyond (`def:K`'s free-end reading), each window's test
`K.cutRead`'s read at its certificate, the check module's pins.
Clause (i)'s membership — the meet over the directed windows —
is the theorem's own statement, arriving with the chain assembly
(`thm:pairpencil`'s presentation with `prop:wg`'s rows); clause
(iii)'s objects — the continuum reads of `thm:continuum` —
arrive with the K-chain transcription, its Prop landing with
them at its site.
-/

namespace main
open ground

set_option genInjectivity false in
/-- The classification's stated domain, each member once: the
`A`-series at the declared residue `r = g + 1`, the series at
their index floors (`B` at `ℓ = g + 2`, `C` at `ℓ = g + 3`, `D`
at `ℓ = g + 4`), and the five fixed members. -/
inductive Member where
  | A (g : Nat)
  | B (g : Nat)
  | C (g : Nat)
  | D (g : Nat)
  | G2
  | F4
  | E6
  | E7
  | E8

/-- The member's weight table, the carried datum's read. -/
def table : Member → gentable.Table
  | .A g => gentable.tableA (g + 1)
  | .B g => sertables.tableB (g + 2)
  | .C g => sertables.tableC (g + 3)
  | .D g => sertables.tableD (g + 4)
  | .G2 => sertables.tableG2
  | .F4 => sertables.tableF4
  | .E6 => sertables.tableE6
  | .E7 => sertables.tableE7
  | .E8 => sertables.tableE8

/-- The member's derived residue, the table's one fold. -/
def residue (m : Member) : Nat := gentable.residue (table m)

/-- The member's base, θ's coroot-support count. -/
def base (m : Member) : Nat := row.supportCount (table m)

/-- The member's fusion interface, the carried datum's
instantiation read: the label calculus's `dataA` at the `A`-series'
fundamental count (`con:fusion`'s own instantiation) and the member
instantiations at the weight tables (`con:fusion`'s member clause,
`lem:memberdata`'s constructions), the floors the successor
spellings' own beside `table`'s. -/
def data : Member → fusion.Data places.Shape
  | .A g => fusion.dataA (g + 2)
  | .B g => fusion.dataB (g + 2)
  | .C g => fusion.dataC (g + 3)
  | .D g => fusion.dataD (g + 4)
  | .G2 => fusion.dataG2
  | .F4 => fusion.dataF4
  | .E6 => fusion.dataE6
  | .E7 => fusion.dataE7
  | .E8 => fusion.dataE8

/-- Clause (ii) at a member: the contact pair reads the lattice
point `(3, H_r)` at the member's own base and residue,
`thm:closing`'s read off the carried datum. -/
def clauseII (m : Member) : Prop := closing.read (base m) (residue m)

instance (m : Member) : Decidable (clauseII m) :=
  inferInstanceAs (Decidable (closing.read _ _))

end main
