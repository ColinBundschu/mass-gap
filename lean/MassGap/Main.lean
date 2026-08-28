import MassGap.Sertables
import MassGap.Row
import MassGap.Closing
import MassGap.Memberdata
import MassGap.Pairpencil
import MassGap.Freecell
import MassGap.Gappos
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
Clause (i) reads at the member through the committed
level sweeps: `clauseI` is the two count-one chains at the floor
window's pair `(E : τ²M)` — `winE` the four-link diagonal and
`winM` the label-index counts (`thm:pairpencil`'s loop-window
read), the covers `lem:cellcount`'s priced pivot nests, the
samples the free end's own splits — flat across the committed
range at `thm:gappos`(iv)'s fixed pair `(ℓ, ℓ + E₀ κ*)` with
`thm:flatstep`'s vacuum-sector jump reads, the tie at the member
pair `κ* = [2 winFloorN − 1 : 4]` positive by its shape, and
`clauseI_counts` carrying both counts to every ray of the range;
the meet over the directed windows — the cut of `def:K` whole —
is the theorem tier's own statement at the chain assembly's
presentation (`thm:pairpencil` with `prop:wg`'s rows), and clause
(iii)'s objects are `thm:continuum`'s continuum reads at the
K-chain's own site.
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

/-- The member floor's numerator, the least nonunit cleared Casimir
(`lem:casfloor`'s displayed minima at the member's clearing): the
`A`-series' fundamental `r (r + 2)`, the `B` member's vector against
its spinor at the displayed trichotomy, the `C` member's first
fundamental, the `D` member's vector (the spinors at or beyond it at
every index, the two tied at the floor index), and the fixed
members' displayed evaluations. -/
def winFloorN : Member → Nat
  | .A g => (g + 1) * (g + 3)
  | .B g => min (8 * (g + 2)) ((g + 2) * (2 * g + 5))
  | .C g => 2 * (2 * g + 7)
  | .D g => 8 * (2 * g + 7)
  | .G2 => 24
  | .F4 => 24
  | .E6 => 104
  | .E7 => 114
  | .E8 => 120

/-- The member's committed window cutoff, the floor content's
four-link read (`lem:freeend`'s member clause at the committed
square). -/
def winCut (m : Member) : Nat := 4 * winFloorN m

/-- The window's label list: the nonunit labels at or below the
floor, the committed square's single-loop index off the vacuum
(`def:carrier`'s window index at the cutoff, each loop's content the
label's four-link read). -/
def winLabels (m : Member) : List places.Shape :=
  (data m).below (winFloorN m)

/-- The window's order, the vacuum with the floor loops — the
committed datum, its enumeration tie `(winLabels m).length + 1`
the check module's pin per member. -/
def winO : Member → Nat
  | .A 0 => 2
  | .A (_ + 1) => 3
  | .B _ => 2
  | .C _ => 2
  | .D 0 => 4
  | .D (_ + 1) => 2
  | .G2 => 2
  | .F4 => 2
  | .E6 => 3
  | .E7 => 2
  | .E8 => 2

/-- The floor window's diagonal at a stated loop value, the unit
line at its head. -/
private def winDiag (o : Nat) (v : BPair) : elim.Mat :=
  ground.matOf o o (fun i j =>
    if i == j then (if i == 0 then BPair.unit else v)
    else BPair.unit)

/-- The window's electric matrix: the diagonal at the one four-link
content with the unit line at its head — every floor label ties at
the floor, the least nonunit read, so the loop block is the content
four times the floor exactly (`def:pencil`'s diagonal `E` at the
label index; `lem:freeend`'s member clause). -/
def winE (m : Member) : elim.Mat :=
  winDiag (winO m) (BPair.ofNat (winCut m))

/-- The window's magnetic matrix at the label index, the interface
counts `M[x, y] = N^x_{θ y}` (`con:xfusion`'s label-index action;
`thm:pairpencil`), the member constructions' committed values
(`con:fusion`'s member clause): the vacuum row `prop:repring`'s
unit read, occupied exactly where `θ` is itself a floor label —
`E8` alone, its coupled row `prop:row`'s base one — the
off-diagonal loop entries vacant at distinct floor labels' classes
and degrees (`lem:chargedcell`(i); `con:labels`), and each floor
label's diagonal one, the word's distinct-value count at the
series (`lem:serstable`(ii)) with the `A`-series' member-key count
(`lem:rankstable`(ii)); the walk ties `pairpencil.loopMag` are the
check module's pins at the walked members, the `E7` and `E8`
walks priced at the standing record. -/
def winM : Member → elim.Mat
  | .A g => winDiag (winO (.A g)) ⟨2, 1⟩
  | .B g => winDiag (winO (.B g)) ⟨2, 1⟩
  | .C g => winDiag (winO (.C g)) ⟨2, 1⟩
  | .D g => winDiag (winO (.D g)) ⟨2, 1⟩
  | .G2 => winDiag 2 ⟨2, 1⟩
  | .F4 => winDiag 2 ⟨2, 1⟩
  | .E6 => winDiag 3 ⟨2, 1⟩
  | .E7 => winDiag 2 ⟨2, 1⟩
  | .E8 => [[BPair.unit, ⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]]

/-- The upper level line `ℓ₊ = 2 winFloorN`, the fixed pair
`(ℓ, ℓ + E₀ κ*)`'s second line (`thm:gappos`(iv)). -/
def winLvl (m : Member) : ground.Pos :=
  ground.posOfSucc (2 * winFloorN m)

/-- The lower level line's cell carrier: the window pair
`(E : τ²M)`'s site datum at the level `1`, `lem:freecell`'s carrier
at the committed window. -/
def sweepLo (m : Member) : split.PMat :=
  freecell.freePMat (winE m) (winM m) (inertia.idMat (winO m)) 2 1

/-- The upper level line's cell carrier, the level `2 winFloorN` —
the fixed pair `(ℓ, ℓ + E₀ κ*)`'s second line
(`thm:gappos`(iv)). -/
def sweepHi (m : Member) : split.PMat :=
  freecell.freePMat (winE m) (winM m) (inertia.idMat (winO m))
    (winLvl m) 1

/-- The committed range's foot, the free end. -/
def winFoot : ground.CPair := ⟨BPair.unit, 1⟩

/-- The committed range's top in the root coordinate, the covered
segment a stated certificate datum (`thm:certconstruct`'s emitted
data; the free cell's whole extent `lem:freecell`'s output). -/
def winTop : ground.CPair := ⟨BPair.ofNat 1, 1⟩

/-- The member's committed cover: the diagonal pivot nest at the
committed range's own magnitude bound. -/
def winCover (m : Member) : cellcount.Cover :=
  cellcount.diagCover winTop ⟨2, 1⟩ ⟨2, 1⟩ (winO m - 1)

/-- The lower sweep's sample at the free end, count one: the
construction's split of the evaluated pair (`lem:inertia`'s
existence clause). -/
def sampleLo (m : Member) : inertia.Split (winO m) :=
  inertia.mkSplit (winO m) (cellcount.evalPC (sweepLo m) BPair.unit 1 2)

/-- The upper sweep's sample at the free end, count one. -/
def sampleHi (m : Member) : inertia.Split (winO m) :=
  inertia.mkSplit (winO m) (cellcount.evalPC (sweepHi m) BPair.unit 1 2)

/-- The lower sweep's one committed cell. -/
def cellsLo (m : Member) :
    List (ground.CPair × cellcount.Cover
      × (BPair × ground.Pos) × inertia.Split (winO m)) :=
  [(winTop, winCover m, (BPair.unit, 1), sampleLo m)]

/-- The upper sweep's one committed cell. -/
def cellsHi (m : Member) :
    List (ground.CPair × cellcount.Cover
      × (BPair × ground.Pos) × inertia.Split (winO m)) :=
  [(winTop, winCover m, (BPair.unit, 1), sampleHi m)]

/-- Clause (i) at a member: the two committed level sweeps at the
member's floor window, count one flat across the committed range —
`thm:gappos`(iv)'s fixed pairs with `thm:flatstep`'s vacuum-sector
jump reads — and the tie `ℓ₀ + E₀ κ* ≤ ℓ₊` at the committed member
pair `κ* = [2 winFloorN − 1 : 4]` at `E₀ = 4` (`prop:E0`'s
four-link count, the tie's inner factor), κ* positive by its
shape; the window's cut at consumer-stated diagonalization data is
`gappos.windowCut`'s read, and the cut of `def:K` — the meet over
the directed windows — reads at the chain assembly's presentation
(`thm:pairpencil` with `prop:wg`'s rows), its own statement's
site. -/
def clauseI (m : Member) : Prop :=
  gappos.chainRead (sweepLo m) 2 1 winFoot (cellsLo m)
  ∧ gappos.chainRead (sweepHi m) 2 1 winFoot (cellsHi m)
  ∧ BPair.scale (⟨2, 1⟩ : BPair) 4
      + BPair.ofPos (4 * ground.posOfSucc (2 * winFloorN m - 2))
    ≤ BPair.scale (⟨winLvl m, 1⟩ : BPair) 4

instance (m : Member) : Decidable (clauseI m) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The counts carried to every ray of the committed range: at
clause (i)'s read both level lines' counts read one at every pair
point from the foot to the top, `gappos.chainCount` at the two
committed chains — the flat window `thm:flatstep`'s comparisons
consume. -/
theorem clauseI_counts (m : Member) (h : clauseI m)
    (vn : BPair) (vc : ground.Pos)
    (h1 : winFoot ≤ (⟨vn, vc⟩ : ground.CPair))
    (h2 : (⟨vn, vc⟩ : ground.CPair) ≤ winTop) :
    (∀ sp : inertia.Split (winO m),
      inertia.splitRead (cellcount.evalPC (sweepLo m) vn vc 2) sp →
        inertia.revAt sp = 1)
    ∧ (∀ sp : inertia.Split (winO m),
      inertia.splitRead (cellcount.evalPC (sweepHi m) vn vc 2) sp →
        inertia.revAt sp = 1) :=
  ⟨fun sp hsp => gappos.chainCount (sweepLo m) 2 1 winFoot
      (winTop, winCover m, (BPair.unit, 1), sampleLo m) [] h.1
      vn vc h1 h2 sp hsp,
   fun sp hsp => gappos.chainCount (sweepHi m) 2 1 winFoot
      (winTop, winCover m, (BPair.unit, 1), sampleHi m) [] h.2.1
      vn vc h1 h2 sp hsp⟩

end main
