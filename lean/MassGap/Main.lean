import MassGap.Sertables
import MassGap.Row
import MassGap.Closing
import MassGap.Memberdata
import MassGap.Pairpencil
import MassGap.Freecell
import MassGap.Gappos
import MassGap.Cornerstore
import MassGap.Cornerfloor
/-!
`thm:main` — the statement over the classification's stated
domain, the member a carried datum: the `A`-series at the declared
residue, the three series at their index floors and the five fixed
members, each member once, the floors the successor spellings' own
(`Member`'s arguments read `r = g + 1`, `ℓ = g + 2`, `ℓ = g + 3`,
`ℓ = g + 4`, the domain the type).  The member's weight table is
the carried datum's read (`con:sertables`; `con:gentable`'s first
table at the `A`-series), the derived residue and the base θ's
coroot-support count its table reads (`prop:row`).  Clause (ii) reads
at every member: the contact end's walk is the head's compression
to the tower labels (`prop:row`), and `clauseII`
is the walk's two divisor reads at the member's own base and
residue, the lattice point `(3, H_r)` (`thm:closing`'s componentwise
read), held at the whole domain by `clauseII_all` through the
occupancy door (`closing.read_pos` at the tables' support and
residue reads); the clause's window half, the cut's edge at every
window and coupling a located root of the window's symbol attained
at a word image, is `attained.attained_at` at the window matrices
with the root read `divisorid.rootIff`, stated at the tex's own
quantifier.  The member instantiations are the
check module's pins with the low-index
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
Clause (i)'s floor-window instance reads at the member through
the committed level sweeps: `clauseI` is one window cut of
`def:K`, the two count-one chains at the floor
window's pair `(E : τ²M)` — `winE` the four-link diagonal and
`winM` the label-index counts (`thm:pairpencil`'s loop-window
read), the covers `lem:cellcount`'s priced pivot nests, the
samples the free end's own splits — flat across the committed
range at `thm:gappos`(iv)'s fixed pair `(ℓ, ℓ + E₀ κ*)` with
`thm:flatstep`'s vacuum-sector jump reads, the tie at the member
pair `κ* = [2 winFloorN − 1 : 4]` positive by its shape, and
`clauseI_counts` carrying both counts to every ray of the range,
the clause held at the whole domain by `clauseI_all` through the
parametric window sweeps at the member's floor numerator — the
series and the diagonal-window fixed members at the two level
lines' chain generals, one per window order, with `D₄`'s four-loop
window and `E₈`'s coupled window decided by kernel reduction.
The cut of `def:K` is the meet of the window cuts over the
directed family at every interior ray; `clauseI` reads it at the
floor window over the committed range, one window cut per member
at the floor numerator's cutoff.
Clause (iii)'s corner cell reads at the member through the one
certificate transported across the residues
(`lem:cornerpivot`(vi)): `clauseIII` is `lem:corner`'s cell-floor
datum at the member's derived residue, the member's tail scale
`[1 : 524288(r+1)²]` (`cornerScaleD`, the ceiling at the residue's
successor squared) and its endpoint key (`cornerKey`, the least
natural beyond one at the key's comparison `keyRead`, the search
bounded at the comparison's stated witness `2000(r+1)²`), the
residue-one cell at the cut member `[41 : 40]` at the `A`-series'
first member (`cellS`) and the transported cell at `[6 : 5]` at every
further member (`cellT`); the datum's reads are the flat window at
the member line (`corner.cut_flat_T`, `corner.cut_flat_S`), the floor
positive by its shape (`corner.floor_pos`) and the chain's ground at
or below the line (`corner.ground_below_line`).  The clause is held
at the whole domain by `clauseIII_all`: the key's read at the member
scale (the comparison at the stated witness, the leastness the
search's own), the key at or beyond the ceiling's own — beyond `1652`
at every residue at or beyond two and beyond `1495` at the residue
one — and clearing twenty residues, the tied scale under the
ceiling, and the cut member's line under the transported rate
(`cornerpivot.resRate`, `cornerpivot.oneRate`), the series through
their residue reads and the fixed members' residues decided by kernel
reduction.
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

/-- Clause (ii)'s contact-end read at a member: the walk's two
divisor reads, the contact pair, read the lattice point `(3, H_r)`
at the member's own base and residue, `thm:closing`'s componentwise
read off the carried datum. -/
def clauseII (m : Member) : Prop := closing.read (base m) (residue m)

instance (m : Member) : Decidable (clauseII m) :=
  inferInstanceAs (Decidable (closing.read _ _))

/-- Clause (ii)'s pair arithmetic at the whole `A`-series: the occupancy door
(`closing.read_pos`) at the first table's support and residue
reads. -/
theorem clauseII_A (g : Nat) : clauseII (.A g) :=
  closing.read_pos _ _
    (row.supportCount_tableA_pos (g + 1) (Nat.succ_pos g))
    (gentable.residue_tableA_pos (g + 1) (Nat.succ_pos g))

/-- Clause (ii)'s pair arithmetic at the whole `B`-series: the occupancy door at the
member table's support and residue reads. -/
theorem clauseII_B (g : Nat) : clauseII (.B g) :=
  closing.read_pos _ _
    (row.supportCount_tableB_pos g)
    (sertables.residue_tableB_pos g)

/-- Clause (ii)'s pair arithmetic at the whole `C`-series: the occupancy door at the
member table's support and residue reads. -/
theorem clauseII_C (g : Nat) : clauseII (.C g) :=
  closing.read_pos _ _
    (row.supportCount_tableC_pos g)
    (sertables.residue_tableC_pos g)

/-- Clause (ii)'s pair arithmetic at the whole `D`-series: the occupancy door at the
member table's support and residue reads. -/
theorem clauseII_D (g : Nat) : clauseII (.D g) :=
  closing.read_pos _ _
    (row.supportCount_tableD_pos g)
    (sertables.residue_tableD_pos g)

/-- Clause (ii)'s pair arithmetic at every member of the
classification: the series
through the occupancy door at their tables' support and residue
reads, the fixed members' occupancies decided by kernel
reduction. -/
theorem clauseII_all : ∀ m : Member, clauseII m
  | .A g => clauseII_A g
  | .B g => clauseII_B g
  | .C g => clauseII_C g
  | .D g => clauseII_D g
  | .G2 => closing.read_pos _ _ (by decide +kernel) (by decide +kernel)
  | .F4 => closing.read_pos _ _ (by decide +kernel) (by decide +kernel)
  | .E6 => closing.read_pos _ _ (by decide +kernel) (by decide +kernel)
  | .E7 => closing.read_pos _ _ (by decide +kernel) (by decide +kernel)
  | .E8 => closing.read_pos _ _ (by decide +kernel) (by decide +kernel)

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

/-- Clause (i)'s floor-window instance at a member, one window cut
of `def:K`: the two committed level sweeps at the
member's floor window, count one flat across the committed range —
`thm:gappos`(iv)'s fixed pairs with `thm:flatstep`'s vacuum-sector
jump reads — and the tie `ℓ₀ + E₀ κ* ≤ ℓ₊` at the committed member
pair `κ* = [2 winFloorN − 1 : 4]` at `E₀ = 4` (`prop:E0`'s
four-link count, the tie's inner factor), κ* positive by its
shape; the window's cut at consumer-stated diagonalization data is
`gappos.windowCut`'s read, one member of the meet the cut of
`def:K` takes over the directed windows. -/
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

/-! The window sweeps' parametric reads: the two level lines'
carriers at a stated order, the loop head's two-coefficient value and its cube
with their priced side reads, the deflation kit at an abstract pencil,
and the member floors' lower bounds — clause (i)'s proof at every
series at once, one chain general per order. -/

/-- The lower level line's parametric carrier at a stated order
and four-link cutoff: the window pair `(E : τ²M)`'s site datum at the
level `1` (`lem:freecell`'s carrier at the committed window). -/
private def sLo (o cut : Nat) : split.PMat :=
  freecell.freePMat (winDiag o (BPair.ofNat cut)) (winDiag o ⟨2, 1⟩)
    (inertia.idMat o) 2 1

/-- The upper level line's parametric carrier at a stated order and
floor numerator, the level `2 F`. -/
private def sHi (o F : Nat) : split.PMat :=
  freecell.freePMat (winDiag o (BPair.ofNat (4 * F))) (winDiag o ⟨2, 1⟩)
    (inertia.idMat o) (ground.posOfSucc (2 * F)) 1

/-! The window carriers' entry reads: `lem:freecell`'s display at
the diagonal window, each entry the one polynomial list — the
level datum's entry at the constant key (`def:pencil`'s join at
`thm:certconstruct`'s cross-added level), the unit middle, and the
magnetic member's balance partner at the top key — read off the
stated displays (`freecell.freePMat_entry`;
`inertia.siteDatum_entry`; the diagonal's own `matOf` read at
`def:pencil`'s diagonal `E` with `lem:freeend`'s member clause). -/

/-- The floor window's diagonal keeps the stated order. -/
private theorem sqAt_winDiag (o : Nat) (v : BPair) :
    elim.sqAt (winDiag o v) o :=
  elim.sqAt_of (ground.matOf_length o o _) (elim.rowsLen_matOf o o _)

/-- The floor window's diagonal at an entry: the loop value at the
occupied diagonal keys, the unit line at its head, the vacant
couplings at the sum's unit. -/
private theorem winDiag_entry (o : Nat) (v : BPair) (i j : Nat)
    (hi : i < o) (hj : j < o) :
    getAt BPair.unit (getAt [] (winDiag o v) i) j
      = if i == j then (if i == 0 then BPair.unit else v)
        else BPair.unit :=
  ground.matOf_entry [] BPair.unit o o _ i j hi hj

/-- The window carrier's entry at any key pair inside the order,
the displays composed: the diagonal reads at their guards with the
identity gram's level weights. -/
private theorem winEntry (o : Nat) (v w : BPair) (x y : Pos)
    (i j : Nat) (hi : i < o) (hj : j < o) :
    getAt [] (getAt [] (freecell.freePMat (winDiag o v)
        (winDiag o w) (inertia.idMat o) x y) i) j
      = (((if i == j then (if i == 0 then BPair.unit else v)
            else BPair.unit)
          + (if j = i then BPair.ofNat 1 else BPair.unit).scale y)
        + ((if j = i then BPair.ofNat 1 else BPair.unit).scale x).swap)
        :: ([BPair.unit]
            ++ [(if i == j then (if i == 0 then BPair.unit else w)
                else BPair.unit).swap]) := by
  have hScY : elim.sqAt (inertia.matScale y (inertia.idMat o)) o :=
    inertia.sqAt_matScale o y _ (inertia.sqAt_idMat o)
  have hScX : elim.sqAt (inertia.matScale x (inertia.idMat o)) o :=
    inertia.sqAt_matScale o x _ (inertia.sqAt_idMat o)
  have hAdd : elim.sqAt (elim.matAdd (winDiag o v)
      (inertia.matScale y (inertia.idMat o))) o :=
    elim.sqAt_matAdd o _ _ (sqAt_winDiag o v) hScY
  have hIdRow : j < (getAt ([] : List BPair)
      (inertia.idMat o) i).length := by
    rw [elim.rowsLen_getAt _ i (inertia.idMat_rows o)
        (by rw [inertia.idMat_len]; exact hi)]
    exact hj
  rw [freecell.freePMat_entry (winDiag o v) (winDiag o w)
      (inertia.idMat o) x y o (sqAt_winDiag o v) (sqAt_winDiag o w)
      (inertia.sqAt_idMat o) i j hi hj,
    inertia.siteDatum_entry _ _ o (elim.rowsLen_of_sqAt hAdd)
      (elim.rowsLen_of_sqAt hScX) i j
      (by rw [elim.sqAt_len hAdd]; exact hi)
      (by rw [elim.sqAt_len hScX]; exact hi) hj,
    elim.entry_matAdd _ _ o
      (elim.rowsLen_of_sqAt (sqAt_winDiag o v))
      (elim.rowsLen_of_sqAt hScY) i j
      (by rw [elim.sqAt_len (sqAt_winDiag o v)]; exact hi)
      (by rw [elim.sqAt_len hScY]; exact hi) hj,
    inertia.matScale_entry y (inertia.idMat o) i j
      (by rw [inertia.idMat_len]; exact hi) hIdRow,
    inertia.matScale_entry x (inertia.idMat o) i j
      (by rw [inertia.idMat_len]; exact hi) hIdRow,
    inertia.getAt_idMat o i j hi hj,
    winDiag_entry o v i j hi hj,
    winDiag_entry o w i j hi hj]

/-- The head entry at the window carrier: the unit line's own
read, the level weights at the identity gram alone. -/
private theorem winEntry_head (o : Nat) (v w : BPair) (x y : Pos)
    (ho : 0 < o) :
    getAt [] (getAt [] (freecell.freePMat (winDiag o v)
        (winDiag o w) (inertia.idMat o) x y) 0) 0
      = [(BPair.unit + (BPair.ofNat 1).scale y)
          + ((BPair.ofNat 1).scale x).swap,
         BPair.unit, BPair.unit] := by
  rw [winEntry o v w x y 0 0 ho ho]
  rfl

/-- A loop entry at the window carrier: the loop values at their
occupied diagonal key. -/
private theorem winEntry_loop (o : Nat) (v w : BPair) (x y : Pos)
    (i : Nat) (h1 : 0 < i) (hio : i < o) :
    getAt [] (getAt [] (freecell.freePMat (winDiag o v)
        (winDiag o w) (inertia.idMat o) x y) i) i
      = [(v + (BPair.ofNat 1).scale y)
          + ((BPair.ofNat 1).scale x).swap,
         BPair.unit, w.swap] := by
  rw [winEntry o v w x y i i hio hio,
    if_pos (ground.eqBeqOf (rfl : i = i)),
    if_neg (show ¬ ((i == 0) = true) from fun h =>
      Nat.ne_of_gt h1 (ground.beqEqOf h)),
    if_pos (ground.eqBeqOf (rfl : i = i)),
    if_neg (show ¬ ((i == 0) = true) from fun h =>
      Nat.ne_of_gt h1 (ground.beqEqOf h)),
    if_pos (rfl : i = i)]
  rfl

/-- A coupling entry at the window carrier: the vacant off-diagonal
reads at the level weights, the one entry shape every carrier's
off-diagonal takes. -/
private theorem winEntry_coup (o : Nat) (v w : BPair) (x y : Pos)
    (i j : Nat) (hi : i < o) (hj : j < o) (hne : i ≠ j) :
    getAt [] (getAt [] (freecell.freePMat (winDiag o v)
        (winDiag o w) (inertia.idMat o) x y) i) j
      = [(BPair.unit + BPair.unit.scale y)
          + (BPair.unit.scale x).swap,
         BPair.unit, BPair.unit] := by
  rw [winEntry o v w x y i j hi hj,
    if_neg (show ¬ ((i == j) = true) from fun h =>
      hne (ground.beqEqOf h)),
    if_neg (show ¬ ((i == j) = true) from fun h =>
      hne (ground.beqEqOf h)),
    if_neg (show ¬ (j = i) from fun h => hne h.symm)]
  rfl

/-- The lower carrier's coupling entry, the level-one instance. -/
private theorem sLo_coup (o cut i j : Nat) (hi : i < o) (hj : j < o)
    (hne : i ≠ j) :
    getAt [] (getAt [] (sLo o cut) i) j
      = [(BPair.unit + BPair.unit.scale 1) + (BPair.unit.scale 2).swap,
         BPair.unit, BPair.unit] :=
  winEntry_coup o (BPair.ofNat cut) ⟨2, 1⟩ 2 1 i j hi hj hne

/-- The upper carrier's coupling entry at the stated level scale. -/
private theorem sHi_coup (o F i j : Nat) (hi : i < o) (hj : j < o)
    (hne : i ≠ j) :
    getAt [] (getAt [] (sHi o F) i) j
      = [(BPair.unit + BPair.unit.scale 1)
          + (BPair.unit.scale (ground.posOfSucc (2 * F))).swap,
         BPair.unit, BPair.unit] :=
  winEntry_coup o (BPair.ofNat (4 * F)) ⟨2, 1⟩
    (ground.posOfSucc (2 * F)) 1 i j hi hj hne

/-- The window carrier is symmetric at the stated order: the
diagonal reads at their own keys with every coupling the one
entry shape (`thm:pairpencil`'s symmetric site datum). -/
private theorem winSym (o : Nat) (v w : BPair) (x y : Pos) :
    split.pSymAt (freecell.freePMat (winDiag o v) (winDiag o w)
      (inertia.idMat o) x y) o := by
  refine split.pSymAt_of _ o (fun i j hi hj => ?_)
  by_cases h : i = j
  · rw [h]
    exact poly.oneValue_refl _
  · rw [winEntry_coup o v w x y i j hi hj h,
      winEntry_coup o v w x y j i hj hi (fun hh => h hh.symm)]
    exact poly.oneValue_refl _

/-- The lower carrier's symmetry read. -/
private theorem sLo_sym (o cut : Nat) : split.pSymAt (sLo o cut) o :=
  winSym o (BPair.ofNat cut) ⟨2, 1⟩ 2 1

/-- The upper carrier's symmetry read. -/
private theorem sHi_sym (o F : Nat) : split.pSymAt (sHi o F) o :=
  winSym o (BPair.ofNat (4 * F)) ⟨2, 1⟩ (ground.posOfSucc (2 * F)) 1

/-- The coupling entry's head at a stated level scale reads the
sum's unit, the one entry shape every carrier's off-diagonal
takes. -/
private theorem coupHead (s : Pos) :
    (ground.getAt BPair.unit
      [(BPair.unit + BPair.unit.scale 1) + (BPair.unit.scale s).swap,
       BPair.unit, BPair.unit] 0).oneValue BPair.unit :=
  BPair.oneValue_of_eqMem rfl

/-- The coupling entry at a stated level scale is unit-tailed, the
head's read with the vacant keys'. -/
private theorem coupUT (s : Pos) :
    poly.unitTail
      [(BPair.unit + BPair.unit.scale 1) + (BPair.unit.scale s).swap,
       BPair.unit, BPair.unit] :=
  ⟨BPair.oneValue_of_eqMem rfl, BPair.oneValue_refl _,
   BPair.oneValue_refl _, trivial⟩

/-- A trailing row's coupling at the head column is unit-tailed,
the deflation's row hypothesis at the lower carrier. -/
private theorem sLo_offR (o cut i : Nat) (h1 : 0 < i) (hio : i < o) :
    poly.unitTail (getAt [] (getAt [] (sLo o cut) i) 0) := by
  rw [sLo_coup o cut i 0 hio (Nat.lt_trans h1 hio) (Nat.ne_of_gt h1)]
  exact coupUT 2

/-- A trailing row's coupling at the head column is unit-tailed,
the deflation's row hypothesis at the upper carrier. -/
private theorem sHi_offR (o F i : Nat) (h1 : 0 < i) (hio : i < o) :
    poly.unitTail (getAt [] (getAt [] (sHi o F) i) 0) := by
  rw [sHi_coup o F i 0 hio (Nat.lt_trans h1 hio) (Nat.ne_of_gt h1)]
  exact coupUT (ground.posOfSucc (2 * F))

/-- The lower carrier's head entry, value `−1`: the level one over
the unit line. -/
private theorem sLo_head (o cut : Nat) (ho : 0 < o) :
    getAt [] (getAt [] (sLo o cut) 0) 0
      = [(⟨⟨4⟩, ⟨5⟩⟩ : BPair), BPair.unit, BPair.unit] := by
  rw [show sLo o cut = freecell.freePMat (winDiag o (BPair.ofNat cut))
      (winDiag o ⟨2, 1⟩) (inertia.idMat o) 2 1 from rfl,
    winEntry_head o (BPair.ofNat cut) ⟨2, 1⟩ 2 1 ho]
  rfl


/-! The committed range's cover data: the endpoint and sample-point
orders, the piece's distinct place, and the head entry's lower keep
at the committed range. -/

private theorem winFoot_le_top : winFoot ≤ winTop := by decide +kernel

private theorem winFoot_le_sample :
    winFoot ≤ (⟨BPair.unit, 1⟩ : ground.CPair) := by decide +kernel

private theorem winSample_le_top :
    (⟨BPair.unit, 1⟩ : ground.CPair) ≤ winTop := by decide +kernel

private theorem winPlace0 : ground.distinctList [0] := by decide +kernel

private theorem headKeepLower :
    stage.keepLower [(⟨⟨4⟩, ⟨5⟩⟩ : BPair), BPair.unit, BPair.unit]
      winFoot winTop ⟨2, 1⟩ ⟨2, 1⟩ := by decide +kernel
/-- The lower carrier's head keep at the committed range, the free
end's own read at every order and cutoff. -/
private theorem sLo_headKeep (o cut : Nat) (ho : 0 < o) :
    stage.keepLower (getAt [] (getAt [] (sLo o cut) 0) 0)
      winFoot winTop ⟨2, 1⟩ ⟨2, 1⟩ := by
  rw [sLo_head o cut ho]
  exact headKeepLower

/-- The lower carrier's shape at the stated order, the affine
list's own clearing degree (`cellcount.pShapeAt_levelPMat`). -/
private theorem sLo_shape (o cut : Nat) :
    cellcount.pShapeAt (sLo o cut) o 2 :=
  freecell.pShapeAt_freePMat _ _ _ 2 1 o
    (sqAt_winDiag o (BPair.ofNat cut)) (sqAt_winDiag o ⟨2, 1⟩)
    (inertia.sqAt_idMat o)

/-- The upper carrier's shape at the stated order. -/
private theorem sHi_shape (o F : Nat) :
    cellcount.pShapeAt (sHi o F) o 2 :=
  freecell.pShapeAt_freePMat _ _ _ (ground.posOfSucc (2 * F)) 1 o
    (sqAt_winDiag o (BPair.ofNat (4 * F))) (sqAt_winDiag o ⟨2, 1⟩)
    (inertia.sqAt_idMat o)

/-- The loop head's two-coefficient value `a − c z²` at its one-member
coefficients, subtraction-free. -/
private def qp (a c : Nat) : poly.Poly :=
  [⟨⟨a⟩, ⟨0⟩⟩, BPair.unit, ⟨⟨0⟩, ⟨c⟩⟩]

/-- The loop head's two-coefficient value's cube,
`a³ − 3a²c z² + 3ac² z⁴ − c³ z⁶`, `c`-cleared. -/
private def qp3 (a c : Nat) : poly.Poly :=
  [⟨⟨a * (a * a)⟩, ⟨0⟩⟩, BPair.unit, ⟨⟨0⟩, ⟨3 * (a * (a * c))⟩⟩,
   BPair.unit, ⟨⟨3 * (a * (c * c))⟩, ⟨0⟩⟩, BPair.unit, ⟨⟨0⟩, ⟨c * (c * c)⟩⟩]


/-- The composite Horner read at the free end: the point's vacant
value leaves the constant coefficient alone. -/
private theorem evalC_foot : ∀ p : poly.Poly,
    (stage.evalC p winFoot).oneValue
      (stage.ofB (ground.getAt BPair.unit p 0))
  | [] => CPair.oneValue_refl _
  | c :: _ =>
    CPair.oneValue_trans
      (CPair.add_congr (CPair.oneValue_refl (stage.ofB c))
        (CPair.num_oneValue (BPair.unit_mul _) (Pos.one * _)))
      (CPair.opUnit_oneValue (stage.ofB c) Pos.one (Pos.one * _))

/-- A composite factor at the multiplicative unit drops. -/
private theorem cmul_one {x y : CPair}
    (hy : y.oneValue (stage.ofB (BPair.ofPos Pos.one))) :
    (x * y).oneValue x :=
  CPair.oneValue_trans (CPair.mul_congr (CPair.oneValue_refl x) hy)
    (CPair.oneValue_trans
      (CPair.num_oneValue (BPair.mul_one_read _) (_ * Pos.one))
      (CPair.den_congr (ground.mul_one _)))

/-- The cleared evaluation at the free end reads the entry's head
coefficient. -/
private theorem evalHead (p : poly.Poly) :
    (poly.evalClear p BPair.unit 1 2).oneValue
      (ground.getAt BPair.unit p 0) :=
  BPair.oneValue_trans (poly.evalClear_unit p Pos.one 2)
    (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_comm _ _))
      (BPair.mul_one_read _))

/-- A one-member pair at its occupancy read. -/
private theorem bofNat (n : Nat) : (⟨⟨n⟩, ⟨0⟩⟩ : BPair) = BPair.ofNat n := by
  cases n with | zero => rfl | succ k => rfl

/-- A one-member pair's memberwise swap at its occupancy read. -/
private theorem bofNatSwap (n : Nat) :
    (⟨⟨0⟩, ⟨n⟩⟩ : BPair) = (BPair.ofNat n).swap := by
  cases n with | zero => rfl | succ k => rfl

/-! The balance carrier's unit and occupancy rearrangements, the
cube's coefficient reads. -/

private theorem ofNat_mul3 (x y z : Nat) :
    (BPair.ofNat (x * (y * z))).oneValue
      (BPair.ofNat x * (BPair.ofNat y * BPair.ofNat z)) :=
  BPair.oneValue_trans (BPair.ofNat_mul x (y * z))
    (BPair.mul_congr (BPair.oneValue_refl _) (BPair.ofNat_mul y z))

private theorem ofNat_three (n : Nat) :
    (BPair.ofNat (3 * n)).oneValue
      (BPair.ofNat n + BPair.ofNat n + BPair.ofNat n) := by
  rw [ground.threeMul n]
  exact BPair.oneValue_trans (BPair.ofNat_add (n + n) n)
    (BPair.add_congr (BPair.ofNat_add n n)
      (BPair.oneValue_refl (BPair.ofNat n)))

private theorem e2eq (A C : BPair) :
    A * (A * C + C * A) + C * (A * A)
      = A * (A * C) + A * (A * C) + A * (A * C) := by
  rw [BPair.left_distrib A (A * C) (C * A), BPair.mul_comm C A,
    BPair.mul_comm C (A * A), BPair.mul_assoc A A C]

private theorem e4eq (A C : BPair) :
    A * (C * C) + C * (A * C + C * A)
      = A * (C * C) + A * (C * C) + A * (C * C) := by
  rw [BPair.left_distrib C (A * C) (C * A), BPair.mul_comm C A,
    BPair.mul_comm C (A * C), BPair.mul_assoc A C C, ← BPair.add_assoc]

private theorem tripSum (A S : BPair) :
    A * (A * S.swap) + A * (A * S.swap) + A * (A * S.swap)
      = (A * (A * S) + A * (A * S) + A * (A * S)).swap := by
  rw [BPair.mul_swap A S, BPair.mul_swap A (A * S),
    BPair.swap_add (A * (A * S)) (A * (A * S)),
    BPair.swap_add (A * (A * S) + A * (A * S)) (A * (A * S))]

private theorem tripSqSwap (A S : BPair) :
    A * (S.swap * S.swap) + A * (S.swap * S.swap) + A * (S.swap * S.swap)
      = A * (S * S) + A * (S * S) + A * (S * S) := by
  rw [BPair.swap_sq S]

private theorem cubeSwap (S : BPair) :
    S.swap * (S.swap * S.swap) = (S * (S * S)).swap := by
  rw [BPair.swap_sq S, BPair.swap_mul S (S * S)]

/-- The loop head's two-coefficient value's cube reads the displayed
sextic at every parameter pair, the product's entries read against the
cleared coefficients. -/
private theorem cube_qp (a c : Nat) :
    poly.oneValue (poly.mul (qp a c) (poly.mul (qp a c) (qp a c))) (qp3 a c) := by
  have hu : BPair.oneValue BPair.unit BPair.unit := BPair.oneValue_refl BPair.unit
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · rw [bofNat a, bofNat (a * (a * a))]
    exact BPair.oneValue_trans
      (BPair.oneValue_trans (BPair.add_unit _)
        (BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat a))
          (BPair.add_unit (BPair.ofNat a * BPair.ofNat a))))
      (BPair.oneValue_symm (ofNat_mul3 a a a))
  · exact BPair.add_units
      (elim.oneValue_mul_unit _ _ (BPair.add_units (elim.oneValue_mul_unit _ _ hu) (BPair.add_units (elim.oneValue_unit_mul hu) hu)))
      (BPair.add_units (elim.oneValue_unit_mul hu) hu)
  · rw [bofNat a, bofNatSwap c, bofNatSwap (3 * (a * (a * c)))]
    have hA := BPair.oneValue_refl (BPair.ofNat a)
    have hC := BPair.oneValue_refl (BPair.ofNat c).swap
    have h1 : ((BPair.ofNat a * (BPair.ofNat c).swap
          + (BPair.unit * BPair.unit
            + ((BPair.ofNat c).swap * BPair.ofNat a + BPair.unit))).oneValue
        (BPair.ofNat a * (BPair.ofNat c).swap
          + (BPair.ofNat c).swap * BPair.ofNat a)) :=
      BPair.add_congr (BPair.oneValue_refl _)
        (BPair.oneValue_trans
          (BPair.add_congr (BPair.unit_mul BPair.unit)
            (BPair.add_unit ((BPair.ofNat c).swap * BPair.ofNat a)))
          (BPair.unit_add ((BPair.ofNat c).swap * BPair.ofNat a)))
    have h3 : (((BPair.unit * (BPair.ofNat a * BPair.unit
              + (BPair.unit * BPair.ofNat a + BPair.unit)))
          + ((BPair.ofNat c).swap * (BPair.ofNat a * BPair.ofNat a + BPair.unit)
            + BPair.unit)).oneValue
        ((BPair.ofNat c).swap * (BPair.ofNat a * BPair.ofNat a))) :=
      BPair.oneValue_trans
        (BPair.add_congr (elim.oneValue_unit_mul hu)
          (BPair.oneValue_trans (BPair.add_unit _)
            (BPair.mul_congr hC
              (BPair.add_unit (BPair.ofNat a * BPair.ofNat a)))))
        (BPair.unit_add _)
    have hQ : ((BPair.ofNat (3 * (a * (a * c)))).oneValue
        (BPair.ofNat a * (BPair.ofNat a * BPair.ofNat c)
          + BPair.ofNat a * (BPair.ofNat a * BPair.ofNat c)
          + BPair.ofNat a * (BPair.ofNat a * BPair.ofNat c))) :=
      BPair.oneValue_trans (ofNat_three (a * (a * c)))
        (BPair.add_congr (BPair.add_congr (ofNat_mul3 a a c) (ofNat_mul3 a a c))
          (ofNat_mul3 a a c))
    exact BPair.oneValue_trans
      (BPair.oneValue_trans (BPair.add_congr (BPair.mul_congr hA h1) h3)
        (BPair.oneValue_of_eq (e2eq (BPair.ofNat a) (BPair.ofNat c).swap)))
      (BPair.oneValue_symm
        (BPair.oneValue_trans (swap_congr hQ)
          (BPair.oneValue_of_eq
            (tripSum (BPair.ofNat a) (BPair.ofNat c)).symm)))
  · exact BPair.add_units
      (elim.oneValue_mul_unit _ _ (BPair.add_units (elim.oneValue_unit_mul hu) (elim.oneValue_mul_unit _ _ hu)))
      (BPair.add_units (elim.oneValue_unit_mul hu)
        (elim.oneValue_mul_unit _ _ (BPair.add_units (elim.oneValue_mul_unit _ _ hu) (BPair.add_units (elim.oneValue_unit_mul hu) hu))))
  · rw [bofNat a, bofNatSwap c, bofNat (3 * (a * (c * c)))]
    have hC := BPair.oneValue_refl (BPair.ofNat c).swap
    have h1 : ((BPair.ofNat a * (BPair.ofNat c).swap
          + (BPair.unit * BPair.unit
            + ((BPair.ofNat c).swap * BPair.ofNat a + BPair.unit))).oneValue
        (BPair.ofNat a * (BPair.ofNat c).swap
          + (BPair.ofNat c).swap * BPair.ofNat a)) :=
      BPair.add_congr (BPair.oneValue_refl _)
        (BPair.oneValue_trans
          (BPair.add_congr (BPair.unit_mul BPair.unit)
            (BPair.add_unit ((BPair.ofNat c).swap * BPair.ofNat a)))
          (BPair.unit_add ((BPair.ofNat c).swap * BPair.ofNat a)))
    have h3 : (((BPair.unit * (BPair.unit * (BPair.ofNat c).swap
              + (BPair.ofNat c).swap * BPair.unit))
          + (BPair.ofNat c).swap * (BPair.ofNat a * (BPair.ofNat c).swap
              + (BPair.unit * BPair.unit
                + ((BPair.ofNat c).swap * BPair.ofNat a
                  + BPair.unit)))).oneValue
        ((BPair.ofNat c).swap * (BPair.ofNat a * (BPair.ofNat c).swap
          + (BPair.ofNat c).swap * BPair.ofNat a))) :=
      BPair.oneValue_trans
        (BPair.add_congr (elim.oneValue_unit_mul hu) (BPair.mul_congr hC h1))
        (BPair.unit_add _)
    have hQ : ((BPair.ofNat (3 * (a * (c * c)))).oneValue
        (BPair.ofNat a * (BPair.ofNat c * BPair.ofNat c)
          + BPair.ofNat a * (BPair.ofNat c * BPair.ofNat c)
          + BPair.ofNat a * (BPair.ofNat c * BPair.ofNat c))) :=
      BPair.oneValue_trans (ofNat_three (a * (c * c)))
        (BPair.add_congr (BPair.add_congr (ofNat_mul3 a c c) (ofNat_mul3 a c c))
          (ofNat_mul3 a c c))
    exact BPair.oneValue_trans
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _) h3)
        (BPair.oneValue_of_eq (e4eq (BPair.ofNat a) (BPair.ofNat c).swap)))
      (BPair.oneValue_symm
        (BPair.oneValue_trans hQ
          (BPair.oneValue_of_eq
            (tripSqSwap (BPair.ofNat a) (BPair.ofNat c)).symm)))
  · exact BPair.add_units (elim.oneValue_unit_mul hu)
      (elim.oneValue_mul_unit _ _ (BPair.add_units (elim.oneValue_unit_mul hu) (elim.oneValue_mul_unit _ _ hu)))
  · rw [bofNatSwap c, bofNatSwap (c * (c * c))]
    exact BPair.oneValue_trans
      (BPair.oneValue_of_eq (cubeSwap (BPair.ofNat c)))
      (BPair.oneValue_symm (swap_congr (ofNat_mul3 c c c)))

/-! The one-member pairs' magnitudes and the cube's coefficient
arithmetic at the counts. -/

private theorem unitLeMk : ∀ n : Nat, BPair.unit ≤ (⟨⟨n⟩, ⟨0⟩⟩ : BPair)
  | 0 => Or.inl rfl
  | k + 1 => Or.inr ⟨⟨k⟩, congrArg Pos.mk (by
      show 0 + 0 + 1 + k + 1 = k + 1 + 0 + 1
      rw [Nat.add_comm 1 k])⟩

private theorem magPos (n : Nat) :
    windowsep.mag (⟨⟨n⟩, ⟨0⟩⟩ : BPair) = (⟨⟨n⟩, ⟨0⟩⟩ : BPair) :=
  windowsep.mag_unitLe (unitLeMk n)

private theorem magNeg (n : Nat) :
    windowsep.mag (⟨⟨0⟩, ⟨n⟩⟩ : BPair) = (⟨⟨n⟩, ⟨0⟩⟩ : BPair) :=
  (windowsep.mag_swap (⟨⟨n⟩, ⟨0⟩⟩ : BPair)).trans (magPos n)

private theorem mulSucc (n k : Nat) : k * n + k = (n + 1) * k := by
  rw [ground.mulAddR n 1 k, Nat.one_mul k, Nat.mul_comm k n]

private theorem cAA (a c : Nat) : c * (a * a) = a * (a * c) := by
  rw [Nat.mul_comm c (a * a), ground.mulAssoc a a c]

private theorem cAC (a c : Nat) : c * (a * c) = a * (c * c) := by
  rw [Nat.mul_comm c (a * c), ground.mulAssoc a c c]

private theorem cCA (a c : Nat) : c * (c * a) = a * (c * c) := by
  rw [Nat.mul_comm c a, cAC a c]

private theorem sqExp (a c : Nat) :
    (a + c) * (a + c) = a * a + a * c + (c * a + c * c) := by
  rw [ground.mulAddR a c (a + c), Nat.left_distrib a a c,
    Nat.left_distrib c a c]

private theorem hW (a c : Nat) :
    c * ((a + c) * (a + c))
      = a * (a * c) + a * (c * c) + (a * (c * c) + c * (c * c)) := by
  rw [sqExp a c, Nat.left_distrib c (a * a + a * c) (c * a + c * c),
    Nat.left_distrib c (a * a) (a * c),
    Nat.left_distrib c (c * a) (c * c),
    cAA a c, cAC a c, cCA a c]

private theorem shuffleAdd (A B C : Nat) :
    A + 1 + (B + B + 3 + (C + 5) + 1) + 1 = A + B + (B + C) + 11 := by
  rw [Nat.add_right_comm (B + B) 3 (C + 5), ← Nat.add_assoc (B + B) C 5,
    Nat.add_right_comm A 1 (B + B + C + 5 + 3 + 1),
    ← Nat.add_assoc A (B + B + C + 5 + 3) 1,
    ← Nat.add_assoc A (B + B + C + 5) 3,
    ← Nat.add_assoc A (B + B + C) 5,
    Nat.add_assoc B B C, Nat.add_assoc A B (B + C)]

private theorem tfEq (a c : Nat) :
    3 * (a * (a * c)) * 1 + 3 * (a * (a * c)) + 1
      + (3 * (a * (c * c)) * 3 + 3 * (a * (c * c)) + 3
          + (c * (c * c) * 5 + c * (c * c) + 5) + 1) + 1
      = 6 * (c * ((a + c) * (a + c))) + 11 := by
  have e1 : 3 * (a * (a * c)) * 1 + 3 * (a * (a * c)) = 6 * (a * (a * c)) :=
    (mulSucc 1 (3 * (a * (a * c)))).trans (ground.mulAssoc 2 3 (a * (a * c))).symm
  have e2 : 3 * (a * (c * c)) * 3 + 3 * (a * (c * c)) = 12 * (a * (c * c)) :=
    (mulSucc 3 (3 * (a * (c * c)))).trans (ground.mulAssoc 4 3 (a * (c * c))).symm
  have e3 : c * (c * c) * 5 + c * (c * c) = 6 * (c * (c * c)) :=
    mulSucc 5 (c * (c * c))
  have e12 : 12 * (a * (c * c)) = 6 * (a * (c * c)) + 6 * (a * (c * c)) :=
    ground.mulAddR 6 6 (a * (c * c))
  rw [e1, e2, e3, e12,
    shuffleAdd (6 * (a * (a * c))) (6 * (a * (c * c))) (6 * (c * (c * c))),
    hW a c, Nat.left_distrib 6 (a * (a * c) + a * (c * c))
      (a * (c * c) + c * (c * c)),
    Nat.left_distrib 6 (a * (a * c)) (a * (c * c)),
    Nat.left_distrib 6 (a * (c * c)) (c * (c * c))]

/-- The cube's derivative reads six coefficients at an occupied
loop content, the top coefficient off the sum's unit. -/
private theorem hlen6 (a m : Nat) :
    (poly.vnorm (poly.deriv (qp3 a (m + 1)))).length = 6 := by
  have hoff : ¬ ((⟨⟨0⟩, ⟨(m+1) * ((m+1) * (m+1))⟩⟩ : BPair).scale 6).oneValue
      BPair.unit := by
    intro h
    have h2 : (0 * 5 + 0 + 5) + 0 + 1 = 0 + ((m+1) * ((m+1) * (m+1)) * 5
        + (m+1) * ((m+1) * (m+1)) + 5) + 1 := ground.posMkInj h
    exact Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj
      (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj h2))))))
  have h1 : poly.vnorm [((⟨⟨0⟩, ⟨(m+1) * ((m+1) * (m+1))⟩⟩ : BPair).scale 6)]
      = [((⟨⟨0⟩, ⟨(m+1) * ((m+1) * (m+1))⟩⟩ : BPair).scale 6).norm] :=
    poly.vnorm_cons_off _ [] rfl hoff
  have h2 := poly.vnorm_cons_occ (BPair.unit.scale 5) _ _ _ h1
  have h3 := poly.vnorm_cons_occ
    ((⟨⟨3 * (a * ((m+1) * (m+1)))⟩, ⟨0⟩⟩ : BPair).scale 4) _ _ _ h2
  have h4 := poly.vnorm_cons_occ (BPair.unit.scale 3) _ _ _ h3
  have h5 := poly.vnorm_cons_occ
    ((⟨⟨0⟩, ⟨3 * (a * (a * (m+1)))⟩⟩ : BPair).scale 2) _ _ _ h4
  have h6 := poly.vnorm_cons_occ (BPair.unit.scale 1) _ _ _ h5
  have h7 : poly.vnorm (poly.deriv (qp3 a (m+1)))
      = (BPair.unit.scale 1).norm
        :: ((⟨⟨0⟩, ⟨3 * (a * (a * (m+1)))⟩⟩ : BPair).scale 2).norm
        :: (BPair.unit.scale 3).norm
        :: ((⟨⟨3 * (a * ((m+1) * (m+1)))⟩, ⟨0⟩⟩ : BPair).scale 4).norm
        :: (BPair.unit.scale 5).norm
        :: [((⟨⟨0⟩, ⟨(m+1) * ((m+1) * (m+1))⟩⟩ : BPair).scale 6).norm] := h6
  rw [h7]
  rfl

/-- The upper side's priced read at the cube: the derivative's
magnitude fold `6c(a+c)²` against the constant `a³` at the committed
segment, the hypothesis the comparison itself. -/
private theorem keepUpper_qp3 (a c : Nat) (hc : 1 ≤ c)
    (ha : 6 * (c * ((a + c) * (a + c))) < a * (a * a)) :
    stage.keepUpper (qp3 a c) winFoot winTop ⟨2, 1⟩ ⟨2, 1⟩ := by
  cases c with
  | zero => exact absurd hc (Nat.not_lt_zero 0)
  | succ m =>
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  have hm1 : windowsep.mag ((⟨⟨0⟩, ⟨3 * (a * (a * (m+1)))⟩⟩ : BPair).scale 2)
      = (⟨⟨3 * (a * (a * (m+1)))⟩, ⟨0⟩⟩ : BPair).scale 2 := by
    rw [windowsep.mag_scale, magNeg]
  have hm3 : windowsep.mag
      ((⟨⟨3 * (a * ((m+1) * (m+1)))⟩, ⟨0⟩⟩ : BPair).scale 4)
      = (⟨⟨3 * (a * ((m+1) * (m+1)))⟩, ⟨0⟩⟩ : BPair).scale 4 := by
    rw [windowsep.mag_scale, magPos]
  have hm5 : windowsep.mag
      ((⟨⟨0⟩, ⟨(m+1) * ((m+1) * (m+1))⟩⟩ : BPair).scale 6)
      = (⟨⟨(m+1) * ((m+1) * (m+1))⟩, ⟨0⟩⟩ : BPair).scale 6 := by
    rw [windowsep.mag_scale, magNeg]
  have hread := windowsep.magFold_read (poly.deriv (qp3 a (m+1)))
    (⟨2, 1⟩ : BPair) ⟨2, 1⟩
  rw [hlen6 a m] at hread
  have hg0 : (ground.getAt BPair.unit
      (poly.vnorm (poly.deriv (qp3 a (m+1)))) 0).oneValue
      (BPair.unit.scale 1) :=
    poly.oneValue_getAt 0 (poly.vnorm_ov _)
  have hg1 : (ground.getAt BPair.unit
      (poly.vnorm (poly.deriv (qp3 a (m+1)))) 1).oneValue
      ((⟨⟨0⟩, ⟨3 * (a * (a * (m+1)))⟩⟩ : BPair).scale 2) :=
    poly.oneValue_getAt 1 (poly.vnorm_ov _)
  have hg2 : (ground.getAt BPair.unit
      (poly.vnorm (poly.deriv (qp3 a (m+1)))) 2).oneValue
      (BPair.unit.scale 3) :=
    poly.oneValue_getAt 2 (poly.vnorm_ov _)
  have hg3 : (ground.getAt BPair.unit
      (poly.vnorm (poly.deriv (qp3 a (m+1)))) 3).oneValue
      ((⟨⟨3 * (a * ((m+1) * (m+1)))⟩, ⟨0⟩⟩ : BPair).scale 4) :=
    poly.oneValue_getAt 3 (poly.vnorm_ov _)
  have hg4 : (ground.getAt BPair.unit
      (poly.vnorm (poly.deriv (qp3 a (m+1)))) 4).oneValue
      (BPair.unit.scale 5) :=
    poly.oneValue_getAt 4 (poly.vnorm_ov _)
  have hg5 : (ground.getAt BPair.unit
      (poly.vnorm (poly.deriv (qp3 a (m+1)))) 5).oneValue
      ((⟨⟨0⟩, ⟨(m+1) * ((m+1) * (m+1))⟩⟩ : BPair).scale 6) :=
    poly.oneValue_getAt 5 (poly.vnorm_ov _)
  have hM : (windowsep.magFold (poly.deriv (qp3 a (m+1)))
      (⟨2, 1⟩ : BPair) ⟨2, 1⟩).oneValue
      ((⟨⟨3 * (a * (a * (m+1)))⟩, ⟨0⟩⟩ : BPair).scale 2
        + ((⟨⟨3 * (a * ((m+1) * (m+1)))⟩, ⟨0⟩⟩ : BPair).scale 4
          + (⟨⟨(m+1) * ((m+1) * (m+1))⟩, ⟨0⟩⟩ : BPair).scale 6)) := by
    refine BPair.oneValue_trans hread ?_
    show (windowsep.mag (ground.getAt BPair.unit
            (poly.vnorm (poly.deriv (qp3 a (m+1)))) 0)
          * ground.bpow (⟨2, 1⟩ : BPair) 0 * ground.bpow (⟨2, 1⟩ : BPair) 5
        + (windowsep.mag (ground.getAt BPair.unit
              (poly.vnorm (poly.deriv (qp3 a (m+1)))) 1)
            * ground.bpow (⟨2, 1⟩ : BPair) 1 * ground.bpow (⟨2, 1⟩ : BPair) 4
        + (windowsep.mag (ground.getAt BPair.unit
              (poly.vnorm (poly.deriv (qp3 a (m+1)))) 2)
            * ground.bpow (⟨2, 1⟩ : BPair) 2 * ground.bpow (⟨2, 1⟩ : BPair) 3
        + (windowsep.mag (ground.getAt BPair.unit
              (poly.vnorm (poly.deriv (qp3 a (m+1)))) 3)
            * ground.bpow (⟨2, 1⟩ : BPair) 3 * ground.bpow (⟨2, 1⟩ : BPair) 2
        + (windowsep.mag (ground.getAt BPair.unit
              (poly.vnorm (poly.deriv (qp3 a (m+1)))) 4)
            * ground.bpow (⟨2, 1⟩ : BPair) 4 * ground.bpow (⟨2, 1⟩ : BPair) 1
        + (windowsep.mag (ground.getAt BPair.unit
              (poly.vnorm (poly.deriv (qp3 a (m+1)))) 5)
            * ground.bpow (⟨2, 1⟩ : BPair) 5 * ground.bpow (⟨2, 1⟩ : BPair) 0
          + BPair.unit)))))).oneValue
      ((⟨⟨3 * (a * (a * (m+1)))⟩, ⟨0⟩⟩ : BPair).scale 2
        + ((⟨⟨3 * (a * ((m+1) * (m+1)))⟩, ⟨0⟩⟩ : BPair).scale 4
          + (⟨⟨(m+1) * ((m+1) * (m+1))⟩, ⟨0⟩⟩ : BPair).scale 6))
    have h0 : (windowsep.mag (ground.getAt BPair.unit
          (poly.vnorm (poly.deriv (qp3 a (m+1)))) 0)
        * ground.bpow (⟨2, 1⟩ : BPair) 0
        * ground.bpow (⟨2, 1⟩ : BPair) 5).oneValue BPair.unit := by
      refine BPair.oneValue_trans (BPair.mul_congr (BPair.mul_congr
        (BPair.oneValue_trans (windowsep.mag_congr hg0)
          (show (windowsep.mag (BPair.unit.scale 1)).oneValue BPair.unit by
            decide +kernel))
        (BPair.oneValue_refl _)) (BPair.oneValue_refl _)) ?_
      decide +kernel
    have h1 : (windowsep.mag (ground.getAt BPair.unit
          (poly.vnorm (poly.deriv (qp3 a (m+1)))) 1)
        * ground.bpow (⟨2, 1⟩ : BPair) 1
        * ground.bpow (⟨2, 1⟩ : BPair) 4).oneValue
        ((⟨⟨3 * (a * (a * (m+1)))⟩, ⟨0⟩⟩ : BPair).scale 2) := by
      refine BPair.oneValue_trans (BPair.mul_congr (BPair.mul_congr
        (BPair.oneValue_trans (windowsep.mag_congr hg1)
          (BPair.oneValue_of_eq hm1))
        (BPair.oneValue_refl _)) (BPair.oneValue_refl _)) ?_
      exact BPair.oneValue_trans
        (BPair.mul_one_read ((⟨⟨3 * (a * (a * (m+1)))⟩, ⟨0⟩⟩ : BPair).scale 2
          * ground.bpow (⟨2, 1⟩ : BPair) 1))
        (BPair.mul_one_read ((⟨⟨3 * (a * (a * (m+1)))⟩, ⟨0⟩⟩ : BPair).scale 2))
    have h2 : (windowsep.mag (ground.getAt BPair.unit
          (poly.vnorm (poly.deriv (qp3 a (m+1)))) 2)
        * ground.bpow (⟨2, 1⟩ : BPair) 2
        * ground.bpow (⟨2, 1⟩ : BPair) 3).oneValue BPair.unit := by
      refine BPair.oneValue_trans (BPair.mul_congr (BPair.mul_congr
        (BPair.oneValue_trans (windowsep.mag_congr hg2)
          (show (windowsep.mag (BPair.unit.scale 3)).oneValue BPair.unit by
            decide +kernel))
        (BPair.oneValue_refl _)) (BPair.oneValue_refl _)) ?_
      decide +kernel
    have h3 : (windowsep.mag (ground.getAt BPair.unit
          (poly.vnorm (poly.deriv (qp3 a (m+1)))) 3)
        * ground.bpow (⟨2, 1⟩ : BPair) 3
        * ground.bpow (⟨2, 1⟩ : BPair) 2).oneValue
        ((⟨⟨3 * (a * ((m+1) * (m+1)))⟩, ⟨0⟩⟩ : BPair).scale 4) := by
      refine BPair.oneValue_trans (BPair.mul_congr (BPair.mul_congr
        (BPair.oneValue_trans (windowsep.mag_congr hg3)
          (BPair.oneValue_of_eq hm3))
        (BPair.oneValue_refl _)) (BPair.oneValue_refl _)) ?_
      exact BPair.oneValue_trans
        (BPair.mul_one_read
          ((⟨⟨3 * (a * ((m+1) * (m+1)))⟩, ⟨0⟩⟩ : BPair).scale 4
            * ground.bpow (⟨2, 1⟩ : BPair) 3))
        (BPair.mul_one_read
          ((⟨⟨3 * (a * ((m+1) * (m+1)))⟩, ⟨0⟩⟩ : BPair).scale 4))
    have h4 : (windowsep.mag (ground.getAt BPair.unit
          (poly.vnorm (poly.deriv (qp3 a (m+1)))) 4)
        * ground.bpow (⟨2, 1⟩ : BPair) 4
        * ground.bpow (⟨2, 1⟩ : BPair) 1).oneValue BPair.unit := by
      refine BPair.oneValue_trans (BPair.mul_congr (BPair.mul_congr
        (BPair.oneValue_trans (windowsep.mag_congr hg4)
          (show (windowsep.mag (BPair.unit.scale 5)).oneValue BPair.unit by
            decide +kernel))
        (BPair.oneValue_refl _)) (BPair.oneValue_refl _)) ?_
      decide +kernel
    have h5 : (windowsep.mag (ground.getAt BPair.unit
          (poly.vnorm (poly.deriv (qp3 a (m+1)))) 5)
        * ground.bpow (⟨2, 1⟩ : BPair) 5
        * ground.bpow (⟨2, 1⟩ : BPair) 0).oneValue
        ((⟨⟨(m+1) * ((m+1) * (m+1))⟩, ⟨0⟩⟩ : BPair).scale 6) := by
      refine BPair.oneValue_trans (BPair.mul_congr (BPair.mul_congr
        (BPair.oneValue_trans (windowsep.mag_congr hg5)
          (BPair.oneValue_of_eq hm5))
        (BPair.oneValue_refl _)) (BPair.oneValue_refl _)) ?_
      exact BPair.oneValue_trans
        (BPair.mul_one_read
          ((⟨⟨(m+1) * ((m+1) * (m+1))⟩, ⟨0⟩⟩ : BPair).scale 6
            * ground.bpow (⟨2, 1⟩ : BPair) 5))
        (BPair.mul_one_read
          ((⟨⟨(m+1) * ((m+1) * (m+1))⟩, ⟨0⟩⟩ : BPair).scale 6))
    refine BPair.oneValue_trans
      (BPair.add_congr h0 (BPair.add_congr h1 (BPair.add_congr h2
        (BPair.add_congr h3 (BPair.add_congr h4 (BPair.add_congr h5
          (BPair.oneValue_refl BPair.unit))))))) ?_
    exact BPair.oneValue_trans (BPair.unit_add _)
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.oneValue_trans (BPair.unit_add _)
          (BPair.add_congr (BPair.oneValue_refl _)
            (BPair.oneValue_trans (BPair.unit_add _)
              (BPair.add_unit _)))))
  have hC : (winTop + CPair.swap winFoot).oneValue
      (stage.ofB (BPair.ofPos Pos.one)) := by decide +kernel
  have hbp : (stage.ofB (ground.bpow (⟨2, 1⟩ : BPair)
      ((poly.vnorm (poly.deriv (qp3 a (m+1)))).length - 1))).oneValue
      (stage.ofB (BPair.ofPos Pos.one)) :=
    CPair.num_oneValue (ground.bpow_one _) Pos.one
  have hx : (stage.ofB ((⟨⟨3 * (a * (a * (m+1)))⟩, ⟨0⟩⟩ : BPair).scale 2
        + ((⟨⟨3 * (a * ((m+1) * (m+1)))⟩, ⟨0⟩⟩ : BPair).scale 4
          + (⟨⟨(m+1) * ((m+1) * (m+1))⟩, ⟨0⟩⟩ : BPair).scale 6))).oneValue
      (stage.ofB (windowsep.magFold (poly.deriv (qp3 a (m+1)))
          (⟨2, 1⟩ : BPair) ⟨2, 1⟩)
        * (winTop + CPair.swap winFoot)) :=
    CPair.oneValue_symm (CPair.oneValue_trans (cmul_one hC)
      (CPair.num_oneValue hM Pos.one))
  have hy : (stage.ofB (⟨⟨a * (a * a)⟩, ⟨0⟩⟩ : BPair)).oneValue
      (stage.evalC (qp3 a (m+1)) winFoot
        * stage.ofB (ground.bpow (⟨2, 1⟩ : BPair)
          ((poly.vnorm (poly.deriv (qp3 a (m+1)))).length - 1))) :=
    CPair.oneValue_symm (CPair.oneValue_trans (cmul_one hbp)
      (evalC_foot (qp3 a (m+1))))
  refine CPair.lt_congr hx hy (BPair.scale_lt Pos.one ?_)
  refine Exists.elim (Nat.le.dest ha) (fun j hj => ?_)
  refine ⟨⟨j⟩, congrArg Pos.mk ?_⟩
  show 3 * (a * (a * (m+1))) * 1 + 3 * (a * (a * (m+1))) + 1
      + (3 * (a * ((m+1) * (m+1))) * 3 + 3 * (a * ((m+1) * (m+1))) + 3
          + ((m+1) * ((m+1) * (m+1)) * 5 + (m+1) * ((m+1) * (m+1)) + 5) + 1)
      + 1 + 1 + j + 1
    = a * (a * a) + 11 + 1
  rw [tfEq a (m + 1), ← hj]
  show 6 * ((m+1) * ((a + (m+1)) * (a + (m+1)))) + 11 + 1 + j + 1
      = 6 * ((m+1) * ((a + (m+1)) * (a + (m+1)))) + 1 + j + 11 + 1
  rw [Nat.add_right_comm (6 * ((m+1) * ((a + (m+1)) * (a + (m+1)))) + 11) 1 j,
    Nat.add_right_comm (6 * ((m+1) * ((a + (m+1)) * (a + (m+1))))) 11 j,
    Nat.add_right_comm (6 * ((m+1) * ((a + (m+1)) * (a + (m+1))))) 1 j]

/-- The upper side's priced read at the loop head's
two-coefficient value: the derivative's magnitude fold `2c` against the constant
`a` at the committed segment. -/
private theorem keepUpper_qp (a c : Nat) (hc : 1 ≤ c) (ha : 2 * c + 1 ≤ a) :
    stage.keepUpper (qp a c) winFoot winTop ⟨2, 1⟩ ⟨2, 1⟩ := by
  cases c with
  | zero => exact absurd hc (Nat.not_lt_zero 0)
  | succ m =>
    refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, ?_⟩
    have hoff : ¬ ((⟨⟨0⟩, ⟨m+1⟩⟩ : BPair).scale 2).oneValue BPair.unit := by
      intro h
      exact Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (ground.posMkInj h)))
    have hv1 : poly.vnorm [((⟨⟨0⟩, ⟨m+1⟩⟩ : BPair).scale 2)]
        = [((⟨⟨0⟩, ⟨m+1⟩⟩ : BPair).scale 2).norm] :=
      poly.vnorm_cons_off _ [] rfl hoff
    have hv2 : poly.vnorm (poly.deriv (qp a (m+1)))
        = (BPair.unit.scale 1).norm
          :: [((⟨⟨0⟩, ⟨m+1⟩⟩ : BPair).scale 2).norm] :=
      poly.vnorm_cons_occ (BPair.unit.scale 1)
        ((⟨⟨0⟩, ⟨m+1⟩⟩ : BPair).scale 2).norm
        [((⟨⟨0⟩, ⟨m+1⟩⟩ : BPair).scale 2)] [] hv1
    have hlen : (poly.vnorm (poly.deriv (qp a (m+1)))).length = 2 := by
      rw [hv2]
      rfl
    have hread := windowsep.magFold_read (poly.deriv (qp a (m+1)))
      (⟨2, 1⟩ : BPair) ⟨2, 1⟩
    rw [hlen] at hread
    have hg0 : (ground.getAt BPair.unit
        (poly.vnorm (poly.deriv (qp a (m+1)))) 0).oneValue
        (BPair.unit.scale 1) :=
      poly.oneValue_getAt 0 (poly.vnorm_ov _)
    have hg1 : (ground.getAt BPair.unit
        (poly.vnorm (poly.deriv (qp a (m+1)))) 1).oneValue
        ((⟨⟨0⟩, ⟨m+1⟩⟩ : BPair).scale 2) :=
      poly.oneValue_getAt 1 (poly.vnorm_ov _)
    have hlt2 : ((⟨⟨0⟩, ⟨m+1⟩⟩ : BPair).scale 2)
        < ((⟨⟨0⟩, ⟨m+1⟩⟩ : BPair).scale 2).swap := by
      have h1 : Pos.one < (⟨m+1⟩ : Pos) := by
        have h0 := ground.posLtSelfAdd Pos.one ⟨m⟩
        rw [ground.add_comm Pos.one ⟨m⟩] at h0
        exact h0
      exact ground.posLtAddLe (ground.mul_lt_mul_right 2 h1)
        (Or.inr (ground.mul_lt_mul_right 2 h1))
    have hmag2 : windowsep.mag ((⟨⟨0⟩, ⟨m+1⟩⟩ : BPair).scale 2)
        = ((⟨⟨0⟩, ⟨m+1⟩⟩ : BPair).scale 2).swap := by
      unfold windowsep.mag
      rw [if_pos hlt2]
    have hmag1u : (windowsep.mag (BPair.unit.scale 1)).oneValue BPair.unit := by
      decide +kernel
    have hM : (windowsep.magFold (poly.deriv (qp a (m+1)))
        (⟨2, 1⟩ : BPair) ⟨2, 1⟩).oneValue
        ((⟨⟨0⟩, ⟨m+1⟩⟩ : BPair).scale 2).swap := by
      refine BPair.oneValue_trans hread ?_
      show (windowsep.mag (ground.getAt BPair.unit
              (poly.vnorm (poly.deriv (qp a (m+1)))) 0)
            * ground.bpow (⟨2, 1⟩ : BPair) 0 * ground.bpow (⟨2, 1⟩ : BPair) 1
          + (windowsep.mag (ground.getAt BPair.unit
                (poly.vnorm (poly.deriv (qp a (m+1)))) 1)
              * ground.bpow (⟨2, 1⟩ : BPair) 1
              * ground.bpow (⟨2, 1⟩ : BPair) 0
            + BPair.unit)).oneValue
        ((⟨⟨0⟩, ⟨m+1⟩⟩ : BPair).scale 2).swap
      refine BPair.oneValue_trans (BPair.add_congr ?_ (BPair.add_congr ?_
        (BPair.oneValue_refl BPair.unit)))
        (BPair.oneValue_trans (BPair.unit_add _) (BPair.add_unit _))
      · refine BPair.oneValue_trans (BPair.mul_congr (BPair.mul_congr
          (BPair.oneValue_trans (windowsep.mag_congr hg0) hmag1u)
          (BPair.oneValue_refl _)) (BPair.oneValue_refl _)) ?_
        decide +kernel
      · refine BPair.oneValue_trans (BPair.mul_congr (BPair.mul_congr
          (BPair.oneValue_trans (windowsep.mag_congr hg1)
            (BPair.oneValue_of_eq hmag2))
          (BPair.oneValue_refl _)) (BPair.oneValue_refl _)) ?_
        exact BPair.oneValue_trans
          (BPair.mul_one_read (((⟨⟨0⟩, ⟨m+1⟩⟩ : BPair).scale 2).swap
            * ground.bpow (⟨2, 1⟩ : BPair) 1))
          (BPair.mul_one_read ((⟨⟨0⟩, ⟨m+1⟩⟩ : BPair).scale 2).swap)
    have hC : (winTop + CPair.swap winFoot).oneValue
        (stage.ofB (BPair.ofPos Pos.one)) := by decide +kernel
    have hbp : (stage.ofB (ground.bpow (⟨2, 1⟩ : BPair)
        ((poly.vnorm (poly.deriv (qp a (m+1)))).length - 1))).oneValue
        (stage.ofB (BPair.ofPos Pos.one)) :=
      CPair.num_oneValue (ground.bpow_one _) Pos.one
    have hx : (stage.ofB ((⟨⟨0⟩, ⟨m+1⟩⟩ : BPair).scale 2).swap).oneValue
        (stage.ofB (windowsep.magFold (poly.deriv (qp a (m+1)))
            (⟨2, 1⟩ : BPair) ⟨2, 1⟩)
          * (winTop + CPair.swap winFoot)) :=
      CPair.oneValue_symm (CPair.oneValue_trans (cmul_one hC)
        (CPair.num_oneValue hM Pos.one))
    have hy : (stage.ofB (⟨⟨a⟩, ⟨0⟩⟩ : BPair)).oneValue
        (stage.evalC (qp a (m+1)) winFoot
          * stage.ofB (ground.bpow (⟨2, 1⟩ : BPair)
            ((poly.vnorm (poly.deriv (qp a (m+1)))).length - 1))) :=
      CPair.oneValue_symm (CPair.oneValue_trans (cmul_one hbp)
        (evalC_foot (qp a (m+1))))
    refine CPair.lt_congr hx hy (BPair.scale_lt Pos.one ?_)
    refine Exists.elim (Nat.le.dest ha) (fun j hj => ?_)
    subst hj
    refine ⟨⟨j⟩, congrArg Pos.mk ?_⟩
    show ((((m+1)*1 + (m+1) + 1) + 0 + 1) + j + 1)
        = ((2*(m+1)+1+j) + 1 + 1)
    rw [Nat.mul_one (m+1), Nat.mul_comm 2 (m+1)]
    show ((m+1) + (m+1) + 1) + 1 + j + 1
        = (((0 + (m+1)) + (m+1)) + 1 + j) + 1 + 1
    rw [Nat.zero_add (m+1), Nat.add_right_comm ((m+1) + (m+1) + 1) 1 j]

/-! The member floors' lower reads. -/

private theorem two_le_add {a b : Nat} (h : 2 ≤ b) : 2 ≤ a + b :=
  Nat.le_trans h (Nat.le_add_left b a)

private theorem two_le_ite {c : Prop} (inst : Decidable c) {a b : Nat}
    (ha : 2 ≤ a) (hb : 2 ≤ b) : 2 ≤ @ite Nat c inst a b :=
  match inst with
  | isTrue _ => ha
  | isFalse _ => hb

/-- The `A`-series' floor numerator sits at or above four. -/
private theorem floorA_ge (g : Nat) : 4 ≤ winFloorN (.A (g + 1)) := by
  have h2 : 2 ≤ g + 2 := Nat.le_add_left 2 g
  show 4 ≤ (g + 2) * (g + 4)
  exact Nat.add_le_add (two_le_add h2) h2

/-- The `B`-series' floor numerator sits at or above two, either
branch of the displayed minimum. -/
private theorem floorB_ge (g : Nat) : 2 ≤ winFloorN (.B g) := by
  show 2 ≤ @ite Nat (8 * (g + 2) ≤ (g + 2) * (2 * g + 5))
    (Nat.decLe _ _) (8 * (g + 2)) ((g + 2) * (2 * g + 5))
  exact two_le_ite _ (two_le_add (by decide +kernel : 2 ≤ 8))
    (two_le_add (Nat.le_add_left 2 g))

/-- The `C`-series' floor numerator sits at or above two. -/
private theorem floorC_ge (g : Nat) : 2 ≤ winFloorN (.C g) := by
  show 2 ≤ 2 * (2 * g + 7)
  exact two_le_add (Nat.le_refl 2)

/-- The `D`-series' floor numerator sits at or above two past the
four-loop index. -/
private theorem floorD_ge (g : Nat) : 2 ≤ winFloorN (.D (g + 1)) := by
  show 2 ≤ 8 * (2 * (g + 1) + 7)
  exact two_le_add (by decide +kernel : 2 ≤ 8)

/-- The lower side's priced read at a one-coefficient polynomial
off the vacuum: the vacant derivative's fold against the entry's own
value. -/
private theorem keepLower_cn (m : Nat) (hm : 1 ≤ m) :
    stage.keepLower [(BPair.ofNat m).swap] winFoot winTop ⟨2, 1⟩ ⟨2, 1⟩ := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  have hcore : BPair.unit < BPair.ofNat m := by
    cases m with
    | zero => exact absurd hm (Nat.not_lt_zero 0)
    | succ k =>
      refine ⟨⟨k⟩, congrArg Pos.mk ?_⟩
      show 0 + 0 + 1 + k + 1 = k + 0 + 1 + 0 + 1
      rw [Nat.add_comm 1 k]
  have hC : (winTop + CPair.swap winFoot).oneValue
      (stage.ofB (BPair.ofPos Pos.one)) := by decide +kernel
  have hbp : (stage.ofB (ground.bpow (⟨2, 1⟩ : BPair)
      ((poly.vnorm (poly.deriv [(BPair.ofNat m).swap])).length - 1))).oneValue
      (stage.ofB (BPair.ofPos Pos.one)) :=
    CPair.oneValue_refl _
  have hx : (stage.ofB BPair.unit).oneValue
      (stage.ofB (windowsep.magFold (poly.deriv [(BPair.ofNat m).swap])
          (⟨2, 1⟩ : BPair) ⟨2, 1⟩)
        * (winTop + CPair.swap winFoot)) :=
    CPair.oneValue_symm (cmul_one hC)
  have hy : (stage.ofB (BPair.ofNat m)).oneValue
      (CPair.swap (stage.evalC [(BPair.ofNat m).swap] winFoot)
        * stage.ofB (ground.bpow (⟨2, 1⟩ : BPair)
          ((poly.vnorm (poly.deriv [(BPair.ofNat m).swap])).length - 1))) :=
    CPair.oneValue_symm (CPair.oneValue_trans (cmul_one hbp)
      (CPair.swap_congr (evalC_foot [(BPair.ofNat m).swap])))
  exact CPair.lt_congr hx hy (BPair.scale_lt Pos.one hcore)

/-! The member tie at the committed pair. -/

private theorem tieNat (X m : Nat) :
    7 + (X + 3 + m + 0 + 1) + 1 + 3 + 1 = X + 6 + (m + 2) + 3 + 4 + 1 := by
  rw [Nat.add_comm 7 (X + 3 + m + 0 + 1), Nat.add_right_comm X 3 m]
  show X + m + 3 + 0 + 1 + 7 + 1 + 3 + 1 = X + 6 + m + 2 + 3 + 4 + 1
  rw [Nat.add_right_comm X 6 m]

/-- The member tie `ℓ₀ + E₀ κ* ≤ ℓ₊` at every occupied floor
numerator, the two sides equal-membered (`thm:gappos`(iv)'s fixed pair
at `E₀ = 4`). -/
private theorem tieRead (F : Nat) (hF : 1 ≤ F) :
    BPair.scale (⟨2, 1⟩ : BPair) 4
      + BPair.ofPos (4 * ground.posOfSucc (2 * F - 2))
    ≤ BPair.scale (⟨ground.posOfSucc (2 * F), 1⟩ : BPair) 4 := by
  cases F with
  | zero => exact absurd hF (Nat.not_lt_zero 0)
  | succ k =>
    refine Or.inl (congrArg Pos.mk ?_)
    show 7 + (3 * (2 * k) + 3 + 2 * k + 0 + 1) + 1 + 3 + 1
        = ((2 * k + 2) * 3 + (2 * k + 2) + 3) + 4 + 1
    rw [Nat.mul_comm 3 (2 * k), ground.mulAddR (2 * k) 2 3]
    exact tieNat ((2 * k) * 3) (2 * k)

/-! The cube's strict bound at the loop content, and the degree-nine
comparison at the upper sweep's own: the count monotonicity at an
occupied factor with the products' rearrangements. -/

private theorem natMulLtL {m u v : Nat} (hm : 0 < m) (h : u < v) :
    m * u < m * v := by
  refine Exists.elim (Nat.le.dest h) (fun d hd => ?_)
  rw [← hd, Nat.add_assoc u 1 d, Nat.add_comm 1 d, Nat.left_distrib m u (d + 1)]
  exact Nat.lt_add_of_pos_right (Nat.mul_pos hm (Nat.succ_pos d))

private theorem natCubeSwap (x y : Nat) :
    (x * y) * ((x * y) * (x * y)) = (x * (x * x)) * (y * (y * y)) := by
  rw [ground.mulMulMulComm x y x y, ground.mulMulMulComm x y (x * x) (y * y)]

private theorem coreIneq (n : Nat) (hn : 8 ≤ n) :
    6 * ((n + 1) * (n + 1)) < n * (n * n) := by
  have h8n : 8 * n ≤ n * n := Nat.mul_le_mul_right n hn
  have h7 : 7 ≤ 4 * n :=
    Nat.le_trans (show (7 : Nat) ≤ 4 * 8 by decide +kernel)
      (Nat.mul_le_mul_left 4 hn)
  have h16 : 12 * n + 4 * n = 16 * n := (ground.mulAddR 12 4 n).symm
  have h12 : 6 * n + 6 * n = 12 * n := (ground.mulAddR 6 6 n).symm
  have h2nn : 16 * n ≤ 2 * (n * n) := by
    rw [show (16 : Nat) * n = 2 * (8 * n) from ground.mulAssoc 2 8 n]
    exact Nat.mul_le_mul_left 2 h8n
  have hstep : 12 * n + 6 < 16 * n := by
    rw [← h16]
    exact Nat.lt_of_lt_of_le (show 12 * n + 6 < 12 * n + 7 from Nat.le_refl _)
      (Nat.add_le_add (Nat.le_refl (12 * n)) h7)
  have hmid : 6 * n + 6 * n + 6 < 2 * (n * n) := by
    rw [h12]
    exact Nat.lt_of_lt_of_le hstep h2nn
  have hR : 6 * (n * n) + 2 * (n * n) ≤ n * (n * n) := by
    rw [← ground.mulAddR 6 2 (n * n)]
    exact Nat.mul_le_mul_right (n * n) hn
  have hL : 6 * ((n + 1) * (n + 1)) = 6 * (n * n) + (6 * n + 6 * n + 6) := by
    rw [Nat.mul_add (n + 1) n 1, Nat.mul_one (n + 1), ground.mulAddR n 1 n,
      Nat.one_mul n, ← Nat.add_assoc (n * n + n) n 1,
      Nat.mul_add 6 (n * n + n + n) 1, Nat.mul_one 6,
      Nat.mul_add 6 (n * n + n) n, Nat.mul_add 6 (n * n) n,
      Nat.add_assoc (6 * (n * n) + 6 * n) (6 * n) 6,
      Nat.add_assoc (6 * (n * n)) (6 * n) (6 * n + 6),
      ← Nat.add_assoc (6 * n) (6 * n) 6]
  rw [hL]
  exact Nat.lt_of_lt_of_le (Nat.add_le_add (Nat.le_refl (6 * (n * n))) hmid) hR

private theorem bigIneq (n : Nat) (hn : 8 ≤ n) :
    6 * ((n * n) * ((n * n * n + n * n) * (n * n * n + n * n)))
      < (n * n * n) * ((n * n * n) * (n * n * n)) := by
  have hn0 : 0 < n :=
    Nat.lt_of_lt_of_le (show (0 : Nat) < 8 by decide +kernel) hn
  have hnn : 0 < n * n := Nat.mul_pos hn0 hn0
  have hAC : (n * n) * (n + 1) = n * n * n + n * n := by
    rw [Nat.mul_add (n * n) n 1, Nat.mul_one (n * n)]
  rw [natCubeSwap (n * n) n, ← hAC, ground.mulMulMulComm (n * n) (n + 1) (n * n) (n + 1),
    ← ground.mulAssoc (n * n) ((n * n) * (n * n)) ((n + 1) * (n + 1)),
    ground.mulLeftComm 6 ((n * n) * ((n * n) * (n * n))) ((n + 1) * (n + 1))]
  exact natMulLtL (Nat.mul_pos hnn (Nat.mul_pos hnn hnn)) (coreIneq n hn)

/-- The order-one deflation's leading entry at one trailing key,
the coupling's tail read at the key itself, read at an abstract
pencil. -/
private theorem defl1' (T : split.PMat)
    (hut : poly.unitTail (ground.getAt [] (ground.getAt [] T 1) 0)) :
    poly.oneValue
      (ground.getAt [] (ground.getAt [] (cellcount.pdefl [0] [1] T) 0) 0)
      (poly.mul (poly.mul (ground.getAt [] (ground.getAt [] T 0) 0)
          (ground.getAt [] (ground.getAt [] T 0) 0))
        (ground.getAt [] (ground.getAt [] T 1) 1)) :=
  have hoff : ∀ k, k < ([1] : List Nat).length → poly.unitTail
      (ground.getAt [] (ground.getAt [] T (ground.getAt 0 [1] k)) 0) :=
    fun k => match k with
      | 0 => fun _ => hut
      | k + 1 => fun hk2 => absurd (Nat.lt_of_succ_lt_succ hk2)
        (Nat.not_lt_zero k)
  (cellcount.pdefl_offC T 0 [1] hoff).1.1

/-- The order-one deflation's four trailing entries at stated entry
values: the two loop places at the valued product, the couplings
exchanged and unit-tailed — the deflation display read at an
abstract pencil, every entry a stated datum. -/
private theorem defl2v (T : split.PMat) (hd lp1 lp2 cp Q : poly.Poly)
    (hoff : ∀ k, k < ([1, 2] : List Nat).length → poly.unitTail
      (getAt [] (getAt [] T (getAt 0 [1, 2] k)) 0))
    (hh : getAt [] (getAt [] T 0) 0 = hd)
    (hl1 : getAt [] (getAt [] T 1) 1 = lp1)
    (hl2 : getAt [] (getAt [] T 2) 2 = lp2)
    (hc1 : getAt [] (getAt [] T 1) 2 = cp)
    (hc2 : getAt [] (getAt [] T 2) 1 = cp)
    (hcut : poly.unitTail cp)
    (h1 : poly.oneValue (poly.mul (poly.mul hd hd) lp1) Q)
    (h2 : poly.oneValue (poly.mul (poly.mul hd hd) lp2) Q) :
    poly.oneValue
        (getAt [] (getAt [] (cellcount.pdefl [0] [1, 2] T) 0) 0) Q
      ∧ poly.oneValue
        (getAt [] (getAt [] (cellcount.pdefl [0] [1, 2] T) 1) 1) Q
      ∧ poly.oneValue
        (getAt [] (getAt [] (cellcount.pdefl [0] [1, 2] T) 0) 1)
        (getAt [] (getAt [] (cellcount.pdefl [0] [1, 2] T) 1) 0)
      ∧ poly.unitTail
        (getAt [] (getAt [] (cellcount.pdefl [0] [1, 2] T) 1) 0) := by
  have hoc := cellcount.pdefl_offC T 0 [1, 2] hoff
  have g00 : poly.oneValue
      (getAt [] (getAt [] (cellcount.pdefl [0] [1, 2] T) 0) 0)
      (poly.mul (poly.mul (getAt [] (getAt [] T 0) 0)
          (getAt [] (getAt [] T 0) 0))
        (getAt [] (getAt [] T 1) 1)) := hoc.1.1
  have g01 : poly.oneValue
      (getAt [] (getAt [] (cellcount.pdefl [0] [1, 2] T) 0) 1)
      (poly.mul (poly.mul (getAt [] (getAt [] T 0) 0)
          (getAt [] (getAt [] T 0) 0))
        (getAt [] (getAt [] T 1) 2)) := hoc.1.2.1
  have g10 : poly.oneValue
      (getAt [] (getAt [] (cellcount.pdefl [0] [1, 2] T) 1) 0)
      (poly.mul (poly.mul (getAt [] (getAt [] T 0) 0)
          (getAt [] (getAt [] T 0) 0))
        (getAt [] (getAt [] T 2) 1)) := hoc.2.1.1
  have g11 : poly.oneValue
      (getAt [] (getAt [] (cellcount.pdefl [0] [1, 2] T) 1) 1)
      (poly.mul (poly.mul (getAt [] (getAt [] T 0) 0)
          (getAt [] (getAt [] T 0) 0))
        (getAt [] (getAt [] T 2) 2)) := hoc.2.1.2.1
  rw [hh, hl1] at g00
  rw [hh, hc1] at g01
  rw [hh, hc2] at g10
  rw [hh, hl2] at g11
  exact ⟨poly.oneValue_trans g00 h1, poly.oneValue_trans g11 h2,
    poly.oneValue_trans g01 (poly.oneValue_symm g10),
    poly.oneValue_unitTail g10
      (poly.of_unitTail_mul (Or.inr hcut))⟩

/-- The cube step at an abstract pencil: the order-one deflation's
leading entry reads the pivot's cube when the pivot and the trailing
loop read one value and the coupling keeps the sum's unit. -/
private theorem cubeStep (T : split.PMat) (Q R : poly.Poly)
    (hut : poly.unitTail (ground.getAt [] (ground.getAt [] T 1) 0))
    (h00 : poly.oneValue (ground.getAt [] (ground.getAt [] T 0) 0) Q)
    (h11 : poly.oneValue (ground.getAt [] (ground.getAt [] T 1) 1) Q)
    (hR : poly.oneValue (poly.mul Q (poly.mul Q Q)) R) :
    poly.oneValue
      (ground.getAt [] (ground.getAt [] (cellcount.pdefl [0]
        (cellcount.compl [0] 2) T) 0) 0) R :=
  poly.oneValue_trans (defl1' T hut)
    (poly.oneValue_trans
      (poly.mul_congr_left
        (poly.oneValue_trans (poly.mul_congr_left h00 _)
          (poly.mul_congr Q h00)) _)
      (poly.oneValue_trans (poly.mul_congr (poly.mul Q Q) h11)
        (poly.oneValue_trans (poly.mul_assoc Q Q Q) hR)))

/-- The two-level diagonal nest at an abstract pencil of order
two: the pivot's own priced side read above the cleared deflation's,
the clearings the odd multiples `3 K` and `3 (3 K)`. -/
private theorem subCover (T : split.PMat) (Q R : poly.Poly)
    (hsh : cellcount.pShapeAt T 2 6)
    (hents : poly.oneValue (ground.getAt [] (ground.getAt [] T 0) 0) Q
      ∧ poly.oneValue (ground.getAt [] (ground.getAt [] T 1) 1) Q
      ∧ poly.oneValue (ground.getAt [] (ground.getAt [] T 0) 1)
        (ground.getAt [] (ground.getAt [] T 1) 0)
      ∧ poly.unitTail (ground.getAt [] (ground.getAt [] T 1) 0))
    (hQ : stage.keepUpper Q winFoot winTop ⟨2, 1⟩ ⟨2, 1⟩)
    (hR : poly.oneValue (poly.mul Q (poly.mul Q Q)) R)
    (hRk : stage.keepUpper R winFoot winTop ⟨2, 1⟩ ⟨2, 1⟩) :
    cellcount.coverRead T 2 6 winFoot winTop
      (cellcount.diagNest winTop ⟨2, 1⟩ ⟨2, 1⟩ 2) := by
  have h00 := hents.1
  have h11 := hents.2.1
  have hsym01 := hents.2.2.1
  have hut := hents.2.2.2
  have hsub2 : cellcount.pShapeAt (cellcount.pdefl [0]
      (cellcount.compl [0] 2) T) 1 18 :=
    cellcount.pShape_pdefl T 2 6 [0] (cellcount.compl [0] 2) hsh (Or.inl rfl)
  refine ⟨⟨by decide +kernel, rfl, by decide +kernel, hsh, ?_⟩,
    ?_,
    ⟨⟨by decide +kernel, rfl, by decide +kernel, hsub2, ?_⟩,
      ?_, rfl, ⟨hsub2, rfl⟩⟩,
    ⟨hsh, rfl⟩⟩
  · refine split.pSymAt_of _ 2 (fun i j hi hj => ?_)
    match i, j with
    | 0, 0 => exact poly.oneValue_refl _
    | 0, 1 => exact hsym01
    | 1, 0 => exact poly.oneValue_symm hsym01
    | 1, 1 => exact poly.oneValue_refl _
    | 0, j + 2 => exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hj)) (Nat.not_lt_zero j)
    | 1, j + 2 => exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hj)) (Nat.not_lt_zero j)
    | i + 2, _ => exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi)) (Nat.not_lt_zero i)
  · exact stage.keepUpper_congr (poly.oneValue_symm h00) winFoot winTop
      ⟨2, 1⟩ ⟨2, 1⟩ hQ
  · refine split.pSymAt_of _ 1 (fun i j hi hj => ?_)
    match i, j with
    | 0, 0 => exact poly.oneValue_refl _
    | 0, j + 1 => exact absurd (Nat.lt_of_succ_lt_succ hj) (Nat.not_lt_zero j)
    | i + 1, _ => exact absurd (Nat.lt_of_succ_lt_succ hi) (Nat.not_lt_zero i)
  · exact stage.keepUpper_congr
      (poly.oneValue_symm (cubeStep T Q R hut h00 h11 hR))
      winFoot winTop ⟨2, 1⟩ ⟨2, 1⟩ hRk

/-! The lower sweep's structural reads at order two. -/

private theorem loOffR (cut : Nat) : ∀ k, k < ([1] : List Nat).length →
    poly.unitTail (getAt [] (getAt [] (sLo 2 cut) (getAt 0 [1] k)) 0) := by
  intro k hk
  match k with
  | 0 => exact sLo_offR 2 cut 1 (Nat.succ_pos 0) (Nat.le_refl 2)
  | k + 1 => exact absurd (Nat.lt_of_succ_lt_succ hk) (Nat.not_lt_zero k)

/-- The lower head's square reads the product's unit, one decided
value. -/
private theorem loSq3 : poly.oneValue
    (poly.mul [(⟨⟨4⟩, ⟨5⟩⟩ : BPair), BPair.unit, BPair.unit]
      [(⟨⟨4⟩, ⟨5⟩⟩ : BPair), BPair.unit, BPair.unit]) poly.one := by
  decide +kernel

/-- The lower sweep's loop head coefficient at a stated cutoff. -/
private def loD1 (cut : Nat) : BPair :=
  (BPair.ofNat cut + (BPair.ofNat 1).scale 1) + ((BPair.ofNat 1).scale 2).swap

/-- The lower carrier's loop entry at its occupied diagonal key:
the loop head coefficient at the cutoff with the magnetic member's
balance partner. -/
private theorem sLo_loop (o cut i : Nat) (h1 : 0 < i) (hio : i < o) :
    getAt [] (getAt [] (sLo o cut) i) i
      = [loD1 cut, BPair.unit, (⟨1, 2⟩ : BPair)] := by
  rw [show sLo o cut = freecell.freePMat (winDiag o (BPair.ofNat cut))
      (winDiag o ⟨2, 1⟩) (inertia.idMat o) 2 1 from rfl,
    winEntry_loop o (BPair.ofNat cut) ⟨2, 1⟩ 2 1 i h1 hio]
  rfl

/-- The lower sweep's cleared deflation reads the loop head's
two-coefficient value at the cutoff's predecessor. -/
private theorem loHeadValue (k : Nat) :
    poly.oneValue
      (getAt [] (getAt [] (cellcount.pdefl [0] (cellcount.compl [0] 2)
        (sLo 2 (4 * (k + 2)))) 0) 0) (qp (4 * k + 7) 1) := by
  have hd := cellcount.pdefl_offC (sLo 2 (4 * (k + 2))) 0 [1]
    (loOffR (4 * (k + 2)))
  refine poly.oneValue_trans hd.1.1 ?_
  show poly.oneValue
    (poly.mul (poly.mul (getAt [] (getAt [] (sLo 2 (4 * (k + 2))) 0) 0)
        (getAt [] (getAt [] (sLo 2 (4 * (k + 2))) 0) 0))
      (getAt [] (getAt [] (sLo 2 (4 * (k + 2))) 1) 1))
    (qp (4 * k + 7) 1)
  rw [sLo_head 2 (4 * (k + 2)) (Nat.succ_pos 1),
    sLo_loop 2 (4 * (k + 2)) 1 (Nat.succ_pos 0) (Nat.le_refl 2)]
  refine poly.oneValue_trans (poly.mul_congr_left loSq3 _) ?_
  refine poly.oneValue_trans (poly.one_mul _) ?_
  exact ⟨rfl, rfl, rfl, trivial⟩

private theorem loD1_le (j : Nat) : BPair.unit ≤ loD1 (j + 8) := by
  refine Or.inr ⟨⟨j + 6⟩, congrArg Pos.mk ?_⟩
  show 6 + (j + 6) + 1 = j + 13
  rw [Nat.add_comm 6 (j + 6)]

private theorem loD1_off (j : Nat) : ¬ (loD1 (j + 8)).oneValue BPair.unit := by
  intro h
  exact Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj
    (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (ground.posMkInj h)))))))

private theorem loBlock (k : Nat) :
    elim.matOneValue (cellcount.evalPC (sLo 2 (4 * (k + 2))) BPair.unit 1 2)
      (inertia.blockMat [.one (⟨⟨4⟩, ⟨5⟩⟩ : BPair),
        .one (loD1 (4 * (k + 2)))] 0) := by
  refine ⟨⟨evalHead _, ?_, trivial⟩, ⟨?_, evalHead _, trivial⟩, trivial⟩
  · exact BPair.oneValue_trans (evalHead _) (coupHead 2)
  · exact BPair.oneValue_trans (evalHead _) (coupHead 2)

private theorem loCount (k : Nat) :
    inertia.splitRead
        (cellcount.evalPC (sLo 2 (4 * (k + 2))) BPair.unit 1 2)
        (inertia.mkSplit 2
          (cellcount.evalPC (sLo 2 (4 * (k + 2))) BPair.unit 1 2))
      ∧ inertia.revAt (inertia.mkSplit 2
          (cellcount.evalPC (sLo 2 (4 * (k + 2))) BPair.unit 1 2)) = 1 := by
  have hshape : cellcount.pShapeAt (sLo 2 (4 * (k + 2))) 2 2 :=
      sLo_shape 2 (4 * (k + 2))
  have hoffD1 : ¬ (loD1 (4 * (k + 2))).oneValue BPair.unit := loD1_off (4 * k)
  have hleD1 : BPair.unit ≤ loD1 (4 * (k + 2)) := loD1_le (4 * k)
  have hsq : elim.sqAt
      (cellcount.evalPC (sLo 2 (4 * (k + 2))) BPair.unit 1 2) 2 :=
    cellcount.evalPC_sqAt hshape BPair.unit 1
  have hsplit := inertia.mkSplit_read 2
    (cellcount.evalPC (sLo 2 (4 * (k + 2))) BPair.unit 1 2) hsq
    (elim.matOne_symm (cellcount.evalPC_symAt (sLo 2 (4 * (k + 2))) 2 2
      BPair.unit 1 hshape (sLo_sym 2 (4 * (k + 2)))))
  have hoff : (([(⟨⟨4⟩, ⟨5⟩⟩ : BPair), loD1 (4 * (k + 2))] : List BPair).all
      (fun d => !(decide (d.oneValue BPair.unit)))) = true := by
    show (!(decide ((⟨⟨4⟩, ⟨5⟩⟩ : BPair).oneValue BPair.unit))
      && (!(decide ((loD1 (4 * (k + 2))).oneValue BPair.unit)) && true))
      = true
    rw [decide_eq_false hoffD1]
    rfl
  have hone := inertia.oneSplit_read
    [(⟨⟨4⟩, ⟨5⟩⟩ : BPair), loD1 (4 * (k + 2))]
    (cellcount.evalPC (sLo 2 (4 * (k + 2))) BPair.unit 1 2) hsq
    (loBlock k) hoff
  refine ⟨hsplit, ?_⟩
  rw [inertia.rev_exchange
      (cellcount.evalPC (sLo 2 (4 * (k + 2))) BPair.unit 1 2) _ _
      hsplit hone,
    inertia.revAt_oneSplit [(⟨⟨4⟩, ⟨5⟩⟩ : BPair), loD1 (4 * (k + 2))]]
  show 0 + (inertia.SBlock.one (⟨⟨4⟩, ⟨5⟩⟩ : BPair)).rev
      + (inertia.SBlock.one (loD1 (4 * (k + 2)))).rev = 1
  rw [inertia.rev_one_le hleD1,
    inertia.rev_one_lt (show (⟨⟨4⟩, ⟨5⟩⟩ : BPair) < BPair.unit by
      decide +kernel)]

/-- The lower sweep's chain at order two: one located cell at the
committed segment, the diagonal pivot nest beneath it and the count one
at the free end. -/
private theorem chainLo2 (F : Nat) (hF : 2 ≤ F) :
    gappos.chainRead (sLo 2 (4 * F)) 2 1 winFoot
      [(winTop, cellcount.diagCover winTop ⟨2, 1⟩ ⟨2, 1⟩ 1,
        (BPair.unit, 1),
        inertia.mkSplit 2 (cellcount.evalPC (sLo 2 (4 * F))
          BPair.unit 1 2))] := by
  match F, hF with
  | 0, hF => exact absurd hF (Nat.not_lt_zero 1)
  | 1, hF => exact absurd (Nat.lt_of_succ_lt_succ hF) (Nat.not_lt_zero 0)
  | k + 2, _ =>
    have hshape : cellcount.pShapeAt (sLo 2 (4 * (k + 2))) 2 2 :=
      sLo_shape 2 (4 * (k + 2))
    have hsub : cellcount.pShapeAt (cellcount.pdefl [0]
        (cellcount.compl [0] 2) (sLo 2 (4 * (k + 2)))) 1 6 :=
      cellcount.pShape_pdefl _ 2 2 [0] (cellcount.compl [0] 2) hshape
        (Or.inl rfl)
    refine ⟨⟨⟨winFoot_le_top, rfl, winPlace0, hshape,
          sLo_sym 2 (4 * (k + 2))⟩,
        ?_,
        ⟨⟨winFoot_le_top, rfl, winPlace0, hsub, ?_⟩,
          ?_, rfl, ⟨hsub, rfl⟩⟩,
        ⟨hshape, rfl⟩⟩,
      winFoot_le_sample, winSample_le_top,
      ⟨hshape, (loCount k).1, (loCount k).2⟩, trivial⟩
    · exact sLo_headKeep 2 (4 * (k + 2)) (Nat.succ_pos 1)
    · refine split.pSymAt_of _ 1 (fun i j hi hj => ?_)
      match i, j with
      | 0, 0 => exact poly.oneValue_refl _
      | 0, j + 1 => exact absurd (Nat.lt_of_succ_lt_succ hj) (Nat.not_lt_zero j)
      | i + 1, _ => exact absurd (Nat.lt_of_succ_lt_succ hi) (Nat.not_lt_zero i)
    · show stage.keepUpper (getAt [] (getAt [] (cellcount.pdefl [0]
        (cellcount.compl [0] 2) (sLo 2 (4 * (k + 2)))) 0) 0)
        winFoot winTop ⟨2, 1⟩ ⟨2, 1⟩
      exact stage.keepUpper_congr (poly.oneValue_symm (loHeadValue k)) winFoot winTop
        ⟨2, 1⟩ ⟨2, 1⟩
        (keepUpper_qp (4 * k + 7) 1 (Nat.le_refl 1)
          (Nat.le_add_left 3 (4 * k + 4)))

/-! The upper sweep's structural reads at order two. -/

private theorem cubeGap (C m : Nat) (hC : 1 ≤ C) : 2 * C + 1 ≤ C * (m + 4) := by
  rw [Nat.two_mul C]
  show C + C + 1 ≤ C * m + C + C + C + C
  refine Nat.le_trans (Nat.add_le_add (Nat.le_refl (C + C)) hC) ?_
  refine Nat.le_trans (Nat.add_le_add (Nat.add_le_add
    (Nat.le_add_left C (C * m)) (Nat.le_refl C)) (Nat.le_refl C)) ?_
  exact Nat.le_add_right (C * m + C + C + C) C

private theorem natI1 (n : Nat) :
    (2 + (0 * n + 0 + n) + 1) + n + 1 = 0 + (1 + (1 * n + 1 + n) + 1) + 1 := by
  show (2 + (0 * n + n) + 1) + n + 1 = 0 + (1 + (1 * n + 1 + n) + 1) + 1
  rw [Nat.zero_mul n, Nat.zero_add n, Nat.one_mul n,
    Nat.zero_add (1 + (n + 1 + n) + 1),
    Nat.add_comm 2 n, Nat.add_comm 1 (n + 1 + n),
    Nat.add_right_comm (n + 2) 1 n, Nat.add_right_comm n 2 n,
    Nat.add_right_comm n 1 n]

private theorem natI2 (m : Nat) :
    m + m + 8 + 1 + 1 + (m + 4) + 1 + 1
      = m + 4 + (1 + (m + 4 + 1 + (m + 4)) + 1) + 1 := by
  rw [← Nat.add_assoc (m + m + 8 + 1 + 1) m 4,
    Nat.add_right_comm (m + m + 8 + 1) 1 m,
    Nat.add_right_comm (m + m + 8) 1 m,
    Nat.add_right_comm (m + m) 8 m,
    ← Nat.add_assoc (m + 4 + 1) m 4,
    Nat.add_right_comm (m + 4) 1 m,
    Nat.add_right_comm m 4 m,
    Nat.add_comm 1 (m + m + 4 + 1 + 4),
    Nat.add_comm (m + 4) (m + m + 4 + 1 + 4 + 1 + 1),
    ← Nat.add_assoc (m + m + 4 + 1 + 4 + 1 + 1) m 4,
    Nat.add_right_comm (m + m + 4 + 1 + 4 + 1) 1 m,
    Nat.add_right_comm (m + m + 4 + 1 + 4) 1 m,
    Nat.add_right_comm (m + m + 4 + 1) 4 m,
    Nat.add_right_comm (m + m + 4) 1 m,
    Nat.add_right_comm (m + m) 4 m]

private theorem swapLtUnit (m : Nat) :
    (⟨⟨0⟩, ⟨m + 1⟩⟩ : BPair) < BPair.unit := by
  refine ⟨⟨m⟩, congrArg Pos.mk ?_⟩
  show 1 + m + 1 = 0 + (m + 1) + 1
  rw [Nat.zero_add (m + 1), Nat.add_comm 1 m]

private theorem unitLeNat (m : Nat) :
    BPair.unit ≤ (⟨⟨m + 1⟩, ⟨0⟩⟩ : BPair) := by
  refine Or.inr ⟨⟨m⟩, congrArg Pos.mk ?_⟩
  show 1 + m + 1 = m + 1 + 1
  rw [Nat.add_comm 1 m]

/-- The upper sweep's head coefficient at a stated floor numerator,
value `−2F`. -/
private def hiD0 (F : Nat) : BPair :=
  (BPair.unit + (BPair.ofNat 1).scale 1)
    + ((BPair.ofNat 1).scale (ground.posOfSucc (2 * F))).swap

/-- The upper sweep's loop head coefficient at a stated floor
numerator, value `2F`. -/
private def hiD1 (F : Nat) : BPair :=
  (BPair.ofNat (4 * F) + (BPair.ofNat 1).scale 1)
    + ((BPair.ofNat 1).scale (ground.posOfSucc (2 * F))).swap

/-- The upper carrier's head entry, value `−2F`: the stated level
over the unit line. -/
private theorem sHi_head (o F : Nat) (ho : 0 < o) :
    getAt [] (getAt [] (sHi o F) 0) 0
      = [hiD0 F, BPair.unit, BPair.unit] := by
  rw [show sHi o F = freecell.freePMat (winDiag o (BPair.ofNat (4 * F)))
      (winDiag o ⟨2, 1⟩) (inertia.idMat o)
      (ground.posOfSucc (2 * F)) 1 from rfl,
    winEntry_head o (BPair.ofNat (4 * F)) ⟨2, 1⟩
      (ground.posOfSucc (2 * F)) 1 ho]
  rfl

/-- The upper carrier's loop entry at its occupied diagonal key. -/
private theorem sHi_loop (o F i : Nat) (h1 : 0 < i) (hio : i < o) :
    getAt [] (getAt [] (sHi o F) i) i
      = [hiD1 F, BPair.unit, (⟨1, 2⟩ : BPair)] := by
  rw [show sHi o F = freecell.freePMat (winDiag o (BPair.ofNat (4 * F)))
      (winDiag o ⟨2, 1⟩) (inertia.idMat o)
      (ground.posOfSucc (2 * F)) 1 from rfl,
    winEntry_loop o (BPair.ofNat (4 * F)) ⟨2, 1⟩
      (ground.posOfSucc (2 * F)) 1 i h1 hio]
  rfl

private theorem hiD0_raw (F : Nat) :
    (hiD0 F).oneValue (⟨⟨0⟩, ⟨2 * F⟩⟩ : BPair) := by
  refine congrArg Pos.mk ?_
  exact natI1 (2 * F)

private theorem hiD1_raw (k : Nat) :
    (hiD1 (k + 2)).oneValue (⟨⟨2 * (k + 2)⟩, ⟨0⟩⟩ : BPair) := by
  refine congrArg Pos.mk ?_
  show 4 * k + 8 + 1 + 1 + (0 * (2 * (k + 2)) + 2 * (k + 2)) + 1 + 1
      = 2 * (k + 2) + (1 + (1 * (2 * (k + 2)) + 1 + 2 * (k + 2)) + 1) + 1
  rw [Nat.zero_mul (2 * (k + 2)), Nat.zero_add (2 * (k + 2)),
    Nat.one_mul (2 * (k + 2)), ground.fourMul k]
  exact natI2 (2 * k)

private theorem hiD0_read (F : Nat) :
    (hiD0 F).oneValue ((BPair.ofNat (2 * F)).swap) :=
  BPair.oneValue_trans (hiD0_raw F) (BPair.oneValue_of_eq (bofNatSwap (2 * F)))

private theorem hiD1_read (k : Nat) :
    (hiD1 (k + 2)).oneValue (BPair.ofNat (2 * (k + 2))) :=
  BPair.oneValue_trans (hiD1_raw k) (BPair.oneValue_of_eq (bofNat (2 * (k + 2))))

private theorem hiD0_lt (k : Nat) : hiD0 (k + 2) < BPair.unit :=
  BPair.lt_congr (BPair.oneValue_symm (hiD0_raw (k + 2)))
    (BPair.oneValue_refl _) (swapLtUnit (2 * k + 3))

private theorem hiD1_le (k : Nat) : BPair.unit ≤ hiD1 (k + 2) :=
  ground.leB_congr_right (BPair.oneValue_symm (hiD1_raw k))
    (unitLeNat (2 * k + 3))

private theorem hiD0_off (k : Nat) : ¬ (hiD0 (k + 2)).oneValue BPair.unit :=
  fun h => BPair.ofNat_swap_off (2 * (k + 2)) (Nat.succ_pos _)
    (BPair.oneValue_trans
      (BPair.oneValue_symm (hiD0_read (k + 2))) h)

private theorem hiD1_off (k : Nat) : ¬ (hiD1 (k + 2)).oneValue BPair.unit :=
  fun h => BPair.ofNat_off_unit (2 * (k + 2)) (Nat.succ_pos _)
    (BPair.oneValue_trans (BPair.oneValue_symm (hiD1_read k)) h)

private theorem hiOffR (F : Nat) : ∀ k, k < ([1] : List Nat).length →
    poly.unitTail (getAt [] (getAt [] (sHi 2 F) (getAt 0 [1] k)) 0) := by
  intro k hk
  match k with
  | 0 => exact sHi_offR 2 F 1 (Nat.succ_pos 0) (Nat.le_refl 2)
  | k + 1 => exact absurd (Nat.lt_of_succ_lt_succ hk) (Nat.not_lt_zero k)

private theorem hiHeadPolyLit (F : Nat) :
    poly.oneValue [hiD0 F, BPair.unit, BPair.unit]
      [(BPair.ofNat (2 * F)).swap] :=
  ⟨hiD0_read F, BPair.oneValue_refl _, BPair.oneValue_refl _, trivial⟩

private theorem hiSqLit (F : Nat) :
    poly.oneValue (poly.mul [hiD0 F, BPair.unit, BPair.unit]
        [hiD0 F, BPair.unit, BPair.unit])
      [(BPair.ofNat (2 * F)).swap * (BPair.ofNat (2 * F)).swap] :=
  poly.oneValue_trans
    (poly.mul_congr_left (hiHeadPolyLit F) _)
    (poly.oneValue_trans
      (poly.mul_congr [(BPair.ofNat (2 * F)).swap] (hiHeadPolyLit F))
      (poly.mul_single [(BPair.ofNat (2 * F)).swap] (BPair.ofNat (2 * F)).swap))

private theorem hiHeadPoly (o F : Nat) (ho : 0 < o) :
    poly.oneValue (getAt [] (getAt [] (sHi o F) 0) 0)
      [(BPair.ofNat (2 * F)).swap] := by
  rw [sHi_head o F ho]
  exact hiHeadPolyLit F

/-- The upper sweep's cleared deflation reads the loop head's
two-coefficient value at the cube and square of the level. -/
private theorem hiLoop (k : Nat) :
    poly.oneValue
      (poly.mul (poly.mul [hiD0 (k + 2), BPair.unit, BPair.unit]
          [hiD0 (k + 2), BPair.unit, BPair.unit])
        [hiD1 (k + 2), BPair.unit, (⟨1, 2⟩ : BPair)])
      (qp (2 * (k + 2) * (2 * (k + 2)) * (2 * (k + 2)))
        (2 * (k + 2) * (2 * (k + 2)))) := by
  refine poly.oneValue_trans (poly.mul_congr_left (hiSqLit (k + 2)) _) ?_
  refine poly.oneValue_trans (poly.mul_comm _ _) ?_
  refine poly.oneValue_trans (poly.mul_single _
    ((BPair.ofNat (2 * (k + 2))).swap * (BPair.ofNat (2 * (k + 2))).swap)) ?_
  refine ⟨?_, BPair.mul_unit _, ?_, trivial⟩
  · refine BPair.oneValue_trans
      (BPair.mul_congr
        (BPair.oneValue_of_eq (BPair.swap_mul_swap _ _)) (hiD1_read k)) ?_
    refine BPair.oneValue_symm (BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (bofNat (2 * (k + 2) * (2 * (k + 2)) * (2 * (k + 2))))) ?_)
    exact BPair.oneValue_trans
      (BPair.ofNat_mul (2 * (k + 2) * (2 * (k + 2))) (2 * (k + 2)))
      (BPair.mul_congr_left (BPair.ofNat_mul (2 * (k + 2)) (2 * (k + 2))))
  · have h3 : (((BPair.ofNat (2 * (k + 2))).swap
          * (BPair.ofNat (2 * (k + 2))).swap) * BPair.ofNat 1).oneValue
        (BPair.ofNat (2 * (k + 2) * (2 * (k + 2)))) :=
      BPair.oneValue_trans (BPair.mul_ofNat_one _)
        (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.swap_mul_swap _ _))
          (BPair.oneValue_symm
            (BPair.ofNat_mul (2 * (k + 2)) (2 * (k + 2)))))
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_swap
        ((BPair.ofNat (2 * (k + 2))).swap * (BPair.ofNat (2 * (k + 2))).swap)
        (BPair.ofNat 1))) ?_
    exact BPair.oneValue_trans (ground.swap_congr h3)
      (BPair.oneValue_of_eq (bofNatSwap (2 * (k + 2) * (2 * (k + 2)))).symm)

/-- The upper sweep's cleared deflation reads the loop head's
two-coefficient value at the cube and square of the level. -/
private theorem hiHeadValue (k : Nat) :
    poly.oneValue
      (getAt [] (getAt [] (cellcount.pdefl [0] (cellcount.compl [0] 2)
        (sHi 2 (k + 2))) 0) 0)
      (qp (2 * (k + 2) * (2 * (k + 2)) * (2 * (k + 2)))
        (2 * (k + 2) * (2 * (k + 2)))) := by
  have hd := cellcount.pdefl_offC (sHi 2 (k + 2)) 0 [1] (hiOffR (k + 2))
  refine poly.oneValue_trans hd.1.1 ?_
  show poly.oneValue
    (poly.mul (poly.mul (getAt [] (getAt [] (sHi 2 (k + 2)) 0) 0)
        (getAt [] (getAt [] (sHi 2 (k + 2)) 0) 0))
      (getAt [] (getAt [] (sHi 2 (k + 2)) 1) 1))
    (qp (2 * (k + 2) * (2 * (k + 2)) * (2 * (k + 2)))
      (2 * (k + 2) * (2 * (k + 2))))
  rw [sHi_head 2 (k + 2) (Nat.succ_pos 1),
    sHi_loop 2 (k + 2) 1 (Nat.succ_pos 0) (Nat.le_refl 2)]
  exact hiLoop k

private theorem hiBlock (k : Nat) :
    elim.matOneValue (cellcount.evalPC (sHi 2 (k + 2)) BPair.unit 1 2)
      (inertia.blockMat [.one (hiD0 (k + 2)), .one (hiD1 (k + 2))] 0) := by
  refine ⟨⟨evalHead _, ?_, trivial⟩, ⟨?_, evalHead _, trivial⟩, trivial⟩
  · exact BPair.oneValue_trans (evalHead _) (coupHead (ground.posOfSucc (2 * (k + 2))))
  · exact BPair.oneValue_trans (evalHead _) (coupHead (ground.posOfSucc (2 * (k + 2))))

private theorem hiCount (k : Nat) :
    inertia.splitRead
        (cellcount.evalPC (sHi 2 (k + 2)) BPair.unit 1 2)
        (inertia.mkSplit 2
          (cellcount.evalPC (sHi 2 (k + 2)) BPair.unit 1 2))
      ∧ inertia.revAt (inertia.mkSplit 2
          (cellcount.evalPC (sHi 2 (k + 2)) BPair.unit 1 2)) = 1 := by
  have hshape : cellcount.pShapeAt (sHi 2 (k + 2)) 2 2 :=
      sHi_shape 2 (k + 2)
  have hsq : elim.sqAt
      (cellcount.evalPC (sHi 2 (k + 2)) BPair.unit 1 2) 2 :=
    cellcount.evalPC_sqAt hshape BPair.unit 1
  have hsplit := inertia.mkSplit_read 2
    (cellcount.evalPC (sHi 2 (k + 2)) BPair.unit 1 2) hsq
    (elim.matOne_symm (cellcount.evalPC_symAt (sHi 2 (k + 2)) 2 2
      BPair.unit 1 hshape (sHi_sym 2 (k + 2))))
  have hoff : (([hiD0 (k + 2), hiD1 (k + 2)] : List BPair).all
      (fun d => !(decide (d.oneValue BPair.unit)))) = true := by
    show (!(decide ((hiD0 (k + 2)).oneValue BPair.unit))
      && (!(decide ((hiD1 (k + 2)).oneValue BPair.unit)) && true))
      = true
    rw [decide_eq_false (hiD0_off k), decide_eq_false (hiD1_off k)]
    rfl
  have hone := inertia.oneSplit_read
    [hiD0 (k + 2), hiD1 (k + 2)]
    (cellcount.evalPC (sHi 2 (k + 2)) BPair.unit 1 2) hsq
    (hiBlock k) hoff
  refine ⟨hsplit, ?_⟩
  rw [inertia.rev_exchange
      (cellcount.evalPC (sHi 2 (k + 2)) BPair.unit 1 2) _ _
      hsplit hone,
    inertia.revAt_oneSplit [hiD0 (k + 2), hiD1 (k + 2)]]
  show 0 + (inertia.SBlock.one (hiD0 (k + 2))).rev
      + (inertia.SBlock.one (hiD1 (k + 2))).rev = 1
  rw [inertia.rev_one_le (hiD1_le k), inertia.rev_one_lt (hiD0_lt k)]

/-- The upper sweep's chain at order two. -/
private theorem chainHi2 (F : Nat) (hF : 2 ≤ F) :
    gappos.chainRead (sHi 2 F) 2 1 winFoot
      [(winTop, cellcount.diagCover winTop ⟨2, 1⟩ ⟨2, 1⟩ 1,
        (BPair.unit, 1),
        inertia.mkSplit 2 (cellcount.evalPC (sHi 2 F) BPair.unit 1 2))] := by
  match F, hF with
  | 0, hF => exact absurd hF (Nat.not_lt_zero 1)
  | 1, hF => exact absurd (Nat.lt_of_succ_lt_succ hF) (Nat.not_lt_zero 0)
  | k + 2, _ =>
    have hshape : cellcount.pShapeAt (sHi 2 (k + 2)) 2 2 :=
      sHi_shape 2 (k + 2)
    have hsub : cellcount.pShapeAt (cellcount.pdefl [0]
        (cellcount.compl [0] 2) (sHi 2 (k + 2))) 1 6 :=
      cellcount.pShape_pdefl _ 2 2 [0] (cellcount.compl [0] 2) hshape
        (Or.inl rfl)
    refine ⟨⟨⟨winFoot_le_top, rfl, winPlace0, hshape,
          sHi_sym 2 (k + 2)⟩,
        ?_,
        ⟨⟨winFoot_le_top, rfl, winPlace0, hsub, ?_⟩,
          ?_, rfl, ⟨hsub, rfl⟩⟩,
        ⟨hshape, rfl⟩⟩,
      winFoot_le_sample, winSample_le_top,
      ⟨hshape, (hiCount k).1, (hiCount k).2⟩, trivial⟩
    · exact stage.keepLower_congr
        (poly.oneValue_symm (hiHeadPoly 2 (k + 2) (Nat.succ_pos 1)))
        winFoot winTop ⟨2, 1⟩ ⟨2, 1⟩
        (keepLower_cn (2 * (k + 2)) (Nat.succ_le_succ (Nat.zero_le _)))
    · refine split.pSymAt_of _ 1 (fun i j hi hj => ?_)
      match i, j with
      | 0, 0 => exact poly.oneValue_refl _
      | 0, j + 1 => exact absurd (Nat.lt_of_succ_lt_succ hj) (Nat.not_lt_zero j)
      | i + 1, _ => exact absurd (Nat.lt_of_succ_lt_succ hi) (Nat.not_lt_zero i)
    · exact stage.keepUpper_congr (poly.oneValue_symm (hiHeadValue k))
        winFoot winTop ⟨2, 1⟩ ⟨2, 1⟩
        (keepUpper_qp (2 * (k + 2) * (2 * (k + 2)) * (2 * (k + 2)))
          (2 * (k + 2) * (2 * (k + 2)))
          (Nat.succ_le_succ (Nat.zero_le _))
          (cubeGap (2 * (k + 2) * (2 * (k + 2))) (2 * k)
            (Nat.succ_le_succ (Nat.zero_le _))))

/-! The lower sweep's structural reads at order three. -/

private theorem loOffR3 (cut : Nat) : ∀ k, k < ([1, 2] : List Nat).length →
    poly.unitTail
      (getAt [] (getAt [] (sLo 3 cut) (getAt 0 [1, 2] k)) 0) := by
  intro k hk
  match k with
  | 0 => exact sLo_offR 3 cut 1 (Nat.succ_pos 0)
           (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 1)))
  | 1 => exact sLo_offR 3 cut 2 (Nat.succ_pos 1) (Nat.le_refl 3)
  | k + 2 => exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hk)) (Nat.not_lt_zero k)

private theorem loLoop3 (k : Nat) : poly.oneValue
    (poly.mul (poly.mul [(⟨⟨4⟩, ⟨5⟩⟩ : BPair), BPair.unit, BPair.unit]
        [(⟨⟨4⟩, ⟨5⟩⟩ : BPair), BPair.unit, BPair.unit])
      [loD1 (4 * (k + 4)), BPair.unit, (⟨1, 2⟩ : BPair)])
    (qp (4 * k + 15) 1) := by
  refine poly.oneValue_trans (poly.mul_congr_left loSq3 _) ?_
  refine poly.oneValue_trans (poly.one_mul _) ?_
  exact ⟨rfl, rfl, rfl, trivial⟩

/-- The lower sweep's order-three deflation at its four entries:
the two loop places at the loop head's two-coefficient value, the couplings
exchanged and unit-tailed. -/
private theorem loLvl1 (k : Nat) :
    poly.oneValue
        (getAt [] (getAt [] (cellcount.pdefl [0] (cellcount.compl [0] 3)
          (sLo 3 (4 * (k + 4)))) 0) 0) (qp (4 * k + 15) 1)
      ∧ poly.oneValue
        (getAt [] (getAt [] (cellcount.pdefl [0] (cellcount.compl [0] 3)
          (sLo 3 (4 * (k + 4)))) 1) 1) (qp (4 * k + 15) 1)
      ∧ poly.oneValue
        (getAt [] (getAt [] (cellcount.pdefl [0] (cellcount.compl [0] 3)
          (sLo 3 (4 * (k + 4)))) 0) 1)
        (getAt [] (getAt [] (cellcount.pdefl [0] (cellcount.compl [0] 3)
          (sLo 3 (4 * (k + 4)))) 1) 0)
      ∧ poly.unitTail
        (getAt [] (getAt [] (cellcount.pdefl [0] (cellcount.compl [0] 3)
          (sLo 3 (4 * (k + 4)))) 1) 0) := by
  exact defl2v (sLo 3 (4 * (k + 4))) _ _ _ _ (qp (4 * k + 15) 1)
    (loOffR3 (4 * (k + 4)))
    (sLo_head 3 (4 * (k + 4)) (Nat.succ_pos 2))
    (sLo_loop 3 (4 * (k + 4)) 1 (Nat.succ_pos 0)
      (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 1))))
    (sLo_loop 3 (4 * (k + 4)) 2 (Nat.succ_pos 1) (Nat.le_refl 3))
    (sLo_coup 3 (4 * (k + 4)) 1 2
      (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 1))) (Nat.le_refl 3)
      (fun hh => Nat.noConfusion (Nat.succ.inj hh)))
    (sLo_coup 3 (4 * (k + 4)) 2 1 (Nat.le_refl 3)
      (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 1)))
      (fun hh => Nat.noConfusion (Nat.succ.inj hh)))
    (coupUT 2) (loLoop3 k) (loLoop3 k)

private theorem loBlock3 (k : Nat) :
    elim.matOneValue (cellcount.evalPC (sLo 3 (4 * (k + 4))) BPair.unit 1 2)
      (inertia.blockMat [.one (⟨⟨4⟩, ⟨5⟩⟩ : BPair),
        .one (loD1 (4 * (k + 4))), .one (loD1 (4 * (k + 4)))] 0) := by
  refine ⟨⟨evalHead _, ?_, ?_, trivial⟩, ⟨?_, evalHead _, ?_, trivial⟩,
    ⟨?_, ?_, evalHead _, trivial⟩, trivial⟩
  · exact BPair.oneValue_trans (evalHead _) (coupHead 2)
  · exact BPair.oneValue_trans (evalHead _) (coupHead 2)
  · exact BPair.oneValue_trans (evalHead _) (coupHead 2)
  · exact BPair.oneValue_trans (evalHead _) (coupHead 2)
  · exact BPair.oneValue_trans (evalHead _) (coupHead 2)
  · exact BPair.oneValue_trans (evalHead _) (coupHead 2)

private theorem loCount3 (k : Nat) :
    inertia.splitRead
        (cellcount.evalPC (sLo 3 (4 * (k + 4))) BPair.unit 1 2)
        (inertia.mkSplit 3
          (cellcount.evalPC (sLo 3 (4 * (k + 4))) BPair.unit 1 2))
      ∧ inertia.revAt (inertia.mkSplit 3
          (cellcount.evalPC (sLo 3 (4 * (k + 4))) BPair.unit 1 2)) = 1 := by
  have hshape : cellcount.pShapeAt (sLo 3 (4 * (k + 4))) 3 2 :=
      sLo_shape 3 (4 * (k + 4))
  have hoffD1 : ¬ (loD1 (4 * (k + 4))).oneValue BPair.unit := loD1_off (4 * k + 8)
  have hleD1 : BPair.unit ≤ loD1 (4 * (k + 4)) := loD1_le (4 * k + 8)
  have hsq : elim.sqAt
      (cellcount.evalPC (sLo 3 (4 * (k + 4))) BPair.unit 1 2) 3 :=
    cellcount.evalPC_sqAt hshape BPair.unit 1
  have hsplit := inertia.mkSplit_read 3
    (cellcount.evalPC (sLo 3 (4 * (k + 4))) BPair.unit 1 2) hsq
    (elim.matOne_symm (cellcount.evalPC_symAt (sLo 3 (4 * (k + 4))) 3 2
      BPair.unit 1 hshape (sLo_sym 3 (4 * (k + 4)))))
  have hoff : (([(⟨⟨4⟩, ⟨5⟩⟩ : BPair), loD1 (4 * (k + 4)),
      loD1 (4 * (k + 4))] : List BPair).all
      (fun d => !(decide (d.oneValue BPair.unit)))) = true := by
    show (!(decide ((⟨⟨4⟩, ⟨5⟩⟩ : BPair).oneValue BPair.unit))
      && (!(decide ((loD1 (4 * (k + 4))).oneValue BPair.unit))
        && (!(decide ((loD1 (4 * (k + 4))).oneValue BPair.unit)) && true)))
      = true
    rw [decide_eq_false hoffD1]
    rfl
  have hone := inertia.oneSplit_read
    [(⟨⟨4⟩, ⟨5⟩⟩ : BPair), loD1 (4 * (k + 4)), loD1 (4 * (k + 4))]
    (cellcount.evalPC (sLo 3 (4 * (k + 4))) BPair.unit 1 2) hsq
    (loBlock3 k) hoff
  refine ⟨hsplit, ?_⟩
  rw [inertia.rev_exchange
      (cellcount.evalPC (sLo 3 (4 * (k + 4))) BPair.unit 1 2) _ _
      hsplit hone,
    inertia.revAt_oneSplit [(⟨⟨4⟩, ⟨5⟩⟩ : BPair), loD1 (4 * (k + 4)),
      loD1 (4 * (k + 4))]]
  show 0 + (inertia.SBlock.one (⟨⟨4⟩, ⟨5⟩⟩ : BPair)).rev
      + (inertia.SBlock.one (loD1 (4 * (k + 4)))).rev
      + (inertia.SBlock.one (loD1 (4 * (k + 4)))).rev = 1
  rw [inertia.rev_one_le hleD1,
    inertia.rev_one_lt (show (⟨⟨4⟩, ⟨5⟩⟩ : BPair) < BPair.unit by
      decide +kernel)]

/-- The lower sweep's chain at order three, the deflation nest one
level deeper. -/
private theorem chainLo3 (F : Nat) (hF : 4 ≤ F) :
    gappos.chainRead (sLo 3 (4 * F)) 2 1 winFoot
      [(winTop, cellcount.diagCover winTop ⟨2, 1⟩ ⟨2, 1⟩ 2,
        (BPair.unit, 1),
        inertia.mkSplit 3 (cellcount.evalPC (sLo 3 (4 * F))
          BPair.unit 1 2))] := by
  match F, hF with
  | 0, hF => exact absurd hF (Nat.not_lt_zero 3)
  | 1, hF => exact absurd (Nat.lt_of_succ_lt_succ hF) (Nat.not_lt_zero 2)
  | 2, hF => exact absurd (Nat.lt_of_succ_lt_succ
      (Nat.lt_of_succ_lt_succ hF)) (Nat.not_lt_zero 1)
  | 3, hF => exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
      (Nat.lt_of_succ_lt_succ hF))) (Nat.not_lt_zero 0)
  | k + 4, _ =>
    have hshape : cellcount.pShapeAt (sLo 3 (4 * (k + 4))) 3 2 :=
      sLo_shape 3 (4 * (k + 4))
    have hcount := loCount3 k
    have h1 := loLvl1 k
    have hsub1 : cellcount.pShapeAt (cellcount.pdefl [0]
        (cellcount.compl [0] 3) (sLo 3 (4 * (k + 4)))) 2 6 :=
      cellcount.pShape_pdefl _ 3 2 [0] (cellcount.compl [0] 3) hshape
        (Or.inl rfl)
    refine ⟨⟨⟨winFoot_le_top, rfl, winPlace0, hshape,
          sLo_sym 3 (4 * (k + 4))⟩,
        ?_,
        subCover (cellcount.pdefl [0] (cellcount.compl [0] 3)
            (sLo 3 (4 * (k + 4))))
          (qp (4 * k + 15) 1) (qp3 (4 * k + 15) 1)
          hsub1 h1
          (keepUpper_qp (4 * k + 15) 1 (Nat.le_refl 1)
            (Nat.le_add_left 3 (4 * k + 12)))
          (cube_qp (4 * k + 15) 1)
          (keepUpper_qp3 (4 * k + 15) 1 (Nat.le_refl 1)
            (by rw [Nat.one_mul]
                exact coreIneq (4 * k + 15)
                  (Nat.le_trans (Nat.le_add_left 8 7 : (8 : Nat) ≤ 15)
                    (Nat.le_add_left 15 (4 * k))))),
        ⟨hshape, rfl⟩⟩,
      winFoot_le_sample, winSample_le_top,
      ⟨hshape, hcount.1, hcount.2⟩, trivial⟩
    · exact sLo_headKeep 3 (4 * (k + 4)) (Nat.succ_pos 2)

/-! The upper sweep's structural reads at order three. -/

private theorem hiOffR3 (F : Nat) : ∀ k, k < ([1, 2] : List Nat).length →
    poly.unitTail (getAt [] (getAt [] (sHi 3 F) (getAt 0 [1, 2] k)) 0) := by
  intro k hk
  match k with
  | 0 => exact sHi_offR 3 F 1 (Nat.succ_pos 0)
           (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 1)))
  | 1 => exact sHi_offR 3 F 2 (Nat.succ_pos 1) (Nat.le_refl 3)
  | k + 2 => exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hk)) (Nat.not_lt_zero k)


/-- The upper sweep's order-three deflation at its four entries: the
two loop places at the loop head's two-coefficient value, the couplings
exchanged and unit-tailed. -/
private theorem hiLvl1 (k : Nat) :
    poly.oneValue (getAt [] (getAt [] (cellcount.pdefl [0]
        (cellcount.compl [0] 3) (sHi 3 (k + 4))) 0) 0)
        (qp (2 * (k + 4) * (2 * (k + 4)) * (2 * (k + 4)))
          (2 * (k + 4) * (2 * (k + 4))))
      ∧ poly.oneValue (getAt [] (getAt [] (cellcount.pdefl [0]
        (cellcount.compl [0] 3) (sHi 3 (k + 4))) 1) 1)
        (qp (2 * (k + 4) * (2 * (k + 4)) * (2 * (k + 4)))
          (2 * (k + 4) * (2 * (k + 4))))
      ∧ poly.oneValue (getAt [] (getAt [] (cellcount.pdefl [0]
        (cellcount.compl [0] 3) (sHi 3 (k + 4))) 0) 1)
        (getAt [] (getAt [] (cellcount.pdefl [0]
          (cellcount.compl [0] 3) (sHi 3 (k + 4))) 1) 0)
      ∧ poly.unitTail (getAt [] (getAt [] (cellcount.pdefl [0]
        (cellcount.compl [0] 3) (sHi 3 (k + 4))) 1) 0) := by
  exact defl2v (sHi 3 (k + 4)) _ _ _ _
    (qp (2 * (k + 4) * (2 * (k + 4)) * (2 * (k + 4)))
      (2 * (k + 4) * (2 * (k + 4))))
    (hiOffR3 (k + 4))
    (sHi_head 3 (k + 4) (Nat.succ_pos 2))
    (sHi_loop 3 (k + 4) 1 (Nat.succ_pos 0)
      (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 1))))
    (sHi_loop 3 (k + 4) 2 (Nat.succ_pos 1) (Nat.le_refl 3))
    (sHi_coup 3 (k + 4) 1 2
      (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 1))) (Nat.le_refl 3)
      (fun hh => Nat.noConfusion (Nat.succ.inj hh)))
    (sHi_coup 3 (k + 4) 2 1 (Nat.le_refl 3)
      (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 1)))
      (fun hh => Nat.noConfusion (Nat.succ.inj hh)))
    (coupUT (ground.posOfSucc (2 * (k + 4))))
    (hiLoop (k + 2)) (hiLoop (k + 2))

private theorem hiBlock3 (k : Nat) :
    elim.matOneValue (cellcount.evalPC (sHi 3 (k + 4)) BPair.unit 1 2)
      (inertia.blockMat [.one (hiD0 (k + 4)), .one (hiD1 (k + 4)),
        .one (hiD1 (k + 4))] 0) := by
  refine ⟨⟨evalHead _, ?_, ?_, trivial⟩, ⟨?_, evalHead _, ?_, trivial⟩,
    ⟨?_, ?_, evalHead _, trivial⟩, trivial⟩
  · exact BPair.oneValue_trans (evalHead _) (coupHead (ground.posOfSucc (2 * (k + 4))))
  · exact BPair.oneValue_trans (evalHead _) (coupHead (ground.posOfSucc (2 * (k + 4))))
  · exact BPair.oneValue_trans (evalHead _) (coupHead (ground.posOfSucc (2 * (k + 4))))
  · exact BPair.oneValue_trans (evalHead _) (coupHead (ground.posOfSucc (2 * (k + 4))))
  · exact BPair.oneValue_trans (evalHead _) (coupHead (ground.posOfSucc (2 * (k + 4))))
  · exact BPair.oneValue_trans (evalHead _) (coupHead (ground.posOfSucc (2 * (k + 4))))

private theorem hiCount3 (k : Nat) :
    inertia.splitRead
        (cellcount.evalPC (sHi 3 (k + 4)) BPair.unit 1 2)
        (inertia.mkSplit 3
          (cellcount.evalPC (sHi 3 (k + 4)) BPair.unit 1 2))
      ∧ inertia.revAt (inertia.mkSplit 3
          (cellcount.evalPC (sHi 3 (k + 4)) BPair.unit 1 2)) = 1 := by
  have hshape : cellcount.pShapeAt (sHi 3 (k + 4)) 3 2 :=
      sHi_shape 3 (k + 4)
  have hsq : elim.sqAt
      (cellcount.evalPC (sHi 3 (k + 4)) BPair.unit 1 2) 3 :=
    cellcount.evalPC_sqAt hshape BPair.unit 1
  have hsplit := inertia.mkSplit_read 3
    (cellcount.evalPC (sHi 3 (k + 4)) BPair.unit 1 2) hsq
    (elim.matOne_symm (cellcount.evalPC_symAt (sHi 3 (k + 4)) 3 2
      BPair.unit 1 hshape (sHi_sym 3 (k + 4))))
  have hoff : (([hiD0 (k + 4), hiD1 (k + 4), hiD1 (k + 4)] : List BPair).all
      (fun d => !(decide (d.oneValue BPair.unit)))) = true := by
    show (!(decide ((hiD0 (k + 4)).oneValue BPair.unit))
      && (!(decide ((hiD1 (k + 4)).oneValue BPair.unit))
        && (!(decide ((hiD1 (k + 4)).oneValue BPair.unit)) && true)))
      = true
    rw [decide_eq_false (hiD0_off (k + 2)), decide_eq_false (hiD1_off (k + 2))]
    rfl
  have hone := inertia.oneSplit_read
    [hiD0 (k + 4), hiD1 (k + 4), hiD1 (k + 4)]
    (cellcount.evalPC (sHi 3 (k + 4)) BPair.unit 1 2) hsq
    (hiBlock3 k) hoff
  refine ⟨hsplit, ?_⟩
  rw [inertia.rev_exchange
      (cellcount.evalPC (sHi 3 (k + 4)) BPair.unit 1 2) _ _
      hsplit hone,
    inertia.revAt_oneSplit [hiD0 (k + 4), hiD1 (k + 4), hiD1 (k + 4)]]
  show 0 + (inertia.SBlock.one (hiD0 (k + 4))).rev
      + (inertia.SBlock.one (hiD1 (k + 4))).rev
      + (inertia.SBlock.one (hiD1 (k + 4))).rev = 1
  rw [inertia.rev_one_le (hiD1_le (k + 2)), inertia.rev_one_lt (hiD0_lt (k + 2))]

/-- The upper sweep's chain at order three, the deflation nest one
level deeper. -/
private theorem chainHi3 (F : Nat) (hF : 4 ≤ F) :
    gappos.chainRead (sHi 3 F) 2 1 winFoot
      [(winTop, cellcount.diagCover winTop ⟨2, 1⟩ ⟨2, 1⟩ 2,
        (BPair.unit, 1),
        inertia.mkSplit 3 (cellcount.evalPC (sHi 3 F) BPair.unit 1 2))] := by
  match F, hF with
  | 0, hF => exact absurd hF (Nat.not_lt_zero 3)
  | 1, hF => exact absurd (Nat.lt_of_succ_lt_succ hF) (Nat.not_lt_zero 2)
  | 2, hF => exact absurd (Nat.lt_of_succ_lt_succ
      (Nat.lt_of_succ_lt_succ hF)) (Nat.not_lt_zero 1)
  | 3, hF => exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
      (Nat.lt_of_succ_lt_succ hF))) (Nat.not_lt_zero 0)
  | k + 4, _ =>
    have hshape : cellcount.pShapeAt (sHi 3 (k + 4)) 3 2 :=
      sHi_shape 3 (k + 4)
    have hcount := hiCount3 k
    have h1 := hiLvl1 k
    have hsub1 : cellcount.pShapeAt (cellcount.pdefl [0]
        (cellcount.compl [0] 3) (sHi 3 (k + 4))) 2 6 :=
      cellcount.pShape_pdefl _ 3 2 [0] (cellcount.compl [0] 3) hshape
        (Or.inl rfl)
    refine ⟨⟨⟨winFoot_le_top, rfl, winPlace0, hshape,
          sHi_sym 3 (k + 4)⟩,
        ?_,
        subCover (cellcount.pdefl [0] (cellcount.compl [0] 3)
            (sHi 3 (k + 4)))
          (qp (2 * (k + 4) * (2 * (k + 4)) * (2 * (k + 4)))
            (2 * (k + 4) * (2 * (k + 4))))
          (qp3 (2 * (k + 4) * (2 * (k + 4)) * (2 * (k + 4)))
            (2 * (k + 4) * (2 * (k + 4))))
          hsub1 h1
          (keepUpper_qp (2 * (k + 4) * (2 * (k + 4)) * (2 * (k + 4)))
            (2 * (k + 4) * (2 * (k + 4)))
            (Nat.succ_le_succ (Nat.zero_le _))
            (cubeGap (2 * (k + 4) * (2 * (k + 4))) (2 * k + 4)
              (Nat.succ_le_succ (Nat.zero_le _))))
          (cube_qp (2 * (k + 4) * (2 * (k + 4)) * (2 * (k + 4)))
            (2 * (k + 4) * (2 * (k + 4))))
          (keepUpper_qp3 (2 * (k + 4) * (2 * (k + 4)) * (2 * (k + 4)))
            (2 * (k + 4) * (2 * (k + 4)))
            (Nat.succ_le_succ (Nat.zero_le _))
            (bigIneq (2 * (k + 4)) (Nat.le_add_left 8 (2 * k)))),
        ⟨hshape, rfl⟩⟩,
      winFoot_le_sample, winSample_le_top,
      ⟨hshape, hcount.1, hcount.2⟩, trivial⟩
    · exact stage.keepLower_congr
        (poly.oneValue_symm (hiHeadPoly 3 (k + 4) (Nat.succ_pos 2)))
        winFoot winTop ⟨2, 1⟩ ⟨2, 1⟩
        (keepLower_cn (2 * (k + 4)) (Nat.succ_le_succ (Nat.zero_le _)))

/-! The floors' occupancy weakenings, read at the tie's hypothesis and
at the order-two chains' own. -/

/-- Clause (i)'s floor-window instance at every member of the
classification: the series and the diagonal-window fixed members through the parametric window sweeps
at the member's floor numerator — the two level lines' chains at the
window's order with the tie at the committed member pair — and `D₄`'s
four-loop window and `E₈`'s coupled window decided by kernel
reduction. -/
theorem clauseI_all : ∀ m : Member, clauseI m
  | .A 0 => ⟨chainLo2 3 (by decide +kernel), chainHi2 3 (by decide +kernel),
      tieRead 3 (by decide +kernel)⟩
  | .A (g + 1) =>
      ⟨chainLo3 (winFloorN (.A (g + 1))) (floorA_ge g),
       chainHi3 (winFloorN (.A (g + 1))) (floorA_ge g),
       tieRead (winFloorN (.A (g + 1)))
         (Nat.le_of_succ_le (Nat.le_of_succ_le (Nat.le_of_succ_le
           (floorA_ge g))))⟩
  | .B g =>
      ⟨chainLo2 (winFloorN (.B g)) (floorB_ge g),
       chainHi2 (winFloorN (.B g)) (floorB_ge g),
       tieRead (winFloorN (.B g)) (Nat.le_of_succ_le (floorB_ge g))⟩
  | .C g =>
      ⟨chainLo2 (winFloorN (.C g)) (floorC_ge g),
       chainHi2 (winFloorN (.C g)) (floorC_ge g),
       tieRead (winFloorN (.C g)) (Nat.le_of_succ_le (floorC_ge g))⟩
  | .D 0 => ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
  | .D (g + 1) =>
      ⟨chainLo2 (winFloorN (.D (g + 1))) (floorD_ge g),
       chainHi2 (winFloorN (.D (g + 1))) (floorD_ge g),
       tieRead (winFloorN (.D (g + 1))) (Nat.le_of_succ_le (floorD_ge g))⟩
  | .G2 => ⟨chainLo2 24 (by decide +kernel), chainHi2 24 (by decide +kernel),
      tieRead 24 (by decide +kernel)⟩
  | .F4 => ⟨chainLo2 24 (by decide +kernel), chainHi2 24 (by decide +kernel),
      tieRead 24 (by decide +kernel)⟩
  | .E6 => ⟨chainLo3 104 (by decide +kernel), chainHi3 104 (by decide +kernel),
      tieRead 104 (by decide +kernel)⟩
  | .E7 => ⟨chainLo2 114 (by decide +kernel), chainHi2 114 (by decide +kernel),
      tieRead 114 (by decide +kernel)⟩
  | .E8 => ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩


/-- The member's tail scale, `[1 : 524288(r+1)²]`: the reference
certificate's ceiling `[1 : 524288]` at the residue's successor
squared (`lem:cornerpivot`(vi)). -/
def cornerScaleD (r : Nat) : Pos := posOfSucc (524288 * (r + 1) * (r + 1) - 1)

private theorem cornerScaleD_val (r : Nat) :
    posVal (cornerScaleD r) = 524288 * (r + 1) * (r + 1) :=
  ground.subAdd (Nat.le_trans (by decide : 1 ≤ 524288)
    (Nat.le_trans (Nat.le_mul_of_pos_right 524288 (Nat.succ_pos r))
      (Nat.le_mul_of_pos_right _ (Nat.succ_pos r))))

/-- The endpoint key's comparison at the member's scale
(`lem:cornerpivot`(v)'s `40N⁴η² ≥ 363(r+1)`). -/
def keyRead (r N : Nat) : Prop :=
  363 * (r + 1) * posVal (cornerScaleD r) ^ 2 ≤ 40 * N ^ 4 * posVal (1 : Pos) ^ 2

instance (r N : Nat) : Decidable (keyRead r N) := inferInstanceAs (Decidable (_ ≤ _))

/-- The member's endpoint key, the least natural beyond one at the
key's comparison, the search bounded at the comparison's stated
witness `2000(r+1)²` (`lem:cornerpivot`(v),(vi)). -/
def cornerKey (r : Nat) : Nat :=
  ground.firstAt (keyRead r) 2 (2000 * (r + 1) * (r + 1))

private theorem kyA (r1 : Nat) :
    363 * r1 * ((524288 * r1 * r1) * (524288 * r1 * r1))
      = r1 * r1 * r1 * r1 * r1 * 99780680220672 :=
  ground.monEq [r1]
    (Mon.mul (Mon.mul (Mon.cst 363) (Mon.var 0)) (Mon.mul (Mon.mul (Mon.mul (Mon.cst 524288) (Mon.var 0)) (Mon.var 0)) (Mon.mul (Mon.mul (Mon.cst 524288) (Mon.var 0)) (Mon.var 0))))
    (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 0)) (Mon.var 0)) (Mon.var 0)) (Mon.cst 99780680220672))
    (by decide +kernel) (by decide +kernel)
private theorem kyB (r1 : Nat) :
    40 * ((2000 * r1 * r1) * (2000 * r1 * r1) * (2000 * r1 * r1) * (2000 * r1 * r1)) * 1
      = r1 * r1 * r1 * r1 * r1 * (r1 * r1 * r1 * 640000000000000) :=
  ground.monEq [r1]
    (Mon.mul (Mon.mul (Mon.cst 40) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2000) (Mon.var 0)) (Mon.var 0)) (Mon.mul (Mon.mul (Mon.cst 2000) (Mon.var 0)) (Mon.var 0))) (Mon.mul (Mon.mul (Mon.cst 2000) (Mon.var 0)) (Mon.var 0))) (Mon.mul (Mon.mul (Mon.cst 2000) (Mon.var 0)) (Mon.var 0)))) (Mon.cst 1))
    (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 0)) (Mon.var 0)) (Mon.var 0)) (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 0)) (Mon.cst 640000000000000)))
    (by decide +kernel) (by decide +kernel)
private theorem kyC (r : Nat) :
    40 * (20 * r * (20 * r) * (20 * r) * (20 * r)) * 1
      = r * r * r * r * 6400000 :=
  ground.monEq [r]
    (Mon.mul (Mon.mul (Mon.cst 40) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 20) (Mon.var 0)) (Mon.mul (Mon.cst 20) (Mon.var 0))) (Mon.mul (Mon.cst 20) (Mon.var 0))) (Mon.mul (Mon.cst 20) (Mon.var 0)))) (Mon.cst 1))
    (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 0)) (Mon.var 0)) (Mon.cst 6400000))
    (by decide +kernel) (by decide +kernel)

/-- The key's comparison at the stated witness `2000(r+1)²`, the
search's bound (`lem:cornerpivot`(vi)). -/
private theorem key_budget (r : Nat) : keyRead r (2 + 2000 * (r + 1) * (r + 1)) := by
  show 363 * (r + 1) * posVal (cornerScaleD r) ^ 2
    ≤ 40 * (2 + 2000 * (r + 1) * (r + 1)) ^ 4 * posVal (1 : Pos) ^ 2
  rw [cornerScaleD_val r, sqRead]
  refine Nat.le_trans ?_ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 40
    (Nat.pow_le_pow_left (Nat.le_add_left _ 2) 4)))
  show 363 * (r + 1) * (524288 * (r + 1) * (r + 1) * (524288 * (r + 1) * (r + 1)))
    ≤ 40 * (2000 * (r + 1) * (r + 1)) ^ 4 * 1 ^ 2
  rw [pow4Read, Nat.one_pow]
  have h1 : 1 ≤ r + 1 := Nat.succ_pos r
  generalize r + 1 = r1 at h1 ⊢
  rw [kyA, kyB]
  refine Nat.mul_le_mul_left _ ?_
  refine Nat.le_trans (by decide +kernel : 99780680220672 ≤ 1 * 640000000000000) ?_
  exact Nat.mul_le_mul_right _ (Nat.mul_pos (Nat.mul_pos h1 h1) h1)

private theorem key_hit (r : Nat) : keyRead r (cornerKey r) :=
  ground.firstAt_hit (keyRead r) (2000 * (r + 1) * (r + 1)) 2 (key_budget r)

private theorem key_ge2 (r : Nat) : 2 ≤ cornerKey r :=
  ground.firstAt_ge (keyRead r) (2000 * (r + 1) * (r + 1)) 2

/-- The member's endpoint key reads `lem:cornerpivot`(v)'s key at
the member's scale: the depth beyond one, the comparison, and the
leastness. -/
private theorem key_end (r : Nat) :
    cornerpivot.endRead (posVal 1) (posVal (cornerScaleD r)) r (cornerKey r) := by
  refine ⟨key_ge2 r, key_hit r, ?_⟩
  match Nat.lt_or_ge (cornerKey r) 3 with
  | Or.inl h3 => exact Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ h3) (key_ge2 r))
  | Or.inr h3 =>
    refine Or.inr (ground.firstAt_below (keyRead r) (2000 * (r + 1) * (r + 1)) 2
      (cornerKey r - 1) ?_ ?_)
    · exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_succ_self 2)
        (show 3 ≤ cornerKey r - 1 + 1 from
          (ground.subAdd (Nat.le_trans (by decide : 1 ≤ 3) h3)).symm ▸ h3))
    · exact Nat.sub_lt (Nat.lt_of_lt_of_le (by decide) h3) (by decide)

/-- A depth whose fourth power sits under the key's comparison lies
below the key. -/
private theorem key_lb (r c : Nat)
    (hc : 40 * c ^ 4 * posVal (1 : Pos) ^ 2
      < 363 * (r + 1) * posVal (cornerScaleD r) ^ 2) :
    c < cornerKey r :=
  Nat.lt_of_not_le (fun hle =>
    Nat.lt_irrefl _ (Nat.lt_of_le_of_lt
      (Nat.le_trans (key_hit r) (Nat.mul_le_mul_right _
        (Nat.mul_le_mul_left 40 (Nat.pow_le_pow_left hle 4)))) hc))

/-- The key sits at or beyond `1652` at every residue at or beyond
two: the member's key at or beyond the ceiling's own, `1654` at the
residue two (`lem:cornerpivot`(vi)). -/
private theorem key_ge1652 (r : Nat) (hr : 2 ≤ r) : 1652 ≤ cornerKey r := by
  refine key_lb r 1651 ?_
  rw [cornerScaleD_val r, show posVal (1 : Pos) = 1 from rfl, Nat.one_pow,
    sqRead (524288 * (r + 1) * (r + 1)), kyA]
  have h3 : 3 ≤ r + 1 := Nat.succ_le_succ hr
  refine Nat.lt_of_lt_of_le (by decide +kernel : 40 * 1651 ^ 4 * 1
    < 3 * 3 * 3 * 3 * 3 * 99780680220672) ?_
  exact Nat.mul_le_mul_right _
    (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h3 h3) h3) h3) h3)

/-- The key clears twenty residues (`lem:cornerpivot`(vi)'s
`20r ≤ N`). -/
private theorem key_ge20 (r : Nat) : 20 * r ≤ cornerKey r := by
  refine Nat.le_of_lt (key_lb r (20 * r) ?_)
  rw [cornerScaleD_val r, show posVal (1 : Pos) = 1 from rfl, Nat.one_pow,
    pow4Read (20 * r), sqRead (524288 * (r + 1) * (r + 1)), kyC, kyA]
  have hr1 : r ≤ r + 1 := Nat.le_succ r
  refine Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 6400000
    (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hr1 hr1) hr1) hr1)) ?_
  refine Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 6400000
    (Nat.le_mul_of_pos_right _ (Nat.succ_pos r))) ?_
  exact Nat.mul_lt_mul_of_pos_left (by decide +kernel)
    (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos
      (Nat.mul_pos (Nat.succ_pos r) (Nat.succ_pos r)) (Nat.succ_pos r))
      (Nat.succ_pos r)) (Nat.succ_pos r))

/-- The key sits at or beyond `1495` at the residue one, the
ceiling's own read there (`lem:cornerpivot`(vi)). -/
private theorem key_ge1495 : 1495 ≤ cornerKey 1 :=
  key_lb 1 1494 (by decide +kernel)

/-- The key's leastness at a key beyond two: the predecessor refuses
the comparison. -/
private theorem key_least (r : Nat) (h3 : 3 ≤ cornerKey r) :
    40 * (cornerKey r - 1) ^ 4 * posVal (1 : Pos) ^ 2
      < 363 * (r + 1) * posVal (cornerScaleD r) ^ 2 :=
  match (key_end r).2.2 with
  | Or.inl h2 => absurd (h2 ▸ h3) (by decide)
  | Or.inr hn => Nat.lt_of_not_le hn

/-- The transported cell at a member of residue at or beyond two:
the reference certificate at the member's scale and key, the tied
scale under the ceiling at the key beyond `1652`, and the cut member
`[6 : 5]` under the transported rate (`cornerpivot.resRate`). -/
private theorem memberT (r : Nat) (hr : 2 ≤ r) :
    corner.cellReadT r cornerpivot.disconjC 1 (cornerScaleD r) (cornerKey r) 6 5 1 := by
  have hN := key_ge1652 r hr
  refine ⟨hr, cornerpivot.disconjC_read, ?_, key_end r, rfl, Nat.le_refl 1, ?_⟩
  · show BPair.ofNat 26 * BPair.ofNat 524288
      ≤ BPair.ofNat 1 * BPair.ofPos (cornerpivot.tieScaleD (cornerKey r))
    rw [BPair.ofPos_val (cornerpivot.tieScaleD (cornerKey r)),
      cornerpivot.tieScaleD_val _ (Nat.le_trans (by decide : 1 ≤ 1652) hN)]
    refine ground.leB_congr (BPair.ofNat_mul 26 524288) (BPair.ofNat_mul 1 _)
      (ground.leB_ofNat ?_)
    exact Nat.le_trans (by decide +kernel : 26 * 524288 ≤ 1 * (5 * 1652 * 1652))
      (Nat.mul_le_mul_left 1 (Nat.mul_le_mul (Nat.mul_le_mul_left 5 hN) hN))
  · rw [cornerpivot.disconjC_qcN, cornerpivot.disconjC_qcD]
    exact cornerpivot.resRate (posVal 1) (posVal (cornerScaleD r)) r (cornerKey r) hN
      (key_ge20 r) (key_least r (Nat.le_trans (by decide : 3 ≤ 1652) hN))

/-- The residue-one cell at the `A`-series' first member: the
reference certificate at the member's scale under its ceiling and
the key from `1495`, and the cut member `[41 : 40]` under the stated
rate (`cornerpivot.oneRate`). -/
private theorem memberS :
    corner.cellReadS cornerpivot.disconjC 1 (cornerScaleD 1) (cornerKey 1) 41 40 1 := by
  refine ⟨cornerpivot.disconjC_read, by decide +kernel, key_end 1, rfl, Nat.le_refl 1, ?_⟩
  rw [cornerpivot.disconjC_qcN, cornerpivot.disconjC_qcD]
  exact cornerpivot.oneRate (posVal 1) (posVal (cornerScaleD 1)) (cornerKey 1) key_ge1495
    (key_least 1 (Nat.le_trans (by decide : 3 ≤ 1495) key_ge1495)) (key_hit 1)

/-- The member's residue-one corner cell: `lem:corner`'s cell datum
at the member's derived residue, its tail scale and its endpoint
key, the cut member `[41 : 40]` at the gap one. -/
def cellS (m : Member) : Prop :=
  corner.cellReadS cornerpivot.disconjC 1 (cornerScaleD (residue m))
    (cornerKey (residue m)) 41 40 1

instance (m : Member) : Decidable (cellS m) :=
  inferInstanceAs (Decidable (corner.cellReadS _ _ _ _ _ _ _))

/-- The member's transported corner cell: `lem:corner`'s cell datum
at the member's derived residue, its tail scale and its endpoint
key, the cut member `[6 : 5]` at the gap one. -/
def cellT (m : Member) : Prop :=
  corner.cellReadT (residue m) cornerpivot.disconjC 1 (cornerScaleD (residue m))
    (cornerKey (residue m)) 6 5 1

instance (m : Member) : Decidable (cellT m) :=
  inferInstanceAs (Decidable (corner.cellReadT _ _ _ _ _ _ _ _))

/-- Clause (iii)'s corner cell at a member: `lem:corner`'s cell-floor
datum at the member's derived residue, the one certificate
transported across the residues at the key's bracket
(`lem:cornerpivot`(vi)) — the residue-one cell at the cut member
`[41 : 40]` at the `A`-series' first member and the transported cell
at `[6 : 5]` at every further member — whose reads are the flat
window at the member line (`corner.cut_flat_T`, `corner.cut_flat_S`),
the floor positive by its shape (`corner.floor_pos`) and the chain's
ground at or below the line (`corner.ground_below_line`). -/
def clauseIII : Member → Prop
  | .A 0 => cellS (.A 0)
  | .A (g + 1) => cellT (.A (g + 1))
  | .B g => cellT (.B g)
  | .C g => cellT (.C g)
  | .D g => cellT (.D g)
  | .G2 => cellT .G2
  | .F4 => cellT .F4
  | .E6 => cellT .E6
  | .E7 => cellT .E7
  | .E8 => cellT .E8

instance : (m : Member) → Decidable (clauseIII m)
  | .A 0 => inferInstanceAs (Decidable (cellS (.A 0)))
  | .A (g + 1) => inferInstanceAs (Decidable (cellT (.A (g + 1))))
  | .B g => inferInstanceAs (Decidable (cellT (.B g)))
  | .C g => inferInstanceAs (Decidable (cellT (.C g)))
  | .D g => inferInstanceAs (Decidable (cellT (.D g)))
  | .G2 => inferInstanceAs (Decidable (cellT .G2))
  | .F4 => inferInstanceAs (Decidable (cellT .F4))
  | .E6 => inferInstanceAs (Decidable (cellT .E6))
  | .E7 => inferInstanceAs (Decidable (cellT .E7))
  | .E8 => inferInstanceAs (Decidable (cellT .E8))

/-- Clause (iii)'s corner cell at every member of the classification:
the `A`-series' first member at the residue-one cell, and every
further member at the transported cell through its derived residue
at or beyond two — the series through their residue reads and the
fixed members' residues decided by kernel reduction. -/
theorem clauseIII_all : ∀ m : Member, clauseIII m
  | .A 0 => by
      show corner.cellReadS cornerpivot.disconjC 1 (cornerScaleD (residue (.A 0)))
        (cornerKey (residue (.A 0))) 41 40 1
      rw [show residue (.A 0) = 1 from gentable.residue_tableA 1]
      exact memberS
  | .A (g + 1) => memberT _ (by
      show 2 ≤ gentable.residue (gentable.tableA (g + 1 + 1))
      rw [gentable.residue_tableA]
      exact Nat.le_add_left 2 g)
  | .B g => memberT _ (by
      show 2 ≤ gentable.residue (sertables.tableB (g + 2))
      rw [sertables.residue_tableB g]
      exact Nat.mul_le_mul_left 2 (Nat.le_add_left 1 g))
  | .C g => memberT _ (by
      show 2 ≤ gentable.residue (sertables.tableC (g + 3))
      rw [sertables.residue_tableC g]
      exact Nat.le_trans (by decide) (Nat.le_add_left 3 g))
  | .D g => memberT _ (by
      show 2 ≤ gentable.residue (sertables.tableD (g + 4))
      rw [sertables.residue_tableD g]
      exact Nat.le_trans (by decide) (Nat.le_add_left 5 (2 * g)))
  | .G2 => memberT _ (by decide +kernel)
  | .F4 => memberT _ (by decide +kernel)
  | .E6 => memberT _ (by decide +kernel)
  | .E7 => memberT _ (by decide +kernel)
  | .E8 => memberT _ (by decide +kernel)

end main
