import MassGap.Sertables
import MassGap.Inertia
/-!
The check module for `con:sertables`: the batteries re-read the
member tables by kernel `decide`, every read family at all twelve
committed members (`B_{2,3,4}`, `C_{3,4}`, `D_{4,5}`, `G_2`,
`F_4`, `E_6`, `E_7`, `E_8`) — the residue folds with their naming
identities (`r = 2ℓ - 2`, `ℓ`, `2ℓ - 3`, and `3, 8, 11, 17, 29`);
the positive counts (`ℓ²`, `ℓ²`, `ℓ² - ℓ`, and
`6, 24, 36, 63, 120`); the highest root's form read; the form's
simple symmetry; the shape and occupancy reads with the root
fold's coroot reads at the direct-fold members (the series and
`G_2`); and the adjugate rows' coroot witnesses with the θ-fold
rows at the five fold keys.  The `F_4` member closes its
descent-built positive list through the family read — the stored
fold list against the displayed coordinate family, the round trip
with the per-fold key counts and the coroot reads at one forcing,
the occupancy and shape clauses riding the round trip — and the
`E` members close their committed literals twice: the family read
at the literal, and one certifying equation per member reading the
literal as the descent's own output, the `E_8` pair the module's
heavy pins at their own heartbeat allowance, the 120-member
family's descent at the shared Gram.
The defining-table batteries read the invariant counts at the
dual pair's line; the triple displays read at the generating
tables in `MassGapChecks.Memtable`.  Budget: the pair-partition counts sit beyond the kernel
allowance — `invCountB 2 2` at 190 s user by kernel decide,
`invCountC 3 2` refusing the 4000000-heartbeat allowance at
318 s user, `invCountD 4 2` beyond both — each value `3` at the
compiled evaluator, the stacked matrix's elimination the whole
cost.
-/

namespace sertables
set_option maxHeartbeats 4000000

open ground gentable

/-! The `B_2` member data the member-tier batteries state — the
table, the vacant content, the one-hot top, the `ρ`-orbit with its
dominance witnesses, the `ω_1`-block's multiplicity family, and the
`λ+ρ`-orbit — one stated copy at `con:sertables`' first series
member, the member-tier check modules' shared data. -/


def tB2 : gentable.Table := tableB 2

def zeroV : List BPair := List.replicate 2 BPair.unit

def lamB2 : List BPair := [BPair.ofNat 1, BPair.unit]

def wB2 : List (List BPair × Bool) :=
  [([(BPair.ofNat 1), (BPair.ofNat 1)], false),
   ([(BPair.ofNat 1).swap, (BPair.ofNat 3)], true),
   ([(BPair.ofNat 2), (BPair.ofNat 1).swap], true),
   ([(BPair.ofNat 2).swap, (BPair.ofNat 3)], false),
   ([(BPair.ofNat 1), (BPair.ofNat 3).swap], true),
   ([(BPair.ofNat 1).swap, (BPair.ofNat 1).swap], false),
   ([(BPair.ofNat 2).swap, (BPair.ofNat 1)], true),
   ([(BPair.ofNat 2), (BPair.ofNat 3).swap], false)]

def witsB2 : List (List Nat) :=
  [[0, 0], [1, 0], [0, 1], [2, 1], [2, 4], [3, 4], [3, 3], [1, 3]]

def mB2 : List (List BPair) :=
  [[BPair.ofNat 1, BPair.unit],
   [(BPair.ofNat 1).swap, BPair.ofNat 2],
   [BPair.unit, BPair.unit],
   [BPair.ofNat 1, (BPair.ofNat 2).swap],
   [(BPair.ofNat 1).swap, BPair.unit]]

def mwitsB2 : List (List Nat) :=
  [[0, 0], [1, 0], [1, 1], [1, 2], [2, 2]]

def wpB2 : List (List BPair × Bool) :=
  [([(BPair.ofNat 2), (BPair.ofNat 1)], false),
   ([(BPair.ofNat 2).swap, (BPair.ofNat 5)], true),
   ([(BPair.ofNat 3), (BPair.ofNat 1).swap], true),
   ([(BPair.ofNat 3), (BPair.ofNat 5).swap], false),
   ([(BPair.ofNat 3).swap, (BPair.ofNat 5)], false),
   ([(BPair.ofNat 3).swap, (BPair.ofNat 1)], true),
   ([(BPair.ofNat 2), (BPair.ofNat 5).swap], true),
   ([(BPair.ofNat 2).swap, (BPair.ofNat 1).swap], false)]

def wpwitsB2 : List (List Nat) :=
  [[0, 0], [2, 0], [0, 1], [2, 5], [3, 1], [5, 5], [3, 6], [5, 6]]


/-! The fixed members' residue folds at their displayed values,
and the naming identity at every committed member. -/

theorem pin1 : residue tableG2 = 3 := by decide +kernel
theorem pin2 : residue tableF4 = 8 := by decide +kernel
theorem pin3 : residue tableE6 = 11 := by decide +kernel
theorem pin4 : residue tableE7 = 17 := by decide +kernel
theorem pin5 : residue tableE8 = 29 := by decide +kernel

theorem pin6 : residueRead (tableB 2) := by decide +kernel
theorem pin7 : residueRead (tableB 3) := by decide +kernel
theorem pin8 : residueRead (tableB 4) := by decide +kernel
theorem pin9 : residueRead (tableC 3) := by decide +kernel
theorem pin10 : residueRead (tableC 4) := by decide +kernel
theorem pin11 : residueRead (tableD 4) := by decide +kernel
theorem pin12 : residueRead (tableD 5) := by decide +kernel
theorem pin13 : residueRead tableG2 := by decide +kernel
theorem pin14 : residueRead tableF4 := by decide +kernel
theorem pin15 : residueRead tableE6 := by decide +kernel
theorem pin16 : residueRead tableE7 := by decide +kernel
theorem pin17 : residueRead tableE8 := by decide +kernel

/-! The series' residue values and support-key refusals at the
theorem routes: coherence pairs at committed ranks and reads at
ranks no decide touches. -/

theorem pin18 : residue (tableB 9) = 16 := by decide +kernel
theorem pin19 : residue (tableB 9) = 16 := residue_tableB 7
theorem pin20 : residue (tableC 9) = 9 := by decide +kernel
theorem pin21 : residue (tableC 9) = 9 := residue_tableC 6
theorem pin22 : residue (tableD 9) = 15 := by decide +kernel
theorem pin23 : residue (tableD 9) = 15 := residue_tableD 5
theorem pin24 : residue (tableB 30) = 58 := residue_tableB 28
theorem pin25 : residue (tableC 30) = 30 := residue_tableC 27
theorem pin26 : residue (tableD 30) = 57 := residue_tableD 26

theorem pin27 : ¬ (corootAt (tableB 3) (tableB 3).thetaFold 1).oneValue
    BPair.unit := by decide +kernel
theorem pin28 : ¬ (corootAt (tableB 3) (tableB 3).thetaFold 1).oneValue
    BPair.unit := corootB_off 1
theorem pin29 : ¬ (corootAt (tableC 4) (tableC 4).thetaFold 0).oneValue
    BPair.unit := by decide +kernel
theorem pin30 : ¬ (corootAt (tableC 4) (tableC 4).thetaFold 0).oneValue
    BPair.unit := corootC_off 1
theorem pin31 : ¬ (corootAt (tableD 5) (tableD 5).thetaFold 1).oneValue
    BPair.unit := by decide +kernel
theorem pin32 : ¬ (corootAt (tableD 5) (tableD 5).thetaFold 1).oneValue
    BPair.unit := corootD_off 1

/-! The floors' spellings, isolated: below the `B` floor the
support key's read is the unit and the residue is vacant, so the
`g + 2` spelling binds; the `C` and `D` floors are the
classification's own domain (`thm:main`'s prefix), the below-floor
tables keeping both occupancy reads. -/

theorem pin33 : (corootAt (tableB 1) (tableB 1).thetaFold 1).oneValue
    BPair.unit := by decide +kernel
theorem pin34 : ¬ 0 < residue (tableB 1) := by decide +kernel
theorem pin35 : ¬ (corootAt (tableC 2) (tableC 2).thetaFold 0).oneValue
    BPair.unit := by decide +kernel
theorem pin36 : 0 < residue (tableC 2) := by decide +kernel
theorem pin37 : ¬ (corootAt (tableD 3) (tableD 3).thetaFold 1).oneValue
    BPair.unit := by decide +kernel
theorem pin38 : 0 < residue (tableD 3) := by decide +kernel

/-! The positive counts: `ℓ²` at `B` and `C`, `ℓ² - ℓ` at `D`,
and the fixed members' displayed counts. -/

theorem pin39 : posCount (tableB 2) = 4 := by decide +kernel
theorem pin40 : posCount (tableB 3) = 9 := by decide +kernel
theorem pin41 : posCount (tableB 4) = 16 := by decide +kernel
theorem pin42 : posCount (tableC 3) = 9 := by decide +kernel
theorem pin43 : posCount (tableC 4) = 16 := by decide +kernel
theorem pin44 : posCount (tableD 4) = 12 := by decide +kernel
theorem pin45 : posCount (tableD 5) = 20 := by decide +kernel
theorem pin46 : posCount tableG2 = 6 := by decide +kernel
theorem pin47 : posCount tableF4 = 24 := by decide +kernel
theorem pin48 : posCount tableE6 = 36 := by decide +kernel
theorem pin49 : posCount tableE7 = 63 := by decide +kernel
theorem pin50 : posCount tableE8 = 120 := by decide +kernel

/-! The highest root's form read per member. -/

theorem pin51 : thetaNormRead (tableB 2) := by decide +kernel
theorem pin52 : thetaNormRead (tableB 3) := by decide +kernel
theorem pin53 : thetaNormRead (tableB 4) := by decide +kernel
theorem pin54 : thetaNormRead (tableC 3) := by decide +kernel
theorem pin55 : thetaNormRead (tableC 4) := by decide +kernel
theorem pin56 : thetaNormRead (tableD 4) := by decide +kernel
theorem pin57 : thetaNormRead (tableD 5) := by decide +kernel
theorem pin58 : thetaNormRead tableG2 := by decide +kernel
theorem pin59 : thetaNormRead tableF4 := by decide +kernel
theorem pin60 : thetaNormRead tableE6 := by decide +kernel
theorem pin61 : thetaNormRead tableE7 := by decide +kernel
theorem pin62 : thetaNormRead tableE8 := by decide +kernel

/-! The form's simple symmetry per member. -/

theorem pin63 : symRead (tableB 2) := by decide +kernel
theorem pin64 : symRead (tableB 3) := by decide +kernel
theorem pin65 : symRead (tableB 4) := by decide +kernel
theorem pin66 : symRead (tableC 3) := by decide +kernel
theorem pin67 : symRead (tableC 4) := by decide +kernel
theorem pin68 : symRead (tableD 4) := by decide +kernel
theorem pin69 : symRead (tableD 5) := by decide +kernel
theorem pin70 : symRead tableG2 := by decide +kernel
theorem pin71 : symRead tableF4 := by decide +kernel
theorem pin72 : symRead tableE6 := by decide +kernel
theorem pin73 : symRead tableE7 := by decide +kernel
theorem pin74 : symRead tableE8 := by decide +kernel

/-! The shape, occupancy and root-fold coroot reads at the
direct-fold members, the series and `G_2` (the descent-built
members' positive lists close through the family reads below,
the three clauses riding the round trip there). -/

theorem pin75 : shapeRead (tableB 2) := by decide +kernel
theorem pin76 : shapeRead (tableB 3) := by decide +kernel
theorem pin77 : shapeRead (tableB 4) := by decide +kernel
theorem pin78 : shapeRead (tableC 3) := by decide +kernel
theorem pin79 : shapeRead (tableC 4) := by decide +kernel
theorem pin80 : shapeRead (tableD 4) := by decide +kernel
theorem pin81 : shapeRead (tableD 5) := by decide +kernel
theorem pin82 : shapeRead tableG2 := by decide +kernel

theorem pin83 : occRead (tableB 2) := by decide +kernel
theorem pin84 : occRead (tableB 3) := by decide +kernel
theorem pin85 : occRead (tableB 4) := by decide +kernel
theorem pin86 : occRead (tableC 3) := by decide +kernel
theorem pin87 : occRead (tableC 4) := by decide +kernel
theorem pin88 : occRead (tableD 4) := by decide +kernel
theorem pin89 : occRead (tableD 5) := by decide +kernel
theorem pin90 : occRead tableG2 := by decide +kernel

theorem pin91 : rhoRead (tableB 2) := by decide +kernel
theorem pin92 : rhoRead (tableB 3) := by decide +kernel
theorem pin93 : rhoRead (tableB 4) := by decide +kernel
theorem pin94 : rhoRead (tableC 3) := by decide +kernel
theorem pin95 : rhoRead (tableC 4) := by decide +kernel
theorem pin96 : rhoRead (tableD 4) := by decide +kernel
theorem pin97 : rhoRead (tableD 5) := by decide +kernel
theorem pin98 : rhoRead tableG2 := by decide +kernel

/-! The family reads at the descent-built members: the table's own
positive list against the displayed coordinate family, the round
trip with the per-fold key counts and the coroot reads at one
forcing.  The `E_8` read is the module's heavy pin, the 120-member family
at the shared Gram. -/

theorem pin99 : famRead tableF4 f4Simples f4Family := by decide +kernel

set_option maxHeartbeats 16000000 in
theorem pin100 : famRead tableE6 (e8Simples.take 6) (e8Family.filter selE6) := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem pin101 : famRead tableE7 (e8Simples.take 7) (e8Family.filter selE7) := by
  decide +kernel

set_option maxHeartbeats 16000000 in
theorem pin102 : famRead tableE8 e8Simples e8Family := by decide +kernel

/-! The committed positive-list literals are the descent's own
outputs: one certifying equation per `E`-member against
`descentAll`, so every further read walks the literal. -/

set_option maxHeartbeats 16000000 in
theorem pin103 : descentAll (e8Simples.take 6) 64 (e8Family.filter selE6)
    = posE6 := by decide +kernel

set_option maxHeartbeats 16000000 in
theorem pin104 : descentAll (e8Simples.take 7) 64 (e8Family.filter selE7)
    = posE7 := by decide +kernel

set_option maxHeartbeats 16000000 in
theorem pin105 : descentAll e8Simples 64 e8Family = posE8 := by
  decide +kernel

/-! The adjugate rows: the coroot witnesses at the five fold keys
`1, 1, 3, 2, 1`, and the θ-fold rows. -/

theorem pin106 : adjRead tableG2 1 adjG2 := by decide +kernel
theorem pin107 : adjRead tableF4 1 adjF4 := by decide +kernel
theorem pin108 : adjRead tableE6 3 adjE6 := by decide +kernel
theorem pin109 : adjRead tableE7 2 adjE7 := by decide +kernel
theorem pin110 : adjRead tableE8 1 adjE8 := by decide +kernel

theorem pin111 : thetaRowRead tableG2 1 adjG2 1 := by decide +kernel
theorem pin112 : thetaRowRead tableF4 1 adjF4 0 := by decide +kernel
theorem pin113 : thetaRowRead tableE6 3 adjE6 1 := by decide +kernel
theorem pin114 : thetaRowRead tableE7 2 adjE7 0 := by decide +kernel
theorem pin115 : thetaRowRead tableE8 1 adjE8 7 := by decide +kernel

/-! The invariant counts at the dual pair's line, one per
series. -/

theorem pin116 : invCountB 2 1 = 1 := by decide +kernel
theorem pin117 : invCountC 3 1 = 1 := by decide +kernel
theorem pin118 : invCountD 4 1 = 1 := by decide +kernel

/-! The coordinate tier at `B_2` and `G_2`: the fundamental data at
the coroot presentation — the cleared Gram with its scale, the
simple members' positions in the positive list, and the
reflections' permutations of it — read at the ten clauses, the
shape conjuncts, the Gram's defining read against the Cartan rows
with its symmetry and an inertia split certificate, the simple
positions, the involution and form-keeping reads, the permutation
of the positive list, and the `ρ`-dot positivity. -/


private def spGramB2 : inertia.Split 2 :=
  ⟨⟨[[BPair.ofNat 1, (BPair.ofNat 1).swap],
     [BPair.ofNat 0, BPair.ofNat 2]], rfl⟩,
   ⟨[[BPair.ofNat 2, BPair.ofNat 1],
     [BPair.ofNat 0, BPair.ofNat 1]], rfl⟩,
   [.one (BPair.ofNat 2), .one (BPair.ofNat 2)], 0, rfl⟩

private def spGramG2 : inertia.Split 2 :=
  ⟨⟨[[BPair.ofNat 1, (BPair.ofNat 6).swap],
     [BPair.ofNat 0, BPair.ofNat 4]], rfl⟩,
   ⟨[[BPair.ofNat 4, BPair.ofNat 6],
     [BPair.ofNat 0, BPair.ofNat 1]], rfl⟩,
   [.one (BPair.ofNat 4), .one (BPair.ofNat 48)], 0, rfl⟩

theorem pin119 : fundShape tB2 fundB2 := by decide +kernel
theorem pin120 : gramRead tB2 fundB2 := by decide +kernel
theorem pin121 : gramSymRead fundB2 := by decide +kernel
theorem pin122 : inertia.splitRead fundB2.gram spGramB2 := by decide +kernel
theorem pin123 : inertia.pdAt spGramB2 := by decide +kernel
theorem pin124 : simplePosRead tB2 fundB2 := by decide +kernel
theorem pin125 : reflSquareRead tB2 := by decide +kernel
theorem pin126 : permSquareRead tB2 fundB2 := by decide +kernel
theorem pin127 : reflFormRead tB2 fundB2 := by decide +kernel
theorem pin128 : permImageRead tB2 fundB2 := by decide +kernel
theorem pin129 : rhoDotRead tB2 fundB2 := by decide +kernel

/-! The Gram-side reads' classification at `balanceRead`: the
theorem's conclusion binds no field of the fundamental data, so no
fundamental-data forgery can refuse it — the defining read, the
symmetry and the shape sit in the frame class at the conclusion's
own shape, each pinned at the stated members and refused at the
committed forged tables' own batteries.  `gentable.rhoRead` binds
nowhere at all: it is four of its co-binders' own consequence,
landed as `assembly.rhoRead_derived` — `con:sertables`' own
sentence `s_i(2ρ) + 2α_i = 2ρ`, so the root fold's coroot pairs
read `(2ρ)(α_i^∨) = 2` — and withdrawn from `balanceRead`'s
signature.  The derivation: at the stated family's vector sum `T`
a letter reads `s_i T` two ways, the reflection join's kick at
`T`'s own coroot pair at `i` and the image clauses memberwise
(the simple's position crossing to its balance partner, every
further key carried along the permutation), and the permuted
remainder the two readings share cancels, placing the member at
the permutation's image `q` of the simple's position at
`(T_i - 1) α_i`.  Where `q` is the simple's own position the
cancelled positive `ρ`-dot reads `T_i` at two; off it the
permutation datum's involution returns at `q` — it carries `q`
back to the simple's position, so that member's own image clause
reads `α_i` itself — and the returned reading is what forces the
multiple negative, the member's `ρ`-dot joining the simple's to
the sum's unit against two strictly positive dots.  So `T_i`
reads two at every key, and no isolating forgery exists. -/

theorem pin130 : fundShape tableG2 fundG2 := by decide +kernel
theorem pin131 : gramRead tableG2 fundG2 := by decide +kernel
theorem pin132 : gramSymRead fundG2 := by decide +kernel
theorem pin133 : inertia.splitRead fundG2.gram spGramG2 := by decide +kernel
theorem pin134 : inertia.pdAt spGramG2 := by decide +kernel
theorem pin135 : simplePosRead tableG2 fundG2 := by decide +kernel
theorem pin136 : reflSquareRead tableG2 := by decide +kernel
theorem pin137 : permSquareRead tableG2 fundG2 := by decide +kernel
theorem pin138 : reflFormRead tableG2 fundG2 := by decide +kernel
theorem pin139 : permImageRead tableG2 fundG2 := by decide +kernel
theorem pin140 : rhoDotRead tableG2 fundG2 := by decide +kernel

/-! The committed refusals at the coordinate tier, each forged
datum's refusing reads pinned with the reads it leaves untouched
beside them. -/

-- the Gram forged symmetric off the Cartan rows' scaled diagonal:
-- the defining read refuses, the ρ-dot read with it (the Gram
-- enters the pairing), the symmetry alone deciding nothing
private def forgedGramB2 : FundData :=
  ⟨[[(BPair.ofNat 2), (BPair.ofNat 1)],
    [(BPair.ofNat 1), (BPair.ofNat 2)]],
   fundB2.scale, fundB2.simplePos, fundB2.perms⟩

theorem pin141 : ¬ gramRead tB2 forgedGramB2 := by decide +kernel
theorem pin142 : ¬ rhoDotRead tB2 forgedGramB2 := by decide +kernel
theorem pin143 : gramSymRead forgedGramB2 := by decide +kernel

-- the second simple's position forged off the positive list's
-- one-key fold: the simple positions' read refuses, the image
-- read with it (the images read at the simple's coroot vector),
-- the shape and square reads untouched
private def forgedSimplePosB2 : FundData :=
  ⟨fundB2.gram, fundB2.scale, [0, 2], fundB2.perms⟩

theorem pin144 : ¬ simplePosRead tB2 forgedSimplePosB2 := by decide +kernel
theorem pin145 : ¬ permImageRead tB2 forgedSimplePosB2 := by decide +kernel
theorem pin146 : fundShape tB2 forgedSimplePosB2 := by decide +kernel
theorem pin147 : permSquareRead tB2 forgedSimplePosB2 := by decide +kernel

-- the permutations forged to the identity and the leading
-- transposition: both stay involutions, so the involution read
-- passes and the permutation read refuses at the images
private def forgedPermsB2 : FundData :=
  ⟨fundB2.gram, fundB2.scale, fundB2.simplePos,
   [[0, 1, 2, 3], [1, 0, 2, 3]]⟩

theorem pin148 : ¬ permImageRead tB2 forgedPermsB2 := by decide +kernel
theorem pin149 : permSquareRead tB2 forgedPermsB2 := by decide +kernel

/-! The coordinate solves and the signed enumeration at symbolic
widths, with the half reads' parity and width refusals. -/

theorem pin150 (v : List BPair) : (coordsB v).length = v.length := coordsB_length v
theorem pin151 (v : List BPair) : (coordsC v).length = v.length := coordsC_length v
theorem pin152 (v : List BPair) (h : 2 ≤ v.length) : (coordsD v).length = v.length := coordsD_length v h
theorem pin153 : (coordsD [BPair.ofNat 1]).length = 0 := rfl
theorem pin154 (x : BPair) : (halfB (x + x)).oneValue x := halfB_double x
theorem pin155 (x : BPair) (h : x.marginN % 2 = 0) :
    (halfB x + halfB x).oneValue x := halfB_read x h
theorem pin156 : ¬ (halfB (BPair.ofNat 1) + halfB (BPair.ofNat 1)).oneValue (BPair.ofNat 1) := by
  decide +kernel
theorem pin157 : halfB (⟨3, 9⟩ : BPair) = (BPair.ofNat 3).swap
    ∧ halfB (⟨9, 3⟩ : BPair) = BPair.ofNat 3 := by decide +kernel
theorem pin158 (v : List BPair) (h : 0 < v.length) :
    poly.pnorm (corootsB (coordsB v)) = poly.pnorm v := corootsB_coordsB_norm v h
theorem pin159 (v : List BPair) (h : 0 < v.length) :
    poly.pnorm (corootsC (coordsC v)) = poly.pnorm v := corootsC_coordsC_norm v h
theorem pin160 (v : List BPair) (h : 2 ≤ v.length) :
    poly.pnorm (corootsD (coordsD v)) = poly.pnorm v := corootsD_coordsD_norm v h
theorem pin161 : poly.pnorm (corootsB (coordsB [])) ≠ ([] : List BPair)
    ∧ poly.pnorm (corootsC (coordsC [])) ≠ ([] : List BPair) := by decide +kernel
theorem pin162 : poly.pnorm (corootsD (coordsD [BPair.ofNat 2])) ≠ [BPair.ofNat 2] := by
  decide +kernel
theorem pin163 : poly.pnorm (corootsD (coordsD [⟨5, 2⟩, ⟨1, 3⟩, ⟨4, 7⟩]))
    = poly.pnorm [⟨5, 2⟩, ⟨1, 3⟩, ⟨4, 7⟩] := corootsD_coordsD_norm _ (by decide : 2 ≤ 3)
theorem pin164 : poly.pnorm (coordsB (corootsB [BPair.ofNat 1, BPair.unit]))
    ≠ [BPair.ofNat 1, BPair.unit] := by decide +kernel
theorem pin165 : poly.pnorm (coordsB (corootsB [BPair.ofNat 5, (BPair.ofNat 3).swap]))
    = [BPair.ofNat 5, (BPair.ofNat 3).swap] := by decide +kernel
theorem pin166 : poly.pnorm (coordsD (corootsD [BPair.ofNat 1, BPair.unit]))
    ≠ [BPair.ofNat 1, BPair.unit] := by decide +kernel
theorem pin167 : poly.pnorm (coordsD (corootsD [BPair.ofNat 5, (BPair.ofNat 3).swap]))
    = [BPair.ofNat 5, (BPair.ofNat 3).swap] := by decide +kernel
theorem pin168 (l : Nat) (v : List BPair) :
    (serWeylB l v).length = 2 ^ l * ground.factorial l := serWeylB_length l v
theorem pin169 (l : Nat) (v : List BPair) :
    (serWeylC l v).length = 2 ^ l * ground.factorial l := serWeylC_length l v
theorem pin170 (l : Nat) (v : List BPair) :
    (serWeylD (l + 1) v).length = 2 ^ l * ground.factorial (l + 1) := serWeylD_length l v
theorem pin171 (l : Nat) (v : List BPair) :
    (serWeylD l v).length ≤ 2 ^ l * ground.factorial l := serWeylD_length_le l v
theorem pin172 (l : Nat) (hl : 0 < l) (v : List BPair) :
    wShapeRead (tableB l) (serWeylB l v) := serWeylB_shape l hl v
theorem pin173 (l : Nat) (hl : 0 < l) (v : List BPair) :
    wShapeRead (tableC l) (serWeylC l v) := serWeylC_shape l hl v
theorem pin174 (l : Nat) (hl : 0 < l) (v : List BPair) :
    wShapeRead (tableD l) (serWeylD l v) := serWeylD_shape l hl v
theorem pin175 : ¬ wShapeRead (tableB 0) (serWeylB 0 []) := by decide +kernel
theorem pin176 : ¬ wShapeRead (tableC 0) (serWeylC 0 []) := by decide +kernel
theorem pin177 : ¬ wShapeRead (tableD 0) (serWeylD 0 []) := by decide +kernel
theorem pin178 (l : Nat) (v : List BPair) (hv : v.length = l) (hl : 0 < l) :
    (poly.pnorm v, false) ∈ serWeylB l v := serWeylB_seed l v hv hl
theorem pin179 (l : Nat) (v : List BPair) (hv : v.length = l) (hl : 0 < l) :
    (poly.pnorm v, false) ∈ serWeylC l v := serWeylC_seed l v hv hl
theorem pin180 (l : Nat) (v : List BPair) (hv : v.length = l) (hl : 2 ≤ l) :
    (poly.pnorm v, false) ∈ serWeylD l v := serWeylD_seed l v hv hl
theorem pin181 : ground.countOf ([BPair.ofNat 1], false) (serWeylB 2 [BPair.ofNat 1]) = 0 := by
  decide +kernel
theorem pin182 : ground.countOf ([BPair.ofNat 1], false) (serWeylC 2 [BPair.ofNat 1]) = 0 := by
  decide +kernel
theorem pin183 : ground.countOf ([BPair.ofNat 1], false) (serWeylD 1 [BPair.ofNat 1]) = 0 := by
  decide +kernel
theorem pin184 (l : Nat) (hl : 0 < l) (v : List BPair) (hv : v.length = l)
    (hp : ∀ i, i < l → BPair.unit < ground.getAt BPair.unit v i) :
    ground.distinctList ((serWeylB l v).map Prod.fst) := serWeylB_regular l hl v hv hp
theorem pin185 (l : Nat) (hl : 0 < l) (v : List BPair) (hv : v.length = l)
    (hp : ∀ i, i < l → BPair.unit < ground.getAt BPair.unit v i) :
    ground.distinctList ((serWeylC l v).map Prod.fst) := serWeylC_regular l hl v hv hp
theorem pin186 : ¬ ground.distinctList ((serWeylB 2 [BPair.unit, BPair.ofNat 1]).map Prod.fst) := by
  decide +kernel
theorem pin187 : ¬ ground.distinctList ((serWeylC 2 [BPair.unit, BPair.ofNat 1]).map Prod.fst) := by
  decide +kernel
theorem pin188 : (ground.dedupF ((serWeylB 2 [BPair.unit, BPair.ofNat 1]).map Prod.fst)).length = 4
    ∧ (serWeylB 2 [BPair.unit, BPair.ofNat 1]).length = 8 := by decide +kernel
theorem pin189 : (ground.dedupF ((serWeylC 2 [BPair.unit, BPair.ofNat 1]).map Prod.fst)).length = 4
    ∧ (serWeylC 2 [BPair.unit, BPair.ofNat 1]).length = 8 := by decide +kernel
theorem pin190 (l : Nat) :
    ((List.range (2 ^ (l + 1))).filter (fun n => !(flipParity (l + 1) n))).length = 2 ^ l :=
  evenSigns_length l
theorem pin191 : ((List.range 8).filter (fun n => !(flipParity 3 n))) = [0, 3, 5, 6] := by
  decide +kernel
theorem pin192 (l i n : Nat) (hi : i < l) (hn : n < 2 ^ l) :
    ∃ m, m < 2 ^ l ∧ flipParity l m = !(flipParity l n)
      ∧ ground.baseDigit 2 i m + ground.baseDigit 2 i n = 1
      ∧ ∀ j, j < l → j ≠ i → ground.baseDigit 2 j m = ground.baseDigit 2 j n :=
  flipParity_flip l i n hi hn
theorem pin193 : flipParity 3 1 = true ∧ flipParity 3 0 = false
    ∧ flipParity 3 5 = false ∧ flipParity 3 4 = true := by decide +kernel
theorem pin194 : flipParity 3 (0 + 2 ^ 3) = flipParity 3 0 := by decide +kernel
theorem pin195 (l : Nat) (D : List BPair) (p q : List Nat) (n : Nat)
    (hq : 0 < ground.countOf q (places.perms l)) :
    ∃ m, m < 2 ^ l ∧ flipParity l m = flipParity l n
      ∧ signedImage l D (places.expo p q) m = (List.range l).map (fun i =>
        ground.getAt BPair.unit (signedImage l D p n) (ground.getAt 0 q i)) :=
  signedImage_permute l D p q n hq
theorem pin196 : signedImage 2 [BPair.ofNat 2, BPair.ofNat 1] [1, 0] 2
    = [BPair.ofNat 1, (BPair.ofNat 2).swap] := by decide +kernel
theorem pin197 : signedImage 2 [BPair.ofNat 1, BPair.ofNat 1] [0, 1] 0
    = signedImage 2 [BPair.ofNat 1, BPair.ofNat 1] [1, 0] 0 := by decide +kernel
theorem pin198 : signedImage 2 [BPair.ofNat 1, (BPair.ofNat 1).swap] [0, 1] 3
    = signedImage 2 [BPair.ofNat 1, (BPair.ofNat 1).swap] [1, 0] 0 := by decide +kernel
theorem pin199 : signedImage 2 [BPair.ofNat 2, BPair.ofNat 1, BPair.ofNat 1] [0, 1] 0
    = signedImage 2 [BPair.ofNat 2, BPair.ofNat 1, BPair.ofNat 1] [0, 2] 0
    ∧ ground.countOf [0, 2] (places.perms 2) = 0 := by decide +kernel
theorem pin200 : signedImage 2 [BPair.ofNat 2, BPair.ofNat 1] [0, 1] 0
    = signedImage 2 [BPair.ofNat 2, BPair.ofNat 1] [0, 1] 4 := by decide +kernel
theorem pin201 (m : List BPair) (i j : Nat) (hi : i < m.length) (hj : j < m.length) :
    (ground.getAt BPair.unit (coordsB m) i).marginN % 2
      = (ground.getAt BPair.unit (coordsB m) j).marginN % 2 := coordsB_parity m i j hi hj
theorem pin202 (m : List BPair) (hm : 2 ≤ m.length) (i j : Nat)
    (hi : i < m.length) (hj : j < m.length) :
    (ground.getAt BPair.unit (coordsD m) i).marginN % 2
      = (ground.getAt BPair.unit (coordsD m) j).marginN % 2 := coordsD_parity m hm i j hi hj
theorem pin203 : poly.pnorm (coordsB [BPair.ofNat 2, BPair.ofNat 1, BPair.ofNat 3])
    = [BPair.ofNat 9, BPair.ofNat 5, BPair.ofNat 3] := by decide +kernel
theorem pin204 : poly.pnorm (coordsD [BPair.ofNat 2, BPair.ofNat 1, BPair.ofNat 3])
    = [BPair.ofNat 8, BPair.ofNat 4, BPair.ofNat 2] := by decide +kernel
theorem pin205 : poly.pnorm (coordsD [BPair.ofNat 2, BPair.ofNat 3, BPair.ofNat 1])
    = [BPair.ofNat 8, BPair.ofNat 4, (BPair.ofNat 2).swap] := by decide +kernel
theorem pin206 : poly.pnorm (coordsD [BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1])
    = [BPair.ofNat 4, BPair.ofNat 2, BPair.unit] := by decide +kernel

theorem pin207 : signedImage 3
      (signedImage 3 [BPair.ofNat 3, BPair.ofNat 2, BPair.ofNat 1] [2, 0, 1] 5) [1, 2, 0] 3
    = signedImage 3 [BPair.ofNat 3, BPair.ofNat 2, BPair.ofNat 1] [0, 1, 2] 5
    ∧ flipParity 3 5 = xor (flipParity 3 5) (flipParity 3 3) := by decide +kernel
theorem pin208 (D E : List BPair) (hD : D.length = 3) (hE : E.length = 3) :
    (elim.dotP (signedImage 3 D [2, 0, 1] 5) (signedImage 3 E [2, 0, 1] 5)).oneValue
      (elim.dotP D E) := signedImage_dot 3 D E [2, 0, 1] 5 hD hE (by decide +kernel)
theorem pin209 : ¬ (elim.dotP
      (signedImage 1 [BPair.ofNat 2] [0] 0) (signedImage 1 [BPair.ofNat 3] [0] 1)).oneValue
    (elim.dotP [BPair.ofNat 2] [BPair.ofNat 3]) := by decide +kernel
theorem pin210 : ¬ (elim.dotP
      (signedImage 2 [BPair.ofNat 2, BPair.ofNat 1] [0, 0] 0)
      (signedImage 2 [BPair.ofNat 2, BPair.ofNat 1] [0, 0] 0)).oneValue
    (elim.dotP [BPair.ofNat 2, BPair.ofNat 1] [BPair.ofNat 2, BPair.ofNat 1]) := by decide +kernel
theorem pin211 : ¬ (elim.dotP
      (signedImage 1 [BPair.ofNat 2, BPair.ofNat 3] [0] 0)
      (signedImage 1 [BPair.ofNat 3, BPair.ofNat 4] [0] 0)).oneValue
    (elim.dotP [BPair.ofNat 2, BPair.ofNat 3] [BPair.ofNat 3, BPair.ofNat 4]) := by decide +kernel
theorem pin212 : poly.oneValue
    (coordsD (corootsD [BPair.ofNat 5, BPair.ofNat 3, (BPair.ofNat 1).swap]))
    [BPair.ofNat 5, BPair.ofNat 3, (BPair.ofNat 1).swap] := by
  apply coordsD_corootsD [BPair.ofNat 5, BPair.ofNat 3, (BPair.ofNat 1).swap] (by decide : 2 ≤ 3)
  decide +kernel

/-! The B/C diagonal change and signed coordinate generators are
read at symbolic widths and at the half-gap domain boundary. -/

theorem pin213 (l i j : Nat) : cartB l i j = cartC l j i := cartB_C_transpose l i j
theorem pin214 (l i j : Nat) (hi : i < l) (hj : j < l) :
    (BPair.ofNat (if j + 1 = l then 1 else 2) * cartB l i j).oneValue
      (BPair.ofNat (if i + 1 = l then 1 else 2) * cartC l i j) := cartB_C_scale l i j hi hj
theorem pin215 (D : List BPair)
    (he : ∀ i, i + 1 < D.length →
      (ground.getAt BPair.unit D i + (ground.getAt BPair.unit D (i + 1)).swap).marginN % 2 = 0)
    (j : Nat) (hj : j < D.length) :
    (ground.getAt BPair.unit (corootsC D) j).oneValue
      (BPair.ofNat (if j + 1 = D.length then 1 else 2)
        * ground.getAt BPair.unit (corootsB D) j) := corootsB_C_scale D he j hj
theorem pin216 : ¬ (ground.getAt BPair.unit (corootsC [BPair.ofNat 2, BPair.ofNat 1]) 0).oneValue
    (BPair.ofNat 2 * ground.getAt BPair.unit (corootsB [BPair.ofNat 2, BPair.ofNat 1]) 0) := by
  decide +kernel
theorem pin217 (l i : Nat) (D : List BPair) (p : List Nat) (n : Nat)
    (hp : 0 < ground.countOf p (places.perms l)) (hi : i + 1 < l) :
    ∃ q, 0 < ground.countOf q (places.perms l) ∧ ∃ m, m < 2 ^ l
      ∧ flipParity l m = flipParity l n ∧ places.parity q = !(places.parity p)
      ∧ signedImage l D q m = ground.adjSwap i (signedImage l D p n) :=
  signedImage_adjSwap l i D p n hp hi
theorem pin218 (l i n : Nat) (D : List BPair) (p : List Nat) (hi : i < l) (hn : n < 2 ^ l) :
    ∃ m, m < 2 ^ l ∧ flipParity l m = !(flipParity l n)
      ∧ signedImage l D p m = (signedImage l D p n).set i
        (ground.getAt BPair.unit (signedImage l D p n) i).swap := signedImage_flip_set l i n D p hi hn
theorem pin219 (l i j : Nat) (h : i ≠ j) :
    ¬ (cartB l i j * cartB l j i).oneValue (BPair.ofNat 4) := cartB_pair l i j h
theorem pin220 (l i j : Nat) (h : i ≠ j) :
    ¬ (cartD l i j * cartD l j i).oneValue (BPair.ofNat 4) := cartD_pair l i j h
theorem pin221 : (cartD 4 2 2 * cartD 4 2 2).oneValue (BPair.ofNat 4) := by decide +kernel

/-! D regularity reads the even sign codes at a final coordinate
on either side or at equal members. -/

theorem pin222 (l : Nat) (hl : 2 ≤ l) (v : List BPair) (hv : v.length = l)
    (hp : ∀ i, i < l → BPair.unit < ground.getAt BPair.unit v i) :
    ground.distinctList ((serWeylD l v).map Prod.fst) := serWeylD_regular l hl v hv hp
theorem pin223 : ground.distinctList ((serWeylD 3 [BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1]).map Prod.fst) := by
  apply serWeylD_regular 3 (by decide) _ rfl
  decide +kernel
theorem pin224 : ground.distinctList ((serWeylD 3 [BPair.ofNat 2, BPair.ofNat 3, BPair.ofNat 1]).map Prod.fst) := by
  apply serWeylD_regular 3 (by decide) _ rfl
  decide +kernel
theorem pin225 : ground.distinctList ((serWeylD 3 [BPair.ofNat 2, BPair.ofNat 1, BPair.ofNat 3]).map Prod.fst) := by
  apply serWeylD_regular 3 (by decide) _ rfl
  decide +kernel
theorem pin226 : ¬ ground.distinctList ((serWeylD 3 [BPair.ofNat 1, BPair.unit, BPair.ofNat 1]).map Prod.fst) := by
  decide +kernel
theorem pin227 : signedImage 2 [BPair.ofNat 1, BPair.unit] [0, 1] 0
      = signedImage 2 [BPair.ofNat 1, BPair.unit] [0, 1] 2
    ∧ flipParity 2 0 ≠ flipParity 2 2 := by decide +kernel
theorem pin228 : signedImage 2 [BPair.ofNat 1, BPair.ofNat 1] [0, 1] 0
      = signedImage 2 [BPair.ofNat 1, BPair.ofNat 1] [1, 0] 0
    ∧ ([0, 1] : List Nat) ≠ [1, 0] := by decide +kernel
theorem pin229 (l i : Nat) (D : List BPair) (p : List Nat) (n : Nat)
    (hp : 0 < ground.countOf p (places.perms l)) (hi : i + 1 < l) :
    ∃ q, 0 < ground.countOf q (places.perms l) ∧ ∃ m, m < 2 ^ l
      ∧ flipParity l m = flipParity l n ∧ places.parity q = !(places.parity p)
      ∧ signedImage l D q m = ((signedImage l D p n).set i
        (ground.getAt BPair.unit (signedImage l D p n) (i + 1)).swap).set (i + 1)
          (ground.getAt BPair.unit (signedImage l D p n) i).swap :=
  signedImage_adjSwap_flip l i D p n hp hi

/-! Strictly dominant orbit keys are unique. The D display keeps
its final sign through the even-sign constraint, including a
final coordinate at equal members. -/

theorem pin230 (l : Nat) (hl : 0 < l) (v w : List BPair)
    (hv : v.length = l) (hw : w.length = l)
    (hpv : ∀ i, i < l → BPair.unit < ground.getAt BPair.unit v i)
    (hpw : ∀ i, i < l → BPair.unit < ground.getAt BPair.unit w i)
    (b : Bool) (h : (w, b) ∈ serWeylB l v) : poly.pnorm w = poly.pnorm v :=
  serWeylB_strict_top l hl v w hv hw hpv hpw b h
theorem pin231 (l : Nat) (hl : 0 < l) (v w : List BPair)
    (hv : v.length = l) (hw : w.length = l)
    (hpv : ∀ i, i < l → BPair.unit < ground.getAt BPair.unit v i)
    (hpw : ∀ i, i < l → BPair.unit < ground.getAt BPair.unit w i)
    (b : Bool) (h : (w, b) ∈ serWeylC l v) : poly.pnorm w = poly.pnorm v :=
  serWeylC_strict_top l hl v w hv hw hpv hpw b h
theorem pin232 (l : Nat) (hl : 2 ≤ l) (v w : List BPair)
    (hv : v.length = l) (hw : w.length = l)
    (hpv : ∀ i, i < l → BPair.unit < ground.getAt BPair.unit v i)
    (hpw : ∀ i, i < l → BPair.unit < ground.getAt BPair.unit w i)
    (b : Bool) (h : (w, b) ∈ serWeylD l v) : poly.pnorm w = poly.pnorm v :=
  serWeylD_strict_top l hl v w hv hw hpv hpw b h
theorem pin233 : (signedImage 2 [BPair.ofNat 3, BPair.ofNat 1] [0, 1] 2).map BPair.marginN = [3, 1]
    ∧ ¬ poly.oneValue (signedImage 2 [BPair.ofNat 3, BPair.ofNat 1] [0, 1] 2) [BPair.ofNat 3, BPair.ofNat 1]
    ∧ flipParity 2 2 = true := by decide +kernel
theorem pin234 (l : Nat) (D : List BPair) (hD : D.length = l)
    (p : List Nat) (n a : Nat) (hp : 0 < ground.countOf p (places.perms l)) :
    ground.countOf a ((signedImage l D p n).map BPair.marginN) = ground.countOf a (D.map BPair.marginN) :=
  signedImage_margin_counts l D hD p n hp a
theorem pin235 : (ground.getAt BPair.unit (coordsD [BPair.ofNat 2, BPair.ofNat 4, BPair.ofNat 4]) 2).oneValue BPair.unit := by
  decide +kernel
theorem pin236 (v : List BPair) (k : Nat) (hv : v.length = k + 2) :
    coordsD (ground.adjSwap k v) = (coordsD v).set (k + 1) (ground.getAt BPair.unit (coordsD v) (k + 1)).swap :=
  coordsD_forkSwap v k hv

/-! The D Cartan Gram is nonsingular at every leading block,
and its final-key symmetry includes the two-key floor. -/

theorem pin237 (k m : Nat) (hm : m < k + 2) :
    ¬ (elim.leadMinor (tableD (k + 2)).cartan (m + 1)).oneValue BPair.unit := cartanD_lead k m hm
theorem pin238 (k i j : Nat) (hi : i < k + 2) (hj : j < k + 2) :
    cartD (k + 2) (ground.swapIx k (k + 1) i) (ground.swapIx k (k + 1) j)
      = cartD (k + 2) i j := cartD_forkSwap k i j hi hj
theorem pin239 : (elim.leadMinor (tableD 2).cartan 1).oneValue (BPair.ofNat 2)
    ∧ (elim.leadMinor (tableD 2).cartan 2).oneValue (BPair.ofNat 4) := by decide +kernel
theorem pin240 : (elim.leadMinor (tableD 4).cartan 3).oneValue (BPair.ofNat 4)
    ∧ (elim.leadMinor (tableD 4).cartan 4).oneValue (BPair.ofNat 4) := by decide +kernel
theorem pin241 : cartD 4 0 1 ≠ cartD 4 0 2 := by decide +kernel

/-! The G2 cycle contains the actual letter actions, with both
parities and the identity's seed position. -/

theorem pin242 : ∀ i, i < 2 → ∀ j, j < 12 →
    weylStepG2 i (weylStepG2 i j) = j ∧ (weylStepG2 i j % 2 == 1) = !(j % 2 == 1) := by
  intro i hi j hj
  exact ⟨weylStepG2_invol i hi j hj, weylStepG2_parity i hi j hj⟩
theorem pin243 (v : List BPair) : (weylG2 v).length = 12 := weylG2_length v
theorem pin244 : weylMatG2 6 = elim.idMat 2 ∧ weylStepG2 1 0 = 11 ∧ weylStepG2 0 11 = 10 := by decide +kernel
theorem pin245 : fundOfRows tableG2 adjG2 1 = fundG2 := by rfl

/-! The derived fixed-member data retain the clearing scales and
reject false reflection permutations or length-diagonal scales. -/

theorem pin246 : ¬ gramRead tableE6 { fundE6 with scale := 1 } := by decide +kernel
theorem pin247 : ¬ gramRead tableE7 { fundE7 with scale := 1 } := by decide +kernel
theorem pin248 : ¬ permImageRead tableF4 { fundF4 with perms := List.replicate 4 (List.range 24) } := by decide +kernel
theorem pin249 : ¬ permSquareRead tableF4 { fundF4 with perms := List.replicate 4 (List.replicate 24 0) } := by decide +kernel
theorem pin250 : ¬ reflFormRead tableE8 { fundE8 with gram := elim.idMat 8 } := by decide +kernel
theorem pin251 : BPair.unit < elim.detD (elim.transposeM tableG2.cartan)
    ∧ BPair.unit < elim.detD (elim.transposeM tableF4.cartan)
    ∧ BPair.unit < elim.detD (elim.transposeM tableE6.cartan)
    ∧ BPair.unit < elim.detD (elim.transposeM tableE7.cartan)
    ∧ BPair.unit < elim.detD (elim.transposeM tableE8.cartan) :=
  ⟨cartanSolve_G2.2.2, cartanSolve_F4.2.2, cartanSolve_E6.2.2, cartanSolve_E7.2.2, cartanSolve_E8.2.2⟩

/-- Every simple reflection of a symbolic series table squares
to the identity, including the vacant rank's bounded read. -/
theorem pin252 (l : Nat) : reflSquareRead (tableB l) := reflSquareRead_B l
theorem pin253 (l : Nat) : reflSquareRead (tableC l) := reflSquareRead_C l
theorem pin254 (l : Nat) : reflSquareRead (tableD l) := reflSquareRead_D l

/-- Changing the diagonal away from two can destroy the
reflection's square even at one coordinate. -/
theorem pin255 : ¬ reflSquareRead { tableB 1 with cartan := [[BPair.ofNat 3]] } := by decide +kernel

/-- A chamber wall allows a nonidentity permutation of repeated
magnitudes, including a negative final coordinate. -/
theorem pin256 : poly.oneValue [BPair.ofNat 3, BPair.ofNat 3, (BPair.ofNat 3).swap]
    [BPair.ofNat 3, BPair.ofNat 3, (BPair.ofNat 3).swap] :=
  signedImage_even_weak_unique 2 _ _ rfl rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [1, 0, 2] 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Two zero coordinates can be exchanged and flipped within
one even-sign orbit without changing the coordinate read. -/
theorem pin257 : poly.oneValue [BPair.ofNat 3, BPair.unit, BPair.unit]
    [BPair.ofNat 3, BPair.unit, BPair.unit] :=
  signedImage_even_weak_unique 2 _ _ rfl rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [0, 2, 1] 6 (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Odd sign parity admits the opposite final coordinate
at the same weakly ordered magnitudes. -/
theorem pin258 : flipParity 3 4 = true
    ∧ poly.oneValue [BPair.ofNat 3, BPair.ofNat 3, BPair.ofNat 3]
      (signedImage 3 [BPair.ofNat 3, BPair.ofNat 3, (BPair.ofNat 3).swap] [0, 1, 2] 4)
    ∧ ¬ poly.oneValue [BPair.ofNat 3, BPair.ofNat 3, BPair.ofNat 3]
      [BPair.ofNat 3, BPair.ofNat 3, (BPair.ofNat 3).swap] := by decide +kernel

/-- Even parity does not identify a display whose earlier
coordinates can lie on the lower side. -/
theorem pin259 : flipParity 3 5 = false
    ∧ poly.oneValue [BPair.ofNat 3, BPair.ofNat 3, BPair.ofNat 3]
      (signedImage 3 [(BPair.ofNat 3).swap, BPair.ofNat 3, (BPair.ofNat 3).swap] [0, 1, 2] 5)
    ∧ ¬ poly.oneValue [BPair.ofNat 3, BPair.ofNat 3, BPair.ofNat 3]
      [(BPair.ofNat 3).swap, BPair.ofNat 3, (BPair.ofNat 3).swap] := by decide +kernel

/-- The signed product records odd parity at an occupied
coordinate product, and reads the unit at a zero factor. -/
theorem pin260 (D : List BPair) (hD : D.length = 3) :
    ground.famFold BPair.mul (BPair.ofNat 1) (fun x => x) (signedImage 3 D [2, 0, 1] 1)
      = ground.signedAt (flipParity 3 1) (ground.famFold BPair.mul (BPair.ofNat 1) (fun x => x) D) :=
  signedImage_product 3 D hD [2, 0, 1] 1 (by decide +kernel)

theorem pin261 : (ground.famFold BPair.mul (BPair.ofNat 1) (fun x => x)
    (signedImage 3 [BPair.ofNat 3, BPair.unit, BPair.unit] [2, 0, 1] 1)).oneValue BPair.unit := by decide +kernel

/-- A false place assignment can duplicate a coordinate and
change the product; the permutation read is needed. -/
theorem pin262 : ¬ (ground.famFold BPair.mul (BPair.ofNat 1) (fun x => x)
      (signedImage 2 [BPair.ofNat 2, BPair.ofNat 3] [0, 0] 0)).oneValue
    (ground.famFold BPair.mul (BPair.ofNat 1) (fun x => x) [BPair.ofNat 2, BPair.ofNat 3]) := by decide +kernel

/-- The D fork's two wall labels have opposite final coordinates
at repeated magnitudes, each in its own dominant orbit. -/
theorem pin263 : poly.oneValue (coordsD [BPair.unit, BPair.unit, BPair.ofNat 1, BPair.unit])
    [BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1, (BPair.ofNat 1).swap]
    ∧ poly.oneValue (coordsD [BPair.unit, BPair.unit, BPair.unit, BPair.ofNat 1])
    [BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1] := by decide +kernel

/-- Every strictly positive G2 seed gives twelve distinct keys,
with both coroot coordinates arbitrary. -/
theorem pin264 (v : List BPair) (hv : v.length = 2)
    (hp : ∀ i, i < 2 → BPair.unit < ground.getAt BPair.unit v i) :
    ground.distinctList ((weylG2 v).map Prod.fst) := weylG2_regular v hv hp

/-- A wall or the zero seed repeats keys in the twelve-word
family; the strict-seed premise is needed for graded regularity. -/
theorem pin265 : ¬ ground.distinctList ((weylG2 [BPair.unit, BPair.ofNat 1]).map Prod.fst)
    ∧ ¬ ground.distinctList ((weylG2 [BPair.unit, BPair.unit]).map Prod.fst) := by decide +kernel

/-- The identity has the vacant fold and the negative identity
has twice the fundamental fold matrix. -/
theorem pin266 : elim.matNull (weylFoldG2 6)
    ∧ elim.matOneValue (weylFoldG2 0) [[BPair.ofNat 4, BPair.ofNat 6], [BPair.ofNat 2, BPair.ofNat 4]] := by decide +kernel

/-- The fundamental adjugate rows enter transposed: the opposite
orientation refuses the Cartan solve at the negative identity. -/
theorem pin267 : ¬ elim.matOneValue
    (elim.matAdd (weylMatG2 0) (elim.matMul (elim.transposeM tableG2.cartan)
      [[BPair.ofNat 4, BPair.ofNat 2], [BPair.ofNat 6, BPair.ofNat 4]])) (elim.idMat 2) := by decide +kernel


/-- Reversal is an involution at every displayed word, and its
pairing transport reads arbitrary coroot data. -/
theorem pin268 (j : Nat) (hj : j < 12) :
    weylInvG2 (weylInvG2 j) = j ∧ weylInvG2 j % 2 = j % 2 :=
  ⟨(weylInvG2_read j hj).2.1, (weylInvG2_read j hj).2.2.1⟩

theorem pin269 (j : Nat) (hj : j < 12) (x y : List BPair)
    (hx : x.length = 2) (hy : y.length = 2) :
    (dotB fundG2 (poly.pnorm (elim.matVec (weylMatG2 j) x)) y).oneValue
      (dotB fundG2 x (poly.pnorm (elim.matVec (weylMatG2 (weylInvG2 j)) y))) :=
  weylMatG2_dot j hj x y hx hy

/-- A word off its own inverse requires the reversed index in
its transpose transport. -/
theorem pin270 : weylInvG2 2 = 10 ∧ ¬ elim.matOneValue
    (elim.matMul (elim.transposeM (weylMatG2 2)) fundG2.gram)
    (elim.matMul fundG2.gram (weylMatG2 2)) := by decide +kernel

/-- The root-occupancy reads hold at symbolic ranks and actual
members of each family's list. -/
theorem pin271 (l : Nat) (f : List Nat) (hf : f ∈ foldsB l) :
    f.length = l ∧ 0 < ground.sumNat f := foldsB_occupied l f hf

theorem pin272 (l : Nat) (f : List Nat) (hf : f ∈ foldsC l) :
    f.length = l ∧ 0 < ground.sumNat f := foldsC_occupied l f hf

theorem pin273 (l : Nat) (f : List Nat) (hf : f ∈ foldsD l) :
    f.length = l ∧ 0 < ground.sumNat f := foldsD_occupied l f hf

theorem pin274 (l i : Nat) (hi : i < l) :
    ((List.range l).map (fun k => if k == i then 1 else 0)) ∈ foldsB l := simpleFold_mem_B l i hi

theorem pin275 (l i : Nat) (hi : i < l) :
    ((List.range l).map (fun k => if k == i then 1 else 0)) ∈ foldsC l := simpleFold_mem_C l i hi

theorem pin276 (l i : Nat) (hl : 2 ≤ l) (hi : i < l) :
    ((List.range l).map (fun k => if k == i then 1 else 0)) ∈ foldsD l := simpleFold_mem_D l i hl hi

theorem pin277 : foldsD 1 = [] ∧ ground.countOf [1] (foldsD 1) = 0 := by decide +kernel

end sertables
