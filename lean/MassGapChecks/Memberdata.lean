import MassGap.Memberdata
/-!
The check module for `lem:memberdata` and `con:fusion`'s member
instantiations.  The producers' outputs are decided against the
landed verification kit — the multiplicity families at
`memberchar`'s reads with the trace recursion's own read
(`recRead`) at the committed fundamental data, the produced Gram
at its defining read against the Cartan rows — and the interface
laws are pinned per instance at stated labels, the count-law pins
at the members whose row folds sit inside the budget (`B_2`,
`G_2`, with `B_3`'s and `D_4`'s single-target reads beside them)
and the cheap-field laws across the classification.  The drift
identity is pinned at each of those members' own `θ` — the adjoint
square's row fold against `2 d_θ²` cleared — `B_2` and `G_2` with
`B_3`, `C_3` and `D_4` beside them, and at `B_2`'s and `G_2`'s
further labels off `θ`, the row's uniformity exercised away from
the adjoint's own shape.  The value
pins tie the fields to the displayed data: the `θ` keys, the
dimensions, the Casimir ratios (`lem:casfloor`'s end lists), the
`θ`-square rows, and the involutions (`lem:memberdata`(ii): the
identity at `B_3`, the last two simple keys' exchange at `D_5`,
the branch involution at `E_6`).  The committed refusals isolate
the load-bearing data: the involution's exchange at `D_5` (the
identity refusing the dual-class law), the Casimir field (a
flattened read refusing the drift), and the walks' fuel (the
starved closure refusing the Cartan strictness).  The count pins
run the family fold (`lem:memberdata`(i)'s display fold) at the
members whose family solves sit inside the budget, `G_2` and
`F_4` the fixed instances, with the displayed Weyl lists pinned
against the word closure at the one-graded-multiset reads
(`sertables.serWeylB` at `B_2`, `serWeylC` at `C_3`, `serWeylD`
at `D_3`, each against `orbitFam`), and the heavy members'
further rows are the polynomial tier's, read at
`lem:serstable`'s word reads rather than re-decided here.
-/

namespace memberdata
set_option maxHeartbeats 64000000

open ground fusion

/-! ## The producers at the landed kit

The `B_2` family at `θ` runs the whole kit, the recursion's read
at the committed fundamental data with the produced `ρ`-orbit;
the further members run the shape, symmetry, top and dominance
reads at their own produced families. -/

theorem pin1 : memberchar.mShapeRead (sertables.tableB 2)
    (multFam (sertables.tableB 2) (gramOf (sertables.tableB 2)) 16 [0,2]) := by
  decide +kernel
theorem pin2 : memberchar.symRead (sertables.tableB 2)
    (multFam (sertables.tableB 2) (gramOf (sertables.tableB 2)) 16 [0,2]) := by
  decide +kernel
theorem pin3 : memberchar.topRead
    (multFam (sertables.tableB 2) (gramOf (sertables.tableB 2)) 16 [0,2])
    (poly.pnorm (natV [0,2])) := by decide +kernel
theorem pin4 : memberchar.lamRead (sertables.tableB 2)
    (poly.pnorm (natV [0,2])) := by decide +kernel
theorem pin5 : memberchar.supportRead (sertables.tableB 2)
    (multFam (sertables.tableB 2) (gramOf (sertables.tableB 2)) 16 [0,2])
    ((multFam (sertables.tableB 2) (gramOf (sertables.tableB 2)) 16
      [0,2]).map (foldWits (sertables.tableB 2) (natV [0,2])))
    (poly.pnorm (natV [0,2])) := by decide +kernel
theorem pin6 : memberchar.recRead (sertables.tableB 2) sertables.fundB2
    (sertables.serWeylB 2 (sertables.rhoV (sertables.tableB 2)))
    (multFam (sertables.tableB 2) (gramOf (sertables.tableB 2)) 16 [0,2])
    (poly.pnorm (natV [0,2])) := by decide +kernel

/-! The displayed Weyl lists against the word closure: at a shifted
key each displayed member sits in the letters' closure once, the
lists one graded multiset (`con:sertables`' one-member-each
read). -/

theorem pin7 : ((sertables.serWeylB 2
      (shiftV (sertables.tableB 2) [0,2])).all (fun vp =>
    ground.countOf vp (orbitFam (sertables.tableB 2) 16
      (shiftV (sertables.tableB 2) [0,2])) == 1)) = true
    ∧ (sertables.serWeylB 2 (shiftV (sertables.tableB 2) [0,2])).length
      = (orbitFam (sertables.tableB 2) 16
          (shiftV (sertables.tableB 2) [0,2])).length := by decide +kernel
theorem pin8 : ((sertables.serWeylC 3
      (shiftV (sertables.tableC 3) [2,0,0])).all (fun vp =>
    ground.countOf vp (orbitFam (sertables.tableC 3) 60
      (shiftV (sertables.tableC 3) [2,0,0])) == 1)) = true := by decide +kernel
theorem pin9 : ((sertables.serWeylD 3
      (shiftV (sertables.tableD 3) [0,1,0])).all (fun vp =>
    ground.countOf vp (orbitFam (sertables.tableD 3) 60
      (shiftV (sertables.tableD 3) [0,1,0])) == 1)) = true
    ∧ (sertables.serWeylD 3 (shiftV (sertables.tableD 3) [0,1,0])).length
      = (orbitFam (sertables.tableD 3) 60
          (shiftV (sertables.tableD 3) [0,1,0])).length := by decide +kernel

theorem pin10 : memberchar.mShapeRead (sertables.tableB 3)
    (multFam (sertables.tableB 3) (gramOf (sertables.tableB 3)) 60 [0,1,0]) := by
  decide +kernel
theorem pin11 : memberchar.symRead (sertables.tableB 3)
    (multFam (sertables.tableB 3) (gramOf (sertables.tableB 3)) 60 [0,1,0]) := by
  decide +kernel
theorem pin12 : memberchar.topRead
    (multFam (sertables.tableB 3) (gramOf (sertables.tableB 3)) 60 [0,1,0])
    (poly.pnorm (natV [0,1,0])) := by decide +kernel
theorem pin13 : memberchar.supportRead (sertables.tableB 3)
    (multFam (sertables.tableB 3) (gramOf (sertables.tableB 3)) 60 [0,1,0])
    ((multFam (sertables.tableB 3) (gramOf (sertables.tableB 3)) 60
      [0,1,0]).map (foldWits (sertables.tableB 3) (natV [0,1,0])))
    (poly.pnorm (natV [0,1,0])) := by decide +kernel
theorem pin14 : memberchar.mShapeRead sertables.tableG2
    (multFam sertables.tableG2 (sertables.gramRows sertables.tableG2 sertables.adjG2)
      16 [0,1]) := by decide +kernel
theorem pin15 : memberchar.symRead sertables.tableG2
    (multFam sertables.tableG2 (sertables.gramRows sertables.tableG2 sertables.adjG2)
      16 [0,1]) := by decide +kernel
theorem pin16 : memberchar.supportRead sertables.tableG2
    (multFam sertables.tableG2 (sertables.gramRows sertables.tableG2 sertables.adjG2)
      16 [0,1])
    ((multFam sertables.tableG2 (sertables.gramRows sertables.tableG2 sertables.adjG2)
      16 [0,1]).map (foldWits sertables.tableG2 (natV [0,1])))
    (poly.pnorm (natV [0,1])) := by decide +kernel

/-! The produced Gram's defining read: the Cartan rows against the
produced rows read the determinant-scaled length diagonal. -/

theorem pin17 : elim.matOneValue
    (elim.matMul (sertables.tableB 2).cartan (gramOf (sertables.tableB 2)))
    (ground.matOf 2 2 (fun i j =>
      if i == j then BPair.ofNat (2 * getAt 0 (sertables.tableB 2).lenNums i)
      else BPair.unit)) := by decide +kernel
theorem pin18 : elim.matOneValue
    (elim.matMul (sertables.tableD 4).cartan (gramOf (sertables.tableD 4)))
    (ground.matOf 4 4 (fun i j =>
      if i == j then BPair.ofNat (4 * getAt 0 (sertables.tableD 4).lenNums i)
      else BPair.unit)) := by decide +kernel
theorem pin19 : elim.matOneValue
    (elim.transposeM (sertables.gramRows sertables.tableE7 sertables.adjE7))
    (sertables.gramRows sertables.tableE7 sertables.adjE7) := by decide +kernel

/-! ## The interface laws at the instances

The count laws at `B_2` and `G_2` run whole rows; `B_3` and `D_4`
pin single-target reads; the class, Casimir and enumeration laws
run across the classification. -/

theorem pin20 : unitLaw (dataB 2) [0,2] [0,2] := by decide +kernel
theorem pin21 : commLaw (dataB 2) [0,2] [1,0] [1,2] := by decide +kernel
theorem pin22 : cartanLaw (dataB 2) [0,2] [0,2] := by decide +kernel
theorem pin23 : assocLaw (dataB 2) [0,2] [0,2] [0,2] [0,2] := by decide +kernel
theorem pin24 : dimLaw (dataB 2) [0,2] [0,2] := by decide +kernel
theorem pin25 : driftLaw (dataB 2) [0,2] := by decide +kernel
theorem pin26 : driftLaw (dataB 2) [1,0] := by decide +kernel
theorem pin27 : driftLaw (dataB 2) [2,0] := by decide +kernel
theorem pin28 : casPos (dataB 2) [1,0] := by decide +kernel
theorem pin29 : clsLaw (dataB 2) [0,1] [0,1] := by decide +kernel
theorem pin30 : clsDualLaw (dataB 2) [0,1] := by decide +kernel
theorem pin31 : clsThetaLaw (dataB 2) := by decide +kernel
theorem pin32 : belowSound (dataB 2) 60 := by decide +kernel
theorem pin33 : oneUnit (dataB 2) ((dataB 2).below 60) := by decide +kernel

theorem pin34 : unitLaw (dataG2) [1,0] [1,0] := by decide +kernel
theorem pin35 : cartanLaw (dataG2) [0,1] [0,1] := by decide +kernel
theorem pin36 : dimLaw (dataG2) [0,1] [0,1] := by decide +kernel
theorem pin37 : driftLaw (dataG2) [0,1] := by decide +kernel
theorem pin38 : driftLaw (dataG2) [1,0] := by decide +kernel
theorem pin39 : casPos (dataG2) [1,0] := by decide +kernel
theorem pin40 : belowSound (dataG2) 60 := by decide +kernel

theorem pin41 : dimLaw (dataB 3) [0,1,0] [0,1,0] := by decide +kernel
theorem pin42 : driftLaw (dataB 3) [0,1,0] := by decide +kernel
theorem pin43 : cartanLaw (dataB 3) [0,1,0] [0,1,0] := by decide +kernel
theorem pin44 : belowSound (dataB 3) 130 := by decide +kernel
theorem pin45 : oneUnit (dataB 3) ((dataB 3).below 130) := by decide +kernel
theorem pin46 : clsDualLaw (dataB 3) [0,0,1] := by decide +kernel
theorem pin47 : clsThetaLaw (dataB 3) := by decide +kernel

theorem pin48 : cartanLaw (dataC 3) [2,0,0] [2,0,0] := by decide +kernel
theorem pin49 : dimLaw (dataC 3) [2,0,0] [2,0,0] := by decide +kernel
theorem pin50 : driftLaw (dataC 3) [2,0,0] := by decide +kernel
theorem pin51 : casPos (dataC 3) [1,0,0] := by decide +kernel
theorem pin52 : clsDualLaw (dataC 3) [1,0,0] := by decide +kernel
theorem pin53 : clsThetaLaw (dataC 3) := by decide +kernel

/-- The fork's own count at `D_4`: the two spinors fuse to the
vector once, the count read through the fork keys' wiring. -/
theorem pin54 : (dataD 4).count [0,0,1,0] [0,0,0,1] [1,0,0,0] = 1 := by decide +kernel
theorem pin55 : cartanLaw (dataD 4) [0,1,0,0] [0,1,0,0] := by decide +kernel
theorem pin56 : driftLaw (dataD 4) [0,1,0,0] := by decide +kernel
theorem pin57 : casPos (dataD 4) [0,0,1,0] := by decide +kernel
theorem pin58 : clsDualLaw (dataD 4) [0,0,1,0] := by decide +kernel
theorem pin59 : clsThetaLaw (dataD 4) := by decide +kernel

/-- The `D` coordinate solve's round trips: the displayed coroot
pairs read the coordinate display back at the fork seed. -/
theorem pin60 : sertables.corootsD (sertables.coordsD
      (shiftV (sertables.tableD 4) [0,1,0,0]))
    = shiftV (sertables.tableD 4) [0,1,0,0] := by decide +kernel
theorem pin61 : sertables.corootsD (sertables.coordsD
      (shiftV (sertables.tableD 5) [1,0,2,1,0]))
    = shiftV (sertables.tableD 5) [1,0,2,1,0] := by decide +kernel
/-- The unit read at `D_5`'s spinor pair: the count field against
the involution at the exchanged fork keys, the one dual read off
the self-dual labels. -/
theorem pin62 : unitLaw (dataD 5) [0,0,0,1,0] [0,0,0,0,1] := by decide +kernel
theorem pin63 : casPos (dataD 5) [1,0,0,0,0] := by decide +kernel
theorem pin64 : clsDualLaw (dataD 5) [0,0,0,1,0] := by decide +kernel
theorem pin65 : clsThetaLaw (dataD 5) := by decide +kernel

theorem pin66 : casPos (dataF4) [0,0,0,1] := by decide +kernel
theorem pin67 : clsThetaLaw (dataF4) := by decide +kernel

theorem pin68 : casPos (dataE6) [1,0,0,0,0,0] := by decide +kernel
theorem pin69 : clsDualLaw (dataE6) [1,0,0,0,0,0] := by decide +kernel
theorem pin70 : clsThetaLaw (dataE6) := by decide +kernel

theorem pin71 : casPos (dataE7) [0,0,0,0,0,0,1] := by decide +kernel
theorem pin72 : clsDualLaw (dataE7) [0,0,0,0,0,0,1] := by decide +kernel
theorem pin73 : clsThetaLaw (dataE7) := by decide +kernel

theorem pin74 : casPos (dataE8) (memberdata.thetaKey sertables.tableE8) := by decide +kernel
theorem pin75 : clsThetaLaw (dataE8) := by decide +kernel

/-! ## The value pins at the displayed data

The `θ` keys, the `θ`-square rows, the dimensions, the Casimir
ratios (`lem:casfloor`'s end lists at the cleared pairs), the
diagonal (the base, `prop:row`'s member read), and the
involutions' reads. -/

theorem pin76 : (dataB 2).theta = [0, 2] := by decide +kernel
theorem pin77 : (dataB 3).theta = [0, 1, 0] := by decide +kernel
theorem pin78 : (dataC 3).theta = [2, 0, 0] := by decide +kernel
theorem pin79 : (dataD 4).theta = [0, 1, 0, 0] := by decide +kernel
theorem pin80 : (dataG2).theta = [0, 1] := by decide +kernel
theorem pin81 : (dataF4).theta = [1, 0, 0, 0] := by decide +kernel
theorem pin82 : (dataE6).theta = [0, 1, 0, 0, 0, 0] := by decide +kernel
theorem pin83 : (dataE7).theta = [1, 0, 0, 0, 0, 0, 0] := by decide +kernel
theorem pin84 : (dataE8).theta = [0, 0, 0, 0, 0, 0, 0, 1] := by decide +kernel

theorem pin85 : (dataB 2).row [0,2] [0,2]
    = [[0,0], [0,2], [0,4], [1,0], [1,2], [2,0]] := by decide +kernel
theorem pin86 : (dataG2).row [0,1] [0,1]
    = [[0,0], [0,1], [0,2], [2,0], [3,0]] := by decide +kernel

theorem pin87 : (dataB 2).count [0,2] [0,2] [0,2] = 1 := by decide +kernel
theorem pin88 : (dataB 3).count [0,1,0] [0,1,0] [0,1,0] = 1 := by decide +kernel
theorem pin89 : (dataG2).count [0,1] [0,1] [0,1] = 1 := by decide +kernel
theorem pin90 : (dataB 2).c1 = 1 := by decide +kernel
theorem pin91 : (dataF4).c1 = 1 := by decide +kernel

theorem pin92 : (dataB 2).dim [0,2] = 10 := by decide +kernel
theorem pin93 : (dataB 3).dim [0,1,0] = 21 := by decide +kernel
theorem pin94 : (dataB 3).dim [0,0,1] = 8 := by decide +kernel
theorem pin95 : (dataC 3).dim [2,0,0] = 21 := by decide +kernel
theorem pin96 : (dataD 4).dim [0,1,0,0] = 28 := by decide +kernel
theorem pin97 : (dataD 5).dim [0,0,0,1,0] = 16 := by decide +kernel
theorem pin98 : (dataG2).dim [0,1] = 14 := by decide +kernel
theorem pin99 : (dataF4).dim [1,0,0,0] = 52 := by decide +kernel
theorem pin100 : (dataE6).dim [0,1,0,0,0,0] = 78 := by decide +kernel
theorem pin101 : (dataE7).dim [1,0,0,0,0,0,0] = 133 := by decide +kernel
theorem pin102 : (dataE8).dim [0,0,0,0,0,0,0,1] = 248 := by decide +kernel

/-- The spinor's ratio at `B_3`: `ĉ₂ = [ℓ(2ℓ+1) : 8(r+1)]` reads
`21` against the adjoint's `40` (`lem:casfloor`'s end list). -/
theorem pin103 : (dataB 3).c2N [0,0,1] = 21 ∧ (dataB 3).c2D = 40 := by decide +kernel
/-- The vector's ratio at `B_3`: `[ℓ : r+1]` at `24` against
`40`. -/
theorem pin104 : (dataB 3).c2N [1,0,0] = 24 := by decide +kernel
/-- `G_2`'s short dominant root at `[1:2]` (`lem:casfloor`). -/
theorem pin105 : (dataG2).c2N [1,0] = 24 ∧ (dataG2).c2D = 48 := by decide +kernel

theorem pin106 : (dataB 3).dual [1,2,1] = [1,2,1] := by decide +kernel
theorem pin107 : (dataD 4).dual [0,0,1,0] = [0,0,1,0] := by decide +kernel
theorem pin108 : (dataD 5).dual [0,0,0,1,0] = [0,0,0,0,1] := by decide +kernel
theorem pin109 : (dataD 5).dual [0,0,0,0,1] = [0,0,0,1,0] := by decide +kernel
theorem pin110 : (dataE6).dual [1,0,0,0,0,0] = [0,0,0,0,0,1] := by decide +kernel
theorem pin111 : (dataE6).dual [0,0,1,0,0,0] = [0,0,0,0,1,0] := by decide +kernel
theorem pin112 : (dataE7).dual [0,0,0,0,0,0,1] = [0,0,0,0,0,0,1] := by decide +kernel

theorem pin113 : (dataB 3).clsFloorN 1 = (dataB 3).c2N [0,0,1] := by decide +kernel
theorem pin114 : (dataD 5).clsFloorN 2 = (dataD 5).c2N [1,0,0,0,0] := by decide +kernel

/-! The polynomial tier's ties: the instance fields against
`lem:serstable`(i)'s cleared pairs at the leading words, one
cross-multiplied read each (`con:fusion`'s series clause, the
fields at the rank against the stated pairs). -/

theorem pin115 : (dataB 3).c2N (serstable.member [1] 3) * serstable.casDenB 3
    = serstable.casNumB [1] 3 * (dataB 3).c2D := by decide +kernel
theorem pin116 : (dataC 3).c2N (serstable.member [2] 3) * serstable.casDenC 3
    = serstable.casNumC [2] 3 * (dataC 3).c2D := by decide +kernel
theorem pin117 : (dataB 3).dim (serstable.member [1] 3) * serstable.dimDenB [1] 3
    = serstable.dimNumB [1] 3 := by decide +kernel
theorem pin118 : (dataD 4).dim (serstable.member [1,1] 4) * serstable.dimDenD [1,1] 4
    = serstable.dimNumD [1,1] 4 := by decide +kernel

/-! ## The committed refusals

The involution's exchange at `D_5` is load-bearing: the identity
involution refuses the dual-class law at the spinor.  The Casimir
field is load-bearing in the drift: the flattened read refuses.
The walks' fuel is load-bearing: the starved closure refuses the
Cartan strictness at `B_2`'s own data. -/

theorem pin119 : ¬ clsDualLaw { dataD 5 with dual := fun a => a }
    [0,0,0,1,0] := by decide +kernel
theorem pin120 : ¬ driftLaw { dataB 2 with c2N := fun _ => 1 } [0,2] := by decide +kernel
theorem pin121 : ¬ cartanLaw
    (dataOf (sertables.tableB 2) (gramOf (sertables.tableB 2)) 0
      (fusion.clsB 2) (fun x y => (x + y) % 2) (fun _ => 0) (fiber.presNone _))
    [0,2] [0,2] := by decide +kernel
theorem pin122 : (dataB 2).residue = 2 ∧ (dataC 3).residue = 3 ∧ (dataD 4).residue = 5 := by
  decide +kernel

/-! The coroot carrier's shape, and the member cutoff laws at
every rank and cutoff. The constructor proofs read the finite box
and its filter; the displayed count and involution data are fixed.
-/

theorem pin123 : padN 3 [2, 1, 0] = [2, 1, 0] := padN_of_length 3 _ rfl
theorem pin124 : (padN 4 [2, 1]).length = 4 := padN_length 4 [2, 1]
theorem pin125 : padN 4 [2, 1] = [2, 1, 0, 0]
    ∧ padN 2 [2, 1, 7] = [2, 1] := by decide +kernel
theorem pin126 : ¬ padN 2 [2, 1, 7] = [2, 1, 7] := by decide +kernel

theorem pin127 (l k : Nat) : belowSound (dataB l) k := by
  apply belowSound_dataOf
theorem pin128 (l k : Nat) : belowSound (dataC l) k := by
  apply belowSound_dataOf
theorem pin129 (l k : Nat) : belowSound (dataD l) k := by
  apply belowSound_dataOf
theorem pin130 (k : Nat) : belowSound dataG2 k := by
  apply belowSound_dataOf (fuel := 16) (cls := fun _ => 0)
    (clsAdd := fun _ _ => 0) (clsFloorN := fun _ => 0) (P := dataG2.pres)
theorem pin131 (k : Nat) : belowSound dataF4 k := by
  apply belowSound_dataOf (fuel := 1200) (cls := fun _ => 0)
    (clsAdd := fun _ _ => 0) (clsFloorN := fun _ => 0) (P := dataF4.pres)
theorem pin132 (k : Nat) : belowSound dataE6 k := by apply belowSound_dataOf
theorem pin133 (k : Nat) : belowSound dataE7 k := by apply belowSound_dataOf
theorem pin134 (k : Nat) : belowSound dataE8 k := by
  apply belowSound_dataOf (fuel := 696729600) (cls := fun _ => 0)
    (clsAdd := fun _ _ => 0) (clsFloorN := fun _ => 0) (P := dataE8.pres)

theorem pin135 (l k : Nat) : belowNonunit (dataB l) k := by
  apply belowNonunit_dataOf
theorem pin136 (l k : Nat) : belowNonunit (dataC l) k := by
  apply belowNonunit_dataOf
theorem pin137 (l k : Nat) : belowNonunit (dataD l) k := by
  apply belowNonunit_dataOf
theorem pin138 (k : Nat) : belowNonunit dataG2 k := by apply belowNonunit_dataOf
theorem pin139 (k : Nat) : belowNonunit dataF4 k := by apply belowNonunit_dataOf
theorem pin140 (k : Nat) : belowNonunit dataE6 k := by apply belowNonunit_dataOf
theorem pin141 (k : Nat) : belowNonunit dataE7 k := by apply belowNonunit_dataOf
theorem pin142 (k : Nat) : belowNonunit dataE8 k := by apply belowNonunit_dataOf

theorem pin143 (l k : Nat) : distinctList ((dataB l).unit :: (dataB l).below k) := by
  apply below_distinct_dataOf
theorem pin144 (l k : Nat) : distinctList ((dataC l).unit :: (dataC l).below k) := by
  apply below_distinct_dataOf
theorem pin145 (l k : Nat) : distinctList ((dataD l).unit :: (dataD l).below k) := by
  apply below_distinct_dataOf
theorem pin146 (k : Nat) : distinctList (dataE8.unit :: dataE8.below k) := by
  apply below_distinct_dataOf

theorem pin147 : ¬ belowSound { dataB 2 with below := fun _ => [[0, 1]] } 0 := by
  decide +kernel
theorem pin148 : ¬ belowNonunit { dataG2 with below := fun _ => [[0, 0]] } 0 := by
  decide +kernel
theorem pin149 : ¬ distinctList ([[0, 1], [0, 1]] : List (List Nat)) := by
  decide +kernel

theorem pin150 (l : Nat) (a b c : List Nat) (hc : c ∈ (dataB l).row a b) :
    0 < (dataB l).count a b c := by
  apply row_count_pos_dataOf
  exact hc
theorem pin151 (l : Nat) (a b c : List Nat) (hc : c ∈ (dataC l).row a b) :
    0 < (dataC l).count a b c := by
  apply row_count_pos_dataOf
  exact hc
theorem pin152 (l : Nat) (a b c : List Nat) (hc : c ∈ (dataD l).row a b) :
    0 < (dataD l).count a b c := by
  apply row_count_pos_dataOf
  exact hc
theorem pin153 (a b c : List Nat) (hc : c ∈ dataE6.row a b) :
    0 < dataE6.count a b c := by
  apply row_count_pos_dataOf
  exact hc
theorem pin154 (l : Nat) (a b : List Nat) : distinctList ((dataB l).row a b) := by
  apply row_distinct_dataOf
theorem pin155 (l : Nat) (a b : List Nat) : distinctList ((dataC l).row a b) := by
  apply row_distinct_dataOf
theorem pin156 (l : Nat) (a b : List Nat) : distinctList ((dataD l).row a b) := by
  apply row_distinct_dataOf
theorem pin157 (a b : List Nat) : distinctList (dataG2.row a b) := by
  apply row_distinct_dataOf (cls := fun _ => 0)
    (clsAdd := fun _ _ => 0) (clsFloorN := fun _ => 0) (P := dataG2.pres)

/-! The produced families' shape reads and the returned dominance
key, with the width, canonical input and returned-output conditions
isolated at their refusals. -/

theorem pin158 (t : gentable.Table) (G : elim.Mat) (fuel : Nat) (a : List Nat) :
    memberchar.mShapeRead t (multFam t G fuel a) := by apply multFam_shape
theorem pin159 (t : gentable.Table) (fuel : Nat) (v : List BPair)
    (hv : v.length = t.rank) : memberchar.mShapeRead t (orbitSet t fuel v) :=
  orbitSet_shape t fuel v hv
theorem pin160 (t : gentable.Table) (fuel : Nat) (v : List BPair)
    (hv : v.length = t.rank) : sertables.wShapeRead t (orbitFam t fuel v) :=
  orbitFam_shape t fuel v hv

theorem pin161 (fuel : Nat) : domWalk sertables.tableG2 fuel
    [BPair.ofNat 1, BPair.ofNat 2] = [BPair.ofNat 1, BPair.ofNat 2] :=
  domWalk_of_nonneg _ _ _ (by decide +kernel)
theorem pin162 : memberchar.lamRead sertables.tableG2
    (domWalk sertables.tableG2 0 [BPair.ofNat 1, BPair.ofNat 2]) :=
  domWalk_lam _ _ _ rfl (by decide +kernel) (by decide +kernel)
theorem pin163 : ¬ memberchar.lamRead sertables.tableG2
    (domWalk sertables.tableG2 0 [BPair.ofNat 1]) := by decide +kernel
theorem pin164 : ¬ memberchar.lamRead sertables.tableG2
    (domWalk sertables.tableG2 0 [⟨3, 2⟩, BPair.unit]) := by decide +kernel
theorem pin165 : domWalk sertables.tableG2 0 [⟨1, 2⟩, BPair.unit] = []
    ∧ ¬ memberchar.lamRead sertables.tableG2
      (domWalk sertables.tableG2 0 [⟨1, 2⟩, BPair.unit]) := by decide +kernel

theorem pin166 : (dualM sertables.tableG2 16 [1, 0]).length = sertables.tableG2.rank :=
  dualM_length _ _ _ rfl (by decide +kernel)
theorem pin167 : ¬ (dualM sertables.tableG2 0 [1, 0]).length = sertables.tableG2.rank := by
  decide +kernel
theorem pin168 : domWalk sertables.tableG2 1
      (poly.pnorm (poly.neg (shiftV sertables.tableG2 [0]))) ≠ []
    ∧ ¬ (dualM sertables.tableG2 1 [0]).length = sertables.tableG2.rank := by
  decide +kernel
theorem pin169 : ¬ memberchar.mShapeRead sertables.tableG2
    (orbitSet sertables.tableG2 1 []) := by decide +kernel
theorem pin170 : ¬ sertables.wShapeRead sertables.tableG2
    (orbitFam sertables.tableG2 1 []) := by decide +kernel

/-! The orbit queue's completed reads: the seed, reflection
closure, and one result at every larger step bound. The vacant
result at a starved queue separates completion from shape. -/

theorem pin171 (t : gentable.Table) (fuel : Nat) (v w : List BPair)
    (hw : w ∈ orbitSet t fuel v) (i : Nat) (hi : i < t.rank) :
    assembly.reflF t i w ∈ orbitSet t fuel v := orbitSet_closed t fuel v w hw i hi
theorem pin172 : poly.pnorm [BPair.ofNat 1, BPair.unit]
    ∈ orbitSet sertables.tableG2 16 [BPair.ofNat 1, BPair.unit] :=
  orbitSet_seed _ _ _ (by decide +kernel)
theorem pin173 : (poly.pnorm [BPair.ofNat 1, BPair.ofNat 1], false)
    ∈ orbitFam sertables.tableG2 16 [BPair.ofNat 1, BPair.ofNat 1] :=
  orbitFam_seed _ _ _ (by decide +kernel)
theorem pin174 (extra : Nat) :
    orbitSet sertables.tableG2 (16 + extra) [BPair.ofNat 1, BPair.unit]
      = orbitSet sertables.tableG2 16 [BPair.ofNat 1, BPair.unit] :=
  orbitSet_more _ _ _ _ (by decide +kernel)
theorem pin175 (extra : Nat) :
    orbitFam sertables.tableG2 (16 + extra) [BPair.ofNat 1, BPair.ofNat 1]
      = orbitFam sertables.tableG2 16 [BPair.ofNat 1, BPair.ofNat 1] :=
  orbitFam_more _ _ _ _ (by decide +kernel)
theorem pin176 : orbitSet sertables.tableG2 0 [BPair.ofNat 1, BPair.unit] = []
    ∧ orbitSet sertables.tableG2 16 [BPair.ofNat 1, BPair.unit] ≠ [] := by
  decide +kernel
theorem pin177 : orbitFam sertables.tableG2 0 [BPair.ofNat 1, BPair.ofNat 1] = []
    ∧ orbitFam sertables.tableG2 16 [BPair.ofNat 1, BPair.ofNat 1] ≠ [] := by
  decide +kernel
theorem pin178 : orbitSet (gentable.tableA 0) 1 [BPair.ofNat 1] = [[BPair.ofNat 1]]
    ∧ assembly.reflF (gentable.tableA 0) 0 [BPair.ofNat 1] = []
    ∧ countOf [] (orbitSet (gentable.tableA 0) 1 [BPair.ofNat 1]) = 0 := by
  decide +kernel
theorem pin179 : ¬ (poly.pnorm [BPair.ofNat 1, BPair.unit]
    ∈ orbitSet sertables.tableG2 0 [BPair.ofNat 1, BPair.unit]) := by
  intro h
  exact nomatch h

/-! The cleared rho-dot gap completes a walk inside its finite
orbit; the table reads are the displayed G2 data. -/

theorem pin180 :
    domWalk sertables.tableG2 20 [⟨1, 2⟩, BPair.unit]
      ∈ orbitSet sertables.tableG2 16 [⟨1, 2⟩, BPair.unit]
    ∧ memberchar.lamRead sertables.tableG2
      (domWalk sertables.tableG2 20 [⟨1, 2⟩, BPair.unit]) := by
  apply domWalk_complete sertables.tableG2 sertables.fundG2
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (orbitSet sertables.tableG2 16 [⟨1, 2⟩, BPair.unit])
    (orbitSet_shape _ _ _ rfl)
    (fun w hw i hi => orbitSet_closed _ _ _ w hw i hi)
    (BPair.ofNat 10) (by decide +kernel) 20
  · exact orbitSet_seed _ _ _ (by decide +kernel)
  · decide +kernel
theorem pin181 : domWalk sertables.tableG2 20 [⟨1, 2⟩, BPair.unit]
    = [BPair.ofNat 1, BPair.unit] := by decide +kernel
theorem pin182 : ¬ (BPair.ofNat 10 ≤ sertables.dotB sertables.fundG2
    [⟨1, 2⟩, BPair.unit] (sertables.rhoV sertables.tableG2) + BPair.ofNat 0) := by
  decide +kernel
theorem pin183 : ¬ (∀ w ∈ orbitSet sertables.tableG2 16 [⟨1, 2⟩, BPair.unit],
    sertables.dotB sertables.fundG2 w (sertables.rhoV sertables.tableG2)
      ≤ BPair.ofNat 9) := by decide +kernel

theorem pin184 (t : gentable.Table) (fuel : Nat) (v : List BPair) :
    (orbitFam t fuel v).map Prod.fst = orbitSet t fuel v := orbitFam_keys t fuel v
theorem pin185 : (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)).map Prod.fst
    = orbitSet sertables.tableG2 16 (sertables.rhoV sertables.tableG2) := by
  decide +kernel
theorem pin186 (t : gentable.Table) (fuel : Nat) (v : List BPair)
    (S : List (List BPair)) (hv : poly.pnorm v ∈ S)
    (hc : ∀ w ∈ S, ∀ i, i < t.rank → assembly.reflF t i w ∈ S) :
    ∀ w ∈ orbitSet t fuel v, w ∈ S := orbitSet_least t fuel v S hv hc

theorem pin187 : domWalk sertables.tableG2 6 [⟨1, 2⟩, BPair.unit]
      ∈ orbitSet sertables.tableG2 16 [⟨1, 2⟩, BPair.unit]
    ∧ memberchar.lamRead sertables.tableG2
      (domWalk sertables.tableG2 6 [⟨1, 2⟩, BPair.unit]) := by
  apply domWalk_finite sertables.tableG2 sertables.fundG2
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (orbitSet sertables.tableG2 16 [⟨1, 2⟩, BPair.unit])
    (orbitSet_shape _ _ _ rfl)
    (fun w hw i hi => orbitSet_closed _ _ _ w hw i hi) 6 (by decide +kernel)
  exact orbitSet_seed _ _ _ (by decide +kernel)
theorem pin188 : (orbitSet sertables.tableG2 16 [⟨1, 2⟩, BPair.unit]).length = 6
    ∧ domWalk sertables.tableG2 6 [⟨1, 2⟩, BPair.unit] = [BPair.ofNat 1, BPair.unit] := by
  decide +kernel

/-! The reference orbit's count completes both queues, with each
returned key at multiplicity one, including a seed on a wall. -/

theorem pin189 : orbitSet sertables.tableG2 6 [BPair.ofNat 1, BPair.unit] ≠ []
    ∧ distinctList (orbitSet sertables.tableG2 6 [BPair.ofNat 1, BPair.unit]) := by
  apply orbitSet_complete sertables.tableG2
    (orbitSet sertables.tableG2 16 [BPair.ofNat 1, BPair.unit])
    (by decide +kernel)
    (fun w hw i hi => orbitSet_closed _ _ _ w hw i hi)
    (by decide +kernel) 6 (by decide +kernel)
  exact orbitSet_seed _ _ _ (by decide +kernel)
theorem pin190 : orbitFam sertables.tableG2 12 (sertables.rhoV sertables.tableG2) ≠ []
    ∧ distinctList ((orbitFam sertables.tableG2 12
      (sertables.rhoV sertables.tableG2)).map Prod.fst) := by
  apply orbitFam_complete sertables.tableG2
    (orbitSet sertables.tableG2 16 (sertables.rhoV sertables.tableG2))
    (by decide +kernel)
    (fun w hw i hi => orbitSet_closed _ _ _ w hw i hi)
    (by decide +kernel) 12 (by decide +kernel)
  exact orbitSet_seed _ _ _ (by decide +kernel)
theorem pin191 : orbitSet sertables.tableG2 5 [BPair.ofNat 1, BPair.unit] = []
    ∧ (orbitSet sertables.tableG2 6 [BPair.ofNat 1, BPair.unit]).length = 6 := by
  decide +kernel
theorem pin192 : orbitFam sertables.tableG2 11 (sertables.rhoV sertables.tableG2) = []
    ∧ (orbitFam sertables.tableG2 12 (sertables.rhoV sertables.tableG2)).length = 12 := by
  decide +kernel

/-! The produced families satisfy the character kit's symmetry,
graded closure and top reads at the reference orbit's bound. -/

theorem pin193 : memberchar.symRead sertables.tableG2
    (orbitSet sertables.tableG2 6 [BPair.ofNat 1, BPair.unit]) := by
  apply orbitSet_sym sertables.tableG2
    (orbitSet sertables.tableG2 16 [BPair.ofNat 1, BPair.unit])
    (by decide +kernel)
    (fun w hw i hi => orbitSet_closed _ _ _ w hw i hi)
    (by decide +kernel) 6
  · exact orbitSet_seed _ _ _ (by decide +kernel)
  · rfl
theorem pin194 : assembly.wCloseRead sertables.tableG2
    (orbitFam sertables.tableG2 12 (sertables.rhoV sertables.tableG2)) := by
  apply orbitFam_close sertables.tableG2
    (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2))
    (orbitFam_shape _ _ _ rfl) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 12
  exact orbitFam_seed _ _ _ (by decide +kernel)
theorem pin195 : assembly.wTopRead sertables.tableG2
    (orbitFam sertables.tableG2 12 (sertables.rhoV sertables.tableG2)) :=
  orbitFam_top _ _ _ pin190.1
theorem pin196 : ∀ p ∈ domFam sertables.tableG2
    (sertables.gramRows sertables.tableG2 sertables.adjG2) 16 [1, 0],
    memberchar.symRead sertables.tableG2 (orbitSet sertables.tableG2 16 (natV p.1)) := by
  decide +kernel
theorem pin197 : memberchar.symRead sertables.tableG2
    (multFam sertables.tableG2 (sertables.gramRows sertables.tableG2 sertables.adjG2) 16 [1, 0]) :=
  multFam_sym _ _ _ _ (by decide +kernel) pin196
theorem pin198 : (multFam sertables.tableG2
    (sertables.gramRows sertables.tableG2 sertables.adjG2) 16 [1, 0]).length = 7 := by
  decide +kernel

/-- Two coincident simple rows, whose images agree off their input
key: the separation condition's refusal at a finite closed list. -/
private def coincidentLetters : gentable.Table :=
  { gentable.tableA 2 with
    cartan := [[BPair.ofNat 2, BPair.ofNat 2], [BPair.ofNat 2, BPair.ofNat 2]] }

theorem pin199 : distinctList
      [[BPair.ofNat 1, BPair.ofNat 1], [⟨1, 2⟩, ⟨1, 2⟩]]
    ∧ (∀ w ∈ [[BPair.ofNat 1, BPair.ofNat 1], [⟨1, 2⟩, ⟨1, 2⟩]],
      ∀ i, i < 2 → 0 < countOf (assembly.reflF coincidentLetters i w)
        [[BPair.ofNat 1, BPair.ofNat 1], [⟨1, 2⟩, ⟨1, 2⟩]]) := by decide +kernel
theorem pin200 : orbitSet coincidentLetters 2 [BPair.ofNat 1, BPair.ofNat 1] = []
    ∧ (orbitSet coincidentLetters 3 [BPair.ofNat 1, BPair.ofNat 1]).length = 3
    ∧ ¬ distinctList (orbitSet coincidentLetters 3 [BPair.ofNat 1, BPair.ofNat 1]) := by
  decide +kernel
theorem pin201 : assembly.reflF coincidentLetters 0 [BPair.ofNat 1, BPair.ofNat 1]
      = assembly.reflF coincidentLetters 1 [BPair.ofNat 1, BPair.ofNat 1]
    ∧ assembly.reflF coincidentLetters 0 [BPair.ofNat 1, BPair.ofNat 1]
      ≠ [BPair.ofNat 1, BPair.ofNat 1] := by decide +kernel

/-! The fixed members' positivity and nesting laws at their full
label and cutoff quantifiers, at the displayed natural Gram rows. -/

theorem pin202 (a : List Nat) : casPos dataG2 a := casPos_dataG2 a
theorem pin203 (a : List Nat) : casPos dataF4 a := casPos_dataF4 a
theorem pin204 (a : List Nat) : casPos dataE6 a := casPos_dataE6 a
theorem pin205 (a : List Nat) : casPos dataE7 a := casPos_dataE7 a
theorem pin206 (a : List Nat) : casPos dataE8 a := casPos_dataE8 a
theorem pin207 (k k' : Nat) (h : k ≤ k') : belowNest dataG2 k k' := belowNest_dataG2 k k' h
theorem pin208 (k k' : Nat) (h : k ≤ k') : belowNest dataF4 k k' := belowNest_dataF4 k k' h
theorem pin209 (k k' : Nat) (h : k ≤ k') : belowNest dataE6 k k' := belowNest_dataE6 k k' h
theorem pin210 (k k' : Nat) (h : k ≤ k') : belowNest dataE7 k k' := belowNest_dataE7 k k' h
theorem pin211 (k k' : Nat) (h : k ≤ k') : belowNest dataE8 k k' := belowNest_dataE8 k k' h

theorem pin212 : c2M sertables.tableG2 ([[4, 6], [6, 12]].map natV) [1, 0]
    = dotNat [1, 0] ([ [4, 6], [6, 12] ].map (fun r => dotNat r [3, 2])) :=
  c2M_nat _ _ _ rfl
theorem pin213 : c2M (gentable.tableA 1) ([[0, 1], [0, 1]].map natV) [0, 1] = 0
    ∧ dotNat [0, 1] ([[0, 1], [0, 1]].map (fun r => dotNat r [2, 3])) = 3 := by
  decide +kernel
theorem pin214 : ¬ casPos (dataOf (gentable.tableA 1) ([[0]].map natV) 0
    (fun _ => 0) (fun _ _ => 0) (fun _ => 0) (fiber.presNone _)) [1] := by
  decide +kernel
theorem pin215 : ¬ casPos (dataOf (gentable.tableA 2) ([[1, 0]].map natV) 0
    (fun _ => 0) (fun _ _ => 0) (fun _ => 0) (fiber.presNone _)) [0, 1] := by
  decide +kernel
theorem pin216 : ¬ casPos (dataOf (gentable.tableA 2) ([[0, 0, 1], [0, 0, 1]].map natV) 0
    (fun _ => 0) (fun _ _ => 0) (fun _ => 0) (fiber.presNone _)) [1, 0] := by
  decide +kernel
theorem pin217 : ¬ belowNest dataG2 24 0 := by decide +kernel
theorem pin218 : dataG2.below 24 = [[1, 0]]
    ∧ dataG2.below 48 = [[0, 1], [1, 0]] := by decide +kernel
theorem pin219 : casPos dataG2 [1] ∧ casPos dataE8 [0, 0, 0, 0, 0, 0, 0, 1, 9] :=
  ⟨casPos_dataG2 [1], casPos_dataE8 [0, 0, 0, 0, 0, 0, 0, 1, 9]⟩
theorem pin220 : (2 * sumNat (getAt [] [[4, 6], [6, 12]] 1)) * getAt 0 [1, 2] 1
    ≤ c2M sertables.tableG2 ([[4, 6], [6, 12]].map natV) [1, 2] :=
  c2M_coordinate _ _ rfl (by decide +kernel) _ rfl 1 (by decide)
theorem pin221 : c2M sertables.tableG2 ([[4, 6], [6, 12]].map natV) [1, 2] = 168 := by
  decide +kernel

/-! The unit class groups' three laws and the G2 shifted dual walk
at arbitrary coroot coordinates. -/

theorem pin222 (a b : List Nat) : clsLaw dataG2 a b ∧ clsDualLaw dataG2 a ∧ clsThetaLaw dataG2 :=
  clsLaws_dataFixed sertables.tableG2 sertables.adjG2 16 dataG2.pres a b
theorem pin223 (a b : List Nat) : clsLaw dataF4 a b ∧ clsDualLaw dataF4 a ∧ clsThetaLaw dataF4 :=
  clsLaws_dataFixed sertables.tableF4 sertables.adjF4 1200 dataF4.pres a b
theorem pin224 (a b : List Nat) : clsLaw dataE8 a b ∧ clsDualLaw dataE8 a ∧ clsThetaLaw dataE8 :=
  clsLaws_dataFixed sertables.tableE8 sertables.adjE8 696729600 dataE8.pres a b
theorem pin225 : clsThetaLaw dataE6 ∧ clsThetaLaw dataE7 := ⟨clsThetaLaw_dataE6, clsThetaLaw_dataE7⟩
theorem pin226 (extra a b : Nat) : dualM sertables.tableG2 (extra + 6) [a, b] = [a, b] :=
  dualM_G2 extra a b
theorem pin227 (a : List Nat) : dataG2.dual a = padN 2 a := dual_dataG2 a
theorem pin228 (a : List Nat) : casDualLaw dataG2 a ∧ dimDualLaw dataG2 a :=
  ⟨casDualLaw_dataG2 a, dimDualLaw_dataG2 a⟩
theorem pin229 : thetaSelfDual dataG2 := thetaSelfDual_dataG2
theorem pin230 : dualM sertables.tableG2 6 [3, 4] = [3, 4] := by decide +kernel
theorem pin231 : dataG2.dual [2] = [2, 0] ∧ dataG2.dual [2, 3, 4] = [2, 3] := by
  decide +kernel
theorem pin232 : dualM sertables.tableG2 5 [0, 0] = []
    ∧ dualM sertables.tableG2 6 [0, 0] = [0, 0] := by decide +kernel

theorem pin233 : thetaSelfDual dataF4 := thetaSelfDual_dataF4
theorem pin234 : thetaSelfDual dataE6 := thetaSelfDual_dataE6
theorem pin235 : thetaSelfDual dataE7 := thetaSelfDual_dataE7
theorem pin236 : thetaSelfDual dataE8 := thetaSelfDual_dataE8

/-! A shape-correct singleton on a lower side is smaller than its
reflection closure; its own count does not complete either walk. -/

theorem pin237 : memberchar.mShapeRead sertables.tableG2 [[⟨1, 2⟩, BPair.unit]]
    ∧ domWalk sertables.tableG2 1 [⟨1, 2⟩, BPair.unit] = []
    ∧ orbitSet sertables.tableG2 1 [⟨1, 2⟩, BPair.unit] = []
    ∧ countOf (assembly.reflF sertables.tableG2 0 [⟨1, 2⟩, BPair.unit])
      [[⟨1, 2⟩, BPair.unit]] = 0 := by decide +kernel
theorem pin238 : ¬ memberchar.lamRead sertables.tableG2
    (domWalk sertables.tableG2 1 [⟨1, 2⟩, BPair.unit]) := by decide +kernel
theorem pin239 : orbitSet sertables.tableG2 0 [BPair.ofNat 1, BPair.unit] = []
    ∧ countOf [BPair.ofNat 1, BPair.unit] ([] : List (List BPair)) = 0 := by decide +kernel

/-! The displayed Weyl references fit the constructors' stored
step counts, including singular references with repeated images. -/

theorem pin240 (l : Nat) : fusion.wFuel l = 2 ^ l * ground.factorial l + l := fusion.wFuel_eq l
theorem pin241 (l : Nat) (v : List BPair) :
    (sertables.serWeylB l v).length ≤ fusion.wFuel l
      ∧ (ground.dedupF ((sertables.serWeylB l v).map Prod.fst)).length ≤ fusion.wFuel l :=
  fusion.serWeylB_fuel l v
theorem pin242 (l : Nat) (v : List BPair) :
    (sertables.serWeylC l v).length ≤ fusion.wFuel l
      ∧ (ground.dedupF ((sertables.serWeylC l v).map Prod.fst)).length ≤ fusion.wFuel l :=
  fusion.serWeylC_fuel l v
theorem pin243 (l : Nat) (v : List BPair) :
    (sertables.serWeylD l v).length ≤ fusion.wFuel l
      ∧ (ground.dedupF ((sertables.serWeylD l v).map Prod.fst)).length ≤ fusion.wFuel l :=
  fusion.serWeylD_fuel l v
theorem pin244 : fusion.wFuel 2 = 10 ∧ fusion.wFuel 3 = 51 ∧ fusion.wFuel 4 = 388 := by
  decide +kernel
theorem pin245 : (sertables.serWeylD 4 (sertables.rhoV (sertables.tableD 4))).length = 192 :=
  sertables.serWeylD_length 3 _
theorem pin246 : ground.distinctList ((sertables.serWeylB 3
    (shiftV (sertables.tableB 3) [2, 0, 1])).map Prod.fst) := by
  apply sertables.serWeylB_regular 3 (by decide) _ rfl
  decide +kernel
theorem pin247 : ground.distinctList ((sertables.serWeylC 3
    (shiftV (sertables.tableC 3) [2, 0, 1])).map Prod.fst) := by
  apply sertables.serWeylC_regular 3 (by decide) _ rfl
  decide +kernel

/-! The stored bounds complete the actual B and C queues for
every seed of the declared width, without regularity assumptions. -/

theorem pin248 (l : Nat) (hl : 0 < l) (v : List BPair) (hv : v.length = l) :
    (orbitSet (sertables.tableB l) (fusion.wFuel l) v ≠ []
      ∧ ground.distinctList (orbitSet (sertables.tableB l) (fusion.wFuel l) v))
    ∧ (orbitFam (sertables.tableB l) (fusion.wFuel l) v ≠ []
      ∧ ground.distinctList ((orbitFam (sertables.tableB l) (fusion.wFuel l) v).map Prod.fst)) :=
  orbit_complete_B l hl v hv
theorem pin249 (l : Nat) (hl : 0 < l) (v : List BPair) (hv : v.length = l) :
    (orbitSet (sertables.tableC l) (fusion.wFuel l) v ≠ []
      ∧ ground.distinctList (orbitSet (sertables.tableC l) (fusion.wFuel l) v))
    ∧ (orbitFam (sertables.tableC l) (fusion.wFuel l) v ≠ []
      ∧ ground.distinctList ((orbitFam (sertables.tableC l) (fusion.wFuel l) v).map Prod.fst)) :=
  orbit_complete_C l hl v hv
theorem pin250 : orbitSet (sertables.tableC 2) (fusion.wFuel 2) [BPair.unit, BPair.unit]
      = [[BPair.unit, BPair.unit]]
    ∧ orbitFam (sertables.tableB 2) (fusion.wFuel 2) [BPair.unit, BPair.unit]
      = [([BPair.unit, BPair.unit], false)] := by decide +kernel
theorem pin251 : orbitSet (sertables.tableC 1) 1 [BPair.ofNat 1] = []
    ∧ orbitFam (sertables.tableC 1) 1 [BPair.ofNat 1] = [] := by decide +kernel
theorem pin252 : (orbitSet (sertables.tableC 1) 2 [BPair.ofNat 1]).length = 2
    ∧ (orbitFam (sertables.tableC 1) 2 [BPair.ofNat 1]).length = 2 := by decide +kernel
theorem pin253 : ¬ ground.distinctList ((sertables.serWeylC 2 [BPair.unit, BPair.unit]).map Prod.fst)
    ∧ (ground.dedupF ((sertables.serWeylC 2 [BPair.unit, BPair.unit]).map Prod.fst)).length = 1 := by
  decide +kernel
theorem pin254 : (orbitSet (sertables.tableB 2) (fusion.wFuel 2) [BPair.ofNat 1, BPair.unit]).length = 4
    ∧ (orbitFam (sertables.tableC 2) (fusion.wFuel 2) [BPair.ofNat 1, BPair.ofNat 1]).length = 8 := by
  decide +kernel

/-! D's stored bound completes both queues at regular and
singular seeds, the displayed even-sign reference deduplicated. -/

theorem pin255 (l : Nat) (hl : 2 ≤ l) (v : List BPair) (hv : v.length = l) :
    (orbitSet (sertables.tableD l) (fusion.wFuel l) v ≠ []
      ∧ ground.distinctList (orbitSet (sertables.tableD l) (fusion.wFuel l) v))
    ∧ (orbitFam (sertables.tableD l) (fusion.wFuel l) v ≠ []
      ∧ ground.distinctList ((orbitFam (sertables.tableD l) (fusion.wFuel l) v).map Prod.fst)) :=
  orbit_complete_D l hl v hv
theorem pin256 : orbitSet (sertables.tableD 3) (fusion.wFuel 3) [BPair.unit, BPair.unit, BPair.unit]
      = [[BPair.unit, BPair.unit, BPair.unit]]
    ∧ orbitFam (sertables.tableD 3) (fusion.wFuel 3) [BPair.unit, BPair.unit, BPair.unit]
      = [([BPair.unit, BPair.unit, BPair.unit], false)] := by decide +kernel
theorem pin257 : (orbitSet (sertables.tableD 2) (fusion.wFuel 2) [BPair.ofNat 1, BPair.ofNat 1]).length = 4
    ∧ (orbitFam (sertables.tableD 2) (fusion.wFuel 2) [BPair.ofNat 1, BPair.ofNat 1]).length = 4 := by decide +kernel

/-! The regular queue reads include the grading needed by the
character fold, as well as completion and distinct keys. -/

theorem pin258 (l : Nat) (hl : 0 < l) (v : List BPair) (hv : v.length = l)
    (hp : ∀ i, i < l → BPair.unit < ground.getAt BPair.unit v i) :
    sertables.wShapeRead (sertables.tableB l) (orbitFam (sertables.tableB l) (fusion.wFuel l) v)
      ∧ assembly.wCloseRead (sertables.tableB l) (orbitFam (sertables.tableB l) (fusion.wFuel l) v)
      ∧ assembly.wTopAt (orbitFam (sertables.tableB l) (fusion.wFuel l) v) (poly.pnorm v) :=
  orbitFam_reads_B l hl v hv hp
theorem pin259 (l : Nat) (hl : 0 < l) (v : List BPair) (hv : v.length = l)
    (hp : ∀ i, i < l → BPair.unit < ground.getAt BPair.unit v i) :
    sertables.wShapeRead (sertables.tableC l) (orbitFam (sertables.tableC l) (fusion.wFuel l) v)
      ∧ assembly.wCloseRead (sertables.tableC l) (orbitFam (sertables.tableC l) (fusion.wFuel l) v)
      ∧ assembly.wTopAt (orbitFam (sertables.tableC l) (fusion.wFuel l) v) (poly.pnorm v) :=
  orbitFam_reads_C l hl v hv hp
theorem pin260 (l : Nat) (hl : 2 ≤ l) (v : List BPair) (hv : v.length = l)
    (hp : ∀ i, i < l → BPair.unit < ground.getAt BPair.unit v i) :
    sertables.wShapeRead (sertables.tableD l) (orbitFam (sertables.tableD l) (fusion.wFuel l) v)
      ∧ assembly.wCloseRead (sertables.tableD l) (orbitFam (sertables.tableD l) (fusion.wFuel l) v)
      ∧ assembly.wTopAt (orbitFam (sertables.tableD l) (fusion.wFuel l) v) (poly.pnorm v) :=
  orbitFam_reads_D l hl v hv hp
theorem pin261 : ¬ assembly.wCloseRead (sertables.tableD 3)
    (orbitFam (sertables.tableD 3) (fusion.wFuel 3) [BPair.unit, BPair.unit, BPair.unit]) := by decide +kernel

/-! The actual dominance walks complete at the stored bounds,
and their returned keys belong to the displayed orbit. -/

theorem pin262 (l : Nat) (hl : 0 < l) (v : List BPair) (hv : v.length = l) :
    domWalk (sertables.tableB l) (fusion.wFuel l) (poly.pnorm v)
        ∈ (sertables.serWeylB l v).map Prod.fst
      ∧ memberchar.lamRead (sertables.tableB l)
        (domWalk (sertables.tableB l) (fusion.wFuel l) (poly.pnorm v)) := domWalk_complete_B l hl v hv
theorem pin263 (l : Nat) (hl : 0 < l) (v : List BPair) (hv : v.length = l) :
    domWalk (sertables.tableC l) (fusion.wFuel l) (poly.pnorm v)
        ∈ (sertables.serWeylC l v).map Prod.fst
      ∧ memberchar.lamRead (sertables.tableC l)
        (domWalk (sertables.tableC l) (fusion.wFuel l) (poly.pnorm v)) := domWalk_complete_C l hl v hv
theorem pin264 (l : Nat) (hl : 2 ≤ l) (v : List BPair) (hv : v.length = l) :
    domWalk (sertables.tableD l) (fusion.wFuel l) (poly.pnorm v)
        ∈ (sertables.serWeylD l v).map Prod.fst
      ∧ memberchar.lamRead (sertables.tableD l)
        (domWalk (sertables.tableD l) (fusion.wFuel l) (poly.pnorm v)) := domWalk_complete_D l hl v hv
theorem pin265 : domWalk (sertables.tableC 1) 0 [⟨1, 3⟩] = []
    ∧ domWalk (sertables.tableC 1) (fusion.wFuel 1) (poly.pnorm [⟨1, 3⟩]) = [BPair.ofNat 2] := by decide +kernel
theorem pin266 : domWalk (sertables.tableD 3) (fusion.wFuel 3)
      [(BPair.ofNat 1).swap, (BPair.ofNat 1).swap, (BPair.ofNat 1).swap]
    = [BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1] := by decide +kernel
theorem pin267 : domWalk (sertables.tableB 2) (fusion.wFuel 2) [BPair.unit, BPair.unit]
    = [BPair.unit, BPair.unit] := by decide +kernel

theorem pin268 (l : Nat) (hl : 0 < l) (a : List Nat) : ((dataB l).dual a).length = l :=
  dual_length_dataB l hl a
theorem pin269 (l : Nat) (hl : 0 < l) (a : List Nat) : ((dataC l).dual a).length = l :=
  dual_length_dataC l hl a
theorem pin270 (l : Nat) (hl : 2 ≤ l) (a : List Nat) : ((dataD l).dual a).length = l :=
  dual_length_dataD l hl a
theorem pin271 : (dataB 2).dual [3] = [3, 0]
    ∧ (dataC 2).dual [2, 1, 7] = [2, 1]
    ∧ (dataD 3).dual [0, 1, 2] = [0, 2, 1] := by decide +kernel

/-! The actual duals at stored fuel, at all ranks and labels.
The formulas include padding, the D parity branch and involution. -/

theorem pin272 (l : Nat) (hl : 0 < l) (a : List Nat) :
    (dataB l).dual a = padN l a ∧ (dataC l).dual a = padN l a :=
  ⟨dual_dataB l hl a, dual_dataC l hl a⟩
theorem pin273 (l : Nat) (hl : 2 ≤ l) (a : List Nat) :
    (dataD l).dual a = if l % 2 = 0 then padN l a else ground.adjSwap (l - 2) (padN l a) :=
  dual_dataD l hl a
theorem pin274 (l : Nat) (hl : 0 < l) (a : List Nat) :
    (dataB l).dual ((dataB l).dual a) = padN l a
      ∧ (dataC l).dual ((dataC l).dual a) = padN l a :=
  ⟨dual_invol_dataB l hl a, dual_invol_dataC l hl a⟩
theorem pin275 (l : Nat) (hl : 2 ≤ l) (a : List Nat) :
    (dataD l).dual ((dataD l).dual a) = padN l a := dual_invol_dataD l hl a
theorem pin276 (l : Nat) (hl : 0 < l) (a : List Nat) :
    casDualLaw (dataB l) a ∧ dimDualLaw (dataB l) a :=
  ⟨casDualLaw_dataB l hl a, dimDualLaw_dataB l hl a⟩
theorem pin277 (l : Nat) (hl : 0 < l) (a : List Nat) :
    casDualLaw (dataC l) a ∧ dimDualLaw (dataC l) a :=
  ⟨casDualLaw_dataC l hl a, dimDualLaw_dataC l hl a⟩
theorem pin278 (l : Nat) (hl : 2 ≤ l) (a : List Nat) :
    casDualLaw (dataD l) a ∧ dimDualLaw (dataD l) a :=
  ⟨casDualLaw_dataD l hl a, dimDualLaw_dataD l hl a⟩
theorem pin279 (a b : Nat) : (dataD 2).dual [a, b] = [a, b] := by
  rw [dual_dataD 2 (by decide), if_pos (by decide), padN_of_length 2 [a, b] rfl]
theorem pin280 (a : Nat) : (dataB 1).dual [a] = [a] ∧ (dataC 1).dual [a] = [a] := by
  rw [dual_dataB 1 (by decide), dual_dataC 1 (by decide), padN_of_length 1 [a] rfl]
  exact ⟨rfl, rfl⟩
theorem pin281 (a b c : Nat) : (dataD 3).dual [a, b, c] = [a, c, b] := by
  rw [dual_dataD 3 (by decide), if_neg (by decide), padN_of_length 3 [a, b, c] rfl]
  rfl
theorem pin282 : (dataD 3).dual [2, 4] = [2, 0, 4]
    ∧ (dataD 3).dual [2, 4, 5, 99] = [2, 5, 4] := by
  rw [dual_dataD 3 (by decide), dual_dataD 3 (by decide)]
  decide +kernel
theorem pin283 : (dataD 3).dual ((dataD 3).dual [2, 4]) ≠ [2, 4] := by
  rw [dual_invol_dataD 3 (by decide)]
  decide +kernel
theorem pin284 (a b c d : Nat) : (dataD 4).dual [a, b, c, d] = [a, b, c, d] := by
  rw [dual_dataD 4 (by decide), if_pos (by decide), padN_of_length 4 [a, b, c, d] rfl]
theorem pin285 : (dataD 3).dual [0, 1, 0] ≠ [0, 1, 0] := by
  rw [pin281]
  decide +kernel

/-! The D form uses the computed descent Gram. Its exchange
identity holds for the Gram itself and for arbitrary labels; an
asymmetric replacement matrix refuses the same quadratic read. -/

theorem pin286 (k : Nat) (a : List Nat) (ha : a.length = k + 2) :
    c2M (sertables.tableD (k + 2)) (gramOf (sertables.tableD (k + 2))) (ground.adjSwap k a)
      = c2M (sertables.tableD (k + 2)) (gramOf (sertables.tableD (k + 2))) a := c2M_forkSwap_D k a ha
theorem pin287 (k : Nat) (a : List Nat) (ha : a.length = k + 2) :
    dimM (sertables.tableD (k + 2)) (ground.adjSwap k a)
      = dimM (sertables.tableD (k + 2)) a := dimM_forkSwap_D k a ha
theorem pin288 (k i : Nat) (hi : i < k + 2) :
    poly.oneValue (ground.adjSwap k (getAt [] (gramOf (sertables.tableD (k + 2))) i))
      (getAt [] (gramOf (sertables.tableD (k + 2))) (ground.swapIx k (k + 1) i)) :=
  gramOf_forkSwap_D k i hi
theorem pin289 : c2M (sertables.tableD 3)
      [[BPair.ofNat 1, BPair.unit, BPair.unit], [BPair.unit, BPair.ofNat 2, BPair.unit],
        [BPair.unit, BPair.unit, BPair.ofNat 3]] [0, 1, 0]
    ≠ c2M (sertables.tableD 3)
      [[BPair.ofNat 1, BPair.unit, BPair.unit], [BPair.unit, BPair.ofNat 2, BPair.unit],
        [BPair.unit, BPair.unit, BPair.ofNat 3]] [0, 0, 1] := by decide +kernel
theorem pin290 : c2M (sertables.tableD 2) (gramOf (sertables.tableD 2)) [2, 3]
    = c2M (sertables.tableD 2) (gramOf (sertables.tableD 2)) [3, 2] := by
  exact (c2M_forkSwap_D 0 [2, 3] rfl).symm
theorem pin291 : dualM (sertables.tableD 3) 0 [1, 2, 3] = []
    ∧ dualM (sertables.tableD 3) (wFuel 3) [1, 2, 3] = [1, 3, 2] := by
  refine ⟨by decide +kernel, ?_⟩
  rw [dualM_D 1 [1, 2, 3] rfl]
  rfl

/-! The dominant return is determined by the orbit key alone,
including a start with odd reference grade and shifted balance
representatives. -/

theorem pin292 (l : Nat) (hl : 0 < l) (top v : List BPair) (htop : top.length = l)
    (hpos : ∀ i, i < l → BPair.unit < getAt BPair.unit top i)
    (hmem : poly.pnorm v ∈ (sertables.serWeylB l top).map Prod.fst) :
    domWalk (sertables.tableB l) (wFuel l) (poly.pnorm v) = poly.pnorm top :=
  domWalk_to_B l hl top v htop hpos hmem
theorem pin293 (l : Nat) (hl : 0 < l) (top v : List BPair) (htop : top.length = l)
    (hpos : ∀ i, i < l → BPair.unit < getAt BPair.unit top i)
    (hmem : poly.pnorm v ∈ (sertables.serWeylC l top).map Prod.fst) :
    domWalk (sertables.tableC l) (wFuel l) (poly.pnorm v) = poly.pnorm top :=
  domWalk_to_C l hl top v htop hpos hmem
theorem pin294 (l : Nat) (hl : 2 ≤ l) (top v : List BPair) (htop : top.length = l)
    (hpos : ∀ i, i < l → BPair.unit < getAt BPair.unit top i)
    (hmem : poly.pnorm v ∈ (sertables.serWeylD l top).map Prod.fst) :
    domWalk (sertables.tableD l) (wFuel l) (poly.pnorm v) = poly.pnorm top :=
  domWalk_to_D l hl top v htop hpos hmem
theorem pin295 : ground.countOf ([BPair.ofNat 2], false) (sertables.serWeylC 1 [(BPair.ofNat 2).swap]) = 0
    ∧ ground.countOf ([BPair.ofNat 2], true) (sertables.serWeylC 1 [(BPair.ofNat 2).swap]) = 1
    ∧ domWalk (sertables.tableC 1) (wFuel 1) [BPair.ofNat 2] = [BPair.ofNat 2] := by decide +kernel
theorem pin296 : domWalk (sertables.tableD 3) (wFuel 3) (poly.pnorm [⟨5, 3⟩, ⟨6, 3⟩, ⟨4, 3⟩])
    = [BPair.ofNat 2, BPair.ofNat 3, BPair.ofNat 1] := by decide +kernel

/-! The dual class law at the actual padded producers, with the
odd D spinor classes forming opposite elements of the four-cycle. -/

theorem pin297 (l : Nat) (hl : 0 < l) (a : List Nat) :
    clsDualLaw (dataB l) a ∧ clsDualLaw (dataC l) a :=
  ⟨clsDualLaw_dataB l hl a, clsDualLaw_dataC l hl a⟩
theorem pin298 (l : Nat) (hl : 2 ≤ l) (a : List Nat) :
    clsDualLaw (dataD l) a := clsDualLaw_dataD l hl a
theorem pin299 (k : Nat) (a : List Nat) (ha : a.length = k + 2) :
    (clsDOdd (k + 2) (ground.adjSwap k a) + clsDOdd (k + 2) a) % 4 = 0 := clsDOdd_forkSwap k a ha
theorem pin300 : (dataD 3).cls [0, 1, 0] = 1 ∧ (dataD 3).cls [0, 0, 1] = 3
    ∧ (dataD 3).clsAdd 1 3 = 0 ∧ (dataD 3).clsAdd 1 1 ≠ 0 := by decide +kernel
theorem pin301 : (dataD 4).cls [0, 0, 1, 0] = 2 ∧ (dataD 4).cls [0, 0, 0, 1] = 1
    ∧ (dataD 4).clsAdd 2 2 = 0 ∧ (dataD 4).clsAdd 1 1 = 0 := by decide +kernel
theorem pin302 : clsDOdd 3 [2, 4, 7] ≠ clsDOdd 3 [2, 7, 4]
    ∧ (clsDOdd 3 [2, 4, 7] + clsDOdd 3 [2, 7, 4]) % 4 = 0 := by decide +kernel
theorem pin303 : ¬ clsDualLaw { dataD 3 with dual := fun a => padN 3 a } [0, 1, 0] := by
  decide +kernel

/-! Fixed-member bounds apply to arbitrary seeds. The G2 queue
also completes at singular seeds, while the larger members' walk
bounds are already the positive-root counts. -/

theorem pin304 (v : List BPair) (hv : v.length = 2) :
    orbitSet sertables.tableG2 16 v ≠ [] ∧ orbitFam sertables.tableG2 16 v ≠ [] :=
  ⟨(orbit_complete_G2 v hv).1.1, (orbit_complete_G2 v hv).2.1⟩
theorem pin305 : orbitSet sertables.tableG2 16 [BPair.unit, BPair.unit] = [[BPair.unit, BPair.unit]]
    ∧ orbitFam sertables.tableG2 16 [BPair.unit, BPair.unit] = [([BPair.unit, BPair.unit], false)] := by decide +kernel
theorem pin306 : domWalk sertables.tableG2 5 (poly.neg (sertables.rhoV sertables.tableG2)) = []
    ∧ domWalk sertables.tableG2 6 (poly.neg (sertables.rhoV sertables.tableG2)) = sertables.rhoV sertables.tableG2 := by
  decide +kernel
theorem pin307 (v : List BPair) (hv : v.length = 4) :
    memberchar.lamRead sertables.tableF4 (domWalk sertables.tableF4 24 (poly.pnorm v)) := by
  apply domWalk_root_complete sertables.tableF4 sertables.fundF4
    sertables.fundShape_F4 sertables.gramRead_F4 sertables.simplePosRead_F4
    sertables.reflSquareRead_F4 sertables.permSquareRead_F4 sertables.permImageRead_F4
    sertables.rhoDotRead_F4 sertables.reflFormRead_F4 24 (by decide +kernel) v hv
theorem pin308 (v : List BPair) (hv : v.length = 6) :
    memberchar.lamRead sertables.tableE6 (domWalk sertables.tableE6 36 (poly.pnorm v)) := by
  apply domWalk_root_complete sertables.tableE6 sertables.fundE6
    sertables.fundShape_E6 sertables.gramRead_E6 sertables.simplePosRead_E6
    sertables.reflSquareRead_E6 sertables.permSquareRead_E6 sertables.permImageRead_E6
    sertables.rhoDotRead_E6 sertables.reflFormRead_E6 36 (by decide +kernel) v hv
theorem pin309 (v : List BPair) (hv : v.length = 7) :
    memberchar.lamRead sertables.tableE7 (domWalk sertables.tableE7 63 (poly.pnorm v)) := by
  apply domWalk_root_complete sertables.tableE7 sertables.fundE7
    sertables.fundShape_E7 sertables.gramRead_E7 sertables.simplePosRead_E7
    sertables.reflSquareRead_E7 sertables.permSquareRead_E7 sertables.permImageRead_E7
    sertables.rhoDotRead_E7 sertables.reflFormRead_E7 63 (by decide +kernel) v hv
theorem pin310 (v : List BPair) (hv : v.length = 8) :
    memberchar.lamRead sertables.tableE8 (domWalk sertables.tableE8 120 (poly.pnorm v)) := by
  apply domWalk_root_complete sertables.tableE8 sertables.fundE8
    sertables.fundShape_E8 sertables.gramRead_E8 sertables.simplePosRead_E8
    sertables.reflSquareRead_E8 sertables.permSquareRead_E8 sertables.permImageRead_E8
    sertables.rhoDotRead_E8 sertables.reflFormRead_E8 120 (by decide +kernel) v hv

/-! The actual numerator folds cannot fail from exhausted walks
at any member constructor's stored fuel. -/

theorem pin311 (G : elim.Mat) (acc : List (List Nat × Nat)) (cap : Nat) (m : List Nat) (hm : m.length = 2) :
    numAt sertables.tableG2 G 16 acc cap m ≠ none := by
  obtain ⟨v, hv⟩ := numAt_complete_G2 G acc cap m hm
  rw [hv]
  intro h
  nomatch h
theorem pin312 (G : elim.Mat) (acc : List (List Nat × Nat)) (cap : Nat) (m : List Nat) (hm : m.length = 4) :
    numAt sertables.tableF4 G 1200 acc cap m ≠ none := by
  obtain ⟨v, hv⟩ := numAt_complete_F4 G acc cap m hm
  rw [hv]
  intro h
  nomatch h
theorem pin313 (G : elim.Mat) (acc : List (List Nat × Nat)) (cap : Nat) (m : List Nat) (hm : m.length = 6) :
    numAt sertables.tableE6 G 52000 acc cap m ≠ none := by
  obtain ⟨v, hv⟩ := numAt_complete_E6 G acc cap m hm
  rw [hv]
  intro h
  nomatch h
theorem pin314 (G : elim.Mat) (acc : List (List Nat × Nat)) (cap : Nat) (m : List Nat) (hm : m.length = 7) :
    numAt sertables.tableE7 G 2903040 acc cap m ≠ none := by
  obtain ⟨v, hv⟩ := numAt_complete_E7 G acc cap m hm
  rw [hv]
  intro h
  nomatch h
theorem pin315 (G : elim.Mat) (acc : List (List Nat × Nat)) (cap : Nat) (m : List Nat) (hm : m.length = 8) :
    numAt sertables.tableE8 G 696729600 acc cap m ≠ none := by
  obtain ⟨v, hv⟩ := numAt_complete_E8 G acc cap m hm
  rw [hv]
  intro h
  nomatch h

/-! Fold tests distinguish negative coefficients and nonintegral
root-lattice gaps; accepted cofactors are the actual simple folds. -/

theorem pin316 : foldTest sertables.tableG2 [(BPair.ofNat 2).swap, BPair.ofNat 1] = false := by decide +kernel
theorem pin317 : foldTest sertables.tableE6 (natV [1, 0, 0, 0, 0, 0]) = false
    ∧ foldTest sertables.tableE7 (natV [0, 0, 0, 0, 0, 0, 1]) = false := by decide +kernel
theorem pin318 : foldTest sertables.tableE6 (natV [3, 0, 0, 0, 0, 0]) = true
    ∧ foldWits sertables.tableE6 (natV [3, 0, 0, 0, 0, 0]) (List.replicate 6 BPair.unit)
      = [4, 3, 5, 6, 4, 2] := by decide +kernel
theorem pin319 : foldTest sertables.tableE8 (natV [1, 0, 0, 0, 0, 0, 0, 0]) = true
    ∧ foldWits sertables.tableE8 (natV [1, 0, 0, 0, 0, 0, 0, 0]) (List.replicate 8 BPair.unit)
      = [4, 5, 7, 10, 8, 6, 4, 2] := by decide +kernel
theorem pin320 (lam : List Nat) (hlam : lam.length = 8) (m : List Nat)
    (hm : m ∈ domKeys sertables.tableE8 (sertables.gramRows sertables.tableE8 sertables.adjE8) lam)
    (hne : m ≠ lam) :
    0 < BPair.marginN (BPair.norm
      (formC (sertables.gramRows sertables.tableE8 sertables.adjE8) (shiftV sertables.tableE8 lam) (shiftV sertables.tableE8 lam)
        + (formC (sertables.gramRows sertables.tableE8 sertables.adjE8) (shiftV sertables.tableE8 m) (shiftV sertables.tableE8 m)).swap)) :=
  domKeys_gap_pos_E8 lam hlam m hm hne

/-! The G2 short fundamental has one dominant highest weight and
one zero weight. Its zero-weight numerator is 24 at a gap of 24,
while a forged zero Gram triggers the denominator refusal. -/

theorem pin321 : (numAt sertables.tableG2 sertables.fundG2.gram 16 [([1, 0], 1)] 10 [0, 0]).map BPair.norm
    = some (BPair.ofNat 24) := by decide +kernel
theorem pin322 : domFam sertables.tableG2 sertables.fundG2.gram 16 [1, 0] = [([1, 0], 1), ([0, 0], 1)] := by decide +kernel
theorem pin323 : domFam sertables.tableG2 (List.replicate 2 (List.replicate 2 BPair.unit)) 16 [1, 0] = [] := by decide +kernel
theorem pin324 (t : gentable.Table) (G : elim.Mat) (fuel : Nat) (lam : List Nat) :
    ground.distinctList ((domFam t G fuel lam).map Prod.fst) := domFam_distinct t G fuel lam
theorem pin325 : (multFam sertables.tableG2 sertables.fundG2.gram 16 [1, 0]).length = 7
    ∧ ground.countOf [BPair.unit, BPair.unit] (multFam sertables.tableG2 sertables.fundG2.gram 16 [1, 0]) = 1 := by decide +kernel

/-- The producer's cofactor is read from the full trace recursion
at G2's short fundamental, including the zero-weight count. -/
theorem pin326 : 24 % 24 = 0 ∧ 24 / 24
    = ground.countOf [BPair.unit, BPair.unit] (multFam sertables.tableG2 sertables.fundG2.gram 16 [1, 0]) := by
  have h := recRead_cofactor sertables.tableG2 sertables.fundG2
    sertables.fundShape_G2 sertables.gramRead_G2 sertables.gramSymRead_G2
    sertables.simplePosRead_G2 sertables.permSquareRead_G2 sertables.permImageRead_G2 sertables.rhoDotRead_G2
    sertables.cartanSolve_G2.1 sertables.cartanSolve_G2.2.1 sertables.cartanSolve_G2.2.2
    [1, 0] rfl [0, 0] (ground.mem_of_countOf_pos _ _ (by decide +kernel)) (by decide +kernel)
    (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2))
    (multFam sertables.tableG2 sertables.fundG2.gram 16 [1, 0])
    (ground.mem_of_countOf_pos _ _ (by decide +kernel)) (by decide +kernel)
    (BPair.ofNat 24) (by decide +kernel)
  exact h.2

/-! The short G2 block's seven contents, independently listed
with the simple folds joining them to its top. -/

private def shortG2 : List (List BPair) :=
  [natV [1, 0], [(BPair.ofNat 1).swap, BPair.ofNat 1],
   [BPair.ofNat 2, (BPair.ofNat 1).swap], natV [0, 0],
   [(BPair.ofNat 2).swap, BPair.ofNat 1], [BPair.ofNat 1, (BPair.ofNat 1).swap],
   [(BPair.ofNat 1).swap, BPair.unit]]

private def shortWits : List (List Nat) := [[0, 0], [1, 0], [1, 1], [2, 1], [3, 1], [3, 2], [4, 2]]
private def rhoG2 : List (List BPair × Bool) := orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)
private theorem shortShape : memberchar.mShapeRead sertables.tableG2 shortG2 := by decide +kernel
private theorem shortSym : memberchar.symRead sertables.tableG2 shortG2 := by decide +kernel
private theorem shortSupport : memberchar.supportRead sertables.tableG2 shortG2 shortWits (natV [1, 0]) := by decide +kernel
private theorem shortTop : memberchar.topRead shortG2 (natV [1, 0]) := by decide +kernel
private theorem rhoSeed : (sertables.rhoV sertables.tableG2, false) ∈ rhoG2 :=
  ground.mem_of_countOf_pos _ _ (by decide +kernel)
private theorem shortRec : memberchar.recRead sertables.tableG2 sertables.fundG2 rhoG2 shortG2
    (poly.pnorm (natV [1, 0])) := by decide +kernel

/-- Every lookup of the actual short-block recursion, including
off-list and malformed labels, reads the stated seven-key family. -/
theorem pin327 (m : List Nat) : lookupN m (domFam sertables.tableG2 sertables.fundG2.gram 16 [1, 0])
    = ground.countOf (natV m) shortG2 :=
  domFam_lookup_G2 [1, 0] rfl rhoG2 shortG2 shortShape shortSym shortWits shortSupport shortTop rhoSeed shortRec m

theorem pin328 : lookupN [0, 0] (domFam sertables.tableG2 sertables.fundG2.gram 16 [1, 0]) = 1 := by
  rw [pin327]
  decide +kernel

theorem pin329 : lookupN [1, 0] (domFam sertables.tableG2 sertables.fundG2.gram 16 [1, 0]) = 1 := by
  rw [pin327]
  decide +kernel

theorem pin330 : lookupN [3, 0] (domFam sertables.tableG2 sertables.fundG2.gram 16 [1, 0]) = 0 := by
  rw [pin327]
  decide +kernel

theorem pin331 : lookupN [1] (domFam sertables.tableG2 sertables.fundG2.gram 16 [1, 0]) = 0 := by
  rw [pin327]
  decide +kernel

/-- The numerator refuses exhausted walks and changes when a
needed higher multiplicity is absent from the accumulator. -/
theorem pin332 : numAt sertables.tableG2 sertables.fundG2.gram 0 [([1, 0], 1)] 10 [0, 0] = none := by decide +kernel
theorem pin333 : (numAt sertables.tableG2 sertables.fundG2.gram 16 [] 10 [0, 0]).map BPair.norm
    = some BPair.unit ∧ ¬ (memberchar.gSum sertables.tableG2 sertables.fundG2 shortG2 (natV [0, 0])).oneValue BPair.unit := by
  decide +kernel

/-- Every natural E6 fold passes, at the determinant's occupied
clearing factor, without evaluating the symbolic coefficient list. -/
theorem pin334 (c : List Nat) (hc : c.length = 6) :
    foldTest sertables.tableE6 (assembly.cartanFold sertables.tableE6 c) = true :=
  foldTest_complete sertables.tableE6 sertables.cartanSolve_E6.1 sertables.cartanSolve_E6.2.1
    sertables.cartanSolve_E6.2.2 _ (assembly.cartanFold_length _ sertables.cartanSolve_E6.1 c)
    c hc (poly.oneValue_refl _)

theorem pin335 (m : List Nat) : poly.pnorm (natV m) = natV m ∧ natsOf (natV m) = m :=
  ⟨natV_pnorm m, natsOf_natV m⟩

/-- The natural dominance join forces inclusion in the actual
G2 enumeration at every pair of labels. -/
theorem pin336 (lam m c : List Nat) (hlam : lam.length = 2) (hm : m.length = 2) (hc : c.length = 2)
    (hjoin : poly.pnorm (elim.vecAdd (natV m) (assembly.cartanFold sertables.tableG2 c)) = natV lam) :
    m ∈ domKeys sertables.tableG2 sertables.fundG2.gram lam :=
  domKeys_complete sertables.tableG2 sertables.fundG2 sertables.fundShape_G2 sertables.simplePosRead_G2
    sertables.rhoDotRead_G2 [[4, 6], [6, 12]] rfl (by decide +kernel)
    sertables.cartanSolve_G2.1 sertables.cartanSolve_G2.2.1 sertables.cartanSolve_G2.2.2 lam m hlam hm c hc hjoin

/-- At a zero row sum the coordinate box can omit even its top,
so the occupied-row premise is needed for completeness. -/
theorem pin337 : ground.countOf [1, 0]
    (domKeys sertables.tableG2 (List.replicate 2 (List.replicate 2 BPair.unit)) [1, 0]) = 0 := by decide +kernel

private def adjointG2 : List (List BPair) :=
  (List.range sertables.tableG2.posFolds.length).flatMap (fun j =>
    [poly.pnorm (sertables.posCorootV sertables.tableG2 j),
     poly.pnorm (poly.neg (sertables.posCorootV sertables.tableG2 j))]) ++ [natV [0, 0], natV [0, 0]]
private def adjointWits : List (List Nat) := adjointG2.map (foldWits sertables.tableG2 (natV [0, 1]))
private theorem adjointShape : memberchar.mShapeRead sertables.tableG2 adjointG2 := by decide +kernel
private theorem adjointSym : memberchar.symRead sertables.tableG2 adjointG2 := by decide +kernel
private theorem adjointSupport : memberchar.supportRead sertables.tableG2 adjointG2 adjointWits (natV [0, 1]) := by decide +kernel
private theorem adjointTop : memberchar.topRead adjointG2 (natV [0, 1]) := by decide +kernel
private theorem adjointRec : memberchar.recRead sertables.tableG2 sertables.fundG2 rhoG2 adjointG2
    (poly.pnorm (natV [0, 1])) := by decide +kernel

/-- The adjoint's repeated zero content is read with multiplicity
two by the actual recursion at its stored fuel. -/
theorem pin338 (m : List Nat) : lookupN m (domFam sertables.tableG2 sertables.fundG2.gram 16 [0, 1])
    = ground.countOf (natV m) adjointG2 :=
  domFam_lookup_G2 [0, 1] rfl rhoG2 adjointG2 adjointShape adjointSym adjointWits adjointSupport adjointTop rhoSeed adjointRec m

theorem pin339 : lookupN [0, 0] (domFam sertables.tableG2 sertables.fundG2.gram 16 [0, 1]) = 2 := by
  rw [pin338]
  decide +kernel

/-- An extra zero content preserves symmetry and the top count,
but refuses the trace equation. -/
theorem pin340 : memberchar.symRead sertables.tableG2 (shortG2 ++ [natV [0, 0]])
    ∧ memberchar.topRead (shortG2 ++ [natV [0, 0]]) (natV [1, 0])
    ∧ ¬ memberchar.recRead sertables.tableG2 sertables.fundG2 rhoG2
      (shortG2 ++ [natV [0, 0]]) (poly.pnorm (natV [1, 0])) := by decide +kernel

private theorem walkG2Six (v : List BPair) (hv : v.length = 2) :
    domWalk sertables.tableG2 6 (poly.pnorm v) ≠ [] := by
  intro he
  have h := (domWalk_root_complete sertables.tableG2 sertables.fundG2
    sertables.fundShape_G2 sertables.gramRead_G2 sertables.simplePosRead_G2 sertables.reflSquareRead_G2
    sertables.permSquareRead_G2 sertables.permImageRead_G2 sertables.rhoDotRead_G2 sertables.reflFormRead_G2
    6 (by decide +kernel) v hv).1
  rw [he] at h
  exact Nat.noConfusion h

/-- The trace reads determine every content's count, with the
comparison family arbitrary and the short block independently listed. -/
theorem pin341 (L : List (List BPair)) (wits : List (List Nat))
    (hm : memberchar.mShapeRead sertables.tableG2 L) (hs : memberchar.symRead sertables.tableG2 L)
    (hd : memberchar.supportRead sertables.tableG2 L wits (natV [1, 0]))
    (ht : memberchar.topRead L (natV [1, 0]))
    (hr : memberchar.recRead sertables.tableG2 sertables.fundG2 rhoG2 L (poly.pnorm (natV [1, 0])))
    (v : List BPair) : ground.countOf v L = ground.countOf v shortG2 :=
  multiplicity_unique sertables.tableG2 sertables.fundG2
    sertables.fundShape_G2 sertables.gramRead_G2 sertables.gramSymRead_G2 sertables.simplePosRead_G2
    sertables.permSquareRead_G2 sertables.permImageRead_G2 sertables.rhoDotRead_G2 sertables.reflSquareRead_G2
    [[4, 6], [6, 12]] rfl (by decide +kernel)
    sertables.cartanSolve_G2.1 sertables.cartanSolve_G2.2.1 sertables.cartanSolve_G2.2.2
    6 walkG2Six [1, 0] rfl rhoG2 rhoSeed L shortG2 wits shortWits
    hm shortShape hs shortSym hd shortSupport ht shortTop hr shortRec v

theorem pin342 (G : elim.Mat) (extra : Nat) (acc : List (List Nat × Nat))
    (top : Nat) (m : List Nat) (hm : m.length = 2) :
    numAt sertables.tableG2 G (6 + extra) acc top m = numAt sertables.tableG2 G 6 acc top m :=
  numAt_more sertables.tableG2 G 6 extra walkG2Six acc top m hm

theorem pin343 (G : elim.Mat) (extra : Nat) (lam : List Nat) :
    domFam sertables.tableG2 G (6 + extra) lam = domFam sertables.tableG2 G 6 lam :=
  domFam_more sertables.tableG2 G 6 extra walkG2Six lam

theorem pin344 (G : elim.Mat) (lam : List Nat) :
    domFam sertables.tableG2 G 16 lam = domFam sertables.tableG2 G 6 lam :=
  domFam_more sertables.tableG2 G 6 10 walkG2Six lam

/-- E8's stored recursion fuel and the positive-root count read
one dominant family at every label, without enumerating a Weyl list. -/
theorem pin345 (G : elim.Mat) (lam : List Nat) :
    domFam sertables.tableE8 G 696729600 lam = domFam sertables.tableE8 G 120 lam := by
  apply domFam_more sertables.tableE8 G 120 696729480 _ lam
  intro v hv he
  have h := (domWalk_root_complete sertables.tableE8 sertables.fundE8
    sertables.fundShape_E8 sertables.gramRead_E8 sertables.simplePosRead_E8 sertables.reflSquareRead_E8
    sertables.permSquareRead_E8 sertables.permImageRead_E8 sertables.rhoDotRead_E8 sertables.reflFormRead_E8
    120 (by decide +kernel) v hv).1
  rw [he] at h
  exact Nat.noConfusion h

private def unitE6 : List BPair := natV [0, 0, 0, 0, 0, 0]
private theorem unitShapeE6 : memberchar.mShapeRead sertables.tableE6 [unitE6] := by decide +kernel
private theorem unitSymE6 : memberchar.symRead sertables.tableE6 [unitE6] := by decide +kernel
private theorem unitSupportE6 : memberchar.supportRead sertables.tableE6 [unitE6] [[0, 0, 0, 0, 0, 0]] unitE6 := by decide +kernel
private theorem unitTopE6 : memberchar.topRead [unitE6] unitE6 := by decide +kernel
private theorem unitRecE6 : memberchar.recRead sertables.tableE6 sertables.fundE6
    [(sertables.rhoV sertables.tableE6, false)] [unitE6] (poly.pnorm unitE6) := by
  change memberchar.recRead sertables.tableE6 sertables.fundE6
    [(sertables.rhoV sertables.tableE6, false)] [List.replicate 6 BPair.unit]
    (List.replicate 6 BPair.unit)
  exact memberchar.recRead_unit sertables.tableE6 sertables.fundE6
    sertables.fundShape_E6 sertables.gramRead_E6 sertables.gramSymRead_E6
    (by decide +kernel) sertables.rhoDotRead_E6

/-- The E6 unit block has its exact count at every lookup at
the stored fuel, with the key-three Cartan clearing. -/
theorem pin346 (m : List Nat) :
    lookupN m (domFam sertables.tableE6 sertables.fundE6.gram 52000 [0, 0, 0, 0, 0, 0])
      = ground.countOf (natV m) [unitE6] :=
  domFam_lookup_E6 _ rfl _ [unitE6] unitShapeE6 unitSymE6 _ unitSupportE6 unitTopE6
    (List.Mem.head []) unitRecE6 m

/-- The natural witness is read back at its coefficients, not
just accepted by the fold-membership test. -/
theorem pin347 (lam nu : List BPair) (hlam : lam.length = 7) (hnu : nu.length = 7)
    (c : List Nat) (hc : c.length = 7)
    (hjoin : poly.pnorm (elim.vecAdd nu (assembly.cartanFold sertables.tableE7 c)) = poly.pnorm lam) :
    foldWits sertables.tableE7 lam nu = c :=
  foldWits_eq sertables.tableE7 sertables.cartanSolve_E7.1 sertables.cartanSolve_E7.2.1
    sertables.cartanSolve_E7.2.2 lam nu hlam hnu c hc hjoin

/-- The complete computed G2 short family has the stated count
at every content, through the recursion and the orbit expansion. -/
theorem pin348 (v : List BPair) :
    ground.countOf v (multFam sertables.tableG2 sertables.fundG2.gram 16 [1, 0]) = ground.countOf v shortG2 :=
  multFam_read_G2 [1, 0] rfl rhoG2 shortG2 shortShape shortSym shortWits shortSupport
    shortTop rhoSeed shortRec v

/-- The complete computed G2 adjoint family has the stated count
at every content, including the repeated zero content. -/
theorem pin349 (v : List BPair) :
    ground.countOf v (multFam sertables.tableG2 sertables.fundG2.gram 16 [0, 1]) = ground.countOf v adjointG2 :=
  multFam_read_G2 [0, 1] rfl rhoG2 adjointG2 adjointShape adjointSym adjointWits adjointSupport
    adjointTop rhoSeed adjointRec v

/-- Wall labels and the zero label retain exactly one dominant
orbit point, despite repeated absolute coordinate values. -/
theorem pin350 : (orbitSet (sertables.tableB 2) (fusion.wFuel 2) (natV [0, 1])).filter
    (fun v => v.all (fun x => decide (BPair.unit ≤ x))) = [natV [0, 1]] :=
  orbitSet_dom_B 2 (by decide +kernel) [0, 1] rfl

theorem pin351 : (orbitSet (sertables.tableC 3) (fusion.wFuel 3) (natV [0, 0, 1])).filter
    (fun v => v.all (fun x => decide (BPair.unit ≤ x))) = [natV [0, 0, 1]] :=
  orbitSet_dom_C 3 (by decide +kernel) [0, 0, 1] rfl

theorem pin352 : (orbitSet sertables.tableG2 16 (natV [0, 0])).filter
    (fun v => v.all (fun x => decide (BPair.unit ≤ x))) = [natV [0, 0]] :=
  orbitSet_dom_G2 [0, 0] rfl

theorem pin353 (a b : Nat) : (orbitSet sertables.tableG2 16 (natV [a, b])).filter
    (fun v => v.all (fun x => decide (BPair.unit ≤ x))) = [natV [a, b]] :=
  orbitSet_dom_G2 [a, b] rfl

/-- The dominant filter need not recover a seed with a negative
coroot entry. A short seed also refuses the rank shape read. -/
theorem pin354 : (orbitSet sertables.tableG2 16 [(BPair.ofNat 1).swap, BPair.unit]).filter
    (fun v => v.all (fun x => decide (BPair.unit ≤ x))) ≠ [[(BPair.ofNat 1).swap, BPair.unit]] := by
  decide +kernel

theorem pin355 : ¬ memberchar.mShapeRead sertables.tableG2
    (orbitSet sertables.tableG2 16 (natV [1])) := by decide +kernel

/-- The actual adjoint family has its support witnesses decoded
per occurrence and satisfies the full trace recursion. -/
theorem pin356 : memberchar.supportRead sertables.tableG2
    (multFam sertables.tableG2 sertables.fundG2.gram 16 [0, 1])
    ((multFam sertables.tableG2 sertables.fundG2.gram 16 [0, 1]).map (foldWits sertables.tableG2 (natV [0, 1])))
    (natV [0, 1]) :=
  (multFam_reads_G2 [0, 1] rfl rhoG2 adjointG2 adjointShape adjointSym adjointWits adjointSupport
    adjointTop rhoSeed adjointRec).2.2.1

theorem pin357 : memberchar.recRead sertables.tableG2 sertables.fundG2 rhoG2
    (multFam sertables.tableG2 sertables.fundG2.gram 16 [0, 1]) (poly.pnorm (natV [0, 1])) := by
  apply (multFam_reads_G2 [0, 1] rfl rhoG2 adjointG2 adjointShape adjointSym adjointWits adjointSupport
    adjointTop rhoSeed adjointRec).2.2.2.2

/-- Natural support decoding also handles a relisted family
with a repeated zero content. -/
theorem pin358 : memberchar.supportRead sertables.tableG2 adjointG2.reverse
    (adjointG2.reverse.map (foldWits sertables.tableG2 (natV [0, 1]))) (natV [0, 1]) :=
  supportRead_counts sertables.tableG2 sertables.cartanSolve_G2.1 sertables.cartanSolve_G2.2.1
    sertables.cartanSolve_G2.2.2 _ adjointG2 adjointWits _ rfl (natV_pnorm [0, 1])
    (fun v => ground.countOf_reverse v adjointG2) adjointShape adjointSupport

/-- Both spinor walls have a unique dominant orbit point at
stored fuel; their final coordinate signs distinguish them. -/
theorem pin359 : (orbitSet (sertables.tableD 4) (fusion.wFuel 4) (natV [0, 0, 1, 0])).filter
    (fun v => v.all (fun x => decide (BPair.unit ≤ x))) = [natV [0, 0, 1, 0]] :=
  orbitSet_dom_D 4 (by decide +kernel) [0, 0, 1, 0] rfl

theorem pin360 : (orbitSet (sertables.tableD 4) (fusion.wFuel 4) (natV [0, 0, 0, 1])).filter
    (fun v => v.all (fun x => decide (BPair.unit ≤ x))) = [natV [0, 0, 0, 1]] :=
  orbitSet_dom_D 4 (by decide +kernel) [0, 0, 0, 1] rfl

theorem pin361 : (orbitSet (sertables.tableD 4) (fusion.wFuel 4) (natV [0, 0, 0, 0])).filter
    (fun v => v.all (fun x => decide (BPair.unit ≤ x))) = [natV [0, 0, 0, 0]] :=
  orbitSet_dom_D 4 (by decide +kernel) [0, 0, 0, 0] rfl

/-- Reflection symmetry of the full producer needs no separate
certificate for each computed dominant orbit. -/
theorem pin362 (G : elim.Mat) (lam : List Nat) :
    memberchar.symRead (sertables.tableB 2) (multFam (sertables.tableB 2) G (fusion.wFuel 2) lam) := by
  apply multFam_sym_B 2 (by decide +kernel) G lam

theorem pin363 (G : elim.Mat) (lam : List Nat) :
    memberchar.symRead (sertables.tableC 3) (multFam (sertables.tableC 3) G (fusion.wFuel 3) lam) := by
  apply multFam_sym_C 3 (by decide +kernel) G lam

theorem pin364 (G : elim.Mat) (lam : List Nat) :
    memberchar.symRead (sertables.tableD 4) (multFam (sertables.tableD 4) G (fusion.wFuel 4) lam) := by
  apply multFam_sym_D 4 (by decide +kernel) G lam

/-- Stored-fuel stability preserves actual fusion reads at every
additional step count, including the unit channel. -/
theorem pin365 (extra : Nat) :
    countM sertables.tableG2 sertables.fundG2.gram (16 + extra) [1, 0] [1, 0] [0, 0]
      = countM sertables.tableG2 sertables.fundG2.gram 16 [1, 0] [1, 0] [0, 0] :=
  (fuel_more_G2 sertables.fundG2.gram extra [1, 0] [1, 0] [0, 0] rfl rfl).2.1

theorem pin366 (extra : Nat) :
    rowM sertables.tableG2 sertables.fundG2.gram (16 + extra) [1, 0] [1, 0]
      = rowM sertables.tableG2 sertables.fundG2.gram 16 [1, 0] [1, 0] :=
  (fuel_more_G2 sertables.fundG2.gram extra [1, 0] [1, 0] [0, 0] rfl rfl).2.2.1

theorem pin367 (extra : Nat) :
    multFam sertables.tableG2 sertables.fundG2.gram (16 + extra) [0, 1]
      = multFam sertables.tableG2 sertables.fundG2.gram 16 [0, 1] :=
  (fuel_more_G2 sertables.fundG2.gram extra [0, 1] [1, 0] [0, 0] rfl rfl).1

/-- Series stability holds at arbitrary labels and arbitrary
extra fuel; the fork's dual read includes the spinor labels. -/
theorem pin368 (l : Nat) (hl : 0 < l) (G : elim.Mat) (extra : Nat)
    (a b c : List Nat) (ha : a.length = l) (hc : c.length = l) :
    countM (sertables.tableB l) G (fusion.wFuel l + extra) a b c
      = countM (sertables.tableB l) G (fusion.wFuel l) a b c :=
  (fuel_more_B l hl G extra a b c ha hc).2.1

theorem pin369 (l : Nat) (hl : 0 < l) (G : elim.Mat) (extra : Nat)
    (a b c : List Nat) (ha : a.length = l) (hc : c.length = l) :
    rowM (sertables.tableC l) G (fusion.wFuel l + extra) a b
      = rowM (sertables.tableC l) G (fusion.wFuel l) a b :=
  (fuel_more_C l hl G extra a b c ha hc).2.2.1

theorem pin370 (extra : Nat) :
    dualM (sertables.tableD 5) (fusion.wFuel 5 + extra) [0, 0, 0, 1, 0]
      = dualM (sertables.tableD 5) (fusion.wFuel 5) [0, 0, 0, 1, 0] :=
  (fuel_more_D 5 (by decide +kernel) (elim.idMat 5) extra [0, 0, 0, 1, 0]
    [0, 0, 0, 0, 0] [0, 0, 0, 0, 0] rfl rfl).2.2.2

/-- Below completion, changing the fuel can change the actual
family and the fusion count. -/
theorem pin371 : multFam sertables.tableG2 sertables.fundG2.gram 0 [1, 0] = []
    ∧ countM sertables.tableG2 sertables.fundG2.gram 0 [1, 0] [1, 0] [0, 0] = 0
    ∧ countM sertables.tableG2 sertables.fundG2.gram 16 [1, 0] [1, 0] [0, 0] = 1 := by decide +kernel

/-- The completed G2 count is its actual orbit convolution at
arbitrary first labels and width-matched second and target labels. -/
theorem pin372 (a b c : List Nat) (hb : b.length = 2) (hc : c.length = 2) :
    countM sertables.tableG2 sertables.fundG2.gram 16 a b c =
      memberchar.convCount (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 b))
        (multFam sertables.tableG2 sertables.fundG2.gram 16 a) (shiftV sertables.tableG2 c) false
      - memberchar.convCount (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 b))
        (multFam sertables.tableG2 sertables.fundG2.gram 16 a) (shiftV sertables.tableG2 c) true :=
  countM_conv_G2 sertables.fundG2.gram a b c hb hc

/-- The independently stated short family reads the implemented
count at every second factor and target of the member's width. -/
theorem pin373 (b c : List Nat) (hb : b.length = 2) (hc : c.length = 2) :
    countM sertables.tableG2 sertables.fundG2.gram 16 [1, 0] b c =
      memberchar.convCount (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 b)) shortG2 (shiftV sertables.tableG2 c) false
      - memberchar.convCount (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 b)) shortG2 (shiftV sertables.tableG2 c) true :=
  countM_family_G2 [1, 0] b c rfl hb hc rhoG2 shortG2 shortShape shortSym shortWits shortSupport shortTop rhoSeed shortRec

/-- At the short block against the unit, the two graded
contributions at the unit target are both occupied and equal. -/
theorem pin374 : memberchar.convCount rhoG2 shortG2 (natV [1, 1]) false = 1
    ∧ memberchar.convCount rhoG2 shortG2 (natV [1, 1]) true = 1
    ∧ countM sertables.tableG2 sertables.fundG2.gram 16 [1, 0] [0, 0] [0, 0] = 0 := by decide +kernel

/-- The actual unit row is the second label alone even when the
label lies on a wall or has arbitrarily large coordinates. -/
theorem pin375 (a b : Nat) : fusion.unitRowLaw fusion.dataG2 [a, b] := fusion.unitRowLaw_dataG2 [a, b] rfl

theorem pin376 (b c : List Nat) (hb : b.length = 2) (hc : c.length = 2) :
    countM sertables.tableG2 sertables.fundG2.gram 16 [0, 0] b c = if c = b then 1 else 0 :=
  countM_unit_left_G2 b c hb hc

/-- Starved walks need not read the graded convolution. -/
theorem pin377 : countM sertables.tableG2 sertables.fundG2.gram 0 [1, 0] [1, 0] [0, 0] = 0
    ∧ memberchar.convCount (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 [1, 0]))
      shortG2 (shiftV sertables.tableG2 [0, 0]) false
      - memberchar.convCount (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 [1, 0]))
        shortG2 (shiftV sertables.tableG2 [0, 0]) true = 1 := by decide +kernel

/-- The computed G2 orbit has natural support at every shifted
label, with witnesses supplied by the actual decoder. -/
theorem pin378 (b : List Nat) (hb : b.length = 2) :
    assembly.wDomAt sertables.tableG2 (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 b))
      ((orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 b)).map
        (fun p => foldWits sertables.tableG2 (shiftV sertables.tableG2 b) p.1))
      (poly.pnorm (shiftV sertables.tableG2 b)) := by
  apply orbitFam_dom_G2 _ (shiftV_length sertables.tableG2 b hb) (shiftV_pos sertables.tableG2 b hb)

theorem pin379 (b : List Nat) (hb : b.length = 2) :
    assembly.wRegRead sertables.tableG2 (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 b))
      (poly.pnorm (shiftV sertables.tableG2 b)) := by
  apply orbitFam_reg_G2 _ (shiftV_length sertables.tableG2 b hb) (shiftV_pos sertables.tableG2 b hb)

/-- A lower-side seed has orbit members outside its natural
simple-fold support. -/
theorem pin380 : foldTest sertables.tableG2
    (elim.vecAdd [(BPair.ofNat 1).swap, (BPair.ofNat 1).swap] (poly.neg (natV [1, 1]))) = false := by decide +kernel


/-- The character identity holds for the independent short
family at every content, using both actual orbit queues. -/
theorem pin381 (y : List BPair) : memberchar.identityAt rhoG2 shortG2
    (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 [1, 0])) y :=
  identityRead_G2 [1, 0] rfl shortG2 shortWits shortShape shortSym shortSupport shortTop shortRec y

theorem pin382 (y : List BPair) : memberchar.identityAt rhoG2
    (multFam sertables.tableG2 sertables.fundG2.gram 16 [0, 1])
    (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 [0, 1])) y :=
  multFam_identity_G2 [0, 1] rfl adjointG2 adjointWits adjointShape adjointSym adjointSupport adjointTop adjointRec y

private def unitG2 : List (List BPair) := [natV [0, 0]]
private theorem unitShapeG2 : memberchar.mShapeRead sertables.tableG2 unitG2 := by decide +kernel
private theorem unitSymG2 : memberchar.symRead sertables.tableG2 unitG2 := by decide +kernel
private theorem unitSupportG2 : memberchar.supportRead sertables.tableG2 unitG2 [[0, 0]] (natV [0, 0]) := by decide +kernel
private theorem unitTopG2 : memberchar.topRead unitG2 (natV [0, 0]) := by decide +kernel
private theorem unitRecG2 : memberchar.recRead sertables.tableG2 sertables.fundG2 rhoG2 unitG2 (natV [0, 0]) := by decide +kernel

private theorem shortUnitExhaustion (v : List BPair) :
    ground.countOf v (steinberg.prodFam (multFam sertables.tableG2 sertables.fundG2.gram 16 [1, 0]) unitG2)
      = ground.famFold Nat.add 0 (fun L => ground.countOf v L) [shortG2] := by
  have h : steinberg.prodFam (multFam sertables.tableG2 sertables.fundG2.gram 16 [1, 0]) unitG2
      = multFam sertables.tableG2 sertables.fundG2.gram 16 [1, 0] := by decide +kernel
  rw [h, pin348]
  exact (Nat.add_zero _).symm

private theorem shortChannelReads : ∀ k, k < ([[1, 0]] : List (List Nat)).length →
    (ground.getAt [] [[1, 0]] k).length = 2
      ∧ memberchar.mShapeRead sertables.tableG2 (ground.getAt [] [shortG2] k)
      ∧ memberchar.symRead sertables.tableG2 (ground.getAt [] [shortG2] k)
      ∧ memberchar.supportRead sertables.tableG2 (ground.getAt [] [shortG2] k)
        (ground.getAt [] [shortWits] k) (natV (ground.getAt [] [[1, 0]] k))
      ∧ memberchar.topRead (ground.getAt [] [shortG2] k) (natV (ground.getAt [] [[1, 0]] k))
      ∧ memberchar.recRead sertables.tableG2 sertables.fundG2 rhoG2
        (ground.getAt [] [shortG2] k) (natV (ground.getAt [] [[1, 0]] k)) := by
  intro k hk
  have he : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
  rw [he]
  exact ⟨rfl, shortShape, shortSym, shortSupport, shortTop, shortRec⟩

/-- The computed count reads a one-channel block exhaustion at
every target, with the short block independently listed. -/
theorem pin383 (c : List Nat) (hc : c.length = 2) :
    countM sertables.tableG2 sertables.fundG2.gram 16 [1, 0] [0, 0] c
      = ground.countOf c [[1, 0]] :=
  countM_exhaustion_G2 [1, 0] [0, 0] c rfl hc unitG2 [[0, 0]]
    unitShapeG2 unitSymG2 unitSupportG2 unitTopG2 unitRecG2
    [[1, 0]] [shortG2] [shortWits] rfl shortChannelReads shortUnitExhaustion

/-- The channel support makes every positive computed count a
row member at the actual row list, once per target. -/
theorem pin384 (c : List Nat) (hc : c.length = 2) :
    (0 < countM sertables.tableG2 sertables.fundG2.gram 16 [1, 0] [0, 0] c ↔
      0 < ground.countOf c (rowM sertables.tableG2 sertables.fundG2.gram 16 [1, 0] [0, 0]))
      ∧ ground.countOf c (rowM sertables.tableG2 sertables.fundG2.gram 16 [1, 0] [0, 0]) ≤ 1 :=
  rowM_exhaustion_G2 [1, 0] [0, 0] c rfl rfl hc unitG2 [[0, 0]]
    unitShapeG2 unitSymG2 unitSupportG2 unitTopG2 unitRecG2
    [[1, 0]] [shortG2] [shortWits] rfl shortChannelReads shortUnitExhaustion [[0, 0]] (by decide +kernel)

/-- The wrong channel list cannot satisfy the exhaustion read. -/
theorem pin385 : ground.countOf (natV [1, 0]) (steinberg.prodFam shortG2 unitG2) = 1
    ∧ ground.famFold Nat.add 0 (fun L => ground.countOf (natV [1, 0]) L) [unitG2] = 0 := by decide +kernel

/-- The actual graded walk carries an odd hit to the even seed;
the wrong parity is refused by its returned datum. -/
theorem pin386 : walkP sertables.tableG2 16 [(BPair.ofNat 1).swap, BPair.ofNat 2] false
    = some (natV [1, 1], true)
    ∧ ¬ walkP sertables.tableG2 16 [(BPair.ofNat 1).swap, BPair.ofNat 2] false
      = some (natV [1, 1], false) := by decide +kernel

/-- The shifted target and the returned parity read both orbit
counts, at the stored rho queue. -/
theorem pin387 (side : Bool) : assembly.wCount rhoG2 [(BPair.ofNat 1).swap, BPair.ofNat 2] side
    = if side then 1 else 0 := by
  have h := walkP_wCount sertables.tableG2 rhoG2
    (orbitFam_reads_G2 (sertables.rhoV sertables.tableG2) rfl (by decide +kernel)).2.1
    sertables.reflSquareRead_G2 16 [(BPair.ofNat 1).swap, BPair.ofNat 2] false (natV [1, 1], true)
    rfl (by decide +kernel) pin386.1 side
  have he : assembly.wCount rhoG2 (natV [1, 1]) (xor true side) = if side then 1 else 0 := by
    cases side <;> decide +kernel
  have hx : xor false side = side := by cases side <;> rfl
  rw [hx] at h
  exact h.trans he


/-- The unit-row laws cover every label of all five fixed
members without enumerating a nontrivial Weyl orbit. -/
theorem pin388 (b : List Nat) (hb : b.length = 4) : fusion.unitRowLaw fusion.dataF4 b := by
  apply fusion.unitRowLaw_dataF4 b hb

theorem pin389 (b : List Nat) (hb : b.length = 6) : fusion.unitRowLaw fusion.dataE6 b := by
  apply fusion.unitRowLaw_dataE6 b hb

theorem pin390 (b : List Nat) (hb : b.length = 7) : fusion.unitRowLaw fusion.dataE7 b := by
  apply fusion.unitRowLaw_dataE7 b hb

theorem pin391 (b : List Nat) (hb : b.length = 8) : fusion.unitRowLaw fusion.dataE8 b := by
  apply fusion.unitRowLaw_dataE8 b hb

/-- The zero seed's queue needs exactly one processed entry;
it is independent of the rank and Cartan entries. -/
theorem pin392 (t : gentable.Table) (extra : Nat) :
    orbitSet t (extra + 1) (List.replicate t.rank BPair.unit) = [List.replicate t.rank BPair.unit] := orbitSet_unit t extra

/-- A zero queue budget refuses even the unit orbit. -/
theorem pin393 : orbitSet sertables.tableG2 0 (natV [0, 0]) = [] := by rfl

/-- The actual zero-label solve is independent of the Gram;
a valid Cartan solve still supplies the support decision. -/
theorem pin394 (G : elim.Mat) (fuel : Nat) : domFam sertables.tableE6 G fuel [0, 0, 0, 0, 0, 0]
    = [([0, 0, 0, 0, 0, 0], 1)] :=
  domFam_unit sertables.tableE6 G fuel sertables.cartanSolve_E6.1 sertables.cartanSolve_E6.2.1 sertables.cartanSolve_E6.2.2

theorem pin395 (G : elim.Mat) (fuel : Nat) : multFam sertables.tableE8 G (fuel + 1) [0, 0, 0, 0, 0, 0, 0, 0]
    = [List.replicate 8 BPair.unit] :=
  multFam_unit sertables.tableE8 G fuel sertables.cartanSolve_E8.1 sertables.cartanSolve_E8.2.1 sertables.cartanSolve_E8.2.2

private theorem shortUnitProduct (v : List BPair) : ground.countOf v (steinberg.prodFam shortG2 unitG2)
    = ground.famFold Nat.add 0 (fun L => ground.countOf v L) [shortG2] := by
  have h : steinberg.prodFam shortG2 unitG2 = shortG2 := by decide +kernel
  rw [h]
  exact (Nat.add_zero _).symm

/-- The common block exhaustion gives the same actual count in
both tensor orders at every target label. -/
theorem pin396 (c : List Nat) (hc : c.length = 2) :
    countM sertables.tableG2 sertables.fundG2.gram 16 [1, 0] [0, 0] c
      = countM sertables.tableG2 sertables.fundG2.gram 16 [0, 0] [1, 0] c :=
  countM_comm_G2 [1, 0] [0, 0] c rfl rfl hc shortG2 unitG2 shortWits [[0, 0]]
    shortShape shortSym shortSupport shortTop shortRec unitShapeG2 unitSymG2 unitSupportG2 unitTopG2 unitRecG2
    [[1, 0]] [shortG2] [shortWits] rfl shortChannelReads shortUnitProduct


theorem pin397 (a b : List Nat) :
    fusion.dataG2.count fusion.dataG2.unit a b = if fusion.dataG2.eqL a b then 1 else 0 := by
  apply fusion.unitCount_dataG2 a b

theorem pin398 (a b : List Nat) :
    fusion.dataF4.count fusion.dataF4.unit a b = if fusion.dataF4.eqL a b then 1 else 0 := by
  apply fusion.unitCount_dataF4 a b

theorem pin399 (a b : List Nat) :
    fusion.dataE6.count fusion.dataE6.unit a b = if fusion.dataE6.eqL a b then 1 else 0 := by
  apply fusion.unitCount_dataE6 a b

theorem pin400 (a b : List Nat) :
    fusion.dataE7.count fusion.dataE7.unit a b = if fusion.dataE7.eqL a b then 1 else 0 := by
  apply fusion.unitCount_dataE7 a b

theorem pin401 (a b : List Nat) :
    fusion.dataE8.count fusion.dataE8.unit a b = if fusion.dataE8.eqL a b then 1 else 0 := by
  apply fusion.unitCount_dataE8 a b

/-- The interface pads malformed spellings, so the literal
singleton row law requires a canonical-width label. -/
theorem pin402 : ¬ fusion.unitRowLaw fusion.dataG2 [1] := by decide +kernel

/-- A singular Cartan can accept a gap whose decoded witness
fails to reconstruct it; the support-decoder theorem uses the
member's valid Cartan solve. -/
theorem pin403 : foldTest { sertables.tableG2 with cartan := [[BPair.unit, BPair.unit], [BPair.unit, BPair.unit]] }
      (natV [1, 0]) = true
    ∧ ¬ poly.oneValue
      (assembly.cartanFold { sertables.tableG2 with cartan := [[BPair.unit, BPair.unit], [BPair.unit, BPair.unit]] } [0, 0])
      (natV [1, 0]) := by decide +kernel

/-- B2's actual count uses the actual graded queue for every
second factor and target of the member's width. -/
theorem pin404 (G : elim.Mat) (a b c : List Nat) (hb : b.length = 2) (hc : c.length = 2) :
    countM (sertables.tableB 2) G (fusion.wFuel 2) a b c =
      memberchar.convCount (orbitFam (sertables.tableB 2) (fusion.wFuel 2) (shiftV (sertables.tableB 2) b))
        (multFam (sertables.tableB 2) G (fusion.wFuel 2) a) (shiftV (sertables.tableB 2) c) false
      - memberchar.convCount (orbitFam (sertables.tableB 2) (fusion.wFuel 2) (shiftV (sertables.tableB 2) b))
        (multFam (sertables.tableB 2) G (fusion.wFuel 2) a) (shiftV (sertables.tableB 2) c) true :=
  countM_conv_B 2 (by decide +kernel) G a b c hb hc

/-- C3's actual count uses the actual graded queue for every
second factor and target of the member's width. -/
theorem pin405 (G : elim.Mat) (a b c : List Nat) (hb : b.length = 3) (hc : c.length = 3) :
    countM (sertables.tableC 3) G (fusion.wFuel 3) a b c =
      memberchar.convCount (orbitFam (sertables.tableC 3) (fusion.wFuel 3) (shiftV (sertables.tableC 3) b))
        (multFam (sertables.tableC 3) G (fusion.wFuel 3) a) (shiftV (sertables.tableC 3) c) false
      - memberchar.convCount (orbitFam (sertables.tableC 3) (fusion.wFuel 3) (shiftV (sertables.tableC 3) b))
        (multFam (sertables.tableC 3) G (fusion.wFuel 3) a) (shiftV (sertables.tableC 3) c) true :=
  countM_conv_C 3 (by decide +kernel) G a b c hb hc

/-- D4's actual count uses the actual graded queue for every
second factor and target of the member's width. -/
theorem pin406 (G : elim.Mat) (a b c : List Nat) (hb : b.length = 4) (hc : c.length = 4) :
    countM (sertables.tableD 4) G (fusion.wFuel 4) a b c =
      memberchar.convCount (orbitFam (sertables.tableD 4) (fusion.wFuel 4) (shiftV (sertables.tableD 4) b))
        (multFam (sertables.tableD 4) G (fusion.wFuel 4) a) (shiftV (sertables.tableD 4) c) false
      - memberchar.convCount (orbitFam (sertables.tableD 4) (fusion.wFuel 4) (shiftV (sertables.tableD 4) b))
        (multFam (sertables.tableD 4) G (fusion.wFuel 4) a) (shiftV (sertables.tableD 4) c) true :=
  countM_conv_D 4 (by decide +kernel) G a b c hb hc


/-- The shifted coroot list is the successors at every rank. -/
theorem pin407 (t : gentable.Table) (m : List Nat) (hm : m.length = t.rank) :
    shiftV t m = natV (m.map (fun n => n + 1)) := shiftV_natV t m hm

theorem pin408 : ¬ shiftV sertables.tableG2 [1, 0, 4] = natV [2, 1, 5] := by decide +kernel

/-- Actual regular queues agree with the displayed family at
arbitrary queried keys, not just their own members. -/
theorem pin409 (m : List Nat) (hm : m.length = 2) (p : List BPair × Bool) :
    ground.countOf p (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 m))
      = ground.countOf p (sertables.weylG2 (shiftV sertables.tableG2 m)) :=
  orbitFam_counts_G2 _ (shiftV_length sertables.tableG2 m hm) (shiftV_pos sertables.tableG2 m hm) p

/-- A singular seed repeats in the displayed Weyl family but
has only one actual queue entry; the strict-seed binder matters. -/
theorem pin410 : ground.countOf (natV [0, 0], false) (orbitFam sertables.tableG2 16 (natV [0, 0])) = 1
    ∧ ground.countOf (natV [0, 0], false) (sertables.weylG2 (natV [0, 0])) = 6 := by decide +kernel

theorem pin411 (a b : List Nat) (ha : a.length = 2) (hb : b.length = 2) (p : Nat × Bool) :
    ground.countOf p (weyldim.dmap sertables.fundG2
      (sertables.dotB sertables.fundG2 (shiftV sertables.tableG2 a) (shiftV sertables.tableG2 b))
      (shiftV sertables.tableG2 b) (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 a)))
      = ground.countOf p (weyldim.dmap sertables.fundG2
        (sertables.dotB sertables.fundG2 (shiftV sertables.tableG2 b) (shiftV sertables.tableG2 a))
        (shiftV sertables.tableG2 a) (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 b))) :=
  orbitFam_dmap_exchange_G2 _ _ (shiftV_length sertables.tableG2 a ha) (shiftV_length sertables.tableG2 b hb)
    (shiftV_pos sertables.tableG2 a ha) (shiftV_pos sertables.tableG2 b hb) p

/-- Independently stated seven- and fourteen-content families
enter the dimension theorem through their mathematical reads. -/
theorem pin412 : dimM sertables.tableG2 [1, 0] = 7 :=
  dimM_family_G2 [1, 0] rfl shortG2 shortWits shortShape shortSym shortSupport shortTop shortRec

theorem pin413 : dimM sertables.tableG2 [0, 1] = 14 :=
  dimM_family_G2 [0, 1] rfl adjointG2 adjointWits adjointShape adjointSym adjointSupport adjointTop adjointRec

theorem pin414 : dimM sertables.tableG2 [1, 0]
    = (multFam sertables.tableG2 sertables.fundG2.gram 16 [1, 0]).length :=
  dimM_multFam_G2 [1, 0] rfl shortG2 shortWits shortShape shortSym shortSupport shortTop shortRec

/-- The unit exhaustion gives the dimension identity at the
actual computed row, with an independently listed block family. -/
theorem pin415 : ground.famFold Nat.add 0
    (fun c => countM sertables.tableG2 sertables.fundG2.gram 16 [1, 0] [0, 0] c * dimM sertables.tableG2 c)
    (rowM sertables.tableG2 sertables.fundG2.gram 16 [1, 0] [0, 0])
    = dimM sertables.tableG2 [1, 0] * dimM sertables.tableG2 [0, 0] :=
  dimM_exhaustion_G2 [1, 0] [0, 0] rfl rfl shortG2 unitG2 shortWits [[0, 0]]
    shortShape shortSym shortSupport shortTop shortRec unitShapeG2 unitSymG2 unitSupportG2 unitTopG2 unitRecG2
    [[1, 0]] [shortG2] [shortWits] rfl shortChannelReads shortUnitProduct [[0, 0]] (by decide +kernel)

/-- The actual Cartan count is one with an arbitrary second
label, using independently stated short and adjoint block data. -/
theorem pin416 (b : List Nat) (hb : b.length = 2) :
    countM sertables.tableG2 sertables.fundG2.gram 16 [1, 0] b (List.zipWith Nat.add [1, 0] b) = 1 :=
  countM_cartan_G2 [1, 0] b rfl hb rhoG2 shortG2 shortShape shortSym shortWits shortSupport shortTop rhoSeed shortRec

theorem pin417 (b : List Nat) (hb : b.length = 2) : fusion.cartanLaw fusion.dataG2 [0, 1] b :=
  fusion.cartanLaw_dataG2 [0, 1] b rfl hb rhoG2 adjointG2 adjointShape adjointSym
    adjointWits adjointSupport adjointTop rhoSeed adjointRec

theorem pin418 : fusion.dimLaw fusion.dataG2 [1, 0] [0, 0] :=
  fusion.dimLaw_dataG2 [1, 0] [0, 0] rfl rfl shortG2 unitG2 shortWits [[0, 0]]
    shortShape shortSym shortSupport shortTop shortRec unitShapeG2 unitSymG2 unitSupportG2 unitTopG2 unitRecG2
    [[1, 0]] [shortG2] [shortWits] rfl shortChannelReads shortUnitProduct [[0, 0]] (by decide +kernel)

/-- The product bounds quantify over every rank and every label,
without multiplicity-family hypotheses. -/
theorem pin419 (l : Nat) (m : List Nat) (hm : m.length = l) : 0 < dimM (sertables.tableB l) m :=
  dimM_pos_B l m hm

theorem pin420 (l : Nat) (m : List Nat) (hm : m.length = l) : 0 < dimM (sertables.tableC l) m :=
  dimM_pos_C l m hm

theorem pin421 (l : Nat) (m : List Nat) (hm : m.length = l) : 0 < dimM (sertables.tableD l) m :=
  dimM_pos_D l m hm

theorem pin422 (l : Nat) : dimM (sertables.tableB l) (List.replicate l 0) = 1
    ∧ dimM (sertables.tableC l) (List.replicate l 0) = 1
    ∧ dimM (sertables.tableD l) (List.replicate l 0) = 1 :=
  ⟨dimM_unit_B l, dimM_unit_C l, dimM_unit_D l⟩

theorem pin423 (l : Nat) (m : List Nat) (hm : m.length = l) (hne : m ≠ List.replicate l 0) :
    2 ≤ dimM (sertables.tableB l) m := dimM_ge_two_B l m hm hne

theorem pin424 (l : Nat) (m : List Nat) (hm : m.length = l) (hne : m ≠ List.replicate l 0) :
    2 ≤ dimM (sertables.tableC l) m := dimM_ge_two_C l m hm hne

theorem pin425 (l : Nat) (hl : 2 ≤ l) (m : List Nat) (hm : m.length = l) (hne : m ≠ List.replicate l 0) :
    2 ≤ dimM (sertables.tableD l) m := dimM_ge_two_D l hl m hm hne

/-- Below D's two-key domain a nonunit label need not have a
strict factor. A vacant root or a wrong width also refuses the
positive-product read. -/
theorem pin426 : dimM (sertables.tableD 1) [1] = 1
    ∧ dimM { sertables.tableG2 with posFolds := [[0, 0]] } [1, 0] = 0
    ∧ dimM sertables.tableG2 [] = 0 := by decide +kernel

/-- Positive factors alone do not give strictness without a
simple root detecting the occupied coordinate. -/
theorem pin427 : dimM { sertables.tableG2 with posFolds := [[1, 0]] } [0, 1] = 1 := by decide +kernel

theorem pin428 (m : List Nat) (hm : m.length = 2) (hne : m ≠ List.replicate 2 0) :
    0 < dimM sertables.tableG2 m ∧ 2 ≤ dimM sertables.tableG2 m
      ∧ dimM sertables.tableG2 (List.replicate 2 0) = 1 :=
  ⟨dimM_pos_G2 m hm, dimM_ge_two_G2 m hm hne, dimM_unit_G2⟩

theorem pin429 (m : List Nat) (hm : m.length = 4) (hne : m ≠ List.replicate 4 0) :
    0 < dimM sertables.tableF4 m ∧ 2 ≤ dimM sertables.tableF4 m
      ∧ dimM sertables.tableF4 (List.replicate 4 0) = 1 :=
  ⟨dimM_pos_F4 m hm, dimM_ge_two_F4 m hm hne, dimM_unit_F4⟩

theorem pin430 (m : List Nat) (hm : m.length = 6) (hne : m ≠ List.replicate 6 0) :
    0 < dimM sertables.tableE6 m ∧ 2 ≤ dimM sertables.tableE6 m
      ∧ dimM sertables.tableE6 (List.replicate 6 0) = 1 :=
  ⟨dimM_pos_E6 m hm, dimM_ge_two_E6 m hm hne, dimM_unit_E6⟩

theorem pin431 (m : List Nat) (hm : m.length = 7) (hne : m ≠ List.replicate 7 0) :
    0 < dimM sertables.tableE7 m ∧ 2 ≤ dimM sertables.tableE7 m
      ∧ dimM sertables.tableE7 (List.replicate 7 0) = 1 :=
  ⟨dimM_pos_E7 m hm, dimM_ge_two_E7 m hm hne, dimM_unit_E7⟩

theorem pin432 (m : List Nat) (hm : m.length = 8) (hne : m ≠ List.replicate 8 0) :
    0 < dimM sertables.tableE8 m ∧ 2 ≤ dimM sertables.tableE8 m
      ∧ dimM sertables.tableE8 (List.replicate 8 0) = 1 :=
  ⟨dimM_pos_E8 m hm, dimM_ge_two_E8 m hm hne, dimM_unit_E8⟩

/-- The right-unit character read decides every canonical
target, including labels absent from the block's content family. -/
theorem pin433 (c : List Nat) (hc : c.length = 2) :
    countM sertables.tableG2 sertables.fundG2.gram 16 [1, 0] [0, 0] c = if c = [1, 0] then 1 else 0 :=
  countM_unit_right_G2 [1, 0] c rfl hc shortG2 shortWits shortShape shortSym shortSupport shortTop shortRec

theorem pin434 : rowM sertables.tableG2 sertables.fundG2.gram 16 [0, 1] [0, 0] = [[0, 1]] :=
  rowM_unit_right_G2 [0, 1] rfl adjointG2 adjointWits adjointShape adjointSym adjointSupport adjointTop adjointRec

theorem pin435 (a c : List Nat) (ha : a.length = 2) (hc : c.length = 2) (side : Bool) :
    assembly.wCount (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 a))
      (shiftV sertables.tableG2 c) side = if c = a then (if side then 0 else 1) else 0 :=
  orbitFam_dominant_count_G2 a c ha hc side

theorem pin436 (t : gentable.Table) (a b : List Nat) (ha : a.length = t.rank) (hb : b.length = t.rank)
    (h : shiftV t a = shiftV t b) : a = b := shiftV_inj t a b ha hb h

theorem pin437 (t : gentable.Table) (a b : List Nat) (ha : a.length = t.rank) (hb : b.length = t.rank) :
    shiftV t (List.zipWith Nat.add a b) = poly.pnorm (elim.vecAdd (natV a) (shiftV t b)) :=
  shiftV_join t a b ha hb

/-- The dimension-one characterization is symbolic in the rank
and in the whole coroot list. -/
theorem pin438 (l : Nat) (m : List Nat) (hm : m.length = l) :
    dimM (sertables.tableB l) m = 1 ↔ m = List.replicate l 0 :=
  dimM_eq_one (sertables.tableB l) (ground.length_mapRange _ l) (serstable.gapAt_rho_pos_B l)
    (sertables.simpleFold_mem_B l) m hm

/-- The symmetric pair family of the seven contents, with its
one scalar line withdrawn, gives the twenty-seven-content block. -/
private def symmetricSquareG2 : List (List BPair) :=
  ground.eraseFirst (natV [0, 0])
    ((List.range shortG2.length).flatMap (fun i =>
      (List.range (shortG2.length - i)).map (fun j =>
        poly.pnorm (elim.vecAdd (ground.getAt [] shortG2 i) (ground.getAt [] shortG2 (i + j))))))

private def symmetricSquareWits : List (List Nat) := symmetricSquareG2.map (foldWits sertables.tableG2 (natV [2, 0]))
private theorem symmetricSquareShape : memberchar.mShapeRead sertables.tableG2 symmetricSquareG2 := by decide +kernel
private theorem symmetricSquareSym : memberchar.symRead sertables.tableG2 symmetricSquareG2 := by decide +kernel
private theorem symmetricSquareSupport : memberchar.supportRead sertables.tableG2 symmetricSquareG2 symmetricSquareWits (natV [2, 0]) := by decide +kernel
private theorem symmetricSquareTop : memberchar.topRead symmetricSquareG2 (natV [2, 0]) := by decide +kernel
private theorem symmetricSquareRec : memberchar.recRead sertables.tableG2 sertables.fundG2 rhoG2 symmetricSquareG2
    (natV [2, 0]) := by decide +kernel

private def squareTopsG2 : List (List Nat) := [[0, 0], [1, 0], [0, 1], [2, 0]]
private def squareFamiliesG2 : List (List (List BPair)) := [unitG2, shortG2, adjointG2, symmetricSquareG2]
private def squareWitnessesG2 : List (List (List Nat)) := [[[0, 0]], shortWits, adjointWits, symmetricSquareWits]

private theorem squareExhaustionMembers :
    ∀ v ∈ steinberg.prodFam shortG2 shortG2 ++ squareFamiliesG2.flatMap (fun L => L),
      ground.countOf v (steinberg.prodFam shortG2 shortG2)
        = ground.countOf v (squareFamiliesG2.flatMap (fun L => L)) := by decide +kernel

private theorem squareExhaustion (v : List BPair) :
    ground.countOf v (steinberg.prodFam shortG2 shortG2)
      = ground.famFold Nat.add 0 (fun L => ground.countOf v L) squareFamiliesG2 := by
  have h := ground.countOf_eq_of_members (steinberg.prodFam shortG2 shortG2)
    (squareFamiliesG2.flatMap (fun L => L))
    (fun x hx => squareExhaustionMembers x (ground.mem_append_left _ hx))
    (fun x hx => squareExhaustionMembers x (ground.mem_append_right _ hx)) v
  rw [ground.countOf_flatMap] at h
  exact h

private theorem squareChannelReads : ∀ k, k < squareTopsG2.length →
    (ground.getAt [] squareTopsG2 k).length = 2
      ∧ memberchar.mShapeRead sertables.tableG2 (ground.getAt [] squareFamiliesG2 k)
      ∧ memberchar.symRead sertables.tableG2 (ground.getAt [] squareFamiliesG2 k)
      ∧ memberchar.supportRead sertables.tableG2 (ground.getAt [] squareFamiliesG2 k)
        (ground.getAt [] squareWitnessesG2 k) (natV (ground.getAt [] squareTopsG2 k))
      ∧ memberchar.topRead (ground.getAt [] squareFamiliesG2 k) (natV (ground.getAt [] squareTopsG2 k))
      ∧ memberchar.recRead sertables.tableG2 sertables.fundG2 rhoG2
        (ground.getAt [] squareFamiliesG2 k) (natV (ground.getAt [] squareTopsG2 k)) := by
  let P := fun k => (ground.getAt [] squareTopsG2 k).length = 2
      ∧ memberchar.mShapeRead sertables.tableG2 (ground.getAt [] squareFamiliesG2 k)
      ∧ memberchar.symRead sertables.tableG2 (ground.getAt [] squareFamiliesG2 k)
      ∧ memberchar.supportRead sertables.tableG2 (ground.getAt [] squareFamiliesG2 k)
        (ground.getAt [] squareWitnessesG2 k) (natV (ground.getAt [] squareTopsG2 k))
      ∧ memberchar.topRead (ground.getAt [] squareFamiliesG2 k) (natV (ground.getAt [] squareTopsG2 k))
      ∧ memberchar.recRead sertables.tableG2 sertables.fundG2 rhoG2
        (ground.getAt [] squareFamiliesG2 k) (natV (ground.getAt [] squareTopsG2 k))
  have h0 : P 0 := ⟨rfl, unitShapeG2, unitSymG2, unitSupportG2, unitTopG2, unitRecG2⟩
  have h1 : P 1 := ⟨rfl, shortShape, shortSym, shortSupport, shortTop, shortRec⟩
  have h2 : P 2 := ⟨rfl, adjointShape, adjointSym, adjointSupport, adjointTop, adjointRec⟩
  have h3 : P 3 := ⟨rfl, symmetricSquareShape, symmetricSquareSym, symmetricSquareSupport,
    symmetricSquareTop, symmetricSquareRec⟩
  have hall : (List.range 4).all (fun k => decide (P k)) = true :=
    ground.all_range_succ_intro 3 (ground.all_range_succ_intro 2
      (ground.all_range_succ_intro 1 (ground.all_range_succ_intro 0 rfl (decide_eq_true h0))
        (decide_eq_true h1)) (decide_eq_true h2)) (decide_eq_true h3)
  intro k hk
  exact of_decide_eq_true (ground.all_range_read 4 hall k hk)

private theorem squareTopSupport : memberchar.supportRead sertables.tableG2 (squareTopsG2.map natV)
    [[4, 2], [2, 1], [1, 0], [0, 0]] (natV [2, 0]) := by decide +kernel

private theorem squareActualExhaustion (v : List BPair) :
    ground.countOf v (steinberg.prodFam (multFam sertables.tableG2 sertables.fundG2.gram 16 [1, 0]) shortG2)
      = ground.famFold Nat.add 0 (fun L => ground.countOf v L) squareFamiliesG2 :=
  (steinberg.prodFam_counts _ shortG2 shortG2 shortG2
    (multFam_read_G2 [1, 0] rfl rhoG2 shortG2 shortShape shortSym shortWits shortSupport shortTop rhoSeed shortRec)
    (fun _ => rfl) v).trans (squareExhaustion v)

/-- The independently constructed symmetric-pair block has the
Weyl dimension twenty-seven by the character theorem's route. -/
theorem pin439 : dimM sertables.tableG2 [2, 0] = 27 := by
  have h := dimM_family_G2 [2, 0] rfl symmetricSquareG2 symmetricSquareWits
    symmetricSquareShape symmetricSquareSym symmetricSquareSupport symmetricSquareTop symmetricSquareRec
  exact h

/-- The four channel families exhaust the seven-by-seven
product at every key and give the actual row's dimension identity. -/
theorem pin440 : fusion.dimLaw fusion.dataG2 [1, 0] [1, 0] :=
  fusion.dimLaw_dataG2 [1, 0] [1, 0] rfl rfl shortG2 shortG2 shortWits shortWits
    shortShape shortSym shortSupport shortTop shortRec shortShape shortSym shortSupport shortTop shortRec
    squareTopsG2 squareFamiliesG2 squareWitnessesG2 rfl squareChannelReads squareExhaustion
    [[4, 2], [2, 1], [1, 0], [0, 0]] squareTopSupport

theorem pin441 (c : List Nat) (hc : c.length = 2) : fusion.rowLaw fusion.dataG2 [1, 0] [1, 0] c :=
  fusion.rowLaw_dataG2 [1, 0] [1, 0] c rfl rfl hc shortG2 shortWits
    shortShape shortSym shortSupport shortTop shortRec squareTopsG2 squareFamiliesG2 squareWitnessesG2
    rfl squareChannelReads squareActualExhaustion [[4, 2], [2, 1], [1, 0], [0, 0]] squareTopSupport

theorem pin442 (c : List Nat) (hc : c.length = 2) :
    countM sertables.tableG2 sertables.fundG2.gram 16 [1, 0] [1, 0] c = ground.countOf c squareTopsG2 :=
  countM_exhaustion_G2 [1, 0] [1, 0] c rfl hc shortG2 shortWits shortShape shortSym shortSupport shortTop shortRec
    squareTopsG2 squareFamiliesG2 squareWitnessesG2 rfl squareChannelReads squareActualExhaustion

theorem pin443 : countM sertables.tableG2 sertables.fundG2.gram 16 [1, 0] [1, 0] [0, 0] = 1 := by
  rw [pin442 [0, 0] rfl]
  decide +kernel

theorem pin444 : countM sertables.tableG2 sertables.fundG2.gram 16 [1, 0] [1, 0] [1, 1] = 0 := by
  rw [pin442 [1, 1] rfl]
  decide +kernel

theorem pin445 : 1 + dimM sertables.tableG2 [1, 0] + dimM sertables.tableG2 [0, 1]
    + dimM sertables.tableG2 [2, 0] = dimM sertables.tableG2 [1, 0] * dimM sertables.tableG2 [1, 0] := by
  rw [pin412, pin413, pin439]

/-- The right-unit interface count accepts padded target
spellings while the literal row uses the canonical width. -/
theorem pin446 (c : List Nat) : fusion.dataG2.count [1, 0] fusion.dataG2.unit c
    = if fusion.dataG2.eqL [1, 0] c then 1 else 0 :=
  fusion.rightUnitCount_dataG2 [1, 0] c shortG2 shortWits shortShape shortSym shortSupport shortTop shortRec

theorem pin447 : fusion.dataG2.row [0, 1] fusion.dataG2.unit = [[0, 1]] :=
  fusion.rightUnitRow_dataG2 [0, 1] rfl adjointG2 adjointWits adjointShape adjointSym adjointSupport adjointTop adjointRec

/-- An off-row target cannot be added to the channel tops
without changing the exhaustion's count at its own top. -/
theorem pin448 : ground.countOf (natV [1, 1]) (steinberg.prodFam shortG2 shortG2) = 0
    ∧ ground.countOf [1, 1] (squareTopsG2 ++ [[1, 1]]) = 1 := by decide +kernel

/-- Factor exchange reaches the interface's own law at every
target through the two block families and their common exhaustion. -/
theorem pin449 (c : List Nat) (hc : c.length = 2) : fusion.commLaw fusion.dataG2 [1, 0] [0, 0] c :=
  fusion.commLaw_dataG2 [1, 0] [0, 0] c rfl rfl hc shortG2 unitG2 shortWits [[0, 0]]
    shortShape shortSym shortSupport shortTop shortRec unitShapeG2 unitSymG2 unitSupportG2 unitTopG2 unitRecG2
    [[1, 0]] [shortG2] [shortWits] rfl shortChannelReads shortUnitProduct

/-- The actual G2 block construction has its canonical
shape, natural support and unique top at every label. -/
theorem pin450 (a : List Nat) (ha : a.length = 2) :
    memberchar.mShapeRead sertables.tableG2
      (fiber.blockWeights memtable.genG2 (fiber.fundTops memtable.genG2 [none, some (0, 0)]) a) :=
  fiber.blockWeights_shape_G2 a ha

theorem pin451 (a : List Nat) (ha : a.length = 2) :
    memberchar.supportRead sertables.tableG2
      (fiber.blockWeights memtable.genG2 (fiber.fundTops memtable.genG2 [none, some (0, 0)]) a)
      ((fiber.blockWeights memtable.genG2 (fiber.fundTops memtable.genG2 [none, some (0, 0)]) a).map
        (foldWits sertables.tableG2 (natV a))) (natV a) := blockWeights_support_G2 a ha

theorem pin452 (a : List Nat) (ha : a.length = 2) :
    memberchar.topRead
      (fiber.blockWeights memtable.genG2 (fiber.fundTops memtable.genG2 [none, some (0, 0)]) a)
      (natV a) := blockWeights_topRead_G2 a ha

theorem pin453 (a : List Nat) (ha : a.length = 2) (nu : List BPair)
    (hnu : nu ∈ fiber.blockWeights memtable.genG2 (fiber.fundTops memtable.genG2 [none, some (0, 0)]) a) :
    sertables.dotB sertables.fundG2 nu (sertables.rhoV sertables.tableG2)
      ≤ sertables.dotB sertables.fundG2 (natV a) (sertables.rhoV sertables.tableG2) :=
  blockWeights_height_G2 a ha nu hnu

private def actualShortG2 := fiber.blockWeights memtable.genG2
  (fiber.fundTops memtable.genG2 [none, some (0, 0)]) [1, 0]
private def actualAdjointG2 := fiber.blockWeights memtable.genG2
  (fiber.fundTops memtable.genG2 [none, some (0, 0)]) [0, 1]

/-- The generated families agree with the independent content
families at every key, with repeated contents counted. -/
private theorem actualShortMembers : ∀ v ∈ actualShortG2 ++ shortG2,
    ground.countOf v actualShortG2 = ground.countOf v shortG2 := by decide +kernel
private theorem actualAdjointMembers : ∀ v ∈ actualAdjointG2 ++ adjointG2,
    ground.countOf v actualAdjointG2 = ground.countOf v adjointG2 := by decide +kernel

theorem pin454 (v : List BPair) : ground.countOf v actualShortG2 = ground.countOf v shortG2 :=
  ground.countOf_eq_of_members actualShortG2 shortG2
    (fun x hx => actualShortMembers x (ground.mem_append_left _ hx))
    (fun x hx => actualShortMembers x (ground.mem_append_right _ hx)) v

theorem pin455 (v : List BPair) : ground.countOf v actualAdjointG2 = ground.countOf v adjointG2 :=
  ground.countOf_eq_of_members actualAdjointG2 adjointG2
    (fun x hx => actualAdjointMembers x (ground.mem_append_left _ hx))
    (fun x hx => actualAdjointMembers x (ground.mem_append_right _ hx)) v

end memberdata
