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
set_option maxRecDepth 8192
set_option maxHeartbeats 64000000

open ground memberdata fusion

/-! ## The producers at the landed kit

The `B_2` family at `θ` runs the whole kit, the recursion's read
at the committed fundamental data with the produced `ρ`-orbit;
the further members run the shape, symmetry, top and dominance
reads at their own produced families. -/

example : memberchar.mShapeRead (sertables.tableB 2)
    (multFam (sertables.tableB 2) (gramOf (sertables.tableB 2)) 16 [0,2]) := by
  decide +kernel
example : memberchar.symRead (sertables.tableB 2)
    (multFam (sertables.tableB 2) (gramOf (sertables.tableB 2)) 16 [0,2]) := by
  decide +kernel
example : memberchar.topRead
    (multFam (sertables.tableB 2) (gramOf (sertables.tableB 2)) 16 [0,2])
    (poly.pnorm (natV [0,2])) := by decide +kernel
example : memberchar.lamRead (sertables.tableB 2)
    (poly.pnorm (natV [0,2])) := by decide +kernel
example : memberchar.supportRead (sertables.tableB 2)
    (multFam (sertables.tableB 2) (gramOf (sertables.tableB 2)) 16 [0,2])
    ((multFam (sertables.tableB 2) (gramOf (sertables.tableB 2)) 16
      [0,2]).map (foldWits (sertables.tableB 2) (natV [0,2])))
    (poly.pnorm (natV [0,2])) := by decide +kernel
example : memberchar.recRead (sertables.tableB 2) sertables.fundB2
    (sertables.serWeylB 2 (sertables.rhoV (sertables.tableB 2)))
    (multFam (sertables.tableB 2) (gramOf (sertables.tableB 2)) 16 [0,2])
    (poly.pnorm (natV [0,2])) := by decide +kernel

/-! The displayed Weyl lists against the word closure: at a shifted
key each displayed member sits in the letters' closure once, the
lists one graded multiset (`con:sertables`' one-member-each
read). -/

example : ((sertables.serWeylB 2
      (shiftV (sertables.tableB 2) [0,2])).all (fun vp =>
    ground.countOf vp (orbitFam (sertables.tableB 2) 16
      (shiftV (sertables.tableB 2) [0,2])) == 1)) = true
    ∧ (sertables.serWeylB 2 (shiftV (sertables.tableB 2) [0,2])).length
      = (orbitFam (sertables.tableB 2) 16
          (shiftV (sertables.tableB 2) [0,2])).length := by decide +kernel
example : ((sertables.serWeylC 3
      (shiftV (sertables.tableC 3) [2,0,0])).all (fun vp =>
    ground.countOf vp (orbitFam (sertables.tableC 3) 60
      (shiftV (sertables.tableC 3) [2,0,0])) == 1)) = true := by decide +kernel
example : ((sertables.serWeylD 3
      (shiftV (sertables.tableD 3) [0,1,0])).all (fun vp =>
    ground.countOf vp (orbitFam (sertables.tableD 3) 60
      (shiftV (sertables.tableD 3) [0,1,0])) == 1)) = true
    ∧ (sertables.serWeylD 3 (shiftV (sertables.tableD 3) [0,1,0])).length
      = (orbitFam (sertables.tableD 3) 60
          (shiftV (sertables.tableD 3) [0,1,0])).length := by decide +kernel

example : memberchar.mShapeRead (sertables.tableB 3)
    (multFam (sertables.tableB 3) (gramOf (sertables.tableB 3)) 60 [0,1,0]) := by
  decide +kernel
example : memberchar.symRead (sertables.tableB 3)
    (multFam (sertables.tableB 3) (gramOf (sertables.tableB 3)) 60 [0,1,0]) := by
  decide +kernel
example : memberchar.topRead
    (multFam (sertables.tableB 3) (gramOf (sertables.tableB 3)) 60 [0,1,0])
    (poly.pnorm (natV [0,1,0])) := by decide +kernel
example : memberchar.supportRead (sertables.tableB 3)
    (multFam (sertables.tableB 3) (gramOf (sertables.tableB 3)) 60 [0,1,0])
    ((multFam (sertables.tableB 3) (gramOf (sertables.tableB 3)) 60
      [0,1,0]).map (foldWits (sertables.tableB 3) (natV [0,1,0])))
    (poly.pnorm (natV [0,1,0])) := by decide +kernel
example : memberchar.mShapeRead sertables.tableG2
    (multFam sertables.tableG2 (gramRows sertables.tableG2 sertables.adjG2)
      16 [0,1]) := by decide +kernel
example : memberchar.symRead sertables.tableG2
    (multFam sertables.tableG2 (gramRows sertables.tableG2 sertables.adjG2)
      16 [0,1]) := by decide +kernel
example : memberchar.supportRead sertables.tableG2
    (multFam sertables.tableG2 (gramRows sertables.tableG2 sertables.adjG2)
      16 [0,1])
    ((multFam sertables.tableG2 (gramRows sertables.tableG2 sertables.adjG2)
      16 [0,1]).map (foldWits sertables.tableG2 (natV [0,1])))
    (poly.pnorm (natV [0,1])) := by decide +kernel

/-! The produced Gram's defining read: the Cartan rows against the
produced rows read the determinant-scaled length diagonal. -/

example : elim.matOneValue
    (elim.matMul (sertables.tableB 2).cartan (gramOf (sertables.tableB 2)))
    (ground.matOf 2 2 (fun i j =>
      if i == j then BPair.ofNat (2 * getAt 0 (sertables.tableB 2).lenNums i)
      else BPair.unit)) := by decide +kernel
example : elim.matOneValue
    (elim.matMul (sertables.tableD 4).cartan (gramOf (sertables.tableD 4)))
    (ground.matOf 4 4 (fun i j =>
      if i == j then BPair.ofNat (4 * getAt 0 (sertables.tableD 4).lenNums i)
      else BPair.unit)) := by decide +kernel
example : elim.matOneValue
    (elim.transposeM (gramRows sertables.tableE7 sertables.adjE7))
    (gramRows sertables.tableE7 sertables.adjE7) := by decide +kernel

/-! ## The interface laws at the instances

The count laws at `B_2` and `G_2` run whole rows; `B_3` and `D_4`
pin single-target reads; the class, Casimir and enumeration laws
run across the classification. -/

example : unitLaw (dataB 2) [0,2] [0,2] := by decide +kernel
example : commLaw (dataB 2) [0,2] [1,0] [1,2] := by decide +kernel
example : cartanLaw (dataB 2) [0,2] [0,2] := by decide +kernel
example : assocLaw (dataB 2) [0,2] [0,2] [0,2] [0,2] := by decide +kernel
example : dimLaw (dataB 2) [0,2] [0,2] := by decide +kernel
example : driftLaw (dataB 2) [0,2] := by decide +kernel
example : driftLaw (dataB 2) [1,0] := by decide +kernel
example : driftLaw (dataB 2) [2,0] := by decide +kernel
example : casPos (dataB 2) [1,0] := by decide +kernel
example : clsLaw (dataB 2) [0,1] [0,1] := by decide +kernel
example : clsDualLaw (dataB 2) [0,1] := by decide +kernel
example : clsThetaLaw (dataB 2) := by decide +kernel
example : belowSound (dataB 2) 60 := by decide +kernel
example : oneUnit (dataB 2) ((dataB 2).below 60) := by decide +kernel

example : unitLaw (dataG2) [1,0] [1,0] := by decide +kernel
example : cartanLaw (dataG2) [0,1] [0,1] := by decide +kernel
example : dimLaw (dataG2) [0,1] [0,1] := by decide +kernel
example : driftLaw (dataG2) [0,1] := by decide +kernel
example : driftLaw (dataG2) [1,0] := by decide +kernel
example : casPos (dataG2) [1,0] := by decide +kernel
example : belowSound (dataG2) 60 := by decide +kernel

example : dimLaw (dataB 3) [0,1,0] [0,1,0] := by decide +kernel
example : driftLaw (dataB 3) [0,1,0] := by decide +kernel
example : cartanLaw (dataB 3) [0,1,0] [0,1,0] := by decide +kernel
example : belowSound (dataB 3) 130 := by decide +kernel
example : oneUnit (dataB 3) ((dataB 3).below 130) := by decide +kernel
example : clsDualLaw (dataB 3) [0,0,1] := by decide +kernel
example : clsThetaLaw (dataB 3) := by decide +kernel

example : cartanLaw (dataC 3) [2,0,0] [2,0,0] := by decide +kernel
example : dimLaw (dataC 3) [2,0,0] [2,0,0] := by decide +kernel
example : driftLaw (dataC 3) [2,0,0] := by decide +kernel
example : casPos (dataC 3) [1,0,0] := by decide +kernel
example : clsDualLaw (dataC 3) [1,0,0] := by decide +kernel
example : clsThetaLaw (dataC 3) := by decide +kernel

/-- The fork's own count at `D_4`: the two spinors fuse to the
vector once, the count read through the fork keys' wiring. -/
example : (dataD 4).count [0,0,1,0] [0,0,0,1] [1,0,0,0] = 1 := by decide +kernel
example : cartanLaw (dataD 4) [0,1,0,0] [0,1,0,0] := by decide +kernel
example : driftLaw (dataD 4) [0,1,0,0] := by decide +kernel
example : casPos (dataD 4) [0,0,1,0] := by decide +kernel
example : clsDualLaw (dataD 4) [0,0,1,0] := by decide +kernel
example : clsThetaLaw (dataD 4) := by decide +kernel

/-- The `D` coordinate solve's round trips: the displayed coroot
pairs read the coordinate display back at the fork seed. -/
example : sertables.corootsD (sertables.coordsD
      (shiftV (sertables.tableD 4) [0,1,0,0]))
    = shiftV (sertables.tableD 4) [0,1,0,0] := by decide +kernel
example : sertables.corootsD (sertables.coordsD
      (shiftV (sertables.tableD 5) [1,0,2,1,0]))
    = shiftV (sertables.tableD 5) [1,0,2,1,0] := by decide +kernel
/-- The unit read at `D_5`'s spinor pair: the count field against
the involution at the exchanged fork keys, the one dual read off
the self-dual labels. -/
example : unitLaw (dataD 5) [0,0,0,1,0] [0,0,0,0,1] := by decide +kernel
example : casPos (dataD 5) [1,0,0,0,0] := by decide +kernel
example : clsDualLaw (dataD 5) [0,0,0,1,0] := by decide +kernel
example : clsThetaLaw (dataD 5) := by decide +kernel

example : casPos (dataF4) [0,0,0,1] := by decide +kernel
example : clsThetaLaw (dataF4) := by decide +kernel

example : casPos (dataE6) [1,0,0,0,0,0] := by decide +kernel
example : clsDualLaw (dataE6) [1,0,0,0,0,0] := by decide +kernel
example : clsThetaLaw (dataE6) := by decide +kernel

example : casPos (dataE7) [0,0,0,0,0,0,1] := by decide +kernel
example : clsDualLaw (dataE7) [0,0,0,0,0,0,1] := by decide +kernel
example : clsThetaLaw (dataE7) := by decide +kernel

example : casPos (dataE8) (memberdata.thetaKey sertables.tableE8) := by decide +kernel
example : clsThetaLaw (dataE8) := by decide +kernel

/-! ## The value pins at the displayed data

The `θ` keys, the `θ`-square rows, the dimensions, the Casimir
ratios (`lem:casfloor`'s end lists at the cleared pairs), the
diagonal (the base, `prop:row`'s member read), and the
involutions' reads. -/

example : (dataB 2).theta = [0, 2] := by decide +kernel
example : (dataB 3).theta = [0, 1, 0] := by decide +kernel
example : (dataC 3).theta = [2, 0, 0] := by decide +kernel
example : (dataD 4).theta = [0, 1, 0, 0] := by decide +kernel
example : (dataG2).theta = [0, 1] := by decide +kernel
example : (dataF4).theta = [1, 0, 0, 0] := by decide +kernel
example : (dataE6).theta = [0, 1, 0, 0, 0, 0] := by decide +kernel
example : (dataE7).theta = [1, 0, 0, 0, 0, 0, 0] := by decide +kernel
example : (dataE8).theta = [0, 0, 0, 0, 0, 0, 0, 1] := by decide +kernel

example : (dataB 2).row [0,2] [0,2]
    = [[0,0], [0,2], [0,4], [1,0], [1,2], [2,0]] := by decide +kernel
example : (dataG2).row [0,1] [0,1]
    = [[0,0], [0,1], [0,2], [2,0], [3,0]] := by decide +kernel

example : (dataB 2).count [0,2] [0,2] [0,2] = 1 := by decide +kernel
example : (dataB 3).count [0,1,0] [0,1,0] [0,1,0] = 1 := by decide +kernel
example : (dataG2).count [0,1] [0,1] [0,1] = 1 := by decide +kernel
example : (dataB 2).c1 = 1 := by decide +kernel
example : (dataF4).c1 = 1 := by decide +kernel

example : (dataB 2).dim [0,2] = 10 := by decide +kernel
example : (dataB 3).dim [0,1,0] = 21 := by decide +kernel
example : (dataB 3).dim [0,0,1] = 8 := by decide +kernel
example : (dataC 3).dim [2,0,0] = 21 := by decide +kernel
example : (dataD 4).dim [0,1,0,0] = 28 := by decide +kernel
example : (dataD 5).dim [0,0,0,1,0] = 16 := by decide +kernel
example : (dataG2).dim [0,1] = 14 := by decide +kernel
example : (dataF4).dim [1,0,0,0] = 52 := by decide +kernel
example : (dataE6).dim [0,1,0,0,0,0] = 78 := by decide +kernel
example : (dataE7).dim [1,0,0,0,0,0,0] = 133 := by decide +kernel
example : (dataE8).dim [0,0,0,0,0,0,0,1] = 248 := by decide +kernel

/-- The spinor's ratio at `B_3`: `ĉ₂ = [ℓ(2ℓ+1) : 8(r+1)]` reads
`21` against the adjoint's `40` (`lem:casfloor`'s end list). -/
example : (dataB 3).c2N [0,0,1] = 21 ∧ (dataB 3).c2D = 40 := by decide +kernel
/-- The vector's ratio at `B_3`: `[ℓ : r+1]` at `24` against
`40`. -/
example : (dataB 3).c2N [1,0,0] = 24 := by decide +kernel
/-- `G_2`'s short dominant root at `[1:2]` (`lem:casfloor`). -/
example : (dataG2).c2N [1,0] = 24 ∧ (dataG2).c2D = 48 := by decide +kernel

example : (dataB 3).dual [1,2,1] = [1,2,1] := by decide +kernel
example : (dataD 4).dual [0,0,1,0] = [0,0,1,0] := by decide +kernel
example : (dataD 5).dual [0,0,0,1,0] = [0,0,0,0,1] := by decide +kernel
example : (dataD 5).dual [0,0,0,0,1] = [0,0,0,1,0] := by decide +kernel
example : (dataE6).dual [1,0,0,0,0,0] = [0,0,0,0,0,1] := by decide +kernel
example : (dataE6).dual [0,0,1,0,0,0] = [0,0,0,0,1,0] := by decide +kernel
example : (dataE7).dual [0,0,0,0,0,0,1] = [0,0,0,0,0,0,1] := by decide +kernel

example : (dataB 3).clsFloorN 1 = (dataB 3).c2N [0,0,1] := by decide +kernel
example : (dataD 5).clsFloorN 2 = (dataD 5).c2N [1,0,0,0,0] := by decide +kernel

/-! The polynomial tier's ties: the instance fields against
`lem:serstable`(i)'s cleared pairs at the leading words, one
cross-multiplied read each (`con:fusion`'s series clause, the
fields at the rank against the stated pairs). -/

example : (dataB 3).c2N (serstable.member [1] 3) * serstable.casDenB 3
    = serstable.casNumB [1] 3 * (dataB 3).c2D := by decide +kernel
example : (dataC 3).c2N (serstable.member [2] 3) * serstable.casDenC 3
    = serstable.casNumC [2] 3 * (dataC 3).c2D := by decide +kernel
example : (dataB 3).dim (serstable.member [1] 3) * serstable.dimDenB [1] 3
    = serstable.dimNumB [1] 3 := by decide +kernel
example : (dataD 4).dim (serstable.member [1,1] 4) * serstable.dimDenD [1,1] 4
    = serstable.dimNumD [1,1] 4 := by decide +kernel

/-! ## The committed refusals

The involution's exchange at `D_5` is load-bearing: the identity
involution refuses the dual-class law at the spinor.  The Casimir
field is load-bearing in the drift: the flattened read refuses.
The walks' fuel is load-bearing: the starved closure refuses the
Cartan strictness at `B_2`'s own data. -/

example : ¬ clsDualLaw { dataD 5 with dual := fun a => a }
    [0,0,0,1,0] := by decide +kernel
example : ¬ driftLaw { dataB 2 with c2N := fun _ => 1 } [0,2] := by decide +kernel
example : ¬ cartanLaw
    (dataOf (sertables.tableB 2) (gramOf (sertables.tableB 2)) 0
      (fusion.clsB 2) (fun x y => (x + y) % 2) (fun _ => 0))
    [0,2] [0,2] := by decide +kernel
