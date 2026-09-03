import MassGap.Main
import MassGap.K
import MassGap.Freeend
/-!
The check module for `thm:main`: the batteries re-read the
statement's member layer — clause (ii) at every committed member
through the carried datum, the theorem routes at the members' own
base and residue occupancies with the full reads' decides
`thm:closing`'s own battery, and the low-index
coincidence reads at the floors: `Sp(1)` at `SU(2)` the exact
table identity (`tableC 1`'s six fields read `tableA 1`'s),
`Sp(2)` at `Spin(5)` and `Spin(6)` at `SU(4)` the derived reads'
agreements across the relabelings (the residue, the dimension
fold, the support count and the positive count each one value at
the pair), and `Spin(4)`'s exit from the simple list read at its
Cartan, the fork clause degenerating to the two disjoint keys;
`Spin(3)` at `SU(2)` is the dictionary's identification, the
below-floor `B`-table degenerate at its short θ.

The wiring `main.data` reads beside the table: the base's two
spellings one count at the walked members (`prop:row`'s member
diagonal, θ's occupied coroot support against the interface's
`c1`, the two `A`-arms with `B`, `C`, `D` and `G_2` at their
committed walks), the θ-Casimir's value at every committed member
with the five fixed among them (`c2D` the θ key's Gram evaluation
at `C₂(θ) = 2(r+1)` on the member's clearing scale, `prop:anchor`;
the `A`-arm `casfloor.thetaRead`'s theorem route at every
residue), and the member windows at the committed square
(`lem:freeend`'s member clause with `def:K`'s free-end reading):
the window diagonal one loop at four times the member floor's
numerator, the level at or below every occupied content and
attained at the floor label's own loop, the cut holding at the
floor with the edge neutral and failing beyond — the beyond-floor
split read at the datum first, the refusal the reversal's own —
with the refused split's witness the loop's own vector
(`thm:certconstruct`).  Each window's two enumeration reads sit
in one declaration, the shared enumeration one kernel evaluation
— the module's priced pins, `Spin(5)`, `Sp(3)` and `G_2` the
committed members with the `A`-arm's window beside them.
-/
set_option maxHeartbeats 4000000

open ground gentable sertables row main lattice elim inertia fusion

/-! Clause (ii) at every committed member through the theorem
routes: `clauseII` is definitionally `thm:closing`'s read at the
member's base and residue, whose full-read decides sit at that
theorem's own battery, and the wiring reads here through the
occupancy door at the same members with the series' routes at
ranks past every decide. -/

example : clauseII (.A 0) := clauseII_A 0
example : clauseII (.A 1) := clauseII_A 1
example : clauseII (.A 4) := clauseII_A 4
example : clauseII (.A 30) := clauseII_A 30
example : clauseII (.B 0) := clauseII_B 0
example : clauseII (.B 1) := clauseII_B 1
example : clauseII (.B 2) := clauseII_B 2
example : clauseII (.B 28) := clauseII_B 28
example : clauseII (.C 0) := clauseII_C 0
example : clauseII (.C 1) := clauseII_C 1
example : clauseII (.C 28) := clauseII_C 28
example : clauseII (.D 0) := clauseII_D 0
example : clauseII (.D 1) := clauseII_D 1
example : clauseII (.D 28) := clauseII_D 28
example : clauseII .G2 := clauseII_all .G2
example : clauseII .F4 := clauseII_all .F4
example : clauseII .E6 := clauseII_all .E6
example : clauseII .E7 := clauseII_all .E7
example : clauseII .E8 := clauseII_all .E8

/-! The residues and bases through the carried datum, the members
item's displayed values. -/

example : main.residue (.A 0) = 1 := by decide +kernel
example : main.residue (.B 0) = 2 := by decide +kernel
example : main.residue (.C 0) = 3 := by decide +kernel
example : main.residue (.D 0) = 5 := by decide +kernel
example : main.residue .E8 = 29 := by decide +kernel
example : main.base (.A 0) = 1 := by decide +kernel
example : main.base (.A 1) = 2 := by decide +kernel
example : main.base (.B 0) = 1 := by decide +kernel
example : main.base .E8 = 1 := by decide +kernel

/-! The low-index coincidences at the floors.  `Sp(1)` at
`SU(2)`: the exact table identity. -/

example : (tableC 1).rank = (tableA 1).rank := rfl
example : (tableC 1).lenNums = (tableA 1).lenNums := rfl
example : (tableC 1).lenDen = (tableA 1).lenDen := rfl
example : (tableC 1).cartan = (tableA 1).cartan := rfl
example : (tableC 1).posFolds = (tableA 1).posFolds := rfl
example : (tableC 1).thetaFold = (tableA 1).thetaFold := rfl

/-! `Sp(2)` at `Spin(5)` and `Spin(6)` at `SU(4)`: the derived
reads' agreements across the relabelings. -/

example : gentable.residue (tableC 2) = gentable.residue (tableB 2) := by
  decide +kernel
example : dTheta (tableC 2) = dTheta (tableB 2) := by decide +kernel
example : supportCount (tableC 2) = supportCount (tableB 2) := by decide +kernel
example : posCount (tableC 2) = posCount (tableB 2) := by decide +kernel
example : gentable.residue (tableD 3) = gentable.residue (tableA 3) := by
  decide +kernel
example : dTheta (tableD 3) = dTheta (tableA 3) := by decide +kernel
example : supportCount (tableD 3) = supportCount (tableA 3) := by decide +kernel
example : posCount (tableD 3) = posCount (tableA 3) := by decide +kernel

/-! `Spin(4)`'s exit from the simple list: the fork clause
degenerates to two disjoint keys at `ℓ = 2`. -/

example : (tableD 2).cartan
    = [[BPair.ofNat 2, BPair.unit], [BPair.unit, BPair.ofNat 2]] := rfl

/-! The wiring's base coherence: the interface's `c1` against the
table's support count, one value at the walked members. -/

example : (data (.A 0)).c1 = base (.A 0) := by decide +kernel
example : (data (.A 1)).c1 = base (.A 1) := by decide +kernel
example : (data (.B 0)).c1 = base (.B 0) := by decide +kernel
example : (data (.B 1)).c1 = base (.B 1) := by decide +kernel
example : (data (.C 0)).c1 = base (.C 0) := by decide +kernel
example : (data (.D 0)).c1 = base (.D 0) := by decide +kernel
example : (data .G2).c1 = base .G2 := by decide +kernel

/-! The wiring's θ-Casimir read: `c2D`, the θ key's Gram
evaluation, reads `C₂(θ) = 2(r+1)` at the member's clearing scale
(`prop:anchor`; `lem:casfloor`'s display), one committed value per
member with the five fixed among them; the `A`-arm is the theorem
at every residue (`casfloor.thetaRead`, `dfQ(θ) = 2d_f²`). -/

example (g : Nat) :
    (data (.A g)).c2N ((data (.A g)).theta) = (data (.A g)).c2D :=
  casfloor.thetaRead g
example : (data (.B 0)).c2D = 24 := by decide +kernel
example : (data (.B 1)).c2D = 40 := by decide +kernel
example : (data (.C 0)).c2D = 32 := by decide +kernel
example : (data (.D 0)).c2D = 96 := by decide +kernel
example : (data .G2).c2D = 48 := by decide +kernel
example : (data .F4).c2D = 36 := by decide +kernel
example : (data .E6).c2D = 144 := by decide +kernel
example : (data .E7).c2D = 144 := by decide +kernel
example : (data .E8).c2D = 120 := by decide +kernel

/-! The member windows at the committed square, the free-end
level the member's floor. -/

private def u : BPair := BPair.unit

/-! `Spin(5)`'s window at cutoff forty: the spinor floor `10` at
the clearing twenty-four, the level its four-link read. -/

/-- The window's level gap: one loop at the spinor floor's
four-link read. -/
private def etB : Mat := [[u, u], [u, ⟨41, 1⟩]]

example : K.freeGap (data (.B 0)) square 40 = etB
    ∧ freeend.levelRead (data (.B 0)) square 40 40 := by decide +kernel
example : freeend.belowFloor (data (.B 0)) 40 10 := by decide +kernel
example : carrier.contentN (data (.B 0))
    (freeend.attainConf (data (.B 0)) square sqPlaq [0, 1]) = 40 := by
  decide +kernel
example : carrier.occupied (data (.B 0)) square
    (freeend.attainConf (data (.B 0)) square sqPlaq [0, 1]) = true := by
  decide +kernel
example : K.floorRead etB (idMat 2) u 1
    (⟨⟨exch2, by decide +kernel⟩, ⟨exch2w, by decide +kernel⟩, [.one ⟨41, 1⟩], 1, rfl⟩
      : Split 2) := by decide +kernel
example : K.cutRead (matMul etB etB) etB 4 10 1
    (⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [], 2, rfl⟩ : Split 2) := by
  decide +kernel
example : splitRead
    (siteDatum (matScale 1 (matMul etB etB)) (matScale 44 etB))
    (⟨⟨exch2, by decide +kernel⟩, ⟨exch2w, by decide +kernel⟩, [.one ⟨1, 161⟩], 1, rfl⟩
      : Split 2) := by decide +kernel
example : ¬ K.cutRead (matMul etB etB) etB 4 11 1
    (⟨⟨exch2, by decide +kernel⟩, ⟨exch2w, by decide +kernel⟩, [.one ⟨1, 161⟩], 1, rfl⟩
      : Split 2) := by decide +kernel
example : certconstruct.witnessRead (matMul etB etB)
    (matScale 44 etB) [u, ⟨2, 1⟩] := by decide +kernel

/-! The pencil interface at `Spin(5)`'s floor window, the index the
spinor loop alone: the loop pencil — the window list's diagonal at
the spinor loop's four-link read,
the identity gram at its split, and the one plaquette term the
member's fusion counts, `winM`'s diagonal, capped two-sidedly at the
adjoint dimension ten (`thm:pairpencil`'s fields at a loop window
through `thm:main`'s wiring). -/

example : (data (.B 0)).dim ((data (.B 0)).theta) = 10 := by decide +kernel
example : pairpencil.pencilRead (data (.B 0)) square 40 2
    ((winLabels (.B 0)).map (fun l => List.replicate 4 l)) (winE (.B 0))
    (idMat 2) (winM (.B 0)) (inertia.mkSplit 2 (idMat 2))
    [(winM (.B 0),
      inertia.mkSplit 2 (siteDatum (inertia.matScaleB (BPair.ofNat 10) (idMat 2))
        (winM (.B 0))),
      inertia.mkSplit 2 (matAdd (inertia.matScaleB (BPair.ofNat 10) (idMat 2))
        (winM (.B 0))))] := by decide +kernel

/-! `Sp(3)`'s window at cutoff fifty-six: the first fundamental's
floor `14` at the clearing thirty-two. -/

private def etC : Mat := [[u, u], [u, ⟨57, 1⟩]]

example : K.freeGap (data (.C 0)) square 56 = etC
    ∧ freeend.levelRead (data (.C 0)) square 56 56 := by decide +kernel
example : freeend.belowFloor (data (.C 0)) 56 14 := by decide +kernel
example : carrier.contentN (data (.C 0))
    (freeend.attainConf (data (.C 0)) square sqPlaq [1, 0, 0]) = 56 := by
  decide +kernel
example : carrier.occupied (data (.C 0)) square
    (freeend.attainConf (data (.C 0)) square sqPlaq [1, 0, 0]) = true := by
  decide +kernel
example : K.floorRead etC (idMat 2) u 1
    (⟨⟨exch2, by decide +kernel⟩, ⟨exch2w, by decide +kernel⟩, [.one ⟨57, 1⟩], 1, rfl⟩
      : Split 2) := by decide +kernel
example : K.cutRead (matMul etC etC) etC 4 14 1
    (⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [], 2, rfl⟩ : Split 2) := by
  decide +kernel
example : splitRead
    (siteDatum (matScale 1 (matMul etC etC)) (matScale 60 etC))
    (⟨⟨exch2, by decide +kernel⟩, ⟨exch2w, by decide +kernel⟩, [.one ⟨1, 225⟩], 1, rfl⟩
      : Split 2) := by decide +kernel
example : ¬ K.cutRead (matMul etC etC) etC 4 15 1
    (⟨⟨exch2, by decide +kernel⟩, ⟨exch2w, by decide +kernel⟩, [.one ⟨1, 225⟩], 1, rfl⟩
      : Split 2) := by decide +kernel
example : certconstruct.witnessRead (matMul etC etC)
    (matScale 60 etC) [u, ⟨2, 1⟩] := by decide +kernel

/-! `G_2`'s window at cutoff ninety-six: the short dominant root's
floor `24` at the clearing forty-eight, the fixed members' family
read beside the series'. -/

private def etG : Mat := [[u, u], [u, ⟨97, 1⟩]]

example : K.freeGap (data .G2) square 96 = etG
    ∧ freeend.levelRead (data .G2) square 96 96 := by decide +kernel
example : freeend.belowFloor (data .G2) 96 24 := by decide +kernel
example : carrier.contentN (data .G2)
    (freeend.attainConf (data .G2) square sqPlaq [1, 0]) = 96 := by
  decide +kernel
example : carrier.occupied (data .G2) square
    (freeend.attainConf (data .G2) square sqPlaq [1, 0]) = true := by
  decide +kernel
example : K.floorRead etG (idMat 2) u 1
    (⟨⟨exch2, by decide +kernel⟩, ⟨exch2w, by decide +kernel⟩, [.one ⟨97, 1⟩], 1, rfl⟩
      : Split 2) := by decide +kernel
example : K.cutRead (matMul etG etG) etG 4 24 1
    (⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [], 2, rfl⟩ : Split 2) := by
  decide +kernel
example : splitRead
    (siteDatum (matScale 1 (matMul etG etG)) (matScale 100 etG))
    (⟨⟨exch2, by decide +kernel⟩, ⟨exch2w, by decide +kernel⟩, [.one ⟨1, 385⟩], 1, rfl⟩
      : Split 2) := by decide +kernel
example : ¬ K.cutRead (matMul etG etG) etG 4 25 1
    (⟨⟨exch2, by decide +kernel⟩, ⟨exch2w, by decide +kernel⟩, [.one ⟨1, 385⟩], 1, rfl⟩
      : Split 2) := by decide +kernel
example : certconstruct.witnessRead (matMul etG etG)
    (matScale 100 etG) [u, ⟨2, 1⟩] := by decide +kernel

/-! The `A`-arm's window through the wiring: the fundamental floor
`3` at the clearing eight, `lem:freeend`'s label-calculus read at
the carried datum. -/

example : freeend.levelRead (data (.A 0)) square 12 12 := by
  decide +kernel

/-! Clause (i)'s member sweeps at the committed floor windows: the
two count-one chains and the tie decided whole per member — the
`A`-arm at five residues beside the series and the five fixed
members — with the window data's enumeration ties, the committed
magnetic matrices tied to the wiring's own walk
(`pairpencil.loopMag`) at the walked members and the `E7` and `E8`
walks priced at the record beside the `A`-series' fourth residue's
(`E8`'s matrix `prop:repring`'s unit read with `prop:row`'s base at
the self-dual θ, the tex's own values), the electric matrices at
the standing committed level gaps with the multi-loop window's tie
at the second `A`-arm, the counts carried to an interior ray
through the theorem route beside its decided twin, and one refusal
per binder: the tie at the member pair one beyond, the sample's
split forged at the vacuum's side, the foot shifted off the free
end, the range's top beyond the cover's priced magnitude bound, and
the sweep at a level beyond the window's content refusing the
count; and the universal theorem's routes beside the decided twins —
`D₄`'s four-loop window and `E₈`'s coupled window read off
`clauseI_all` outright, one series route per series at a rank past
every decide. -/

example : clauseI (.A 0) := by decide +kernel
example : clauseI (.A 1) := by decide +kernel
example : clauseI (.A 2) := by decide +kernel
example : clauseI (.A 3) := by decide +kernel
example : clauseI (.A 4) := by decide +kernel
example : clauseI (.B 1) := by decide +kernel
example : clauseI (.B 2) := by decide +kernel
example : clauseI (.C 0) := by decide +kernel
example : clauseI (.C 1) := by decide +kernel
example : clauseI (.D 0) := clauseI_all (.D 0)
example : clauseI (.D 1) := by decide +kernel
example : clauseI .G2 := by decide +kernel
example : clauseI .F4 := by decide +kernel
example : clauseI .E6 := by decide +kernel
example : clauseI .E7 := by decide +kernel
example : clauseI .E8 := clauseI_all .E8

example : clauseI (.A 7) := clauseI_all (.A 7)
example : clauseI (.B 30) := clauseI_all (.B 30)
example : clauseI (.C 30) := clauseI_all (.C 30)
example : clauseI (.D 30) := clauseI_all (.D 30)

/-- `Spin(5)`'s clause read, named once and consumed at its own pin
and the theorem route's hypothesis. -/
private theorem clB0 : clauseI (.B 0) := by decide +kernel

example : clauseI (.B 0) := clB0

/-! The window data: the enumeration ties at the committed orders,
the cutoffs the floor contents' four-link reads, the magnetic
matrices the wiring's own walks, and the electric matrices the
standing committed level gaps. -/

example : (winLabels (.A 0)).length + 1 = winO (.A 0) := by decide +kernel
example : (winLabels (.A 1)).length + 1 = winO (.A 1) := by decide +kernel
example : (winLabels (.A 2)).length + 1 = winO (.A 2) := by decide +kernel
example : (winLabels (.A 3)).length + 1 = winO (.A 3) := by decide +kernel
example : (winLabels (.A 4)).length + 1 = winO (.A 4) := by decide +kernel
example : (winLabels (.B 0)).length + 1 = winO (.B 0) := by decide +kernel
example : (winLabels (.B 1)).length + 1 = winO (.B 1) := by decide +kernel
example : (winLabels (.B 2)).length + 1 = winO (.B 2) := by decide +kernel
example : (winLabels (.C 0)).length + 1 = winO (.C 0) := by decide +kernel
example : (winLabels (.C 1)).length + 1 = winO (.C 1) := by decide +kernel
example : (winLabels (.D 0)).length + 1 = winO (.D 0) := by decide +kernel
example : (winLabels (.D 1)).length + 1 = winO (.D 1) := by decide +kernel
example : (winLabels .G2).length + 1 = winO .G2 := by decide +kernel
example : (winLabels .F4).length + 1 = winO .F4 := by decide +kernel
example : (winLabels .E6).length + 1 = winO .E6 := by decide +kernel
example : (winLabels .E7).length + 1 = winO .E7 := by decide +kernel
example : (winLabels .E8).length + 1 = winO .E8 := by decide +kernel

example : winCut (.A 0) = 12 ∧ winCut (.A 1) = 32 ∧ winCut (.A 2) = 60
    ∧ winCut (.B 0) = 40 ∧ winCut (.B 1) = 84 ∧ winCut (.B 2) = 128
    ∧ winCut (.C 0) = 56 ∧ winCut (.C 1) = 72 ∧ winCut (.D 0) = 224
    ∧ winCut (.D 1) = 288 ∧ winCut .G2 = 96 ∧ winCut .F4 = 96
    ∧ winCut .E6 = 416 ∧ winCut .E7 = 456 ∧ winCut .E8 = 480 := by
  decide +kernel

example : winM (.A 0) = pairpencil.loopMag (data (.A 0))
    (winLabels (.A 0)) := by decide +kernel
example : winM (.A 1) = pairpencil.loopMag (data (.A 1))
    (winLabels (.A 1)) := by decide +kernel
example : winM (.A 2) = pairpencil.loopMag (data (.A 2))
    (winLabels (.A 2)) := by decide +kernel
example : winM (.B 0) = pairpencil.loopMag (data (.B 0))
    (winLabels (.B 0)) := by decide +kernel
example : winM (.B 1) = pairpencil.loopMag (data (.B 1))
    (winLabels (.B 1)) := by decide +kernel
example : winM (.B 2) = pairpencil.loopMag (data (.B 2))
    (winLabels (.B 2)) := by decide +kernel
example : winM (.C 0) = pairpencil.loopMag (data (.C 0))
    (winLabels (.C 0)) := by decide +kernel
example : winM (.C 1) = pairpencil.loopMag (data (.C 1))
    (winLabels (.C 1)) := by decide +kernel
example : winM (.D 0) = pairpencil.loopMag (data (.D 0))
    (winLabels (.D 0)) := by decide +kernel
example : winM (.D 1) = pairpencil.loopMag (data (.D 1))
    (winLabels (.D 1)) := by decide +kernel
example : winM .G2 = pairpencil.loopMag (data .G2)
    (winLabels .G2) := by decide +kernel
example : winM .F4 = pairpencil.loopMag (data .F4)
    (winLabels .F4) := by decide +kernel
example : winM .E6 = pairpencil.loopMag (data .E6)
    (winLabels .E6) := by decide +kernel

example : winE (.B 0) = etB := by decide +kernel
example : winE (.C 0) = etC := by decide +kernel
example : winE .G2 = etG := by decide +kernel
example : winE (.A 1) = K.freeGap (data (.A 1)) square (winCut (.A 1)) := by
  decide +kernel

/-! The counts carried to the interior: the theorem route at the
ray τ = 1/2 of `Spin(5)`'s window beside its decided twin, the
evaluated pair the committed split's own value. -/

private def spHalfB0 : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.one ⟨1, 5⟩, .one ⟨156, 1⟩], 0, rfl⟩

example : splitRead (cellcount.evalPC (sweepLo (.B 0)) ⟨2, 1⟩ 2 2)
    spHalfB0 := by decide +kernel

example : revAt spHalfB0 = 1 :=
  (clauseI_counts (.B 0) clB0 ⟨2, 1⟩ 2 (by decide +kernel)
    (by decide +kernel)).1 spHalfB0 (by decide +kernel)

/-! The refusals, one per binder. -/

example : ¬ (BPair.scale (⟨2, 1⟩ : BPair) 4
    + BPair.ofPos (4 * ground.posOfSucc (2 * winFloorN (.B 0) - 1))
    ≤ BPair.scale (⟨winLvl (.B 0), 1⟩ : BPair) 4) := by
  decide +kernel

private def spForgeB0 : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.one ⟨2, 1⟩, .one ⟨40, 1⟩], 0, rfl⟩

example : ¬ gappos.chainRead (sweepLo (.B 0)) 2 1 winFoot
    [(winTop, winCover (.B 0), (BPair.unit, 1), spForgeB0)] := by
  decide +kernel

example : ¬ gappos.chainRead (sweepLo (.B 0)) 2 1
    ⟨BPair.ofNat 1, 1⟩ (cellsLo (.B 0)) := by decide +kernel

example : ¬ gappos.chainRead (sweepLo (.B 0)) 2 1 winFoot
    [(⟨BPair.ofNat 2, 1⟩,
      cellcount.diagCover ⟨BPair.ofNat 2, 1⟩ ⟨2, 1⟩ ⟨2, 1⟩ 1,
      (BPair.unit, 1), sampleLo (.B 0))] := by decide +kernel

example : ¬ cellcount.countAt
    (freecell.freePMat (winE (.B 0)) (winM (.B 0)) (inertia.idMat 2)
      (ground.posOfSucc (4 * winFloorN (.B 0) + 1)) 1) 2
    BPair.unit 1 1
    (inertia.mkSplit 2 (cellcount.evalPC
      (freecell.freePMat (winE (.B 0)) (winM (.B 0)) (inertia.idMat 2)
        (ground.posOfSucc (4 * winFloorN (.B 0) + 1)) 1)
      BPair.unit 1 2)) := by decide +kernel
