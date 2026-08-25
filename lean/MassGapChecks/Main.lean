import MassGap.Main
import MassGap.K
import MassGap.Freeend
/-!
The check module for `thm:main`: the batteries re-read the
statement's member layer by kernel `decide` — clause (ii) at
every committed member through the carried datum (the base and
residue the member's own table reads), and the low-index
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
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground gentable sertables row main lattice elim inertia fusion

/-! Clause (ii) at every committed member through the carried
datum. -/

example : clauseII (.A 0) := by decide +kernel
example : clauseII (.A 1) := by decide +kernel
example : clauseII (.A 4) := by decide +kernel
example : clauseII (.B 0) := by decide +kernel
example : clauseII (.B 1) := by decide +kernel
example : clauseII (.B 2) := by decide +kernel
example : clauseII (.C 0) := by decide +kernel
example : clauseII (.C 1) := by decide +kernel
example : clauseII (.D 0) := by decide +kernel
example : clauseII (.D 1) := by decide +kernel
example : clauseII .G2 := by decide +kernel
example : clauseII .F4 := by decide +kernel
example : clauseII .E6 := by decide +kernel
example : clauseII .E7 := by decide +kernel
example : clauseII .E8 := by decide +kernel

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
