import MassGap.Serdivisors
/-!
The check module for `lem:serdivisors`: the battery reads the three
members' whole record lists by kernel `decide` — the counts 47, 47
and 83, the unit sectors' Casimir identities at
`lem:serstable`(i)'s polynomials, the charged sectors' three-fold
gap identities, and both certificates at every record — and then
the classification's seven rows one at a time, each the stated
divisor's cross-multiplied evaluation at its stated rank reading
equal members: the `B` spinor pairs `(e₁+e₂, e₁+e₂+e₃+e₄)` at the
rank two and `(e₁+e₂+e₃+e₄, 2e₁)` at three, the `D` unit pair
`((2), (1,1,1,1))` at four, the `D` vector pairs
`((1,1,1), (1,1,1,1,1))` at four and `((3), (1,1,1,1,1))` at
seven, and the `D` spinor pairs `(e₁+e₂+e₃, 2e₁)` at four and
`(e₁+e₂+e₃+e₄, 2e₁+e₂)` at six.  The refusals isolate one
committed datum each: the unit tier's gap, at the `B` family `(2)`
carrying the gap two for four, where the identity parts with the
Casimir polynomial; the charged tier's base list, at the spinor
word `e₁` read against the vector's list; the domain floor, at the
`C` first fundamental pair `((3), (2,2,1))` read at the floor two,
its rank-two tie entering the window uncounted; the settled point,
at the `D` vector pair `((3), (1,1,1,1,1))` read at seven, the
radius sitting at eight; the clearance, at the same pair read at
four, the below-crossing ranks asked for the leading side they sit
off; and the root list's completeness, at the `D` unit pair with
its root withdrawn and again with the rank five forged onto it.
Beside the record tier sit the key-read refusals (the root fold's
key function, the form scale, the unit scale and the stored-word
map each isolated at one committed datum), the dot fold's reach
pin, the based member's entry reads into the row-value tier, and
the edge tier's batteries: per member one kernel-decided
conjunction of every exhibition, witness edge and collision read
at a rank inside the generic arm, with each conclusion routed
through its committed theorem beside it and the exhibition
floors' one-below refusals decided where the table refuses the
read.
-/

namespace serdivisors
open ground

/-- The rank-`ℓ` pair, the balance carrier's own read. -/
private def rk (k : Nat) : BPair :=
  ⟨ground.posOfSucc k, ground.posOfSucc 0⟩

/-- A table's family at its place. -/
private def fm (L : List SFam) (i : Nat) : SFam :=
  ground.getAt ⟨[], 0, 0, 0, 0⟩ L i

/-- A family's unscaled gap at the series fold. -/
private def gp (L : List SFam) (rA rB i : Nat) : poly.Poly :=
  gapL 1 (fm L i).m (fm L i).cu (fm L i).cd rA rB

/-- A comparison's divisor at its two places. -/
private def pp (L : List SFam) (rA rB i j : Nat) : poly.Poly :=
  poly.add (gp L rA rB i) (poly.neg (gp L rA rB j))

/-! The whole reads: the counts, the gap identities, and both
certificates over the three members' record lists. -/

theorem pin1 : recsReadB := by decide +kernel
theorem pin2 : recsReadC := by decide +kernel
theorem pin3 : recsReadD := by decide +kernel

/-! The classification's seven rows, one cross-multiplied
evaluation each. -/

theorem pin4 : (poly.eval (pp spinFams 2 2 1 3) (rk 2)).oneValue
    BPair.unit := by decide +kernel
theorem pin5 : (poly.eval (pp spinFams 2 2 3 4) (rk 3)).oneValue
    BPair.unit := by decide +kernel
theorem pin6 : (poly.eval (pp unitD 2 3 0 1) (rk 4)).oneValue
    BPair.unit := by decide +kernel
theorem pin7 : (poly.eval (pp vecD 2 3 0 3) (rk 4)).oneValue
    BPair.unit := by decide +kernel
theorem pin8 : (poly.eval (pp vecD 2 3 2 3) (rk 7)).oneValue
    BPair.unit := by decide +kernel
theorem pin9 : (poly.eval (pp spinFams 2 3 2 4) (rk 4)).oneValue
    BPair.unit := by decide +kernel
theorem pin10 : (poly.eval (pp spinFams 2 3 3 5) (rk 6)).oneValue
    BPair.unit := by decide +kernel

/-! The unit tier's refusal: the `B` family `(2)` at the forged
gap two parts with the Casimir polynomial's read. -/

theorem pin11 : ¬ unitRead serstable.casPolyB denB 1 2 2
    ⟨[2], 0, 2, 0, 3⟩ := by decide +kernel

/-! The charged tier's refusal: the spinor word `e₁` read against
the vector's base list parts with the displayed gap. -/

theorem pin12 : ¬ chargedRead vS basV wB 4 4 2 2 ⟨[1], 1, 3, 0, 3⟩ := by
  decide +kernel

/-! The domain floor's refusal: the `C` first fundamental pair
`((3), (2,2,1))` ties at the rank two, below the floor three; read
at the floor two the tie enters the window uncounted, and the
committed floor keeps it off the domain. -/

theorem pin13 : ¬ genericlift.rootsCert
    ⟨pp omegaC 1 0 2 3, 2, 5, 5, []⟩ := by decide +kernel
theorem pin14 : genericlift.rootsCert
    ⟨pp omegaC 1 0 2 3, 3, 5, 5, []⟩ := by decide +kernel

/-! The settled point's refusal: the `D` vector pair
`((3), (1,1,1,1,1))` at seven refuses the radius conjunct, the
leading-term bound sitting at eight. -/

theorem pin15 : ¬ genericlift.sideCert
    ⟨pp vecD 2 3 2 3, 4, 7, 7, [7]⟩ := by decide +kernel

/-! The clearance's refusal at the same pair: lowered to four it
asks the leading side of the ranks below the crossing, which sit
on the divisor's other side; the committed clearance seven keeps
them at the off-unit read. -/

theorem pin16 : ¬ genericlift.rootsCert
    ⟨pp vecD 2 3 2 3, 4, 4, 8, [7]⟩ := by decide +kernel
theorem pin17 : genericlift.rootsCert
    ⟨pp vecD 2 3 2 3, 4, 7, 8, [7]⟩ := by decide +kernel

/-! The root list's window at the same record: a listed rank at or
beyond the settled point eight, or listed twice, refuses. -/

theorem pin18 : ¬ genericlift.rootsCert
    ⟨pp vecD 2 3 2 3, 4, 7, 8, [7, 9]⟩ := by decide +kernel
theorem pin19 : ¬ genericlift.rootsCert
    ⟨pp vecD 2 3 2 3, 4, 7, 8, [7, 7]⟩ := by decide +kernel

/-! The root list's refusals at the `D` unit pair
`((2), (1,1,1,1))`: the rank four's withdrawal leaves an
equal-members read uncounted, and the rank five forged onto the
list counts a rank whose evaluation sits off the sum's unit. -/

theorem pin20 : ¬ genericlift.rootsCert
    ⟨pp unitD 2 3 0 1, 4, 6, 6, []⟩ := by decide +kernel
theorem pin21 : ¬ genericlift.rootsCert
    ⟨pp unitD 2 3 0 1, 4, 6, 6, [4, 5]⟩ := by decide +kernel

/-! The key-read refusals: the root fold's key function is
load-bearing at the spinor list, read with `wB` at `B` and `wD` at
`D` — each list refuses the other member's keys — the form scale
at the `C` charged tier refuses the halved read, the unit tier's
scale refuses the `C` doubled gap at one, and the stored-word map
refuses the full family word where the added word is its head
withdrawal. -/

theorem pin22 : ¬ chargedRead vS basOnes wD 4 4 2 2 ⟨[1], 1, 3, 0, 3⟩ := by
  decide +kernel
theorem pin23 : ¬ chargedRead vS basOnes wB 4 4 2 3 ⟨[1], 1, 3, 0, 3⟩ := by
  decide +kernel
theorem pin24 : ¬ chargedRead vC basC wC 1 2 1 0 ⟨[3], 2, 4, 0, 3⟩ := by
  decide +kernel
theorem pin25 : ¬ unitRead serstable.casPolyC denC 1 1 0
    ⟨[2, 2], 2, 0, 0, 4⟩ := by decide +kernel
theorem pin26 : ¬ chargedRead (fun w => w) basC wC 2 2 1 0
    ⟨[3], 2, 4, 0, 3⟩ := by decide +kernel

/-! The dot fold's reach: `dotN` folds at the shorter list, so the
spinor base list covers every stored spinor word — the words' keys
sit inside the base's five. -/

theorem pin27 : (spinFams.all
    (fun F => decide (F.word.length ≤ basOnes.length))) = true := by
  decide +kernel

/-! The based member's entry into `lem:serstable`(ii)'s row-value
tier: the length, positivity and shifted-key reads at the spinor
word `e₁` and the rank four, each beside its decided twin. -/

theorem pin28 : (basedV [1] 4 0).length = 4 := by decide +kernel
theorem pin29 : (basedV [1] 4 0).length = 4 := basedV_length [1] 4 0

theorem pin30 : 1 ≤ ground.getAt 0 (basedRho [1] 4 0) 2 := by decide +kernel
theorem pin31 : 1 ≤ ground.getAt 0 (basedRho [1] 4 0) 2 :=
  basedRho_pos [1] 4 0 2 (by decide +kernel)

theorem pin32 : (ground.getAt ground.BPair.unit
    (poly.pnorm (elim.vecAdd (basedV [1] 4 0)
      (sertables.rhoV (sertables.tableB 4)))) 1).oneValue
    (ground.BPair.ofNat (ground.getAt 0 (basedRho [1] 4 0) 1)) := by
  decide +kernel
theorem pin33 : (ground.getAt ground.BPair.unit
    (poly.pnorm (elim.vecAdd (basedV [1] 4 0)
      (sertables.rhoV (sertables.tableB 4)))) 1).oneValue
    (ground.BPair.ofNat (ground.getAt 0 (basedRho [1] 4 0) 1)) :=
  basedKap (sertables.tableB 4) [1] 4 0 rfl 1 (by decide +kernel)

/-! ## The edge tier's batteries

`lem:serdivisors`' families clause at the three members, pinned
per sector: every builder's exhibition (the moved content occupies
the θ content list once), every witness edge's vacant fold, and
every collision's occupied fold, each decided by kernel at a rank
inside the theorem's generic arm — one conjunction per member, the
θ content list's evaluations shared across its conjuncts — beside
the same conclusion routed through the committed theorem.  The edge
floor binders are reach frames (the folds vanish below them too),
so those pins are instances without refusal boundaries; the
exhibition floors are least ranks wherever the table refuses the
read one rank below — every `D` builder and seven of the `B`
builders, the refusals decided beside their members — while `nB`'s
and the `C` builders' reads hold below their floors, those binders
the members' clearance frames. -/

theorem pin34 : (row.thetaCount (sertables.tableB 7) (nA 7) = 1)
    ∧ (row.thetaCount (sertables.tableB 7) (nB 7) = 1)
    ∧ (row.thetaCount (sertables.tableB 7) (nC 7) = 1)
    ∧ (row.thetaCount (sertables.tableB 7) (nD 7) = 1)
    ∧ (row.thetaCount (sertables.tableB 7) (nE 7) = 1)
    ∧ (row.thetaCount (sertables.tableB 7) (nF 7) = 1)
    ∧ (row.thetaCount (sertables.tableB 7) (nG 7) = 1)
    ∧ (row.thetaCount (sertables.tableB 7) (nH 7) = 1)
    ∧ (serstable.letterFoldVal (sertables.tableB 7) (serstable.memberRho [1, 1] 7) (nA 7) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableB 7) (basedRho [] 7 0) (nB 7) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableB 7) (basedRho [1] 7 0) (nB 7) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableB 7) (basedRho [] 7 0) (nC 7) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableB 7) (basedRho [1] 7 0) (nC 7) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableB 7) (basedRho [1, 1] 7 0) (nC 7) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableB 7) (serstable.memberRho [1, 1] 7) (nC 7) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableB 7) (serstable.memberRho [1, 1] 7) (nD 7) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableB 7) (basedRho [1, 1] 7 0) (nD 7) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableB 7) (basedRho [1] 7 0) (nE 7) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableB 7) (serstable.memberRho [1, 1] 7) (nF 7) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableB 7) (basedRho [1, 1] 7 0) (nF 7) = 0)
    ∧ (1 ≤ serstable.letterFoldVal (sertables.tableB 7) (serstable.memberRho [1, 1] 7) (nB 7))
    ∧ (1 ≤ serstable.letterFoldVal (sertables.tableB 7) (serstable.memberRho [1, 1] 7) (nG 7))
    ∧ (1 ≤ serstable.letterFoldVal (sertables.tableB 7) (serstable.memberRho [1, 1] 7) (nH 7)) := by
  decide +kernel

theorem pin35 : row.thetaCount (sertables.tableB 7) (nA 7) = 1 :=
  nA_mem 7 (by decide +kernel)

theorem pin36 : row.thetaCount (sertables.tableB 7) (nB 7) = 1 :=
  nB_mem 7 (by decide +kernel)

theorem pin37 : row.thetaCount (sertables.tableB 7) (nC 7) = 1 :=
  nC_mem 7 (by decide +kernel)

theorem pin38 : row.thetaCount (sertables.tableB 7) (nD 7) = 1 :=
  nD_mem 7 (by decide +kernel)

theorem pin39 : row.thetaCount (sertables.tableB 7) (nE 7) = 1 :=
  nE_mem 7 (by decide +kernel)

theorem pin40 : row.thetaCount (sertables.tableB 7) (nF 7) = 1 :=
  nF_mem 7 (by decide +kernel)

theorem pin41 : row.thetaCount (sertables.tableB 7) (nG 7) = 1 :=
  nG_mem 7 (by decide +kernel)

theorem pin42 : row.thetaCount (sertables.tableB 7) (nH 7) = 1 :=
  nH_mem 7 (by decide +kernel)

theorem pin43 : serstable.letterFoldVal (sertables.tableB 7) (serstable.memberRho [1, 1] 7) (nA 7) = 0 :=
  edgeB_u1 7 (by decide +kernel)

theorem pin44 : serstable.letterFoldVal (sertables.tableB 7) (basedRho [] 7 0) (nB 7) = 0 :=
  edgeB_s1 7 (by decide +kernel)

theorem pin45 : serstable.letterFoldVal (sertables.tableB 7) (basedRho [1] 7 0) (nB 7) = 0 :=
  edgeB_s3 7 (by decide +kernel)

theorem pin46 : serstable.letterFoldVal (sertables.tableB 7) (basedRho [] 7 0) (nC 7) = 0 :=
  edgeB_s2 7 (by decide +kernel)

theorem pin47 : serstable.letterFoldVal (sertables.tableB 7) (basedRho [1] 7 0) (nC 7) = 0 :=
  edgeB_s4 7 (by decide +kernel)

theorem pin48 : serstable.letterFoldVal (sertables.tableB 7) (basedRho [1, 1] 7 0) (nC 7) = 0 :=
  edgeB_s7 7 (by decide +kernel)

theorem pin49 : serstable.letterFoldVal (sertables.tableB 7) (serstable.memberRho [1, 1] 7) (nC 7) = 0 :=
  edgeB_u2 7 (by decide +kernel)

theorem pin50 : serstable.letterFoldVal (sertables.tableB 7) (serstable.memberRho [1, 1] 7) (nD 7) = 0 :=
  edgeB_u3 7 (by decide +kernel)

theorem pin51 : serstable.letterFoldVal (sertables.tableB 7) (basedRho [1, 1] 7 0) (nD 7) = 0 :=
  edgeB_s8 7 (by decide +kernel)

theorem pin52 : serstable.letterFoldVal (sertables.tableB 7) (basedRho [1] 7 0) (nE 7) = 0 :=
  edgeB_s5 7 (by decide +kernel)

theorem pin53 : serstable.letterFoldVal (sertables.tableB 7) (serstable.memberRho [1, 1] 7) (nF 7) = 0 :=
  edgeB_u4 7 (by decide +kernel)

theorem pin54 : serstable.letterFoldVal (sertables.tableB 7) (basedRho [1, 1] 7 0) (nF 7) = 0 :=
  edgeB_s6 7 (by decide +kernel)

theorem pin55 : 1 ≤ serstable.letterFoldVal (sertables.tableB 7) (serstable.memberRho [1, 1] 7) (nB 7) :=
  strayB_c1 7 (by decide +kernel)

theorem pin56 : 1 ≤ serstable.letterFoldVal (sertables.tableB 7) (serstable.memberRho [1, 1] 7) (nG 7) :=
  strayB_c2 7 (by decide +kernel)

theorem pin57 : 1 ≤ serstable.letterFoldVal (sertables.tableB 7) (serstable.memberRho [1, 1] 7) (nH 7) :=
  strayB_c3 7 (by decide +kernel)

theorem pin58 : ¬ (row.thetaCount (sertables.tableB 2) (nA 2) = 1)
    ∧ ¬ (row.thetaCount (sertables.tableB 2) (nC 2) = 1)
    ∧ ¬ (row.thetaCount (sertables.tableB 3) (nD 3) = 1)
    ∧ ¬ (row.thetaCount (sertables.tableB 3) (nE 3) = 1)
    ∧ ¬ (row.thetaCount (sertables.tableB 4) (nF 4) = 1)
    ∧ ¬ (row.thetaCount (sertables.tableB 2) (nG 2) = 1)
    ∧ ¬ (row.thetaCount (sertables.tableB 3) (nH 3) = 1) := by
  decide +kernel

theorem pin59 : (row.thetaCount (sertables.tableC 7) (cA 7) = 1)
    ∧ (row.thetaCount (sertables.tableC 7) (cB 7) = 1)
    ∧ (row.thetaCount (sertables.tableC 7) (cC 7) = 1)
    ∧ (row.thetaCount (sertables.tableC 7) (cD 7) = 1)
    ∧ (row.thetaCount (sertables.tableC 7) (cE 7) = 1)
    ∧ (row.thetaCount (sertables.tableC 7) (cF 7) = 1)
    ∧ (row.thetaCount (sertables.tableC 7) (cG 7) = 1)
    ∧ (row.thetaCount (sertables.tableC 7) (cH 7) = 1)
    ∧ (1 ≤ serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [2] 7) (cE 7))
    ∧ (1 ≤ serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [1] 7) (cE 7))
    ∧ (1 ≤ serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [2, 1] 7) (cG 7))
    ∧ (1 ≤ serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [3] 7) (cE 7))
    ∧ (serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [2] 7) (cD 7) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [2] 7) (cB 7) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [2] 7) (cA 7) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [2] 7) (cC 7) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [2, 1] 7) (cF 7) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [1] 7) (cA 7) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [1] 7) (cC 7) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [2, 1] 7) (cE 7) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [2, 1] 7) (cH 7) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [3] 7) (cB 7) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [3] 7) (cA 7) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [3] 7) (cC 7) = 0) := by
  decide +kernel

theorem pin60 : row.thetaCount (sertables.tableC 7) (cA 7) = 1 :=
  cA_mem 7 (by decide +kernel)

theorem pin61 : row.thetaCount (sertables.tableC 7) (cB 7) = 1 :=
  cB_mem 7 (by decide +kernel)

theorem pin62 : row.thetaCount (sertables.tableC 7) (cC 7) = 1 :=
  cC_mem 7 (by decide +kernel)

theorem pin63 : row.thetaCount (sertables.tableC 7) (cD 7) = 1 :=
  cD_mem 7 (by decide +kernel)

theorem pin64 : row.thetaCount (sertables.tableC 7) (cE 7) = 1 :=
  cE_mem 7 (by decide +kernel)

theorem pin65 : row.thetaCount (sertables.tableC 7) (cF 7) = 1 :=
  cF_mem 7 (by decide +kernel)

theorem pin66 : row.thetaCount (sertables.tableC 7) (cG 7) = 1 :=
  cG_mem 7 (by decide +kernel)

theorem pin67 : row.thetaCount (sertables.tableC 7) (cH 7) = 1 :=
  cH_mem 7 (by decide +kernel)

theorem pin68 : 1 ≤ serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [2] 7) (cE 7) :=
  strayC_u1 7 (by decide +kernel)

theorem pin69 : 1 ≤ serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [1] 7) (cE 7) :=
  strayC_w1 7 (by decide +kernel)

theorem pin70 : 1 ≤ serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [2, 1] 7) (cG 7) :=
  strayC_w2 7 (by decide +kernel)

theorem pin71 : 1 ≤ serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [3] 7) (cE 7) :=
  strayC_w3 7 (by decide +kernel)

theorem pin72 : serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [2] 7) (cD 7) = 0 :=
  edgeC_u1 7 (by decide +kernel)

theorem pin73 : serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [2] 7) (cB 7) = 0 :=
  edgeC_u2 7 (by decide +kernel)

theorem pin74 : serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [2] 7) (cA 7) = 0 :=
  edgeC_u3 7 (by decide +kernel)

theorem pin75 : serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [2] 7) (cC 7) = 0 :=
  edgeC_u4 7 (by decide +kernel)

theorem pin76 : serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [2, 1] 7) (cF 7) = 0 :=
  edgeC_w1 7 (by decide +kernel)

theorem pin77 : serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [1] 7) (cA 7) = 0 :=
  edgeC_w2 7 (by decide +kernel)

theorem pin78 : serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [1] 7) (cC 7) = 0 :=
  edgeC_w3 7 (by decide +kernel)

theorem pin79 : serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [2, 1] 7) (cE 7) = 0 :=
  edgeC_w4 7 (by decide +kernel)

theorem pin80 : serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [2, 1] 7) (cH 7) = 0 :=
  edgeC_w5 7 (by decide +kernel)

theorem pin81 : serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [3] 7) (cB 7) = 0 :=
  edgeC_w6 7 (by decide +kernel)

theorem pin82 : serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [3] 7) (cA 7) = 0 :=
  edgeC_w7 7 (by decide +kernel)

theorem pin83 : serstable.letterFoldVal (sertables.tableC 7) (serstable.memberRho [3] 7) (cC 7) = 0 :=
  edgeC_w8 7 (by decide +kernel)

theorem pin84 : (row.thetaCount (sertables.tableD 8) (dA 8) = 1)
    ∧ (row.thetaCount (sertables.tableD 8) (dB 8) = 1)
    ∧ (row.thetaCount (sertables.tableD 8) (dC 8) = 1)
    ∧ (row.thetaCount (sertables.tableD 8) (dD 8) = 1)
    ∧ (row.thetaCount (sertables.tableD 8) (dE 8) = 1)
    ∧ (row.thetaCount (sertables.tableD 8) (dF 8) = 1)
    ∧ (row.thetaCount (sertables.tableD 8) (dG 8) = 1)
    ∧ (row.thetaCount (sertables.tableD 8) (dH 8) = 1)
    ∧ (serstable.letterFoldVal (sertables.tableD 8) (serstable.memberRho [1, 1] 8) (dA 8) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableD 8) (serstable.memberRho [1, 1] 8) (dB 8) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableD 8) (serstable.memberRho [1, 1] 8) (dC 8) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableD 8) (serstable.memberRho [1, 1] 8) (dD 8) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableD 8) (serstable.memberRho [1] 8) (dB 8) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableD 8) (serstable.memberRho [1] 8) (dE 8) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableD 8) (serstable.memberRho [2, 1] 8) (dA 8) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableD 8) (serstable.memberRho [2, 1] 8) (dB 8) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableD 8) (serstable.memberRho [2, 1] 8) (dC 8) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableD 8) (serstable.memberRho [1, 1, 1] 8) (dB 8) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableD 8) (serstable.memberRho [1, 1, 1] 8) (dF 8) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableD 8) (serstable.memberRho [1, 1, 1] 8) (dG 8) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableD 8) (basedRho [] 8 0) (dH 8) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableD 8) (basedRho [] 8 0) (dB 8) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableD 8) (basedRho [1] 8 1) (dB 8) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableD 8) (basedRho [1] 8 1) (dE 8) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableD 8) (basedRho [1, 1] 8 0) (dA 8) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableD 8) (basedRho [1, 1] 8 0) (dB 8) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableD 8) (basedRho [1, 1] 8 0) (dC 8) = 0)
    ∧ (serstable.letterFoldVal (sertables.tableD 8) (basedRho [1, 1] 8 0) (dD 8) = 0) := by
  decide +kernel

theorem pin85 : row.thetaCount (sertables.tableD 8) (dA 8) = 1 :=
  dA_mem 8 (by decide +kernel)

theorem pin86 : row.thetaCount (sertables.tableD 8) (dB 8) = 1 :=
  dB_mem 8 (by decide +kernel)

theorem pin87 : row.thetaCount (sertables.tableD 8) (dC 8) = 1 :=
  dC_mem 8 (by decide +kernel)

theorem pin88 : row.thetaCount (sertables.tableD 8) (dD 8) = 1 :=
  dD_mem 8 (by decide +kernel)

theorem pin89 : row.thetaCount (sertables.tableD 8) (dE 8) = 1 :=
  dE_mem 8 (by decide +kernel)

theorem pin90 : row.thetaCount (sertables.tableD 8) (dF 8) = 1 :=
  dF_mem 8 (by decide +kernel)

theorem pin91 : row.thetaCount (sertables.tableD 8) (dG 8) = 1 :=
  dG_mem 8 (by decide +kernel)

theorem pin92 : row.thetaCount (sertables.tableD 8) (dH 8) = 1 :=
  dH_mem 8 (by decide +kernel)

theorem pin93 : serstable.letterFoldVal (sertables.tableD 8) (serstable.memberRho [1, 1] 8) (dA 8) = 0 :=
  edgeD_u1 8 (by decide +kernel)

theorem pin94 : serstable.letterFoldVal (sertables.tableD 8) (serstable.memberRho [1, 1] 8) (dB 8) = 0 :=
  edgeD_u2 8 (by decide +kernel)

theorem pin95 : serstable.letterFoldVal (sertables.tableD 8) (serstable.memberRho [1, 1] 8) (dC 8) = 0 :=
  edgeD_u3 8 (by decide +kernel)

theorem pin96 : serstable.letterFoldVal (sertables.tableD 8) (serstable.memberRho [1, 1] 8) (dD 8) = 0 :=
  edgeD_u4 8 (by decide +kernel)

theorem pin97 : serstable.letterFoldVal (sertables.tableD 8) (serstable.memberRho [1] 8) (dB 8) = 0 :=
  edgeD_v1 8 (by decide +kernel)

theorem pin98 : serstable.letterFoldVal (sertables.tableD 8) (serstable.memberRho [1] 8) (dE 8) = 0 :=
  edgeD_v2 8 (by decide +kernel)

theorem pin99 : serstable.letterFoldVal (sertables.tableD 8) (serstable.memberRho [2, 1] 8) (dA 8) = 0 :=
  edgeD_v3 8 (by decide +kernel)

theorem pin100 : serstable.letterFoldVal (sertables.tableD 8) (serstable.memberRho [2, 1] 8) (dB 8) = 0 :=
  edgeD_v4 8 (by decide +kernel)

theorem pin101 : serstable.letterFoldVal (sertables.tableD 8) (serstable.memberRho [2, 1] 8) (dC 8) = 0 :=
  edgeD_v5 8 (by decide +kernel)

theorem pin102 : serstable.letterFoldVal (sertables.tableD 8) (serstable.memberRho [1, 1, 1] 8) (dB 8) = 0 :=
  edgeD_v6 8 (by decide +kernel)

theorem pin103 : serstable.letterFoldVal (sertables.tableD 8) (serstable.memberRho [1, 1, 1] 8) (dF 8) = 0 :=
  edgeD_v7 8 (by decide +kernel)

theorem pin104 : serstable.letterFoldVal (sertables.tableD 8) (serstable.memberRho [1, 1, 1] 8) (dG 8) = 0 :=
  edgeD_v8 8 (by decide +kernel)

theorem pin105 : serstable.letterFoldVal (sertables.tableD 8) (basedRho [] 8 0) (dH 8) = 0 :=
  edgeD_s1 8 (by decide +kernel)

theorem pin106 : serstable.letterFoldVal (sertables.tableD 8) (basedRho [] 8 0) (dB 8) = 0 :=
  edgeD_s2 8 (by decide +kernel)

theorem pin107 : serstable.letterFoldVal (sertables.tableD 8) (basedRho [1] 8 1) (dB 8) = 0 :=
  edgeD_s3 8 (by decide +kernel)

theorem pin108 : serstable.letterFoldVal (sertables.tableD 8) (basedRho [1] 8 1) (dE 8) = 0 :=
  edgeD_s4 8 (by decide +kernel)

theorem pin109 : serstable.letterFoldVal (sertables.tableD 8) (basedRho [1, 1] 8 0) (dA 8) = 0 :=
  edgeD_s5 8 (by decide +kernel)

theorem pin110 : serstable.letterFoldVal (sertables.tableD 8) (basedRho [1, 1] 8 0) (dB 8) = 0 :=
  edgeD_s6 8 (by decide +kernel)

theorem pin111 : serstable.letterFoldVal (sertables.tableD 8) (basedRho [1, 1] 8 0) (dC 8) = 0 :=
  edgeD_s7 8 (by decide +kernel)

theorem pin112 : serstable.letterFoldVal (sertables.tableD 8) (basedRho [1, 1] 8 0) (dD 8) = 0 :=
  edgeD_s8 8 (by decide +kernel)

theorem pin113 : ¬ (row.thetaCount (sertables.tableD 3) (dA 3) = 1)
    ∧ ¬ (row.thetaCount (sertables.tableD 3) (dB 3) = 1)
    ∧ ¬ (row.thetaCount (sertables.tableD 4) (dC 4) = 1)
    ∧ ¬ (row.thetaCount (sertables.tableD 5) (dD 5) = 1)
    ∧ ¬ (row.thetaCount (sertables.tableD 4) (dE 4) = 1)
    ∧ ¬ (row.thetaCount (sertables.tableD 5) (dF 5) = 1)
    ∧ ¬ (row.thetaCount (sertables.tableD 6) (dG 6) = 1)
    ∧ ¬ (row.thetaCount (sertables.tableD 2) (dH 2) = 1) := by
  decide +kernel

end serdivisors
