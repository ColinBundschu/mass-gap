import MassGap.Deckfactor
import MassGap.Cellcount
import MassGapChecks.Inertia
/-!
The check module for `lem:cellcount`: the batteries re-read the
cell reads by kernel `decide` at the pencil `S(t) = [[t,1],[1,t]]`,
divisor `t² - 1`.  The cleared evaluations and pointwise counts at
`t = 0, 2, 3` (`rev = 1, 0, 0`); the divisor's squarefree witness
at its own Bézout `-4(t²-1) + (2t)(2t) = 4`; and the crossing
segment `[0, 2]`'s avoidance read, the root `1` inside at count
`1`.  The cleared-variable tier at the pencil `[[2t - 3]]`, the
top off the coefficients' divisors: the squarefree witness, the
cleared monic `y - 3` at `y = 2t`, the straddle `[1, 2]`'s
avoidance at count `1`, the rescaling's own refusal at the
unrescaled endpoints, the clearing one value across a padded
representative, and the forged Bézout witness's refusal.  The
deflation tier at the symmetric pencil `[[t² - 2, 1], [1, 5]]`:
the symmetry read decided, assembled entrywise through its intro
read, and refused at the exchanged entry with the entrywise binder
refused beside it, the swapped
once-cleared deflation's evaluation against the evaluated blocks'
own swapped at two clearings both decided and through the theorem,
the small-order adjugate's solve at pivots of orders two and one,
and the order-one deflations at value-unit couplings — the constant
diagonal pencil reading the pivot entry on the trailing block and
its swap at the swapped deflation, refused at the occupied
coupling — with the swapped deflation's shape read at the trailing
order and the successor-multiple clearing, its pivot-order binder
refused at the vacant pivot and trailing lists.  The pivot cover at the
same pencil on `[2, 129/64]`: the nested certificate — the outer
pivot `t² - 2` on its upper side over the subinterval at the bound
`[3 : 1]`, the once-cleared deflation `5t² - 11` its own piece on
the same side and bound with the order-nought deflation
beneath — decided whole, the constancy theorem run at `257/128`
against the lower endpoint with both counts the positive-definite
`0` at the pencil's shape and symmetry reads, the broken chain's
refusal at a piece stopping short of the segment's upper endpoint
(the same certificate decided over its own shorter segment), the
flipped side certificate's refusal at
the pivot read on its lower side, and the subinterval frame
decided at the designated place with its refusal at repeated
places.  The boundary clause closes the module at the order-one
linear pencils: the direction's quadratic form against the
evaluated pencil's own, the clause at the segment's foot and at its
head with the boundary's lower list empty, and the four refusals —
the interior point's positive-semidefinite binder at each end, the
tie at a pencil crossing the sum's unit inside the segment, and the
shape binder at a cubic entry read at the clearing power one, where
the cleared datum and the point's own value part company. -/

namespace cellcount
set_option maxHeartbeats 4000000

open ground poly elim inertia

private def u : BPair := BPair.unit

/-- The pencil `S(t) = [[t, 1], [1, t]]`. -/
private def sP : split.PMat :=
  [[[u, ⟨2, 1⟩], [⟨2, 1⟩]], [[⟨2, 1⟩], [u, ⟨2, 1⟩]]]

theorem pin1 : pShapeAt sP 2 1 := by decide +kernel
theorem pin2 : ¬ pShapeAt sP 2 0 := by decide +kernel
theorem pin3 : poly.oneValue (split.pminor sP) [⟨1, 2⟩, u, ⟨2, 1⟩] := by
  decide +kernel

/-! The pointwise counts: `rev = 1` at `t = 0` (the mixed block),
`rev = 0` at `t = 2` and `t = 3`. -/

private def sp0 : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.two u ⟨2, 1⟩ u], 0, rfl⟩
private def sp2 : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 2⟩], [⟨2, 1⟩, ⟨2, 1⟩]], rfl⟩,
   ⟨[[⟨2, 1⟩, ⟨2, 1⟩], [⟨1, 2⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨7, 1⟩, .one ⟨3, 1⟩], 0, rfl⟩
private def sp3 : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 2⟩], [⟨2, 1⟩, ⟨2, 1⟩]], rfl⟩,
   ⟨[[⟨2, 1⟩, ⟨2, 1⟩], [⟨1, 2⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨9, 1⟩, .one ⟨5, 1⟩], 0, rfl⟩

theorem pin4 : countAt sP 1 u 1 1 sp0 := by decide +kernel
theorem pin5 : countAt sP 1 ⟨3, 1⟩ 1 0 sp2 := by decide +kernel
theorem pin6 : countAt sP 1 ⟨4, 1⟩ 1 0 sp3 := by decide +kernel

/-! The divisor's witness: `t² - 1` its own squarefree part at the
Bézout `-4(t²-1) + (2t)(2t) = 4`. -/

private def ctD : DivCert :=
  ⟨[], [⟨1, 2⟩, u, ⟨2, 1⟩], [u, ⟨3, 1⟩], [⟨1, 5⟩], [u, ⟨3, 1⟩],
   [⟨1, 2⟩, u, ⟨2, 1⟩], [⟨1, 5⟩], [u, ⟨3, 1⟩],
   1, 1, 1, 1, ⟨5, 1⟩, ⟨5, 1⟩⟩

theorem pin7 : divRead (split.pminor sP) ctD := by decide +kernel
theorem pin8 : poly.oneValue (deckfactor.clearVarBT ctD.sq)
    [⟨1, 2⟩, u] := by decide +kernel

/-! The crossing segment `[0, 2]`: the root `1` inside breaks the
avoidance, the pencil mixed at `diag(2, -24)`. -/

private def spHc : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.one ⟨3, 1⟩, .one ⟨3, 1⟩], 0, rfl⟩

private def spBx : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨5, 1⟩], [⟨1, 1⟩, ⟨3, 1⟩]], rfl⟩,
   ⟨[[⟨3, 1⟩, ⟨1, 5⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨3, 1⟩, .one ⟨1, 25⟩], 0, rfl⟩

theorem pin9 : hermitesign.segCountRead [⟨1, 2⟩, u] u ⟨3, 1⟩ 1 1
    spHc spBx := by decide +kernel
theorem pin10 : ¬ hermitesign.segCountRead [⟨1, 2⟩, u] u ⟨3, 1⟩ 1 0
    spHc spBx := by decide +kernel

/-! The cleared-variable tier at the pencil `[[2t - 3]]`: the top
`2` off the constant's divisors, the cleared monic `y - 3` at
`y = 2t` with the roots the display's own rescaled by the
magnitude. -/


private def sP2 : split.PMat := [[[⟨1, 4⟩, ⟨3, 1⟩]]]

private def ctN : DivCert :=
  ⟨[], [⟨1, 4⟩, ⟨3, 1⟩], [⟨3, 1⟩], [], [⟨2, 1⟩],
   [⟨1, 4⟩, ⟨3, 1⟩], [], [⟨2, 1⟩], 1, 1, 1, 1, ⟨3, 1⟩, ⟨3, 1⟩⟩

theorem pin11 : divRead (split.pminor sP2) ctN := by decide +kernel
theorem pin12 : poly.oneValue (deckfactor.clearVarBT ctN.sq) [⟨1, 4⟩] := by
  decide +kernel

/-! The straddle `[1, 2]` refuses: the cleared root `3` inside the
rescaled `[2, 4]`, the avoidance at count `1` with the endpoint
counts split `1` against `0`. -/

theorem pin13 : hermitesign.segCountRead (deckfactor.clearVarBT ctN.sq)
    (deckfactor.clearAt ctN.sq ⟨2, 1⟩)
    (deckfactor.clearAt ctN.sq ⟨3, 1⟩) 1 1
    (inertia.oneSplit [⟨2, 1⟩]) (inertia.oneSplit [⟨1, 2⟩]) := by decide +kernel

/-! The rescaling is the read's own conjunct: at the unrescaled
right endpoint the cleared monic reads the root itself, and the
count refuses there at every split, the endpoint conjunct's own
read. -/

theorem pin14 : (stage.evalC (poly.monic (deckfactor.clearVarBT ctN.sq))
    ⟨⟨4, 1⟩, 1⟩).oneValue stage.unitC := by decide +kernel
theorem pin15 : ¬ hermitesign.segCountRead (deckfactor.clearVarBT ctN.sq)
    ⟨3, 1⟩ ⟨4, 1⟩ 1 0 (inertia.oneSplit [⟨2, 1⟩]) (inertia.oneSplit [⟨4, 1⟩]) := by decide +kernel

/-! The clearing reads one value at every representative: the
squarefree part padded by a unit tail names the one cleared monic,
the one rescaled point, and the one certificate, the homogeneity
principle's read at `poly.vnorm`. -/

private def ctP : DivCert :=
  ⟨[], [⟨1, 4⟩, ⟨3, 1⟩], [⟨3, 1⟩], [], [⟨2, 1⟩],
   [⟨1, 4⟩, ⟨3, 1⟩, u], [], [⟨2, 1⟩], 1, 1, 1, 1, ⟨3, 1⟩, ⟨3, 1⟩⟩

theorem pin16 : poly.oneValue (deckfactor.clearVarBT ctP.sq)
    (deckfactor.clearVarBT ctN.sq) := by decide +kernel
theorem pin17 : (deckfactor.clearAt ctP.sq ⟨3, 1⟩).oneValue
    (deckfactor.clearAt ctN.sq ⟨3, 1⟩) := by decide +kernel
theorem pin18 : divRead (split.pminor sP2) ctP := by decide +kernel

/-! The forged Bézout witness refuses: the part's combination moved
off the displayed constant, every further conjunct at the true
data. -/

private def ctB : DivCert :=
  ⟨[], [⟨1, 4⟩, ⟨3, 1⟩], [⟨3, 1⟩], [], [⟨2, 1⟩],
   [⟨1, 4⟩, ⟨3, 1⟩], [⟨3, 1⟩], [⟨2, 1⟩], 1, 1, 1, 1, ⟨3, 1⟩, ⟨3, 1⟩⟩

theorem pin19 : ¬ divRead (split.pminor sP2) ctB := by decide +kernel

/-! The deflation tier at the symmetric pencil
`S(t) = [[t² - 2, 1], [1, 5]]`: the symmetry read with its refusal
at an exchanged entry, the cleared deflation's evaluation against
the evaluated blocks' own at the pivot key `0` and the trailing key
`1` — the clearing power `3K` at `K = 2`, the point `t = 3` at the
clearings `1` and `2`, decided and through the theorem — and the
adjugate's solve at the pivots `[[3, 2], [2, -1]]` of order two and
`[[3]]` of order one. -/

private def sD : split.PMat :=
  [[[⟨1, 3⟩, u, ⟨2, 1⟩], [⟨2, 1⟩]], [[⟨2, 1⟩], [⟨6, 1⟩]]]

theorem pin20 : split.pSymAt sD 2 := by decide +kernel
theorem pin21 : split.pSymAt sD 2 :=
  elim.symAtO_of poly.polyRead [] sD 2 (fun i j hi hj =>
    (by decide +kernel : ∀ i, i < 2 → ∀ j, j < 2 → poly.oneValue
      (ground.getAt [] (ground.getAt [] sD i) j)
      (ground.getAt [] (ground.getAt [] sD j) i)) i hi j hj)
theorem pin22 : pShapeAt sD 2 2 := by decide +kernel

/-- The exchanged entry moved off its partner: the symmetry read
refuses. -/
private def sA : split.PMat :=
  [[[⟨1, 3⟩, u, ⟨2, 1⟩], [⟨2, 1⟩]], [[⟨3, 1⟩], [⟨6, 1⟩]]]

theorem pin23 : ¬ split.pSymAt sA 2 := by decide +kernel
theorem pin24 : ¬ (∀ i, i < 2 → ∀ j, j < 2 → poly.oneValue
    (ground.getAt [] (ground.getAt [] sA i) j)
    (ground.getAt [] (ground.getAt [] sA j) i)) := by decide +kernel

theorem pin25 : elim.matOneValue
    (evalPC (pdeflM [0] [1] sD) ⟨4, 1⟩ 1
      ((([0] : List Nat).length + 1) * 2))
    (elim.matSwap (inertia.deflMatP (elim.selM [0] [0] (evalPC sD ⟨4, 1⟩ 1 2))
      (elim.selM [0] [1] (evalPC sD ⟨4, 1⟩ 1 2))
      (elim.selM [1] [1] (evalPC sD ⟨4, 1⟩ 1 2))
      (evalPC (pdeflW [0] [1] sD) ⟨4, 1⟩ 1 (([0] : List Nat).length * 2)))) := by
  decide +kernel

theorem pin26 : elim.matOneValue
    (evalPC (pdeflM [0] [1] sD) ⟨4, 1⟩ 1
      ((([0] : List Nat).length + 1) * 2))
    (elim.matSwap (inertia.deflMatP (elim.selM [0] [0] (evalPC sD ⟨4, 1⟩ 1 2))
      (elim.selM [0] [1] (evalPC sD ⟨4, 1⟩ 1 2))
      (elim.selM [1] [1] (evalPC sD ⟨4, 1⟩ 1 2))
      (evalPC (pdeflW [0] [1] sD) ⟨4, 1⟩ 1 (([0] : List Nat).length * 2)))) :=
  evalPC_pdeflM (o := 2) sD 2 [0] [1] ⟨4, 1⟩ 1 (by decide +kernel)
    (by decide +kernel) (Nat.succ_pos 0) (by decide +kernel) (by decide +kernel)

theorem pin27 : elim.matOneValue
    (evalPC (pdeflM [0] [1] sD) ⟨4, 1⟩ 2
      ((([0] : List Nat).length + 1) * 2))
    (elim.matSwap (inertia.deflMatP (elim.selM [0] [0] (evalPC sD ⟨4, 1⟩ 2 2))
      (elim.selM [0] [1] (evalPC sD ⟨4, 1⟩ 2 2))
      (elim.selM [1] [1] (evalPC sD ⟨4, 1⟩ 2 2))
      (evalPC (pdeflW [0] [1] sD) ⟨4, 1⟩ 2 (([0] : List Nat).length * 2)))) := by
  decide +kernel

theorem pin28 : elim.matOneValue
    (evalPC (pdeflM [0] [1] sD) ⟨4, 1⟩ 2
      ((([0] : List Nat).length + 1) * 2))
    (elim.matSwap (inertia.deflMatP (elim.selM [0] [0] (evalPC sD ⟨4, 1⟩ 2 2))
      (elim.selM [0] [1] (evalPC sD ⟨4, 1⟩ 2 2))
      (elim.selM [1] [1] (evalPC sD ⟨4, 1⟩ 2 2))
      (evalPC (pdeflW [0] [1] sD) ⟨4, 1⟩ 2 (([0] : List Nat).length * 2)))) :=
  evalPC_pdeflM (o := 2) sD 2 [0] [1] ⟨4, 1⟩ 2 (by decide +kernel)
    (by decide +kernel) (Nat.succ_pos 0) (by decide +kernel) (by decide +kernel)

/-! The deflation theorem's binder refusals: the symmetry at the
exchanged-entry pencil, every further binder holding, and the shape
at the undersized clearing, the point's own read the isolation. -/

theorem pin29 : ¬ elim.matOneValue
    (evalPC (pdeflM [0] [1] sA) ⟨4, 1⟩ 1
      ((([0] : List Nat).length + 1) * 2))
    (elim.matSwap (inertia.deflMatP (elim.selM [0] [0] (evalPC sA ⟨4, 1⟩ 1 2))
      (elim.selM [0] [1] (evalPC sA ⟨4, 1⟩ 1 2))
      (elim.selM [1] [1] (evalPC sA ⟨4, 1⟩ 1 2))
      (evalPC (pdeflW [0] [1] sA) ⟨4, 1⟩ 1 (([0] : List Nat).length * 2)))) := by
  decide +kernel

theorem pin30 : pShapeAt sA 2 2 := by decide +kernel

theorem pin31 : ¬ pShapeAt sD 2 1 := by decide +kernel

theorem pin32 : ¬ elim.matOneValue
    (evalPC (pdeflM [0] [1] sD) ⟨5, 1⟩ 3
      ((([0] : List Nat).length + 1) * 1))
    (elim.matSwap (inertia.deflMatP (elim.selM [0] [0] (evalPC sD ⟨5, 1⟩ 3 1))
      (elim.selM [0] [1] (evalPC sD ⟨5, 1⟩ 3 1))
      (elim.selM [1] [1] (evalPC sD ⟨5, 1⟩ 3 1))
      (evalPC (pdeflW [0] [1] sD) ⟨5, 1⟩ 3 (([0] : List Nat).length * 1)))) := by
  decide +kernel

/-! The once-cleared deflation at value-unit couplings: the constant
pencil `[[2, 0], [0, 4]]` whose couplings read the sum's unit without
standing at the unit pair, the deflation reading the pivot entry on
the trailing block — decided and through the theorem — against the
occupied-coupling pencil `[[2, 2], [2, 4]]`, where the correction
survives and the two part company; the swapped deflation reads the
pivot entry's swap there, the module's closing pins. -/

private def dfS : split.PMat :=
  [[[⟨3, 1⟩], [⟨2, 2⟩]], [[⟨2, 2⟩], [⟨5, 1⟩]]]

theorem pin41 : split.pmatOneValue (pdeflP [0] [1] dfS)
    (split.pscaleM (ground.getAt [] (ground.getAt [] dfS 0) 0)
      (split.pselM [1] [1] dfS)) := by decide +kernel

theorem pin42 : split.pmatOneValue (pdeflP [0] [1] dfS)
    (split.pscaleM (ground.getAt [] (ground.getAt [] dfS 0) 0)
      (split.pselM [1] [1] dfS)) :=
  pdeflP_offC dfS 0 [1] (by decide +kernel)

private def dfT : split.PMat :=
  [[[⟨3, 1⟩], [⟨3, 1⟩]], [[⟨3, 1⟩], [⟨5, 1⟩]]]

theorem pin43 : ¬ poly.unitTail (ground.getAt ([] : Poly)
    (ground.getAt ([] : List Poly) dfT (ground.getAt 0 [1] 0)) 0) := by
  decide +kernel

theorem pin44 : ¬ split.pmatOneValue (pdeflP [0] [1] dfT)
    (split.pscaleM (ground.getAt [] (ground.getAt [] dfT 0) 0)
      (split.pselM [1] [1] dfT)) := by decide +kernel


/-! The swapped deflation's shape read: the trailing order at the
successor-multiple clearing, decided and through the theorem at both
pivot orders — the one-place pivot on the standing pencil at
clearing two with a refusal at the clearing one isolating the
successor factor, and the two-place pivot at a clearing-one
order-three pencil — with the shape binder refused at a square-entry
pencil read one clearing low, where its deflation's degree outruns
the claimed clearing. -/

theorem pin45 : pShapeAt (pdeflM [0] [1] sD) 1 ((1 + 1) * 2) := by
  decide +kernel
theorem pin46 : pShapeAt (pdeflM [0] [1] sD) 1 ((1 + 1) * 2) :=
  pShape_pdeflM sD 2 2 [0] [1] (by decide +kernel)
theorem pin47 : ¬ pShapeAt (pdeflM [0] [1] sD) 1 1 := by decide +kernel

private def sf3 : split.PMat :=
  [[[⟨2, 1⟩, ⟨1, 2⟩], [u], [u]],
   [[u], [⟨3, 1⟩, u], [u]],
   [[u], [u], [⟨4, 1⟩, ⟨2, 1⟩]]]

theorem pin48 : pShapeAt (pdeflM [0, 1] [2] sf3) 1 ((2 + 1) * 1) := by
  decide +kernel
theorem pin49 : pShapeAt (pdeflM [0, 1] [2] sf3) 1 ((2 + 1) * 1) :=
  pShape_pdeflM sf3 3 1 [0, 1] [2] (by decide +kernel)
theorem pin50 : ¬ pShapeAt (pdeflM [0, 1] [2] sf3) 1 1 := by decide +kernel

/-- `[[t² - 2, t²], [t², 5]]`, its swapped deflation `t⁴ - 5t² + 10`. -/
private def sE : split.PMat :=
  [[[⟨1, 3⟩, u, ⟨2, 1⟩], [u, u, ⟨2, 1⟩]], [[u, u, ⟨2, 1⟩], [⟨6, 1⟩]]]

theorem pin51 : ¬ pShapeAt sE 2 1 ∧ pShapeAt sE 2 2 := by decide +kernel
theorem pin52 : ¬ pShapeAt (pdeflM [0] [1] sE) 1 ((1 + 1) * 1) := by
  decide +kernel

/-! `lem:freecell`'s display read entrywise at the level carrier:
an entry inside the order is the level datum's entry at the
constant key with the stated middle and the trailing member's
entry at the top key, decided and through the theorem.  Each of
the three shape binders refuses at its own ragged member — the
componentwise walk truncates at the shorter operand — with the
beyond-order row and column keys refused at the vacant read, and
the shape read decided, through the theorem, and refused at the
ragged data. -/

private def lvA : elim.Mat := [[⟨3, 1⟩, ⟨1, 2⟩], [⟨2, 1⟩, ⟨5, 1⟩]]
private def lvB : elim.Mat := [[⟨4, 1⟩, ⟨1, 3⟩], [⟨1, 5⟩, ⟨6, 1⟩]]
private def lvG : elim.Mat := [[⟨2, 1⟩, u], [u, ⟨3, 1⟩]]
private def lvAr : elim.Mat := [[⟨3, 1⟩], [⟨2, 1⟩, ⟨5, 1⟩]]
private def lvBr : elim.Mat := [[⟨4, 1⟩], [⟨1, 5⟩, ⟨6, 1⟩]]
private def lvGr : elim.Mat := [[⟨2, 1⟩], [u, ⟨3, 1⟩]]

theorem pin53 : getAt [] (getAt [] (levelPMat lvA lvB lvG 3 2 [u]) 0) 1
    = getAt u (getAt []
        (inertia.siteDatum (elim.matAdd lvA (inertia.matScale 2 lvG))
          (inertia.matScale 3 lvG)) 0) 1
      :: ([u] ++ [getAt u (getAt [] lvB 0) 1]) := by decide +kernel
theorem pin54 : getAt [] (getAt [] (levelPMat lvA lvB lvG 3 2 [u]) 0) 1
    = getAt u (getAt []
        (inertia.siteDatum (elim.matAdd lvA (inertia.matScale 2 lvG))
          (inertia.matScale 3 lvG)) 0) 1
      :: ([u] ++ [getAt u (getAt [] lvB 0) 1]) :=
  levelPMat_entry lvA lvB lvG 3 2 [u] 2 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 0 1 (by decide +kernel)
    (by decide +kernel)
theorem pin55 : ¬ (getAt [] (getAt [] (levelPMat lvA lvBr lvG 3 2 [u]) 0) 1
    = getAt u (getAt []
        (inertia.siteDatum (elim.matAdd lvA (inertia.matScale 2 lvG))
          (inertia.matScale 3 lvG)) 0) 1
      :: ([u] ++ [getAt u (getAt [] lvBr 0) 1])) := by decide +kernel
theorem pin56 : ¬ (getAt [] (getAt [] (levelPMat lvAr lvB lvG 3 2 [u]) 0) 1
    = getAt u (getAt []
        (inertia.siteDatum (elim.matAdd lvAr (inertia.matScale 2 lvG))
          (inertia.matScale 3 lvG)) 0) 1
      :: ([u] ++ [getAt u (getAt [] lvB 0) 1])) := by decide +kernel
theorem pin57 : ¬ (getAt [] (getAt [] (levelPMat lvA lvB lvGr 3 2 [u]) 0) 1
    = getAt u (getAt []
        (inertia.siteDatum (elim.matAdd lvA (inertia.matScale 2 lvGr))
          (inertia.matScale 3 lvGr)) 0) 1
      :: ([u] ++ [getAt u (getAt [] lvB 0) 1])) := by decide +kernel
theorem pin58 : ¬ (getAt [] (getAt [] (levelPMat lvA lvB lvG 3 2 [u]) 2) 1
    = getAt u (getAt []
        (inertia.siteDatum (elim.matAdd lvA (inertia.matScale 2 lvG))
          (inertia.matScale 3 lvG)) 2) 1
      :: ([u] ++ [getAt u (getAt [] lvB 2) 1])) := by decide +kernel
theorem pin59 : ¬ (getAt [] (getAt [] (levelPMat lvA lvB lvG 3 2 [u]) 0) 2
    = getAt u (getAt []
        (inertia.siteDatum (elim.matAdd lvA (inertia.matScale 2 lvG))
          (inertia.matScale 3 lvG)) 0) 2
      :: ([u] ++ [getAt u (getAt [] lvB 0) 2])) := by decide +kernel

theorem pin60 : pShapeAt (levelPMat lvA lvB lvG 3 2 [u]) 2 2 := by
  decide +kernel
theorem pin61 : pShapeAt (levelPMat lvA lvB lvG 3 2 [u]) 2 2 :=
  pShapeAt_levelPMat lvA lvB lvG 3 2 [u] 2 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem pin62 : ¬ pShapeAt (levelPMat lvAr lvB lvG 3 2 [u]) 2 2 := by
  decide +kernel
theorem pin63 : ¬ pShapeAt (levelPMat lvA lvBr lvG 3 2 [u]) 2 2 := by
  decide +kernel
theorem pin64 : ¬ pShapeAt (levelPMat lvA lvB lvGr 3 2 [u]) 2 2 := by
  decide +kernel

private def sfX : split.PMat := [[[(⟨2, 1⟩ : BPair)]]]

theorem pin65 : pShapeAt sfX 1 0 := by decide +kernel
theorem pin66 : ¬ matOneValue (evalPC (pdeflP [] [0] sfX) ⟨2, 1⟩ 1
      ((([] : List Nat).length + 1) * 0))
    (deflMatP (selM [] [] (evalPC sfX ⟨2, 1⟩ 1 0)) (selM [] [0] (evalPC sfX ⟨2, 1⟩ 1 0))
      (selM [0] [0] (evalPC sfX ⟨2, 1⟩ 1 0))
      (evalPC (pdeflW [] [0] sfX) ⟨2, 1⟩ 1 (([] : List Nat).length * 0))) := by
  decide +kernel


/-! The pivot cover at `S(t) = [[t² - 2, 1], [1, 5]]` over
`[2, 129/64]`: the segment is the width the deflation's priced side
read admits — at the lower endpoint the once-cleared deflation
`5t² - 11` reads `9` while its derivative's coefficient fold at the
bound `[3 : 1]` reads `30`, so the subinterval's width sits below
`9/30`. -/

private def loDn : BPair := ⟨3, 1⟩
private def loDc : Pos := 1
private def loD : CPair := ⟨loDn, loDc⟩
private def hiD : CPair := ⟨⟨130, 1⟩, 64⟩

private def cv1 : Cover := diagNest hiD ⟨4, 1⟩ ⟨2, 1⟩ 2

theorem pin67 : coverRead sD 2 2 loD hiD cv1 := by decide +kernel

/-! The constancy theorem at an interior point against the lower
endpoint, the two splits the construction's own. -/

private def xDn : BPair := ⟨258, 1⟩
private def xDc : Pos := 128
private def xD : CPair := ⟨xDn, xDc⟩

theorem pin68 : inertia.revAt (inertia.mkSplit 2 (evalPC sD loDn loDc 2))
    = 0 := by decide +kernel
theorem pin69 : inertia.revAt (inertia.mkSplit 2 (evalPC sD xDn xDc 2))
    = 0 := by decide +kernel

theorem pin70 : inertia.revAt (inertia.mkSplit 2 (evalPC sD xDn xDc 2))
    = inertia.revAt (inertia.mkSplit 2 (evalPC sD loDn loDc 2)) :=
  cover_const (o := 2) sD 2 loD hiD cv1 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) xDn xDc loDn loDc
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (inertia.mkSplit 2 (evalPC sD xDn xDc 2))
    (inertia.mkSplit 2 (evalPC sD loDn loDc 2))
    (inertia.mkSplit_read 2 (evalPC sD xDn xDc 2)
      (by decide +kernel) (by decide +kernel))
    (inertia.mkSplit_read 2 (evalPC sD loDn loDc 2)
      (by decide +kernel) (by decide +kernel))

/-! The refusals: the chain broken at a piece stopping short of the
upper endpoint — the same certificate decided over its own shorter
segment, so the chaining conjunct alone is isolated — and the
forged side certificate at the pivot read on its lower side. -/

private def cvShort : Cover := diagNest xD ⟨4, 1⟩ ⟨2, 1⟩ 2

theorem pin71 : coverRead sD 2 2 loD xD cvShort := by decide +kernel
theorem pin72 : ¬ coverRead sD 2 2 loD hiD cvShort := by decide +kernel

private def cvFlip : Cover :=
  Cover.one hiD 0 false ⟨4, 1⟩ ⟨2, 1⟩
    (diagNest hiD ⟨4, 1⟩ ⟨2, 1⟩ 1) Cover.done

theorem pin73 : ¬ coverRead sD 2 2 loD hiD cvFlip := by decide +kernel

/-! The constancy theorem's shape binder: at the degree-off pencil
`[[1 - t²]]` at clearing `0`, two representatives of the one
segment point read distinct counts, so the shape read is the
theorem's own binder, refused at the pencil. -/

private def sK : split.PMat := [[[⟨2, 1⟩, u, ⟨1, 2⟩]]]

theorem pin74 : (⟨⟨2, 1⟩, 1⟩ : CPair).oneValue ⟨⟨3, 1⟩, 2⟩ := by
  decide +kernel
theorem pin75 : ¬ pShapeAt sK 1 0 := by decide +kernel
theorem pin76 : inertia.revAt (inertia.mkSplit 1 (evalPC sK ⟨2, 1⟩ 1 0))
    = 0 := by decide +kernel
theorem pin77 : inertia.revAt (inertia.mkSplit 1 (evalPC sK ⟨3, 1⟩ 2 0))
    = 1 := by decide +kernel

/-! The piece's frame at the designated place, refused at repeated
places. -/

theorem pin78 : pieceRead 2 [0] := by decide +kernel
theorem pin79 : ¬ pieceRead 2 [0, 0] := by decide +kernel

/-! The one transport (`cellCount`): the sampled vacant count at the
lower endpoint holds at the interior point through the cover, the
route beside the constancy theorem's own; and the level carrier's
evaluation at a point (`levelPMat_eval`): the order-one carrier
`levelPMat [5] [-1] [1]` at the level `⟨3 : 1⟩` evaluated at the
point `⟨3 : 1⟩` over the clearing one reads the level datum at the
clearing's square joined to the magnetic member at the point's, an
occupied middle refusing the read. -/

theorem pin80 : inertia.revAt (inertia.mkSplit 2 (evalPC sD xDn xDc 2)) = 0 :=
  cellCount sD 2 0 loD hiD cv1 (by decide +kernel) (by decide +kernel)
    loDn loDc (by decide +kernel) (by decide +kernel)
    (inertia.mkSplit 2 (evalPC sD loDn loDc 2))
    (by decide +kernel)
    xDn xDc (by decide +kernel) (by decide +kernel)
    (inertia.mkSplit 2 (evalPC sD xDn xDc 2))
    (inertia.mkSplit_read 2 (evalPC sD xDn xDc 2)
      (by decide +kernel) (by decide +kernel))

theorem pin81 : elim.matOneValue
    (evalPC (levelPMat [[⟨6, 1⟩]] [[⟨1, 2⟩]] [[⟨2, 1⟩]] 3 1
      [ground.BPair.unit]) ⟨3, 1⟩ 1 2)
    (elim.matAdd
      (inertia.matScaleB (ground.bpow (ground.BPair.ofPos 1) 2)
        (inertia.siteDatum
          (elim.matAdd [[⟨6, 1⟩]] (inertia.matScale 1 [[⟨2, 1⟩]]))
          (inertia.matScale 3 [[⟨2, 1⟩]])))
      (inertia.matScaleB (ground.bpow ⟨3, 1⟩ 2) [[⟨1, 2⟩]])) := by
  decide +kernel

theorem pin82 : elim.matOneValue
    (evalPC (levelPMat [[⟨6, 1⟩]] [[⟨1, 2⟩]] [[⟨2, 1⟩]] 3 1
      [ground.BPair.unit]) ⟨3, 1⟩ 1 2)
    (elim.matAdd
      (inertia.matScaleB (ground.bpow (ground.BPair.ofPos 1) 2)
        (inertia.siteDatum
          (elim.matAdd [[⟨6, 1⟩]] (inertia.matScale 1 [[⟨2, 1⟩]]))
          (inertia.matScale 3 [[⟨2, 1⟩]])))
      (inertia.matScaleB (ground.bpow ⟨3, 1⟩ 2) [[⟨1, 2⟩]])) :=
  levelPMat_eval [[⟨6, 1⟩]] [[⟨1, 2⟩]] [[⟨2, 1⟩]] 3 1
    [ground.BPair.unit] 1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ⟨3, 1⟩ 1

theorem pin83 : ¬ elim.matOneValue
    (evalPC (levelPMat [[⟨6, 1⟩]] [[⟨1, 2⟩]] [[⟨2, 1⟩]] 3 1
      [⟨2, 1⟩]) ⟨3, 1⟩ 1 2)
    (elim.matAdd
      (inertia.matScaleB (ground.bpow (ground.BPair.ofPos 1) 2)
        (inertia.siteDatum
          (elim.matAdd [[⟨6, 1⟩]] (inertia.matScale 1 [[⟨2, 1⟩]]))
          (inertia.matScale 3 [[⟨2, 1⟩]])))
      (inertia.matScaleB (ground.bpow ⟨3, 1⟩ 2) [[⟨1, 2⟩]])) := by
  decide +kernel

/-! `lem:cellcount`'s boundary clause at the order-one linear
pencils.  The direction's quadratic form reads the evaluated
pencil's own (`evalClear_quadP`) at `[[x - 3]]` against its lower
witness, decided and through the theorem.  The clause itself runs
at the segment's foot (`boundary_psd_lo`) at `[[x - 1]]`, the
boundary the root `x = 1` and the interior point `x = 2`, and at
its head (`boundary_psd_hi`) at `[[2 - x]]`, the boundary the root
`x = 2` and the interior point `x = 1`: at each the boundary's
lower list is empty, so the tie is vacuous, and the conclusion
lands decided and through the theorem.

The refusals isolate three binders.  At `[[x - 3]]` on `[1, 2]` at
the bound `[2 : 1]` the tie holds and the boundary's own count
refuses, so the interior point's positive-semidefinite binder is
the forge — the pencil sits below the sum's unit across the whole
segment.  At `[[x - 2]]` on `[1, 3]` at the bound `[3 : 1]` the
interior point reads positive semidefinite and the boundary does
not, while the tie refuses: the polynomial crosses the sum's unit
inside the segment, its value at the interior point above it, so
the tie is the load-bearing conjunct.  At `[[x - 5]]` on `[1, 2]`
at the bound `[2 : 1]` the upper-endpoint tie holds and the
interior point's count refuses, the head's read carrying the same
isolation as the foot's.

The interior point's split read is its own isolated binder: at the
stated `[[x - 3]]` boundary data a foreign positive-semidefinite
split — the root pencil's interior split — refuses the interior
read while every sibling holds and the conclusion refuses, at the
foot and at the head alike.  The boundary's own split read carries
no such forge at order one: the contradiction closes through the
tie's witness whatever the boundary split reads, an occupied lower
list at a vacant reversal count needing a singular stated block the
certificate's nonsingularity conjunct refuses.

The shape binder's own forge is the cubic `x³ - 3` at the clearing
power one: the shape read refuses there and holds at the power
three, the lower witness's tie holds across `[1/2, 1]` at the bound
`[1 : 1]` where the polynomial's own values are `-46/16` and
`-32/16`, and the boundary's count refuses — while the interior
point's cleared datum at the power one reads `2` and so passes the
positive-semidefinite read that the point's own value refuses.  The
clearing power's shortfall against the entry's degree is what the
shape binder buys. -/

private def bpA : split.PMat := [[[⟨1, 2⟩, ⟨2, 1⟩]]]
private def bpB : split.PMat := [[[⟨1, 4⟩, ⟨2, 1⟩]]]
private def bpC : split.PMat := [[[⟨3, 1⟩, ⟨1, 2⟩]]]
private def bpD : split.PMat := [[[⟨1, 3⟩, ⟨2, 1⟩]]]
private def bpE : split.PMat := [[[⟨1, 6⟩, ⟨2, 1⟩]]]
private def bpQ : split.PMat := [[[⟨1, 4⟩, u, u, ⟨2, 1⟩]]]

private def wOne : List BPair := [⟨2, 1⟩]

theorem pin84 : (poly.evalClear (quadP bpB wOne) ⟨3, 1⟩ 1 1).oneValue
    (elim.dotN wOne (elim.matVec (evalPC bpB ⟨3, 1⟩ 1 1) wOne)) := by
  decide +kernel

theorem pin85 : (poly.evalClear (quadP bpB wOne) ⟨3, 1⟩ 1 1).oneValue
    (elim.dotN wOne (elim.matVec (evalPC bpB ⟨3, 1⟩ 1 1) wOne)) :=
  evalClear_quadP bpB 1 wOne ⟨3, 1⟩ 1

private def spAb : Split 1 := mkSplit 1 (evalPC bpA ⟨2, 1⟩ 1 1)
private def spAt : Split 1 := mkSplit 1 (evalPC bpA ⟨3, 1⟩ 1 1)

private theorem shA : pShapeAt bpA 1 1 := by decide +kernel
private theorem srAb : splitRead (evalPC bpA ⟨2, 1⟩ 1 1) spAb := by
  decide +kernel
private theorem srAt : splitRead (evalPC bpA ⟨3, 1⟩ 1 1) spAt := by
  decide +kernel
private theorem psdA : psdAt spAt := by decide +kernel
theorem pin86 : (lowerList spAb).length = 0 := by decide +kernel
private theorem tieA : ((lowerList spAb).all (fun w => decide
    (stage.keepLower (quadP bpA w) ⟨⟨2, 1⟩, 1⟩ ⟨⟨3, 1⟩, 1⟩
      ⟨3, 1⟩ ⟨2, 1⟩))) = true := by decide +kernel
theorem pin87 : psdAt spAb := by decide +kernel

theorem pin88 : psdAt spAb :=
  boundary_psd_lo bpA 1 ⟨2, 1⟩ 1 ⟨3, 1⟩ 1 ⟨3, 1⟩ ⟨2, 1⟩ spAb spAt
    shA srAb srAt psdA tieA

private def spCb : Split 1 := mkSplit 1 (evalPC bpC ⟨3, 1⟩ 1 1)
private def spCt : Split 1 := mkSplit 1 (evalPC bpC ⟨2, 1⟩ 1 1)

private theorem shC : pShapeAt bpC 1 1 := by decide +kernel
private theorem srCb : splitRead (evalPC bpC ⟨3, 1⟩ 1 1) spCb := by
  decide +kernel
private theorem srCt : splitRead (evalPC bpC ⟨2, 1⟩ 1 1) spCt := by
  decide +kernel
private theorem psdC : psdAt spCt := by decide +kernel
theorem pin89 : (lowerList spCb).length = 0 := by decide +kernel
private theorem tieC : ((lowerList spCb).all (fun w => decide
    (stage.keepLowerTop (quadP bpC w) ⟨⟨2, 1⟩, 1⟩ ⟨⟨3, 1⟩, 1⟩
      ⟨3, 1⟩ ⟨2, 1⟩))) = true := by decide +kernel
theorem pin90 : psdAt spCb := by decide +kernel

theorem pin91 : psdAt spCb :=
  boundary_psd_hi bpC 1 ⟨3, 1⟩ 1 ⟨2, 1⟩ 1 ⟨3, 1⟩ ⟨2, 1⟩ spCb spCt
    shC srCb srCt psdC tieC

private def spBb : Split 1 := mkSplit 1 (evalPC bpB ⟨2, 1⟩ 1 1)
private def spBt : Split 1 := mkSplit 1 (evalPC bpB ⟨3, 1⟩ 1 1)

theorem pin92 : pShapeAt bpB 1 1 := by decide +kernel
theorem pin93 : splitRead (evalPC bpB ⟨2, 1⟩ 1 1) spBb := by decide +kernel
theorem pin94 : splitRead (evalPC bpB ⟨3, 1⟩ 1 1) spBt := by decide +kernel
theorem pin95 : ((lowerList spBb).all (fun w => decide
    (stage.keepLower (quadP bpB w) ⟨⟨2, 1⟩, 1⟩ ⟨⟨3, 1⟩, 1⟩
      ⟨3, 1⟩ ⟨2, 1⟩))) = true := by decide +kernel
theorem pin96 : ¬ psdAt spBt := by decide +kernel
theorem pin97 : ¬ psdAt spBb := by decide +kernel

private def spDb : Split 1 := mkSplit 1 (evalPC bpD ⟨2, 1⟩ 1 1)
private def spDt : Split 1 := mkSplit 1 (evalPC bpD ⟨4, 1⟩ 1 1)

theorem pin98 : pShapeAt bpD 1 1 := by decide +kernel
theorem pin99 : splitRead (evalPC bpD ⟨2, 1⟩ 1 1) spDb := by decide +kernel
theorem pin100 : splitRead (evalPC bpD ⟨4, 1⟩ 1 1) spDt := by decide +kernel
theorem pin101 : psdAt spDt := by decide +kernel
theorem pin102 : ((lowerList spDb).all (fun w => decide
    (stage.keepLower (quadP bpD w) ⟨⟨2, 1⟩, 1⟩ ⟨⟨4, 1⟩, 1⟩
      ⟨4, 1⟩ ⟨2, 1⟩))) = false := by decide +kernel
theorem pin103 : ground.getAt ([] : List BPair) (lowerList spDb) 0 = wOne := by
  decide +kernel
theorem pin104 : stage.evalC (quadP bpD wOne) ⟨⟨2, 1⟩, 1⟩ < stage.unitC := by
  decide +kernel
theorem pin105 : ¬ (stage.evalC (quadP bpD wOne) ⟨⟨4, 1⟩, 1⟩ < stage.unitC) := by
  decide +kernel
theorem pin106 : ¬ psdAt spDb := by decide +kernel

private def spEb : Split 1 := mkSplit 1 (evalPC bpE ⟨3, 1⟩ 1 1)
private def spEt : Split 1 := mkSplit 1 (evalPC bpE ⟨2, 1⟩ 1 1)

theorem pin107 : pShapeAt bpE 1 1 := by decide +kernel
theorem pin108 : splitRead (evalPC bpE ⟨3, 1⟩ 1 1) spEb := by decide +kernel
theorem pin109 : splitRead (evalPC bpE ⟨2, 1⟩ 1 1) spEt := by decide +kernel
theorem pin110 : ((lowerList spEb).all (fun w => decide
    (stage.keepLowerTop (quadP bpE w) ⟨⟨2, 1⟩, 1⟩ ⟨⟨3, 1⟩, 1⟩
      ⟨3, 1⟩ ⟨2, 1⟩))) = true := by decide +kernel
theorem pin111 : ¬ psdAt spEt := by decide +kernel
theorem pin112 : ¬ psdAt spEb := by decide +kernel

private def spQb : Split 1 := mkSplit 1 (evalPC bpQ ⟨2, 1⟩ 2 1)
private def spQt : Split 1 := mkSplit 1 (evalPC bpQ ⟨3, 1⟩ 2 1)

theorem pin113 : ¬ pShapeAt bpQ 1 1 := by decide +kernel
theorem pin114 : pShapeAt bpQ 1 3 := by decide +kernel
theorem pin115 : splitRead (evalPC bpQ ⟨2, 1⟩ 2 1) spQb := by decide +kernel
theorem pin116 : splitRead (evalPC bpQ ⟨3, 1⟩ 2 1) spQt := by decide +kernel
theorem pin117 : psdAt spQt := by decide +kernel
theorem pin118 : ((lowerList spQb).all (fun w => decide
    (stage.keepLower (quadP bpQ w) ⟨⟨2, 1⟩, 2⟩ ⟨⟨3, 1⟩, 2⟩
      ⟨2, 1⟩ ⟨2, 1⟩))) = true := by decide +kernel
theorem pin119 : ground.getAt ([] : List BPair) (lowerList spQb) 0 = wOne := by
  decide +kernel
theorem pin120 : stage.evalC (quadP bpQ wOne) ⟨⟨2, 1⟩, 2⟩ < stage.unitC := by
  decide +kernel
theorem pin121 : stage.evalC (quadP bpQ wOne) ⟨⟨3, 1⟩, 2⟩ < stage.unitC := by
  decide +kernel
theorem pin122 : ¬ psdAt spQb := by decide +kernel

theorem pin123 : ¬ splitRead (evalPC bpB ⟨3, 1⟩ 1 1) spAt := by decide +kernel
theorem pin124 : ¬ splitRead (evalPC bpE ⟨2, 1⟩ 1 1) spAt := by decide +kernel

/-! The pivot at every order: the order-two polynomial pencil
`[[τ² − 6, τ²], [τ², 28 + τ²]]` deflated at its second key, the
deflation cleared once `22τ² − 168` at the clearing four, its
evaluation at `τ = 1/2` the evaluated blocks' once-cleared
deflation at the evaluated witness and the witness's solve read, the replicated
diagonal's evaluation the entry's weighting of the identity, the
vacant pivot the trailing block at the vacant minor, the pivot list's places inside the
order and the pencil's square frame the tex's own frames (the
designated places of `lem:inertia`'s pivot, `def:elim`'s minor at
matched lists), a place beyond the order or a ragged row reading
the vacant defaults on both sides; the order-three symmetric pencil
deflated at its third
key, the evaluated head symmetric, and the symmetry refused at the
pencil with its first row's second entry moved. -/

private def bpT : split.PMat :=
  [[[⟨1, 7⟩, u, ⟨2, 1⟩], [u, u, ⟨2, 1⟩]], [[u, u, ⟨2, 1⟩], [⟨29, 1⟩, u, ⟨2, 1⟩]]]
private def mT : Mat := evalPC bpT ⟨2, 1⟩ 2 2

theorem pin166 : pShapeAt (pdeflP [1] (compl [1] 2) bpT) 1 4 := by decide +kernel
theorem pin167 : ¬ pShapeAt (pdeflP [1] (compl [1] 2) bpT) 1 1 := by decide +kernel
theorem pin168 : ¬ pShapeAt (pdeflP [] (compl [] 2) bpT) 1 2 :=
  fun h => Nat.noConfusion (Nat.succ.inj (pShape_len h))
theorem pin169 : poly.oneValue (ground.getAt [] (ground.getAt [] (pdeflP [1] [0] bpT) 0) 0)
    [⟨1, 169⟩, u, ⟨23, 1⟩] := by decide +kernel
theorem pin170 : pdeflP [] [0, 1] bpT
    = split.pscaleM (split.pminor (split.pselM [] [] bpT)) (split.pselM [0, 1] [0, 1] bpT) :=
  rfl
theorem pin171 : matOneValue (evalPC (pdeflP [1] [0] bpT) ⟨2, 1⟩ 2 4)
    (deflMatP (selM [1] [1] mT) (selM [1] [0] mT) (selM [0] [0] mT)
      (evalPC (pdeflW [1] [0] bpT) ⟨2, 1⟩ 2 2)) := by decide +kernel
theorem pin172 : matOneValue (evalPC (pdeflP [1] [0] bpT) ⟨2, 1⟩ 2 4)
    (deflMatP (selM [1] [1] mT) (selM [1] [0] mT) (selM [0] [0] mT)
      (evalPC (pdeflW [1] [0] bpT) ⟨2, 1⟩ 2 2)) :=
  evalPC_pdeflP (o := 2) bpT 2 [1] [0] ⟨2, 1⟩ 2 (by decide +kernel) (by decide +kernel)
    (Nat.succ_pos 0) (by decide +kernel) (by decide +kernel)
theorem pin173 : matOneValue (matMul (selM [1] [1] mT) (evalPC (pdeflW [1] [0] bpT) ⟨2, 1⟩ 2 2))
    (matScaleB (minor (selM [1] [1] mT)) (selM [1] [0] mT)) := by decide +kernel
theorem pin174 : matOneValue (matMul (selM [1] [1] mT) (evalPC (pdeflW [1] [0] bpT) ⟨2, 1⟩ 2 2))
    (matScaleB (minor (selM [1] [1] mT)) (selM [1] [0] mT)) :=
  pdeflW_solve bpT 2 [1] [0] ⟨2, 1⟩ 2 (ent_ble (by decide +kernel : pShapeAt bpT 2 2))
    (by decide +kernel)
theorem pin175 : matOneValue (evalPC (split.pdiag (List.replicate 2 [⟨3, 1⟩, ⟨2, 1⟩])) ⟨2, 1⟩ 2 1)
    (matScaleB (poly.evalClear [⟨3, 1⟩, ⟨2, 1⟩] ⟨2, 1⟩ 2 1) (idMat 2)) := by decide +kernel
theorem pin176 : matOneValue (evalPC (split.pdiag (List.replicate 2 [⟨3, 1⟩, ⟨2, 1⟩])) ⟨2, 1⟩ 2 1)
    (matScaleB (poly.evalClear [⟨3, 1⟩, ⟨2, 1⟩] ⟨2, 1⟩ 2 1) (idMat 2)) :=
  evalPC_pdiag_repl _ 2 ⟨2, 1⟩ 2 1

private def bpS : split.PMat :=
  [[[⟨1, 7⟩, u, ⟨2, 1⟩], [u, u, ⟨2, 1⟩], [⟨3, 1⟩]],
   [[u, u, ⟨2, 1⟩], [⟨1, 3⟩, u, ⟨2, 1⟩], [u, u, ⟨2, 1⟩]],
   [[⟨3, 1⟩], [u, u, ⟨2, 1⟩], [⟨29, 1⟩, u, ⟨2, 1⟩]]]
private def bpN : split.PMat :=
  [[[⟨1, 7⟩, u, ⟨2, 1⟩], [⟨4, 1⟩, u, ⟨2, 1⟩], [⟨3, 1⟩]],
   [[u, u, ⟨2, 1⟩], [⟨1, 3⟩, u, ⟨2, 1⟩], [u, u, ⟨2, 1⟩]],
   [[⟨3, 1⟩], [u, u, ⟨2, 1⟩], [⟨29, 1⟩, u, ⟨2, 1⟩]]]

theorem pin177 : pShapeAt (pdeflP [2] (compl [2] 3) bpS) 2 4 := by decide +kernel
theorem pin178 : matOneValue (transposeM (evalPC (pdeflP [2] (compl [2] 3) bpS) ⟨2, 1⟩ 2 4))
    (evalPC (pdeflP [2] (compl [2] 3) bpS) ⟨2, 1⟩ 2 4) := by decide +kernel
theorem pin179 : matOneValue (transposeM (evalPC (pdeflP [2] (compl [2] 3) bpS) ⟨2, 1⟩ 2 4))
    (evalPC (pdeflP [2] (compl [2] 3) bpS) ⟨2, 1⟩ 2 4) :=
  evalPC_pdeflP_symm (o := 3) bpS 2 [2] (compl [2] 3) ⟨2, 1⟩ 2 (by decide +kernel)
    (by decide +kernel) (Nat.succ_pos 0) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
theorem pin180 : ¬ matOneValue (transposeM (evalPC bpN ⟨2, 1⟩ 2 2)) (evalPC bpN ⟨2, 1⟩ 2 2) := by
  decide +kernel
theorem pin181 : ¬ matOneValue (transposeM (evalPC (pdeflP [2] (compl [2] 3) bpN) ⟨2, 1⟩ 2 4))
    (evalPC (pdeflP [2] (compl [2] 3) bpN) ⟨2, 1⟩ 2 4) := by decide +kernel

/-! The cover's arms at the once-cleared deflation and the vacant
coupling: the pivot whose coupling to the trailing places reads the
sum's unit reads the trailing block's own cover in the deflation's
place (`Cover.diag`), decided at the pencil `[[t² − 2, 0], [0, 5]]`
over the deflation tier's segment with the constancy theorem run
through it, and refused at that tier's pencil, whose coupling is
occupied; and the order-two piece with the determinant upper reads
the once-cleared deflation beneath it (`Cover.twoUp`), decided at
the deflation tier's pencil with the order-nought deflation beneath,
its leading entry's side refused at the lower read. -/

private def sV : split.PMat :=
  [[[⟨1, 3⟩, u, ⟨2, 1⟩], []], [[], [⟨6, 1⟩]]]
private def cvDiag : Cover :=
  Cover.diag hiD 0 true ⟨4, 1⟩ ⟨2, 1⟩
    (Cover.one hiD 0 true ⟨4, 1⟩ ⟨2, 1⟩ Cover.nought Cover.done) Cover.done

theorem pin182 : coverRead sV 2 2 loD hiD cvDiag := by decide +kernel
theorem pin183 : ¬ coverRead sD 2 2 loD hiD cvDiag := by decide +kernel
theorem pin184 : inertia.revAt (inertia.mkSplit 2 (evalPC sV xDn xDc 2)) = 0 :=
  cellCount sV 2 0 loD hiD cvDiag (by decide +kernel) (by decide +kernel)
    loDn loDc (by decide +kernel) (by decide +kernel)
    (inertia.mkSplit 2 (evalPC sV loDn loDc 2))
    (by decide +kernel)
    xDn xDc (by decide +kernel) (by decide +kernel)
    (inertia.mkSplit 2 (evalPC sV xDn xDc 2))
    (inertia.mkSplit_read 2 (evalPC sV xDn xDc 2)
      (by decide +kernel) (by decide +kernel))

private def cvTwo : Cover :=
  Cover.twoUp hiD 0 1 ⟨4, 1⟩ ⟨2, 1⟩ true ⟨4, 1⟩ ⟨2, 1⟩ Cover.nought Cover.done

theorem pin185 : coverRead sD 2 2 loD hiD cvTwo := by decide +kernel
theorem pin186 : ¬ coverRead sD 2 2 loD hiD
    (Cover.twoUp hiD 0 1 ⟨4, 1⟩ ⟨2, 1⟩ false ⟨4, 1⟩ ⟨2, 1⟩ Cover.nought Cover.done) := by
  decide +kernel

/-! The vacant-coupling pivot cover at the diagonal pencil
`[[−3 − t², 0], [0, 5]]`: the leading entry's lower read with the
nest beneath it at the deflation's one entry `5 (3 + t²)²`, decided
whole. -/

private def sW : split.PMat :=
  [[[⟨1, 4⟩, u, ⟨1, 2⟩], []], [[], [⟨6, 1⟩]]]

theorem pin187 : coverRead sW 2 2 loD hiD (vacCover hiD ⟨4, 1⟩ ⟨2, 1⟩ 1) := by
  decide +kernel
theorem pin188 : ¬ coverRead sV 2 2 loD hiD (vacCover hiD ⟨4, 1⟩ ⟨2, 1⟩ 1) := by
  decide +kernel
theorem pin189 : ¬ (elim.minor (evalPC sV xDn xDc 2)).oneValue BPair.unit := by
  decide +kernel
theorem pin190 : ¬ (elim.minor (evalPC sV xDn xDc 2)).oneValue BPair.unit :=
  cover_rootfree (o := 2) sV 2 loD hiD cvDiag (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) xDn xDc (by decide +kernel) (by decide +kernel)

/-! The swapped order-one deflation at value-unit couplings: the
pivot entry's swap on the trailing block, decided and through the
theorem at the constant diagonal pencil. -/

theorem pin191 : split.pmatOneValue (pdeflM [0] [1] dfS)
    (split.pscaleM (poly.neg (ground.getAt [] (ground.getAt [] dfS 0) 0))
      (split.pselM [1] [1] dfS)) := by decide +kernel
theorem pin192 : split.pmatOneValue (pdeflM [0] [1] dfS)
    (split.pscaleM (poly.neg (ground.getAt [] (ground.getAt [] dfS 0) 0))
      (split.pselM [1] [1] dfS)) :=
  pdeflM_offC dfS 0 [1] (by decide +kernel)

end cellcount
