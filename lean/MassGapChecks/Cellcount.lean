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
refused beside it, the cleared
deflation's evaluation against the evaluated blocks' own at two
clearings both decided and through the theorem, the adjugate's
solve at pivots of orders two and one, and the order-one deflation
at value-unit couplings — the constant diagonal pencil reading the
pivot entry's square on the trailing block, refused at the occupied
coupling — with the cleared deflation's shape read at the trailing
order and the odd-multiple clearing, its pivot-order binder refused
at the vacant pivot list.  The pivot cover at the
same pencil on `[2, 129/64]`: the nested certificate — the outer
pivot `t² - 2` on its upper side over the subinterval at the bound
`[3 : 1]`, the cleared deflation `5t⁴ - 21t² + 22` its own piece
on the same side and bound with the order-nought deflation
beneath — decided whole, the constancy theorem run at `257/128`
against the lower endpoint with both counts the positive-definite
`0`, the broken chain's refusal at a piece stopping short of the
segment's upper endpoint (the same certificate decided over its
own shorter segment), the flipped side certificate's refusal at
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
set_option maxHeartbeats 4000000

open ground poly elim inertia cellcount

private def u : BPair := BPair.unit

/-- The pencil `S(t) = [[t, 1], [1, t]]`. -/
private def sP : split.PMat :=
  [[[u, ⟨2, 1⟩], [⟨2, 1⟩]], [[⟨2, 1⟩], [u, ⟨2, 1⟩]]]

example : pShapeAt sP 2 1 := by decide +kernel
example : ¬ pShapeAt sP 2 0 := by decide +kernel
example : poly.oneValue (split.pminor sP) [⟨1, 2⟩, u, ⟨2, 1⟩] := by
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

example : countAt sP 1 u 1 1 sp0 := by decide +kernel
example : countAt sP 1 ⟨3, 1⟩ 1 0 sp2 := by decide +kernel
example : countAt sP 1 ⟨4, 1⟩ 1 0 sp3 := by decide +kernel

/-! The divisor's witness: `t² - 1` its own squarefree part at the
Bézout `-4(t²-1) + (2t)(2t) = 4`. -/

private def ctD : DivCert :=
  ⟨[], [⟨1, 2⟩, u, ⟨2, 1⟩], [u, ⟨3, 1⟩], [⟨1, 5⟩], [u, ⟨3, 1⟩],
   [⟨1, 2⟩, u, ⟨2, 1⟩], [⟨1, 5⟩], [u, ⟨3, 1⟩],
   1, 1, 1, 1, ⟨5, 1⟩, ⟨5, 1⟩⟩

example : divRead (split.pminor sP) ctD := by decide +kernel
example : poly.oneValue (deckfactor.clearVarBT ctD.sq)
    [⟨1, 2⟩, u] := by decide +kernel

/-! The crossing segment `[0, 2]`: the root `1` inside breaks the
avoidance, the pencil mixed at `diag(2, -24)`. -/

private def spHc : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.one ⟨3, 1⟩, .one ⟨3, 1⟩], 0, rfl⟩

private def spBx : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨5, 1⟩], [⟨1, 1⟩, ⟨3, 1⟩]], rfl⟩,
   ⟨[[⟨3, 1⟩, ⟨1, 5⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨3, 1⟩, .one ⟨1, 25⟩], 0, rfl⟩

example : hermitesign.segCountRead [⟨1, 2⟩, u] u ⟨3, 1⟩ 1 1
    spHc spBx := by decide +kernel
example : ¬ hermitesign.segCountRead [⟨1, 2⟩, u] u ⟨3, 1⟩ 1 0
    spHc spBx := by decide +kernel

/-! The cleared-variable tier at the pencil `[[2t - 3]]`: the top
`2` off the constant's divisors, the cleared monic `y - 3` at
`y = 2t` with the roots the display's own rescaled by the
magnitude. -/


private def sP2 : split.PMat := [[[⟨1, 4⟩, ⟨3, 1⟩]]]

private def ctN : DivCert :=
  ⟨[], [⟨1, 4⟩, ⟨3, 1⟩], [⟨3, 1⟩], [], [⟨2, 1⟩],
   [⟨1, 4⟩, ⟨3, 1⟩], [], [⟨2, 1⟩], 1, 1, 1, 1, ⟨3, 1⟩, ⟨3, 1⟩⟩

example : divRead (split.pminor sP2) ctN := by decide +kernel
example : poly.oneValue (deckfactor.clearVarBT ctN.sq) [⟨1, 4⟩] := by
  decide +kernel

/-! The straddle `[1, 2]` refuses: the cleared root `3` inside the
rescaled `[2, 4]`, the avoidance at count `1` with the endpoint
counts split `1` against `0`. -/

example : hermitesign.segCountRead (deckfactor.clearVarBT ctN.sq)
    (deckfactor.clearAt ctN.sq ⟨2, 1⟩)
    (deckfactor.clearAt ctN.sq ⟨3, 1⟩) 1 1
    (spOne ⟨2, 1⟩) (spOne ⟨1, 2⟩) := by decide +kernel

/-! The rescaling is the read's own conjunct: at the unrescaled
right endpoint the cleared monic reads the root itself, and the
count refuses there at every split, the endpoint conjunct's own
read. -/

example : (stage.evalC (poly.monic (deckfactor.clearVarBT ctN.sq))
    ⟨⟨4, 1⟩, 1⟩).oneValue stage.unitC := by decide +kernel
example : ¬ hermitesign.segCountRead (deckfactor.clearVarBT ctN.sq)
    ⟨3, 1⟩ ⟨4, 1⟩ 1 0 (spOne ⟨2, 1⟩) (spOne ⟨4, 1⟩) := by decide +kernel

/-! The clearing reads one value at every representative: the
squarefree part padded by a unit tail names the one cleared monic,
the one rescaled point, and the one certificate, the homogeneity
principle's read at `poly.vnorm`. -/

private def ctP : DivCert :=
  ⟨[], [⟨1, 4⟩, ⟨3, 1⟩], [⟨3, 1⟩], [], [⟨2, 1⟩],
   [⟨1, 4⟩, ⟨3, 1⟩, u], [], [⟨2, 1⟩], 1, 1, 1, 1, ⟨3, 1⟩, ⟨3, 1⟩⟩

example : poly.oneValue (deckfactor.clearVarBT ctP.sq)
    (deckfactor.clearVarBT ctN.sq) := by decide +kernel
example : (deckfactor.clearAt ctP.sq ⟨3, 1⟩).oneValue
    (deckfactor.clearAt ctN.sq ⟨3, 1⟩) := by decide +kernel
example : divRead (split.pminor sP2) ctP := by decide +kernel

/-! The forged Bézout witness refuses: the part's combination moved
off the displayed constant, every further conjunct at the true
data. -/

private def ctB : DivCert :=
  ⟨[], [⟨1, 4⟩, ⟨3, 1⟩], [⟨3, 1⟩], [], [⟨2, 1⟩],
   [⟨1, 4⟩, ⟨3, 1⟩], [⟨3, 1⟩], [⟨2, 1⟩], 1, 1, 1, 1, ⟨3, 1⟩, ⟨3, 1⟩⟩

example : ¬ divRead (split.pminor sP2) ctB := by decide +kernel

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

example : split.pSymAt sD 2 := by decide +kernel
example : split.pSymAt sD 2 :=
  split.pSymAt_of sD 2 (fun i j hi hj =>
    (by decide +kernel : ∀ i, i < 2 → ∀ j, j < 2 → poly.oneValue
      (ground.getAt [] (ground.getAt [] sD i) j)
      (ground.getAt [] (ground.getAt [] sD j) i)) i hi j hj)
example : pShapeAt sD 2 2 := by decide +kernel

/-- The exchanged entry moved off its partner: the symmetry read
refuses. -/
private def sA : split.PMat :=
  [[[⟨1, 3⟩, u, ⟨2, 1⟩], [⟨2, 1⟩]], [[⟨3, 1⟩], [⟨6, 1⟩]]]

example : ¬ split.pSymAt sA 2 := by decide +kernel
example : ¬ (∀ i, i < 2 → ∀ j, j < 2 → poly.oneValue
    (ground.getAt [] (ground.getAt [] sA i) j)
    (ground.getAt [] (ground.getAt [] sA j) i)) := by decide +kernel

example : elim.matOneValue
    (evalPC (pdefl [0] [1] sD) ⟨4, 1⟩ 1
      ((2 * ([0] : List Nat).length + 1) * 2))
    (inertia.deflMat (evalPC (split.pselM [0] [0] sD) ⟨4, 1⟩ 1 2)
      (evalPC (split.pselM [0] [1] sD) ⟨4, 1⟩ 1 2)
      (evalPC (split.pselM [1] [1] sD) ⟨4, 1⟩ 1 2)
      (elim.matMul (adj2v ([0] : List Nat).length
          (evalPC (split.pselM [0] [0] sD) ⟨4, 1⟩ 1 2))
        (evalPC (split.pselM [0] [1] sD) ⟨4, 1⟩ 1 2))) := by decide +kernel

example : elim.matOneValue
    (evalPC (pdefl [0] [1] sD) ⟨4, 1⟩ 1
      ((2 * ([0] : List Nat).length + 1) * 2))
    (inertia.deflMat (evalPC (split.pselM [0] [0] sD) ⟨4, 1⟩ 1 2)
      (evalPC (split.pselM [0] [1] sD) ⟨4, 1⟩ 1 2)
      (evalPC (split.pselM [1] [1] sD) ⟨4, 1⟩ 1 2)
      (elim.matMul (adj2v ([0] : List Nat).length
          (evalPC (split.pselM [0] [0] sD) ⟨4, 1⟩ 1 2))
        (evalPC (split.pselM [0] [1] sD) ⟨4, 1⟩ 1 2))) :=
  evalPC_pdefl (o := 2) sD 2 [0] [1] ⟨4, 1⟩ 1 (by decide +kernel)
    (by decide +kernel) (Or.inl rfl) (by decide +kernel) (by decide +kernel)

example : elim.matOneValue
    (evalPC (pdefl [0] [1] sD) ⟨4, 1⟩ 2
      ((2 * ([0] : List Nat).length + 1) * 2))
    (inertia.deflMat (evalPC (split.pselM [0] [0] sD) ⟨4, 1⟩ 2 2)
      (evalPC (split.pselM [0] [1] sD) ⟨4, 1⟩ 2 2)
      (evalPC (split.pselM [1] [1] sD) ⟨4, 1⟩ 2 2)
      (elim.matMul (adj2v ([0] : List Nat).length
          (evalPC (split.pselM [0] [0] sD) ⟨4, 1⟩ 2 2))
        (evalPC (split.pselM [0] [1] sD) ⟨4, 1⟩ 2 2))) := by decide +kernel

example : elim.matOneValue
    (evalPC (pdefl [0] [1] sD) ⟨4, 1⟩ 2
      ((2 * ([0] : List Nat).length + 1) * 2))
    (inertia.deflMat (evalPC (split.pselM [0] [0] sD) ⟨4, 1⟩ 2 2)
      (evalPC (split.pselM [0] [1] sD) ⟨4, 1⟩ 2 2)
      (evalPC (split.pselM [1] [1] sD) ⟨4, 1⟩ 2 2)
      (elim.matMul (adj2v ([0] : List Nat).length
          (evalPC (split.pselM [0] [0] sD) ⟨4, 1⟩ 2 2))
        (evalPC (split.pselM [0] [1] sD) ⟨4, 1⟩ 2 2))) :=
  evalPC_pdefl (o := 2) sD 2 [0] [1] ⟨4, 1⟩ 2 (by decide +kernel)
    (by decide +kernel) (Or.inl rfl) (by decide +kernel) (by decide +kernel)

/-! The deflation theorem's binder refusals: the symmetry at the
exchanged-entry pencil, every further binder holding, and the shape
at the undersized clearing, the point's own read the isolation. -/

example : ¬ elim.matOneValue
    (evalPC (pdefl [0] [1] sA) ⟨4, 1⟩ 1
      ((2 * ([0] : List Nat).length + 1) * 2))
    (inertia.deflMat (evalPC (split.pselM [0] [0] sA) ⟨4, 1⟩ 1 2)
      (evalPC (split.pselM [0] [1] sA) ⟨4, 1⟩ 1 2)
      (evalPC (split.pselM [1] [1] sA) ⟨4, 1⟩ 1 2)
      (elim.matMul (adj2v ([0] : List Nat).length
          (evalPC (split.pselM [0] [0] sA) ⟨4, 1⟩ 1 2))
        (evalPC (split.pselM [0] [1] sA) ⟨4, 1⟩ 1 2))) := by
  decide +kernel

example : pShapeAt sA 2 2 := by decide +kernel

example : ¬ pShapeAt sD 2 1 := by decide +kernel

example : ¬ elim.matOneValue
    (evalPC (pdefl [0] [1] sD) ⟨5, 1⟩ 3
      ((2 * ([0] : List Nat).length + 1) * 1))
    (inertia.deflMat (evalPC (split.pselM [0] [0] sD) ⟨5, 1⟩ 3 1)
      (evalPC (split.pselM [0] [1] sD) ⟨5, 1⟩ 3 1)
      (evalPC (split.pselM [1] [1] sD) ⟨5, 1⟩ 3 1)
      (elim.matMul (adj2v ([0] : List Nat).length
          (evalPC (split.pselM [0] [0] sD) ⟨5, 1⟩ 3 1))
        (evalPC (split.pselM [0] [1] sD) ⟨5, 1⟩ 3 1))) := by
  decide +kernel

private def pv2 : elim.Mat := [[⟨3, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨1, 2⟩]]
private def bv2 : elim.Mat := [[⟨5, 1⟩], [⟨1, 4⟩]]

example : elim.matOneValue
    (elim.matMul pv2 (elim.matMul (adj2v 2 pv2) bv2))
    (inertia.matScaleB (elim.minor pv2) bv2) := by decide +kernel

example : elim.matOneValue
    (elim.matMul pv2 (elim.matMul (adj2v 2 pv2) bv2))
    (inertia.matScaleB (elim.minor pv2) bv2) :=
  adj2v_solve (m := 1) pv2 bv2 (Or.inr rfl) (by decide +kernel) rfl
    ⟨rfl, rfl, trivial⟩

private def pv1 : elim.Mat := [[⟨4, 1⟩]]
private def bv1 : elim.Mat := [[⟨2, 1⟩, ⟨1, 3⟩]]

example : elim.matOneValue
    (elim.matMul pv1 (elim.matMul (adj2v 1 pv1) bv1))
    (inertia.matScaleB (elim.minor pv1) bv1) := by decide +kernel

example : elim.matOneValue
    (elim.matMul pv1 (elim.matMul (adj2v 1 pv1) bv1))
    (inertia.matScaleB (elim.minor pv1) bv1) :=
  adj2v_solve (m := 2) pv1 bv1 (Or.inl rfl) (by decide +kernel) rfl
    ⟨rfl, trivial⟩


/-! The deflation at value-unit couplings: the constant pencil
`[[2, 0], [0, 4]]` whose couplings read the sum's unit without
standing at the unit pair, the deflation reading the pivot entry's
square on the trailing block — decided and through the theorem —
against the occupied-coupling pencil `[[2, 2], [2, 4]]`, where the
correction survives and the two part company. -/

private def dfS : split.PMat :=
  [[[⟨3, 1⟩], [⟨2, 2⟩]], [[⟨2, 2⟩], [⟨5, 1⟩]]]

example : split.pmatOneValue (pdefl [0] [1] dfS)
    (split.pscaleM (poly.mul (ground.getAt [] (ground.getAt [] dfS 0) 0)
      (ground.getAt [] (ground.getAt [] dfS 0) 0))
      (split.pselM [1] [1] dfS)) := by decide +kernel

example : split.pmatOneValue (pdefl [0] [1] dfS)
    (split.pscaleM (poly.mul (ground.getAt [] (ground.getAt [] dfS 0) 0)
      (ground.getAt [] (ground.getAt [] dfS 0) 0))
      (split.pselM [1] [1] dfS)) :=
  pdefl_offC dfS 0 [1] (by decide +kernel)

private def dfT : split.PMat :=
  [[[⟨3, 1⟩], [⟨3, 1⟩]], [[⟨3, 1⟩], [⟨5, 1⟩]]]

example : ¬ poly.unitTail (ground.getAt ([] : Poly)
    (ground.getAt ([] : List Poly) dfT (ground.getAt 0 [1] 0)) 0) := by
  decide +kernel

example : ¬ split.pmatOneValue (pdefl [0] [1] dfT)
    (split.pscaleM (poly.mul (ground.getAt [] (ground.getAt [] dfT 0) 0)
      (ground.getAt [] (ground.getAt [] dfT 0) 0))
      (split.pselM [1] [1] dfT)) := by decide +kernel


/-! The cleared deflation's shape read: the trailing order at the
odd-multiple clearing, decided and through the theorem at both
pivot orders — the one-place pivot on the standing pencil at
clearing two with a below-clearing refusal isolating the
odd-multiple factor, and the two-place pivot at a clearing-one
order-three pencil — with the shape binder refused at the pencil
read one clearing low and the pivot-order binder refused at the
vacant pivot list, where the adjugate is vacant, the correction's
rows truncate the sum, and the shape read fails at every occupied
trailing list. -/

example : pShapeAt (pdefl [0] [1] sD) 1 ((2 * 1 + 1) * 2) := by
  decide +kernel
example : pShapeAt (pdefl [0] [1] sD) 1 ((2 * 1 + 1) * 2) :=
  pShape_pdefl sD 2 2 [0] [1] (by decide +kernel) (Or.inl rfl)
example : ¬ pShapeAt (pdefl [0] [1] sD) 1 3 := by decide +kernel

private def sf3 : split.PMat :=
  [[[⟨2, 1⟩, ⟨1, 2⟩], [u], [u]],
   [[u], [⟨3, 1⟩, u], [u]],
   [[u], [u], [⟨4, 1⟩, ⟨2, 1⟩]]]

example : pShapeAt (pdefl [0, 1] [2] sf3) 1 ((2 * 2 + 1) * 1) := by
  decide +kernel
example : pShapeAt (pdefl [0, 1] [2] sf3) 1 ((2 * 2 + 1) * 1) :=
  pShape_pdefl sf3 3 1 [0, 1] [2] (by decide +kernel) (Or.inr rfl)
example : ¬ pShapeAt (pdefl [0, 1] [2] sf3) 1 2 := by decide +kernel

example : ¬ pShapeAt sD 2 1 := by decide +kernel
example : ¬ pShapeAt (pdefl [0] [1] sD) 1 ((2 * 1 + 1) * 1) := by
  decide +kernel

private def sfX : split.PMat := [[[(⟨2, 1⟩ : BPair)]]]

example : pShapeAt sfX 1 0 := by decide +kernel
example : ¬ pShapeAt (pdefl [] [0] sfX) ([0] : List Nat).length
    ((2 * ([] : List Nat).length + 1) * 0) := by decide +kernel


/-! The pivot cover at `S(t) = [[t² - 2, 1], [1, 5]]` over
`[2, 129/64]`: the segment is the width the deflation's priced side
read admits — at the lower endpoint the deflation reads `18` while
its derivative's coefficient fold at the bound `[3 : 1]` reads
`666`, so the subinterval's width sits below `18/666`. -/

private def loDn : BPair := ⟨3, 1⟩
private def loDc : Pos := 1
private def loD : CPair := ⟨loDn, loDc⟩
private def hiD : CPair := ⟨⟨130, 1⟩, 64⟩

private def cv1 : Cover := diagNest hiD ⟨4, 1⟩ ⟨2, 1⟩ 2

example : coverRead sD 2 2 loD hiD cv1 := by decide +kernel

/-! The constancy theorem at an interior point against the lower
endpoint, the two splits the construction's own. -/

private def xDn : BPair := ⟨258, 1⟩
private def xDc : Pos := 128
private def xD : CPair := ⟨xDn, xDc⟩

example : inertia.revAt (inertia.mkSplit 2 (evalPC sD loDn loDc 2))
    = 0 := by decide +kernel
example : inertia.revAt (inertia.mkSplit 2 (evalPC sD xDn xDc 2))
    = 0 := by decide +kernel

example : inertia.revAt (inertia.mkSplit 2 (evalPC sD xDn xDc 2))
    = inertia.revAt (inertia.mkSplit 2 (evalPC sD loDn loDc 2)) :=
  cover_const (o := 2) sD 2 loD hiD cv1 (by decide +kernel)
    xDn xDc loDn loDc
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

example : coverRead sD 2 2 loD xD cvShort := by decide +kernel
example : ¬ coverRead sD 2 2 loD hiD cvShort := by decide +kernel

private def cvFlip : Cover :=
  Cover.one hiD 0 false ⟨4, 1⟩ ⟨2, 1⟩
    (diagNest hiD ⟨4, 1⟩ ⟨2, 1⟩ 1) Cover.done

example : ¬ coverRead sD 2 2 loD hiD cvFlip := by decide +kernel

/-! The closing form's shape conjunct: at the degree-off pencil
`[[1 - t²]]` at clearing `0`, two representatives of the one
segment point read distinct counts, so the `.done` arm without its
shape read is refused — the shape conjunct is the closing form's
own binder. -/

private def sK : split.PMat := [[[⟨2, 1⟩, u, ⟨1, 2⟩]]]

example : (⟨⟨2, 1⟩, 1⟩ : CPair).oneValue ⟨⟨3, 1⟩, 2⟩ := by
  decide +kernel
example : ¬ pShapeAt sK 1 0 := by decide +kernel
example : inertia.revAt (inertia.mkSplit 1 (evalPC sK ⟨2, 1⟩ 1 0))
    = 0 := by decide +kernel
example : inertia.revAt (inertia.mkSplit 1 (evalPC sK ⟨3, 1⟩ 2 0))
    = 1 := by decide +kernel

/-! The subinterval's frame at the designated place, refused at
repeated places. -/

example : pieceRead sD 2 2 loD hiD [0] := by decide +kernel
example : ¬ pieceRead sD 2 2 loD hiD [0, 0] := by decide +kernel

/-! The one transport (`cellCount`): the sampled vacant count at the
lower endpoint holds at the interior point through the cover, the
route beside the constancy theorem's own; and the level carrier's
evaluation at a point (`levelPMat_eval`): the order-one carrier
`levelPMat [5] [-1] [1]` at the level `⟨3 : 1⟩` evaluated at the
point `⟨3 : 1⟩` over the clearing one reads the level datum at the
clearing's square joined to the magnetic member at the point's, an
occupied middle refusing the read. -/

example : inertia.revAt (inertia.mkSplit 2 (evalPC sD xDn xDc 2)) = 0 :=
  cellCount sD 2 0 loD hiD cv1 (by decide +kernel)
    loDn loDc (by decide +kernel) (by decide +kernel)
    (inertia.mkSplit 2 (evalPC sD loDn loDc 2))
    (by decide +kernel)
    xDn xDc (by decide +kernel) (by decide +kernel)
    (inertia.mkSplit 2 (evalPC sD xDn xDc 2))
    (inertia.mkSplit_read 2 (evalPC sD xDn xDc 2)
      (by decide +kernel) (by decide +kernel))

example : elim.matOneValue
    (evalPC (levelPMat [[⟨6, 1⟩]] [[⟨1, 2⟩]] [[⟨2, 1⟩]] 3 1
      [ground.BPair.unit]) ⟨3, 1⟩ 1 2)
    (elim.matAdd
      (inertia.matScaleB (ground.bpow (ground.BPair.ofPos 1) 2)
        (inertia.siteDatum
          (elim.matAdd [[⟨6, 1⟩]] (inertia.matScale 1 [[⟨2, 1⟩]]))
          (inertia.matScale 3 [[⟨2, 1⟩]])))
      (inertia.matScaleB (ground.bpow ⟨3, 1⟩ 2) [[⟨1, 2⟩]])) := by
  decide +kernel

example : elim.matOneValue
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

example : ¬ elim.matOneValue
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
honest `[[x - 3]]` boundary data a foreign positive-semidefinite
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

example : (poly.evalClear (quadP bpB wOne) ⟨3, 1⟩ 1 1).oneValue
    (elim.dotN wOne (elim.matVec (evalPC bpB ⟨3, 1⟩ 1 1) wOne)) := by
  decide +kernel

example : (poly.evalClear (quadP bpB wOne) ⟨3, 1⟩ 1 1).oneValue
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
example : (lowerList spAb).length = 0 := by decide +kernel
private theorem tieA : ((lowerList spAb).all (fun w => decide
    (stage.keepLower (quadP bpA w) ⟨⟨2, 1⟩, 1⟩ ⟨⟨3, 1⟩, 1⟩
      ⟨3, 1⟩ ⟨2, 1⟩))) = true := by decide +kernel
example : psdAt spAb := by decide +kernel

example : psdAt spAb :=
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
example : (lowerList spCb).length = 0 := by decide +kernel
private theorem tieC : ((lowerList spCb).all (fun w => decide
    (stage.keepLowerTop (quadP bpC w) ⟨⟨2, 1⟩, 1⟩ ⟨⟨3, 1⟩, 1⟩
      ⟨3, 1⟩ ⟨2, 1⟩))) = true := by decide +kernel
example : psdAt spCb := by decide +kernel

example : psdAt spCb :=
  boundary_psd_hi bpC 1 ⟨3, 1⟩ 1 ⟨2, 1⟩ 1 ⟨3, 1⟩ ⟨2, 1⟩ spCb spCt
    shC srCb srCt psdC tieC

private def spBb : Split 1 := mkSplit 1 (evalPC bpB ⟨2, 1⟩ 1 1)
private def spBt : Split 1 := mkSplit 1 (evalPC bpB ⟨3, 1⟩ 1 1)

example : pShapeAt bpB 1 1 := by decide +kernel
example : splitRead (evalPC bpB ⟨2, 1⟩ 1 1) spBb := by decide +kernel
example : splitRead (evalPC bpB ⟨3, 1⟩ 1 1) spBt := by decide +kernel
example : ((lowerList spBb).all (fun w => decide
    (stage.keepLower (quadP bpB w) ⟨⟨2, 1⟩, 1⟩ ⟨⟨3, 1⟩, 1⟩
      ⟨3, 1⟩ ⟨2, 1⟩))) = true := by decide +kernel
example : ¬ psdAt spBt := by decide +kernel
example : ¬ psdAt spBb := by decide +kernel

private def spDb : Split 1 := mkSplit 1 (evalPC bpD ⟨2, 1⟩ 1 1)
private def spDt : Split 1 := mkSplit 1 (evalPC bpD ⟨4, 1⟩ 1 1)

example : pShapeAt bpD 1 1 := by decide +kernel
example : splitRead (evalPC bpD ⟨2, 1⟩ 1 1) spDb := by decide +kernel
example : splitRead (evalPC bpD ⟨4, 1⟩ 1 1) spDt := by decide +kernel
example : psdAt spDt := by decide +kernel
example : ((lowerList spDb).all (fun w => decide
    (stage.keepLower (quadP bpD w) ⟨⟨2, 1⟩, 1⟩ ⟨⟨4, 1⟩, 1⟩
      ⟨4, 1⟩ ⟨2, 1⟩))) = false := by decide +kernel
example : ground.getAt ([] : List BPair) (lowerList spDb) 0 = wOne := by
  decide +kernel
example : stage.evalC (quadP bpD wOne) ⟨⟨2, 1⟩, 1⟩ < stage.unitC := by
  decide +kernel
example : ¬ (stage.evalC (quadP bpD wOne) ⟨⟨4, 1⟩, 1⟩ < stage.unitC) := by
  decide +kernel
example : ¬ psdAt spDb := by decide +kernel

private def spEb : Split 1 := mkSplit 1 (evalPC bpE ⟨3, 1⟩ 1 1)
private def spEt : Split 1 := mkSplit 1 (evalPC bpE ⟨2, 1⟩ 1 1)

example : pShapeAt bpE 1 1 := by decide +kernel
example : splitRead (evalPC bpE ⟨3, 1⟩ 1 1) spEb := by decide +kernel
example : splitRead (evalPC bpE ⟨2, 1⟩ 1 1) spEt := by decide +kernel
example : ((lowerList spEb).all (fun w => decide
    (stage.keepLowerTop (quadP bpE w) ⟨⟨2, 1⟩, 1⟩ ⟨⟨3, 1⟩, 1⟩
      ⟨3, 1⟩ ⟨2, 1⟩))) = true := by decide +kernel
example : ¬ psdAt spEt := by decide +kernel
example : ¬ psdAt spEb := by decide +kernel

private def spQb : Split 1 := mkSplit 1 (evalPC bpQ ⟨2, 1⟩ 2 1)
private def spQt : Split 1 := mkSplit 1 (evalPC bpQ ⟨3, 1⟩ 2 1)

example : ¬ pShapeAt bpQ 1 1 := by decide +kernel
example : pShapeAt bpQ 1 3 := by decide +kernel
example : splitRead (evalPC bpQ ⟨2, 1⟩ 2 1) spQb := by decide +kernel
example : splitRead (evalPC bpQ ⟨3, 1⟩ 2 1) spQt := by decide +kernel
example : psdAt spQt := by decide +kernel
example : ((lowerList spQb).all (fun w => decide
    (stage.keepLower (quadP bpQ w) ⟨⟨2, 1⟩, 2⟩ ⟨⟨3, 1⟩, 2⟩
      ⟨2, 1⟩ ⟨2, 1⟩))) = true := by decide +kernel
example : ground.getAt ([] : List BPair) (lowerList spQb) 0 = wOne := by
  decide +kernel
example : stage.evalC (quadP bpQ wOne) ⟨⟨2, 1⟩, 2⟩ < stage.unitC := by
  decide +kernel
example : stage.evalC (quadP bpQ wOne) ⟨⟨3, 1⟩, 2⟩ < stage.unitC := by
  decide +kernel
example : ¬ psdAt spQb := by decide +kernel

example : ¬ splitRead (evalPC bpB ⟨3, 1⟩ 1 1) spAt := by decide +kernel
example : ¬ splitRead (evalPC bpE ⟨2, 1⟩ 1 1) spAt := by decide +kernel
