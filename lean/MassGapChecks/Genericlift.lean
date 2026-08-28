import MassGap.Res
import MassGap.Rankstable
import MassGap.Serstable
/-!
The check module for `lem:genericlift`: the batteries re-read the
polynomial-pair calculus by kernel `decide`.  Clause (i) at the
pairs `[t² + t : t + 1]` and `[t : 1]` — the one-value reads, the
cross datum at the sum's unit, and the lift certificate at three
apart arguments — with the difference pair `[t² - 1 : t - 1]`
against `[t + 1 : 1]` beside it and the off-value refusals.
Clause (ii) at the pencils `[[t,1],[1,t]]` and
`[[t,1,0],[1,t,1],[0,1,t]]` — the adjugate's solved witness
`M adj(M) = det(M) 1` with the determinants `t² - 1` and
`t³ - 2t` occupied, decided and through the theorem route in both
product orders, the square binder a clearance at the ragged frame
whose missing entry sits beyond the walked keys and load-bearing
at the wide first row, where both orders refuse.  Clause (iii) at
`t + 2`, `(t+1)(t+2)` and
`1 - t` — the radius clearances with the under-radius refusal, the
settled sides, and the beyond-radius evaluation pins — with the
side theorem itself run at `lem:rankstable`'s `2 z²` and `z - 1`,
at the lower-top literal `2 - 3 z`, and at `z - 5`, whose
below-radius argument reads the opposite side and refuses the
clearance (the theorem's binder load-bearing); and again at
`lem:serstable`'s own coordinates — the `B` Casimir numerator's
`6 z`, the `C` dimension pair at the word `[2]`, the negated
Casimir's lower top, and the `D` Casimir numerator's `8 z - 16`,
whose below-radius argument reads the opposite side.  Clause
(iv)'s radii fold over the three.  The certified reduction beside
them: the descent's tuple decided at a constant divisor, at a
common factor with the reduced members' lengths pinned, and at two
vacant members refused, with `pReduce_read` exhibited on both arms
and the second spelling `pAddR` at a doubled denominator; and the
reduction's cost at `con:res`' step-1 magnitude, the module's
heaviest read.  The pair adjugate's descent beside clause (ii):
the walk adjugate against the fold adjugate at the occupied square
frames, the occupied ragged frame's refusal, and the
vacant-membered frame's fold-branch record. -/
set_option maxHeartbeats 4000000

open ground poly elim genericlift

private def u : BPair := BPair.unit

/-! Clause (i): the pairs `[t² + t : t + 1]` and `[t : 1]`. -/

private def xP : PPair := ([u, ⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩])
private def yP : PPair := ([u, ⟨2, 1⟩], [⟨2, 1⟩])

example : agreeAt xP yP ⟨3, 1⟩ := by decide +kernel
example : crossNull xP yP := by decide +kernel
example : liftRead xP yP [⟨2, 1⟩, ⟨3, 1⟩, ⟨4, 1⟩] := by decide +kernel
example : crossNull ([⟨1, 2⟩, u, ⟨2, 1⟩], [⟨1, 2⟩, ⟨2, 1⟩])
    ([⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩]) := by decide +kernel
example : ¬ crossNull yP ([⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩]) := by decide +kernel
example : ¬ liftRead yP ([⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩])
    [⟨2, 1⟩, ⟨3, 1⟩, ⟨4, 1⟩] := by decide +kernel
example : ¬ pairwiseApart [⟨2, 1⟩, ⟨3, 2⟩] := by decide +kernel

/-! Clause (ii): the adjugate's solved witness at the two
pencils. -/

private def m2 : split.PMat :=
  [[[u, ⟨2, 1⟩], [⟨2, 1⟩]], [[⟨2, 1⟩], [u, ⟨2, 1⟩]]]
private def m3 : split.PMat :=
  [[[u, ⟨2, 1⟩], [⟨2, 1⟩], []],
   [[⟨2, 1⟩], [u, ⟨2, 1⟩], [⟨2, 1⟩]],
   [[], [⟨2, 1⟩], [u, ⟨2, 1⟩]]]

example : adjRead m2 := by decide +kernel
example : detOcc m2 := by decide +kernel
example : adjRead m3 := by decide +kernel
example : detOcc m3 := by decide +kernel

/-! The solved witness through its theorem route at the square
frame, both product orders. -/

example : adjRead m2 := adjRead_all m2 (by decide +kernel)

example : split.pmatOneValue (split.pmatMul (padj m2) m2)
    (split.pdiag (List.replicate m2.length (split.pminor m2))) :=
  adjColRead_all m2 (by decide +kernel)

example : split.pmatOneValue (split.pmatMul (padj m3) m3)
    (split.pdiag (List.replicate m3.length (split.pminor m3))) := by
  decide +kernel

/-! The descent's adjugate against the fold's at the value, decided
and read through the theorem's route at the decided square frame. -/

example : split.pmatOneValue (padjD m3) (padj m3) := by decide +kernel
example : split.pmatOneValue (padjD m2) (padj m2) :=
  padjD_eq m2 (by decide +kernel)

/-! The square binder isolated at a ragged frame, and the settled
side's reads at the value's representative — a tail of
equal-membered coefficients moves the representative with both
reads held. -/

private def ragP3 : split.PMat :=
  [[[⟨2, 1⟩], [⟨1, 2⟩], [⟨3, 1⟩]],
   [[⟨1, 3⟩], [⟨5, 1⟩]],
   [[⟨2, 1⟩], [⟨2, 1⟩], [⟨1, 2⟩]]]

example : ¬ split.pmatOneValue (padjD ragP3) (padj ragP3) := by
  decide +kernel

/-- The solved witness at the ragged frames: `ragP3`'s missing entry
sits beyond the walked keys, so the identity reads anyway and the
square binder is a clearance there; at the wide first row the
out-of-range column carries no cofactor and both product orders
refuse, the binder load-bearing. -/
example : adjRead ragP3 := by decide +kernel

example : split.pmatOneValue (split.pmatMul (padj ragP3) ragP3)
    (split.pdiag (List.replicate ragP3.length
      (split.pminor ragP3))) := by decide +kernel

private def ragWide : split.PMat :=
  [[poly.one, poly.one, poly.one], [poly.one]]

example : ¬ adjRead ragWide := by decide +kernel

example : ¬ split.pmatOneValue (split.pmatMul (padj ragWide) ragWide)
    (split.pdiag (List.replicate ragWide.length
      (split.pminor ragWide))) := by decide +kernel

example : topUpper [⟨3, 1⟩, ⟨2, 1⟩, ⟨5, 5⟩] := by decide +kernel
example : topLower [⟨2, 1⟩, ⟨1, 2⟩, ⟨4, 4⟩] := by decide +kernel
example : poly.oneValue (split.pminor m3)
    [u, ⟨1, 3⟩, u, ⟨2, 1⟩] := by decide +kernel

/-! Clause (iii): the radius clearances, the settled sides, and the
beyond-radius evaluation pins. -/

example : radiusClears [⟨3, 1⟩, ⟨2, 1⟩] 3 := by decide +kernel
example : ¬ radiusClears [⟨3, 1⟩, ⟨2, 1⟩] 2 := by decide +kernel
example : topUpper [⟨3, 1⟩, ⟨2, 1⟩] := by decide +kernel
example : BPair.unit < poly.eval [⟨3, 1⟩, ⟨2, 1⟩] ⟨4, 1⟩ := by decide +kernel
example : clearsPair ([⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩], [⟨3, 1⟩, ⟨2, 1⟩])
    4 := by decide +kernel
example : topUpper [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] := by decide +kernel
example : topLower [⟨2, 1⟩, ⟨1, 2⟩] := by decide +kernel
example : poly.eval [⟨2, 1⟩, ⟨1, 2⟩] ⟨5, 1⟩ < BPair.unit := by decide +kernel

/-! Clause (iii)'s side theorem at `lem:rankstable`'s own
polynomial data and at two small literals.  The θ family's `2 z²`
(`casPoly [1] [1]`) clears at the argument two and reads strictly
above the sum's unit at every argument beyond, the route run
through the theorem beside its own decided pin; the dimension
denominator's `z - 1` (`dimDen [1] [1]`) carries the same trio, and
the two-place dimension numerator's top is upper at a radius past
the batteries' reach (the decided top alone).  The literal
`2 - 3 z` carries a lower top with the lower route.  The literal
`z - 5` is the clearance binder's load-bearing record: at the
argument one — below its radius five — the evaluation sits on the
OPPOSITE side and the clearance refuses, while at the cleared
argument five the theorem's own side returns. -/

private def casQ : Poly := rankstable.casPoly [1] [1]
private def denQ : Poly := rankstable.dimDen [1] [1]
private def numQ : Poly := rankstable.dimNum [0, 1] [0, 1]
private def lowQ : Poly := [⟨3, 1⟩, ⟨1, 4⟩]
private def offQ : Poly := [⟨1, 6⟩, ⟨2, 1⟩]

example : topUpper casQ := by decide +kernel
example : radiusClears casQ (ground.posOfSucc 2) := by decide +kernel
example : ¬ radiusClears casQ (ground.posOfSucc 0) := by decide +kernel
example : BPair.unit < poly.eval casQ (BPair.ofPos (ground.posOfSucc 5)) := by
  decide +kernel
example : BPair.unit < poly.eval casQ (BPair.ofPos (ground.posOfSucc 5)) :=
  sideUpper casQ (ground.posOfSucc 2) (by decide +kernel) (by decide +kernel)
    (ground.posOfSucc 5) (by decide +kernel)

example : topUpper denQ := by decide +kernel
example : radiusClears denQ (ground.posOfSucc 1) := by decide +kernel
example : BPair.unit < poly.eval denQ (BPair.ofPos (ground.posOfSucc 3)) := by
  decide +kernel
example : BPair.unit < poly.eval denQ (BPair.ofPos (ground.posOfSucc 3)) :=
  sideUpper denQ (ground.posOfSucc 1) (by decide +kernel) (by decide +kernel)
    (ground.posOfSucc 3) (by decide +kernel)

example : topUpper numQ := by decide +kernel

example : topLower lowQ := by decide +kernel
example : radiusClears lowQ (ground.posOfSucc 1) := by decide +kernel
example : poly.eval lowQ (BPair.ofPos (ground.posOfSucc 4)) < BPair.unit := by
  decide +kernel
example : poly.eval lowQ (BPair.ofPos (ground.posOfSucc 4)) < BPair.unit :=
  sideLower lowQ (ground.posOfSucc 1) (by decide +kernel) (by decide +kernel)
    (ground.posOfSucc 4) (by decide +kernel)

example : topUpper offQ := by decide +kernel
example : poly.eval offQ (BPair.ofPos (ground.posOfSucc 1)) < BPair.unit := by
  decide +kernel
example : ¬ radiusClears offQ (ground.posOfSucc 1) := by decide +kernel
example : radiusClears offQ (ground.posOfSucc 5) := by decide +kernel
example : BPair.unit < poly.eval offQ (BPair.ofPos (ground.posOfSucc 6)) := by
  decide +kernel
example : BPair.unit < poly.eval offQ (BPair.ofPos (ground.posOfSucc 6)) :=
  sideUpper offQ (ground.posOfSucc 5) (by decide +kernel) (by decide +kernel)
    (ground.posOfSucc 6) (by decide +kernel)


/-! Clause (iii)'s side theorem at `lem:serstable`'s own
polynomial data, the rank the coordinate.  The `B` Casimir
numerator at the word `[2, 1]` is `6 z` — the word's doubled total
against its cleared square fold, the two coefficients equal-membered
at the constant — and clears at the argument two, reading strictly
above the sum's unit at every argument beyond, the route run
through the theorem beside its own decided pin with the argument
one below the radius refused.  The `C` dimension pair at the word
`[2]` carries the same trio at the radius five, both members'
tops upper.  The negated Casimir carries the lower top with the
lower route.  The `D` Casimir numerator at the word `[1, 1, 1, 1]`
is `8 z - 16`, the clearance binder's load-bearing record: at the
argument one — below its radius three — the evaluation sits on the
OPPOSITE side and the clearance refuses, while at the cleared
argument the theorem's own side returns. -/

private def casSB : Poly := serstable.casPolyB [2, 1]
private def numSC : Poly := serstable.dimPolyNumC [2]
private def denSC : Poly := serstable.dimPolyDenC [2]
private def offSD : Poly := serstable.casPolyD [1, 1, 1, 1]

example : topUpper casSB := by decide +kernel
example : radiusClears casSB (ground.posOfSucc 1) := by decide +kernel
example : ¬ radiusClears casSB (ground.posOfSucc 0) := by decide +kernel
example : BPair.unit < poly.eval casSB (BPair.ofPos (ground.posOfSucc 4)) := by
  decide +kernel
example : BPair.unit < poly.eval casSB (BPair.ofPos (ground.posOfSucc 4)) :=
  sideUpper casSB (ground.posOfSucc 1) (by decide +kernel) (by decide +kernel)
    (ground.posOfSucc 4) (by decide +kernel)

example : topUpper numSC := by decide +kernel
example : radiusClears numSC (ground.posOfSucc 4) := by decide +kernel
example : ¬ radiusClears numSC (ground.posOfSucc 3) := by decide +kernel
example : BPair.unit < poly.eval numSC (BPair.ofPos (ground.posOfSucc 6)) := by
  decide +kernel
example : BPair.unit < poly.eval numSC (BPair.ofPos (ground.posOfSucc 6)) :=
  sideUpper numSC (ground.posOfSucc 4) (by decide +kernel) (by decide +kernel)
    (ground.posOfSucc 6) (by decide +kernel)

example : topUpper denSC := by decide +kernel
example : radiusClears denSC (ground.posOfSucc 4) := by decide +kernel
example : BPair.unit < poly.eval denSC (BPair.ofPos (ground.posOfSucc 6)) :=
  sideUpper denSC (ground.posOfSucc 4) (by decide +kernel) (by decide +kernel)
    (ground.posOfSucc 6) (by decide +kernel)

example : topLower (poly.neg casSB) := by decide +kernel
example : radiusClears (poly.neg casSB) (ground.posOfSucc 1) := by decide +kernel
example : poly.eval (poly.neg casSB) (BPair.ofPos (ground.posOfSucc 4))
    < BPair.unit := by decide +kernel
example : poly.eval (poly.neg casSB) (BPair.ofPos (ground.posOfSucc 4))
    < BPair.unit :=
  sideLower (poly.neg casSB) (ground.posOfSucc 1) (by decide +kernel) (by decide +kernel)
    (ground.posOfSucc 4) (by decide +kernel)

example : topUpper offSD := by decide +kernel
example : poly.eval offSD (BPair.ofPos (ground.posOfSucc 0)) < BPair.unit := by
  decide +kernel
example : ¬ radiusClears offSD (ground.posOfSucc 1) := by decide +kernel
example : radiusClears offSD (ground.posOfSucc 2) := by decide +kernel
example : BPair.unit < poly.eval offSD (BPair.ofPos (ground.posOfSucc 3)) := by
  decide +kernel
example : BPair.unit < poly.eval offSD (BPair.ofPos (ground.posOfSucc 3)) :=
  sideUpper offSD (ground.posOfSucc 2) (by decide +kernel) (by decide +kernel)
    (ground.posOfSucc 3) (by decide +kernel)

/-! Clause (iv)'s radii fold over the series' own three members. -/

example : clearsAll [casSB, numSC, denSC] (ground.posOfSucc 4) := by decide +kernel
example : ¬ clearsAll [casSB, numSC, denSC] (ground.posOfSucc 3) := by decide +kernel

/-! Clause (iv): the radii's fold over the stated members. -/

example : clearsAll
    [[⟨3, 1⟩, ⟨2, 1⟩], [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨1, 2⟩]]
    4 := by decide +kernel
example : ¬ clearsAll
    [[⟨3, 1⟩, ⟨2, 1⟩], [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨1, 2⟩]]
    2 := by decide +kernel

/-! Clause (ii) at the pair carrier: the pencil
`[[c_f, 1], [-1, d_f]]` at genuine denominators — the determinant
`[t² + 2t + 2 : 2]`, the adjugate's solved witness, the application
at the vector `(1, -1)` — and the solve again at a three-place
pencil off the triangle (the module's heaviest read), with the
length-strict refusal and the diagonal's
refusal off the determinant, the solve's own datum.  The pairs are
the Casimir `[t(t+2) : 2(t+1)]`, the negation `[-1 : 1]` and the
count `[t + 1 : 1]`, stated here rather than imported. -/

private def cfP : PPair := ([u, ⟨3, 1⟩, ⟨2, 1⟩], [⟨3, 1⟩, ⟨3, 1⟩])
private def negP : PPair := ([⟨1, 2⟩], [⟨2, 1⟩])
private def dfP : PPair := ([⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩])

private def pm2 : PPMat := [[cfP, pOne], [negP, dfP]]

example : crossNull (ppminor pm2)
    ([⟨3, 1⟩, ⟨3, 1⟩, ⟨2, 1⟩], [⟨3, 1⟩]) := by decide +kernel
example : ppadjRead pm2 := by decide +kernel
example : pprowEq (ppmatVec pm2 [pOne, negP])
    [([⟨1, 3⟩, u, ⟨2, 1⟩], [⟨3, 1⟩, ⟨3, 1⟩]),
     ([⟨1, 3⟩, ⟨1, 2⟩], [⟨2, 1⟩])] := by decide +kernel

private def pm3 : PPMat :=
  [[dfP, pOne, pZero], [pZero, dfP, negP], [negP, pZero, cfP]]

example : ppadjRead pm3 := by decide +kernel

example : ¬ ppmatEq [[pOne]] [] := by decide +kernel
example : ¬ ppmatEq (ppmatMul pm2 (ppadj pm2))
    (ppdiag (List.replicate 2 pOne)) := by decide +kernel

/-! The ragged reads, pinned: at an off-square input the fold's
out-of-range defaults annihilate the extra column and `ppadjRead`
holds vacuously, while a row-length mismatch refuses — the shape is
`ppSquare`'s read at the consumer, this pair the committed record. -/

example : ppadjRead [[pOne, pOne]] := by decide +kernel
example : ¬ ppadjRead [[pOne, pOne, pOne], [pOne]] := by decide +kernel

/-! The pair adjugate at the descent: the walk adjugate reads the
fold adjugate at the occupied square frame — the branch records,
the value pins with the theorem route, the occupied ragged frame's
refusal isolating the square binder, and the vacant-membered
square frame's record at the fold branch. -/

example : elim.matOcc pm2 = true := by decide +kernel
example : elim.matOcc pm3 = true := by decide +kernel
example : ppmatEq (ppadjD pm2) (ppadj pm2) := by decide +kernel
example : ppmatEq (ppadjD pm3) (ppadj pm3) := by decide +kernel
example : ppmatEq (ppadjD pm3) (ppadj pm3) :=
  ppadjD_eq pm3 (by decide +kernel)

private def rag3 : PPMat :=
  [[(poly.one, poly.one), ([⟨1, 3⟩], poly.one), negP],
   [([⟨2, 1⟩], [⟨3, 1⟩]), dfP],
   [cfP, pOne, dfP]]

example : elim.matOcc rag3 = true := by decide +kernel
example : ¬ ppmatEq (ppadjD rag3) (ppadj rag3) := by decide +kernel

private def vacPP : PPMat :=
  [[(poly.one, ([] : poly.Poly)), pOne], [pOne, pOne]]

example : elim.matOcc vacPP = false := by decide +kernel
example : ppadjRead vacPP := by decide +kernel

/-! The certified reduction and its bridge.  At the Casimir pair
the descent's tuple decides with a constant divisor, so the moved
representative is the pair outright; at a pair built on a common
factor (`(2z-1)(z+1)` against `(2z-1)(z+3)`) the tuple decides at
`2z - 1` and the members drop to the quotients cross-cleared —
their lengths the reduction's own evidence; at two vacant members
the tuple refuses and the pair itself is the value.  The bridge
`pReduce_read` is exhibited beside the decided reads on both
arms. -/

private def wR : Poly := [⟨1, 2⟩, ⟨3, 1⟩]
private def q1R : Poly := [⟨2, 1⟩, ⟨2, 1⟩]
private def q2R : Poly := [⟨4, 1⟩, ⟨2, 1⟩]
private def rPair : PPair := (poly.mul wR q1R, poly.mul wR q2R)
private def halfR : PPair := ([⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩])

example : crossNull (pReduce cfP) cfP := by decide +kernel
example : crossNull (pReduce cfP) cfP := pReduce_read cfP
example : pReduce cfP = cfP := by decide +kernel

example : crossNull (pReduce rPair) rPair := by decide +kernel
example : crossNull (pReduce rPair) (q1R, q2R) := by decide +kernel
example : (pReduce rPair).1.length = 2 := by decide +kernel
example : (pReduce rPair).2.length = 2 := by decide +kernel

example : crossNull (pReduce ([], [])) ([], []) := by decide +kernel
example : pReduce ([], []) = ([], []) := by decide +kernel
example : crossNull (pReduce ([], [])) ([], []) := pReduce_read ([], [])

/-! The second spelling: `1/(z+1)` added to itself reads
`2/(z+1)`, the doubled denominator's common factor stripped. -/

example : crossNull (pAddR halfR halfR) ([⟨3, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]) := by
  decide +kernel
example : (pAddR halfR halfR).1.length = 1 := by decide +kernel
example : (pAddR halfR halfR).2.length = 2 := by decide +kernel
example : crossNull (pAddR halfR halfR) (pAdd halfR halfR) :=
  pReduce_read (pAdd halfR halfR)

/-! The reduction at the recorded fold seam: `con:res`' step-1
deflation of `|tr U|²` off `χ_adj` reads its `[1, 0]` coefficient
at the true `[1 : d_f]` at one and two keys — the seams reduce in
place (`wg.pairFull`'s accumulator and `res.deflate1`'s
coefficient), so the unreduced thirty-one-key shape arises nowhere
on the tree; `MassGapChecks/Res.lean`'s docstring holds the
recorded before-and-after measurement.  The reduction is idempotent
at the reduced datum, the constant divisor's arm. -/

private def fAdjR : states.FList := [(false, false), (false, true)]
private def sqCR : states.Comb := [([0, 1], pOne)]
private def adjCR : states.Comb :=
  [([0, 1], pOne), ([1, 0], ([⟨1, 2⟩], [⟨2, 1⟩, ⟨2, 1⟩]))]
private def defR : PPair :=
  states.coeffAtW (res.deflate fAdjR [adjCR] sqCR) [1, 0]

example : defR.1.length = 1 := by decide +kernel
example : defR.2.length = 2 := by decide +kernel
example : crossNull (pReduce defR) defR := by decide +kernel
example : (pReduce defR).1.length = 1 := by decide +kernel
example : (pReduce defR).2.length = 2 := by decide +kernel
example : crossNull defR ([⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]) := by
  decide +kernel
