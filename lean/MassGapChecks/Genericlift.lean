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
`[[t,1,0],[1,t,1],[0,1,t]]` — the determinants `t² - 1` and
`t³ - 2t` occupied.  Clause (iii) at
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
vacant-membered frame's fold-branch record.  Clause (v) at three
members: `1 + ℓ + ℓ² − 2^ℓ`, whose computed natural is sixteen at
the start `4m² = 16` (the tail degree two) and whose settled side
is the lower one, with the root at nought and the upper side
through the rank four the window below the natural; `100 (1 + ℓ + ℓ²)
+ 2^ℓ`, whose comparison refuses at the start sixteen and holds at
seventeen, the computed natural past the start; and the tex's own
stencil caps, `3 · 2^ℓ` at `B_ℓ` and the even-rank `D_ℓ` cap
`3 (2ℓ + 2^{ℓ−1})` cleared at two.  The batteries decide the
computed naturals, the tail degree and fold, the leading margin's
positivity by kernel and through the theorem, the settled side by
kernel and through `expoUpper` and `expoLower`, the two closures by
kernel and through the theorems, the records' two certificates
with the clearance binder's refusal, the computed naturals' fold
with its refusal one below, and the outer representative: a fold
stated with a vacant top coefficient reads its data at the
representative's top.  The binder classification: `expoUpper` and
`expoLower` take the top's side (load-bearing: the fold `1 + ℓ + ℓ²
− 2^ℓ` refuses the upper top and its read at forty refuses the
upper side; the cap `3 · 2^ℓ` refuses the lower top and its read at
three refuses the lower side) and the natural at or beyond the
computed one (load-bearing, the conclusion refused at the rank four
below the natural sixteen); `expoRootsCert`'s clearance is
load-bearing (refused one below at the rank four's upper read) and
its floor and roots are the record's own data decided in the
certificate. -/

namespace genericlift
set_option maxHeartbeats 4000000

open ground poly elim

private def u : BPair := BPair.unit

/-! Clause (i): the pairs `[t² + t : t + 1]` and `[t : 1]`. -/

private def xP : PPair := ([u, ⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩])
private def yP : PPair := ([u, ⟨2, 1⟩], [⟨2, 1⟩])

theorem pin1 : agreeAt xP yP ⟨3, 1⟩ := by decide +kernel
theorem pin2 : crossNull xP yP := by decide +kernel
theorem pin3 : liftRead xP yP [⟨2, 1⟩, ⟨3, 1⟩, ⟨4, 1⟩] := by decide +kernel
theorem pin4 : crossNull ([⟨1, 2⟩, u, ⟨2, 1⟩], [⟨1, 2⟩, ⟨2, 1⟩])
    ([⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩]) := by decide +kernel
theorem pin5 : ¬ crossNull yP ([⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩]) := by decide +kernel
theorem pin6 : ¬ liftRead yP ([⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩])
    [⟨2, 1⟩, ⟨3, 1⟩, ⟨4, 1⟩] := by decide +kernel
theorem pin7 : ¬ pairwiseApart [⟨2, 1⟩, ⟨3, 2⟩] := by decide +kernel

private def m2 : split.PMat :=
  [[[u, ⟨2, 1⟩], [⟨2, 1⟩]], [[⟨2, 1⟩], [u, ⟨2, 1⟩]]]
private def m3 : split.PMat :=
  [[[u, ⟨2, 1⟩], [⟨2, 1⟩], []],
   [[⟨2, 1⟩], [u, ⟨2, 1⟩], [⟨2, 1⟩]],
   [[], [⟨2, 1⟩], [u, ⟨2, 1⟩]]]

theorem pin9 : detOcc m2 := by decide +kernel
theorem pin11 : detOcc m3 := by decide +kernel

theorem pin22 : topUpper [⟨3, 1⟩, ⟨2, 1⟩, ⟨5, 5⟩] := by decide +kernel
theorem pin23 : topLower [⟨2, 1⟩, ⟨1, 2⟩, ⟨4, 4⟩] := by decide +kernel
theorem pin24 : poly.oneValue (split.pminor m3)
    [u, ⟨1, 3⟩, u, ⟨2, 1⟩] := by decide +kernel

/-! Clause (iii): the radius clearances, the settled sides, and the
beyond-radius evaluation pins. -/

theorem pin25 : radiusClears [⟨3, 1⟩, ⟨2, 1⟩] 3 := by decide +kernel
theorem pin26 : ¬ radiusClears [⟨3, 1⟩, ⟨2, 1⟩] 2 := by decide +kernel
theorem pin27 : topUpper [⟨3, 1⟩, ⟨2, 1⟩] := by decide +kernel
theorem pin28 : BPair.unit < poly.eval [⟨3, 1⟩, ⟨2, 1⟩] ⟨4, 1⟩ := by decide +kernel
theorem pin29 : clearsPair ([⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩], [⟨3, 1⟩, ⟨2, 1⟩])
    4 := by decide +kernel
theorem pin30 : topUpper [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] := by decide +kernel
theorem pin31 : topLower [⟨2, 1⟩, ⟨1, 2⟩] := by decide +kernel
theorem pin32 : poly.eval [⟨2, 1⟩, ⟨1, 2⟩] ⟨5, 1⟩ < BPair.unit := by decide +kernel

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

theorem pin33 : topUpper casQ := by decide +kernel
theorem pin34 : radiusClears casQ (ground.posOfSucc 2) := by decide +kernel
theorem pin35 : ¬ radiusClears casQ (ground.posOfSucc 0) := by decide +kernel
theorem pin36 : BPair.unit < poly.eval casQ (BPair.ofPos (ground.posOfSucc 5)) := by
  decide +kernel
theorem pin37 : BPair.unit < poly.eval casQ (BPair.ofPos (ground.posOfSucc 5)) :=
  sideUpper casQ (ground.posOfSucc 2) (by decide +kernel) (by decide +kernel)
    (ground.posOfSucc 5) (by decide +kernel)

theorem pin38 : topUpper denQ := by decide +kernel
theorem pin39 : radiusClears denQ (ground.posOfSucc 1) := by decide +kernel
theorem pin40 : BPair.unit < poly.eval denQ (BPair.ofPos (ground.posOfSucc 3)) := by
  decide +kernel
theorem pin41 : BPair.unit < poly.eval denQ (BPair.ofPos (ground.posOfSucc 3)) :=
  sideUpper denQ (ground.posOfSucc 1) (by decide +kernel) (by decide +kernel)
    (ground.posOfSucc 3) (by decide +kernel)

theorem pin42 : topUpper numQ := by decide +kernel

theorem pin43 : topLower lowQ := by decide +kernel
theorem pin44 : radiusClears lowQ (ground.posOfSucc 1) := by decide +kernel
theorem pin45 : poly.eval lowQ (BPair.ofPos (ground.posOfSucc 4)) < BPair.unit := by
  decide +kernel
theorem pin46 : poly.eval lowQ (BPair.ofPos (ground.posOfSucc 4)) < BPair.unit :=
  sideLower lowQ (ground.posOfSucc 1) (by decide +kernel) (by decide +kernel)
    (ground.posOfSucc 4) (by decide +kernel)

theorem pin47 : topUpper offQ := by decide +kernel
theorem pin48 : poly.eval offQ (BPair.ofPos (ground.posOfSucc 1)) < BPair.unit := by
  decide +kernel
theorem pin49 : ¬ radiusClears offQ (ground.posOfSucc 1) := by decide +kernel
theorem pin50 : radiusClears offQ (ground.posOfSucc 5) := by decide +kernel
theorem pin51 : BPair.unit < poly.eval offQ (BPair.ofPos (ground.posOfSucc 6)) := by
  decide +kernel
theorem pin52 : BPair.unit < poly.eval offQ (BPair.ofPos (ground.posOfSucc 6)) :=
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

theorem pin53 : topUpper casSB := by decide +kernel
theorem pin54 : radiusClears casSB (ground.posOfSucc 1) := by decide +kernel
theorem pin55 : ¬ radiusClears casSB (ground.posOfSucc 0) := by decide +kernel
theorem pin56 : BPair.unit < poly.eval casSB (BPair.ofPos (ground.posOfSucc 4)) := by
  decide +kernel
theorem pin57 : BPair.unit < poly.eval casSB (BPair.ofPos (ground.posOfSucc 4)) :=
  sideUpper casSB (ground.posOfSucc 1) (by decide +kernel) (by decide +kernel)
    (ground.posOfSucc 4) (by decide +kernel)

theorem pin58 : topUpper numSC := by decide +kernel
theorem pin59 : radiusClears numSC (ground.posOfSucc 4) := by decide +kernel
theorem pin60 : ¬ radiusClears numSC (ground.posOfSucc 3) := by decide +kernel
theorem pin61 : BPair.unit < poly.eval numSC (BPair.ofPos (ground.posOfSucc 6)) := by
  decide +kernel
theorem pin62 : BPair.unit < poly.eval numSC (BPair.ofPos (ground.posOfSucc 6)) :=
  sideUpper numSC (ground.posOfSucc 4) (by decide +kernel) (by decide +kernel)
    (ground.posOfSucc 6) (by decide +kernel)

theorem pin63 : topUpper denSC := by decide +kernel
theorem pin64 : radiusClears denSC (ground.posOfSucc 4) := by decide +kernel
theorem pin65 : BPair.unit < poly.eval denSC (BPair.ofPos (ground.posOfSucc 6)) :=
  sideUpper denSC (ground.posOfSucc 4) (by decide +kernel) (by decide +kernel)
    (ground.posOfSucc 6) (by decide +kernel)

theorem pin66 : topLower (poly.neg casSB) := by decide +kernel
theorem pin67 : radiusClears (poly.neg casSB) (ground.posOfSucc 1) := by decide +kernel
theorem pin68 : poly.eval (poly.neg casSB) (BPair.ofPos (ground.posOfSucc 4))
    < BPair.unit := by decide +kernel
theorem pin69 : poly.eval (poly.neg casSB) (BPair.ofPos (ground.posOfSucc 4))
    < BPair.unit :=
  sideLower (poly.neg casSB) (ground.posOfSucc 1) (by decide +kernel) (by decide +kernel)
    (ground.posOfSucc 4) (by decide +kernel)

theorem pin70 : topUpper offSD := by decide +kernel
theorem pin71 : poly.eval offSD (BPair.ofPos (ground.posOfSucc 0)) < BPair.unit := by
  decide +kernel
theorem pin72 : ¬ radiusClears offSD (ground.posOfSucc 1) := by decide +kernel
theorem pin73 : radiusClears offSD (ground.posOfSucc 2) := by decide +kernel
theorem pin74 : BPair.unit < poly.eval offSD (BPair.ofPos (ground.posOfSucc 3)) := by
  decide +kernel
theorem pin75 : BPair.unit < poly.eval offSD (BPair.ofPos (ground.posOfSucc 3)) :=
  sideUpper offSD (ground.posOfSucc 2) (by decide +kernel) (by decide +kernel)
    (ground.posOfSucc 3) (by decide +kernel)

/-! Clause (iv)'s radii fold over the series' own three members. -/

theorem pin76 : clearsAll [casSB, numSC, denSC] (ground.posOfSucc 4) := by decide +kernel
theorem pin77 : ¬ clearsAll [casSB, numSC, denSC] (ground.posOfSucc 3) := by decide +kernel

/-! Clause (iv): the radii's fold over the stated members. -/

theorem pin78 : clearsAll
    [[⟨3, 1⟩, ⟨2, 1⟩], [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨1, 2⟩]]
    4 := by decide +kernel
theorem pin79 : ¬ clearsAll
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

theorem pin80 : crossNull (ppminor pm2)
    ([⟨3, 1⟩, ⟨3, 1⟩, ⟨2, 1⟩], [⟨3, 1⟩]) := by decide +kernel
theorem pin81 : ppadjRead pm2 := by decide +kernel
theorem pin82 : pprowEq (ppmatVec pm2 [pOne, negP])
    [([⟨1, 3⟩, u, ⟨2, 1⟩], [⟨3, 1⟩, ⟨3, 1⟩]),
     ([⟨1, 3⟩, ⟨1, 2⟩], [⟨2, 1⟩])] := by decide +kernel

private def pm3 : PPMat :=
  [[dfP, pOne, pZero], [pZero, dfP, negP], [negP, pZero, cfP]]

theorem pin83 : ppadjRead pm3 := by decide +kernel

theorem pin84 : ¬ ppmatEq [[pOne]] [] := by decide +kernel
theorem pin85 : ¬ ppmatEq (ppmatMul pm2 (ppadj pm2))
    (ppdiag (List.replicate 2 pOne)) := by decide +kernel

/-! The ragged reads, pinned: at an off-square input the fold's
out-of-range defaults annihilate the extra column and `ppadjRead`
holds vacuously, while a row-length mismatch refuses — the shape is
`ppSquare`'s read at the consumer, this pair the committed record. -/

theorem pin86 : ppadjRead [[pOne, pOne]] := by decide +kernel
theorem pin87 : ¬ ppadjRead [[pOne, pOne, pOne], [pOne]] := by decide +kernel

/-! The pair adjugate at the descent: the walk adjugate reads the
fold adjugate at the occupied square frame — the branch records,
the value pins with the theorem route, the occupied ragged frame's
refusal isolating the square binder, and the vacant-membered
square frame's record at the fold branch. -/

theorem pin88 : elim.matOcc pm2 = true := by decide +kernel
theorem pin89 : elim.matOcc pm3 = true := by decide +kernel
theorem pin90 : ppmatEq (ppadjD pm2) (ppadj pm2) := by decide +kernel
theorem pin91 : ppmatEq (ppadjD pm3) (ppadj pm3) := by decide +kernel
theorem pin92 : ppmatEq (ppadjD pm3) (ppadj pm3) :=
  ppadjD_eq pm3 (by decide +kernel)

private def rag3 : PPMat :=
  [[(poly.one, poly.one), ([⟨1, 3⟩], poly.one), negP],
   [([⟨2, 1⟩], [⟨3, 1⟩]), dfP],
   [cfP, pOne, dfP]]

theorem pin93 : elim.matOcc rag3 = true := by decide +kernel
theorem pin94 : ¬ ppmatEq (ppadjD rag3) (ppadj rag3) := by decide +kernel

private def vacPP : PPMat :=
  [[(poly.one, ([] : poly.Poly)), pOne], [pOne, pOne]]

theorem pin95 : elim.matOcc vacPP = false := by decide +kernel
theorem pin96 : ppadjRead vacPP := by decide +kernel

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

theorem pin97 : crossNull (pReduce cfP) cfP := by decide +kernel
theorem pin98 : crossNull (pReduce cfP) cfP := pReduce_read cfP
theorem pin99 : pReduce cfP = cfP := by decide +kernel

theorem pin100 : crossNull (pReduce rPair) rPair := by decide +kernel
theorem pin101 : crossNull (pReduce rPair) (q1R, q2R) := by decide +kernel
theorem pin102 : (pReduce rPair).1.length = 2 := by decide +kernel
theorem pin103 : (pReduce rPair).2.length = 2 := by decide +kernel

theorem pin104 : crossNull (pReduce ([], [])) ([], []) := by decide +kernel
theorem pin105 : pReduce ([], []) = ([], []) := by decide +kernel
theorem pin106 : crossNull (pReduce ([], [])) ([], []) := pReduce_read ([], [])

/-! The second spelling: `1/(z+1)` added to itself reads
`2/(z+1)`, the doubled denominator's common factor stripped. -/

theorem pin107 : crossNull (pAddR halfR halfR) ([⟨3, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]) := by
  decide +kernel
theorem pin108 : (pAddR halfR halfR).1.length = 1 := by decide +kernel
theorem pin109 : (pAddR halfR halfR).2.length = 2 := by decide +kernel
theorem pin110 : crossNull (pAddR halfR halfR) (pAdd halfR halfR) :=
  pReduce_read (pAdd halfR halfR)

/-! The reduction at the recorded fold seam: `con:res`' step-1
deflation of `|tr U|²` off `χ_adj` reads its `[1, 0]` coefficient
at the true `[1 : d_f]` at one and two keys — the seams reduce in
place (`wg.pairFull wg.evalPhi`'s accumulator and `res.deflate1`'s
coefficient), so the unreduced thirty-one-key shape arises nowhere
on the tree; `MassGapChecks/Res.lean`'s docstring holds the
recorded before-and-after measurement.  The reduction is idempotent
at the reduced datum, the constant divisor's arm. -/

private def fAdjR : states.FList := [(0, false), (0, true)]
private def sqCR : states.Comb := [([0, 1], pOne)]
private def adjCR : states.Comb :=
  [([0, 1], pOne), ([1, 0], ([⟨1, 2⟩], [⟨2, 1⟩, ⟨2, 1⟩]))]
private def defR : PPair :=
  states.coeffAtW (res.deflate fAdjR [adjCR] sqCR) [1, 0]

theorem pin111 : defR.1.length = 1 := by decide +kernel
theorem pin112 : defR.2.length = 2 := by decide +kernel
theorem pin113 : crossNull (pReduce defR) defR := by decide +kernel
theorem pin114 : (pReduce defR).1.length = 1 := by decide +kernel
theorem pin115 : (pReduce defR).2.length = 2 := by decide +kernel
theorem pin116 : crossNull defR ([⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]) := by
  decide +kernel

/-! Clause (v): the rank read at three members. -/

/-- `1 + ℓ + ℓ² − 2^ℓ`. -/
private def eA : PPoly := [[⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩], [⟨1, 2⟩]]
/-- `100 (1 + ℓ + ℓ²) + 2^ℓ`. -/
private def eB : PPoly := [[⟨101, 1⟩, ⟨101, 1⟩, ⟨101, 1⟩], [⟨2, 1⟩]]
/-- The `B_ℓ` stencil cap `3 · 2^ℓ`. -/
private def capB : PPoly := [[], [⟨4, 1⟩]]
/-- The even-rank `D_ℓ` stencil cap `3 (2ℓ + 2^{ℓ-1})` cleared at
two, `12 ℓ + 3 · 2^ℓ`. -/
private def capD : PPoly := [[u, ⟨13, 1⟩], [⟨4, 1⟩]]

theorem pin117 : expoTailDeg eA = 2 := by decide +kernel
theorem pin118 : (expoTailFold eA).oneValue (BPair.ofNat 3) := by decide +kernel
theorem pin119 : expoKey eA = 16 := by decide +kernel
theorem pin120 : expoKey eB = 17 := by decide +kernel
theorem pin121 : ¬ expoPred eB 16 := by decide +kernel
theorem pin122 : expoKey capB = 2 := by decide +kernel
theorem pin123 : expoKey capD = 5 := by decide +kernel
theorem pin124 : BPair.unit < windowsep.leadMargin [⟨1, 4⟩, ⟨2, 1⟩, ⟨3, 1⟩] := by
  decide +kernel
theorem pin125 : BPair.unit < windowsep.leadMargin [⟨1, 4⟩, ⟨2, 1⟩, ⟨3, 1⟩] :=
  windowsep.unitLt_leadMargin _ (by decide +kernel)
theorem pin126 : expoEval eA 16 < BPair.unit := by decide +kernel
theorem pin127 : ¬ (expoEval eA 4 < BPair.unit) := by decide +kernel
theorem pin128 : (expoEval eA 0).oneValue BPair.unit := by decide +kernel
theorem pin129 : expoEval eA 40 < BPair.unit :=
  expoLower eA (by decide +kernel) 40 (by decide +kernel)
theorem pin130 : BPair.unit < expoEval capB 3 :=
  expoUpper capB (by decide +kernel) 3 (by decide +kernel)
theorem pin131 : BPair.unit < expoEval eB 17 := by decide +kernel
theorem pin132 : (expoEval (padd eA eB) 5).oneValue (expoEval eA 5 + expoEval eB 5) := by
  decide +kernel
theorem pin133 : (expoEval (padd eA eB) 5).oneValue (expoEval eA 5 + expoEval eB 5) :=
  expoEval_padd eA eB 5
theorem pin134 : (expoEval (pmul eA capD) 3).oneValue (expoEval eA 3 * expoEval capD 3) := by
  decide +kernel
theorem pin135 : (expoEval (pmul eA capD) 3).oneValue (expoEval eA 3 * expoEval capD 3) :=
  expoEval_pmul eA capD 3
theorem pin136 : expoSideCert ⟨eA, 0, 5, [0]⟩ := by decide +kernel
theorem pin137 : ¬ expoSideCert ⟨[[u]], 0, 0, []⟩ := by decide +kernel
theorem pin138 : expoRootsCert ⟨eA, 0, 5, [0]⟩ := by decide +kernel
theorem pin139 : ¬ expoRootsCert ⟨eA, 0, 4, [0]⟩ := by decide +kernel
theorem pin140 : expoRootsCert ⟨capD, 4, 4, []⟩ := by decide +kernel
theorem pin141 : expoClearsAll [eA, eB, capB, capD] 17 := by decide +kernel
theorem pin142 : ¬ expoClearsAll [eA, eB, capB, capD] 16 := by decide +kernel
theorem pin143 : ¬ topUpper (expoTop eA) := by decide +kernel
theorem pin144 : ¬ (BPair.unit < expoEval eA 40) := by decide +kernel
theorem pin145 : ¬ topLower (expoTop capB) := by decide +kernel
theorem pin146 : ¬ (expoEval capB 3 < BPair.unit) := by decide +kernel
theorem pin147 : expoKey (eA ++ [[]]) = 16 := by decide +kernel
theorem pin148 : expoSideCert ⟨[[⟨2, 1⟩], [u]], 0, 0, []⟩ := by decide +kernel

end genericlift
