import MassGap.Row
import MassGap.Sertables
import MassGap.Xfusion
import MassGapChecks.Sertables
/-!
The check module for `prop:row`'s member reads: the batteries
re-read the tables by kernel `decide` at all twelve committed
members with the first table beside them — the support count (one
at every member off the `A`-series, two at the `A`-series at
`r ≥ 2` and one at its first member), pinned against the fast
fusion route at the shared `A`-instances (`xfusion.c1`, the
adjoint's multiplicity in its own square through `cor:steinberg`'s
fold, the two routes' one value the crown pattern); the dimension
fold at the displayed member formulas (`[(r+2)(r+3):2]` at `B` and
`D`, `r(2r+1)` at `C`, `r(r+2)` at the `A`-series, and
`14, 52, 78, 133, 248`); and the member join
`Σ_α ⟨α,α⟩ = ℓ(r+1)` at the displayed length folds (`2ℓ² - ℓ`,
`ℓ² + ℓ`, `2ℓ² - 2ℓ`, and `8, 36, 72, 126, 240`).  The `E_7` and `E_8`
length folds are the module's heavy pins, each one `formNum` fold over its
descent list.

The diagonal tier stands on the tie analysis's own data at `B_2`
and `G_2`: θ's coroot vector with its vacant support, the θ content
list at the adjoint dimension's own count (ten members at `B_2`,
fourteen at `G_2`), the tower keys `mθ + ρ` with their graded
orbits at `m = 1` and `m = 2`, and the `ρ`-orbit — `con:sertables`'
shared copy — at the vacuum's key.  `balanceValues` lands by the
theorem route at both `m`, every binder at kernel `decide` with the
computed twin beside it: the even count the coordinate count and
the odd count θ's vacant coroot support, the `m`-constancy live at
the second key.  `defectValues` lands at the vacuum with both
counts the coordinate count, and `diagRead` closes the display at
the one-member exhaustion, the diagonal's value θ's occupied coroot
support.  The `A`-series cross-pins read that value at
`cor:steinberg`'s fast count over the matched-degree shapes, at
`r = 1` and `r = 2` and at `m = 1` and `m = 2`, the vacuum's own
count nought beside them.  The forge tier carries one committed
refusal per load-bearing binder, and the binder classification
sits at its head.
-/
set_option maxHeartbeats 4000000

open ground gentable sertables row

/-! The support count: one at every member off the `A`-series. -/

example : supportCount (tableB 2) = 1 := by decide +kernel
example : supportCount (tableB 3) = 1 := by decide +kernel
example : supportCount (tableB 4) = 1 := by decide +kernel
example : supportCount (tableC 3) = 1 := by decide +kernel
example : supportCount (tableC 4) = 1 := by decide +kernel
example : supportCount (tableD 4) = 1 := by decide +kernel
example : supportCount (tableD 5) = 1 := by decide +kernel
example : supportCount tableG2 = 1 := by decide +kernel
example : supportCount tableF4 = 1 := by decide +kernel
example : supportCount tableE6 = 1 := by decide +kernel
example : supportCount tableE7 = 1 := by decide +kernel
example : supportCount tableE8 = 1 := by decide +kernel

/-! The `A`-series: two at `r ≥ 2`, one at the first member. -/

example : supportCount (tableA 1) = 1 := by decide +kernel
example : supportCount (tableA 2) = 2 := by decide +kernel
example : supportCount (tableA 3) = 2 := by decide +kernel
example : supportCount (tableA 5) = 2 := by decide +kernel

/-! The two routes' one value at the shared instances: the fast
fusion count against the support count, the crown pattern. -/

example : xfusion.c1 2 = supportCount (tableA 1) := by decide +kernel
example : xfusion.c1 3 = supportCount (tableA 2) := by decide +kernel
example : xfusion.c1 4 = supportCount (tableA 3) := by decide +kernel
example : xfusion.c1 6 = supportCount (tableA 5) := by decide +kernel

/-! The dimension fold at the displayed member formulas. -/

example : 2 * dTheta (tableB 2)
    = (residue (tableB 2) + 2) * (residue (tableB 2) + 3) := by decide +kernel
example : 2 * dTheta (tableB 3)
    = (residue (tableB 3) + 2) * (residue (tableB 3) + 3) := by decide +kernel
example : 2 * dTheta (tableB 4)
    = (residue (tableB 4) + 2) * (residue (tableB 4) + 3) := by decide +kernel
example : dTheta (tableC 3)
    = residue (tableC 3) * (2 * residue (tableC 3) + 1) := by decide +kernel
example : dTheta (tableC 4)
    = residue (tableC 4) * (2 * residue (tableC 4) + 1) := by decide +kernel
example : 2 * dTheta (tableD 4)
    = (residue (tableD 4) + 2) * (residue (tableD 4) + 3) := by decide +kernel
example : 2 * dTheta (tableD 5)
    = (residue (tableD 5) + 2) * (residue (tableD 5) + 3) := by decide +kernel
example : dTheta (tableA 4)
    = residue (tableA 4) * (residue (tableA 4) + 2) := by decide +kernel
example : dTheta tableG2 = 14 := by decide +kernel
example : dTheta tableF4 = 52 := by decide +kernel
example : dTheta tableE6 = 78 := by decide +kernel
example : dTheta tableE7 = 133 := by decide +kernel
example : dTheta tableE8 = 248 := by decide +kernel

/-! The dimension fold against `cor:weyldim`'s gap-product route
at the shared `A`-instances, the adjoint's reduced shape. -/

example : weyldim.dimOf (adjchar.theta 3) = dTheta (tableA 2) := by decide +kernel
example : weyldim.dimOf (adjchar.theta 4) = dTheta (tableA 3) := by decide +kernel

/-! The member join `Σ_α ⟨α,α⟩ = ℓ(r+1)` at the displayed length
folds, the `E_7` and `E_8` reads the module's heavy pins. -/

example : lenFoldRead (tableB 2) 6 := by decide +kernel
example : lenFoldRead (tableB 3) 15 := by decide +kernel
example : lenFoldRead (tableB 4) 28 := by decide +kernel
example : lenFoldRead (tableC 3) 12 := by decide +kernel
example : lenFoldRead (tableC 4) 20 := by decide +kernel
example : lenFoldRead (tableD 4) 24 := by decide +kernel
example : lenFoldRead (tableD 5) 40 := by decide +kernel
example : lenFoldRead tableG2 8 := by decide +kernel
example : lenFoldRead tableF4 36 := by decide +kernel
example : lenFoldRead tableE6 72 := by decide +kernel

set_option maxHeartbeats 16000000 in
example : lenFoldRead tableE7 126 := by decide +kernel

set_option maxHeartbeats 16000000 in
example : lenFoldRead tableE8 240 := by decide +kernel

/-! The diagonal tier's data at `B_2` and `G_2`: the θ content list
at the adjoint dimension's own count — the vacant content at the
coordinate count, the positive members' coroot vectors and their
balance partners at one each — and the tower keys' graded orbits,
the free eight-member orbits of `mθ + ρ` at their letter-count
parities.  The vacuum's orbit is `con:sertables`' shared `ρ`-orbit
`wB2`, the vacuum key `κ_0 = ρ` its own first member; the vacant
content is the shared `zeroV`. -/

private def thFamB2 : List (List BPair) :=
  [zeroV, zeroV,
   [BPair.ofNat 2, (BPair.ofNat 2).swap],
   [BPair.unit, BPair.ofNat 2],
   [BPair.ofNat 1, BPair.unit],
   [(BPair.ofNat 1).swap, BPair.ofNat 2],
   [(BPair.ofNat 2).swap, BPair.ofNat 2],
   [BPair.unit, (BPair.ofNat 2).swap],
   [(BPair.ofNat 1).swap, BPair.unit],
   [BPair.ofNat 1, (BPair.ofNat 2).swap]]

private def thFamG2 : List (List BPair) :=
  [zeroV, zeroV,
   [BPair.ofNat 2, (BPair.ofNat 1).swap],
   [(BPair.ofNat 3).swap, BPair.ofNat 2],
   [(BPair.ofNat 1).swap, BPair.ofNat 1],
   [BPair.ofNat 1, BPair.unit],
   [BPair.ofNat 3, (BPair.ofNat 1).swap],
   [BPair.unit, BPair.ofNat 1],
   [(BPair.ofNat 2).swap, BPair.ofNat 1],
   [BPair.ofNat 3, (BPair.ofNat 2).swap],
   [BPair.ofNat 1, (BPair.ofNat 1).swap],
   [(BPair.ofNat 1).swap, BPair.unit],
   [(BPair.ofNat 3).swap, BPair.ofNat 1],
   [BPair.unit, (BPair.ofNat 1).swap]]

private def wKap1B2 : List (List BPair × Bool) :=
  [([BPair.ofNat 1, BPair.ofNat 3], false),
   ([(BPair.ofNat 1).swap, BPair.ofNat 5], true),
   ([BPair.ofNat 4, (BPair.ofNat 3).swap], true),
   ([BPair.ofNat 4, (BPair.ofNat 5).swap], false),
   ([(BPair.ofNat 4).swap, BPair.ofNat 5], false),
   ([(BPair.ofNat 4).swap, BPair.ofNat 3], true),
   ([BPair.ofNat 1, (BPair.ofNat 5).swap], true),
   ([(BPair.ofNat 1).swap, (BPair.ofNat 3).swap], false)]

private def wKap2B2 : List (List BPair × Bool) :=
  [([BPair.ofNat 1, BPair.ofNat 5], false),
   ([(BPair.ofNat 1).swap, BPair.ofNat 7], true),
   ([BPair.ofNat 6, (BPair.ofNat 5).swap], true),
   ([BPair.ofNat 6, (BPair.ofNat 7).swap], false),
   ([(BPair.ofNat 6).swap, BPair.ofNat 7], false),
   ([(BPair.ofNat 6).swap, BPair.ofNat 5], true),
   ([BPair.ofNat 1, (BPair.ofNat 7).swap], true),
   ([(BPair.ofNat 1).swap, (BPair.ofNat 5).swap], false)]

private def cVsB2 : List (List BPair) := [[BPair.unit, BPair.ofNat 2]]

/-! The tie analysis's value pins: θ's vacant coroot support at both
members, the complement join `N^{mθ}_{θ,mθ} + z = ℓ` beside it, and
the adjoint dimension against the θ content list's own count.  The
occupied support and the length folds stand at the member tier's
pins above, the diagonal tier reading them where they sit. -/

example : zCount tB2 = 1 := by decide +kernel
example : zCount tableG2 = 1 := by decide +kernel
example : supportCount tB2 + zCount tB2 = tB2.rank := by decide +kernel
example : supportCount tableG2 + zCount tableG2 = tableG2.rank := by
  decide +kernel
example : dTheta tB2 = 10 := by decide +kernel
example : dTheta tB2 = thFamB2.length := by decide +kernel
example : dTheta tableG2 = thFamG2.length := by decide +kernel
example : cVsB2
    = [poly.pnorm (elim.vecScale (BPair.ofNat 1) (thetaV tB2))] := by
  decide +kernel

/-! The reads' liveness at the stated data: the θ content list's
three clauses with the matched-list carrier at both members, the
ρ-length read at both members, θ's own dominance, and the orbit's
shape, closure and top reads with the tie's kept square at each of
the three tower keys. -/

example : thetaFamRead tB2 thFamB2 := by decide +kernel
example : memberchar.mShapeRead tB2 thFamB2 := by decide +kernel
example : thetaFamRead tableG2 thFamG2 := by decide +kernel
example : memberchar.mShapeRead tableG2 thFamG2 := by decide +kernel
example : rhoLenRead tB2 fundB2 := by decide +kernel
example : rhoLenRead tableG2 fundG2 := by decide +kernel
example : memberchar.lamRead tB2 (thetaV tB2) := by decide +kernel
example : memberchar.lamRead tableG2 (thetaV tableG2) := by decide +kernel

example : wShapeRead tB2 wKap1B2 := by decide +kernel
example : assembly.wCloseRead tB2 wKap1B2 := by decide +kernel
example : assembly.wTopAt wKap1B2 (kappaV tB2 1) := by decide +kernel
example : sqAtRead fundB2 wKap1B2 (kappaV tB2 1) := by decide +kernel

example : wShapeRead tB2 wKap2B2 := by decide +kernel
example : assembly.wCloseRead tB2 wKap2B2 := by decide +kernel
example : assembly.wTopAt wKap2B2 (kappaV tB2 2) := by decide +kernel
example : sqAtRead fundB2 wKap2B2 (kappaV tB2 2) := by decide +kernel

example : wShapeRead tB2 wB2 := by decide +kernel
example : assembly.wCloseRead tB2 wB2 := by decide +kernel
example : assembly.wTopAt wB2 (kappaV tB2 0) := by decide +kernel
example : sqAtRead fundB2 wB2 (kappaV tB2 0) := by decide +kernel

/-! The core by the theorem route at `m = 1` and `m = 2`, every
binder at kernel `decide`, with the display's computed twin beside
each: the even count the coordinate count and the odd count θ's
vacant coroot support, one at both keys — the `m`-constancy the
second key's own read. -/

example : memberchar.convCount wKap1B2 thFamB2 (kappaV tB2 1) false
      = tB2.rank
    ∧ memberchar.convCount wKap1B2 thFamB2 (kappaV tB2 1) true
      = zCount tB2 :=
  balanceValues tB2 fundB2 wKap1B2 thFamB2 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : memberchar.convCount wKap1B2 thFamB2 (kappaV tB2 1) false = 2
    ∧ memberchar.convCount wKap1B2 thFamB2 (kappaV tB2 1) true = 1 := by
  decide +kernel

example : memberchar.convCount wKap2B2 thFamB2 (kappaV tB2 2) false
      = tB2.rank
    ∧ memberchar.convCount wKap2B2 thFamB2 (kappaV tB2 2) true
      = zCount tB2 :=
  balanceValues tB2 fundB2 wKap2B2 thFamB2 2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : memberchar.convCount wKap2B2 thFamB2 (kappaV tB2 2) false = 2
    ∧ memberchar.convCount wKap2B2 thFamB2 (kappaV tB2 2) true = 1 := by
  decide +kernel

/-! The vacuum by the theorem route with its twin: both counts the
coordinate count, `prop:row`'s defect at the shared `ρ`-orbit. -/

example : memberchar.convCount wB2 thFamB2 (kappaV tB2 0) false
      = tB2.rank
    ∧ memberchar.convCount wB2 thFamB2 (kappaV tB2 0) true = tB2.rank :=
  defectValues tB2 fundB2 wB2 thFamB2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : memberchar.convCount wB2 thFamB2 (kappaV tB2 0) false = 2
    ∧ memberchar.convCount wB2 thFamB2 (kappaV tB2 0) true = 2 := by
  decide +kernel

/-! The display corollary at the minimal exhaustion — the one-member
channel list at `mθ`, its `memberAt` read the landed counts two and
one — with the computed twin beside it: the diagonal's value θ's
occupied coroot support. -/

example : ground.countOf
      (poly.pnorm (elim.vecScale (BPair.ofNat 1) (thetaV tB2))) cVsB2
    = supportCount tB2 :=
  diagRead tB2 fundB2 wKap1B2 thFamB2 cVsB2 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : steinberg.memberAt tB2 wKap1B2 thFamB2 cVsB2
    (poly.pnorm (elim.vecScale (BPair.ofNat 1) (thetaV tB2))) := by
  decide +kernel

example : ground.countOf
      (poly.pnorm (elim.vecScale (BPair.ofNat 1) (thetaV tB2))) cVsB2
    = 1 := by decide +kernel

/-! The `A`-series cross-pins at the fast fusion route: the
diagonal's value against `cor:steinberg`'s count over the
matched-degree shapes — the adjoint's reduced shape against `mθ`'s
at `m = 1` and `m = 2`, at `r = 1` and `r = 2` — and the vacuum's
count nought beside them, the display's own separation at the
tower's foot. -/

example : steinberg.count (adjchar.theta 2) (adjchar.theta 2) [2, 1]
    = supportCount (tableA 1) := by decide +kernel
example : steinberg.count (adjchar.theta 2) [4, 0] [4, 1]
    = supportCount (tableA 1) := by decide +kernel
example : steinberg.count (adjchar.theta 3) (adjchar.theta 3) [1, 1, 1]
    = supportCount (tableA 2) := by decide +kernel
example : steinberg.count (adjchar.theta 3) [2, 2, 0] [2, 2, 1]
    = supportCount (tableA 2) := by decide +kernel

example : steinberg.count (adjchar.theta 2) (List.replicate 2 0) [0, 1]
    = 0 := by decide +kernel
example : steinberg.count (adjchar.theta 3) (List.replicate 3 0) [0, 0, 1]
    = 0 := by decide +kernel

/-! The forge tier, and the binder classification of the three
publics' reads at this data.

`balanceValues` binds fifteen reads.  Six are the fundamental
data's — `fundShape`, `gramRead`, `gramSymRead`, `simplePosRead`,
`rhoDotRead` and `rhoLenRead` — and the conclusion binds no field of
`F`, so no fundamental-data forgery reaches it: they are pinned at
the stated members here and at `ChecksSertables`' coordinate tier,
their refusals that tier's committed forgeries (the forged Gram, the
forged simple position, the forged permutations).  `rhoLenRead`'s
isolating face rides the positive list, the table field the
conclusion reads through the θ-family alone: a member's fold
respelled off the root list parts the ρ-length cap — its second
clause the parting one, the square's read and the simples clause
standing — while every further binder survives at the matched
family and the odd count reads two off the vacant support.  The
Gram-box sweep stands beside it as its own record: over the
symmetric Grams at entries below seven and the scales one to
three, the Gram's defining read carries the ρ-length read outright
— the implication decided at every datum, the defining read itself
occupied at three of the box's thousand and twenty-nine data, the
genuine Gram at its three scales — so the Gram axis holds no
isolation and the positive-list axis is the read's own.

Two reads are the table's alone: `reflSquareRead` and the θ
vector's dominance, the one clause of the dominant-shape read the
derivation consumes — its length and norm conjuncts hypothesis-free
at the vector's own spelling, withdrawn from the binder.  Both are
pinned at `B_2` and `G_2` above, their refusals `con:sertables`'
own tier's.

The seven load-bearing binders carry their committed refusals here.
`thetaFamRead`'s three clauses each part at their own family and
each parts the conclusion: a third vacant content raises the even
count to three off the coordinate count; the qualifying simple's
positive vector withdrawn drops the odd count to nought off the
vacant support; and a content off the root list and the vacant
content — the tower key less a graded member of its own orbit —
gains a tie, the odd count reading two.  All three keep
`mShapeRead`, which is the isolation.  `wTopAt` refuses at the
doubled orbit, the shape, the closure and the kept square all
surviving at the doubled counts, and the conclusion parts on both
sides; the top entry's parity flipped refuses beside it, entangled
with the closure read, its own outcome recorded.  `wCloseRead`
refuses at the qualifying letter's image withdrawn, the shape, the
top and the kept square standing and the odd count at nought.
`sqAtRead` refuses at a stray orbit adjoined whole — the orbit of
the key joined to a positive member, at consistent parities, so the
shape, the closure and the top all stand — and the conclusion parts
at the gained tie, the even count reading three.  `1 ≤ m` is the
vacuum's own face: at `m = 0` the odd count reads the coordinate
count against the vacant support, `defectValues`' conclusion in
place of `balanceValues`', the two theorems' separation.

`wShapeRead` and `mShapeRead` are the matched-list carriers and
carry no isolating face: a member off the rank's order parts the
family read and the closure and kept-square reads with it, the
conclusion standing — both halves pinned below at the truncated
member, the parted reads and the standing counts alike.

`diagRead` binds those fifteen and `steinberg.memberAt` beside them:
the exhaustion read is the display's own hypothesis, refused at the
vacant channel list, where the count reads nought against the
occupied support.  `defectRead` reads the vacuum's display at the
same binders less the tower bound, the channel count the Kronecker
defect. -/

/-! `hfam`'s three faces, one per clause of the θ content list's
read: a third vacant content, the qualifying simple's positive
vector withdrawn, and a content off the root list and the vacant
content — the tower key less the graded member at the third orbit
entry.  Each keeps the matched-list carrier and parts the
conclusion. -/

private def thFamThird : List (List BPair) := thFamB2 ++ [zeroV]

example : ¬ thetaFamRead tB2 thFamThird := by decide +kernel
example : ground.countOf (List.replicate tB2.rank BPair.unit) thFamThird
    = 3 := by decide +kernel
example : memberchar.mShapeRead tB2 thFamThird := by decide +kernel
example : ¬ (memberchar.convCount wKap1B2 thFamThird (kappaV tB2 1) false
    = tB2.rank) := by decide +kernel

/-- The θ content list less the first positive member's coroot
vector, the qualifying simple's own at `B_2`. -/
private def thFamOffSimple : List (List BPair) :=
  [zeroV, zeroV,
   [BPair.unit, BPair.ofNat 2],
   [BPair.ofNat 1, BPair.unit],
   [(BPair.ofNat 1).swap, BPair.ofNat 2],
   [(BPair.ofNat 2).swap, BPair.ofNat 2],
   [BPair.unit, (BPair.ofNat 2).swap],
   [(BPair.ofNat 1).swap, BPair.unit],
   [BPair.ofNat 1, (BPair.ofNat 2).swap]]

example : ¬ thetaFamRead tB2 thFamOffSimple := by decide +kernel
example : ground.countOf (poly.pnorm (posCorootV tB2 0)) thFamOffSimple
    = 0 := by decide +kernel
example : memberchar.mShapeRead tB2 thFamOffSimple := by decide +kernel
example : ¬ (memberchar.convCount wKap1B2 thFamOffSimple (kappaV tB2 1)
    true = zCount tB2) := by decide +kernel

private def thFamTie : List (List BPair) :=
  thFamB2 ++ [[(BPair.ofNat 3).swap, BPair.ofNat 6]]

example : [(BPair.ofNat 3).swap, BPair.ofNat 6]
    = poly.pnorm (elim.vecAdd (kappaV tB2 1)
        (poly.neg [BPair.ofNat 4, (BPair.ofNat 3).swap])) := by decide +kernel
example : ¬ thetaFamRead tB2 thFamTie := by decide +kernel
example : memberchar.mShapeRead tB2 thFamTie := by decide +kernel
example : ¬ (memberchar.convCount wKap1B2 thFamTie (kappaV tB2 1) true
    = zCount tB2) := by decide +kernel

/-! `htop`'s isolating face at the doubled orbit, and the parity
flip's entangled refusal beside it. -/

private def wKapDbl : List (List BPair × Bool) := wKap1B2 ++ wKap1B2

example : ¬ assembly.wTopAt wKapDbl (kappaV tB2 1) := by decide +kernel
example : wShapeRead tB2 wKapDbl := by decide +kernel
example : assembly.wCloseRead tB2 wKapDbl := by decide +kernel
example : sqAtRead fundB2 wKapDbl (kappaV tB2 1) := by decide +kernel
example : ¬ (memberchar.convCount wKapDbl thFamB2 (kappaV tB2 1) false
    = tB2.rank) := by decide +kernel
example : ¬ (memberchar.convCount wKapDbl thFamB2 (kappaV tB2 1) true
    = zCount tB2) := by decide +kernel

private def wKapFlip : List (List BPair × Bool) :=
  ([BPair.ofNat 1, BPair.ofNat 3], true) :: wKap1B2.tail

example : ¬ assembly.wTopAt wKapFlip (kappaV tB2 1) := by decide +kernel
example : ¬ assembly.wCloseRead tB2 wKapFlip := by decide +kernel
example : wShapeRead tB2 wKapFlip := by decide +kernel
example : sqAtRead fundB2 wKapFlip (kappaV tB2 1) := by decide +kernel
example : ¬ (memberchar.convCount wKapFlip thFamB2 (kappaV tB2 1) false
    = tB2.rank) := by decide +kernel

/-! `hclose`'s face: the qualifying letter's image of the top
withdrawn from the orbit. -/

private def wKapDrop : List (List BPair × Bool) :=
  [([BPair.ofNat 1, BPair.ofNat 3], false),
   ([BPair.ofNat 4, (BPair.ofNat 3).swap], true),
   ([BPair.ofNat 4, (BPair.ofNat 5).swap], false),
   ([(BPair.ofNat 4).swap, BPair.ofNat 5], false),
   ([(BPair.ofNat 4).swap, BPair.ofNat 3], true),
   ([BPair.ofNat 1, (BPair.ofNat 5).swap], true),
   ([(BPair.ofNat 1).swap, (BPair.ofNat 3).swap], false)]

example : reflAt tB2 0 (kappaV tB2 1)
    = [(BPair.ofNat 1).swap, BPair.ofNat 5] := by decide +kernel
example : ¬ assembly.wCloseRead tB2 wKapDrop := by decide +kernel
example : wShapeRead tB2 wKapDrop := by decide +kernel
example : assembly.wTopAt wKapDrop (kappaV tB2 1) := by decide +kernel
example : sqAtRead fundB2 wKapDrop (kappaV tB2 1) := by decide +kernel
example : ¬ (memberchar.convCount wKapDrop thFamB2 (kappaV tB2 1) true
    = zCount tB2) := by decide +kernel

/-! `hksq`'s face: the orbit of the tower key joined to the third
positive member, adjoined whole at consistent parities. -/

private def wKapStray : List (List BPair × Bool) :=
  wKap1B2 ++
  [([BPair.ofNat 2, BPair.ofNat 3], false),
   ([(BPair.ofNat 2).swap, BPair.ofNat 7], true),
   ([BPair.ofNat 5, (BPair.ofNat 3).swap], true),
   ([BPair.ofNat 5, (BPair.ofNat 7).swap], false),
   ([(BPair.ofNat 5).swap, BPair.ofNat 7], false),
   ([(BPair.ofNat 5).swap, BPair.ofNat 3], true),
   ([BPair.ofNat 2, (BPair.ofNat 7).swap], true),
   ([(BPair.ofNat 2).swap, (BPair.ofNat 3).swap], false)]

example : [BPair.ofNat 2, BPair.ofNat 3]
    = poly.pnorm (elim.vecAdd (kappaV tB2 1)
        (poly.pnorm (posCorootV tB2 2))) := by decide +kernel
example : ¬ sqAtRead fundB2 wKapStray (kappaV tB2 1) := by decide +kernel
example : wShapeRead tB2 wKapStray := by decide +kernel
example : assembly.wCloseRead tB2 wKapStray := by decide +kernel
example : assembly.wTopAt wKapStray (kappaV tB2 1) := by decide +kernel
example : ¬ (memberchar.convCount wKapStray thFamB2 (kappaV tB2 1) false
    = tB2.rank) := by decide +kernel

/-! `hm`'s face: the vacuum's own key, where the odd count reads the
coordinate count against θ's vacant coroot support. -/

example : ¬ (memberchar.convCount wB2 thFamB2 (kappaV tB2 0) true
    = zCount tB2) := by decide +kernel

/-! The `hrho` records, two axes.  The Gram box: the symmetric
Grams at entries below seven and the scales one to three, at
`con:sertables`' own simple positions and permutations — the
Gram's defining read carries the ρ-length read over the whole box
(that read occupied at three of the thousand and twenty-nine
data), and the raised off-diagonal face parts the ρ-length read
with the shape, the symmetry and the ρ-dot positivity standing and
the Gram's defining read parting beside it: the Gram axis holds no
isolation.  The positive list is the isolating axis, below the
box. -/

private def gramAt (a b c s : Nat) : FundData :=
  ⟨[[BPair.ofNat a, BPair.ofNat b], [BPair.ofNat b, BPair.ofNat c]],
   s + 1, fundB2.simplePos, fundB2.perms⟩

example : ∀ a, a < 7 → ∀ b, b < 7 → ∀ c, c < 7 → ∀ s, s < 3 →
    gramRead tB2 (gramAt a b c s) → rhoLenRead tB2 (gramAt a b c s) := by
  decide +kernel

example : ¬ rhoLenRead tB2 (gramAt 2 2 1 0) := by decide +kernel
example : ¬ gramRead tB2 (gramAt 2 2 1 0) := by decide +kernel
example : fundShape tB2 (gramAt 2 2 1 0) := by decide +kernel
example : gramSymRead (gramAt 2 2 1 0) := by decide +kernel
example : rhoDotRead tB2 (gramAt 2 2 1 0) := by decide +kernel
example : gramRead tB2 (gramAt 2 1 1 0) := by decide +kernel
example : rhoLenRead tB2 (gramAt 2 1 1 0) := by decide +kernel

/-! The `hrho` isolating face, the positive-list axis: one member's
fold respelled off the root list parts the ρ-length cap — the
second clause alone, the square's read and the simples clause
standing — while every further binder survives at the matched
family, and the odd count reads two off the vacant support with
the even count standing at the coordinate count. -/

private def tF : Table :=
  { tB2 with posFolds := [[1, 0], [0, 3], [1, 1], [0, 1]] }

private def LF : List (List BPair) :=
  List.replicate tF.rank (List.replicate tF.rank BPair.unit)
    ++ (List.range tF.posFolds.length).flatMap (fun j =>
        [poly.pnorm (posCorootV tF j),
         poly.pnorm (poly.neg (posCorootV tF j))])

example : ¬ rhoLenRead tF fundB2 := by decide +kernel
example : ∀ j, j < tF.posFolds.length →
    BPair.unit ≤ dotB fundB2 (posCorootV tF j) (posCorootV tF j) := by
  decide +kernel
example : ∀ j, j < tF.posFolds.length →
    ((dotB fundB2 (posCorootV tF j) (rhoV tF)
        + dotB fundB2 (posCorootV tF j) (rhoV tF)).oneValue
      (dotB fundB2 (posCorootV tF j) (posCorootV tF j))
    → ∃ i, i + 1 < tF.rank + 1
        ∧ j = ground.getAt 0 fundB2.simplePos i) := by decide +kernel
example : fundShape tF fundB2 ∧ gramRead tF fundB2
    ∧ gramSymRead fundB2 ∧ reflSquareRead tF
    ∧ simplePosRead tF fundB2 ∧ rhoDotRead tF fundB2 := by decide +kernel
example : ∀ k, k < tF.rank →
    BPair.unit ≤ ground.getAt BPair.unit (thetaV tF) k := by decide +kernel
example : wShapeRead tF wKap1B2 ∧ assembly.wCloseRead tF wKap1B2
    ∧ assembly.wTopAt wKap1B2 (kappaV tF 1)
    ∧ sqAtRead fundB2 wKap1B2 (kappaV tF 1) := by decide +kernel
example : memberchar.mShapeRead tF LF ∧ thetaFamRead tF LF := by
  decide +kernel
example : memberchar.convCount wKap1B2 LF (kappaV tF 1) false
    = tF.rank := by decide +kernel
example : ¬ (memberchar.convCount wKap1B2 LF (kappaV tF 1) true
    = zCount tF) := by decide +kernel
example : memberchar.convCount wKap1B2 LF (kappaV tF 1) true = 2 := by
  decide +kernel

/-! The simples clause's own record: a duplicated simple fold parts
the third clause alone — the doubled ρ-dot's equality at a fold off
the stated positions — with the first two clauses, every further
binder and the conclusion all standing: refused without a break,
the clause the general table's own bound. -/

private def tFc3 : Table :=
  { tB2 with posFolds := tB2.posFolds ++ [[1, 0]] }

example : ¬ rhoLenRead tFc3 fundB2 := by decide +kernel
example : ∀ j, j < tFc3.posFolds.length →
    BPair.unit ≤ dotB fundB2 (posCorootV tFc3 j) (posCorootV tFc3 j)
    ∧ dotB fundB2 (posCorootV tFc3 j) (posCorootV tFc3 j)
      ≤ dotB fundB2 (posCorootV tFc3 j) (rhoV tFc3)
        + dotB fundB2 (posCorootV tFc3 j) (rhoV tFc3) := by decide +kernel
example : thetaFamRead tFc3 thFamB2 := by decide +kernel
example : memberchar.convCount wKap1B2 thFamB2 (kappaV tFc3 1) false
      = tFc3.rank
    ∧ memberchar.convCount wKap1B2 thFamB2 (kappaV tFc3 1) true
      = zCount tFc3 := by decide +kernel

/-! The matched-list carriers at the truncated member: the family
read and the closure and kept-square reads part together, the
conclusion standing — the shape reads' own no-isolation record. -/

private def thFamShort : List (List BPair) := thFamB2 ++ [[BPair.unit]]

example : ¬ memberchar.mShapeRead tB2 thFamShort := by decide +kernel
example : ¬ thetaFamRead tB2 thFamShort := by decide +kernel
example : memberchar.convCount wKap1B2 thFamShort (kappaV tB2 1) false
    = tB2.rank := by decide +kernel
example : memberchar.convCount wKap1B2 thFamShort (kappaV tB2 1) true
    = zCount tB2 := by decide +kernel

private def wKapShort : List (List BPair × Bool) :=
  wKap1B2 ++ [([BPair.unit], false)]

example : ¬ wShapeRead tB2 wKapShort := by decide +kernel
example : ¬ assembly.wCloseRead tB2 wKapShort := by decide +kernel
example : ¬ sqAtRead fundB2 wKapShort (kappaV tB2 1) := by decide +kernel
example : assembly.wTopAt wKapShort (kappaV tB2 1) := by decide +kernel
example : memberchar.convCount wKapShort thFamB2 (kappaV tB2 1) false
    = tB2.rank := by decide +kernel
example : memberchar.convCount wKapShort thFamB2 (kappaV tB2 1) true
    = zCount tB2 := by decide +kernel

/-! `diagRead`'s exhaustion at the vacant channel list: the display's
count reads nought against θ's occupied coroot support. -/

example : ¬ steinberg.memberAt tB2 wKap1B2 thFamB2 []
    (poly.pnorm (elim.vecScale (BPair.ofNat 1) (thetaV tB2))) := by decide +kernel
example : ¬ (ground.countOf
      (poly.pnorm (elim.vecScale (BPair.ofNat 1) (thetaV tB2)))
      ([] : List (List BPair)) = supportCount tB2) := by decide +kernel

/-! The vacuum's display at the vacant channel list: the defect's
member-side read, the channel count nought by the theorem route
with its twin. -/

example : ground.countOf
      (poly.pnorm (elim.vecScale (BPair.ofNat 0) (thetaV tB2)))
      ([] : List (List BPair)) = 0 :=
  defectRead tB2 fundB2 wB2 thFamB2 []
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : steinberg.memberAt tB2 wB2 thFamB2 []
    (poly.pnorm (elim.vecScale (BPair.ofNat 0) (thetaV tB2))) := by
  decide +kernel
