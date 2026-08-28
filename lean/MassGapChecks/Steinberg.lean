import MassGap.Steinberg
import MassGap.Adjchar
import MassGapChecks.Sertables
/-!
The check module for `cor:steinberg`: the batteries re-read the
alternating count by kernel `decide` — the sorted display against
the beta-set, the read's coherence with `def:blockcount`'s
kernel-dimension count at the su(2) scale and the su(3)
fundamentals with a mismatched-degree and an occupied-odd-sum
instance among them, and the walk's parameter through the fast
read at both channel regimes and the first generic residue:
`c_1 = 1` at `r = 1` and `c_1 = 2` at `r = 2` and `r = 3`, the
adjoint's own multiplicity in its square at the matched-degree
shape, the `r = 2` definitional value the `def:blockcount`
battery's crown pin.  The general theorem `readAll` enters at
five of the decided triples by its own route — the occupied odd
sum and the `r = 2` crown among them — with its two width binders
isolated beside it.  The member tier closes the module: the member
display applied whole at `B_2`'s spinor square, once per channel of
the exhaustion unit ⊕ vector ⊕ adjoint, with the product family's
own exhaustion clauses, the three channels' data at their eleven
reads, and one forge per load-bearing binder beside it.  The two
graded sums' parity-guarded split enters at the `su(2)` scale,
both sides decided beside the applied theorem, and the derived
identity `count_fusion` routes the fast count onto the
kernel-dimension count at the fundamental against the adjoint.
-/
set_option maxHeartbeats 4000000

open ground places sertables steinberg

/-! The sorted display `λ + u` as counts, the beta-set's own row
read. -/

example : display [1, 1, 0] = [5, 3, 1] := rfl
example : display [2, 0] = [4, 1] := rfl
example : betaSet [1, 1, 0]
    = (display [1, 1, 0]).map (fun x => posOfSucc (x - 1)) := by decide +kernel

/-! The read against the definitional count: the su(2) scale and
the su(3) fundamentals, a mismatched degree among them. -/

example : steinberg.read [2, 0] [2, 0] [4, 0] := by decide +kernel
example : steinberg.read [2, 0] [2, 0] [0, 2] := by decide +kernel
example : steinberg.read [2, 0] [2, 0] [2, 1] := by decide +kernel
example : steinberg.read [1, 0, 0] [1, 0, 0] [2, 0, 0] := by decide +kernel
example : steinberg.read [1, 0, 0] [1, 0, 0] [0, 1, 0] := by decide +kernel
example : steinberg.read [1, 0] [2, 0] [2, 0] := by decide +kernel

/-- A read at an occupied odd sum: the unit-shape factor's tie
admits the swap beside the identity, one multiplicity on each side,
the subtractive clause exercised at the definitional count. -/
example : steinberg.gradedSums [2, 0] [0, 0] [0, 1] = (1, 1) := by decide +kernel
example : steinberg.read [2, 0] [0, 0] [0, 1] := by decide +kernel

/-! `cor:steinberg`'s general theorem at the decided triples, the
theorem route beside each standing pin: the su(2) square's Cartan
and adjoint channels, an unequal factor pair, the occupied odd
sum, and the su(3) `r = 2` crown at its count two. -/

example : steinberg.read [2, 0] [2, 0] [4, 0] :=
  steinberg.readAll [2, 0] [2, 0] [4, 0] rfl rfl
example : steinberg.read [2, 0] [2, 0] [2, 1] :=
  steinberg.readAll [2, 0] [2, 0] [2, 1] rfl rfl
example : steinberg.read [1, 0] [2, 0] [2, 0] :=
  steinberg.readAll [1, 0] [2, 0] [2, 0] rfl rfl
example : steinberg.read [2, 0] [0, 0] [0, 1] :=
  steinberg.readAll [2, 0] [0, 0] [0, 1] rfl rfl
example : steinberg.read [1, 1, 0] [1, 1, 0] [1, 1, 1] :=
  steinberg.readAll [1, 1, 0] [1, 1, 0] [1, 1, 1] rfl rfl

/-- The theorem's two width binders isolated.  `hba` is
load-bearing: at the ragged second shape `[1]` the even sum reads
one against the count's own nought and the display parts.  `hca` is
the frame: at the narrow third shape `[1]` and at the wide
`[1, 1, 0]` both sums are vacant and the display stands, the
binder unrefusable in either direction.  Off matched degree at
the stated width the display stands too, both sums vacant with the
count at nought — the display is degree-blind, the width alone
`cor:steinberg`'s frame. -/
example : ¬ steinberg.read [1, 0] [1] [0, 0] := by decide +kernel
example : steinberg.read [1, 0] [1, 0] [1] := by decide +kernel
example : steinberg.read [1, 0] [1, 0] [1, 1, 0] := by decide +kernel
example : steinberg.read [1, 0] [1, 0] [0, 0] := by decide +kernel

/-! The fast values at the su(2) square, the reads' value halves. -/

example : steinberg.count [2, 0] [2, 0] [4, 0] = 1 := by decide +kernel
example : steinberg.count [2, 0] [2, 0] [0, 2] = 1 := by decide +kernel

/-- The walk's parameter at `r = 1` through the fast read: the
adjoint's multiplicity in its square at the matched-degree shape
reads one. -/
example : steinberg.count [2, 0] [2, 0] [2, 1] = 1 := by decide +kernel

/-- The walk's parameter at `r = 2`: the multiplicity reads two.
The definitional value at this triple is the `def:blockcount`
battery's crown pin; the two value pins together read the display
at the crown, the count's gap forcing the even side's clearance. -/
example : steinberg.count [1, 1, 0] [1, 1, 0] [1, 1, 1] = 2 := by decide +kernel

/-- The walk's parameter at `r = 3`, the first residue beyond the
channel degenerations: the multiplicity reads two at the generic
regime.  The cost is the su(4) adjoint span's, the multiplicity's
definitional route; the span exits this read at `lem:adjchar`'s
layer, the adjoint's contents explicit there. -/
example : steinberg.count [1, 0, 1, 0] [1, 0, 1, 0] [1, 0, 1, 1] = 2 := by
  decide +kernel

/-! The member tier's batteries at `B_2`, the spinor square.  The
two factors are one datum: the spinor top `ω₂`, whose coroot
coordinates are `(0, 1)`, at its four-member family — the weight
string `(0,1)`, `(1,-1)`, `(-1,1)`, `(0,-1)` read off the Cartan
rows `α_0 = (2,-2)` and `α_1 = (-1,2)`, each member once — and at
the free eight-member orbit of its shifted key `(1, 2)`.  The
square exhausts as unit ⊕ vector ⊕ adjoint at the tops `(0,0)`,
`(1,0)` and `(0,2)`, counts `1 + 5 + 10 = 4²`, every channel at
multiplicity one: the sixteen memberwise joins of the product
family carry `(0,0)` four times, `(1,0)`, `(-1,2)`, `(1,-2)` and
`(-1,0)` twice each, and `(0,2)`, `(0,-2)`, `(2,-2)`, `(-2,2)`
once, which is exactly the three channel families' fold at every
key.  The vector channel's family, its witnesses, its shifted
orbit at `(2,1)` and that orbit's witnesses are
`MassGapChecks/Memberchar.lean`'s committed literals copied under
this module's names, as are the `ρ`-alternant and its witnesses.

The binder classification of `memberRead`'s thirty reads at this
data.  Four are load-bearing at the conclusion, each with a
committed forge below.  `hexh1` and `hexh2` are the exhaustion, the
product family's count at every key against the channels' fold, and
they carry the tier's own asymmetry: the conclusion `memberAt` binds
the shifted alternant, the `a`-family and the channel tops and binds
no channel family at all, so a family-side forge refuses at the read
alone — forge 1 drops one unit content from the adjoint family and
both clauses part at the unit content's own key, four against three,
while the display at the adjoint top is untouched, and the drop
moves that channel's `recRead` with it (the family is the character,
so no family-side forge of this read is isolated, the entanglement
pinned rather than claimed away).  The read's conclusion-bearing
face is the channel side: forge 2 lists the vector channel twice
with its family, orbit and both witness lists copied beside it —
every per-channel read survives verbatim at the fourth index, the
exhaustion's fold double-counts at two against three, and the
display fails at the vector top where `countOf` reads two against
the convolution's gap one.  `hlL` is the channel-list length, the
theorem's fold running over `cVs.length` while the families are
read at `Ls`: forge 3 extends the tops by `2ω₁ = (2,0)` at three
families and the read parts, the display failing at that top, which
no family reaches — one channel count against two vacant
convolution counts.  `hcV` is the stated top's own frame: forge 4
carries an unnormed `(0,0)` — the sum of the natural one and its
swap — whose `lamRead` refuses at the normed conjunct and whose
display fails at `ρ`, the key its normed twin occupies, the count
vacant at the unnormed spelling against the unit channel's gap one;
the non-dominant `(-1,0)` and the short `(1)` are pinned beside it
at the read's other two conjuncts.

`hmsha` is the frame: the `a`-family's carrier convention, every
member at the rank's order and normed, the convolution's own
carrier read through `prodFam`'s memberwise joins.

The remaining twenty-five are inherited.  The nine table reads
(`fundShape`, `gramRead`, `gramSymRead`, `simplePosRead`,
`reflSquareRead`, `permSquareRead`, `permImageRead`, `rhoDotRead`,
`reflFormRead`) and the `W`-side four at `ρ`'s own alternant
(`wShapeRead`, `wCloseRead`, `wDomRead`, `wTopRead`) carry the walk
tier's committed refusals in `MassGapChecks/Assembly.lean` — the
forged witness at the top member, the adjoined reflection closure of
a regular dominant key, the flipped side, the doubled list, and the
forged side at the top member.  The `b`-cluster's six
(`mShapeRead`, `symRead`, `supportRead`, `topRead`, `lamRead`,
`recRead`), `Wb`'s five (`wShapeRead`, `wCloseRead`, `wDomAt`,
`wTopAt`, `wRegRead`) and the per-channel elevens are the conclusion
tier's own reads at `thm:memberchar`, one instance of that theorem's
binder list per factor and per channel, and their refusals are
`MassGapChecks/Memberchar.lean`'s committed batteries — the padded
alternant of the D2 refutation, the doubled top pair, the doubled
family, the dropped non-dominant member, the forged middle
multiplicity, the forged witness fold, the flipped even member, and
the orbit-padded family.

The data is multiplicity-one throughout, so the display reads
`countOf cV cVs = 1` against the convolution's gap one at every
channel top.  The multiplicity-discriminating face of `countOf` is
read outside this tier — at the fast count's own `r = 2` pin above,
where the walk's parameter reads two — and inside it at forge 2's
doubled channel, where the count reads two against the same gap one
and the display parts. -/

/-! The stated data: the two factors' tier and the three channels'
families, shifted orbits and witnesses, over the shared `B_2` data
at `MassGapChecks/Sertables.lean`. -/

private def spinB2 : List BPair := [BPair.unit, BPair.ofNat 1]
private def adjB2 : List BPair := [BPair.unit, BPair.ofNat 2]

/-- The shifted key of a stated top, the display's own argument. -/
private def shk (v : List BPair) : List BPair :=
  poly.pnorm (elim.vecAdd v (sertables.rhoV tB2))

/-! The spinor factor.  The family is the top's weight string, read
from `(0,1)` by the Cartan rows: `α_1` withdrawn gives `(1,-1)`,
then `α_0` gives `(-1,1)`, then `α_1` again gives `(0,-1)`, four
members once each, and each witness is the natural simple fold
carrying its member back to the top. -/

private def LspinB2 : List (List BPair) :=
  [[BPair.unit, BPair.ofNat 1],
   [BPair.ofNat 1, (BPair.ofNat 1).swap],
   [(BPair.ofNat 1).swap, BPair.ofNat 1],
   [BPair.unit, (BPair.ofNat 1).swap]]

private def witsSpinB2 : List (List Nat) := [[0, 0], [0, 1], [1, 1], [1, 2]]

/-! The spinor's shifted alternant at the key `(1,2)`, the regular
key's free orbit: the top at the even side, its two simple images
`(-1,4)` and `(3,-2)` odd, their crossed images `(3,-4)` and
`(-3,4)` even, `(-3,2)` and `(1,-4)` odd, and `(-1,-2)` even, the
side the reflection count's parity. -/

private def WspinB2 : List (List BPair × Bool) :=
  [([(BPair.ofNat 1), (BPair.ofNat 2)], false),
   ([(BPair.ofNat 1).swap, (BPair.ofNat 4)], true),
   ([(BPair.ofNat 3), (BPair.ofNat 2).swap], true),
   ([(BPair.ofNat 3), (BPair.ofNat 4).swap], false),
   ([(BPair.ofNat 3).swap, (BPair.ofNat 4)], false),
   ([(BPair.ofNat 3).swap, (BPair.ofNat 2)], true),
   ([(BPair.ofNat 1), (BPair.ofNat 4).swap], true),
   ([(BPair.ofNat 1).swap, (BPair.ofNat 2).swap], false)]

private def witsWspinB2 : List (List Nat) :=
  [[0, 0], [1, 0], [0, 2], [1, 4], [3, 2], [4, 4], [3, 6], [4, 6]]

/-! The unit channel: the one-member family at the unit content,
its shifted orbit `ρ`'s own alternant. -/

private def LunitB2 : List (List BPair) := [zeroV]
private def witsUnitB2 : List (List Nat) := [[0, 0]]

/-! The adjoint channel: the eight roots' coroot coordinates once
each — the four positive members `(0,2)`, `(1,0)`, `(2,-2)`,
`(-1,2)` of `posCorootV` and their negatives — with the unit
content twice at the rank, ten members, and the shifted orbit at
`(1,3)`. -/

private def LadjB2 : List (List BPair) :=
  [[BPair.unit, BPair.ofNat 2],
   [BPair.ofNat 1, BPair.unit],
   [BPair.ofNat 2, (BPair.ofNat 2).swap],
   [(BPair.ofNat 1).swap, BPair.ofNat 2],
   [BPair.unit, BPair.unit],
   [BPair.unit, BPair.unit],
   [BPair.ofNat 1, (BPair.ofNat 2).swap],
   [(BPair.ofNat 2).swap, BPair.ofNat 2],
   [(BPair.ofNat 1).swap, BPair.unit],
   [BPair.unit, (BPair.ofNat 2).swap]]

private def witsAdjB2 : List (List Nat) :=
  [[0, 0], [0, 1], [0, 2], [1, 1], [1, 2], [1, 2], [1, 3], [2, 2],
   [2, 3], [2, 4]]

private def WadjB2 : List (List BPair × Bool) :=
  [([(BPair.ofNat 1), (BPair.ofNat 3)], false),
   ([(BPair.ofNat 1).swap, (BPair.ofNat 5)], true),
   ([(BPair.ofNat 4), (BPair.ofNat 3).swap], true),
   ([(BPair.ofNat 4), (BPair.ofNat 5).swap], false),
   ([(BPair.ofNat 4).swap, (BPair.ofNat 5)], false),
   ([(BPair.ofNat 4).swap, (BPair.ofNat 3)], true),
   ([(BPair.ofNat 1), (BPair.ofNat 5).swap], true),
   ([(BPair.ofNat 1).swap, (BPair.ofNat 3).swap], false)]

private def witsWadjB2 : List (List Nat) :=
  [[0, 0], [1, 0], [0, 3], [1, 5], [4, 3], [5, 5], [4, 8], [5, 8]]

/-! The channels as parallel lists in one order — unit, vector,
adjoint — the tops, the families, their witnesses, the shifted
orbits and theirs. -/

private def cVsB2 : List (List BPair) := [zeroV, lamB2, adjB2]
private def LsB2 : List (List (List BPair)) := [LunitB2, mB2, LadjB2]
private def witssB2 : List (List (List Nat)) := [witsUnitB2, mwitsB2, witsAdjB2]
private def WsB2 : List (List (List BPair × Bool)) := [wB2, wpB2, WadjB2]
private def witsWsB2 : List (List (List Nat)) := [witsB2, wpwitsB2, witsWadjB2]

/-! The spinor factor's own reads: the top's frame, the family's
three, and the shifted alternant's five. -/

example : memberchar.lamRead tB2 spinB2 := by decide +kernel
example : memberchar.mShapeRead tB2 LspinB2 := by decide +kernel
example : memberchar.symRead tB2 LspinB2 := by decide +kernel
example : memberchar.supportRead tB2 LspinB2 witsSpinB2 spinB2 := by decide +kernel
example : memberchar.topRead LspinB2 spinB2 := by decide +kernel

example : sertables.wShapeRead tB2 WspinB2 := by decide +kernel
example : assembly.wCloseRead tB2 WspinB2 := by decide +kernel
example : assembly.wDomAt tB2 WspinB2 witsWspinB2 (shk spinB2) := by decide +kernel
example : assembly.wTopAt WspinB2 (shk spinB2) := by decide +kernel
example : assembly.wRegRead tB2 WspinB2 (shk spinB2) := by decide +kernel

/-- The spinor factor's recursion read, the `b`-side.  The pin is
carried by each of the three applications below, so it is named
once and consumed by term. -/
private theorem hrecSpinB2 :
    memberchar.recRead tB2 sertables.fundB2 wB2 LspinB2 spinB2 := by decide +kernel

/-! The three channels' eleven reads, one pin per read at the
concrete index.  The unit channel first. -/

example : memberchar.mShapeRead tB2 (ground.getAt [] LsB2 0) := by decide +kernel
example : memberchar.symRead tB2 (ground.getAt [] LsB2 0) := by decide +kernel
example : memberchar.supportRead tB2 (ground.getAt [] LsB2 0)
    (ground.getAt [] witssB2 0) (ground.getAt [] cVsB2 0) := by decide +kernel
example : memberchar.topRead (ground.getAt [] LsB2 0)
    (ground.getAt [] cVsB2 0) := by decide +kernel
example : memberchar.lamRead tB2 (ground.getAt [] cVsB2 0) := by decide +kernel
example : sertables.wShapeRead tB2 (ground.getAt [] WsB2 0) := by decide +kernel
example : assembly.wCloseRead tB2 (ground.getAt [] WsB2 0) := by decide +kernel
example : assembly.wDomAt tB2 (ground.getAt [] WsB2 0)
    (ground.getAt [] witsWsB2 0) (shk (ground.getAt [] cVsB2 0)) := by decide +kernel
example : assembly.wTopAt (ground.getAt [] WsB2 0)
    (shk (ground.getAt [] cVsB2 0)) := by decide +kernel
example : assembly.wRegRead tB2 (ground.getAt [] WsB2 0)
    (shk (ground.getAt [] cVsB2 0)) := by decide +kernel

/-! The vector channel. -/

example : memberchar.mShapeRead tB2 (ground.getAt [] LsB2 1) := by decide +kernel
example : memberchar.symRead tB2 (ground.getAt [] LsB2 1) := by decide +kernel
example : memberchar.supportRead tB2 (ground.getAt [] LsB2 1)
    (ground.getAt [] witssB2 1) (ground.getAt [] cVsB2 1) := by decide +kernel
example : memberchar.topRead (ground.getAt [] LsB2 1)
    (ground.getAt [] cVsB2 1) := by decide +kernel
example : memberchar.lamRead tB2 (ground.getAt [] cVsB2 1) := by decide +kernel
example : sertables.wShapeRead tB2 (ground.getAt [] WsB2 1) := by decide +kernel
example : assembly.wCloseRead tB2 (ground.getAt [] WsB2 1) := by decide +kernel
example : assembly.wDomAt tB2 (ground.getAt [] WsB2 1)
    (ground.getAt [] witsWsB2 1) (shk (ground.getAt [] cVsB2 1)) := by decide +kernel
example : assembly.wTopAt (ground.getAt [] WsB2 1)
    (shk (ground.getAt [] cVsB2 1)) := by decide +kernel
example : assembly.wRegRead tB2 (ground.getAt [] WsB2 1)
    (shk (ground.getAt [] cVsB2 1)) := by decide +kernel

/-! The adjoint channel. -/

example : memberchar.mShapeRead tB2 (ground.getAt [] LsB2 2) := by decide +kernel
example : memberchar.symRead tB2 (ground.getAt [] LsB2 2) := by decide +kernel
example : memberchar.supportRead tB2 (ground.getAt [] LsB2 2)
    (ground.getAt [] witssB2 2) (ground.getAt [] cVsB2 2) := by decide +kernel
example : memberchar.topRead (ground.getAt [] LsB2 2)
    (ground.getAt [] cVsB2 2) := by decide +kernel
example : memberchar.lamRead tB2 (ground.getAt [] cVsB2 2) := by decide +kernel
example : sertables.wShapeRead tB2 (ground.getAt [] WsB2 2) := by decide +kernel
example : assembly.wCloseRead tB2 (ground.getAt [] WsB2 2) := by decide +kernel
example : assembly.wDomAt tB2 (ground.getAt [] WsB2 2)
    (ground.getAt [] witsWsB2 2) (shk (ground.getAt [] cVsB2 2)) := by decide +kernel
example : assembly.wTopAt (ground.getAt [] WsB2 2)
    (shk (ground.getAt [] cVsB2 2)) := by decide +kernel
example : assembly.wRegRead tB2 (ground.getAt [] WsB2 2)
    (shk (ground.getAt [] cVsB2 2)) := by decide +kernel

/-! The three channels' recursion reads, the tier's heavy pins:
the eleven-read bundle the theorem binds is assembled from them
once by index and consumed by term at all three applications. -/

private theorem hrecUnitB2 :
    memberchar.recRead tB2 sertables.fundB2 wB2 LunitB2 zeroV := by decide +kernel

private theorem hrecVecB2 :
    memberchar.recRead tB2 sertables.fundB2 wB2 mB2 lamB2 := by decide +kernel

private theorem hrecAdjB2 :
    memberchar.recRead tB2 sertables.fundB2 wB2 LadjB2 adjB2 := by decide +kernel

/-- The channel bundle at the theorem's own spelling: the eleven
reads at every index below the tops' count, the three recursion
reads entering by term and the ten further reads by the kernel at
the index, the indices beyond the third refuted by the count. -/
private theorem hchB2 : ∀ k, k < cVsB2.length →
    memberchar.mShapeRead tB2 (ground.getAt [] LsB2 k)
    ∧ memberchar.symRead tB2 (ground.getAt [] LsB2 k)
    ∧ memberchar.supportRead tB2 (ground.getAt [] LsB2 k)
        (ground.getAt [] witssB2 k) (ground.getAt [] cVsB2 k)
    ∧ memberchar.topRead (ground.getAt [] LsB2 k) (ground.getAt [] cVsB2 k)
    ∧ memberchar.lamRead tB2 (ground.getAt [] cVsB2 k)
    ∧ memberchar.recRead tB2 sertables.fundB2 wB2 (ground.getAt [] LsB2 k)
        (ground.getAt [] cVsB2 k)
    ∧ sertables.wShapeRead tB2 (ground.getAt [] WsB2 k)
    ∧ assembly.wCloseRead tB2 (ground.getAt [] WsB2 k)
    ∧ assembly.wDomAt tB2 (ground.getAt [] WsB2 k)
        (ground.getAt [] witsWsB2 k)
        (poly.pnorm (elim.vecAdd (ground.getAt [] cVsB2 k)
          (sertables.rhoV tB2)))
    ∧ assembly.wTopAt (ground.getAt [] WsB2 k)
        (poly.pnorm (elim.vecAdd (ground.getAt [] cVsB2 k)
          (sertables.rhoV tB2)))
    ∧ assembly.wRegRead tB2 (ground.getAt [] WsB2 k)
        (poly.pnorm (elim.vecAdd (ground.getAt [] cVsB2 k)
          (sertables.rhoV tB2)))
  | 0, _ => ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      hrecUnitB2, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  | 1, _ => ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      hrecVecB2, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  | 2, _ => ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      hrecAdjB2, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  | (k + 3), h => absurd (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
      (Nat.le_of_succ_le_succ h))) (Nat.not_succ_le_zero k)

/-! The product family and its exhaustion: the sixteen memberwise
joins of the spinor family with itself, and every key's count in
them the three channel families' fold. -/

example : (steinberg.prodFam LspinB2 LspinB2).length = 16 := by decide +kernel

example : ∀ v ∈ steinberg.prodFam LspinB2 LspinB2,
    ground.countOf v (steinberg.prodFam LspinB2 LspinB2)
      = ground.famFold Nat.add 0
          (fun L' => ground.countOf v L') LsB2 := by decide +kernel

example : ∀ k, k < LsB2.length → ∀ v ∈ ground.getAt [] LsB2 k,
    ground.countOf v (steinberg.prodFam LspinB2 LspinB2)
      = ground.famFold Nat.add 0
          (fun L' => ground.countOf v L') LsB2 := by decide +kernel

example : ground.countOf zeroV (steinberg.prodFam LspinB2 LspinB2) = 4 := by
  decide +kernel
example : ground.countOf lamB2 (steinberg.prodFam LspinB2 LspinB2) = 2 := by
  decide +kernel
example : ground.countOf adjB2 (steinberg.prodFam LspinB2 LspinB2) = 1 := by
  decide +kernel

example : LsB2.length = cVsB2.length := by decide +kernel

/-! `cor:steinberg`'s member display applied whole, once per channel
top, every binder discharged at the data with the recursion tier
entering by term — and its computed twin beside each, the display
read directly by the kernel. -/

example : steinberg.memberAt tB2 WspinB2 LspinB2 cVsB2 zeroV :=
  steinberg.memberRead tB2 sertables.fundB2 wB2 witsB2 LspinB2 witsSpinB2
    spinB2 WspinB2 witsWspinB2 LspinB2 LsB2 witssB2 cVsB2 WsB2 witsWsB2
    zeroV
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hrecSpinB2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hchB2 (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : steinberg.memberAt tB2 WspinB2 LspinB2 cVsB2 zeroV := by decide +kernel

example : steinberg.memberAt tB2 WspinB2 LspinB2 cVsB2 lamB2 :=
  steinberg.memberRead tB2 sertables.fundB2 wB2 witsB2 LspinB2 witsSpinB2
    spinB2 WspinB2 witsWspinB2 LspinB2 LsB2 witssB2 cVsB2 WsB2 witsWsB2
    lamB2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hrecSpinB2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hchB2 (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : steinberg.memberAt tB2 WspinB2 LspinB2 cVsB2 lamB2 := by decide +kernel

example : steinberg.memberAt tB2 WspinB2 LspinB2 cVsB2 adjB2 :=
  steinberg.memberRead tB2 sertables.fundB2 wB2 witsB2 LspinB2 witsSpinB2
    spinB2 WspinB2 witsWspinB2 LspinB2 LsB2 witssB2 cVsB2 WsB2 witsWsB2
    adjB2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hrecSpinB2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hchB2 (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : steinberg.memberAt tB2 WspinB2 LspinB2 cVsB2 adjB2 := by decide +kernel

/-! The display's own sides at each channel top: the top's count
among the channel tops reads one, and the two convolution counts at
its shifted key read one even and none odd, the gap one at every
channel. -/

example : ground.countOf zeroV cVsB2 = 1 := by decide +kernel
example : memberchar.convCount WspinB2 LspinB2 (shk zeroV) false = 1 := by
  decide +kernel
example : memberchar.convCount WspinB2 LspinB2 (shk zeroV) true = 0 := by
  decide +kernel

example : ground.countOf lamB2 cVsB2 = 1 := by decide +kernel
example : memberchar.convCount WspinB2 LspinB2 (shk lamB2) false = 1 := by
  decide +kernel
example : memberchar.convCount WspinB2 LspinB2 (shk lamB2) true = 0 := by
  decide +kernel

example : ground.countOf adjB2 cVsB2 = 1 := by decide +kernel
example : memberchar.convCount WspinB2 LspinB2 (shk adjB2) false = 1 := by
  decide +kernel
example : memberchar.convCount WspinB2 LspinB2 (shk adjB2) true = 0 := by
  decide +kernel

/-! The vacant-channel read at a dominant top off the exhaustion,
`2ω₁ = (2,0)`: the count among the channel tops is none and the two
convolution counts agree at none, the display holding with both
sides vacant. -/

private def offV : List BPair := [BPair.ofNat 2, BPair.unit]

example : memberchar.lamRead tB2 offV := by decide +kernel
example : ground.countOf offV cVsB2 = 0 := by decide +kernel
example : memberchar.convCount WspinB2 LspinB2 (shk offV) false = 0 := by
  decide +kernel
example : memberchar.convCount WspinB2 LspinB2 (shk offV) true = 0 := by
  decide +kernel
example : steinberg.memberAt tB2 WspinB2 LspinB2 cVsB2 offV := by decide +kernel

/-! The refusal batteries, one forge per load-bearing binder.

`hexh1` and `hexh2` first, at the family side: one unit content
dropped from the adjoint channel, nine members at their witnesses.
The shape, the invariance, the top count and the support all survive
the drop; both exhaustion clauses refuse, the unit content's count
in the product family reading four against the channels' three.  The
adjoint channel's own recursion read moves with the drop — the
family is the character, so the refusal is committed entangled — and
the display at the adjoint top is untouched, the conclusion binding
no channel family. -/

private def LadjDrop : List (List BPair) :=
  [[BPair.unit, BPair.ofNat 2],
   [BPair.ofNat 1, BPair.unit],
   [BPair.ofNat 2, (BPair.ofNat 2).swap],
   [(BPair.ofNat 1).swap, BPair.ofNat 2],
   [BPair.unit, BPair.unit],
   [BPair.ofNat 1, (BPair.ofNat 2).swap],
   [(BPair.ofNat 2).swap, BPair.ofNat 2],
   [(BPair.ofNat 1).swap, BPair.unit],
   [BPair.unit, (BPair.ofNat 2).swap]]

private def witsAdjDrop : List (List Nat) :=
  [[0, 0], [0, 1], [0, 2], [1, 1], [1, 2], [1, 3], [2, 2], [2, 3], [2, 4]]

private def LsDrop : List (List (List BPair)) := [LunitB2, mB2, LadjDrop]

example : memberchar.mShapeRead tB2 LadjDrop := by decide +kernel
example : memberchar.symRead tB2 LadjDrop := by decide +kernel
example : memberchar.topRead LadjDrop adjB2 := by decide +kernel
example : memberchar.supportRead tB2 LadjDrop witsAdjDrop adjB2 := by decide +kernel

example : ground.famFold Nat.add 0
    (fun L' => ground.countOf zeroV L') LsDrop = 3 := by decide +kernel

example : ¬ (∀ v ∈ steinberg.prodFam LspinB2 LspinB2,
    ground.countOf v (steinberg.prodFam LspinB2 LspinB2)
      = ground.famFold Nat.add 0
          (fun L' => ground.countOf v L') LsDrop) := by decide +kernel

example : ¬ (∀ k, k < LsDrop.length → ∀ v ∈ ground.getAt [] LsDrop k,
    ground.countOf v (steinberg.prodFam LspinB2 LspinB2)
      = ground.famFold Nat.add 0
          (fun L' => ground.countOf v L') LsDrop) := by decide +kernel

/-! The forge's entanglement, pinned at its one instance: the family
IS the character, so the dropped member also refuses the channel's
`recRead` — the display fails at the window key `ρ` against the
`ρ`-member, where the withdrawn content is the dropped unit and the
count reads one against the genuine two.  The refused display is
pinned at that instance with the genuine family's read beside it,
the full `¬ recRead` decide priced past the module budget. -/

example : ¬ BPair.oneValue
    (BPair.mul (sertables.dotB sertables.fundB2 (shk adjB2) (shk adjB2))
      (BPair.ofNat (ground.countOf zeroV LadjDrop)))
    (BPair.add
      (BPair.mul (sertables.dotB sertables.fundB2 (shk zeroV) (shk zeroV))
        (BPair.ofNat (ground.countOf zeroV LadjDrop)))
      (memberchar.gSum tB2 sertables.fundB2 LadjDrop zeroV)) := by decide +kernel

example : BPair.oneValue
    (BPair.mul (sertables.dotB sertables.fundB2 (shk adjB2) (shk adjB2))
      (BPair.ofNat (ground.countOf zeroV LadjB2)))
    (BPair.add
      (BPair.mul (sertables.dotB sertables.fundB2 (shk zeroV) (shk zeroV))
        (BPair.ofNat (ground.countOf zeroV LadjB2)))
      (memberchar.gSum tB2 sertables.fundB2 LadjB2 zeroV)) := by decide +kernel

/-! `hexh1`'s conclusion-bearing face: the vector channel listed
twice, its family, orbit and both witness lists copied beside it.
Every per-channel read survives at the fourth index, the length read
survives, the exhaustion's fold double-counts the vector family —
the vector top's count in the product family reading two against
three — and the display fails at the vector top, where the count
among the tops reads two against the convolution's gap one. -/

private def cVsDup : List (List BPair) := cVsB2 ++ [lamB2]
private def LsDup : List (List (List BPair)) := LsB2 ++ [mB2]
private def witssDup : List (List (List Nat)) := witssB2 ++ [mwitsB2]
private def WsDup : List (List (List BPair × Bool)) := WsB2 ++ [wpB2]
private def witsWsDup : List (List (List Nat)) := witsWsB2 ++ [wpwitsB2]

example : LsDup.length = cVsDup.length := by decide +kernel

example : memberchar.mShapeRead tB2 (ground.getAt [] LsDup 3) := by decide +kernel
example : memberchar.symRead tB2 (ground.getAt [] LsDup 3) := by decide +kernel
example : memberchar.supportRead tB2 (ground.getAt [] LsDup 3)
    (ground.getAt [] witssDup 3) (ground.getAt [] cVsDup 3) := by decide +kernel
example : memberchar.topRead (ground.getAt [] LsDup 3)
    (ground.getAt [] cVsDup 3) := by decide +kernel
example : memberchar.lamRead tB2 (ground.getAt [] cVsDup 3) := by decide +kernel
example : sertables.wShapeRead tB2 (ground.getAt [] WsDup 3) := by decide +kernel
example : assembly.wCloseRead tB2 (ground.getAt [] WsDup 3) := by decide +kernel
example : assembly.wDomAt tB2 (ground.getAt [] WsDup 3)
    (ground.getAt [] witsWsDup 3) (shk (ground.getAt [] cVsDup 3)) := by decide +kernel
example : assembly.wTopAt (ground.getAt [] WsDup 3)
    (shk (ground.getAt [] cVsDup 3)) := by decide +kernel
example : assembly.wRegRead tB2 (ground.getAt [] WsDup 3)
    (shk (ground.getAt [] cVsDup 3)) := by decide +kernel

example : memberchar.recRead tB2 sertables.fundB2 wB2
    (ground.getAt [] LsDup 3) (ground.getAt [] cVsDup 3) := hrecVecB2

example : ground.famFold Nat.add 0
    (fun L' => ground.countOf lamB2 L') LsDup = 3 := by decide +kernel

example : ¬ (∀ v ∈ steinberg.prodFam LspinB2 LspinB2,
    ground.countOf v (steinberg.prodFam LspinB2 LspinB2)
      = ground.famFold Nat.add 0
          (fun L' => ground.countOf v L') LsDup) := by decide +kernel

example : ¬ (∀ k, k < LsDup.length → ∀ v ∈ ground.getAt [] LsDup k,
    ground.countOf v (steinberg.prodFam LspinB2 LspinB2)
      = ground.famFold Nat.add 0
          (fun L' => ground.countOf v L') LsDup) := by decide +kernel

example : ground.countOf lamB2 cVsDup = 2 := by decide +kernel
example : ¬ steinberg.memberAt tB2 WspinB2 LspinB2 cVsDup lamB2 := by decide +kernel

/-! `hlL`: the channel tops extended by `2ω₁ = (2,0)` at three
families.  The theorem's fold runs over the tops' count and the
family list must reach it: the length read refuses, and the display
fails at the added top, whose one count among the tops stands
against two vacant convolution counts.  The channel bundle refuses
with it at the fourth index, where the family list reads its own
default and the top count there is none — the entanglement is the
forge's own, pinned at that conjunct, and the length read is the one
the conclusion needs. -/

private def cVsExt : List (List BPair) := cVsB2 ++ [offV]

example : ¬ (LsB2.length = cVsExt.length) := by decide +kernel
example : ground.countOf offV cVsExt = 1 := by decide +kernel
example : ¬ memberchar.topRead (ground.getAt [] LsB2 3)
    (ground.getAt [] cVsExt 3) := by decide +kernel
example : ¬ steinberg.memberAt tB2 WspinB2 LspinB2 cVsExt offV := by decide +kernel

/-! The exhaustion's blind face: a spurious channel at a vacant
family.  The tops extended by `2ω₁` with the family list extended by
the vacant family: the lengths tie, both exhaustion clauses SURVIVE
— a vacant family enters the fold at the count's unit, so the
exhaustion cannot see the spurious channel — and the refusal is the
channel bundle's own `topRead` at the fourth index, the display
failing at the spurious top as the count among the tops reads one
against two vacant convolution counts. -/

private def LsSpur : List (List (List BPair)) :=
  LsB2 ++ [([] : List (List BPair))]

example : LsSpur.length = cVsExt.length := by decide +kernel

example : ∀ v ∈ steinberg.prodFam LspinB2 LspinB2,
    ground.countOf v (steinberg.prodFam LspinB2 LspinB2)
      = ground.famFold Nat.add 0
          (fun L' => ground.countOf v L') LsSpur := by decide +kernel

example : ∀ k, k < LsSpur.length → ∀ v ∈ ground.getAt [] LsSpur k,
    ground.countOf v (steinberg.prodFam LspinB2 LspinB2)
      = ground.famFold Nat.add 0
          (fun L' => ground.countOf v L') LsSpur := by decide +kernel

example : ¬ memberchar.topRead (ground.getAt [] LsSpur 3)
    (ground.getAt [] cVsExt 3) := by decide +kernel
example : ¬ steinberg.memberAt tB2 WspinB2 LspinB2 cVsExt offV := by decide +kernel

/-! `hcV`: the stated top off its own frame.  The unnormed unit
content — the natural one joined to its swap — refuses at the
normed conjunct, and the display fails at `ρ`, the shifted key its
normed twin occupies: the count among the tops is vacant at the
unnormed spelling while the convolution's gap there reads one.  The
non-dominant `(-1,0)` and the short `(1)` refuse at the read's other
two conjuncts, the dominance and the order. -/

private def badNorm : List BPair :=
  [BPair.ofNat 1 + (BPair.ofNat 1).swap, BPair.unit]
private def badDom : List BPair := [(BPair.ofNat 1).swap, BPair.unit]
private def badLen : List BPair := [BPair.ofNat 1]

example : ¬ memberchar.lamRead tB2 badNorm := by decide +kernel
example : ¬ memberchar.lamRead tB2 badDom := by decide +kernel
example : ¬ memberchar.lamRead tB2 badLen := by decide +kernel

example : poly.pnorm badNorm = zeroV := by decide +kernel
example : shk badNorm = shk zeroV := by decide +kernel
example : ground.countOf badNorm cVsB2 = 0 := by decide +kernel
example : ¬ steinberg.memberAt tB2 WspinB2 LspinB2 cVsB2 badNorm := by decide +kernel

/-! The two graded sums as the parity-guarded folds, at the `su(2)`
scale's own triple. -/

example : steinberg.sumsWith
      (blockcount.occupancyAt (blockcount.blockSpan [2, 0])) 2
      [2, 0] [4, 0]
    = (1, 0) := by decide +kernel

example : (ground.famFold Nat.add 0
      (fun p => if places.parity p = false then
        weylchar.multAtGap
          (blockcount.occupancyAt (blockcount.blockSpan [2, 0]))
          (display [4, 0]) (places.expo (display [2, 0]) p) else 0)
      (places.perms 2),
    ground.famFold Nat.add 0
      (fun p => if places.parity p = true then
        weylchar.multAtGap
          (blockcount.occupancyAt (blockcount.blockSpan [2, 0]))
          (display [4, 0]) (places.expo (display [2, 0]) p) else 0)
      (places.perms 2)) = (1, 0) := by decide +kernel

example : steinberg.sumsWith
      (blockcount.occupancyAt (blockcount.blockSpan [2, 0])) 2
      [2, 0] [4, 0]
    = (ground.famFold Nat.add 0
        (fun p => if places.parity p = false then
          weylchar.multAtGap
            (blockcount.occupancyAt (blockcount.blockSpan [2, 0]))
            (display [4, 0]) (places.expo (display [2, 0]) p) else 0)
        (places.perms 2),
      ground.famFold Nat.add 0
        (fun p => if places.parity p = true then
          weylchar.multAtGap
            (blockcount.occupancyAt (blockcount.blockSpan [2, 0]))
            (display [4, 0]) (places.expo (display [2, 0]) p) else 0)
        (places.perms 2)) :=
  steinberg.sumsWith_split
    (blockcount.occupancyAt (blockcount.blockSpan [2, 0])) 2
    [2, 0] [4, 0]

/-! The fast count against `def:blockcount`'s kernel-dimension
count through the derived identity: the fundamental against the
adjoint at the two-letter data, the display's gap withdrawn at the
shared graded sum. -/

example : steinberg.count [1, 0] (adjchar.theta 2) [1, 1]
    = blockcount.fusionCount [1, 0] (adjchar.theta 2) [1, 1] :=
  steinberg.count_fusion [1, 0] (adjchar.theta 2) [1, 1] rfl rfl

/-- The identity's two width binders isolated.  `hba` is
load-bearing: at the ragged second shape the fast count reads one
against the kernel count's nought, the committed refusal.  `hca`
is the frame: at the wide third shape with `hba` held both counts
are vacant and the identity holds, the binder unrefusable
there. -/
example : ¬ (steinberg.count [1, 0] [1] [0, 0]
    = blockcount.fusionCount [1, 0] [1] [0, 0]) := by decide +kernel
example : steinberg.count [1, 0] (adjchar.theta 2) [1, 1, 0]
    = blockcount.fusionCount [1, 0] (adjchar.theta 2) [1, 1, 0] :=
  by decide +kernel
