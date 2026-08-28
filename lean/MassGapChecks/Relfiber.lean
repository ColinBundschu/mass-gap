import MassGap.Relfiber
import MassGap.E0
import MassGapChecks.Fiberdec
/-!
The check module for `lem:relfiber`: the batteries re-read the
tensor-sum pencil's calculus by kernel `decide`.  The carrier's
shape, its entry reads at the product index, the pairing's
factorization, the action and the matrix product, the key-list
exchange, linearity in each slot with the weighting and the
memberwise swap, associativity and the identity are each decided
at committed two-by-two literals, the laws landed at `Eq` pinned
by their own equations; the tensor-sum pencil is read at the
splittings — at `ϱ = 1` the single-component pencil itself, at
`ϱ = 2` the two-summand display `H ⊗ G + G ⊗ H`, at `ϱ = 3` the
three-summand display associativity-normalized on the right.

The frame classification rides beside them.  Load-bearing with
committed refusals: `rowsLen_tensorM`'s two width binders (a
ragged factor moves the product's rows off the widths' product,
each refusal with the other factor's width standing);
`tensorPow_shape`'s square read (a wide single row powers off its
own row count); `getAt_tensorV`'s and `getAt_tensorM`'s second
key binders (a key beyond the second factor's count reads the
next block against the vacant read, the first key's binder
standing); `dotP_tensorV`'s and `dotN_tensorV`'s second-slot
length (mismatched second factors misalign the product index's
stride, so the collected fold parts from the folds' product);
`matVec_tensorM`'s width (the same stride mismatch at the
action); `matMul_tensorM`'s `rowsLen r B`, `D.length = r` and
`rowsLen s D` (the first two at the entry fold's stride, the
third at the exchange, each with every co-binder standing);
`transposeM_tensorM`'s second-factor width (a ragged second
factor moves the exchanged tensor's entries off the exchanges'
tensor); and `tensorM_addR`'s three binders (unequal row counts
misalign the summands' blocks, and either summand off the stated
width misaligns the strides).

Frame records, no refusal found: `getAt_tensorV`'s and
`getAt_tensorM`'s first key binders — beyond the first factor's
count both sides read the vacant entry, probed at a short first
factor, at a key two beyond the count and at a vacant second
factor; and the first factors' width binders in
`transposeM_tensorM` and `matMul_tensorM` — the exchange pads a
short row at the sum's unit and the tensor carries the padding
through, probed at four ragged first factors for the exchange (a
short leading row, a long leading row, both against square and
against tall second factors, and a three-row raggedness) and at
three for the product (both raggednesses against a single-row
left factor, and the short leading row against a two-row one).
Both are the `getAt_transposeM` and `getAt_tensorV` reads' own
consumers.
`A.length = p` and `B.length = r` in `transposeM_tensorM` are
naming frames: every matrix satisfies them at its own row count.
-/


open ground elim relfiber fiberdec

private def q1 : BPair := BPair.ofNat 2
private def q2 : BPair := BPair.ofNat 1
private def q3 : BPair := (BPair.ofNat 1).swap
private def q4 : BPair := BPair.ofNat 3
private def q5 : BPair := BPair.ofNat 5
private def q6 : BPair := (BPair.ofNat 2).swap

private def mA : Mat := [[q1, q2], [q3, q4]]
private def mB : Mat := [[q2, q3], [q4, q1]]
private def mC : Mat := [[q4, q1], [q2, q3]]
private def mD : Mat := [[q3, q4], [q1, q2]]

private def vU : List BPair := [q1, q3]
private def vV : List BPair := [q2, q4]
private def vW : List BPair := [q4, q2]
private def vZ : List BPair := [q3, q1]

/-! ### The shape and the entry reads -/

example : (tensorV vU vV).length = vU.length * vV.length := by decide +kernel

example : (tensorM mA mB).length = mA.length * mB.length := by decide +kernel

example : rowsLen (2 * 2) (tensorM mA mB) := by decide +kernel

example : rowsLen (mA.length ^ 2) (tensorPow mA 2)
    ∧ (tensorPow mA 2).length = mA.length ^ 2 := by decide +kernel

example : ground.getAt BPair.unit (tensorV vU vV) (1 * vV.length + 0)
    = (ground.getAt BPair.unit vU 1
      * ground.getAt BPair.unit vV 0).norm := by decide +kernel

example : ground.getAt BPair.unit (tensorV vU vV) (0 * vV.length + 1)
    = (ground.getAt BPair.unit vU 0
      * ground.getAt BPair.unit vV 1).norm := by decide +kernel

example : ground.getAt [] (tensorM mA mB) (1 * mB.length + 1)
    = tensorV (ground.getAt [] mA 1) (ground.getAt [] mB 1) := by decide +kernel

example : ground.getAt [] (tensorM mA mB) (0 * mB.length + 1)
    = tensorV (ground.getAt [] mA 0) (ground.getAt [] mB 1) := by decide +kernel

/-! ### The pairing, the action and the product -/

example : (dotP (tensorV vU vV) (tensorV vW vZ)).oneValue
    (dotP vU vW * dotP vV vZ) := by decide +kernel

example : (dotN (tensorV vU vV) (tensorV vW vZ)).oneValue
    ((dotN vU vW * dotN vV vZ).norm) := by decide +kernel

example : poly.oneValue (matVec (tensorM mA mB) (tensorV vU vV))
    (tensorV (matVec mA vU) (matVec mB vV)) := by decide +kernel

example : matOneValue (matMul (tensorM mA mB) (tensorM mC mD))
    (tensorM (matMul mA mC) (matMul mB mD)) := by decide +kernel

/-! ### The equations: the exchange, the weighting, the swap,
associativity and the identity -/

example : transposeM (tensorM mA mB)
    = tensorM (transposeM mA) (transposeM mB) := by decide +kernel

example : tensorM (inertia.matScaleB q4 mA) mB
    = inertia.matScaleB q4 (tensorM mA mB) := by decide +kernel

example : tensorM mA (inertia.matScaleB q4 mB)
    = inertia.matScaleB q4 (tensorM mA mB) := by decide +kernel

example : tensorM (matSwap mA) mB = matSwap (tensorM mA mB) := by decide +kernel

example : tensorM mA (matSwap mB) = matSwap (tensorM mA mB) := by decide +kernel

example : tensorV (tensorV vU vV) vW = tensorV vU (tensorV vV vW) := by
  decide +kernel

example : tensorM (tensorM mA mB) mC = tensorM mA (tensorM mB mC) := by
  decide +kernel

example : tensorM (inertia.idMat 2) (inertia.idMat 3)
    = inertia.idMat (2 * 3) := by decide +kernel

/-! ### Linearity in each slot -/

example : matOneValue (tensorM (matAdd mA mC) mB)
    (matAdd (tensorM mA mB) (tensorM mC mB)) := by decide +kernel

example : matOneValue (tensorM mA (matAdd mB mD))
    (matAdd (tensorM mA mB) (tensorM mA mD)) := by decide +kernel

/-! ### The tensor-sum pencil at the splittings -/

example : matOneValue (sumPencil mA mB 1) mA := by decide +kernel

example : matOneValue (sumPencil mA mB 2)
    (matAdd (tensorM mA mB) (tensorM mB mA)) := by decide +kernel

example : matOneValue (sumPencil mA mB 3)
    (matAdd (tensorM mA (tensorM mB mB))
      (matAdd (tensorM mB (tensorM mA mB))
        (tensorM mB (tensorM mB mA)))) := by decide +kernel

/-! ### The frames' refusals -/

private def ragL : Mat := [[q1], [q2, q3]]
private def sqW : Mat := [[q1, q2]]

example : ¬ rowsLen (1 * 2) (tensorM ragL sqW) := by decide +kernel
example : rowsLen 2 sqW := by decide +kernel

example : ¬ rowsLen (1 * 1) (tensorM [[q1]] ragL) := by decide +kernel
example : rowsLen 1 ([[q1]] : Mat) := by decide +kernel

example : ¬ (rowsLen (sqW.length ^ 1) (tensorPow sqW 1)
    ∧ (tensorPow sqW 1).length = sqW.length ^ 1) := by decide +kernel

example : ¬ (ground.getAt BPair.unit (tensorV [q1, q2] [q3, q4])
      (0 * ([q3, q4] : List BPair).length + 2)
    = (ground.getAt BPair.unit [q1, q2] 0
      * ground.getAt BPair.unit [q3, q4] 2).norm) := by decide +kernel
example : 0 < ([q1, q2] : List BPair).length := by decide +kernel

example : ¬ (ground.getAt [] (tensorM [[q1], [q2]] [[q3]])
      (0 * ([[q3]] : Mat).length + 1)
    = tensorV (ground.getAt [] [[q1], [q2]] 0)
      (ground.getAt [] [[q3]] 1)) := by decide +kernel
example : 0 < ([[q1], [q2]] : Mat).length := by decide +kernel

example : ¬ (dotP (tensorV [q1, q2] [q3, q4]) (tensorV [q5, q6] [q1])).oneValue
    (dotP [q1, q2] [q5, q6] * dotP [q3, q4] [q1]) := by decide +kernel

example : ¬ (dotN (tensorV [q1, q2] [q3, q4]) (tensorV [q5, q6] [q1])).oneValue
    ((dotN [q1, q2] [q5, q6] * dotN [q3, q4] [q1]).norm) := by decide +kernel

example : ¬ poly.oneValue
    (matVec (tensorM [[q1, q2]] [[q3, q4]]) (tensorV [q5, q6] [q1]))
    (tensorV (matVec [[q1, q2]] [q5, q6]) (matVec [[q3, q4]] [q1])) := by
  decide +kernel

private def ragR : Mat := [[q3], [q4, q5]]

example : ¬ (transposeM (tensorM sqW ragR)
    = tensorM (transposeM sqW) (transposeM ragR)) := by decide +kernel
example : sqW.length = 1 := by decide +kernel
example : rowsLen 2 sqW := by decide +kernel

private def aRow : Mat := [[q1, q2]]
private def cSq : Mat := [[q4, q1], [q5, q6]]

example : ¬ matOneValue
    (matMul (tensorM aRow [[q1, q4]]) (tensorM cSq [[q2]]))
    (tensorM (matMul aRow cSq) (matMul [[q1, q4]] [[q2]])) := by decide +kernel
example : rowsLen 2 ([[q1, q4]] : Mat) := by decide +kernel
example : rowsLen 2 cSq := by decide +kernel
example : rowsLen 1 ([[q2]] : Mat) := by decide +kernel

example : ¬ matOneValue
    (matMul (tensorM aRow [[q1], [q4, q5]]) (tensorM cSq [[q2]]))
    (tensorM (matMul aRow cSq) (matMul [[q1], [q4, q5]] [[q2]])) := by decide +kernel
example : ([[q2]] : Mat).length = 1 := by decide +kernel

example : ¬ matOneValue
    (matMul (tensorM aRow [[q1, q4]]) (tensorM cSq [[q2], [q3, q5]]))
    (tensorM (matMul aRow cSq) (matMul [[q1, q4]] [[q2], [q3, q5]])) := by
  decide +kernel
example : ([[q2], [q3, q5]] : Mat).length = 2 := by decide +kernel

example : ¬ matOneValue
    (tensorM [[q1], [q2]] (matAdd [[q3], [q4]] [[q5]]))
    (matAdd (tensorM [[q1], [q2]] [[q3], [q4]])
      (tensorM [[q1], [q2]] [[q5]])) := by decide +kernel
example : rowsLen 1 ([[q3], [q4]] : Mat) := by decide +kernel
example : rowsLen 1 ([[q5]] : Mat) := by decide +kernel

example : ¬ matOneValue
    (tensorM aRow (matAdd [[q3], [q4]] [[q5, q6], [q1, q2]]))
    (matAdd (tensorM aRow [[q3], [q4]])
      (tensorM aRow [[q5, q6], [q1, q2]])) := by decide +kernel
example : ([[q3], [q4]] : Mat).length = ([[q5, q6], [q1, q2]] : Mat).length := by
  decide +kernel

example : ¬ matOneValue
    (tensorM aRow (matAdd [[q5, q6], [q1, q2]] [[q3], [q4]]))
    (matAdd (tensorM aRow [[q5, q6], [q1, q2]])
      (tensorM aRow [[q3], [q4]])) := by decide +kernel

/-! ### The frame records: the reads standing off their binders -/

example : ground.getAt BPair.unit (tensorV [q1] [q3, q4])
      (1 * ([q3, q4] : List BPair).length + 0)
    = (ground.getAt BPair.unit [q1] 1
      * ground.getAt BPair.unit [q3, q4] 0).norm := by decide +kernel

example : ground.getAt BPair.unit (tensorV [q1, q2] [q3, q4])
      (3 * ([q3, q4] : List BPair).length + 1)
    = (ground.getAt BPair.unit [q1, q2] 3
      * ground.getAt BPair.unit [q3, q4] 1).norm := by decide +kernel

example : ground.getAt BPair.unit (tensorV [q1, q2] [])
      (2 * ([] : List BPair).length + 0)
    = (ground.getAt BPair.unit [q1, q2] 2
      * ground.getAt BPair.unit ([] : List BPair) 0).norm := by decide +kernel

example : ground.getAt [] (tensorM [[q1]] [[q3], [q4]])
      (1 * ([[q3], [q4]] : Mat).length + 0)
    = tensorV (ground.getAt [] [[q1]] 1)
      (ground.getAt [] [[q3], [q4]] 0) := by decide +kernel

example : ground.getAt [] (tensorM [[q1], [q2]] [[q3], [q4]])
      (2 * ([[q3], [q4]] : Mat).length + 1)
    = tensorV (ground.getAt [] [[q1], [q2]] 2)
      (ground.getAt [] [[q3], [q4]] 1) := by decide +kernel

example : transposeM (tensorM ragL [[q4, q5]])
    = tensorM (transposeM ragL) (transposeM [[q4, q5]]) := by decide +kernel

example : transposeM (tensorM [[q1, q2], [q3]] [[q4, q5]])
    = tensorM (transposeM [[q1, q2], [q3]]) (transposeM [[q4, q5]]) := by
  decide +kernel

example : transposeM (tensorM [[q1, q2], [q3]] [[q4], [q5]])
    = tensorM (transposeM [[q1, q2], [q3]]) (transposeM [[q4], [q5]]) := by
  decide +kernel

example : transposeM (tensorM [[q1], [q2, q3], [q4]] [[q5, q6]])
    = tensorM (transposeM [[q1], [q2, q3], [q4]])
      (transposeM [[q5, q6]]) := by decide +kernel

example : matOneValue
    (matMul (tensorM aRow [[q1, q4]]) (tensorM [[q4], [q5, q6]] [[q2, q1], [q4, q3]]))
    (tensorM (matMul aRow [[q4], [q5, q6]])
      (matMul [[q1, q4]] [[q2, q1], [q4, q3]])) := by decide +kernel

example : matOneValue
    (matMul (tensorM aRow [[q1, q4]]) (tensorM [[q4, q1], [q5]] [[q2, q1], [q4, q3]]))
    (tensorM (matMul aRow [[q4, q1], [q5]])
      (matMul [[q1, q4]] [[q2, q1], [q4, q3]])) := by decide +kernel

example : matOneValue
    (matMul (tensorM [[q1, q2], [q4, q5]] [[q1, q4]])
      (tensorM [[q4], [q5, q6]] [[q2, q1], [q4, q3]]))
    (tensorM (matMul [[q1, q2], [q4, q5]] [[q4], [q5, q6]])
      (matMul [[q1, q4]] [[q2, q1], [q4, q3]])) := by decide +kernel

/-! ### Tier F: the separated bottom adds

The clause's two form theorems and its clearing ride committed
two-by-two fixtures with their splits written out.  The gram is
`G = [[1,1],[1,2]]` at the integer congruence `T = [[1,-1],[0,1]]`
against its adjugate `[[1,1],[0,1]]`, the image `diag(1,1)`, so the
split's blocks both sit at order one and the reversal count
vanishes; the single-component head is `H = 2G` at the level
`⟨x : y⟩ = ⟨2 : 1⟩`, whose site datum `H + yG - xG` is the gram
itself and reads the same split.  At `ϱ = 2` the sector's pencil is
`H ⊗ G + G ⊗ H = 4 G^{⊗2}`, so the bracket `⟨p : q⟩ = ⟨3 : 1⟩` —
tight against `ϱℓ`, `p + ϱy = ϱx + q` — leaves `2 G^{⊗2}`, and its
committed four-by-four split is the congruence's own tensor
`T ⊗ T` against `Tw ⊗ Tw` at the image `diag(2,2,2,2)`;
`bottomClear` closes `psdAt` there through the theorem and the same
instance decides by the kernel.

The frame classification.  Load-bearing with committed refusals:
the level comparison `hlev` (at `⟨p : q⟩ = ⟨6 : 1⟩` the sector's
datum is `-G^{⊗2}`, its committed split reading four reversals, and
the comparison refuses while every co-binder stands); and the
floor's `psdAt` (at `H = 0` the site datum is `-G`, its committed
split reading two reversals, and the sector's datum is
`-2 G^{⊗2}`, refused — the two splits committed on both sides of
the implication).

Frame records, no refusal found.  `spG`'s all-order-one conjunct is
the route the tex's derivation names — the gram's pivot congruence,
the split at order-one blocks a positive-definite datum reads off
its leading minors — and a positive semidefinite gram tensors to a
positive semidefinite product whatever the split's block shape, so
the conjunct cannot bite the conclusion.  The
search is recorded at the committed order-two split of
`[[2,1],[1,2]]` (the block `.two 2 1 2` at determinant three, the
reversal count vanishing, the order conjunct false) with the
conclusion's form decided at or above the sum's unit at four
vectors.  `1 ≤ rho` is likewise the route's: at `ϱ = 0` the
sector's datum is the one-by-one `[q - p]` and the level
comparison reads `p ≤ q` exactly, so the datum sits at or above
the sum's unit and the conclusion stands; the instance is decided
beside the record.
-/

private def w0 : BPair := BPair.unit
private def w1 : BPair := ⟨2, 1⟩
private def w2 : BPair := ⟨3, 1⟩
private def w4 : BPair := ⟨5, 1⟩
private def wm1 : BPair := ⟨1, 2⟩
private def wm2 : BPair := ⟨1, 3⟩

/-! The gram, its congruence and its split. -/

private def gG : Mat := [[w1, w1], [w1, w2]]
private def gT : Mat := [[w1, wm1], [w0, w1]]
private def gTw : Mat := [[w1, w1], [w0, w1]]

private def spG : inertia.Split 2 :=
  ⟨⟨gT, rfl⟩, ⟨gTw, rfl⟩, [.one w1, .one w1], 0, rfl⟩

example : inertia.splitRead gG spG := by decide +kernel
example : inertia.psdAt spG := by decide +kernel
example : (spG.blocks.all (fun b => b.order == 1)) = true := by decide +kernel

/-! The single-component head at the level `⟨2 : 1⟩`: the site datum
is the gram itself. -/

private def hH : Mat := [[w2, w2], [w2, w4]]

example : inertia.splitRead (inertia.siteDatum
    (matAdd hH (inertia.matScale 1 gG)) (inertia.matScale 2 gG)) spG := by
  decide +kernel

/-! The tensored congruence at the sector's order and the sector's
own split at the bracket `⟨3 : 1⟩`. -/

private def gT4 : Mat :=
  [[w1, wm1, wm1, w1], [w0, w1, w0, wm1],
   [w0, w0, w1, wm1], [w0, w0, w0, w1]]
private def gTw4 : Mat :=
  [[w1, w1, w1, w1], [w0, w1, w0, w1],
   [w0, w0, w1, w1], [w0, w0, w0, w1]]

example : gT4 = tensorM gT gT := by decide +kernel
example : gTw4 = tensorM gTw gTw := by decide +kernel

private def spSec : inertia.Split 4 :=
  ⟨⟨gT4, rfl⟩, ⟨gTw4, rfl⟩, [.one w2, .one w2, .one w2, .one w2], 0, rfl⟩

example : inertia.splitRead (inertia.siteDatum
    (matAdd (sumPencil hH gG 2) (inertia.matScale 1 (tensorPow gG 2)))
    (inertia.matScale 3 (tensorPow gG 2))) spSec := by decide +kernel

example : inertia.psdAt spSec := by decide +kernel

example : BPair.ofPos 3 + BPair.ofNat 2 * BPair.ofPos 1
    ≤ BPair.ofNat 2 * BPair.ofPos 2 + BPair.ofPos 1 := by decide +kernel

/-- The clearing through the theorem at the committed instance. -/
example : inertia.psdAt spSec :=
  bottomClear hH gG (by decide +kernel) (by decide +kernel) 2 1 spG (by decide +kernel)
    (by decide +kernel) spG (by decide +kernel) (by decide +kernel) (by decide +kernel) 2
    (by decide +kernel) 3 1 (by decide +kernel) spSec (by decide +kernel)

/-! ### The refusals -/

/-! The level comparison: at the bracket `⟨6 : 1⟩` the sector's
datum is `-G^{⊗2}`, four reversals at the same congruence, and the
comparison refuses with every co-binder standing. -/

private def spSecNeg : inertia.Split 4 :=
  ⟨⟨gT4, rfl⟩, ⟨gTw4, rfl⟩, [.one wm1, .one wm1, .one wm1, .one wm1],
   0, rfl⟩

example : inertia.splitRead (inertia.siteDatum
    (matAdd (sumPencil hH gG 2) (inertia.matScale 1 (tensorPow gG 2)))
    (inertia.matScale 6 (tensorPow gG 2))) spSecNeg := by decide +kernel

example : inertia.revAt spSecNeg = 4 := by decide +kernel
example : ¬ inertia.psdAt spSecNeg := by decide +kernel

example : ¬ (BPair.ofPos 6 + BPair.ofNat 2 * BPair.ofPos 1
    ≤ BPair.ofNat 2 * BPair.ofPos 2 + BPair.ofPos 1) := by decide +kernel

/-! The floor's `psdAt`: at `H = 0` the site datum is `-G`, two
reversals, and the sector's datum is `-2 G^{⊗2}`, refused. -/

private def hZero : Mat := [[w0, w0], [w0, w0]]

private def spFloorNeg : inertia.Split 2 :=
  ⟨⟨gT, rfl⟩, ⟨gTw, rfl⟩, [.one wm1, .one wm1], 0, rfl⟩

example : inertia.splitRead (inertia.siteDatum
    (matAdd hZero (inertia.matScale 1 gG)) (inertia.matScale 2 gG))
    spFloorNeg := by decide +kernel

example : ¬ inertia.psdAt spFloorNeg := by decide +kernel

private def spSecNeg2 : inertia.Split 4 :=
  ⟨⟨gT4, rfl⟩, ⟨gTw4, rfl⟩, [.one wm2, .one wm2, .one wm2, .one wm2],
   0, rfl⟩

example : inertia.splitRead (inertia.siteDatum
    (matAdd (sumPencil hZero gG 2) (inertia.matScale 1 (tensorPow gG 2)))
    (inertia.matScale 3 (tensorPow gG 2))) spSecNeg2 := by decide +kernel

example : ¬ inertia.psdAt spSecNeg2 := by decide +kernel

/-! ### The frame records -/

/-! The order-one conjunct: the committed order-two split of
`[[2,1],[1,2]]`, positive semidefinite at a block the conjunct
refuses, with the tensor's form standing at or above the sum's unit
at four committed vectors. -/

private def gTwoBlk : Mat := [[w2, w1], [w1, w2]]
private def spTwoBlk : inertia.Split 2 :=
  ⟨⟨inertia.idMat 2, rfl⟩, ⟨inertia.idMat 2, rfl⟩,
   [.two w2 w1 w2], 0, rfl⟩

example : inertia.splitRead gTwoBlk spTwoBlk := by decide +kernel
example : inertia.psdAt spTwoBlk := by decide +kernel
example : (spTwoBlk.blocks.all (fun b => b.order == 1)) = false := by decide +kernel

private def v1 : List BPair := [w1, w0, w0, w0]
private def v2 : List BPair := [w1, wm1, w1, wm1]
private def v3 : List BPair := [w2, w1, wm1, w1]
private def v4 : List BPair := [wm2, w1, w2, wm1]

example : ¬ (inertia.quadForm (tensorM gTwoBlk gG) v1 < BPair.unit) := by
  decide +kernel
example : ¬ (inertia.quadForm (tensorM gTwoBlk gG) v2 < BPair.unit) := by
  decide +kernel
example : ¬ (inertia.quadForm (tensorM gTwoBlk gG) v3 < BPair.unit) := by
  decide +kernel
example : ¬ (inertia.quadForm (tensorM gG gTwoBlk) v4 < BPair.unit) := by
  decide +kernel

/-! `1 ≤ rho`: at the vacant factor count the sector's datum is the
one-by-one bracket difference, and the level comparison reads
`p ≤ q` exactly, so the datum stands. -/

private def spZeroSec : inertia.Split 1 :=
  ⟨⟨[[w1]], rfl⟩, ⟨[[w1]], rfl⟩, [.one w1], 0, rfl⟩

example : BPair.ofPos 1 + BPair.ofNat 0 * BPair.ofPos 1
    ≤ BPair.ofNat 0 * BPair.ofPos 2 + BPair.ofPos 2 := by decide +kernel

example : inertia.splitRead (inertia.siteDatum
    (matAdd (sumPencil hH gG 0) (inertia.matScale 2 (tensorPow gG 0)))
    (inertia.matScale 1 (tensorPow gG 0))) spZeroSec := by decide +kernel

example : inertia.psdAt spZeroSec := by decide +kernel

/-! ### The two form theorems at committed vectors -/

example : ¬ (inertia.quadForm (tensorM gG gG) v1 < BPair.unit) := by decide +kernel
example : ¬ (inertia.quadForm (tensorM gG gG) v2 < BPair.unit) := by decide +kernel
example : ¬ (inertia.quadForm (tensorM gG gG) v3 < BPair.unit) := by decide +kernel
example : ¬ (inertia.quadForm (tensorM gG gG) v4 < BPair.unit) := by decide +kernel

example : ¬ (inertia.quadForm (tensorM gG gG) v3 < BPair.unit) :=
  tensor_form_left gG spG (by decide +kernel) (by decide +kernel) (by decide +kernel) gG 2
    (by decide +kernel) (inertia.psd_all gG spG (by decide +kernel) (by decide +kernel)) v3
    (by decide +kernel)

example : ¬ (inertia.quadForm (tensorM gG gG) v4 < BPair.unit) :=
  tensor_form_right gG spG (by decide +kernel) (by decide +kernel) (by decide +kernel) gG 2
    (by decide +kernel) (inertia.psd_all gG spG (by decide +kernel) (by decide +kernel)) v4
    (by decide +kernel)

/-! ### The relative translation and the tensor congruence -/

private def mP : Mat := [[w2, w1], [w1, w2]]

example : matOneValue
    (matMul (tensorM gG (inertia.idMat 2))
      (tensorM (inertia.idMat 2) mP))
    (matMul (tensorM (inertia.idMat 2) mP)
      (tensorM gG (inertia.idMat 2))) := by decide +kernel

example : matOneValue
    (matMul (tensorM gG (inertia.idMat 2))
      (tensorM (inertia.idMat 2) mP))
    (matMul (tensorM (inertia.idMat 2) mP)
      (tensorM gG (inertia.idMat 2))) :=
  comm_shift 2 2 gG mP (by decide +kernel) (by decide +kernel)

example : matOneValue
    (matMul (transposeM (tensorM gT gTw))
      (matMul (tensorM gG mP) (tensorM gT gTw)))
    (tensorM (matMul (transposeM gT) (matMul gG gT))
      (matMul (transposeM gTw) (matMul mP gTw))) := by decide +kernel

example : matOneValue
    (matMul (transposeM (tensorM gT gTw))
      (matMul (tensorM gG mP) (tensorM gT gTw)))
    (tensorM (matMul (transposeM gT) (matMul gG gT))
      (matMul (transposeM gTw) (matMul mP gTw))) :=
  congr_tensorM 2 2 2 2 gG mP gT gTw (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) rfl (by decide +kernel)

/-! ### Tier I: the components' index reads

The index tier's batteries ride the plaquette chain of nine
squares (`R9`) at the label calculus of fundamental count three,
the elementary loop on one square the band component (`loopAt`,
the forward boundary entries at the fundamental label, the
reversed at its dual).  The chain is a ring, so the class at the
squares three apart is pairwise vertex-disjoint while the class
at zero, four and eight is refused across the wrap — the two
classes decide the join's own reads (`allDisj`, `disjAll`), and
the three-apart class's join occupies twelve links at three times
one loop's content.  The content's additivity is read at the pair
four apart through the theorem and by `decide` beside it, and the
reach read at every boundary word of the region: at the separated
pair no word reads both neighborhoods, while the once-interposed
pair refuses the separation and its interposed square reads both.
The fibering instance closes clause (ii)'s reads at the three-key
cycle: the deck column's base diagonalizes the fiber slot, the
tensor congruence takes the pencil `X ⊗ 1` onto `X ⊗ VVᵀ`, the
relative translation commutes with it, and the congruenced
datum's committed split reads the three fibers' scaled copies of
`X` with the reversal counts summing to the whole's.

The frame classification.  `contentN_join`'s four binders are
load-bearing with committed refusals: the shape read `hw` (at the
vacant vertex count the vertex-disjoint read passes over an empty
vertex range while both parts occupy every link of one square,
and the content refuses at one loop against two); the
vertex-disjoint read `hd` (the adjacent squares share a rung, the
join keeps one copy of it and the parts' sum prices it twice);
and the two width binders (a key adjoined beyond the region's own
range prices into that part's content while the join reads the
key range alone, each refusal with every co-binder decided).
`sepPlaq`'s separation binder `hs` is load-bearing with its
committed refusal at the once-interposed pair — the interposed
square's boundary reads both loops' neighborhoods, the
conclusion's conjunction decided true there.  Its key binder `hi`
is a frame record, no refusal found: at a key at or beyond the
plaquette count the read is the vacant boundary word, which no
neighborhood meets, so the conclusion holds; probed at the count
itself.
-/

private def R9 : lattice.Region := fiberdec.chainRegion 9
private def FA : fusion.Data places.Shape := fusion.dataA 3

-- the interface's equality-read law at an occupied label, the
-- field's read off the unit
example : FA.eqL [2, 1, 0] [2, 1, 0] = true := FA.eqLRefl [2, 1, 0]

private def cls3 : List (List places.Shape) :=
  [loopAt 9 0, loopAt 9 3, loopAt 9 6]
private def clsW : List (List places.Shape) :=
  [loopAt 9 0, loopAt 9 4, loopAt 9 8]

/-! ### The class's separation and its join -/

example : stableentries.disjSupp FA R9 (loopAt 9 0) (loopAt 9 4) := by
  decide +kernel
example : ¬ stableentries.disjSupp FA R9 (loopAt 9 0) (loopAt 9 8) := by
  decide +kernel

example : allDisj FA R9 (loopAt 9 0) [loopAt 9 3, loopAt 9 6] := by decide +kernel
example : ¬ allDisj FA R9 (loopAt 9 0) [loopAt 9 4, loopAt 9 8] := by
  decide +kernel

example : disjAll FA R9 cls3 := by decide +kernel
example : ¬ disjAll FA R9 clsW := by decide +kernel

example : (carrier.support FA R9 (joinAll FA R9 cls3)).length = 12 := by
  decide +kernel
example : carrier.contentN FA (joinAll FA R9 cls3) = 96 := by decide +kernel
example : carrier.contentN FA (loopAt 9 0) = 32 := by decide +kernel

/-! ### The content at a separated pair -/

example : carrier.contentN FA
      (stableentries.joinConf FA R9 (loopAt 9 0) (loopAt 9 4))
    = carrier.contentN FA (loopAt 9 0)
      + carrier.contentN FA (loopAt 9 4) := by decide +kernel

example : carrier.contentN FA
      (stableentries.joinConf FA R9 (loopAt 9 0) (loopAt 9 4))
    = carrier.contentN FA (loopAt 9 0)
      + carrier.contentN FA (loopAt 9 4) :=
  contentN_join FA R9 (loopAt 9 0) (loopAt 9 4) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-! The vertex-disjoint read's refusal: the adjacent squares share
a rung, the join keeps one copy of it and the parts' sum prices it
twice. -/

example : ¬ stableentries.disjSupp FA R9 (loopAt 9 0) (loopAt 9 1) := by
  decide +kernel
example : ¬ (carrier.contentN FA
      (stableentries.joinConf FA R9 (loopAt 9 0) (loopAt 9 1))
    = carrier.contentN FA (loopAt 9 0)
      + carrier.contentN FA (loopAt 9 1)) := by decide +kernel
example : lattice.wellRead R9 := by decide +kernel
example : (loopAt 9 0).length = R9.links
    ∧ (loopAt 9 1).length = R9.links := by decide +kernel

/-! The shape read's refusal: at the vacant vertex count the
vertex-disjoint read passes over an empty vertex range while one
loop meets itself at every link. -/

private def R9v : lattice.Region := { R9 with verts := 0 }

example : ¬ lattice.wellRead R9v := by decide +kernel
example : stableentries.disjSupp FA R9v (loopAt 9 0) (loopAt 9 0) := by
  decide +kernel
example : (loopAt 9 0).length = R9v.links := by decide +kernel
example : ¬ (carrier.contentN FA
      (stableentries.joinConf FA R9v (loopAt 9 0) (loopAt 9 0))
    = carrier.contentN FA (loopAt 9 0)
      + carrier.contentN FA (loopAt 9 0)) := by decide +kernel

/-! The width binders' refusals: a key adjoined beyond the
region's own range prices into that part's content while the join
reads the key range alone. -/

private def wideA : List places.Shape := loopAt 9 0 ++ [[1, 0, 0]]
private def wideB : List places.Shape := loopAt 9 4 ++ [[1, 0, 0]]

example : ¬ (wideA.length = R9.links) := by decide +kernel
example : stableentries.disjSupp FA R9 wideA (loopAt 9 4)
    ∧ (loopAt 9 4).length = R9.links := by decide +kernel
example : ¬ (carrier.contentN FA
      (stableentries.joinConf FA R9 wideA (loopAt 9 4))
    = carrier.contentN FA wideA
      + carrier.contentN FA (loopAt 9 4)) := by decide +kernel

example : ¬ (wideB.length = R9.links) := by decide +kernel
example : stableentries.disjSupp FA R9 (loopAt 9 0) wideB
    ∧ (loopAt 9 0).length = R9.links := by decide +kernel
example : ¬ (carrier.contentN FA
      (stableentries.joinConf FA R9 (loopAt 9 0) wideB)
    = carrier.contentN FA (loopAt 9 0)
      + carrier.contentN FA wideB) := by decide +kernel

/-! ### The reach at one plaquette -/

example : grading.sepBeyond FA R9 (loopAt 9 0) (loopAt 9 4) := by decide +kernel

example : ((List.range R9.plaqs.length).all (fun i =>
    !(stableentries.nearPlaq FA R9 (loopAt 9 0)
        (ground.getAt [] R9.plaqs i)
      && stableentries.nearPlaq FA R9 (loopAt 9 4)
        (ground.getAt [] R9.plaqs i)))) = true := by decide +kernel

example : ¬ (stableentries.nearPlaq FA R9 (loopAt 9 0)
      (ground.getAt [] R9.plaqs 0) = true
    ∧ stableentries.nearPlaq FA R9 (loopAt 9 4)
      (ground.getAt [] R9.plaqs 0) = true) :=
  sepPlaq FA R9 (loopAt 9 0) (loopAt 9 4) (by decide +kernel) 0

example : ¬ (stableentries.nearPlaq FA R9 (loopAt 9 0)
      (ground.getAt [] R9.plaqs 4) = true
    ∧ stableentries.nearPlaq FA R9 (loopAt 9 4)
      (ground.getAt [] R9.plaqs 4) = true) :=
  sepPlaq FA R9 (loopAt 9 0) (loopAt 9 4) (by decide +kernel) 4

/-! The separation's refusal: the once-interposed pair, whose
interposed square reads both loops' neighborhoods. -/

example : ¬ grading.sepBeyond FA R9 (loopAt 9 0) (loopAt 9 2) := by decide +kernel
example : stableentries.nearPlaq FA R9 (loopAt 9 0)
      (ground.getAt [] R9.plaqs 1) = true
    ∧ stableentries.nearPlaq FA R9 (loopAt 9 2)
      (ground.getAt [] R9.plaqs 1) = true := by decide +kernel
example : 1 < R9.plaqs.length := by decide +kernel

/-! The key binder's frame record: at the plaquette count the read
is the vacant boundary word and no neighborhood meets it. -/

example : ground.getAt [] R9.plaqs R9.plaqs.length
    = ([] : List (Nat × Bool)) := by decide +kernel
example : ¬ (stableentries.nearPlaq FA R9 (loopAt 9 0)
      (ground.getAt [] R9.plaqs R9.plaqs.length) = true
    ∧ stableentries.nearPlaq FA R9 (loopAt 9 4)
      (ground.getAt [] R9.plaqs R9.plaqs.length) = true) := by decide +kernel

/-! ### The relative fibering at the three-key cycle

The fiber slot's carrier is the deck column's base at depth one:
the orbit's own row with the pair base's two rows, three keys
wide.  Its rows pair to `diag(3, 6, 18)`, so the congruence at
`1₂ ⊗ Vᵀ` takes the pencil `X ⊗ 1₃` onto `X ⊗ VVᵀ` — the three
relative fibers, each a scaled copy of `X` — and the wrap shift's
permutation matrix commutes with the pencil on the other slot.
The congruenced datum's committed split reads the six entries
`(6, 12, 36, 30, 60, 180)` at the tensored congruence `T ⊗ 1₃`,
and the three fibers' own splits at `T` read `(6, 30)`,
`(12, 60)` and `(36, 180)`: the whole's reversal count is the
fibers' counts' sum. -/

private def n0 : BPair := BPair.unit
private def n1 : BPair := BPair.ofNat 1
private def n2 : BPair := BPair.ofNat 2
private def n3 : BPair := BPair.ofNat 3
private def n4 : BPair := BPair.ofNat 4
private def n6 : BPair := BPair.ofNat 6
private def n12 : BPair := BPair.ofNat 12
private def n18 : BPair := BPair.ofNat 18
private def n30 : BPair := BPair.ofNat 30
private def n36 : BPair := BPair.ofNat 36
private def n60 : BPair := BPair.ofNat 60
private def n180 : BPair := BPair.ofNat 180
private def nm1 : BPair := (BPair.ofNat 1).swap

private def xX : Mat := [[n2, n1], [n1, n3]]
private def fibV : Mat := fiberdec.orbitSum 1 :: fiberdec.pairBase 1
private def pP : Mat := fiberdec.permMatAt 3 (fiberdec.tShift 1)
private def dD : Mat := [[n3, n0, n0], [n0, n6, n0], [n0, n0, n18]]
private def tT : Mat := [[n1, nm1], [n0, n2]]
private def tTw : Mat := [[n2, n1], [n0, n1]]

example : matOneValue (matMul fibV (transposeM fibV)) dD := by decide +kernel

example : matOneValue
    (matMul (tensorM xX (inertia.idMat 3)) (tensorM (inertia.idMat 2) pP))
    (matMul (tensorM (inertia.idMat 2) pP)
      (tensorM xX (inertia.idMat 3))) :=
  comm_shift 2 3 xX pP (by decide +kernel) (by decide +kernel)

example : matOneValue
    (matMul (tensorM xX (inertia.idMat 3)) (tensorM (inertia.idMat 2) pP))
    (matMul (tensorM (inertia.idMat 2) pP)
      (tensorM xX (inertia.idMat 3))) := by decide +kernel

example : matOneValue
    (matMul (transposeM (tensorM (inertia.idMat 2) (transposeM fibV)))
      (matMul (tensorM xX (inertia.idMat 3))
        (tensorM (inertia.idMat 2) (transposeM fibV))))
    (tensorM (matMul (transposeM (inertia.idMat 2)) (matMul xX (inertia.idMat 2)))
      (matMul (transposeM (transposeM fibV))
        (matMul (inertia.idMat 3) (transposeM fibV)))) :=
  congr_tensorM 2 3 2 3 xX (inertia.idMat 3) (inertia.idMat 2)
    (transposeM fibV) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

example : matOneValue
    (matMul (transposeM (tensorM (inertia.idMat 2) (transposeM fibV)))
      (matMul (tensorM xX (inertia.idMat 3))
        (tensorM (inertia.idMat 2) (transposeM fibV))))
    (tensorM xX dD) := by decide +kernel

private def spWhole : inertia.Split 6 :=
  ⟨⟨tensorM tT (inertia.idMat 3), rfl⟩,
   ⟨tensorM (inertia.matScaleB n4 tTw) (inertia.idMat 3), rfl⟩,
   [.one n6, .one n12, .one n36, .one n30, .one n60, .one n180], 0, rfl⟩

private def spF1 : inertia.Split 2 :=
  ⟨⟨tT, rfl⟩, ⟨tTw, rfl⟩, [.one n6, .one n30], 0, rfl⟩
private def spF2 : inertia.Split 2 :=
  ⟨⟨tT, rfl⟩, ⟨tTw, rfl⟩, [.one n12, .one n60], 0, rfl⟩
private def spF3 : inertia.Split 2 :=
  ⟨⟨tT, rfl⟩, ⟨tTw, rfl⟩, [.one n36, .one n180], 0, rfl⟩

example : inertia.splitRead (tensorM xX dD) spWhole := by decide +kernel
example : inertia.splitRead (inertia.matScaleB n3 xX) spF1 := by decide +kernel
example : inertia.splitRead (inertia.matScaleB n6 xX) spF2 := by decide +kernel
example : inertia.splitRead (inertia.matScaleB n18 xX) spF3 := by decide +kernel

example : inertia.revAt spWhole
    = inertia.revAt spF1 + inertia.revAt spF2 + inertia.revAt spF3 := by
  decide +kernel

example : inertia.psdAt spWhole := by decide +kernel

/-! ### The folds over a separated class

`contentN_joinAll` and `fibProd_joinAll` at the three-apart class,
each through the theorem with its kernel twin, and the refusals:
the pairwise-separation binder at the wrapped class (the ring's
squares zero and eight touch); the width fold and the shape read
at their own committed section below, each load-bearing at the
content fold, the fiber fold's binder set free of the shape read.
The unit's own equality read is the interface's `eqLRefl` field,
so an interface refusing a label against itself admits no
instantiation, the forged datum off the carrier. -/

example : carrier.contentN FA (joinAll FA R9 cls3)
    = ground.sumNat (cls3.map (carrier.contentN FA)) := by decide +kernel

example : carrier.contentN FA (joinAll FA R9 cls3)
    = ground.sumNat (cls3.map (carrier.contentN FA)) :=
  contentN_joinAll FA R9 (by decide +kernel) cls3 (by decide +kernel)
    (by decide +kernel)

example : windowfinite.fibProd FA R9 (joinAll FA R9 cls3)
    = (cls3.map (windowfinite.fibProd FA R9)).foldl (· * ·) 1 := by
  decide +kernel

example : windowfinite.fibProd FA R9 (joinAll FA R9 cls3)
    = (cls3.map (windowfinite.fibProd FA R9)).foldl (· * ·) 1 :=
  fibProd_joinAll FA R9 cls3 (by decide +kernel)

example : ¬ (carrier.contentN FA (joinAll FA R9 clsW)
    = ground.sumNat (clsW.map (carrier.contentN FA))) := by decide +kernel
example : ¬ (windowfinite.fibProd FA R9 (joinAll FA R9 clsW)
    = (clsW.map (windowfinite.fibProd FA R9)).foldl (· * ·) 1) := by
  decide +kernel
example : (clsW.all (fun c => c.length == R9.links)) = true := by
  decide +kernel

private def RD : lattice.Region :=
  { links := 4, verts := 4, tail := [0,1,2,3], head := [1,2,3,0],
    plaqs := [[(0,true),(1,true),(2,true),(3,true)]],
    color := [true,false,true,false] , tailLen := rfl, headLen := rfl }

example : lattice.wellRead RD := by decide +kernel

/-! ### The stencil row at a separated spectator

`plaqRow_join` at the fundamental loop pair: the moved square's row
target counts one at the join with the spectator riding, through
the theorem and at the kernel.  The refusals, each isolating one
binder with every co-binder decided beside it: the spectator's
occupancy (`hob`, the single-link spectator empties the joined
row), the target's occupancy (`htn`, the adjoint loop's one-move
annihilation collides the vacuum's overlay with the border
target), the target-spectator separation (`hd2`, the copy of one
spectator link mimics the border target), the unit-class fold
(`hsnd`, the interface conflating a label with the unit leaks the
spectator into the join), and the target's width (`htl`).  The
shape read (`hw`) is load-bearing: a partial vertex truncation
hides the moved part's overlap with the spectator, the refusal at
its own committed section below.  The moved-part separation
(`hd`) is load-bearing there as well, the overlapped moved part
its refusal.  The moved-part width (`ha`) and the spectator's
width (`hb`) are frame records: the widened lists' extra keys sit
beyond the fold's range and the incidence alike, the searches'
shapes committed as standing pins.  The `hfar` binder is the
route's own: at a spectator-adjacent plaquette every genuinely
moved target meets the spectator's support, so its refusals
co-refuse `hd2` (the joint record below). -/

private def p0R : List (Nat × Bool) := ground.getAt [] R9.plaqs 0

private def tGood : List places.Shape := loopConf 9 0 [2, 1, 0] [1, 2, 0]
private def thetaLoop : List places.Shape := E0.moduleConf FA R9 p0R
private def tVac : List places.Shape :=
  List.replicate R9.links ([0, 0, 0] : places.Shape)
private def tAdv : List places.Shape :=
  (List.range R9.links).map (fun l =>
    if l == 4 then ground.getAt ([0,0,0] : places.Shape) (loopAt 9 4) 4
    else [0, 0, 0])
private def bU : List places.Shape :=
  (List.range R9.links).map (fun l =>
    if l == 4 then [1, 0, 0] else [0, 0, 0])

/-! The committed rows, the tier's fixtures: `plaqRow`'s value at
the shared source configurations, each pin one kernel walk of the
row in the module, the consuming batteries' reads rewrites at the
literal, `tGood`'s committed value the row's own head. -/

private def row00 : List (List places.Shape) :=
  [loopConf 9 0 [2, 1, 0] [1, 2, 0], loopConf 9 0 [0, 2, 0] [2, 0, 0],
   loopAt 9 0]

private theorem row00_pin :
    algebra.plaqRow FA R9 p0R (loopAt 9 0) = row00 := by decide +kernel

example : tGood
    = ground.getAt [] (algebra.plaqRow FA R9 p0R (loopAt 9 0)) 0 := by
  rw [row00_pin]; decide +kernel

private def rowTh : List (List places.Shape) :=
  [loopConf 9 0 [2, 2, 0] [2, 2, 0], loopConf 9 0 [0, 3, 0] [3, 0, 0],
   loopConf 9 0 [3, 0, 0] [0, 3, 0], loopConf 9 0 [1, 1, 0] [1, 1, 0]]

private theorem rowTh_pin :
    algebra.plaqRow FA R9 p0R thetaLoop = rowTh := by decide +kernel

private def rowJ0 : List (List places.Shape) :=
  row00.map (fun c => stableentries.joinConf FA R9 c (loopAt 9 4))

private theorem rowJ0_pin :
    algebra.plaqRow FA R9 p0R
      (stableentries.joinConf FA R9 (loopAt 9 0) (loopAt 9 4))
    = rowJ0 := by decide +kernel

private def rowThJ : List (List places.Shape) :=
  rowTh.map (fun c => stableentries.joinConf FA R9 c (loopAt 9 4))
    ++ [loopAt 9 4]

private theorem rowThJ_pin :
    algebra.plaqRow FA R9 p0R
      (stableentries.joinConf FA R9 thetaLoop (loopAt 9 4))
    = rowThJ := by decide +kernel

example : ground.countOf
      (stableentries.joinConf FA R9 tGood (loopAt 9 4))
      (algebra.plaqRow FA R9 p0R
        (stableentries.joinConf FA R9 (loopAt 9 0) (loopAt 9 4)))
    = ground.countOf tGood (algebra.plaqRow FA R9 p0R (loopAt 9 0)) := by
  rw [rowJ0_pin, row00_pin]; decide +kernel

example : ground.countOf
      (stableentries.joinConf FA R9 tGood (loopAt 9 4))
      (algebra.plaqRow FA R9 p0R
        (stableentries.joinConf FA R9 (loopAt 9 0) (loopAt 9 4)))
    = ground.countOf tGood (algebra.plaqRow FA R9 p0R (loopAt 9 0)) :=
  plaqRow_join FA R9 p0R (loopAt 9 0) (loopAt 9 4) tGood (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The adjoint loop's border target: the one-move annihilation
exists there, the join's row exceeding the moved part's by one. -/

example : (algebra.plaqRow FA R9 p0R thetaLoop).length = 4 := by
  rw [rowTh_pin]; decide +kernel
example : (algebra.plaqRow FA R9 p0R
    (stableentries.joinConf FA R9 thetaLoop (loopAt 9 4))).length = 5 := by
  rw [rowThJ_pin]; decide +kernel

/-! The spectator-occupancy refusal (`hob`). -/

example : ¬ (carrier.occupied FA R9 bU = true) := by decide +kernel
example : stableentries.disjSupp FA R9 (loopAt 9 0) bU := by decide +kernel
example : stableentries.disjSupp FA R9 tGood bU := by decide +kernel
example : stableentries.nearPlaq FA R9 bU p0R = false := by decide +kernel
example : ¬ (ground.countOf (stableentries.joinConf FA R9 tGood bU)
      (algebra.plaqRow FA R9 p0R
        (stableentries.joinConf FA R9 (loopAt 9 0) bU))
    = ground.countOf tGood
        (algebra.plaqRow FA R9 p0R (loopAt 9 0))) := by
  rw [row00_pin]; decide +kernel

/-! The target-occupancy refusal (`htn`) at the adjoint loop. -/

example : ¬ ((tVac.any (fun m => !(FA.eqL m FA.unit))) = true) := by
  decide +kernel
example : stableentries.disjSupp FA R9 tVac (loopAt 9 4) := by decide +kernel
example : ¬ (ground.countOf
      (stableentries.joinConf FA R9 tVac (loopAt 9 4))
      (algebra.plaqRow FA R9 p0R
        (stableentries.joinConf FA R9 thetaLoop (loopAt 9 4)))
    = ground.countOf tVac
        (algebra.plaqRow FA R9 p0R thetaLoop)) := by
  rw [rowThJ_pin, rowTh_pin]; decide +kernel

/-! The separation refusal (`hd2`): the copy of one spectator link. -/

example : ¬ stableentries.disjSupp FA R9 tAdv (loopAt 9 4) := by decide +kernel
example : (tAdv.any (fun m => !(FA.eqL m FA.unit))) = true := by decide +kernel
example : ((thetaLoop ++ loopAt 9 4 ++ tAdv
    ++ (List.range R9.links).flatMap
      (fun k => algebra.linkTargets FA p0R thetaLoop k)).all
  (fun m => (!(FA.eqL m FA.unit)) || (m == FA.unit))) = true := by decide +kernel
example : ¬ (ground.countOf
      (stableentries.joinConf FA R9 tAdv (loopAt 9 4))
      (algebra.plaqRow FA R9 p0R
        (stableentries.joinConf FA R9 thetaLoop (loopAt 9 4)))
    = ground.countOf tAdv
        (algebra.plaqRow FA R9 p0R thetaLoop)) := by
  rw [rowThJ_pin, rowTh_pin]; decide +kernel

/-! The unit-class fold's refusal (`hsnd`): an interface conflating
the label five with the unit reads the spectator unoccupied and
separated while its labels move the join's row. -/

private def FD : fusion.Data Nat :=
  ⟨(fun x y => (if x == 5 then 0 else x) == (if y == 5 then 0 else y)),
   (fun _ => ground.eqBeqOf rfl),
   0, (fun x => x), (fun x y => x + y), 1,
   (fun _ _ _ => 1), (fun x _ => if x == 5 then [7] else [3]),
   (fun _ => 1), (fun _ => 1), 1, 1, (fun _ => []),
   (fun _ => 0), (fun _ _ => 0), (fun _ => 0)⟩

example : ¬ fusion.oneUnit FD (([0,0,0,0] : List Nat) ++ [5,5,5,5]
    ++ [3,3,3,3] ++ (List.range RD.links).flatMap
      (fun k => algebra.linkTargets FD (ground.getAt [] RD.plaqs 0)
        [0,0,0,0] k)) := by
  decide +kernel
example : stableentries.disjSupp FD RD [0,0,0,0] [5,5,5,5] := by decide +kernel
example : stableentries.disjSupp FD RD [3,3,3,3] [5,5,5,5] := by decide +kernel
example : stableentries.nearPlaq FD RD [5,5,5,5]
    (ground.getAt [] RD.plaqs 0) = false := by decide +kernel
example : carrier.occupied FD RD [5,5,5,5] = true := by decide +kernel
example : (([3,3,3,3] : List Nat).any
    (fun m => !(FD.eqL m FD.unit))) = true := by decide +kernel
example : ¬ (ground.countOf
      (stableentries.joinConf FD RD [3,3,3,3] [5,5,5,5])
      (algebra.plaqRow FD RD (ground.getAt [] RD.plaqs 0)
        (stableentries.joinConf FD RD [0,0,0,0] [5,5,5,5]))
    = ground.countOf ([3,3,3,3] : List Nat)
        (algebra.plaqRow FD RD (ground.getAt [] RD.plaqs 0)
          [0,0,0,0])) := by decide +kernel

/-! The width refusal (`htl`) and the two frame records. -/

example : ¬ (ground.countOf
      (stableentries.joinConf FA R9 (tGood ++ [[1,0,0]]) (loopAt 9 4))
      (algebra.plaqRow FA R9 p0R
        (stableentries.joinConf FA R9 (loopAt 9 0) (loopAt 9 4)))
    = ground.countOf (tGood ++ [[1,0,0]])
        (algebra.plaqRow FA R9 p0R (loopAt 9 0))) := by
  rw [rowJ0_pin, row00_pin]; decide +kernel
example : ground.countOf
      (stableentries.joinConf FA R9 tGood (loopAt 9 4))
      (algebra.plaqRow FA R9 p0R (stableentries.joinConf FA R9
        (loopAt 9 0 ++ [[1,0,0]]) (loopAt 9 4)))
    = ground.countOf tGood (algebra.plaqRow FA R9 p0R
        (loopAt 9 0 ++ [[1,0,0]])) := by decide +kernel
example : ground.countOf
      (stableentries.joinConf FA R9v tGood (loopAt 9 4))
      (algebra.plaqRow FA R9v p0R
        (stableentries.joinConf FA R9v (loopAt 9 0) (loopAt 9 4)))
    = ground.countOf tGood
        (algebra.plaqRow FA R9v p0R (loopAt 9 0)) := by decide +kernel

/-! The joint `hfar` record: at the spectator's own plaquette the
conclusion refuses with the separation refused beside it, every
genuinely moved target meeting the spectator's support. -/

private def p4R : List (Nat × Bool) := ground.getAt [] R9.plaqs 4
private def tG4 : List places.Shape :=
  stableentries.joinConf FA R9 (loopAt 9 0) (E0.moduleConf FA R9 p4R)

private theorem row4_pin :
    algebra.plaqRow FA R9 p4R (loopAt 9 0) = [tG4] := by decide +kernel

example : tG4
    = ground.getAt [] (algebra.plaqRow FA R9 p4R (loopAt 9 0)) 0 := by
  rw [row4_pin]; decide +kernel

example : stableentries.nearPlaq FA R9 (loopAt 9 4) p4R = true := by
  decide +kernel
example : ¬ stableentries.disjSupp FA R9 tG4 (loopAt 9 4) := by decide +kernel
example : ¬ (ground.countOf
      (stableentries.joinConf FA R9 tG4 (loopAt 9 4))
      (algebra.plaqRow FA R9 p4R
        (stableentries.joinConf FA R9 (loopAt 9 0) (loopAt 9 4)))
    = ground.countOf tG4
        (algebra.plaqRow FA R9 p4R (loopAt 9 0))) := by
  rw [row4_pin]; decide +kernel

/-! ### The review's absorbed classifications

The shape read (`hw`) at the row transport is load-bearing: a
partial vertex truncation hides the moved part's overlap with the
spectator, every co-binder standing and the transport refused.  The
moved-part separation (`hd`) is load-bearing at the untruncated
region: the moved part overlapping the spectator, the join's row
keeps a target the moved part's row misses.  The spectator's width
(`hb`) is a frame record: the widened spectator's extra key sits
beyond the incidence and the join alike, the display standing. -/

private def R9k : lattice.Region := { R9 with verts := 4 }
private def aOv : List places.Shape :=
  stableentries.joinConf FA R9 (loopAt 9 0) (loopAt 9 4)

private theorem rowJ0a_pin :
    algebra.plaqRow FA R9 p0R aOv = rowJ0 := rowJ0_pin

example : ¬ lattice.wellRead R9k := by decide +kernel
example : stableentries.disjSupp FA R9k aOv (loopAt 9 4) := by decide +kernel
example : stableentries.disjSupp FA R9k tGood (loopAt 9 4) := by decide +kernel
example : stableentries.nearPlaq FA R9k (loopAt 9 4) p0R = false := by
  decide +kernel
example : carrier.occupied FA R9k (loopAt 9 4) = true := by decide +kernel
example : ¬ (ground.countOf
      (stableentries.joinConf FA R9k tGood (loopAt 9 4))
      (algebra.plaqRow FA R9k p0R
        (stableentries.joinConf FA R9k aOv (loopAt 9 4)))
    = ground.countOf tGood
        (algebra.plaqRow FA R9k p0R aOv)) := by decide +kernel

example : ¬ stableentries.disjSupp FA R9 aOv (loopAt 9 4) := by decide +kernel
example : ((aOv ++ loopAt 9 4 ++ tGood
    ++ (List.range R9.links).flatMap
      (fun k => algebra.linkTargets FA p0R aOv k)).all
  (fun m => (!(FA.eqL m FA.unit)) || (m == FA.unit))) = true := by
  decide +kernel
example : ¬ (ground.countOf
      (stableentries.joinConf FA R9 tGood (loopAt 9 4))
      (algebra.plaqRow FA R9 p0R
        (stableentries.joinConf FA R9 aOv (loopAt 9 4)))
    = ground.countOf tGood
        (algebra.plaqRow FA R9 p0R aOv)) := by
  rw [rowJ0a_pin]; decide +kernel

private def bWide : List places.Shape := loopAt 9 4 ++ [[1,0,0]]

example : ground.countOf
      (stableentries.joinConf FA R9 tGood bWide)
      (algebra.plaqRow FA R9 p0R
        (stableentries.joinConf FA R9 (loopAt 9 0) bWide))
    = ground.countOf tGood
        (algebra.plaqRow FA R9 p0R (loopAt 9 0)) := by
  rw [row00_pin]; decide +kernel

/-! The class folds' further binders.  The width fold (`hlen`) is
load-bearing: a widened member prices its adjoined key into the
part alone.  The shape read (`hw`) is load-bearing at the vacant
vertex count: the pairwise separation passes over the vacant range
while the members meet at every link.  The fiber fold at the same
forgery stands, its binder set free of the shape read. -/

private def csW : List (List places.Shape) :=
  [loopAt 9 0 ++ [[1,0,0]], loopAt 9 4]
private def csV : List (List places.Shape) :=
  [loopAt 9 0, loopAt 9 0]

example : disjAll FA R9 csW := by decide +kernel
example : ¬ ((csW.all (fun c => c.length == R9.links)) = true) := by
  decide +kernel
example : ¬ (carrier.contentN FA (joinAll FA R9 csW)
    = ground.sumNat (csW.map (carrier.contentN FA))) := by decide +kernel

example : disjAll FA R9v csV := by decide +kernel
example : (csV.all (fun c => c.length == R9v.links)) = true := by decide +kernel
example : ¬ (carrier.contentN FA (joinAll FA R9v csV)
    = ground.sumNat (csV.map (carrier.contentN FA))) := by decide +kernel
example : windowfinite.fibProd FA R9v (joinAll FA R9v csV)
    = (csV.map (windowfinite.fibProd FA R9v)).foldl (· * ·) 1 := by
  decide +kernel

/-! The clearance's gram positivity (`hgp`) is load-bearing: at an
indefinite gram every co-binder stands and the sector's datum reads
three reversals.  The form transports' binder sets classify with
it: the partner-form positivity (`hXpos`) and the gram's
positivity (`hp`) are load-bearing at the one-key instances below,
the transported form reading its lower side at the refused binder
with every co-binder standing; the shape and split reads
(`sqAt`, `splitRead`, the width frames, and `bottomClear`'s
level data) are coherence binders discharged per instance by
`decide`, the `grading.deepRow` precedent's category. -/

private def w3p : BPair := ⟨4, 1⟩
private def gI : elim.Mat := [[w1, w0], [w0, wm1]]
private def hI : elim.Mat := [[w2, w0], [w0, w0]]
private def spGi : inertia.Split 2 :=
  ⟨⟨inertia.idMat 2, by decide +kernel⟩, ⟨inertia.idMat 2, by decide +kernel⟩,
   [.one w1, .one wm1], 0, rfl⟩
private def spFi : inertia.Split 2 :=
  ⟨⟨inertia.idMat 2, by decide +kernel⟩, ⟨inertia.idMat 2, by decide +kernel⟩,
   [.one w1, .one w1], 0, rfl⟩
private def spSi : inertia.Split 4 :=
  ⟨⟨inertia.idMat 4, by decide +kernel⟩, ⟨inertia.idMat 4, by decide +kernel⟩,
   [.one w3p, .one wm1, .one wm1, .one wm1], 0, rfl⟩

example : inertia.splitRead gI spGi := by decide +kernel
example : (spGi.blocks.all (fun b => b.order == 1)) = true := by decide +kernel
example : ¬ inertia.psdAt spGi := by decide +kernel
example : inertia.splitRead (inertia.siteDatum
    (matAdd hI (inertia.matScale 1 gI)) (inertia.matScale 2 gI))
    spFi := by decide +kernel
example : inertia.psdAt spFi := by decide +kernel
example : inertia.splitRead (inertia.siteDatum
    (matAdd (sumPencil hI gI 2) (inertia.matScale 1 (tensorPow gI 2)))
    (inertia.matScale 2 (tensorPow gI 2))) spSi := by decide +kernel
example : ¬ inertia.psdAt spSi := by decide +kernel
example : inertia.revAt spSi = 3 := by decide +kernel

private def spOne : inertia.Split 1 :=
  ⟨⟨[[w1]], rfl⟩, ⟨[[w1]], rfl⟩, [.one w1], 0, rfl⟩
private def spNegOne : inertia.Split 1 :=
  ⟨⟨[[w1]], rfl⟩, ⟨[[w1]], rfl⟩, [.one wm1], 0, rfl⟩

example : inertia.splitRead [[w1]] spOne := by decide +kernel
example : inertia.splitRead [[wm1]] spNegOne := by decide +kernel
example : ¬ inertia.psdAt spNegOne := by decide +kernel
example : ¬ (¬ (inertia.quadForm (tensorM [[w1]] [[wm1]]) [w1]
    < BPair.unit)) := by decide +kernel
example : ¬ (¬ (inertia.quadForm (tensorM [[wm1]] [[w1]]) [w1]
    < BPair.unit)) := by decide +kernel

/-! The fibering pin at an indefinite internal datum: the whole's
reversal count is the fibers' counts' sum with both sides
occupied. -/

private def w6p : BPair := ⟨7, 1⟩
private def w18p : BPair := ⟨19, 1⟩
private def dD3 : elim.Mat := [[w3p, w0, w0], [w0, w6p, w0],
  [w0, w0, w18p]]
private def spWI : inertia.Split 6 :=
  ⟨⟨inertia.idMat 6, by decide +kernel⟩, ⟨inertia.idMat 6, by decide +kernel⟩,
   [.one w3p, .one w6p, .one w18p, .one ⟨1, 4⟩, .one ⟨1, 7⟩,
    .one ⟨1, 19⟩], 0, rfl⟩
private def spI1 : inertia.Split 2 :=
  ⟨⟨inertia.idMat 2, by decide +kernel⟩, ⟨inertia.idMat 2, by decide +kernel⟩,
   [.one w3p, .one ⟨1, 4⟩], 0, rfl⟩
private def spI2 : inertia.Split 2 :=
  ⟨⟨inertia.idMat 2, by decide +kernel⟩, ⟨inertia.idMat 2, by decide +kernel⟩,
   [.one w6p, .one ⟨1, 7⟩], 0, rfl⟩
private def spI3 : inertia.Split 2 :=
  ⟨⟨inertia.idMat 2, by decide +kernel⟩, ⟨inertia.idMat 2, by decide +kernel⟩,
   [.one w18p, .one ⟨1, 19⟩], 0, rfl⟩

example : inertia.splitRead (tensorM gI dD3) spWI := by decide +kernel
example : inertia.splitRead
    (inertia.matScaleB (BPair.ofNat 3) gI) spI1 := by decide +kernel
example : inertia.splitRead
    (inertia.matScaleB (BPair.ofNat 6) gI) spI2 := by decide +kernel
example : inertia.splitRead
    (inertia.matScaleB (BPair.ofNat 18) gI) spI3 := by decide +kernel
example : inertia.revAt spWI
    = inertia.revAt spI1 + inertia.revAt spI2 + inertia.revAt spI3 := by
  decide +kernel
example : inertia.revAt spWI = 3 := by decide +kernel
