import MassGap.Drift
/-!
The check module for `thm:drift`: the uniform drift applied whole
at committed labels of the width, the summed recursion routed at
small shapes with one value-level twin, the strictness read at two
occupied reduced shapes, and the recursion display's reindexed
pair weights at committed contents.

The theorem's route binds no reduction — the drift reads at an
unreduced label exactly as at its reduced representative, `[1, 2]`
against `[1, 0]` at the two-letter data — while both stated
binders are load-bearing at committed refusals.  The width binder
refuses at a two-letter label read against the three-letter data,
where the row is taken against the wrong adjoint.  The width floor
refuses at the one-letter data, whose adjoint row carries the unit
label alone with vacant cleared Casimir while the display's right
side is the doubled fundamental square: the two sides part at
`0 = 2`.

The strictness read's two binders are load-bearing at the two
dimension-one shapes.  The unreduced unit-class label `[0, 2]`
reduces to the unit shape `[0, 0]` and carries dimension one, so
the reduction binder discriminates; the unit shape `[0, 0, 0]` is
its own reduction at vacant degree and carries dimension one, so
the occupancy binder does.

The pair weights discriminate against one another at a three-place
content: over the strictly ordered place pairs `wCross` folds the
pair's product and `wSqP` its first place's square, so `[2, 1, 0]`
reads `2` against `9` while the two-place content `[3, 1]`, whose
one pair holds the whole content, reads `3` against `9`.
-/
open ground

/-! ## The row read at committed labels

The display applied whole at labels of the data's own width — the
`θ` instance `[1, 1, 0]` at its own shape with the two-row crown
`[2, 1, 0]` beside it — and at an unreduced label, the statement
binding no reduction, with the same unreduced instance decided
beside its route. -/

example : fusion.driftLaw (fusion.dataA 2) [1, 0] :=
  drift.readAll 2 (by decide +kernel) [1, 0] rfl

example : fusion.driftLaw (fusion.dataA 3) [1, 1, 0] :=
  drift.readAll 3 (by decide +kernel) [1, 1, 0] rfl

example : fusion.driftLaw (fusion.dataA 3) [2, 1, 0] :=
  drift.readAll 3 (by decide +kernel) [2, 1, 0] rfl

example : fusion.driftLaw (fusion.dataA 2) [1, 2] :=
  drift.readAll 2 (by decide +kernel) [1, 2] rfl

example : fusion.driftLaw (fusion.dataA 2) [1, 2] := by decide +kernel

/-! ## The binder refusals

The width binder at a label short of the data's rank, and the
width floor at the one-letter data at both of its small labels. -/

example : ¬ fusion.driftLaw (fusion.dataA 3) [1, 0] := by decide +kernel
example : ¬ fusion.driftLaw (fusion.dataA 1) [0] := by decide +kernel
example : ¬ fusion.driftLaw (fusion.dataA 1) [1] := by decide +kernel

/-! ## The summed recursion

The trace recursion summed over the block's occupancy family: the
top's square against the span's length with the cross weights'
doubled fold on the left, the shifted squares against the square
weights' doubled fold on the right.  Routed at two occupied shapes
and at the vacant shape, where both sides collapse to the unit
span's own read, with one value-level twin pinning the identity
independently of the theorem. -/

example : weylchar.stdSq (places.display [1, 0])
      * (blockcount.blockSpan [1, 0]).length
    + 2 * ground.famFold Nat.add 0 (fun v => drift.wCross v.content)
        (blockcount.blockSpan [1, 0])
  = ground.famFold Nat.add 0
      (fun v => weylchar.stdSq (List.zipWith (fun a b => a + b)
        v.content (places.unitDisp ([1, 0] : List Nat).length)))
      (blockcount.blockSpan [1, 0])
    + 2 * ground.famFold Nat.add 0 (fun v => drift.wSqP v.content)
        (blockcount.blockSpan [1, 0]) := drift.sumRec [1, 0]

example : weylchar.stdSq (places.display [1, 0])
      * (blockcount.blockSpan [1, 0]).length
    + 2 * ground.famFold Nat.add 0 (fun v => drift.wCross v.content)
        (blockcount.blockSpan [1, 0])
  = ground.famFold Nat.add 0
      (fun v => weylchar.stdSq (List.zipWith (fun a b => a + b)
        v.content (places.unitDisp ([1, 0] : List Nat).length)))
      (blockcount.blockSpan [1, 0])
    + 2 * ground.famFold Nat.add 0 (fun v => drift.wSqP v.content)
        (blockcount.blockSpan [1, 0]) := by decide +kernel

example : weylchar.stdSq (places.display [2, 0])
      * (blockcount.blockSpan [2, 0]).length
    + 2 * ground.famFold Nat.add 0 (fun v => drift.wCross v.content)
        (blockcount.blockSpan [2, 0])
  = ground.famFold Nat.add 0
      (fun v => weylchar.stdSq (List.zipWith (fun a b => a + b)
        v.content (places.unitDisp ([2, 0] : List Nat).length)))
      (blockcount.blockSpan [2, 0])
    + 2 * ground.famFold Nat.add 0 (fun v => drift.wSqP v.content)
        (blockcount.blockSpan [2, 0]) := drift.sumRec [2, 0]

example : weylchar.stdSq (places.display ([] : List Nat))
      * (blockcount.blockSpan []).length
    + 2 * ground.famFold Nat.add 0 (fun v => drift.wCross v.content)
        (blockcount.blockSpan [])
  = ground.famFold Nat.add 0
      (fun v => weylchar.stdSq (List.zipWith (fun a b => a + b)
        v.content (places.unitDisp ([] : List Nat).length)))
      (blockcount.blockSpan [])
    + 2 * ground.famFold Nat.add 0 (fun v => drift.wSqP v.content)
        (blockcount.blockSpan []) := drift.sumRec []

/-! ## The strictness read

A reduced occupied shape's dimension clears one, routed at the
fundamental and at the two-letter-gap shape, with both binders
refused at the dimension-one shapes: the unreduced unit-class
label and the unit shape. -/

example : 2 ≤ weyldim.dimOf [1, 0] := drift.strict [1, 0] rfl (by decide +kernel)
example : 2 ≤ weyldim.dimOf [2, 1, 0] := drift.strict [2, 1, 0] rfl (by decide +kernel)

example : ¬ 2 ≤ weyldim.dimOf [0, 2] := by decide +kernel
example : ¬ 2 ≤ weyldim.dimOf [0, 0, 0] := by decide +kernel

/-! ## The reindexed pair weights

The pair's product and its first place's square, each folded over
the width's strictly ordered place pairs, at a two-place and a
three-place content. -/

example : drift.wCross [3, 1] = 3 := by decide +kernel
example : drift.wSqP [3, 1] = 9 := by decide +kernel
example : drift.wCross [2, 1, 0] = 2 := by decide +kernel
example : drift.wSqP [2, 1, 0] = 9 := by decide +kernel
