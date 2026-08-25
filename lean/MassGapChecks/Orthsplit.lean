import MassGap.Orthsplit
import MassGap.Fusiondata
/-!
The check module for `lem:orthsplit`: the complement invariance
pinned at the swap operator on two letters — the invariant row
`[1, 1]` kept by the swap, the perpendicular `[1, -1]` with its
swapped image perpendicular, `perp_invariant` applied whole at the
two groups coinciding — and the invariance refusal: at the first
coordinate line, kept by no swap, the perpendicular's image pairs
off the unit.  The cross-content pin closes the module: at a
stated top's closure pool the two groups are the source and the
moved content's own, the letter-pair unit and its transpose
partner the operator pair, and the residual member's image reads
the sum's unit against every moved row.
-/

open ground

/-- The committed instance: the swap's transpose partner keeps the
diagonal row's span, the perpendicular's adjoint read, and the
perpendicular read. -/
example : (∀ k, k < [[BPair.ofNat 1, BPair.ofNat 1]].length →
      (elim.dotP
        (elim.matVec [[BPair.unit, BPair.ofNat 1],
          [BPair.ofNat 1, BPair.unit]]
          [BPair.ofNat 1, (BPair.ofNat 1).swap])
        (ground.getAt [] [[BPair.ofNat 1, BPair.ofNat 1]]
          k)).oneValue
      (elim.dotP [BPair.ofNat 1, (BPair.ofNat 1).swap]
        (elim.matVec [[BPair.unit, BPair.ofNat 1],
          [BPair.ofNat 1, BPair.unit]]
          (ground.getAt [] [[BPair.ofNat 1, BPair.ofNat 1]] k))))
    ∧ (∀ k, k < [[BPair.ofNat 1, BPair.ofNat 1]].length →
      elim.spanRel 2 [[BPair.ofNat 1, BPair.ofNat 1]]
        (elim.matVec [[BPair.unit, BPair.ofNat 1],
          [BPair.ofNat 1, BPair.unit]]
          (ground.getAt [] [[BPair.ofNat 1, BPair.ofNat 1]] k)))
    ∧ (∀ k, k < [[BPair.ofNat 1, BPair.ofNat 1]].length →
      (elim.dotP [BPair.ofNat 1, (BPair.ofNat 1).swap]
        (ground.getAt [] [[BPair.ofNat 1, BPair.ofNat 1]]
          k)).oneValue BPair.unit) := by decide +kernel

/-- The committed instance reads `perp_invariant` applied whole,
the two content groups coinciding at the diagonal. -/
example : ∀ k, k < [[BPair.ofNat 1, BPair.ofNat 1]].length →
    (elim.dotP
      (elim.matVec [[BPair.unit, BPair.ofNat 1],
        [BPair.ofNat 1, BPair.unit]]
        [BPair.ofNat 1, (BPair.ofNat 1).swap])
      (ground.getAt [] [[BPair.ofNat 1, BPair.ofNat 1]]
        k)).oneValue BPair.unit :=
  orthsplit.perp_invariant 2
    [[BPair.unit, BPair.ofNat 1], [BPair.ofNat 1, BPair.unit]]
    [[BPair.unit, BPair.ofNat 1], [BPair.ofNat 1, BPair.unit]]
    [[BPair.ofNat 1, BPair.ofNat 1]]
    [[BPair.ofNat 1, BPair.ofNat 1]]
    [BPair.ofNat 1, (BPair.ofNat 1).swap]
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The invariance binder is load-bearing: at the first coordinate
line the swap's image leaves the span — the adjoint and
perpendicular reads hold, the invariance refuses, and the
conclusion refuses with it. -/
example : ¬ (∀ k, k < [[BPair.ofNat 1, BPair.unit]].length →
    elim.spanRel 2 [[BPair.ofNat 1, BPair.unit]]
      (elim.matVec [[BPair.unit, BPair.ofNat 1],
        [BPair.ofNat 1, BPair.unit]]
        (ground.getAt [] [[BPair.ofNat 1, BPair.unit]] k)))
  := by decide +kernel

example : (∀ k, k < [[BPair.ofNat 1, BPair.unit]].length →
      (elim.dotP [BPair.unit, BPair.ofNat 1]
        (ground.getAt [] [[BPair.ofNat 1, BPair.unit]]
          k)).oneValue BPair.unit)
    ∧ ¬ (∀ k, k < [[BPair.ofNat 1, BPair.unit]].length →
      (elim.dotP
        (elim.matVec [[BPair.unit, BPair.ofNat 1],
          [BPair.ofNat 1, BPair.unit]]
          [BPair.unit, BPair.ofNat 1])
        (ground.getAt [] [[BPair.ofNat 1, BPair.unit]]
          k)).oneValue BPair.unit) := by decide +kernel

/-! The cross-content pin from the exhaustion data: at a stated
top's closure pool the source and the moved content carry their own
groups, the letter-pair unit and its transpose partner cross
between them, and the residual member's image reads the sum's unit
against every moved row. -/

private def topSeed : blockcount.HVec := ⟨[2, 0], [BPair.ofNat 1]⟩

private def blockPool : List blockcount.HVec :=
  blockcount.closeSpan 2 (lowerspan.ht [2, 0]) [topSeed] [topSeed]

private def residMember : blockcount.HVec :=
  blockcount.residAt blockPool ⟨[1, 1], [BPair.ofNat 1, BPair.unit]⟩

private def srcGroup : elim.Mat := blockcount.groupAt blockPool [1, 1]

private def movedGroup : elim.Mat := blockcount.groupAt blockPool [0, 2]

private def raiseUnit : elim.Mat := units.matUnitAt [0, 2] [1, 1] 1 0

private def lowerUnit : elim.Mat := units.matUnitAt [1, 1] [0, 2] 0 1

/-- The cross-content conclusion decided outright, the instance
kernel-confirmed independently of the theorem. -/
example : ∀ k, k < movedGroup.length →
    (elim.dotP (elim.matVec raiseUnit residMember.coords)
      (ground.getAt [] movedGroup k)).oneValue BPair.unit := by decide +kernel

/-- The cross-content instance reads `perp_invariant` applied
whole: the residual perpendicular to its own content group, the
transpose partner carrying every moved row into that group's span,
and the raised image perpendicular to the moved group. -/
example : ∀ k, k < movedGroup.length →
    (elim.dotP (elim.matVec raiseUnit residMember.coords)
      (ground.getAt [] movedGroup k)).oneValue BPair.unit :=
  orthsplit.perp_invariant 2 raiseUnit lowerUnit srcGroup movedGroup
    residMember.coords (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
