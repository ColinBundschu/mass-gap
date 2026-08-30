import MassGap.Cornerstore

/-! # Checks: the pre-tier store

The pre tier's certificate reads decided by the kernel at the
stated data: the two graded devices, the box order with the
two-step overlap, and the boundary seed's three clearings — the
certificate read's own pre-tier conjuncts at the store. -/

open ground cornerpivot

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

example : gradRead preV preE0n preE0d prePos := by
  decide +kernel

example : gradRead (profStrip (termProf preV preR preQN preQD))
    preE0n preE0d preTerm := by decide +kernel

example : prePos.lo ≤ stage.unitC := by decide +kernel

example : preTerm.lo ≤ stage.unitC := by decide +kernel

example : stepClear preTerm.hi preMid preE0n preE0d := by
  decide +kernel

example : stepClear preMid prePos.hi preE0n preE0d := by
  decide +kernel

example : seedRead preR preQN preQD preE0n preE0d preV
    seedK seedCK seedTK := by decide +kernel
