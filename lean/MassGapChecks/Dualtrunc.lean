import MassGap.Dualtrunc
import MassGapChecks.Truncation
/-!
The check module for `lem:dualtrunc`: the batteries re-read the dual
coupling's two publics by kernel `decide`.

`admRead` is the displayed admissibility comparison
`σΛ_C > λ + W + c_ϑ` at the level's two members cross-added and the
whole cleared to the naturals, read at the clearance pair
`ϑ = [1 : 1]` with `σ = 1`, the level `⟨6 : 1⟩`, `W = 2`: the
comparison `1 · 8 + 4 · 1 = 12 < 20 + 1` at the cutoff twenty, and
the moved cutoff eleven refused at its own equality — the cutoff's
own isolating record, the admissible set an output whose floor rises
toward the contact end.

`pin_count` is the pinned count at a bracket clear of the head's
divisor, read at the order `1 + 1` fixture (head pencil `[2]`,
removed pencil `[10]`, coupling `[1]` over the block-diagonal unit
gram): the head's two counts at the bracket's ends — five and six —
are the one integer one, the removed block's count is vacant at
nine, the difference site `[[1,1],[1,4]]` is positive semidefinite,
and the two transports squeeze the full pencil's own count onto that
integer.

Two refusals ride beside it, each isolating one binder.  The floor: a
forged removed pencil `[3]` takes the full pencil to `[[2,1],[1,3]]`,
negative definite at five and reading count two against the pinned
one, its own vacant count at nine refused.  The clear bracket: a
forged head pencil `[5]` reads the sum's unit at five and one at six,
so the bracket's two ends part and no integer is pinned, while the
full pencil reads one at five.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground elim inertia certconstruct truncation dualtrunc

/-! The admissibility comparison at its data, and the moved cutoff's
refusal at the comparison's own equality. -/

example : admRead 1 20 6 1 2 1 1 := by decide +kernel
example : ¬ admRead 1 11 6 1 2 1 1 := by decide +kernel

/-! `pin_count`'s route at the fixture: the head's two counts at five
and six are one integer, the blocking tie reads the full pencil's
site at five as the two blocks' join over the shared coupling, the
removed block's count is vacant at nine, and the difference site is
positive semidefinite — so the full pencil's count is that integer,
the two transports meeting on it. -/

example : countAtPair pHead gHead 6 1 1 (inertia.spOne ⟨1, 4⟩) := by decide +kernel
example : countAtPair pHead gHead 7 1 1 (inertia.spOne ⟨1, 5⟩) := by decide +kernel
example : countAtPair qRem gRem 10 1 0 (inertia.spOne ⟨2, 1⟩) := by decide +kernel
example : countAtPair hFull gFull 6 1 1 (spThree ⟨1, 4⟩ ⟨49, 1⟩) := by
  decide +kernel

example : (1 : Nat) = 1 :=
  pin_count (k := 1) (m := 1) hFull gFull pHead gHead bCoup qRem gRem
    6 1 7 1 10 1 1 1
    (inertia.spOne ⟨1, 4⟩) (inertia.spOne ⟨1, 5⟩) (inertia.spOne ⟨2, 1⟩)
    (spThree ⟨1, 4⟩ ⟨49, 1⟩) (spId ⟨1, 5⟩ ⟨2, 1⟩)
    (spShear ⟨2, 1⟩ ⟨4, 1⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The floor binder's refusal: at the forged removed pencil `[3]` the
full pencil is negative definite at five and reads count two, so the
pinned integer one is refused; the removed block's own vacant count
at nine is refused beside it, its site reading `[-6]`. -/

example : countAtPair hForge gFull 6 1 2 (spThree ⟨1, 4⟩ ⟨1, 16⟩) := by
  decide +kernel
example : ¬ ((2 : Nat) = 1) := by decide +kernel
example : ¬ countAtPair qForge gRem 10 1 0 (inertia.spOne ⟨1, 7⟩) := by decide +kernel

/-! The clear bracket's refusal: at the forged head pencil `[5]` the
head reads the sum's unit at five and one at six, so the bracket's
two ends carry no one integer, while the full pencil `[[5,1],[1,10]]`
reads one at five — the pin's two head reads part. -/

example : countAtPair pForge gHead 6 1 0 spKern := by decide +kernel
example : countAtPair pForge gHead 7 1 1 (inertia.spOne ⟨1, 2⟩) := by decide +kernel
example : countAtPair hBracket gFull 6 1 1 (spMix u ⟨2, 1⟩ ⟨6, 1⟩) := by
  decide +kernel
example : ¬ ((1 : Nat) = 0) := by decide +kernel
