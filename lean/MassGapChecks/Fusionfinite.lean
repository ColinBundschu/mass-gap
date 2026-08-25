import MassGap.Fusionfinite
import MassGap.Algebra
import MassGap.Leastwindow
/-!
The check module for `prop:fusionfinite`: the batteries re-read the
content ball by kernel `decide` at the label calculus's
instantiation — the row read at the adjoint square and at the
fundamental's rows in two and three letters, the unit source's row
among them; the rows' exact cleared Casimirs beside them, the ball
attained at the Cartan product (24 at two letters, 48 at three) so
the comparison is tight, not slack; and the multiplication window
bound at the square's `θ`-loop pool, the pool's window content the
summed per-link ball 96 = 4 · 24 attained exactly, the source's own
content 32 beside it.  The two refusals pin the read's conjuncts:
a forged interface whose row carries one further reduced shape past
the Cartan product's Casimir refuses the ball, and a forged
interface reading the unit label beyond the product holds under the
guard while the guard-free spelling refuses — the unit member of
every row inside every ball outright.
-/

open ground places lattice fusion

/-! The content ball's rows at the label calculus's instantiation:
the adjoint square, the fundamental against `θ`, the fundamental
against its dual, and the unit source's row. -/

example : fusionfinite.rowBall (dataA 2) (adjchar.theta 2)
    (adjchar.theta 2) := by decide +kernel
example : fusionfinite.rowBall (dataA 3) (adjchar.theta 3)
    (adjchar.theta 3) := by decide +kernel
example : fusionfinite.rowBall (dataA 2) [1, 0]
    (adjchar.theta 2) := by decide +kernel
example : fusionfinite.rowBall (dataA 3) [1, 0, 0]
    (labels.dualL [1, 0, 0]) := by decide +kernel
example : fusionfinite.rowBall (dataA 2) (labels.unitL 2)
    (adjchar.theta 2) := by decide +kernel

/-! The rows' exact cleared Casimirs, the ball attained at the
Cartan product: 24 at two letters and 48 at three, the row's
maximum reading the product's own value with the unit member's zero
at the row's end. -/

example : ((dataA 2).row (adjchar.theta 2) (adjchar.theta 2)).map
    (dataA 2).c2N = [24, 8, 0] := by decide +kernel
example : (dataA 2).c2N (places.addS (adjchar.theta 2)
    (adjchar.theta 2)) = 24 := by decide +kernel
example : ((dataA 3).row (adjchar.theta 3) (adjchar.theta 3)).map
    (dataA 3).c2N = [48, 36, 36, 18, 0] := by decide +kernel
example : (dataA 3).c2N (places.addS (adjchar.theta 3)
    (adjchar.theta 3)) = 48 := by decide +kernel

/-! The multiplication window bound at the square's `θ`-loop pool:
the pool's window content at or below the summed per-link ball, and
the summed ball 96 = 4 · 24 attained exactly, the source's own
content 32 beside it. -/

example : leastwindow.windowContent (dataA 2)
    (algebra.plaqRow (dataA 2) square sqPlaq
      (List.replicate 4 (adjchar.theta 2)))
    ≤ 4 * (dataA 2).c2N (places.addS (adjchar.theta 2)
      (adjchar.theta 2)) := by decide +kernel
example : leastwindow.windowContent (dataA 2)
    (algebra.plaqRow (dataA 2) square sqPlaq
      (List.replicate 4 (adjchar.theta 2))) = 96 := by decide +kernel
example : carrier.contentN (dataA 2)
    (List.replicate 4 (adjchar.theta 2)) = 32 := by decide +kernel

/-! The refusals.  The comparison conjunct is load-bearing: a
forged interface whose adjoint-square row carries the reduced shape
`[5, 0]` past the Cartan product's 24 refuses the ball. -/

private def forged : Data Shape :=
  { dataA 2 with
    row := fun a b => (dataA 2).row a b ++ [[5, 0]] }

example : ¬ fusionfinite.rowBall forged (adjchar.theta 2)
    (adjchar.theta 2) := by decide +kernel

/-! The unit guard is load-bearing: a forged interface reading the
unit label beyond the product holds under the guard — the row's
last member is the unit — while the guard-free spelling refuses. -/

private def forged2 : Data Shape :=
  { dataA 2 with
    c2N := fun s =>
      if (dataA 2).eqL s (labels.unitL 2) then 100
      else (dataA 2).c2N s }

example : fusionfinite.rowBall forged2 (adjchar.theta 2)
    (adjchar.theta 2) := by decide +kernel
example : ¬ (((forged2.row (adjchar.theta 2)
    (adjchar.theta 2)).all (fun c =>
      decide (forged2.c2N c
        ≤ forged2.c2N (forged2.add (adjchar.theta 2)
          (adjchar.theta 2))))) = true) := by decide +kernel
