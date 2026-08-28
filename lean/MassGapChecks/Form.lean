import MassGap.Form
/-!
The check module for `prop:form`: the batteries re-read theta's
self-duality by kernel `decide` — the reduction and the occupancy
reversal fixing the adjoint shape at the small widths with the
theorem routes beside them, the form line's unit-label count at
one, and the width bound's refusals at the single column.
-/
set_option maxHeartbeats 4000000

open labels adjchar form

/-! The self-duality decided at the small widths. -/

example : reduce (theta 2) = theta 2 := by decide +kernel
example : reduce (theta 3) = theta 3 := by decide +kernel
example : reduce (theta 4) = theta 4 := by decide +kernel
example : reduce (theta 5) = theta 5 := by decide +kernel
example : dualL (theta 2) = theta 2 := by decide +kernel
example : dualL (theta 3) = theta 3 := by decide +kernel
example : dualL (theta 4) = theta 4 := by decide +kernel
example : dualL (theta 5) = theta 5 := by decide +kernel

/-! The self-duality as the theorems' own routes. -/

example : reduce (theta 2) = theta 2 := reduce_theta 2 (Nat.le_refl 2)
example : reduce (theta 3) = theta 3 := reduce_theta 3 (Nat.le_succ 2)
example : reduce (theta 4) = theta 4 :=
  reduce_theta 4 (Nat.le.step (Nat.le_succ 2))
example : dualL (theta 2) = theta 2 := dualL_theta 2 (Nat.le_refl 2)
example : dualL (theta 3) = theta 3 := dualL_theta 3 (Nat.le_succ 2)
example : dualL (theta 4) = theta 4 :=
  dualL_theta 4 (Nat.le.step (Nat.le_succ 2))

/-! The form line's unit-label count at one, the kernel read and
the theorem route. -/

example : countL (theta 2) (theta 2) (unitL 2) = 1 := by decide +kernel
example : countL (theta 3) (theta 3) (unitL 3) = 1 := by decide +kernel
example : countL (theta 4) (theta 4) (unitL 4) = 1 := by decide +kernel

example : countL (theta 2) (theta 2) (unitL 2) = 1 :=
  lineRead 2 (Nat.le_refl 2)
example : countL (theta 3) (theta 3) (unitL 3) = 1 :=
  lineRead 3 (Nat.le_succ 2)
example : countL (theta 4) (theta 4) (unitL 4) = 1 :=
  lineRead 4 (Nat.le.step (Nat.le_succ 2))

/-! The width bound's refusals at the single column: the adjoint
shape at `d = 1` is the doubled column, whose reduction and
reversal both read the unit occupancy. -/

example : theta 1 = [2] := rfl
example : reduce (theta 1) = [0] := rfl
example : dualL (theta 1) = [0] := rfl
example : reduce (theta 1) ≠ theta 1 := by decide +kernel
example : dualL (theta 1) ≠ theta 1 := by decide +kernel
