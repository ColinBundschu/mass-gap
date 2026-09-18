import MassGap.Form
/-!
The check module for `prop:form`: the batteries re-read theta's
self-duality by kernel `decide` — the reduction and the occupancy
reversal fixing the adjoint shape at the small widths with the
theorem routes beside them, the form line's unit-label count at
one, and the width bound's refusals at the single column.
-/

namespace form
set_option maxHeartbeats 4000000

open labels adjchar

/-! The self-duality decided at the small widths. -/

theorem pin1 : reduce (theta 2) = theta 2 := by decide +kernel
theorem pin2 : reduce (theta 3) = theta 3 := by decide +kernel
theorem pin3 : reduce (theta 4) = theta 4 := by decide +kernel
theorem pin4 : reduce (theta 5) = theta 5 := by decide +kernel
theorem pin5 : dualL (theta 2) = theta 2 := by decide +kernel
theorem pin6 : dualL (theta 3) = theta 3 := by decide +kernel
theorem pin7 : dualL (theta 4) = theta 4 := by decide +kernel
theorem pin8 : dualL (theta 5) = theta 5 := by decide +kernel

/-! The self-duality as the theorems' own routes. -/

theorem pin9 : reduce (theta 2) = theta 2 := reduce_theta 2 (Nat.le_refl 2)
theorem pin10 : reduce (theta 3) = theta 3 := reduce_theta 3 (Nat.le_succ 2)
theorem pin11 : reduce (theta 4) = theta 4 :=
  reduce_theta 4 (Nat.le.step (Nat.le_succ 2))
theorem pin12 : dualL (theta 2) = theta 2 := dualL_theta 2 (Nat.le_refl 2)
theorem pin13 : dualL (theta 3) = theta 3 := dualL_theta 3 (Nat.le_succ 2)
theorem pin14 : dualL (theta 4) = theta 4 :=
  dualL_theta 4 (Nat.le.step (Nat.le_succ 2))

/-! The form line's unit-label count at one, the kernel read and
the theorem route. -/

theorem pin15 : countL (theta 2) (theta 2) (unitL 2) = 1 := by decide +kernel
theorem pin16 : countL (theta 3) (theta 3) (unitL 3) = 1 := by decide +kernel
theorem pin17 : countL (theta 4) (theta 4) (unitL 4) = 1 := by decide +kernel

theorem pin18 : countL (theta 2) (theta 2) (unitL 2) = 1 :=
  lineRead 2 (Nat.le_refl 2)
theorem pin19 : countL (theta 3) (theta 3) (unitL 3) = 1 :=
  lineRead 3 (Nat.le_succ 2)
theorem pin20 : countL (theta 4) (theta 4) (unitL 4) = 1 :=
  lineRead 4 (Nat.le.step (Nat.le_succ 2))

/-! The width bound's refusals at the single column: the adjoint
shape at `d = 1` is the doubled column, whose reduction and
reversal both read the unit occupancy. -/

theorem pin21 : theta 1 = [2] := rfl
theorem pin22 : reduce (theta 1) = [0] := rfl
theorem pin23 : dualL (theta 1) = [0] := rfl
theorem pin24 : reduce (theta 1) ≠ theta 1 := by decide +kernel
theorem pin25 : dualL (theta 1) ≠ theta 1 := by decide +kernel

end form
