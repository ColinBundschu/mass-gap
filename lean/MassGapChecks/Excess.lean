import MassGap.Excess
/-!
The check module for `def:excess`: the batteries re-read the ruler
excess by kernel `decide` — the coefficient window at the
successor spelling, the evaluation at one at displayed values, and
the geometric-derivative display over the support at residue
instances through the classification's range.
-/
set_option maxHeartbeats 4000000

open ground excess

/-! The coefficient window: `[1:j]` at the keys one through
`r = g + 1`. -/

example : (coeffs 0).length = 1 := by decide +kernel
example : (coeffs 3).length = 4 := by decide +kernel

/-! The evaluation at one at displayed values: `A(1)` reads
`1`, `3/2`, `11/6` at the first three residues. -/

example : (evalOne 0).oneValue (Pair.ofPos Pos.one) := by decide +kernel
example : (evalOne 1).oneValue ⟨3, 2⟩ := by decide +kernel
example : (evalOne 2).oneValue ⟨11, 6⟩ := by decide +kernel

/-! The derivative display over the support, at the residues of
the classification's committed members. -/

example : derivRead 0 := by decide +kernel
example : derivRead 1 := by decide +kernel
example : derivRead 7 := by decide +kernel
example : derivRead 28 := by decide +kernel
