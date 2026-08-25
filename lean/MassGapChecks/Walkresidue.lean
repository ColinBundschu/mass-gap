import MassGap.Walkresidue
/-!
The check module for `thm:walkresidue`: the batteries re-read the
walk residue by kernel `decide` — the tower pairing's join and
Casimir split with the summand identity over a residue-by-tower
grid; the finite telescope's exactness at stated `M` across
residues, the `A`-series' first regimes and the fixed members'
`F_4` residue among them; and the value read `A(1) = H_r` at
every committed member's residue.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground walkresidue

/-! The pairing's join, split and summand identity over the
grid. -/

example : pairRead 1 1 := by decide +kernel
example : pairRead 1 5 := by decide +kernel
example : pairRead 2 3 := by decide +kernel
example : pairRead 8 2 := by decide +kernel
example : splitRead 1 2 := by decide +kernel
example : splitRead 2 5 := by decide +kernel
example : splitRead 8 3 := by decide +kernel
example : summandRead 1 1 := by decide +kernel
example : summandRead 2 4 := by decide +kernel
example : summandRead 8 6 := by decide +kernel

/-! The telescope's exactness at stated `M`, at `r = g + 1`. -/

example : teleRead 0 1 := by decide +kernel
example : teleRead 0 6 := by decide +kernel
example : teleRead 1 0 := by decide +kernel
example : teleRead 28 3 := by decide +kernel
example : teleRead 1 1 := by decide +kernel
example : teleRead 1 4 := by decide +kernel
example : teleRead 2 3 := by decide +kernel
example : teleRead 2 9 := by decide +kernel
example : teleRead 7 5 := by decide +kernel

/-! The value read `A(1) = H_r` at every committed member's
residue: `2, 4, 6, 3, 5, 7, 8, 11, 17, 29` beside the first
regimes. -/

example : excessRead 0 := by decide +kernel
example : excessRead 1 := by decide +kernel
example : excessRead 2 := by decide +kernel
example : excessRead 3 := by decide +kernel
example : excessRead 4 := by decide +kernel
example : excessRead 5 := by decide +kernel
example : excessRead 6 := by decide +kernel
example : excessRead 7 := by decide +kernel
example : excessRead 10 := by decide +kernel
example : excessRead 16 := by decide +kernel
example : excessRead 28 := by decide +kernel
