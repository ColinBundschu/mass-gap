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

namespace walkresidue
set_option maxHeartbeats 4000000

open ground

/-! The pairing's join, split and summand identity over the
grid. -/

theorem pin1 : pairRead 1 1 := by decide +kernel
theorem pin2 : pairRead 1 5 := by decide +kernel
theorem pin3 : pairRead 2 3 := by decide +kernel
theorem pin4 : pairRead 8 2 := by decide +kernel
theorem pin5 : splitRead 1 2 := by decide +kernel
theorem pin6 : splitRead 2 5 := by decide +kernel
theorem pin7 : splitRead 8 3 := by decide +kernel
theorem pin8 : summandRead 1 1 := by decide +kernel
theorem pin9 : summandRead 2 4 := by decide +kernel
theorem pin10 : summandRead 8 6 := by decide +kernel

/-! The telescope's exactness at stated `M`, at `r = g + 1`. -/

theorem pin11 : teleRead 0 1 := by decide +kernel
theorem pin12 : teleRead 0 6 := by decide +kernel
theorem pin13 : teleRead 1 0 := by decide +kernel
theorem pin14 : teleRead 28 3 := by decide +kernel
theorem pin15 : teleRead 1 1 := by decide +kernel
theorem pin16 : teleRead 1 4 := by decide +kernel
theorem pin17 : teleRead 2 3 := by decide +kernel
theorem pin18 : teleRead 2 9 := by decide +kernel
theorem pin19 : teleRead 7 5 := by decide +kernel

/-! The value read `A(1) = H_r` at every committed member's
residue: `2, 4, 6, 3, 5, 7, 8, 11, 17, 29` beside the first
regimes. -/

theorem pin20 : excessRead 0 := by decide +kernel
theorem pin21 : excessRead 1 := by decide +kernel
theorem pin22 : excessRead 2 := by decide +kernel
theorem pin23 : excessRead 3 := by decide +kernel
theorem pin24 : excessRead 4 := by decide +kernel
theorem pin25 : excessRead 5 := by decide +kernel
theorem pin26 : excessRead 6 := by decide +kernel
theorem pin27 : excessRead 7 := by decide +kernel
theorem pin28 : excessRead 10 := by decide +kernel
theorem pin29 : excessRead 16 := by decide +kernel
theorem pin30 : excessRead 28 := by decide +kernel

end walkresidue
