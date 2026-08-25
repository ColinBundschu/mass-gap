import MassGap.Windowfinite
import MassGapChecks.Carrier
/-!
The check module for `prop:windowfinite`: the batteries re-read
the window dimension's count by kernel `decide` — the display
`dim = 1 + Σ_a Π_v vmult(v, a)` at the square and the theta graph
at stated cutoffs, the fundamental loop's window at two, the two
label loops at three, and the theta graph's two squares with the
hexagon entering at its content's cutoff.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000

open ground lattice fusion windowfinite

/-! The square's window dimensions: the fundamental loop alone,
then the two label loops. -/

example : dimSect (dataA 2) square 12 = 2 := by decide +kernel
set_option maxRecDepth 1000000 in
example : dimSect (dataA 2) square 32 = 3 := by decide +kernel

/-! The theta graph's window dimensions: the two squares' loops,
the hexagon entering at its content's cutoff. -/

example : (carrier.idx (tabulate (dataA 2) 12) thetaG 12).length = 2 := by
  rw [carrier.thIx12_pin]; decide +kernel
example : dimSect (tabulate (dataA 2) 12) thetaG 12 = 3 :=
  dimSect_at (tabulate (dataA 2) 12) thetaG 12 3 carrier.thIx12
    carrier.thIx12_pin (by decide +kernel)
example : dimSect (tabulate (dataA 2) 18) thetaG 18 = 4 :=
  dimSect_at (tabulate (dataA 2) 18) thetaG 18 4 carrier.thIx18
    carrier.thIx18_pin (by decide +kernel)


/-! `degree_le_dfQ`'s route at the reduced shape `[2, 1, 0]`: the
cleared read thirty-two clears the count's multiple of the degree,
twelve; the reduced binder isolated at `[1]`, whose count multiple
of the degree exceeds its vacant cleared read. -/

example : (3 : Nat) * places.degree [2, 1, 0]
    ≤ c2hat.dfQ [2, 1, 0] :=
  degree_le_dfQ [2, 1, 0] 2 rfl rfl
example : (3 : Nat) * places.degree [2, 1, 0] = 12 := by decide +kernel
example : c2hat.dfQ [2, 1, 0] = 32 := by decide +kernel
example : ¬ ((1 : Nat) * places.degree [1] ≤ c2hat.dfQ [1]) := by
  decide +kernel
example : ([1] : places.Shape).length = 0 + 1 := by decide +kernel
example : ¬ (ground.getAt 0 [1] 0 = 0) := by decide +kernel
