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

namespace windowfinite
set_option maxHeartbeats 16000000

open ground lattice fusion

/-! The square's window dimensions: the fundamental loop alone,
then the two label loops. -/

theorem pin1 : dimSect (dataA 2) square 12 = 2 := by decide +kernel
theorem pin2 : dimSect (dataA 2) square 32 = 3 := by decide +kernel

/-! The theta graph's window dimensions: the two squares' loops,
the hexagon entering at its content's cutoff. -/

theorem pin3 : (carrier.idx (tabulate (dataA 2) 12) thetaG 12).length = 2 := by
  rw [carrier.thIx12_pin]; decide +kernel
theorem pin4 : dimSect (tabulate (dataA 2) 12) thetaG 12 = 3 :=
  dimSect_at (tabulate (dataA 2) 12) thetaG 12 3 carrier.thIx12
    carrier.thIx12_pin (by decide +kernel)
theorem pin5 : dimSect (tabulate (dataA 2) 18) thetaG 18 = 4 :=
  dimSect_at (tabulate (dataA 2) 18) thetaG 18 4 carrier.thIx18
    carrier.thIx18_pin (by decide +kernel)

end windowfinite
