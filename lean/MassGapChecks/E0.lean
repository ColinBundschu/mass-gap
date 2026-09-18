import MassGap.E0
/-!
The check module for `prop:E0`: the batteries re-read the module's
data by kernel `decide` at the label calculus's instantiation — the
four-link content `4 C₂(θ)` at the square's plaquette at two and
three letters (the boundary's four distinct links), the module's
occupancy at the self-dual `θ`'s corner reads, and its membership in
the window index at a cutoff admitting its content, the eigen-read's
index form at the diagonal electric member.
-/

namespace E0
set_option maxHeartbeats 16000000

open ground lattice fusion

/-! The four-link content `4 C₂(θ)` at two and three letters. -/

theorem pin1 : contentRead (dataA 2) square sqPlaq := by decide +kernel
theorem pin2 : contentRead (dataA 3) square sqPlaq := by decide +kernel
theorem pin3 : carrier.contentN (dataA 2) (moduleConf (dataA 2) square sqPlaq)
    = 32 := by decide +kernel
theorem pin4 : carrier.contentN (dataA 3) (moduleConf (dataA 3) square sqPlaq)
    = 72 := by decide +kernel

/-! The module's occupancy, each corner's multiplicity the unit
law's read at the self-dual `θ`. -/

theorem pin5 : occRead (dataA 2) square sqPlaq := by decide +kernel
theorem pin6 : occRead (dataA 3) square sqPlaq := by decide +kernel

/-! The membership in the window index at a cutoff admitting the
module's content. -/

theorem pin7 : memberRead (dataA 2) square 32 sqPlaq := by
  decide +kernel

end E0
