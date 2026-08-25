import MassGap.Pairpencil
import MassGapChecks.Carrier
/-!
The check module for `thm:pairpencil`: the batteries re-read the
window pencil's symmetric pair matrix by kernel `decide` at the
label calculus's instantiation — the label-index magnetic matrix at
two and three letters (the fusion counts' own entries, the vacuum
defect the Kronecker delta at two labels and the diagonal the base
`c₁`), its symmetry at the self-dual `θ`, the window diagonal with
the unit line at its head over the committed square and theta
windows, and the pair's site datum `H([α : β])` symmetric with
pair entries at both weights.  The window-diagonal pins read the
committed enumerations at the carrier check module's pins through
the named display, the theta window's at the tabulated lookup
route. -/
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

open ground lattice fusion elim pairpencil

private def u : BPair := BPair.unit

/-! The label-index magnetic matrix at two letters over
`(𝟏, f, θ)`: the vacuum defect, the `f` diagonal one, and the base
`c₁ = 1`. -/

example : matOneValue (loopMag (dataA 2) [[1, 0], adjchar.theta 2])
    [[u, u, ⟨2, 1⟩], [u, ⟨2, 1⟩, u], [⟨2, 1⟩, u, ⟨2, 1⟩]] := by
  decide +kernel

/-! At three letters the base reads `c₁ = 2`, the further entries
the counts' own. -/

example : matOneValue (loopMag (dataA 3) [[1, 0, 0], adjchar.theta 3])
    [[u, u, ⟨2, 1⟩], [u, ⟨2, 1⟩, u], [⟨2, 1⟩, u, ⟨3, 1⟩]] := by
  decide +kernel

/-! The symmetry at the self-dual `θ`, both letter counts. -/

example : symmRead (loopMag (dataA 2) [[1, 0], adjchar.theta 2]) := by
  decide +kernel
example : symmRead (loopMag (dataA 3) [[1, 0, 0], adjchar.theta 3]) := by
  decide +kernel

/-! The window diagonal with the unit line at its head, the
committed windows' reads. -/

example : windowDiag (dataA 2) square 32
    = [0, 12, 32] :=
  windowDiag_at (dataA 2) square 32 carrier.sqIx2 [0, 12, 32]
    carrier.sqIx2_pin (by decide +kernel)
example : windowDiag (tabulate (dataA 2) 18) thetaG 18
    = [0, 12, 18, 12] :=
  windowDiag_at (tabulate (dataA 2) 18) thetaG 18 carrier.thIx18
    [0, 12, 18, 12] carrier.thIx18_pin (by decide +kernel)

/-! The pair's site datum at the square's label index: symmetric
with pair entries at both weights, the displayed matrix at
`[1 : 1]`. -/

example : matOneValue
    (pencilH 1 1 [0, 12, 32] (loopMag (dataA 2) [[1, 0], adjchar.theta 2]))
    [[u, u, ⟨1, 2⟩], [u, ⟨12, 1⟩, u], [⟨1, 2⟩, u, ⟨32, 1⟩]] := by
  decide +kernel

example : symmRead
    (pencilH 2 3 [0, 12, 32]
      (loopMag (dataA 2) [[1, 0], adjchar.theta 2])) := by decide +kernel
