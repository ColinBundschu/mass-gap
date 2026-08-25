import MassGap.Ground
/-!
`thm:bridge` — the scheme bridge is a count:
`[d_adj C₂(adj) : d_f C₂(f)] = 2 d_f` exactly, the pair of two
weight-one objects, one value at every form point, and the read is
a count: the `f`-flux bridge's component at the contact end is
`b_f^equiv = 2 d_f b_X`, one rescaling of the coupling coordinate.
The pair reads the cross-multiplied natural identity
`r(r+2) · 2 d_f² = 2 d_f · (d_f · r(r+2))` at `d_f = r + 1`
(`count`, every residue); the pair carrier's committed evaluations
are the check module's pins, the `r = 2` value `6` among them.
-/

namespace bridge

/-- The scheme bridge's count: the pair
`[d_adj C₂(adj) : d_f C₂(f)]` reads `2 d_f` at the cross-multiplied
natural identity `r(r+2) · 2 d_f² = 2 d_f · (d_f · r(r+2))`, one
identity at every residue. -/
theorem count (r : Nat) :
    r * (r + 2) * (2 * ((r + 1) * (r + 1)))
      = 2 * (r + 1) * ((r + 1) * (r * (r + 2))) := by
  rw [ground.mulLeftComm (r * (r + 2)) 2 ((r + 1) * (r + 1)),
    ground.mulLeftComm (r * (r + 2)) (r + 1) (r + 1),
    Nat.mul_comm (r * (r + 2)) (r + 1),
    ground.mulAssoc 2 (r + 1) ((r + 1) * (r * (r + 2)))]

end bridge
