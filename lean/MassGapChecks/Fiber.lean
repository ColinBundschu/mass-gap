import MassGap.Fiber
/-!
The check module for `con:fiber`: the batteries re-read the fiber's
pairing by kernel `decide` at the presentation's own values —
`⟨tr U, tr U⟩ = 1` at the one-factor site, and at the adjoint site
`⟨χ_adj, χ_adj⟩ = 1` with `⟨1, χ_adj⟩` of equal members at
`χ_adj = |tr U|² - [1 : d_f] tr(U U†)`, `prop:wg`'s pinned
Weingarten values read through the fiber's own display. -/
set_option maxHeartbeats 4000000

open ground poly genericlift states fiber

private def fU : FList := [(false, false)]
private def fAdj : FList := [(false, false), (false, true)]

/-- The fundamental trace's presentation, `tr U`. -/
private def trU : Comb := [([0], pOne)]

/-- The unit's presentation, `[1 : d_f] tr(U U†)`. -/
private def unitC : Comb := [([1, 0], ([⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]))]

/-- The adjoint character's presentation,
`|tr U|² - [1 : d_f] tr(U U†)`. -/
private def adjC : Comb :=
  [([0, 1], pOne), ([1, 0], ([⟨1, 2⟩], [⟨2, 1⟩, ⟨2, 1⟩]))]

example : crossNull (pairP fU fU trU trU) pOne := by decide +kernel
example : crossNull (pairP fAdj fAdj adjC adjC) pOne := by decide +kernel
example : crossNull (pairP fAdj fAdj unitC adjC) pZero := by decide +kernel
