import MassGap.Freeend
import MassGapChecks.Carrier
/-!
The check module for `lem:freeend`: the batteries re-read the free
end's level by kernel `decide` at the label calculus's committed
windows — the level read at the square and the theta graph (the
value `4 · dfQ(f)` at or below every occupied content and attained,
at two letters `12` and at three `32`, the theta graph's larger
cutoff admitting the hexagon with the level unmoved, the window
enumerations the carrier check module's committed pins), the window floor read at the below-cutoff
enumerations (`belowFloor` at `dfQ(f) = r (r+2)`, two through four
letters at the `θ`-admitting cutoffs), the attainment's
configuration (the
fundamental loop the level's witness, its content the display's and
its occupancy the corner units'); `prop:E0`'s module is the
attainment's `θ` instance by `attainTheta`, the definitional read in
the content module.
-/
set_option maxRecDepth 8192

open ground lattice fusion freeend

/-! The level read: `4 · dfQ(f)` at or below every occupied content
and attained, the first computed value of the invariant at
`K = ĉ₂(f)` against `E₀ = 4`. -/

example : levelRead (dataA 2) square 12 12 := by decide +kernel
example : levelRead (dataA 2) square 32 12 :=
  levelRead_at (dataA 2) square 32 12 carrier.sqIx2
    carrier.sqIx2_pin (by decide +kernel)
example : levelRead (tabulate (dataA 2) 12) thetaG 12 12 :=
  levelRead_at (tabulate (dataA 2) 12) thetaG 12 12 carrier.thIx12
    carrier.thIx12_pin (by decide +kernel)
example : levelRead (tabulate (dataA 2) 18) thetaG 18 12 :=
  levelRead_at (tabulate (dataA 2) 18) thetaG 18 12 carrier.thIx18
    carrier.thIx18_pin (by decide +kernel)
example : levelRead (dataA 3) square 32 32 :=
  levelRead_at (dataA 3) square 32 32 carrier.sqIx3
    carrier.sqIx3_pin (by decide +kernel)

/-! The window floor read at the below-cutoff enumerations,
`lem:casfloor`'s floor `r (r+2)` at the window's own labels. -/

example : belowFloor (dataA 2) 12 3 := by decide +kernel
example : belowFloor (dataA 2) 32 3 := by decide +kernel
example : belowFloor (dataA 3) 32 8 := by decide +kernel
example : belowFloor (dataA 4) 32 15 := by decide +kernel

/-! The attainment: the fundamental loop the level's witness, its
content the display's and its occupancy the corner units'. -/

example : carrier.contentN (dataA 2)
    (attainConf (dataA 2) square sqPlaq [1, 0]) = 12 := by decide +kernel
example : carrier.occupied (dataA 2) square
    (attainConf (dataA 2) square sqPlaq [1, 0]) = true := by decide +kernel
example : carrier.contentN (dataA 3)
    (attainConf (dataA 3) square sqPlaq [1, 0, 0]) = 32 := by decide +kernel
example : carrier.occupied (dataA 3) square
    (attainConf (dataA 3) square sqPlaq [1, 0, 0]) = true := by decide +kernel
