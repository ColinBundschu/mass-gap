import MassGap.Xfusion
import MassGap.Twoplaq
/-!
`thm:xdata` — the X-sector block data.  The two integer
coefficients are the sector's anchors general in the residue:
`⟨q₁, M vac⟩ = 1`, the vacuum's multiplicity at
`xfusion.vacMult_eq`, and `c₁ = ⟨q₁, X q₁⟩`, the fusion
multiplicity at `xfusion.c1_eq` with `xfusion.c1_one` the `r = 1`
read.  The vacuum `Q`-dressing reads equal members as a polynomial
pair (`vacDressU_null`, `vacDressV_null`): `M vac`'s component at
a plaquette is the module state itself — `con:twoplaq`'s magnetic
multiplication at the vacuum, the adjoint's presentation `phiAdj`
at the plaquette's own site — so `con:res` step 1's deflation at
the module presentation withdraws it whole, and the residual's
self-pairing reads the sum's unit, the membership read: `M vac`
lies in the module space `Q` projects off.  The module is isolated
at the channel distances, the Casimir gaps of `lem:channels`' list
— `channels.dist2Theta_pos` and `channels.distOmega_pos` the
occupied gaps, the unit channel's and the dual pair's at one — and
the structural identities are the channel table's closes,
`channels.dimClosureAll` and `channels.casClosureAll`, the second
`thm:drift`'s display at `R = adj`: `d_adj = r (r + 2)` and
`ĉ₂(adj) = 1` read `d_R d_adj (ĉ₂(R) + 1)` at `2 r² (r + 2)²`.
-/

namespace xdata
open twoplaq

set_option maxRecDepth 8192 in
/-- The vacuum `Q`-dressing at the `U` plaquette: the magnetic
image's component is the module state at the `U` site, and its
deflation's residual reads its self-pairing at equal members. -/
theorem vacDressU_null : genericlift.crossNull
    (wg.pairFull siteQ1 siteQ1
      (res.deflate siteQ1 [phiAdj] phiAdj)
      (res.deflate siteQ1 [phiAdj] phiAdj))
    poly.pZero := by decide +kernel

set_option maxRecDepth 8192 in
/-- The vacuum `Q`-dressing at the `V` plaquette, the second
site's read. -/
theorem vacDressV_null : genericlift.crossNull
    (wg.pairFull siteQ2 siteQ2
      (res.deflate siteQ2 [phiAdj] phiAdj)
      (res.deflate siteQ2 [phiAdj] phiAdj))
    poly.pZero := by decide +kernel

end xdata
