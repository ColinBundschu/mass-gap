import MassGap.Xdata
/-!
The check module for `thm:xdata`: the batteries read the vacuum
`Q`-dressing's data by kernel `decide`.  The two module states'
deflation certificates first — `con:res` step 1's read at the
vacuum's magnetic image, the presentation's self-pairing occupied
with its pairing against the residual at equal members, the two
sites' data the content theorems' own — and the discriminating
refusal beside them: the squared trace `|tr U|²` sits off the
module space, its dressing's self-pairing occupied, so the
dressing read separates the module states from the sector's
further states.  The integer coefficients' batteries are
`MassGapChecks/Xfusion`'s, the anchors at the sector's own
module.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open genericlift states res twoplaq poly

/-! The vacuum's deflation certificates at the two sites. -/

example : res.deflateRead siteQ1 [phiAdj] phiAdj := by decide +kernel
example : res.deflateRead siteQ2 [phiAdj] phiAdj := by decide +kernel

/-! The discriminating refusal: the squared trace's dressing reads
its self-pairing occupied. -/

example : ¬ genericlift.crossNull
    (wg.pairFull wg.evalPhi siteQ1 siteQ1
      (res.deflate siteQ1 [phiAdj] [([0, 1], pOne)])
      (res.deflate siteQ1 [phiAdj] [([0, 1], pOne)]))
    poly.pZero := by decide +kernel

/-! The two dressing reads through the theorems, the routes beside
the certificates. -/

example : genericlift.crossNull
    (wg.pairFull wg.evalPhi siteQ1 siteQ1
      (res.deflate siteQ1 [phiAdj] phiAdj)
      (res.deflate siteQ1 [phiAdj] phiAdj))
    poly.pZero := xdata.vacDressU_null

example : genericlift.crossNull
    (wg.pairFull wg.evalPhi siteQ2 siteQ2
      (res.deflate siteQ2 [phiAdj] phiAdj)
      (res.deflate siteQ2 [phiAdj] phiAdj))
    poly.pZero := xdata.vacDressV_null
