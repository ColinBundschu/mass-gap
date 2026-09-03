import MassGap.Decomp
/-!
The check module for `thm:decomp`'s corner clause: at the corner
data `E = diag(3, 2)`, `M = diag(2, 3)` over the unit gram at the
scale `[2 : 1]` the family scaled by `3` reads its corner pencil as
the scaled pencil, `3·(4E − M) = diag(30, 15)`, decided beside the
`pencil_scale` route; the count at the level `⟨7 : 1⟩` reads one at
the family and one at the scaled family at the scaled level
`⟨21 : 3⟩`, routed both ways through `count_scale` and
`count_unscale` at the computed splits; and the level's move with the
scale is load-bearing, the scaled family at the unscaled level
reading the count vacant.
-/

open ground elim inertia certconstruct corner decomp

private def u : BPair := BPair.unit
private def dE : Mat := [[⟨4, 1⟩, u], [u, ⟨3, 1⟩]]
private def dM : Mat := [[⟨3, 1⟩, u], [u, ⟨4, 1⟩]]

example : cornerPencil (matScale 3 dE) (matScale 3 dM) 2 1
    = matScale 3 (cornerPencil dE dM 2 1) := by decide +kernel
example : cornerPencil (matScale 3 dE) (matScale 3 dM) 2 1
    = matScale 3 (cornerPencil dE dM 2 1) := pencil_scale dE dM 3 2 1

private def sBase : Mat :=
  siteDatum (matAdd (cornerPencil dE dM 2 1) (matScale 1 (idMat 2)))
    (matScale 7 (idMat 2))
private def sScaled : Mat :=
  siteDatum
    (matAdd (cornerPencil (matScale 3 dE) (matScale 3 dM) 2 1)
      (matScale (3 * 1) (idMat 2)))
    (matScale (3 * 7) (idMat 2))

private theorem cBase : countAtPair (cornerPencil dE dM 2 1) (idMat 2) 7 1 1
    (mkSplit 2 sBase) := by decide +kernel
private theorem cScaled : countAtPair
    (cornerPencil (matScale 3 dE) (matScale 3 dM) 2 1) (idMat 2)
    (3 * 7) (3 * 1) 1 (mkSplit 2 sScaled) := by decide +kernel

example : countAtPair
    (cornerPencil (matScale 3 dE) (matScale 3 dM) 2 1) (idMat 2)
    (3 * 7) (3 * 1) 1 (mkSplit 2 sScaled) :=
  count_scale dE dM (idMat 2) 3 2 1 7 1 1 (mkSplit 2 sBase) (mkSplit 2 sScaled)
    cBase (by decide +kernel)

example : countAtPair (cornerPencil dE dM 2 1) (idMat 2) 7 1 1
    (mkSplit 2 sBase) :=
  count_unscale dE dM (idMat 2) 3 2 1 7 1 1 (mkSplit 2 sBase)
    (mkSplit 2 sScaled) cScaled (by decide +kernel)

/-- The level moves with the scale: the scaled family at the
unscaled level `⟨7 : 1⟩` reads its count vacant, `diag(24, 9)`. -/
example : countAtPair
    (cornerPencil (matScale 3 dE) (matScale 3 dM) 2 1) (idMat 2) 7 1 0
    (mkSplit 2 (siteDatum
      (matAdd (cornerPencil (matScale 3 dE) (matScale 3 dM) 2 1)
        (matScale 1 (idMat 2)))
      (matScale 7 (idMat 2)))) := by decide +kernel
