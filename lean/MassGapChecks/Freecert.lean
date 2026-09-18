import MassGap.Freecert
/-!
The check module for `lem:freecell`'s certificate: the batteries
re-read the free cell's certificate at the order-two window with a
tower, `E = diag(6, 40)`, `M` the balance partner of one at every
entry and the unit gram, the tower place the second key, by kernel
`decide`.  The cell is the segment `[0, 1]` at the level pair
`⟨13 : 1⟩ < ⟨17 : 1⟩` with the gap four, its two tower deflations
`22τ² − 168` and `14τ² − 240` at count one, the sample at the free
end; the dominance divisor at the head bound `20`, the per-term cap
one, the direction count one (the per-vertex count two, the plaquette
chain's) and the floor twelve reads `48 − 80τ²` and `12 − 4τ²`, the
first designated with its root `√(3/5)` inside the bracket
`[3/4, 1]` at the clearing four, the segment from the free end to
the bracket's foot vacant, the second keeping its upper side to the
bracket's top at one piece; the cap read at the tower row, `20 ≤ 40`
and `12 · 1 ≤ 160`; the floor pair one at the level four against the
gap four.  The refusals, one per binder: the cap read at a head bound
beyond the tower row's content and at a floor beyond the cap; the
head bound at the upper level; the designated member beyond the
list, the origin multiplicity one at the occupied constant, the
bracket's foot at the lower-side point `−1`, the second member's
cover missing and the covers short of the list; the bracket's top
past a cell shortened to `[0, 1/2]` (the shortened cell read holding
on its own); the floor pair two beyond the gap; the cell's count two;
and the direction count two and the per-term cap two, each moving
the first read's root under the bracket's foot.  `listExtent_off`
reads the second member off the sum's unit at an interior point
through the theorem beside its own `decide`, and `freeRead_jump` both
level carriers' determinants off the sum's unit at the point `1/2`
through the theorem beside its own `decide`. -/

namespace freecell
open ground poly elim inertia cellcount

private def eT : Mat := [[⟨7, 1⟩, BPair.unit], [BPair.unit, ⟨41, 1⟩]]
private def mT : Mat := [[⟨1, 2⟩, ⟨1, 2⟩], [⟨1, 2⟩, ⟨1, 2⟩]]
private def gT : Mat := idMat 2
private def cfoot : CPair := ⟨BPair.unit, 1⟩
private def ctop : CPair := ⟨BPair.ofPos 1, 1⟩
private def chalf : CPair := ⟨⟨2, 1⟩, 2⟩
private def cvL : Cover :=
  Cover.one ctop 0 false ⟨3, 1⟩ ⟨2, 1⟩ Cover.nought Cover.done
private def cvLS : Cover :=
  Cover.one chalf 0 false ⟨3, 1⟩ ⟨2, 1⟩ Cover.nought Cover.done
private def hdA : split.PMat := pdeflP [1] (compl [1] 2) (freePMat eT mT gT 13 1)
private def hdT : split.PMat := pdeflP [1] (compl [1] 2) (freePMat eT mT gT 17 1)
private def cellTw : gappos.Cell 2 :=
  ⟨cfoot, ctop, 13, 1, 17, 1, 4, [1], ⟨3, 1⟩, ⟨2, 1⟩, cvL, cvL, BPair.unit, 1, 1,
   inertia.mkSplit 1 (evalPC hdA BPair.unit 1 4),
   inertia.mkSplit 1 (evalPC hdT BPair.unit 1 4)⟩
private def cellTwS : gappos.Cell 2 :=
  ⟨cfoot, chalf, 13, 1, 17, 1, 4, [1], ⟨3, 1⟩, ⟨2, 1⟩, cvLS, cvLS, BPair.unit, 1, 1,
   inertia.mkSplit 1 (evalPC hdA BPair.unit 1 4),
   inertia.mkSplit 1 (evalPC hdT BPair.unit 1 4)⟩

private def R1 : Poly := getAt [] (domDiv 20 1 2 12 17 1) 0
private def dR : windowsep.GcdData := windowsep.gcdD R1 (poly.deriv R1)
private def ctR : DivCert :=
  ⟨dR.g, dR.A, dR.B, dR.u, dR.v, R1, dR.u, dR.v, dR.top, dR.cA, dR.cB, dR.top,
   dR.c, dR.c⟩
private def sR : Poly := deckfactor.clearVarBT ctR.sq
private def spH : Split sR.length :=
  mkSplit sR.length (hermitesign.hermite sR poly.one)
private def spB (lo hi : BPair) : Split sR.length :=
  mkSplit sR.length (hermitesign.pencilB sR poly.one
    (deckfactor.clearAt ctR.sq lo) (deckfactor.clearAt ctR.sq hi) 4)
private def cvR2 : Cover :=
  Cover.one ⟨⟨5, 1⟩, 4⟩ 0 true ⟨2, 1⟩ ⟨2, 1⟩ Cover.nought Cover.done

private def fcT : FreeCert 2 :=
  ⟨cellTw, 20, 1, 1, 12, [], [Cover.done, cvR2], 0, 0, ctR, ⟨4, 1⟩, ⟨5, 1⟩, 4,
   sR.length, sR.length, sR.length, sR.length,
   spH, spB BPair.unit ⟨4, 1⟩, spH, spB ⟨4, 1⟩ ⟨5, 1⟩, 1, 1⟩

theorem pin45 : poly.oneValue R1 [⟨49, 1⟩, BPair.unit, ⟨1, 81⟩]
    ∧ poly.oneValue (getAt [] (domDiv 20 1 2 12 18 2) 0) R1 := by decide +kernel
theorem pin46 : poly.oneValue (getAt [] (freeList fcT) 1) [⟨13, 1⟩, BPair.unit, ⟨1, 5⟩] := by
  decide +kernel
theorem pin47 : sR.length = 2 := by decide +kernel
theorem pin48 : freeRead eT mT gT 4 fcT := by decide +kernel
theorem pin49 : BPair.unit < fcT.lo := freeRead_pos eT mT gT 4 fcT (by decide +kernel)
theorem pin50 : capRead eT mT [1] 20 1 2 12 := by decide +kernel
theorem pin51 : ¬ capRead eT mT [1] 41 1 2 12 := by decide +kernel
theorem pin52 : ¬ capRead eT mT [1] 20 1 2 200 := by decide +kernel
theorem pin53 : ¬ (fcT.cell.tx < (16 : Pos) + fcT.cell.ty)
    ∧ ¬ freeRead eT mT gT 4 { fcT with hb := 16 } := by decide +kernel
theorem pin54 : ¬ freeRead eT mT gT 4 { fcT with j := 2 } := by decide +kernel
theorem pin55 : ¬ freeRead eT mT gT 4 { fcT with k := 1 } := by decide +kernel
private def fcNeg : FreeCert 2 :=
  ⟨cellTw, 20, 1, 1, 12, [], [Cover.done, cvR2], 0, 0, ctR, ⟨1, 2⟩, ⟨5, 1⟩, 4,
   sR.length, sR.length, sR.length, sR.length,
   spH, spB BPair.unit ⟨1, 2⟩, spH, spB ⟨1, 2⟩ ⟨5, 1⟩, 1, 1⟩
theorem pin56 : ¬ freeRead eT mT gT 4 fcNeg := by decide +kernel
theorem pin57 : ¬ freeRead eT mT gT 4 { fcT with covs := [Cover.done, Cover.done] } := by
  decide +kernel
theorem pin58 : gappos.cellsRead eT mT gT cfoot [cellTwS] := by decide +kernel
theorem pin59 : ¬ freeRead eT mT gT 4 { fcT with cell := cellTwS } := by decide +kernel
theorem pin60 : ¬ freeRead eT mT gT 4 { fcT with kn := 2 } := by decide +kernel
private def cellG2 : gappos.Cell 2 := { cellTw with g := 2 }
theorem pin61 : ¬ freeRead eT mT gT 4 { fcT with cell := cellG2 } := by decide +kernel
theorem pin62 : ¬ (stage.evalC (getAt [] (freeList fcT) 1) chalf).oneValue stage.unitC := by
  decide +kernel
theorem pin63 : ¬ (stage.evalC (getAt [] (freeList fcT) 1) chalf).oneValue stage.unitC :=
  listExtent_off (freeList fcT) 0 0 ctR ⟨4, 1⟩ ⟨5, 1⟩ 4 spH (spB BPair.unit ⟨4, 1⟩)
    spH (spB ⟨4, 1⟩ ⟨5, 1⟩) [Cover.done, cvR2] (by decide +kernel) (by decide +kernel)
    1 (by decide +kernel) (by decide +kernel) chalf (by decide +kernel) (by decide +kernel)
theorem pin64 : ¬ freeRead eT mT gT 4 { fcT with covs := [Cover.done] } := by decide +kernel
theorem pin65 : ¬ freeRead eT mT gT 4 { fcT with d := 2 } := by decide +kernel
theorem pin66 : ¬ freeRead eT mT gT 4 { fcT with dL := 2 } := by decide +kernel
private def xJ : BPair := ⟨3, 1⟩
theorem pin67 : ¬ (elim.minor (evalPC (freePMat eT mT gT 13 1) xJ 4 2)).oneValue BPair.unit
    ∧ ¬ (elim.minor (evalPC (freePMat eT mT gT 17 1) xJ 4 2)).oneValue BPair.unit := by
  decide +kernel
theorem pin68 : ¬ (elim.minor (evalPC (freePMat eT mT gT 13 1) xJ 4 2)).oneValue BPair.unit
    ∧ ¬ (elim.minor (evalPC (freePMat eT mT gT 17 1) xJ 4 2)).oneValue BPair.unit :=
  freeRead_jump eT mT gT 4 fcT (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) pin48 (by decide +kernel)
    xJ 4 (by decide +kernel) (by decide +kernel)

end freecell
