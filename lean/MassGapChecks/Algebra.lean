import MassGap.Algebra
/-!
The check module for `def:algebra`'s read layer: the batteries
re-read the changed edge by kernel `decide` at the label calculus's
instantiation — the unit law's row (`row(𝟏, θ) = [θ]`, the far
factorization's per-link read), the plaquette rows at the square
(the unit assignment's one target the `θ`-loop; the fundamental
loop's targets the constant loops with the diagonal among them, the
walk's `c₁` shape at two and three letters; the `θ`-loop's targets
with the all-unit member dropped to the unit line), the involution's
reads (the fundamental loop to its dual's, the self-dual `θ`-loop
fixed, the double dual the identity), and the unit-coordinate read
(one at the unit assignment, the sum's unit at an occupied
support, `Eval(χ_θ) = δ_{θ𝟏}` among the instances).

The determination's batteries read the product `tr U · tr U†` over
the `(U, U†)` window: the window Gram's displayed values
(`[[2, d_f], [d_f, d_f²]]` at the determinant `d_f²`, `Eval(|tr U|⁴)
= 2` the Weingarten pairing's own), the solve at `det·(1, 0)` with
the pairing identity's verification whole and the adjugate's solved
witness beside it, the beyond-window agreement — the one-member
window's coordinate against the full window's at the cleared
cross comparison, each side's determinant crossing — and the
refusal at the forged vector carrying the determinant in the null
coordinate's place.
-/
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

open ground lattice fusion algebra

private def uA : List places.Shape := List.replicate 4 (labels.unitL 2)

/-! The unit law's row, the far factorization's per-link read. -/

example : (dataA 2).row (labels.unitL 2) (adjchar.theta 2)
    = [adjchar.theta 2] := by decide +kernel
example : (dataA 3).row (labels.unitL 3) (adjchar.theta 3)
    = [adjchar.theta 3] := by decide +kernel

/-! The plaquette rows at the square: the unit assignment's one
target, the fundamental loop's constant loops with the diagonal
among them, and the `θ`-loop's with the all-unit member dropped to
the unit line. -/

example : plaqRow (dataA 2) square sqPlaq uA
    = [List.replicate 4 [2, 0]] := by decide +kernel
example : plaqRow (dataA 2) square sqPlaq (List.replicate 4 [1, 0])
    = [List.replicate 4 [3, 0], List.replicate 4 [1, 0]] := by decide +kernel
example : plaqRow (dataA 2) square sqPlaq (List.replicate 4 [2, 0])
    = [List.replicate 4 [4, 0], List.replicate 4 [2, 0]] := by decide +kernel
example : plaqRow (dataA 3) square sqPlaq (List.replicate 4 [1, 0, 0])
    = [List.replicate 4 [2, 1, 0], List.replicate 4 [0, 2, 0],
       List.replicate 4 [1, 0, 0]] := by decide +kernel

/-! The involution's reads: contour reversal at the linkwise
duals. -/

example : conj (dataA 3) (List.replicate 4 [1, 0, 0])
    = List.replicate 4 [0, 1, 0] := by decide +kernel
example : conj (dataA 3) (conj (dataA 3) (List.replicate 4 [1, 0, 0]))
    = List.replicate 4 [1, 0, 0] := by decide +kernel
example : conj (dataA 3) (List.replicate 4 (adjchar.theta 3))
    = List.replicate 4 (adjchar.theta 3) := by decide +kernel

/-! The unit-coordinate read: one at the unit assignment, the sum's
unit at an occupied support. -/

example : evalConf (dataA 2) uA = 1 := by decide +kernel
example : evalConf (dataA 2) (List.replicate 4 [1, 0]) = 0 := by decide +kernel
example : evalConf (dataA 2) (List.replicate 4 (adjchar.theta 2))
    = 0 := by decide +kernel

/-! The determination at the presentation Gram: the two-factor site
`(U, U†)`, its window the two wirings, and the product's factors
the single `U` and the single `U†` — so `tr U · tr U†` is the
window's first member and the solve reads its coordinate. -/

private def dF2 : states.FList := [(false, false), (false, true)]
private def dWs : List states.Comb :=
  [[([0, 1], poly.pOne)], [([1, 0], poly.pOne)]]
private def dAU : states.Comb := [([0], poly.pOne)]
private def dUD : states.Comb := [([0], poly.pOne)]
private def dX :=
  algebra.prodSolve dF2 [(false, false)] [(false, true)] dWs dAU dUD
private def dWs1 : List states.Comb := [[([0, 1], poly.pOne)]]
private def dX1 :=
  algebra.prodSolve dF2 [(false, false)] [(false, true)] dWs1 dAU dUD
private def dG := algebra.windowGram dF2 dWs
private def dM := genericlift.ppminor dG
private def dRhs :=
  algebra.prodRhs dF2 [(false, false)] [(false, true)] dWs dAU dUD
private def dG1 := algebra.windowGram dF2 dWs1
private def dM1 := genericlift.ppminor dG1

/-! The window Gram's values: `[[2, d_f], [d_f, d_f²]]` at the
determinant `d_f²` — `Eval(|tr U|⁴) = 2` the Weingarten pairing's
own value. -/

example : genericlift.crossNull
    (ground.getAt poly.pZero (ground.getAt [] dG 0) 0)
    ([⟨3, 1⟩], poly.one) := by decide +kernel
example : genericlift.crossNull
    (ground.getAt poly.pZero (ground.getAt [] dG 0) 1)
    (wg.dfPow 1, poly.one) := by decide +kernel
example : genericlift.crossNull dM (wg.dfPow 2, poly.one) := by decide +kernel

/-! The solve's verification and its coordinates: the pairing
identity whole, the first coordinate the determinant and the second
the sum's unit, with the adjugate's solved witness beside them. -/

example : algebra.prodReadAt dG dM dRhs dX := by decide +kernel
example : elim.matOcc dG = true := by decide +kernel
example : genericlift.crossNull (ground.getAt poly.pZero dX 0)
    dM := by decide +kernel
example : genericlift.crossNull (ground.getAt poly.pZero dX 1)
    poly.pZero := by decide +kernel
example : genericlift.ppadjRead dG := by decide +kernel

/-! The beyond-window agreement: the one-member window solves the
identity too, and the two coordinates read one value at the cleared
cross comparison — each side scaled by the other window's
determinant, `2 · d_f² = d_f² · 2`. -/

example : algebra.prodRead dF2 [(false, false)] [(false, true)]
    dWs1 dAU dUD dX1 := by decide +kernel
example : genericlift.crossNull
    (poly.pMul (ground.getAt poly.pZero dX1 0) dM)
    (poly.pMul (ground.getAt poly.pZero dX 0) dM1)
  := by decide +kernel

/-! The isolating refusal: the forged vector at the determinant in
the null coordinate's place. -/

example : ¬ algebra.prodReadAt dG dM dRhs [dM, dM] := by decide +kernel
