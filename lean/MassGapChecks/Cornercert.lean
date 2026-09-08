import MassGap.Cornercert
import MassGap.Kernel
/-!
The check module for `lem:corner`'s squares' certificate's matrix
reads.  `rowSq` at the two-by-three `mA = [[1, 2, 0], [0, 1, 3]]`
reads `5 + 10 = 15`, its transpose `[[1, 0], [2, 1], [0, 3]]`
reads `1 + 5 + 9 = 15` as well.  At `aH = [[1, 1], [1, -1]]`,
`aH^T aH = 2 I`, and `gB = [[1, 2], [3, 4]]`: `aH gB = [[4, 6],
[-2, -2]]` at `rowSq` `60`, the columns' forms at `2 I` reading
`2 · 10 + 2 · 20 = 60`.  The projector `pOne = [[1, 0], [0, 0]]`
at `v = (3, 4)` reads the form `9`, the residual `(0, 4)` its
square `16`, the sum the self-pairing `25`.  The local square at
`G = aH gB`, `c = 2`, `Π = I`: `60 + 2 · 0 = 2 · 30`, the theorem
route beside the kernel; the idempotence is load-bearing: at
`pTwo = 2 I`, `c = 1`, the display reads `60 + 30` against `30`,
refused.
-/

open ground elim inertia corner

private def one : BPair := BPair.ofNat 1

private def mA : Mat := [[one, BPair.ofNat 2, BPair.unit],
  [BPair.unit, one, BPair.ofNat 3]]

private def aH : Mat := [[one, one], [one, one.swap]]

private def gB : Mat := [[one, BPair.ofNat 2], [BPair.ofNat 3, BPair.ofNat 4]]

private def pOne : Mat := [[one, BPair.unit], [BPair.unit, BPair.unit]]

private def pTwo : Mat := [[BPair.ofNat 2, BPair.unit], [BPair.unit, BPair.ofNat 2]]

private def v34 : List BPair := [BPair.ofNat 3, BPair.ofNat 4]

private def resid (Pi : Mat) (u : List BPair) : BPair :=
  dotN (vecAdd u ((matVec Pi u).map BPair.swap))
    (vecAdd u ((matVec Pi u).map BPair.swap))

private def localDisp (G g Pi : Mat) (c : BPair) (n : Nat) : BPair :=
  rowSq G + c * bsum (fun a => resid Pi (getAt [] (transposeM g) a)) (List.range n)

example : (rowSq mA).oneValue (BPair.ofNat 15) := by decide +kernel
example : (rowSq (transposeM mA)).oneValue (BPair.ofNat 15) := by decide +kernel
example : (rowSq mA).oneValue (rowSq (transposeM mA)) :=
  rowSq_transpose 3 mA (by decide) (by decide)
example : (rowSq (matMul aH gB)).oneValue (BPair.ofNat 60) := by decide +kernel
example : (bsum (fun c => quadForm (matMul (transposeM aH) aH)
    (getAt [] (transposeM gB) c)) (List.range 2)).oneValue (BPair.ofNat 60) := by
  decide +kernel
example : (rowSq (matMul aH gB)).oneValue
    (bsum (fun c => quadForm (matMul (transposeM aH) aH)
      (getAt [] (transposeM gB) c)) (List.range 2)) :=
  rowSq_matMul 2 2 aH gB (by decide) (by decide) (by decide) (by decide) (by decide)
example : (quadForm pOne v34).oneValue (BPair.ofNat 9) := by decide +kernel
example : (resid pOne v34).oneValue (BPair.ofNat 16) := by decide +kernel
example : (quadForm pOne v34 + resid pOne v34).oneValue (dotN v34 v34) :=
  proj_split 2 pOne (by decide) (by decide +kernel) (by decide +kernel) v34 (by decide)
example : (localDisp (matMul aH gB) gB (elim.idMat 2) (BPair.ofNat 2) 2).oneValue
    (BPair.ofNat 2 * rowSq gB) := by decide +kernel
example : (localDisp (matMul aH gB) gB (elim.idMat 2) (BPair.ofNat 2) 2).oneValue
    (BPair.ofNat 2 * rowSq gB) :=
  local_square 2 2 2 (matMul aH gB) aH gB (elim.idMat 2) (BPair.ofNat 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (BPair.oneValue_refl _)
example : ¬ matOneValue (matMul pTwo pTwo) pTwo := by decide +kernel
example : ¬ (localDisp (matMul aH gB) gB pTwo (BPair.ofNat 1) 2).oneValue
    (BPair.ofNat 1 * rowSq gB) := by decide +kernel

/-! The kernel identity and the transports' orthogonality are
load-bearing: at `c = 1` against `aH^T aH = 2 I` the display reads
`60` against `30`, refused; at the fluxes `gB` in place of `aH gB`,
their squares `30` off the product's `60`, the display reads `30`
against `60`, refused.  The projector's symmetry is the tex's own
datum of the range projector. -/

example : ¬ matOneValue (matMul (transposeM aH) aH)
    (matScaleB (BPair.ofNat 1) (elim.idMat 2)) := by decide +kernel
example : ¬ (localDisp (matMul aH gB) gB (elim.idMat 2) (BPair.ofNat 1) 2).oneValue
    (BPair.ofNat 1 * rowSq gB) := by decide +kernel
example : ¬ (rowSq gB).oneValue (rowSq (matMul aH gB)) := by decide +kernel
example : ¬ (localDisp gB gB (elim.idMat 2) (BPair.ofNat 2) 2).oneValue
    (BPair.ofNat 2 * rowSq gB) := by decide +kernel

/-! `lem:corner`'s local square against the gradient deficit at two
plaquettes' fluxes `gF = [[1, 1], [2, 0]]`, the index `κ = 2` and
the count `d = 3`: the deficits `δ = (1, 2)` read the cleared
deficit `3 · 2 + 2 ≤ 12` and `3 · 4 + 8 ≤ 24`; at `c = 4`, the
residual `R = 2`, the squares' fold `G2 = 16` reads the local
square `16 + 8 ≡ 4 · 6`, and the count's multiple `48` sits below
`4 · (10 + 16) = 104`, the theorem route beside the kernel.  The
residual's side is load-bearing: at `R = -8` the fold reads `56`
and `168` against `104`, refused; and the pair's, at `c = -4` the
fold `-16` reads `-48` against `-104`, refused. -/

private def gF : Mat := [[one, one], [BPair.ofNat 2, BPair.unit]]

private def dF : Nat → BPair := fun p => getAt BPair.unit [one, BPair.ofNat 2] p

private def defRhs (κ d : BPair) : BPair :=
  bsum (fun p => (dF p + dF p) * κ * d + (dF p * dF p * κ).swap) (List.range 2)

example : (defRhs (BPair.ofNat 2) (BPair.ofNat 3)).oneValue (BPair.ofNat 26) := by
  decide +kernel
example : BPair.ofNat 3 * BPair.ofNat 16
    ≤ BPair.ofNat 4 * defRhs (BPair.ofNat 2) (BPair.ofNat 3) := by decide +kernel
example : BPair.ofNat 3 * BPair.ofNat 16
    ≤ BPair.ofNat 4 * defRhs (BPair.ofNat 2) (BPair.ofNat 3) :=
  sq_deficit 2 gF dF (BPair.ofNat 16) (BPair.ofNat 2) (BPair.ofNat 4)
    (BPair.ofNat 2) (BPair.ofNat 3) (by decide) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide +kernel)
example : ¬ (BPair.ofNat 3 * BPair.ofNat 56
    ≤ BPair.ofNat 4 * defRhs (BPair.ofNat 2) (BPair.ofNat 3)) := by decide +kernel
example : ¬ (BPair.unit ≤ (BPair.ofNat 8).swap) := by decide +kernel
example : (BPair.ofNat 56 + BPair.ofNat 4 * (BPair.ofNat 8).swap).oneValue
    (BPair.ofNat 4 * rowSq gF) := by decide +kernel
example : ¬ (BPair.ofNat 3 * (BPair.ofNat 16).swap
    ≤ (BPair.ofNat 4).swap * defRhs (BPair.ofNat 2) (BPair.ofNat 3)) := by
  decide +kernel
example : ((BPair.ofNat 16).swap + (BPair.ofNat 4).swap * BPair.ofNat 2).oneValue
    ((BPair.ofNat 4).swap * rowSq gF) := by decide +kernel

/-! The deficit read per row and the count's side are load-bearing:
at the deficits `(6, 1)` the first row reads `6 + 72 ≤ 72`, refused,
and the display `48 ≤ 4 · 10`, refused; at the count `-3` the side
parts and the display reads `-48 ≤ -184`, refused. -/

private def dG : Nat → BPair := fun p => getAt BPair.unit [BPair.ofNat 6, one] p

private def defRhsAt (δ : Nat → BPair) (κ d : BPair) : BPair :=
  bsum (fun p => (δ p + δ p) * κ * d + (δ p * δ p * κ).swap) (List.range 2)

example : ¬ (dotP (getAt [] gF 0) (getAt [] gF 0) * BPair.ofNat 3
    + dG 0 * dG 0 * BPair.ofNat 2 ≤ (dG 0 + dG 0) * BPair.ofNat 2 * BPair.ofNat 3) := by
  decide +kernel
example : ¬ (BPair.ofNat 3 * BPair.ofNat 16
    ≤ BPair.ofNat 4 * defRhsAt dG (BPair.ofNat 2) (BPair.ofNat 3)) := by decide +kernel
example : ¬ (BPair.unit ≤ (BPair.ofNat 3).swap) := by decide +kernel
example : ¬ ((BPair.ofNat 3).swap * BPair.ofNat 16
    ≤ BPair.ofNat 4 * defRhsAt dF (BPair.ofNat 2) (BPair.ofNat 3).swap) := by
  decide +kernel

/-! `lem:corner`'s assembly at two plaquettes, the scale pair
`[1 : 10]`, the count `d = 3`, the kernel's read `a = 4` and the
covering count `b = 5`, the shift `M = 27`: the deficits `(1, 2)`
against the terms `(2, 1)`, the squares' fold `G2 = 2` at the
deficit read `-1300 ≤ -1200`, the cross read `X = 3` at
`24 - 27 ≤ -3`, and `L0 = -3618`; the left member `289 + 49 -
3618 = -3280` sits below the right `600 · (-5) - 180 = -3180`,
the theorem route beside the kernel.  The shift's tie is
load-bearing: at `M' = 20` with `L0' = -2960` the left reads
`-2860`, refused; and the cross read's: at `X = 5` the right
reads `-3300`, refused. -/

private def cF : Nat → BPair := fun p => getAt BPair.unit [BPair.ofNat 2, one] p

private def n1 : BPair := one
private def s10 : BPair := BPair.ofNat 10
private def d3 : BPair := BPair.ofNat 3
private def a4 : BPair := BPair.ofNat 4
private def b5 : BPair := BPair.ofNat 5

private def sqFold (M : BPair) : BPair :=
  bsum (fun p => (s10 * dF p + M.swap) * (s10 * dF p + M.swap)) (List.range 2)

private def floorAt (M : BPair) : BPair :=
  bsum (fun _ => (d3 + d3) * d3 * (n1 * s10 * a4 + (s10 * s10).swap)
    + (M * M).swap) (List.range 2)

private def rightAt (G2 X : BPair) : BPair :=
  (d3 + d3) * (s10 * s10) * (G2.swap + (bsum cF (List.range 2)).swap)
    + (d3 + d3) * s10 * (n1 * X).swap

example : (floorAt (BPair.ofNat 27)).oneValue (BPair.ofNat 3618).swap := by
  decide +kernel
example : (sqFold (BPair.ofNat 27) + floorAt (BPair.ofNat 27)).oneValue
    (BPair.ofNat 3280).swap := by decide +kernel
example : (rightAt (BPair.ofNat 2) (BPair.ofNat 3)).oneValue
    (BPair.ofNat 3180).swap := by decide +kernel
example : sqFold (n1 * d3 * (a4 + b5)) + floorAt (n1 * d3 * (a4 + b5))
    ≤ rightAt (BPair.ofNat 2) (BPair.ofNat 3) := by decide +kernel
example : sqFold (n1 * d3 * (a4 + b5)) + floorAt (n1 * d3 * (a4 + b5))
    ≤ rightAt (BPair.ofNat 2) (BPair.ofNat 3) :=
  floor_assembly 2 dF cF (BPair.ofNat 2) (BPair.ofNat 3) d3 n1 s10 a4 b5
    (floorAt (n1 * d3 * (a4 + b5))) (by decide) (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (BPair.oneValue_refl _)
example : ¬ (sqFold (BPair.ofNat 20) + floorAt (BPair.ofNat 20)
    ≤ rightAt (BPair.ofNat 2) (BPair.ofNat 3)) := by decide +kernel
example : ¬ (sqFold (n1 * d3 * (a4 + b5)) + floorAt (n1 * d3 * (a4 + b5))
    ≤ rightAt (BPair.ofNat 2) (BPair.ofNat 5)) := by decide +kernel
example : ¬ (bsum (fun _ => n1 * a4 * d3) (List.range 2)
    + (n1 * (a4 + b5) * bsum dF (List.range 2)).swap
      ≤ (n1 * BPair.ofNat 5).swap) := by decide +kernel

/-! The seam from the cleared deficit read to the assembly's binder:
at the fluxes `gF`, `c = 4 ≡ 2 + 2` at the index `2`, the cleared
fold `16 ≡ 4 · 4 · 1`, so the uncleared fold reads `1` and at the
scale `10` the deficit read is `-1300 ≤ -600`, the theorem route
through `sq_deficit`'s instance beside the kernel; and the assembly
at that fold, `-3640 ≤ -2940`, the whole chain at one data set.  The
pair's tie is load-bearing: at the index `3` against the pair `4`
with the cleared fold `48 ≡ 16 · 3`, the cleared read `144 ≤ 156`
holds while the seam's read `-1300 ≤ -1800` is refused. -/

private def seamLhs (δ : Nat → BPair) : BPair :=
  bsum (fun p => s10 * δ p * (s10 * δ p) + ((d3 + d3) * (s10 * s10) * δ p).swap)
    (List.range 2)

example : (seamLhs dF).oneValue (BPair.ofNat 1300).swap := by decide +kernel
example : seamLhs dF ≤ ((d3 + d3) * (s10 * s10) * BPair.ofNat 1).swap := by
  decide +kernel
example : seamLhs dF ≤ ((d3 + d3) * (s10 * s10) * BPair.ofNat 1).swap :=
  deficit_seam 2 dF (BPair.ofNat 1) (BPair.ofNat 16) (BPair.ofNat 4) (BPair.ofNat 2) d3 s10
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (sq_deficit 2 gF dF (BPair.ofNat 16) (BPair.ofNat 2) (BPair.ofNat 4) (BPair.ofNat 2) d3
      (by decide) (by decide +kernel) (by decide) (by decide) (by decide) (by decide +kernel))
example : ¬ (BPair.ofNat 4).oneValue (BPair.ofNat 3 + BPair.ofNat 3) := by decide +kernel
example : d3 * BPair.ofNat 48 ≤ BPair.ofNat 4 * defRhsAt dF (BPair.ofNat 3) d3 := by
  decide +kernel
example : ¬ (seamLhs dF ≤ ((d3 + d3) * (s10 * s10) * BPair.ofNat 3).swap) := by
  decide +kernel

/-! The assembly at the scale pair `[3 : 10]`, the shift `M = 81`:
the left member `5041 + 3721 - 12402 = -3640` sits below the right
`-3540`, the theorem route beside the kernel.  The deficit read is
load-bearing: at the squares' fold `G2 = 3` it reads `-1300 ≤ -1800`,
refused, and the display's right member `-4140`, refused; and the
plaquette terms' tie: at the terms `(2, 2)` the second term parts the
tie and the right member reads `-4140`, refused. -/

private def n3 : BPair := BPair.ofNat 3
private def cG : Nat → BPair := fun p => getAt BPair.unit [BPair.ofNat 2, BPair.ofNat 2] p

private def floorAt3 (M : BPair) : BPair :=
  bsum (fun _ => (d3 + d3) * d3 * (n3 * s10 * a4 + (s10 * s10).swap)
    + (M * M).swap) (List.range 2)

private def rightAt3 (G2 X : BPair) (χ : Nat → BPair) : BPair :=
  (d3 + d3) * (s10 * s10) * (G2.swap + (bsum χ (List.range 2)).swap)
    + (d3 + d3) * s10 * (n3 * X).swap

example : (sqFold (BPair.ofNat 81) + floorAt3 (BPair.ofNat 81)).oneValue
    (BPair.ofNat 3640).swap := by decide +kernel
example : (rightAt3 (BPair.ofNat 2) (BPair.ofNat 3) cF).oneValue
    (BPair.ofNat 3540).swap := by decide +kernel
example : sqFold (n3 * d3 * (a4 + b5)) + floorAt3 (n3 * d3 * (a4 + b5))
    ≤ rightAt3 (BPair.ofNat 2) (BPair.ofNat 3) cF :=
  floor_assembly 2 dF cF (BPair.ofNat 2) (BPair.ofNat 3) d3 n3 s10 a4 b5
    (floorAt3 (n3 * d3 * (a4 + b5))) (by decide) (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (BPair.oneValue_refl _)
example : ¬ (bsum (fun p => s10 * dF p * (s10 * dF p) + ((d3 + d3) * (s10 * s10) * dF p).swap)
    (List.range 2) ≤ ((d3 + d3) * (s10 * s10) * BPair.ofNat 3).swap) := by decide +kernel
example : ¬ (sqFold (n3 * d3 * (a4 + b5)) + floorAt3 (n3 * d3 * (a4 + b5))
    ≤ rightAt3 (BPair.ofNat 3) (BPair.ofNat 3) cF) := by decide +kernel
example : sqFold (n3 * d3 * (a4 + b5)) + floorAt3 (n3 * d3 * (a4 + b5))
    ≤ rightAt3 (BPair.ofNat 1) (BPair.ofNat 3) cF :=
  floor_assembly 2 dF cF (BPair.ofNat 1) (BPair.ofNat 3) d3 n3 s10 a4 b5
    (floorAt3 (n3 * d3 * (a4 + b5))) (by decide) (by decide)
    (deficit_seam 2 dF (BPair.ofNat 1) (BPair.ofNat 16) (BPair.ofNat 4) (BPair.ofNat 2) d3 s10
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
      (sq_deficit 2 gF dF (BPair.ofNat 16) (BPair.ofNat 2) (BPair.ofNat 4) (BPair.ofNat 2) d3
        (by decide) (by decide +kernel) (by decide) (by decide) (by decide)
        (by decide +kernel)))
    (by decide +kernel) (by decide +kernel) (BPair.oneValue_refl _)
example : ¬ (dF 1 + cG 1).oneValue d3 := by decide +kernel
example : ¬ (sqFold (n3 * d3 * (a4 + b5)) + floorAt3 (n3 * d3 * (a4 + b5))
    ≤ rightAt3 (BPair.ofNat 2) (BPair.ofNat 3) cG) := by decide +kernel

/-! The cross read's deviation at the four-link loop: the tree path
the arc `U2† U1†` with the backtrack `U5 U5†` reads the arc's own
joint insertion, the backtrack withdrawing, so the deviation at the
forward sign reads the sum's unit at the evaluation identity; at the
other arc `U3 U4` as well, either arc one value; and the word `U4†`
off the arc holds a deviation. -/

open states lap kernel

private def fLoopC : FList :=
  [(1, false), (2, false), (3, false), (4, false),
   (4, true), (3, true), (2, true), (1, true)]
private def loopW : List Nat := [3, 0, 1, 2, 7, 4, 5, 6]
private def unitW : List Nat := [7, 6, 5, 4, 3, 2, 1, 0]
private def invDf4 : poly.PPair :=
  poly.pMul invDfP (poly.pMul invDfP (poly.pMul invDfP invDfP))
private def chiC : Comb := [(loopW, poly.pOne), (unitW, poly.pMul negP invDf4)]
private def arcB : FList := [(3, false), (4, false)]
private def backA : FList := [(5, false), (5, true), (2, true), (1, true)]
private def offW : FList := [(4, true)]

example : evalEqRead (fLoopC ++ backA ++ daggerW backA)
    (crossDev fLoopC backA 3 1 poly.pOne chiC) [] := by decide +kernel
example : evalEqRead (fLoopC ++ arcB ++ daggerW arcB)
    (crossDev fLoopC arcB 3 1 poly.pOne chiC) [] := by decide +kernel
example : ¬ evalEqRead (fLoopC ++ offW ++ daggerW offW)
    (crossDev fLoopC offW 3 1 poly.pOne chiC) [] := by decide +kernel

/-! At the loop with link `3` traversed backward, `tr(U1 U2 U3† U4)`,
the arc `U3 U2† U1†` from the base's tail to the link's tail: the
deviation reads the sum's unit at the traversal sign, the balance
partner, and the forward sign is refused. -/

private def fLoopB : FList :=
  [(1, false), (2, false), (3, true), (4, false),
   (4, true), (3, false), (2, true), (1, true)]
private def arcC : FList := [(3, false), (2, true), (1, true)]

example : evalEqRead (fLoopB ++ arcC ++ daggerW arcC)
    (crossDev fLoopB arcC 3 1 negP chiC) [] := by decide +kernel
example : ¬ evalEqRead (fLoopB ++ arcC ++ daggerW arcC)
    (crossDev fLoopB arcC 3 1 poly.pOne chiC) [] := by decide +kernel

-- the mode's variance read (`mode_variance`) at the scale `[1 : 3]` and
-- the solve `[3 : 2]`: the mode square's moment 3 at the solve against
-- the unit's moment 3, the square's square's moment 5 at the profile's two
-- reads 3 and 6, the side 2 at `dim G = 2`, the remainders and their caps
-- at the unit: 1296 ≤ 1296 decided and through the theorem; at the
-- square's square's moment 4 the profile's second read refuses and the
-- conclusion parts, 1296 against 936
example : BPair.ofNat 4 * BPair.ofNat 1 * BPair.ofNat 2 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat
    3 * BPair.ofNat 3 + BPair.ofNat 4 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 3 *
    BPair.ofNat 3 * BPair.ofNat 2 ≤ BPair.ofNat 4 * BPair.ofNat 5 * BPair.ofNat 3 * BPair.ofNat
    3 * BPair.ofNat 3 * BPair.ofNat 2 + BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 2 *
    (BPair.ofNat 2 + BPair.ofNat 2) * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 3 +
    BPair.ofNat 4 * BPair.ofNat 1 * BPair.ofNat 3 * BPair.unit * BPair.ofNat 2 * BPair.ofNat 3 +
    BPair.ofNat 4 * BPair.ofNat 1 * BPair.ofNat 3 * BPair.unit * BPair.ofNat 2 * BPair.ofNat 3 := by
  decide +kernel
example : BPair.ofNat 4 * BPair.ofNat 1 * BPair.ofNat 2 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat
    3 * BPair.ofNat 3 + BPair.ofNat 4 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 3 *
    BPair.ofNat 3 * BPair.ofNat 2 ≤ BPair.ofNat 4 * BPair.ofNat 5 * BPair.ofNat 3 * BPair.ofNat
    3 * BPair.ofNat 3 * BPair.ofNat 2 + BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 2 *
    (BPair.ofNat 2 + BPair.ofNat 2) * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 3 +
    BPair.ofNat 4 * BPair.ofNat 1 * BPair.ofNat 3 * BPair.unit * BPair.ofNat 2 * BPair.ofNat 3 +
    BPair.ofNat 4 * BPair.ofNat 1 * BPair.ofNat 3 * BPair.unit * BPair.ofNat 2 * BPair.ofNat 3 :=
  mode_variance
    (BPair.ofNat 3) (BPair.ofNat 5) (BPair.ofNat 3) (BPair.ofNat 6) (BPair.ofNat 3)
    (BPair.ofNat 2) (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 3) (BPair.ofNat 3)
    (BPair.ofNat 2) BPair.unit BPair.unit BPair.unit BPair.unit
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
example : ¬ (BPair.ofNat 2 * BPair.ofNat 6 * BPair.ofNat 3 ≤ BPair.ofNat 2 * BPair.ofNat 4 * BPair.ofNat
    3 + BPair.ofNat 1 * BPair.ofNat 6) := by decide +kernel
example : ¬ (BPair.ofNat 4 * BPair.ofNat 1 * BPair.ofNat 2 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat
    3 * BPair.ofNat 3 + BPair.ofNat 4 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 3 *
    BPair.ofNat 3 * BPair.ofNat 2 ≤ BPair.ofNat 4 * BPair.ofNat 4 * BPair.ofNat 3 * BPair.ofNat
    3 * BPair.ofNat 3 * BPair.ofNat 2 + BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 2 *
    (BPair.ofNat 2 + BPair.ofNat 2) * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 3 +
    BPair.ofNat 4 * BPair.ofNat 1 * BPair.ofNat 3 * BPair.unit * BPair.ofNat 2 * BPair.ofNat 3 +
    BPair.ofNat 4 * BPair.ofNat 1 * BPair.ofNat 3 * BPair.unit * BPair.ofNat 2 * BPair.ofNat 3) := by
  decide +kernel

-- the coordinate identity (`coord_identity`) at one link and one generator
-- index: every weight one, the remainders at the unit, the exponent's
-- gradient read the coordinate's balance partner, decided and through the
-- theorem; at the gradient read at the unit the parts identity refuses and
-- the conclusion parts at the remainder's read one, 2 against 1
example : (BPair.ofNat 1 * BPair.ofNat 1
      + bsum (fun _ => BPair.ofNat 1 * BPair.unit) (List.range 1)
      + bsum (fun _ => BPair.ofNat 1 * BPair.unit) (List.range 1)
      + BPair.ofNat 1 * bsum (fun _ => BPair.ofNat 1 * BPair.unit) (List.range 1)).oneValue
    (BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 1) := by decide +kernel
example : (BPair.ofNat 1 * BPair.ofNat 1
      + bsum (fun _ => BPair.ofNat 1 * BPair.unit) (List.range 1)
      + bsum (fun _ => BPair.ofNat 1 * BPair.unit) (List.range 1)
      + BPair.ofNat 1 * bsum (fun _ => BPair.ofNat 1 * BPair.unit) (List.range 1)).oneValue
    (BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 1) :=
  coord_identity 1 1 (fun _ => BPair.ofNat 1) (fun _ => BPair.ofNat 1) (fun _ => BPair.unit)
    (fun _ => BPair.unit) (fun _ => BPair.ofNat 1) (fun _ => BPair.unit)
    (fun _ _ => (BPair.ofNat 1).swap) (fun _ _ => BPair.ofNat 1)
    (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun _ _ _ _ => by decide +kernel)
example : ¬ ((BPair.unit + BPair.ofNat 1 * BPair.ofNat 1).oneValue BPair.unit) := by decide +kernel
example : ¬ ((BPair.ofNat 1 * BPair.ofNat 1
      + bsum (fun _ => BPair.ofNat 1 * BPair.ofNat 1) (List.range 1)
      + bsum (fun _ => BPair.ofNat 1 * BPair.unit) (List.range 1)
      + BPair.ofNat 1 * bsum (fun _ => BPair.ofNat 1 * BPair.unit) (List.range 1)).oneValue
    (BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 1)) := by decide +kernel

-- the excess read (`excess_read`) at the scale `[1 : 2]`, the mass
-- `[1 : 2]`, every coefficient one and the unit's moment two: the flux
-- moments' fold 2 at the deficit's moment 1, the gradient deficit at the
-- index one, the deficit caps 1 and 1 at the clearing, the squares' cap 60
-- with the slack's 2 read the excess 31, its clearing 992 at or below the
-- displayed cap 1016, decided and through the theorem; at the squares'
-- cap 62 the cap's binder refuses and the excess 32's clearing 1024 parts
example : BPair.ofNat 31 * (BPair.ofNat 2 * BPair.ofNat 2 * BPair.ofNat 2) *
    (BPair.ofNat 2 * BPair.ofNat 2) ≤ BPair.ofNat 192 *
    (BPair.ofNat 1 * BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1)) *
    (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 1 * (BPair.ofNat 2 * BPair.ofNat 2) +
    (BPair.ofNat 24 * (BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1)) + BPair.ofNat 2 * (BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1)) + BPair.ofNat 3 * (BPair.ofNat 1 * BPair.ofNat 1) + BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1) + BPair.ofNat 1)
    * (BPair.ofNat 2 * BPair.ofNat 2) * (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 2 := by
  decide +kernel
example : BPair.ofNat 31 * (BPair.ofNat 2 * BPair.ofNat 2 * BPair.ofNat 2) *
    (BPair.ofNat 2 * BPair.ofNat 2) ≤ BPair.ofNat 192 *
    (BPair.ofNat 1 * BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1)) *
    (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 1 * (BPair.ofNat 2 * BPair.ofNat 2) +
    (BPair.ofNat 24 * (BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1)) + BPair.ofNat 2 * (BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1)) + BPair.ofNat 3 * (BPair.ofNat 1 * BPair.ofNat 1) + BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1) + BPair.ofNat 1)
    * (BPair.ofNat 2 * BPair.ofNat 2) * (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 2 :=
  excess_read
    (BPair.ofNat 31) (BPair.ofNat 60) (BPair.ofNat 2) (BPair.ofNat 2) (BPair.ofNat 2)
    (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1)
    (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1)
    (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : ¬ (BPair.ofNat 62 * (BPair.ofNat 2 * BPair.ofNat 2) *
    (BPair.ofNat 2 * BPair.ofNat 2 * BPair.ofNat 2) ≤ BPair.ofNat 96 *
    (BPair.ofNat 1 * ((BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 2)) *
    (BPair.ofNat 2 * BPair.ofNat 2 * BPair.ofNat 2) + BPair.ofNat 12 *
    (BPair.ofNat 1 * BPair.ofNat 1) * (BPair.ofNat 2 * BPair.ofNat 2) *
    (BPair.ofNat 2 * BPair.ofNat 2 * BPair.ofNat 2) + BPair.ofNat 3 *
    ((BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 1) * (BPair.ofNat 2 * BPair.ofNat 2) *
    BPair.ofNat 2) := by decide +kernel
example : ¬ (BPair.ofNat 32 * (BPair.ofNat 2 * BPair.ofNat 2 * BPair.ofNat 2) *
    (BPair.ofNat 2 * BPair.ofNat 2) ≤ BPair.ofNat 192 *
    (BPair.ofNat 1 * BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1)) *
    (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 1 * (BPair.ofNat 2 * BPair.ofNat 2) +
    (BPair.ofNat 24 * (BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1)) + BPair.ofNat 2 * (BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1)) + BPair.ofNat 3 * (BPair.ofNat 1 * BPair.ofNat 1) + BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1) + BPair.ofNat 1)
    * (BPair.ofNat 2 * BPair.ofNat 2) * (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 2) := by decide +kernel

-- the mode read (`mode_read`) at the scale `[1 : 2]`, the mass `[1 : 2]`,
-- the solve `[2 : 2]`, the mode read `[1 : 3]`, the side one, `dim G = 1`
-- and the deficits' moment 2: the deficit moments 1 and 2 at the mode
-- weight, the mode square's 1, the squares' cap 72, the slack 3 and the
-- fluxes' range read 10 read the form 152 at the deficits' moment, the
-- excess 76, its clearing 3648 at or below the displayed cap 5860, decided
-- and through the theorem; at the range read 198 the second moments'
-- binder refuses and the excess 123's clearing 5904 parts
example : BPair.ofNat 76 * (BPair.ofNat 2 * BPair.ofNat 2) * (BPair.ofNat 2 * BPair.ofNat 2) *
    BPair.ofNat 3 ≤ BPair.ofNat 16 * BPair.ofNat 1 *
    (BPair.ofNat 1 * BPair.ofNat 2 + BPair.ofNat 2 * BPair.ofNat 1) * BPair.ofNat 1 *
    BPair.ofNat 1 * BPair.ofNat 2 * BPair.ofNat 2 + BPair.ofNat 384 *
    (BPair.ofNat 1 * BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1)) *
    (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 1 * BPair.ofNat 2 * BPair.ofNat 3 +
    (BPair.ofNat 32 * (BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 2 + BPair.ofNat 2 * BPair.ofNat 1)) * BPair.ofNat 2 + BPair.ofNat 384 * (BPair.ofNat 1 * BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1)) * BPair.ofNat 1 + (BPair.ofNat 48 * (BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1) * (BPair.ofNat 1 + BPair.ofNat 1)) + BPair.ofNat 6 * (BPair.ofNat 1 * BPair.ofNat 1 + BPair.ofNat 1) + BPair.ofNat 2 * (BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1) * (BPair.ofNat 1 + BPair.ofNat 1)) + BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1 + BPair.ofNat 1) + BPair.ofNat 1) * (BPair.ofNat 2 * BPair.ofNat 2))
    * (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 3 := by
  decide +kernel
example : BPair.ofNat 76 * (BPair.ofNat 2 * BPair.ofNat 2) * (BPair.ofNat 2 * BPair.ofNat 2) *
    BPair.ofNat 3 ≤ BPair.ofNat 16 * BPair.ofNat 1 *
    (BPair.ofNat 1 * BPair.ofNat 2 + BPair.ofNat 2 * BPair.ofNat 1) * BPair.ofNat 1 *
    BPair.ofNat 1 * BPair.ofNat 2 * BPair.ofNat 2 + BPair.ofNat 384 *
    (BPair.ofNat 1 * BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1)) *
    (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 1 * BPair.ofNat 2 * BPair.ofNat 3 +
    (BPair.ofNat 32 * (BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 2 + BPair.ofNat 2 * BPair.ofNat 1)) * BPair.ofNat 2 + BPair.ofNat 384 * (BPair.ofNat 1 * BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1)) * BPair.ofNat 1 + (BPair.ofNat 48 * (BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1) * (BPair.ofNat 1 + BPair.ofNat 1)) + BPair.ofNat 6 * (BPair.ofNat 1 * BPair.ofNat 1 + BPair.ofNat 1) + BPair.ofNat 2 * (BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1) * (BPair.ofNat 1 + BPair.ofNat 1)) + BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1 + BPair.ofNat 1) + BPair.ofNat 1) * (BPair.ofNat 2 * BPair.ofNat 2))
    * (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 3 :=
  mode_read
    (BPair.ofNat 76) (BPair.ofNat 2) (BPair.ofNat 152) (BPair.ofNat 10) (BPair.ofNat 72)
    (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 1)
    (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 2)
    (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1)
    (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1)
    (BPair.ofNat 1) (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 2)
    (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : ¬ (BPair.ofNat 198 * BPair.ofNat 3 ≤ BPair.ofNat 8 * (BPair.ofNat 1 * BPair.ofNat 1) *
    BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 1 + BPair.ofNat 8 * BPair.ofNat 1 * BPair.ofNat
    1 * BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 3) := by decide +kernel
example : ¬ (BPair.ofNat 123 * (BPair.ofNat 2 * BPair.ofNat 2) * (BPair.ofNat 2 * BPair.ofNat 2) *
    BPair.ofNat 3 ≤ BPair.ofNat 16 * BPair.ofNat 1 *
    (BPair.ofNat 1 * BPair.ofNat 2 + BPair.ofNat 2 * BPair.ofNat 1) * BPair.ofNat 1 *
    BPair.ofNat 1 * BPair.ofNat 2 * BPair.ofNat 2 + BPair.ofNat 384 *
    (BPair.ofNat 1 * BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1)) *
    (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 1 * BPair.ofNat 2 * BPair.ofNat 3 +
    (BPair.ofNat 32 * (BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 2 + BPair.ofNat 2 * BPair.ofNat 1)) * BPair.ofNat 2 + BPair.ofNat 384 * (BPair.ofNat 1 * BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1)) * BPair.ofNat 1 + (BPair.ofNat 48 * (BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1) * (BPair.ofNat 1 + BPair.ofNat 1)) + BPair.ofNat 6 * (BPair.ofNat 1 * BPair.ofNat 1 + BPair.ofNat 1) + BPair.ofNat 2 * (BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1) * (BPair.ofNat 1 + BPair.ofNat 1)) + BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1 + BPair.ofNat 1) + BPair.ofNat 1) * (BPair.ofNat 2 * BPair.ofNat 2))
    * (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 3) := by decide +kernel

-- the key's quarters (`key_quarters`) at the excess and the mode read
-- themselves, the two assemblies' conclusions its first two binders with
-- `P_u` and `P_v` read off their groups, 124 and 1100 at the mass's
-- square: the scale `[1 : 2]`, the mass `[1 : 2]`, the mode read `[1 : 3]`
-- and the floor `[613 : 1]`, the side, mass and scale comparisons at
-- 192 < 1839, 2304 < 2452 and 4896 < 4904, the reads' sum's clearing 214
-- under the floor's 613, decided and through the theorem; at the floor
-- `[300 : 2]` the mass comparison refuses, 4608 against 1200, and the
-- sum's 428 parts from 300
example : (BPair.ofNat 31 + BPair.ofNat 76) * BPair.ofNat 2 * BPair.ofNat 1
    < BPair.ofNat 1 * BPair.ofNat 613 := by decide +kernel
example : (BPair.ofNat 31 + BPair.ofNat 76) * BPair.ofNat 2 * BPair.ofNat 1
    < BPair.ofNat 1 * BPair.ofNat 613 :=
  key_quarters (BPair.ofNat 31) (BPair.ofNat 76) _ _ (BPair.ofNat 1) (BPair.ofNat 1)
    (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 1)
    (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 613)
    (BPair.ofNat 1)
    (excess_read
      (BPair.ofNat 31) (BPair.ofNat 60) (BPair.ofNat 2) (BPair.ofNat 2) (BPair.ofNat 2)
      (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1)
      (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1)
      (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 2)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (mode_read
      (BPair.ofNat 76) (BPair.ofNat 2) (BPair.ofNat 152) (BPair.ofNat 10) (BPair.ofNat 72)
      (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 1)
      (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 2)
      (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1)
      (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1)
      (BPair.ofNat 1) (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 2)
      (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : ¬ (BPair.ofNat 2304 * (BPair.ofNat 1 * BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1)) *
    (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 2 < BPair.ofNat 300 *
    (BPair.ofNat 2 * BPair.ofNat 2)) := by decide +kernel
example : ¬ ((BPair.ofNat 31 + BPair.ofNat 76) * BPair.ofNat 2 * BPair.ofNat 2
    < BPair.ofNat 1 * BPair.ofNat 300) := by decide +kernel
