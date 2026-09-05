import MassGap.Fpcap
/-!
The check module for `lem:fpcap`: the batteries re-read the fusion
form's two-sided dimension cap by kernel `decide` at the label
calculus's instantiation, the window `(𝟏, θ)` at two letters.  The
form's matrix at `θ` is the walk's own `[[0, 1], [1, 1]]`; the
quadratic form is decided at two committed vectors — the occupied
pair `(1, 2)` at eight and the swap-signed `(1, -1)` at the
memberwise swap of one — with both cap sides decided beside the
theorems' own instances, whose hypothesis terms are the interface's
own decided reads: each window Prop is the Boolean fold over its
key range, so the term is the kernel's verdict at the window.  The
composition read
rides the fundamental `f = (1, 0)` with the intermediate list
`(f, (3, 0))`, the display's window carrier at `lem:loopcap`'s
consumer.

The eigen row's boundary values are pinned rather than a forged
table: at the window the row folds read `3 ≤ 3 · 1` at the unit —
tight, the cap's own boundary — and `4 ≤ 3 · 3` at `θ`, so
`rowCap`'s slack is exercised on both sides.  The zero-dimension
clause needs no pin: at the label calculus every window dimension
is a Weyl dimension, positive by construction, so `hdim` is
structural at `dataA` and the corner the theorem's docstring names
is unreachable at this interface.
-/
set_option maxHeartbeats 16000000

open ground fusion elim fpcap

private def F : Data (List Nat) := dataA 2

private def th : List Nat := adjchar.theta 2

private def win : List (List Nat) := [labels.unitL 2, adjchar.theta 2]

private def u1 : List BPair := [BPair.ofNat 1, BPair.ofNat 2]

private def u2 : List BPair := [BPair.ofNat 1, (BPair.ofNat 1).swap]

/-! The form's matrix at `θ` over the window: the walk's own
`[[0, 1], [1, 1]]`, the vacuum defect at the unit's diagonal. -/

example : fusionMat F th win
    = [[BPair.ofNat 0, BPair.ofNat 1],
       [BPair.ofNat 1, BPair.ofNat 1]] := by decide +kernel

/-! The form at two committed vectors, the occupied pair and the
swap-signed one. -/

example : (inertia.quadForm (fusionMat F th win) u1).oneValue
    (BPair.ofNat 8) := by decide +kernel

example : (inertia.quadForm (fusionMat F th win) u2).oneValue
    (BPair.ofNat 1).swap := by decide +kernel

/-! Both cap sides decided at the two vectors: the dimension
against the gram above, the summed form at or above the sum's unit
below. -/

example : ¬ (BPair.ofNat (F.dim th) * dotN u1 u1
    < inertia.quadForm (fusionMat F th win) u1) := by decide +kernel

example : ¬ (BPair.ofNat (F.dim th) * dotN u2 u2
    < inertia.quadForm (fusionMat F th win) u2) := by decide +kernel

example : ¬ (BPair.ofNat (F.dim th) * dotN u1 u1
      + inertia.quadForm (fusionMat F th win) u1
    < BPair.unit) := by decide +kernel

example : ¬ (BPair.ofNat (F.dim th) * dotN u2 u2
      + inertia.quadForm (fusionMat F th win) u2
    < BPair.unit) := by decide +kernel

/-! The interface's hypothesis terms at the window: the symmetry
read at the self-dual `θ`, the eigen row's window read, and the
window's positive dimensions, each the decided fold at the window's
key range. -/

private theorem symWin : symAt F th win := by decide +kernel

private theorem rowWin : rowCap F th win := by decide +kernel

private theorem dimWin : dimPos F win := by decide +kernel

/-! The theorems' own instances beside the decided values. -/

example : ¬ (BPair.ofNat (F.dim th) * dotN u1 u1
    < inertia.quadForm (fusionMat F th win) u1) :=
  capUpper F th win symWin rowWin dimWin u1 rfl

example : ¬ (BPair.ofNat (F.dim th) * dotN u2 u2
    < inertia.quadForm (fusionMat F th win) u2) :=
  capUpper F th win symWin rowWin dimWin u2 rfl

example : ¬ (BPair.ofNat (F.dim th) * dotN u1 u1
      + inertia.quadForm (fusionMat F th win) u1
    < BPair.unit) :=
  capLower F th win symWin rowWin dimWin u1 rfl

example : ¬ (BPair.ofNat (F.dim th) * dotN u2 u2
      + inertia.quadForm (fusionMat F th win) u2
    < BPair.unit) :=
  capLower F th win symWin rowWin dimWin u2 rfl

/-! The eigen row's boundary values at the window: the unit's row
fold tight against `d_θ d_𝟏`, the `θ` row's fold inside
`d_θ d_θ`. -/

example : (win.foldl (fun acc x => acc
      + F.count th (ground.getAt F.unit win 0) x * F.dim x) 0,
    F.dim th * F.dim (ground.getAt F.unit win 0)) = (3, 3) := by
  decide +kernel

example : (win.foldl (fun acc x => acc
      + F.count th (ground.getAt F.unit win 1) x * F.dim x) 0,
    F.dim th * F.dim (ground.getAt F.unit win 1)) = (4, 9) := by
  decide +kernel

/-! The composition read at the fundamental `f = (1, 0)` over the
intermediate list `(f, (3, 0))`: the squared fundamental's entry
identity at every window pair, the decided values beside the
read. -/

example : ((([[1, 0], [3, 0]] : List (List Nat)).foldl
      (fun acc c => acc
        + F.count [1, 0] (ground.getAt F.unit win 1) c
          * F.count [1, 0] (ground.getAt F.unit win 1) c) 0),
    F.count F.theta (ground.getAt F.unit win 1)
        (ground.getAt F.unit win 1)
      + (if F.eqL (ground.getAt F.unit win 1)
          (ground.getAt F.unit win 1) then 1 else 0)) = (2, 2) := by
  decide +kernel

example : compRead F [1, 0] win [[1, 0], [3, 0]] := by decide +kernel

/-! The index-fold expansion's own instance (`quadFold`), the
identity decided at the window's occupied vector. -/

example : (inertia.quadForm (fusionMat F th win) u1).oneValue
      (bsum (fun i => bsum (fun j =>
        BPair.ofNat (F.count th (ground.getAt F.unit win j)
            (ground.getAt F.unit win i))
          * (ground.getAt BPair.unit u1 i
            * ground.getAt BPair.unit u1 j)) (List.range win.length))
        (List.range win.length)) :=
  fpcap.quadFold F th win u1 rfl

example : (bsum (fun i => bsum (fun j =>
        BPair.ofNat (F.count th (ground.getAt F.unit win j)
            (ground.getAt F.unit win i))
          * (ground.getAt BPair.unit u1 i
            * ground.getAt BPair.unit u1 j)) (List.range win.length))
        (List.range win.length)).oneValue (BPair.ofNat 8) := by decide +kernel

/-! The interface's dimension identity meets the window's eigen-row
read at one site: `dimLaw` decided at the window's two letters
beside the row folds' pins above — the derivation
`dimLaw → rowCap` at a distinct window inside the row's support
lands with the instantiation tier.  The adjoint dimension reads
`r (r+2)` with the squared-count join `1 + d_θ = d_f²`, the
display's own base. -/

example : fusion.dimLaw F th (labels.unitL 2) := by decide +kernel
example : fusion.dimLaw F th th := by decide +kernel

example : (fusion.dataA 2).dim (fusion.dataA 2).theta = 3 := by
  decide +kernel
example : (fusion.dataA 3).dim (fusion.dataA 3).theta = 8 := by
  decide +kernel
example : (fusion.dataA 2).dim (fusion.dataA 2).theta + 1 = 2 * 2 := by
  decide +kernel
example : (fusion.dataA 3).dim (fusion.dataA 3).theta + 1 = 3 * 3 := by
  decide +kernel

/-! The window commutation at the source's reach (`multComm`): the
composed orders decided at one value on the unit-supported vector
of the `(𝟏, f, θ)` window and landed by the theorem route, the
frontier-supported vector parting the orders (one against two at
the leaked row), the reach read passing and refusing at exactly
those cells; the two forged interfaces — a coarse equality
identifying an off-window and an off-row label, which every
carried law permits — refused by the structural reach read with
the conclusion parting at each; and the window distinctness
refused at a repeated label. -/

private def F2 : Data (List Nat) := dataA 2
private def win3 : List (List Nat) :=
  [labels.unitL 2, [1, 0], adjchar.theta 2]
private def fnd : List Nat := [1, 0]
private def e0 : List BPair := [BPair.ofNat 1, BPair.unit, BPair.unit]
private def eth : List BPair := [BPair.unit, BPair.unit, BPair.ofNat 1]

-- P1 conclusion true at the unit support
example : poly.oneValue
    (matVec (fusionMat F2 (adjchar.theta 2) win3)
      (matVec (fusionMat F2 fnd win3) e0))
    (matVec (fusionMat F2 fnd win3)
      (matVec (fusionMat F2 (adjchar.theta 2) win3) e0)) := by
  decide +kernel
-- theorem route
example : poly.oneValue
    (matVec (fusionMat F2 (adjchar.theta 2) win3)
      (matVec (fusionMat F2 fnd win3) e0))
    (matVec (fusionMat F2 fnd win3)
      (matVec (fusionMat F2 (adjchar.theta 2) win3) e0)) :=
  multComm F2 (adjchar.theta 2) fnd win3 e0 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
-- P2 the frontier support parts the orders
example : ¬ poly.oneValue
    (matVec (fusionMat F2 (adjchar.theta 2) win3)
      (matVec (fusionMat F2 fnd win3) eth))
    (matVec (fusionMat F2 fnd win3)
      (matVec (fusionMat F2 (adjchar.theta 2) win3) eth)) := by
  decide +kernel
-- P3 the reach read passes and refuses at exactly those cells
example : commReach F2 (adjchar.theta 2) fnd win3 e0 := by decide +kernel
example : ¬ commReach F2 (adjchar.theta 2) fnd win3 eth := by decide +kernel

-- the forged interfaces: the coarse equality identifying an
-- off-window (xF) and an off-row (yF) label; the structural reach
-- read refuses both, and at xF the conclusion parts
private def xeq (x y : Nat) : Bool := (x == y) || (x == 0 && y == 2)
private theorem xeqRefl (l : Nat) : xeq l l = true := by
  show ((l == l) || (l == 0 && l == 2)) = true
  rw [ground.eqBeqOf (rfl : l = l)]
  rfl
private def xcount : Nat → Nat → Nat → Nat
  | 10, 0, 2 => 1 | 11, 2, 0 => 1 | 11, 0, 1 => 1 | 10, 1, 0 => 1
  | 11, 10, 3 => 1 | 10, 11, 3 => 1 | 3, 0, 0 => 1 | _, _, _ => 0
private def xrow : Nat → Nat → List Nat
  | 10, 0 => [2] | 11, 0 => [1] | 11, 10 => [3] | 10, 11 => [3]
  | _, _ => []
private def xF : Data Nat :=
  ⟨xeq, xeqRefl, 9, (fun l => l), (fun x y => x + y), 8,
   xcount, xrow, (fun _ => 1), (fun _ => 1), 1, 1,
   (fun _ => []), (fun _ => 0), (fun x y => x + y), (fun _ => 0),
   (fun _ => none)⟩
private def yeq (x y : Nat) : Bool := (x == y) || (x == 4 && y == 3)
private theorem yeqRefl (l : Nat) : yeq l l = true := by
  show ((l == l) || (l == 4 && l == 3)) = true
  rw [ground.eqBeqOf (rfl : l = l)]
  rfl
private def ycount : Nat → Nat → Nat → Nat
  | 10, 0, 0 => 1 | 11, 0, 1 => 1 | 11, 10, 3 => 1 | 10, 11, 3 => 1
  | 3, 0, 1 => 1 | _, _, _ => 0
private def yrow : Nat → Nat → List Nat
  | 10, 0 => [0] | 11, 0 => [1] | 11, 10 => [3] | 10, 11 => [4]
  | _, _ => []
private def yF : Data Nat :=
  ⟨yeq, yeqRefl, 9, (fun l => l), (fun x y => x + y), 8,
   ycount, yrow, (fun _ => 1), (fun _ => 1), 1, 1,
   (fun _ => []), (fun _ => 0), (fun x y => x + y), (fun _ => 0),
   (fun _ => none)⟩
private def fIx : List Nat := [0, 1]
private def fPsi : List BPair := [BPair.ofNat 1, BPair.unit]

example : ¬ commReach xF 11 10 fIx fPsi := by decide +kernel
example : ¬ poly.oneValue
    (matVec (fusionMat xF 11 fIx) (matVec (fusionMat xF 10 fIx) fPsi))
    (matVec (fusionMat xF 10 fIx) (matVec (fusionMat xF 11 fIx) fPsi)) := by
  decide +kernel
example : ¬ commReach yF 11 10 fIx fPsi := by decide +kernel
example : ¬ poly.oneValue
    (matVec (fusionMat yF 11 fIx) (matVec (fusionMat yF 10 fIx) fPsi))
    (matVec (fusionMat yF 10 fIx) (matVec (fusionMat yF 11 fIx) fPsi)) := by
  decide +kernel

-- distinctness refusal at a repeated window label
example : ¬ distinctAt F2 [labels.unitL 2, labels.unitL 2] := by
  decide +kernel
