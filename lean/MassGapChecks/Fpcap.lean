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
set_option maxRecDepth 1000000
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
