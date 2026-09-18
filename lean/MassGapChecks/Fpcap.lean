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
consumer.  The fusion walk's flat read (`lem:cornerkey`'s near mass)
is decided at the window `(𝟏, θ)` to one step and at the window
`(𝟏, θ, (4, 0))` to two, reading `6` and `36`, the seed's flat
read one and the eigen row's window identity on the walk's support
decided beside the theorem route, and its two binders isolated:
the seed read refused at a repeated unit key and at a window off
the unit, and the support identity refused one step past each
window's reach with the flat read parting there (`31` against
`36`, `209` against `216`); the walk's pairing side decided at the
two-step window.

The eigen row's boundary values are pinned rather than a forged
table: at the window the row folds read `3 ≤ 3 · 1` at the unit —
tight, the cap's own boundary — and `4 ≤ 3 · 3` at `θ`, so
`rowCap`'s slack is exercised on both sides.  The zero-dimension
clause needs no pin: at the label calculus every window dimension
is a Weyl dimension, positive by construction, so `hdim` is
structural at `dataA` and the corner the theorem's docstring names
is unreachable at this interface.

The dual pair's fold and the closure fold are decided at three
letters: the fundamental `f` off symmetry alone, its dual pair's
fold symmetric at the involution read and capped at `2 d_f = 6`
(the dual dimension read decided beside), the closure
`{θ} ∪ {f, f̄}` at the self-dual member and the representative with
its list, its dimension fold `14` read as the dimensions' fold over
the list, its form the two members' forms summed, and both folds'
caps at the window `(𝟏, f, f̄, θ)`, each decided by kernel beside the
theorem route; the squared fundamental reads `13 = 5 + 8` at the
occupied vector, the adjoint's form joined to the gram, under
`1 + d_θ = 4` times the gram.  Four forged interfaces isolate the
caps' binders, each with every other binder holding and the cap
parting: the dual dimension read refused, the involution read
refused, the eigen row's read refused at the dual pair's fold, and
the symmetry read refused at the self-dual cap; the squared
fundamental's distinctness read is refused at a repeated adjoint
letter, where the composition read holds and the form parts from
the adjoint's form joined to the gram (`18` against `14`), and the
dual dimension read over a list is refused at the forged dual with
the dimension fold parting from the list's fold (`2` against `10`).
-/

namespace fpcap
set_option maxHeartbeats 16000000

open ground fusion elim

private def F : Data (List Nat) := dataA 2

private def th : List Nat := adjchar.theta 2

private def win : List (List Nat) := [labels.unitL 2, adjchar.theta 2]

private def u1 : List BPair := [BPair.ofNat 1, BPair.ofNat 2]

private def u2 : List BPair := [BPair.ofNat 1, (BPair.ofNat 1).swap]

/-! The form's matrix at `θ` over the window: the walk's own
`[[0, 1], [1, 1]]`, the vacuum defect at the unit's diagonal. -/

theorem pin1 : fusionMat F th win
    = [[BPair.ofNat 0, BPair.ofNat 1],
       [BPair.ofNat 1, BPair.ofNat 1]] := by decide +kernel

/-! The form at two committed vectors, the occupied pair and the
swap-signed one. -/

theorem pin2 : (inertia.quadForm (fusionMat F th win) u1).oneValue
    (BPair.ofNat 8) := by decide +kernel

theorem pin3 : (inertia.quadForm (fusionMat F th win) u2).oneValue
    (BPair.ofNat 1).swap := by decide +kernel

/-! Both cap sides decided at the two vectors: the dimension
against the gram above, the summed form at or above the sum's unit
below. -/

theorem pin4 : ¬ (BPair.ofNat (F.dim th) * dotN u1 u1
    < inertia.quadForm (fusionMat F th win) u1) := by decide +kernel

theorem pin5 : ¬ (BPair.ofNat (F.dim th) * dotN u2 u2
    < inertia.quadForm (fusionMat F th win) u2) := by decide +kernel

theorem pin6 : ¬ (BPair.ofNat (F.dim th) * dotN u1 u1
      + inertia.quadForm (fusionMat F th win) u1
    < BPair.unit) := by decide +kernel

theorem pin7 : ¬ (BPair.ofNat (F.dim th) * dotN u2 u2
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

theorem pin8 : ¬ (BPair.ofNat (F.dim th) * dotN u1 u1
    < inertia.quadForm (fusionMat F th win) u1) :=
  capUpper F th win symWin rowWin dimWin u1 rfl

theorem pin9 : ¬ (BPair.ofNat (F.dim th) * dotN u2 u2
    < inertia.quadForm (fusionMat F th win) u2) :=
  capUpper F th win symWin rowWin dimWin u2 rfl

theorem pin10 : ¬ (BPair.ofNat (F.dim th) * dotN u1 u1
      + inertia.quadForm (fusionMat F th win) u1
    < BPair.unit) :=
  capLower F th win symWin rowWin dimWin u1 rfl

theorem pin11 : ¬ (BPair.ofNat (F.dim th) * dotN u2 u2
      + inertia.quadForm (fusionMat F th win) u2
    < BPair.unit) :=
  capLower F th win symWin rowWin dimWin u2 rfl

/-! The eigen row's boundary values at the window: the unit's row
fold tight against `d_θ d_𝟏`, the `θ` row's fold inside
`d_θ d_θ`. -/

theorem pin12 : (win.foldl (fun acc x => acc
      + F.count th (ground.getAt F.unit win 0) x * F.dim x) 0,
    F.dim th * F.dim (ground.getAt F.unit win 0)) = (3, 3) := by
  decide +kernel

theorem pin13 : (win.foldl (fun acc x => acc
      + F.count th (ground.getAt F.unit win 1) x * F.dim x) 0,
    F.dim th * F.dim (ground.getAt F.unit win 1)) = (4, 9) := by
  decide +kernel

/-! The composition read at the fundamental `f = (1, 0)` over the
intermediate list `(f, (3, 0))`: the squared fundamental's entry
identity at every window pair, the decided values beside the
read. -/

theorem pin14 : ((([[1, 0], [3, 0]] : List (List Nat)).foldl
      (fun acc c => acc
        + F.count [1, 0] (ground.getAt F.unit win 1) c
          * F.count [1, 0] (ground.getAt F.unit win 1) c) 0),
    F.count F.theta (ground.getAt F.unit win 1)
        (ground.getAt F.unit win 1)
      + (if F.eqL (ground.getAt F.unit win 1)
          (ground.getAt F.unit win 1) then 1 else 0)) = (2, 2) := by
  decide +kernel

theorem pin15 : compRead F [1, 0] win [[1, 0], [3, 0]] := by decide +kernel

/-! The index-fold expansion's own instance (`quadFold`), the
identity decided at the window's occupied vector. -/

theorem pin16 : (inertia.quadForm (fusionMat F th win) u1).oneValue
      (bsum (fun i => bsum (fun j =>
        BPair.ofNat (F.count th (ground.getAt F.unit win j)
            (ground.getAt F.unit win i))
          * (ground.getAt BPair.unit u1 i
            * ground.getAt BPair.unit u1 j)) (List.range win.length))
        (List.range win.length)) :=
  fpcap.quadFold F th win u1 rfl

theorem pin17 : (bsum (fun i => bsum (fun j =>
        BPair.ofNat (F.count th (ground.getAt F.unit win j)
            (ground.getAt F.unit win i))
          * (ground.getAt BPair.unit u1 i
            * ground.getAt BPair.unit u1 j)) (List.range win.length))
        (List.range win.length)).oneValue (BPair.ofNat 8) := by decide +kernel

/-! The interface's dimension identity meets the window's eigen-row
read at one site: `dimLaw` decided at the window's two letters
beside the row folds' pins above.  The adjoint dimension reads
`r (r+2)` with the squared-count join `1 + d_θ = d_f²`, the
display's own base. -/

theorem pin18 : fusion.dimLaw F th (labels.unitL 2) := by decide +kernel
theorem pin19 : fusion.dimLaw F th th := by decide +kernel

theorem pin20 : (fusion.dataA 2).dim (fusion.dataA 2).theta = 3 := by
  decide +kernel
theorem pin21 : (fusion.dataA 3).dim (fusion.dataA 3).theta = 8 := by
  decide +kernel
theorem pin22 : (fusion.dataA 2).dim (fusion.dataA 2).theta + 1 = 2 * 2 := by
  decide +kernel
theorem pin23 : (fusion.dataA 3).dim (fusion.dataA 3).theta + 1 = 3 * 3 := by
  decide +kernel

/-! The window commutation at the source's reach (`multComm`): the
composed orders decided at one value on the unit-supported vector
of the `(𝟏, f, θ)` window and landed by the theorem route, the
vector supported at the window's last fusion step parting the
orders (one against two at the leaked row), the reach read passing
and refusing at exactly
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
theorem pin24 : poly.oneValue
    (matVec (fusionMat F2 (adjchar.theta 2) win3)
      (matVec (fusionMat F2 fnd win3) e0))
    (matVec (fusionMat F2 fnd win3)
      (matVec (fusionMat F2 (adjchar.theta 2) win3) e0)) := by
  decide +kernel
-- theorem route
theorem pin25 : poly.oneValue
    (matVec (fusionMat F2 (adjchar.theta 2) win3)
      (matVec (fusionMat F2 fnd win3) e0))
    (matVec (fusionMat F2 fnd win3)
      (matVec (fusionMat F2 (adjchar.theta 2) win3) e0)) :=
  multComm F2 (adjchar.theta 2) fnd win3 e0 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
-- P2 the last-step support parts the orders
theorem pin26 : ¬ poly.oneValue
    (matVec (fusionMat F2 (adjchar.theta 2) win3)
      (matVec (fusionMat F2 fnd win3) eth))
    (matVec (fusionMat F2 fnd win3)
      (matVec (fusionMat F2 (adjchar.theta 2) win3) eth)) := by
  decide +kernel
-- P3 the reach read passes and refuses at exactly those cells
theorem pin27 : commReach F2 (adjchar.theta 2) fnd win3 e0 := by decide +kernel
theorem pin28 : ¬ commReach F2 (adjchar.theta 2) fnd win3 eth := by decide +kernel

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
   xcount, xrow, (fun _ => 1), (fun _ => 1), 1, 1, 1,
   (fun _ => []), (fun _ => 0), (fun x y => x + y), (fun _ => 0),
   (fiber.presNone _)⟩
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
   ycount, yrow, (fun _ => 1), (fun _ => 1), 1, 1, 1,
   (fun _ => []), (fun _ => 0), (fun x y => x + y), (fun _ => 0),
   (fiber.presNone _)⟩
private def fIx : List Nat := [0, 1]
private def fPsi : List BPair := [BPair.ofNat 1, BPair.unit]

theorem pin29 : ¬ commReach xF 11 10 fIx fPsi := by decide +kernel
theorem pin30 : ¬ poly.oneValue
    (matVec (fusionMat xF 11 fIx) (matVec (fusionMat xF 10 fIx) fPsi))
    (matVec (fusionMat xF 10 fIx) (matVec (fusionMat xF 11 fIx) fPsi)) := by
  decide +kernel
theorem pin31 : ¬ commReach yF 11 10 fIx fPsi := by decide +kernel
theorem pin32 : ¬ poly.oneValue
    (matVec (fusionMat yF 11 fIx) (matVec (fusionMat yF 10 fIx) fPsi))
    (matVec (fusionMat yF 10 fIx) (matVec (fusionMat yF 11 fIx) fPsi)) := by
  decide +kernel

-- distinctness refusal at a repeated window label
theorem pin33 : ¬ distinctAt F2 [labels.unitL 2, labels.unitL 2] := by
  decide +kernel

-- the fusion walk's flat read (`lem:cornerkey`'s near mass)
private def winW : List (List Nat) := [labels.unitL 2, adjchar.theta 2, [4, 0]]

theorem pin34 : seedFlat F win := by decide +kernel
theorem pin35 : seedFlat F winW := by decide +kernel
theorem pin36 : ¬ seedFlat F [labels.unitL 2, labels.unitL 2] := by decide +kernel
theorem pin37 : ¬ seedFlat F [adjchar.theta 2] := by decide +kernel
theorem pin38 : walkExact F win 1 := by decide +kernel
theorem pin39 : ¬ walkExact F win 2 := by decide +kernel
theorem pin40 : walkExact F winW 2 := by decide +kernel
theorem pin41 : ¬ walkExact F winW 3 := by decide +kernel
theorem pin42 : (dotN (walkVec F win 1) (dimVec F win)).oneValue
    (bpow (BPair.ofNat (2 * F.dim th)) 1) := by decide +kernel
theorem pin43 : (dotN (walkVec F win 1) (dimVec F win)).oneValue
    (bpow (BPair.ofNat (2 * F.dim th)) 1) :=
  walk_dim F win 1 (by decide +kernel) (by decide +kernel)
theorem pin44 : (dotN (walkVec F winW 2) (dimVec F winW)).oneValue (BPair.ofNat 36) := by
  decide +kernel
theorem pin45 : (dotN (walkVec F winW 2) (dimVec F winW)).oneValue
    (bpow (BPair.ofNat (2 * F.dim th)) 2) :=
  walk_dim F winW 2 (by decide +kernel) (by decide +kernel)
-- the support identity's refusal parts the flat read
theorem pin46 : ¬ (dotN (walkVec F win 2) (dimVec F win)).oneValue
    (bpow (BPair.ofNat (2 * F.dim th)) 2) := by decide +kernel
theorem pin47 : (dotN (walkVec F win 2) (dimVec F win)).oneValue (BPair.ofNat 31) := by
  decide +kernel
theorem pin48 : ¬ (dotN (walkVec F winW 3) (dimVec F winW)).oneValue
    (bpow (BPair.ofNat (2 * F.dim th)) 3) := by decide +kernel
theorem pin49 : (dotN (walkVec F winW 3) (dimVec F winW)).oneValue (BPair.ofNat 209) := by
  decide +kernel
-- the pairing side
theorem pin50 : (dotN (walkVec F winW 2) (dimVec F winW)).oneValue
      (dotN (walkVec F winW 2) (suppDims F winW (walkVec F winW 2)))
    ∧ dotN (walkVec F winW 2) (dimVec F winW) * dotN (walkVec F winW 2) (dimVec F winW)
      ≤ dotN (walkVec F winW 2) (walkVec F winW 2)
        * dotN (suppDims F winW (walkVec F winW 2)) (suppDims F winW (walkVec F winW 2)) := by
  decide +kernel
theorem pin51 : (dotN (walkVec F winW 2) (dimVec F winW)).oneValue
      (dotN (walkVec F winW 2) (suppDims F winW (walkVec F winW 2)))
    ∧ dotN (walkVec F winW 2) (dimVec F winW) * dotN (walkVec F winW 2) (dimVec F winW)
      ≤ dotN (walkVec F winW 2) (walkVec F winW 2)
        * dotN (suppDims F winW (walkVec F winW 2)) (suppDims F winW (walkVec F winW 2)) :=
  walk_cs F winW 2

/-! The dual pair's fold and the closure fold at three letters,
`dataA 3`: the fundamental `f` off symmetry alone, its dual pair's
fold symmetric at the involution read and capped at `2 d_f = 6`; the
closure `{θ} ∪ {f, f̄}` at the self-dual member `θ` and the
representative `f`, its list `(θ, f, f̄)`, its dimension fold
`8 + 2·3 = 14` read as the dimensions' fold over the list, and its
caps at the window `(𝟏, f, f̄, θ)`, the closure's form the two
members' forms summed; each cap decided by kernel beside the theorem
route.  Two forged interfaces isolate the dual fold's binders: at
`zF` the dual dimension read fails (the dual at nine against one)
with every other binder holding and the cap parting; at `wF` the
involution read fails (a one-sided count) with every other binder
holding and the cap parting. -/

private def F3 : Data (List Nat) := dataA 3
private def f3 : List Nat := [1, 0, 0]
private def th3 : List Nat := adjchar.theta 3
private def win4 : List (List Nat) :=
  [labels.unitL 3, f3, labels.dualL f3, th3]
private def v4 : List BPair :=
  [BPair.ofNat 1, BPair.ofNat 2, BPair.ofNat 1, (BPair.ofNat 1).swap]

theorem pin52 : involAt F3 f3 win4 := by decide +kernel
theorem pin53 : ¬ symAt F3 f3 win4 := by decide +kernel
theorem pin54 : symAtC F3 (dualCount F3 f3) win4 := dualSym F3 f3 win4 pin52
theorem pin55 : fusion.dimDualLaw F3 f3 := by decide +kernel
private theorem rowF3 : rowCap F3 f3 win4 := by decide +kernel
private theorem rowFd3 : rowCap F3 (F3.dual f3) win4 := by decide +kernel
private theorem dim4 : dimPos F3 win4 := by decide +kernel
theorem pin56 : rowCapC F3 (dualCount F3 f3) (2 * F3.dim f3) win4 :=
  dualRow F3 f3 win4 rowF3 rowFd3 pin55
theorem pin57 : ¬ (BPair.ofNat (2 * F3.dim f3) * dotN v4 v4
    < inertia.quadForm (dualMat F3 f3 win4) v4) :=
  dualCapUpper F3 f3 win4 pin52 rowF3 rowFd3 pin55 dim4 v4 rfl
theorem pin58 : ¬ (BPair.ofNat (2 * F3.dim f3) * dotN v4 v4
      + inertia.quadForm (dualMat F3 f3 win4) v4
    < BPair.unit) :=
  dualCapLower F3 f3 win4 pin52 rowF3 rowFd3 pin55 dim4 v4 rfl
theorem pin59 : ¬ (BPair.ofNat (2 * F3.dim f3) * dotN v4 v4
    < inertia.quadForm (dualMat F3 f3 win4) v4) := by decide +kernel
theorem pin60 : (2 * F3.dim f3, F3.dim F3.theta) = (6, 8) := by decide +kernel

-- the closure at the self-dual `θ` and the representative `f`
theorem pin61 : closureList F3 [th3] [f3] = [th3, f3, labels.dualL f3] := by
  decide +kernel
theorem pin62 : dimFold F3 [th3] [f3] = 14 := by decide +kernel
theorem pin63 : dimDualAll F3 [f3] := by decide +kernel
theorem pin64 : dimFold F3 [th3] [f3]
    = ground.famFold Nat.add 0 F3.dim (closureList F3 [th3] [f3]) :=
  dimFold_list F3 [th3] [f3] pin63
theorem pin65 : closureCount F3 [th3] [f3] f3 th3
    = ground.famFold Nat.add 0 (fun l => F3.count l f3 th3)
      (closureList F3 [th3] [f3]) :=
  closureCount_list F3 [th3] [f3] f3 th3
private theorem symAll3 : symAll F3 [th3] win4 := by decide +kernel
private theorem involAll3 : involAll F3 [f3] win4 := by decide +kernel
private theorem rowAll3 : rowAll F3 [th3] win4 := by decide +kernel
private theorem dualRowAll3 : dualRowAll F3 [f3] win4 := by decide +kernel
theorem pin66 : symAtC F3 (closureCount F3 [th3] [f3]) win4 :=
  closureSym F3 [th3] [f3] win4 symAll3 involAll3
theorem pin67 : (inertia.quadForm (closureMat F3 [th3] [f3] win4) v4).oneValue
    (bsum (fun l => inertia.quadForm (fusionMat F3 l win4) v4) [th3]
      + bsum (fun l => inertia.quadForm (dualMat F3 l win4) v4) [f3]) :=
  closureForm F3 [th3] [f3] win4 v4 rfl
theorem pin68 : ¬ (BPair.ofNat (dimFold F3 [th3] [f3]) * dotN v4 v4
    < inertia.quadForm (closureMat F3 [th3] [f3] win4) v4) :=
  closureCapUpper F3 [th3] [f3] win4 symAll3 involAll3 rowAll3 dualRowAll3 dim4 v4 rfl
theorem pin69 : ¬ (BPair.ofNat (dimFold F3 [th3] [f3]) * dotN v4 v4
      + inertia.quadForm (closureMat F3 [th3] [f3] win4) v4
    < BPair.unit) :=
  closureCapLower F3 [th3] [f3] win4 symAll3 involAll3 rowAll3 dualRowAll3 dim4 v4 rfl
theorem pin70 : ¬ (BPair.ofNat (dimFold F3 [th3] [f3]) * dotN v4 v4
    < inertia.quadForm (closureMat F3 [th3] [f3] win4) v4) := by decide +kernel

-- the squared fundamental at two letters: `M†M = M_{1 + χ_θ}` at the
-- composition read, `13 = 5 + 8` at the occupied vector, under
-- `1 + d_θ = 4` times the gram
private theorem distWin2 : distinctAt F win := by decide +kernel
theorem pin71 : (inertia.quadForm (sqMat F [1, 0] [[1, 0], [3, 0]] win) u1).oneValue
    (dotN u1 u1 + inertia.quadForm (fusionMat F th win) u1) :=
  sqForm F [1, 0] win [[1, 0], [3, 0]] u1 rfl pin15 distWin2
theorem pin72 : (inertia.quadForm (sqMat F [1, 0] [[1, 0], [3, 0]] win) u1).oneValue
    (BPair.ofNat 13) := by decide +kernel
theorem pin73 : ¬ (BPair.ofNat (F.dim th + 1) * dotN u1 u1
    < inertia.quadForm (sqMat F [1, 0] [[1, 0], [3, 0]] win) u1) :=
  sqCap F [1, 0] win [[1, 0], [3, 0]] pin15 distWin2 symWin rowWin dimWin u1 rfl
theorem pin74 : ¬ (BPair.ofNat (F.dim th + 1) * dotN u1 u1
    < inertia.quadForm (sqMat F [1, 0] [[1, 0], [3, 0]] win) u1) := by decide +kernel

-- the forged interfaces: `zF` refuses the dual dimension read, `wF`
-- the involution read; at each the dual fold's cap parts
private def zdual (l : Nat) : Nat := if l = 5 then 6 else if l = 6 then 5 else l
private def zcount : Nat → Nat → Nat → Nat
  | 5, 0, 1 => 3 | 6, 1, 0 => 3 | _, _, _ => 0
private def zdim : Nat → Nat
  | 0 => 1 | 1 => 3 | 5 => 9 | _ => 1
private def zF : Data Nat :=
  ⟨(fun x y => x == y), (fun l => ground.eqBeqOf (rfl : l = l)), 9, zdual,
   (fun x y => x + y), 8, zcount, (fun _ _ => []), zdim, (fun _ => 1), 1, 1, 1,
   (fun _ => []), (fun _ => 0), (fun x y => x + y), (fun _ => 0),
   (fiber.presNone _)⟩
private def zw : List Nat := [0, 1]
private def zu : List BPair := [BPair.ofNat 1, BPair.ofNat 1]
theorem pin75 : involAt zF 6 zw := by decide +kernel
theorem pin76 : rowCap zF 6 zw ∧ rowCap zF (zF.dual 6) zw ∧ dimPos zF zw := by
  decide +kernel
theorem pin77 : ¬ fusion.dimDualLaw zF 6 := by decide +kernel
theorem pin78 : BPair.ofNat (2 * zF.dim 6) * dotN zu zu
    < inertia.quadForm (dualMat zF 6 zw) zu := by decide +kernel

private def wcount : Nat → Nat → Nat → Nat
  | 5, 0, 1 => 20 | _, _, _ => 0
private def wdim : Nat → Nat
  | 0 => 20 | _ => 1
private def wF : Data Nat :=
  ⟨(fun x y => x == y), (fun l => ground.eqBeqOf (rfl : l = l)), 9, (fun l => l),
   (fun x y => x + y), 8, wcount, (fun _ _ => []), wdim, (fun _ => 1), 1, 1, 1,
   (fun _ => []), (fun _ => 0), (fun x y => x + y), (fun _ => 0),
   (fiber.presNone _)⟩
theorem pin79 : ¬ involAt wF 5 zw := by decide +kernel
theorem pin80 : rowCap wF 5 zw ∧ rowCap wF (wF.dual 5) zw
    ∧ fusion.dimDualLaw wF 5 ∧ dimPos wF zw := by decide +kernel
theorem pin81 : BPair.ofNat (2 * wF.dim 5) * dotN zu zu
    < inertia.quadForm (dualMat wF 5 zw) zu := by decide +kernel

-- the squared fundamental's distinctness read refused at a repeated
-- adjoint letter: the composition read holds there and the form
-- parts from the adjoint's form joined to the gram, `18` against `14`
private def ls2 : List (List Nat) := [adjchar.theta 2, adjchar.theta 2]
theorem pin82 : compRead F [1, 0] ls2 [[1, 0], [3, 0]] := by decide +kernel
theorem pin83 : ¬ distinctAt F ls2 := by decide +kernel
theorem pin84 : ¬ (inertia.quadForm (sqMat F [1, 0] [[1, 0], [3, 0]] ls2) u1).oneValue
    (dotN u1 u1 + inertia.quadForm (fusionMat F th ls2) u1) := by decide +kernel
theorem pin85 : (inertia.quadForm (sqMat F [1, 0] [[1, 0], [3, 0]] ls2) u1).oneValue
      (BPair.ofNat 18)
    ∧ (dotN u1 u1 + inertia.quadForm (fusionMat F th ls2) u1).oneValue
      (BPair.ofNat 14) := by decide +kernel

-- the dual dimension read over a list refused at the forged dual,
-- the dimension fold parting from the closure list's fold
theorem pin86 : ¬ dimDualAll zF [6] := by decide +kernel
theorem pin87 : (dimFold zF [] [6],
    ground.famFold Nat.add 0 zF.dim (closureList zF [] [6])) = (2, 10) := by
  decide +kernel

-- the forged interface `rF` refuses the eigen row's read at the dual
-- pair's fold: a symmetric count at the identity involution, the
-- row fold at nine against one; every other binder holds and the
-- cap parts
private def rcount : Nat → Nat → Nat → Nat
  | 5, 0, 1 => 3 | 5, 1, 0 => 3 | _, _, _ => 0
private def rdim : Nat → Nat
  | 0 => 1 | 1 => 3 | _ => 1
private def rF : Data Nat :=
  ⟨(fun x y => x == y), (fun l => ground.eqBeqOf (rfl : l = l)), 9, (fun l => l),
   (fun x y => x + y), 8, rcount, (fun _ _ => []), rdim, (fun _ => 1), 1, 1, 1,
   (fun _ => []), (fun _ => 0), (fun x y => x + y), (fun _ => 0),
   (fiber.presNone _)⟩
theorem pin88 : involAt rF 5 zw ∧ fusion.dimDualLaw rF 5 ∧ dimPos rF zw := by
  decide +kernel
theorem pin89 : ¬ rowCap rF 5 zw := by decide +kernel
theorem pin90 : BPair.ofNat (2 * rF.dim 5) * dotN zu zu
    < inertia.quadForm (dualMat rF 5 zw) zu := by decide +kernel

-- the forged interface `sF` refuses the symmetry read at the
-- self-dual cap: a one-sided count at six, the eigen row's read tight
-- at the dimension two and the window occupied; both cap sides part,
-- the upper at the occupied pair and the lower at the swap-signed one
private def scount : Nat → Nat → Nat → Nat
  | 7, 0, 1 => 6 | _, _, _ => 0
private def sdim : Nat → Nat
  | 0 => 3 | 1 => 1 | 7 => 2 | _ => 1
private def sF : Data Nat :=
  ⟨(fun x y => x == y), (fun l => ground.eqBeqOf (rfl : l = l)), 9, (fun l => l),
   (fun x y => x + y), 8, scount, (fun _ _ => []), sdim, (fun _ => 1), 1, 1, 1,
   (fun _ => []), (fun _ => 0), (fun x y => x + y), (fun _ => 0),
   (fiber.presNone _)⟩
private def su2 : List BPair := [BPair.ofNat 1, (BPair.ofNat 1).swap]
theorem pin91 : ¬ symAt sF 7 zw := by decide +kernel
theorem pin92 : rowCap sF 7 zw ∧ dimPos sF zw := by decide +kernel
theorem pin93 : BPair.ofNat (sF.dim 7) * dotN zu zu
    < inertia.quadForm (fusionMat sF 7 zw) zu := by decide +kernel
theorem pin94 : BPair.ofNat (sF.dim 7) * dotN su2 su2
      + inertia.quadForm (fusionMat sF 7 zw) su2
    < BPair.unit := by decide +kernel

end fpcap
