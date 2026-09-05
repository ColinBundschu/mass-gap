import MassGap.Pairpencil
import MassGapChecks.Carrier
/-!
The check module for `thm:pairpencil`: the batteries re-read the
window pencil's symmetric pair matrix by kernel `decide` at the
label calculus's instantiation — the label-index magnetic matrix at
two and three letters (the fusion counts' own entries, the vacuum
defect the Kronecker delta at two labels and the diagonal the base
`c₁`), its symmetry at the self-dual `θ`, the window list's
diagonal with the unit line at its head over the committed square
and theta windows, and the pair's site datum `H([α : β])` symmetric
with pair entries at both weights.  The diagonal pins read the
committed enumerations at the carrier check module's pins, the
theta window's at the tabulated lookup route.  The pencil interface
reads at the square window over two
letters: the loop pencil — the window list's diagonal at the two
loops' contents, the identity gram, and the one plaquette term the
fusion counts capped two-sidedly at the adjoint dimension three —
passes the whole read, with the refusals isolating the gram's unit
line, the gram's block structure and its block content (the
identity refused at the clearing two, a loop block doubled
refused), a term's support (an entry
between the two loops, off every changed-edge row), the cap at a
term scaled past the dimension, and the order tie.  The gram's
block content reads at the theta graph's four-slot fiber over
three letters, the two trivalent vertices' Grams' Kronecker
product at the stated clearing, the identity gram refused there.  The window
list itself reads at the square window, every fiber at one slot
with its diagonal the window diagonal, and at the theta graph over
three letters at a fiber of four slots, the two trivalent vertices
at multiplicity two. -/
set_option maxHeartbeats 16000000

open ground lattice fusion elim pairpencil

private def u : BPair := BPair.unit

/-! The label-index magnetic matrix at two letters over
`(𝟏, f, θ)`: the vacuum defect, the `f` diagonal one, and the base
`c₁ = 1`. -/

example : matOneValue (loopMag (dataA 2) [[1, 0], adjchar.theta 2])
    [[u, u, ⟨2, 1⟩], [u, ⟨2, 1⟩, u], [⟨2, 1⟩, u, ⟨2, 1⟩]] := by
  decide +kernel

/-! At three letters the base reads `c₁ = 2`, the further entries
the counts' own. -/

example : matOneValue (loopMag (dataA 3) [[1, 0, 0], adjchar.theta 3])
    [[u, u, ⟨2, 1⟩], [u, ⟨2, 1⟩, u], [⟨2, 1⟩, u, ⟨3, 1⟩]] := by
  decide +kernel

/-! The symmetry at the self-dual `θ`, both letter counts. -/

example : symmRead (loopMag (dataA 2) [[1, 0], adjchar.theta 2]) := by
  decide +kernel
example : symmRead (loopMag (dataA 3) [[1, 0, 0], adjchar.theta 3]) := by
  decide +kernel

/-! The window list's diagonal with the unit line at its head, the
committed windows' reads: at the square over two letters and at the
theta window over the tabulated interface, every fiber at one
slot. -/

example : slotDiag (dataA 2) square (carrier.idx (dataA 2) square 32)
    = [0, 12, 32] := by
  rw [carrier.sqIx2_pin]; decide +kernel
example : slotDiag (tabulate (dataA 2) 18) thetaG
    (carrier.idx (tabulate (dataA 2) 18) thetaG 18) = [0, 12, 18, 12] := by
  rw [carrier.thIx18_pin]; decide +kernel

/-! The pair's site datum at the square's label index: symmetric
with pair entries at both weights, the displayed matrix at
`[1 : 1]`. -/

example : matOneValue
    (pencilH 1 1 [0, 12, 32] (inertia.idMat 3)
 (loopMag (dataA 2) [[1, 0], adjchar.theta 2]))
    [[u, u, ⟨1, 2⟩], [u, ⟨12, 1⟩, u], [⟨1, 2⟩, u, ⟨32, 1⟩]] := by
  decide +kernel

example : symmRead
    (pencilH 2 3 [0, 12, 32] (inertia.idMat 3)
      (loopMag (dataA 2) [[1, 0], adjchar.theta 2])) := by decide +kernel

/-! The pencil interface at the square window over two letters, the
loop pencil at cutoff thirty-two: the slot diagonal at the
fundamental and adjoint loops' contents, the identity gram at its
own split, and the one plaquette term the fusion counts with its
two cap splits at the adjoint dimension three. -/

private def mSq : Mat := loopMag (dataA 2) [[1, 0], adjchar.theta 2]
private def gSq : Mat := inertia.idMat 3
private def cSq : Mat := inertia.matScaleB (BPair.ofNat 3) gSq
private def spGSq : inertia.Split 3 := inertia.mkSplit 3 gSq
private def spUSq : inertia.Split 3 :=
  inertia.mkSplit 3 (inertia.siteDatum cSq mSq)
private def spLSq : inertia.Split 3 := inertia.mkSplit 3 (matAdd cSq mSq)

example : (dataA 2).dim (adjchar.theta 2) = 3 := by decide +kernel
example : posConf (dataA 2) square (carrier.idx (dataA 2) square 32) 0
      = carrier.unitConf (dataA 2) square
    ∧ posConf (dataA 2) square (carrier.idx (dataA 2) square 32) 1
      = [[1, 0], [1, 0], [1, 0], [1, 0]]
    ∧ posConf (dataA 2) square (carrier.idx (dataA 2) square 32) 2
      = [[2, 0], [2, 0], [2, 0], [2, 0]] := by
  decide +kernel

/-! The window list at the square window: the two loops each at
one slot, the vacant key over the four vertices, the window list's
diagonal the index's contents at the unit fiber products, and the
window list's count with the unit line the window dimension. -/

example : slotList (dataA 2) square carrier.sqIx2
    = [([[1, 0], [1, 0], [1, 0], [1, 0]], [0, 0, 0, 0]),
       ([[2, 0], [2, 0], [2, 0], [2, 0]], [0, 0, 0, 0])] := by decide +kernel
example : slotDiag (dataA 2) square carrier.sqIx2 = 0 :: carrier.sqIx2.map
    (carrier.contentN (dataA 2)) :=
  slotDiag_unit (dataA 2) square carrier.sqIx2 (by decide +kernel)
example : (slotList (dataA 2) square (carrier.idx (dataA 2) square 32)).length + 1
    = windowfinite.dimSect (dataA 2) square 32 :=
  slotList_dimSect (dataA 2) square 32
example : (slotList (dataA 2) square carrier.sqIx2).length + 1 = 3 := by
  decide +kernel

/-! A fiber of four slots: the adjoint on every link of the theta
graph at three letters, the two trivalent vertices at multiplicity
two, the slot keys the digit pairs there, their count the fiber's
multiplicity product through the theorem, and a key with a digit at
the multiplicity refused. -/

private def thAll : List places.Shape := List.replicate 7 (adjchar.theta 3)

example : slotKeys (dataA 3) thetaG thAll
    = [[0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0],
       [1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0]] := by decide +kernel
example : windowfinite.fibProd (dataA 3) thetaG thAll = 4 := by decide +kernel
example : (slotKeys (dataA 3) thetaG thAll).length
    = windowfinite.fibProd (dataA 3) thetaG thAll :=
  length_slotKeys (dataA 3) thetaG thAll
example : ground.countOf [0, 0, 0, 2, 0, 0] (slotKeys (dataA 3) thetaG thAll) = 0
    ∧ ground.countOf [0, 0, 0, 1, 0] (slotKeys (dataA 3) thetaG thAll) = 0 := by
  decide +kernel
example : pencilRead (dataA 2) square 32 3 carrier.sqIx2 1 (pencilE [0, 12, 32])
    gSq mSq spGSq [(mSq, spUSq, spLSq)] := by decide +kernel

/-! The refusals, each at one conjunct with the rest at the passing
data: the gram's unit line at two, a gram coupling the two loops, a
term with an entry between the two loops (off every changed-edge
row on the square), the term scaled to four against the dimension
three, the order tie at two, and the magnetic member doubled
against its one term's sum. -/

example : ¬ pencilRead (dataA 2) square 32 3 carrier.sqIx2 1 (pencilE [0, 12, 32])
    gSq (inertia.matScaleB (BPair.ofNat 2) mSq) spGSq
    [(mSq, spUSq, spLSq)] := by decide +kernel

/-! The magnetic member's order isolated: the member with one row
padded by a trailing unit reads one value with the terms' sum and
is refused at the order, the padded row off the square shape. -/

private def mSqRag : Mat :=
  (List.range 3).map (fun i =>
    if i == 0 then ground.getAt [] mSq 0 ++ [BPair.unit] else ground.getAt [] mSq i)

example : matOneValue mSqRag (termSum 3 [(mSq, spUSq, spLSq)])
    ∧ ¬ sqAt mSqRag 3
    ∧ ¬ pencilRead (dataA 2) square 32 3 carrier.sqIx2 1 (pencilE [0, 12, 32])
        gSq mSqRag spGSq [(mSq, spUSq, spLSq)] := by decide +kernel

/-! The terms' reads' two extractions at the square's one term: the
terms' count the plaquettes' and the term square at the order. -/

example : [(mSq, spUSq, spLSq)].length = square.plaqs.length :=
  termsRead_len (dataA 2) square 3 carrier.sqIx2 gSq _ _ (by decide +kernel)
example : sqAt mSq 3 :=
  termsRead_sq (dataA 2) square 3 carrier.sqIx2 gSq square.plaqs
    [(mSq, spUSq, spLSq)] (by decide +kernel) 0 (by decide)

/-! The index tie isolated: the two loops stated in the reversed
order with the pencil's data reordered beside them, every further
conjunct standing, refuse at the window's own enumeration. -/

private def mSqR : Mat := loopMag (dataA 2) [adjchar.theta 2, [1, 0]]
private def spUSqR : inertia.Split 3 :=
  inertia.mkSplit 3 (inertia.siteDatum cSq mSqR)
private def spLSqR : inertia.Split 3 := inertia.mkSplit 3 (matAdd cSq mSqR)

example : ¬ (carrier.idx (dataA 2) square 32 = carrier.sqIx2.reverse)
    ∧ windowfinite.dimSect (dataA 2) square 32 = 3
    ∧ matOneValue (pencilE [0, 32, 12]) (formE (slotDiag (dataA 2) square
        carrier.sqIx2.reverse) gSq)
    ∧ gramBlockRead (dataA 2) square 3 carrier.sqIx2.reverse 1 gSq
    ∧ termsRead (dataA 2) square 3 carrier.sqIx2.reverse gSq square.plaqs
        [(mSqR, spUSqR, spLSqR)] := by decide +kernel
example : ¬ pencilRead (dataA 2) square 32 3 carrier.sqIx2.reverse 1
    (pencilE [0, 32, 12]) gSq mSqR spGSq [(mSqR, spUSqR, spLSqR)] := by
  decide +kernel

example : ¬ gramBlockRead (dataA 2) square 3 carrier.sqIx2 1
    [[⟨3, 1⟩, u, u], [u, ⟨2, 1⟩, u], [u, u, ⟨2, 1⟩]] := by decide +kernel
example : ¬ gramBlockRead (dataA 2) square 3 carrier.sqIx2 1
    [[⟨2, 1⟩, u, u], [u, ⟨2, 1⟩, ⟨2, 1⟩], [u, ⟨2, 1⟩, ⟨2, 1⟩]] := by
  decide +kernel
example : gramBlockRead (dataA 2) square 3 carrier.sqIx2 1 gSq := by decide +kernel

/-! The block content isolated at the square: the identity gram
refused at the clearing two, and a loop block doubled at the
clearing one refused — each loop's block the four coevaluations
against the four link scales, one exactly. -/

example : ¬ gramBlockRead (dataA 2) square 3 carrier.sqIx2 2 gSq
    ∧ ¬ gramBlockRead (dataA 2) square 3 carrier.sqIx2 1
        [[⟨2, 1⟩, u, u], [u, ⟨3, 1⟩, u], [u, u, ⟨2, 1⟩]]
    ∧ fibGram (dataA 2) square [[2, 0], [2, 0], [2, 0], [2, 0]]
      = some [([[BPair.ofNat 3]], 1), ([[BPair.ofNat 3]], 1),
          ([[BPair.ofNat 3]], 1), ([[BPair.ofNat 3]], 1)]
    ∧ blockScale (dataA 2) square [[2, 0], [2, 0], [2, 0], [2, 0]] = 81 := by
  decide +kernel
example : ¬ termSupport (dataA 2) square 3 carrier.sqIx2 sqPlaq
    [[u, u, ⟨2, 1⟩], [u, ⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩]] := by
  decide +kernel
example : termSupport (dataA 2) square 3 carrier.sqIx2 sqPlaq mSq := by
  decide +kernel

/-! The gram and the support at a fiber of four slots: the theta
graph's all-adjoint member beside the first plaquette's fundamental
loop over three letters, six positions with the unit line.  The
gram's block read admits a pairing within the four-slot fiber and
refuses one across the two members. -/

private def fLoop : List places.Shape :=
  [[1, 0, 0], [1, 0, 0], [1, 0, 0], [1, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]
private def ix6 : List (List places.Shape) := [thAll, fLoop]
private def e6 (i j : Nat) : Mat :=
  ground.matOf 6 6 (fun a b =>
    if (a == i && b == j) || (a == j && b == i) then ⟨2, 1⟩ else u)

example : (slotList (dataA 3) thetaG ix6).length = 5 := by decide +kernel

/-! The gram's block content at the four-slot fiber: the two
trivalent vertices' Grams `[[56, -16], [-16, 56]]` at the second
member three (`con:fiber`'s symbolic tag at three adjoints over
three letters, the check module for `con:fiber` its pin), the four
two-end vertices at the coevaluation's eight, and the seven links'
scale `[1 : 8]` each, so at the clearing `9 · 8` the block is the
Kronecker product of the vertex Grams at their own eighth,
`[[7, -2], [-2, 7]]`, the loop member's block the clearing itself; the identity gram is refused there, as
is the block at the clearing one, the block with the two members
coupled, and the block with one entry moved. -/

private def vg3 : Mat :=
  [[BPair.ofNat 56, (BPair.ofNat 16).swap], [(BPair.ofNat 16).swap, BPair.ofNat 56]]
private def kron2 (A B : Mat) : Mat :=
  ground.matOf 4 4 (fun i j =>
    ground.getAt u (ground.getAt [] A (i / 2)) (j / 2)
      * ground.getAt u (ground.getAt [] B (i % 2)) (j % 2))
private def vg7 : Mat :=
  [[BPair.ofNat 7, (BPair.ofNat 2).swap], [(BPair.ofNat 2).swap, BPair.ofNat 7]]
private def cTh : Pos := 72
private def gTh : Mat :=
  ground.matOf 6 6 (fun i j =>
    if i == 0 && j == 0 then BPair.ofPos cTh
    else if i == 5 && j == 5 then BPair.ofPos cTh
    else if 1 ≤ i && i ≤ 4 && 1 ≤ j && j ≤ 4 then
      ground.getAt u (ground.getAt [] (kron2 vg7 vg7) (i - 1)) (j - 1)
    else u)

example : fibGram (dataA 3) thetaG thAll
    = some [(vg3, 3), ([[BPair.ofNat 8]], 1), ([[BPair.ofNat 8]], 1), (vg3, 3),
        ([[BPair.ofNat 8]], 1), ([[BPair.ofNat 8]], 1)]
    ∧ blockScale (dataA 3) thetaG thAll = 2097152 := by decide +kernel
example : gramBlockRead (dataA 3) thetaG 6 ix6 cTh gTh := by decide +kernel
example : ¬ gramBlockRead (dataA 3) thetaG 6 ix6 cTh (inertia.idMat 6)
    ∧ ¬ gramBlockRead (dataA 3) thetaG 6 ix6 1 gTh
    ∧ ¬ gramBlockRead (dataA 3) thetaG 6 ix6 cTh (matAdd gTh (e6 1 5))
    ∧ ¬ gramBlockRead (dataA 3) thetaG 6 ix6 cTh (matAdd gTh (e6 1 2)) := by
  decide +kernel
example : inertia.pdAt (inertia.mkSplit 6 gTh) := by decide +kernel

example : ¬ inertia.capAt (inertia.matScaleB (BPair.ofNat 4) mSq) cSq
    (inertia.mkSplit 3 (inertia.siteDatum cSq
      (inertia.matScaleB (BPair.ofNat 4) mSq)))
    (inertia.mkSplit 3 (matAdd cSq
      (inertia.matScaleB (BPair.ofNat 4) mSq))) := by
  decide +kernel
example : ¬ (windowfinite.dimSect (dataA 2) square 32 = 2) := by
  decide +kernel
