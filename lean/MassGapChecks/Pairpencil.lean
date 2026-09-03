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
line, the gram's block structure, a term's support (an entry
between the two loops, off every changed-edge row), the cap at a
term scaled past the dimension, and the order tie.  The window
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
    (pencilH 1 1 [0, 12, 32] (loopMag (dataA 2) [[1, 0], adjchar.theta 2]))
    [[u, u, ⟨1, 2⟩], [u, ⟨12, 1⟩, u], [⟨1, 2⟩, u, ⟨32, 1⟩]] := by
  decide +kernel

example : symmRead
    (pencilH 2 3 [0, 12, 32]
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
example : pencilRead (dataA 2) square 32 3 carrier.sqIx2 (pencilE [0, 12, 32])
    gSq mSq spGSq [(mSq, spUSq, spLSq)] := by decide +kernel

/-! The refusals, each at one conjunct with the rest at the passing
data: the gram's unit line at two, a gram coupling the two loops, a
term with an entry between the two loops (off every changed-edge
row on the square), the term scaled to four against the dimension
three, the order tie at two, and the magnetic member doubled
against its one term's sum. -/

example : ¬ pencilRead (dataA 2) square 32 3 carrier.sqIx2 (pencilE [0, 12, 32])
    gSq (inertia.matScaleB (BPair.ofNat 2) mSq) spGSq
    [(mSq, spUSq, spLSq)] := by decide +kernel

/-! The index tie isolated: the two loops stated in the reversed
order with the pencil's data reordered beside them, every further
conjunct standing, refuse at the window's own enumeration. -/

private def mSqR : Mat := loopMag (dataA 2) [adjchar.theta 2, [1, 0]]
private def spUSqR : inertia.Split 3 :=
  inertia.mkSplit 3 (inertia.siteDatum cSq mSqR)
private def spLSqR : inertia.Split 3 := inertia.mkSplit 3 (matAdd cSq mSqR)

example : ¬ (carrier.idx (dataA 2) square 32 = carrier.sqIx2.reverse)
    ∧ windowfinite.dimSect (dataA 2) square 32 = 3
    ∧ matOneValue (pencilE [0, 32, 12]) (pencilE (slotDiag (dataA 2) square
        carrier.sqIx2.reverse))
    ∧ gramBlockRead (dataA 2) square 3 carrier.sqIx2.reverse gSq
    ∧ termsRead (dataA 2) square 3 carrier.sqIx2.reverse gSq square.plaqs
        [(mSqR, spUSqR, spLSqR)] := by decide +kernel
example : ¬ pencilRead (dataA 2) square 32 3 carrier.sqIx2.reverse
    (pencilE [0, 32, 12]) gSq mSqR spGSq [(mSqR, spUSqR, spLSqR)] := by
  decide +kernel

example : ¬ gramBlockRead (dataA 2) square 3 carrier.sqIx2
    [[⟨3, 1⟩, u, u], [u, ⟨2, 1⟩, u], [u, u, ⟨2, 1⟩]] := by decide +kernel
example : ¬ gramBlockRead (dataA 2) square 3 carrier.sqIx2
    [[⟨2, 1⟩, u, u], [u, ⟨2, 1⟩, ⟨2, 1⟩], [u, ⟨2, 1⟩, ⟨2, 1⟩]] := by
  decide +kernel
example : gramBlockRead (dataA 2) square 3 carrier.sqIx2 gSq := by decide +kernel
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
example : gramBlockRead (dataA 3) thetaG 6 ix6 (inertia.idMat 6) := by
  decide +kernel
example : gramBlockRead (dataA 3) thetaG 6 ix6
    (matAdd (inertia.idMat 6) (e6 1 2)) := by decide +kernel
example : ¬ gramBlockRead (dataA 3) thetaG 6 ix6
    (matAdd (inertia.idMat 6) (e6 1 5)) := by decide +kernel

example : ¬ inertia.capAt (inertia.matScaleB (BPair.ofNat 4) mSq) cSq
    (inertia.mkSplit 3 (inertia.siteDatum cSq
      (inertia.matScaleB (BPair.ofNat 4) mSq)))
    (inertia.mkSplit 3 (matAdd cSq
      (inertia.matScaleB (BPair.ofNat 4) mSq))) := by
  decide +kernel
example : ¬ (windowfinite.dimSect (dataA 2) square 32 = 2) := by
  decide +kernel
