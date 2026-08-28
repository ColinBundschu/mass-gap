import MassGap.Pencil
import MassGap.Inertia
import MassGap.Fpcap
/-!
`thm:pairpencil` — the window pencil as a symmetric pair matrix:
`E` is diagonal in the label index with the unit line at its head
(`windowDiag` over `def:pencil`'s electric diagonal), `M` is the
multiplication by the real character sum, symmetric against the
orthonormal characters — at a loop window the label-index matrix is
the fusion counts' own, `M[x, y] = N^x_{θ y}` read at the
interface's count (`loopMag`, `prop:repring`'s orthonormality the
warrant, the vacuum defect the Kronecker delta at two labels), the
loop window's two-sided cap reading at `lem:loopcap` over the
interface's counts — and
the pair
`(α E : β M)`'s site datum `H([α : β])` is symmetric with pair
entries at weights of the positive carrier (`pencilH`, the free end's
own diagonal read `pencilE`, `symmRead` the transpose's
one-value read).  The magnetic matrix at fibered vertex
multiplicities — the intertwiner pairing's rows — arrives with
`prop:wg`'s presentation Gram at its recorded site, the loop
windows the tier's own compressions.
-/

namespace pairpencil
open ground lattice fusion elim

/-- The window diagonal with the unit line at its head, the
electric member's whole read. -/
def windowDiag {L : Type} (F : Data L) (R : Region) (C : Nat) :
    List Nat :=
  0 :: pencil.elecDiag F R C

/-- The label-index magnetic matrix at a loop window: over the unit
with a stated label list, `M[x, y] = N^x_{θ y}` — the
multiplication's matrix at the adjoint, `fpcap.fusionMat`'s read
at the unit-headed index. -/
def loopMag {L : Type} (F : Data L) (ls : List L) : Mat :=
  fpcap.fusionMat F F.theta (F.unit :: ls)

/-- The symmetry read: the matrix one value with its transpose. -/
def symmRead (m : Mat) : Prop := matOneValue m (transposeM m)

instance (m : Mat) : Decidable (symmRead m) :=
  inferInstanceAs (Decidable (matOneValue _ _))

/-- The pair `(α E : β M)`'s site datum `H([α : β])` at
`α E = β M + H`: the electric diagonal at the first weight against
the magnetic matrix at the second, every entry a pair datum at pair
weights. -/
def pencilH (al be : Pos) (diag : List Nat) (M : Mat) : Mat :=
  ground.matOf diag.length diag.length (fun i j =>
      ((if i == j
          then BPair.ofPos al * BPair.ofNat (ground.getAt 0 diag i)
          else BPair.unit)
        + (BPair.ofPos be
            * ground.getAt BPair.unit (ground.getAt [] M i) j).swap
       ).norm)

/-- The free end's window matrix, the electric member's own read:
the diagonal at the window contents alone — `prop:segment`'s
one-member weighting, its own site with no weight pair. -/
def pencilE (diag : List Nat) : Mat :=
  ground.matOf diag.length diag.length (fun i j =>
      if i == j then BPair.ofNat (ground.getAt 0 diag i)
      else BPair.unit)

/-- The window diagonal at a stated enumeration: the unit line at
the head over the index's contents, read off the committed
index. -/
theorem windowDiag_at {L : Type} (F : Data L) (R : Region) (C : Nat)
    (l : List (List L)) (d : List Nat) (hl : carrier.idx F R C = l)
    (hd : 0 :: l.map (carrier.contentN F) = d) :
    windowDiag F R C = d := by
  show 0 :: (carrier.idx F R C).map (carrier.contentN F) = d
  rw [hl]
  exact hd

end pairpencil
