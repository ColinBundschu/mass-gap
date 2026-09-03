import MassGap.Pairpencil
import MassGap.Certconstruct
/-!
`def:K` — the invariant's cut: at a coupling and a pair
`κ = [p : q]`, membership is the pair `(q Ẽ² : E₀ p Ẽ)` positive
semidefinite at every window, each test one reversal count on a
form pair (`cutRead`, the split the test's certificate,
`lem:inertia`'s read with the pair cleared to integer coefficients,
the positive rescaling fixing the count); the level gap `Ẽ` enters
at its floor certificate, `ε₀ G + Ẽ = H` with the pair at the floor
positive semidefinite and the ground occupied (`floorRead`,
`gapMat` the cleared site datum); clause (i)'s membership is the
meet of these window tests over the directed family, each window's
test `cutRead`'s read at its certificate with the window's pencil
the chain assembly's presentation (`thm:pairpencil` the pencils'
entry, `thm:gappos`'s tier the per-window derivation), the member
instantiations reading through `thm:main`'s wiring at their floor
windows, the main check module's pins.  The compression to
the word sector reads at
`thm:coeffone`'s exact line — at the free end the word sector is the
window itself (`lem:freeend`), and the free-end reading closes
here: the level gap is the electric member at the window list's
diagonal (`freeGap`, the unit line at its head), the cut's pair is diagonal with the entries
`c ⟨q c : E₀ p⟩`, and the cut holds at every pair at or below the
member floor and fails beyond, the floor's edge neutral — the
check module's pins at the committed windows, `lem:casfloor`'s
floors with `prop:E0`'s count the levels' data, the first computed
value of the invariant.  The descent tier carries
`thm:unitschain`'s scaling form at the cut: the square at the
ray factor's square against the gap and the level's first member
at the factor (`cutRead_scale`, `cutRead_unscale`), the reversal
blind to the positive multiple (`lem:inertia`).
-/

namespace K
open ground elim inertia lattice

/-- The level gap's cleared site datum at a floor pair `[en : ed]`,
the first member a balance pair (the free end's floor the
equal-membered class): `ed·H - en·G`, the datum at `ε₀ G + Ẽ = H`
cleared. -/
def gapMat (H G : Mat) (en : BPair) (ed : Pos) : Mat :=
  siteDatum (matScale ed H) (matScaleB en G)

/-- The floor's certificate: the pair `(H : ε₀ G)` positive
semidefinite with the ground occupied, the kernel block's order
beyond the sum's unit. -/
def floorRead {o : Nat} (H G : Mat) (en : BPair) (ed : Pos) (sp : Split o) : Prop :=
  sqAt H o ∧ sqAt G o
  ∧ splitRead (gapMat H G en ed) sp ∧ psdAt sp ∧ 1 ≤ sp.kern

instance {o : Nat} (H G : Mat) (en : BPair) (ed : Pos) (sp : Split o) :
    Decidable (floorRead H G en ed sp) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The cut's test at a window: the pair `(q Ẽ² : E₀ p Ẽ)` positive
semidefinite at the split certificate, one reversal count on the
form pair — the two compressed forms entering as data, the square's
compression `(Ẽ²)_Λ` beside the gap's `(Ẽ)_Λ`, the detector form
compressed whole; at the free end the word sector is the window
itself and the square is the gap's own (`lem:freeend`). -/
def cutRead {o : Nat} (Esq Et : Mat) (E0 p q : Pos) (sp : Split o) : Prop :=
  sqAt Esq o ∧ sqAt Et o
  ∧ leAt (matScale (E0 * p) Et) (matScale q Esq) sp

instance {o : Nat} (Esq Et : Mat) (E0 p q : Pos) (sp : Split o) :
    Decidable (cutRead Esq Et E0 p q sp) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The cut datum's rescaling: the site datum at the `u²`-scaled
square, the `u`-scaled gap and the `u`-scaled level is the base
datum's `u²`-multiple, the square's two scale steps against the
gap's one (`thm:unitschain`'s degree-one homogeneity at the cut's
own carrier). -/
private theorem cutScale (u : Pos) (Esq Et : Mat) (E0 p q : Pos) :
    matScale (u * u) (siteDatum (matScale q Esq)
        (matScale (E0 * p) Et))
      = siteDatum (matScale q (matScale (u * u) Esq))
          (matScale (E0 * (u * p)) (matScale u Et)) := by
  show matScale (u * u) (matAdd (matScale q Esq)
      (matSwap (matScale (E0 * p) Et)))
    = matAdd (matScale q (matScale (u * u) Esq))
        (matSwap (matScale (E0 * (u * p)) (matScale u Et)))
  rw [matScale_matAdd (u * u) (matScale q Esq)
      (matSwap (matScale (E0 * p) Et)),
    matScale_matScale q (u * u) Esq,
    matScale_matSwap (u * u) (matScale (E0 * p) Et),
    matScale_matScale (E0 * p) (u * u) Et,
    matScale_matScale (u * u) q Esq,
    matScale_matScale u (E0 * (u * p)) Et,
    ground.mul_comm (u * u) q,
    show (u * u) * (E0 * p) = (E0 * (u * p)) * u by
      rw [ground.mul_comm (u * u) (E0 * p),
        ground.mul_assoc E0 p (u * u),
        ← ground.mul_assoc p u u,
        ground.mul_comm p u,
        ← ground.mul_assoc E0 (u * p) u]]

/-- The cut descends along the ray (`thm:unitschain`): the cut at
the `u²`-scaled square, the `u`-scaled gap and the level's first
member at the `u`-multiple reads with the base cut — the square of
the `u`-scaled gap the two scale steps — the scaled certificate's
split stated data and its positive-semidefinite read the base's
own, the reversal blind to the ray's factor. -/
theorem cutRead_scale {o : Nat} (u : Pos) (Esq Et : Mat)
    (E0 p q : Pos) (sp sp' : Split o)
    (h : cutRead Esq Et E0 p q sp)
    (h' : splitRead (siteDatum (matScale q (matScale (u * u) Esq))
      (matScale (E0 * (u * p)) (matScale u Et))) sp') :
    cutRead (matScale (u * u) Esq) (matScale u Et) E0 (u * p) q
      sp' :=
  ⟨sqAt_matScale o (u * u) Esq h.1, sqAt_matScale o u Et h.2.1, h',
   (rev_scalePos (u * u)
     (siteDatum (matScale q Esq) (matScale (E0 * p) Et)) sp sp'
     h.2.2.1 (by rw [cutScale u Esq Et E0 p q]; exact h')).trans
     h.2.2.2⟩

/-- The descent's return (`thm:unitschain`): a cut at the
`u`-scaled data and level reads back at the base, the base split
stated data. -/
theorem cutRead_unscale {o : Nat} (u : Pos) (Esq Et : Mat)
    (E0 p q : Pos) (sp sp' : Split o)
    (h : cutRead (matScale (u * u) Esq) (matScale u Et) E0 (u * p)
      q sp')
    (hs : splitRead (siteDatum (matScale q Esq)
      (matScale (E0 * p) Et)) sp) :
    cutRead Esq Et E0 p q sp :=
  ⟨sqAt_matScale_reflect (u * u) Esq h.1,
   sqAt_matScale_reflect u Et h.2.1, hs,
   (rev_scalePos (u * u)
     (siteDatum (matScale q Esq) (matScale (E0 * p) Et)) sp sp'
     hs (by rw [cutScale u Esq Et E0 p q]; exact h.2.2.1)).symm.trans
     h.2.2.2⟩

/-- The free end's level gap: the electric member at the window
list's diagonal with the unit line at its head, `lem:freeend`'s
diagonal presentation. -/
def freeGap {L : Type} (F : fusion.Data L) (R : Region) (C : Nat) :
    Mat :=
  pairpencil.pencilE (pairpencil.slotDiag F R (carrier.idx F R C))

/-- The free-end level gap at a stated window list's diagonal:
`lem:freeend`'s diagonal presentation read off the committed
diagonal. -/
theorem freeGap_ofDiag {L : Type} (F : fusion.Data L) (R : Region)
    (C : Nat) (d : List Nat) (m : Mat)
    (hd : pairpencil.slotDiag F R (carrier.idx F R C) = d)
    (hm : pairpencil.pencilE d = m) :
    freeGap F R C = m := by
  show pairpencil.pencilE (pairpencil.slotDiag F R (carrier.idx F R C)) = m
  rw [hd]
  exact hm

end K
