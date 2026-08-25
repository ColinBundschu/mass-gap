import MassGap.Certconstruct
/-!
`thm:SO` — the window multiplicity is a count, and the count is a
divisor read: the ground bracket at a width below the pencil
polynomial's separation admits the ground root alone, the pair at
the lower level positive semidefinite and the upper count the
multiplicity (`multRead`, `thm:certconstruct`'s designation whole with the
lower pair's positivity the least-root sharpening — one spelling
of the one tex datum); and the character clause: a window
symmetry, an orthogonal map commuting with the pencil, reads the
ground line at a scalar squaring to one, the state's reads blind
to the grading (`symRead` at the stated data — the ground's
occupancy the floor certificate's own read, `def:K`'s
`floorRead` — the blind read the check module's pin).  The divisor
half reads at `thm:divisorid`(iii)'s cell theorem, the
multiplicity one integer per cell at the one pencil's two level
covers, over `thm:decimation`'s emitted record entries (the
two-sided bracket read the boundary binding at its flanking
samples), the free end at multiplicity one over the covered
bracket (`lem:freecell`'s batteries), and a move across a located
boundary a ground collision on the crossing read's locus
(`thm:divisorid`(ii)'s specialization).
-/

namespace SO
open ground elim inertia

/-- The multiplicity's certificate: the designation whole at the
ground bracket — the counts at the gap `m`, the width joining the
endpoints below the pencil polynomial's separation — with the
lower pair positive semidefinite, so the bracket admits the
ground root alone at the count the multiplicity. -/
def multRead {o : Nat} (H G : Mat) (ln ld hn hd wn wd : Pos)
    (m : Nat) (spl sph : Split o) : Prop :=
  certconstruct.desigWhole H G ln ld hn hd wn wd m spl sph
  ∧ psdAt spl

instance {o : Nat} (H G : Mat) (ln ld hn hd wn wd : Pos) (m : Nat)
    (spl sph : Split o) :
    Decidable (multRead H G ln ld hn hd wn wd m spl sph) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A window symmetry's ground read at the carrier: the map
commutes with the pencil, is orthogonal, and reads the ground at a
scalar squaring to one — the vector kept or read to its memberwise
swap, the graded read, the orders one by the types. -/
def symRead {n : Nat} (H g : SqMat n) (psi : Vec n) : Prop :=
  matOneValue (matMul g.val H.val) (matMul H.val g.val)
  ∧ matOneValue (matMul (transposeM g.val) g.val) (idMat n)
  ∧ (poly.oneValue (matVec g.val psi.val) psi.val
    ∨ poly.oneValue (matVec g.val psi.val) (psi.val.map BPair.swap))

instance {n : Nat} (H g : SqMat n) (psi : Vec n) :
    Decidable (symRead H g psi) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ (_ ∨ _)))

end SO
