import MassGap.Carrier
import MassGap.Inertia
/-!
`def:pencil` — the pencil's electric member at the index layer: `E`
is diagonal in the label index, scaling a configuration's summand by
its content and reading the unit line as its kernel; over a window
the diagonal is the index's content list (`elecDiag`), and `E` is
positive semidefinite with the unit line its kernel by the contents'
positivity (`diagPos`).  The pair `(αE : βM)`'s site datum
`H([α : β])` at stated electric and magnetic matrices is `rayH`, the
join `αE = βM + H` read as the site datum of the two scaled members
(`inertia.siteDatum`), square at the members' order (`sqAt_rayH`)
and degree one in the weights: at both weights' `u`-multiples the
datum is the `u`-rescaled datum entry by entry (`rayH_scale`, the
homogeneity `prop:segment` reads).  The magnetic member `M` itself,
the floor `ε₀` with the level gap `Ẽ`, the root coordinate and the
word sector land with their consumers (`def:algebra`'s product at
the magnetic matrix, `def:K`'s cut, `thm:coeffone`'s moments).
-/

namespace pencil
open ground lattice fusion elim inertia

/-- The electric diagonal over the window index: one content per
index member, the unit line the kernel beside them. -/
def elecDiag {L : Type} (F : Data L) (R : Region) (C : Nat) :
    List Nat :=
  (carrier.idx F R C).map (carrier.contentN F)

/-- The diagonal's positivity: every occupied content positive, `E`
positive semidefinite with the unit line its kernel by
construction. -/
def diagPos {L : Type} (F : Data L) (R : Region) (C : Nat) : Prop :=
  ((elecDiag F R C).all (fun c => 0 < c)) = true

instance {L : Type} (F : Data L) (R : Region) (C : Nat) :
    Decidable (diagPos F R C) :=
  inferInstanceAs (Decidable (_ = _))

/-- The electric diagonal at a stated enumeration: one content per
index member, read off the committed index. -/
theorem elecDiag_at {L : Type} (F : Data L) (R : Region) (C : Nat)
    (l : List (List L)) (d : List Nat) (hl : carrier.idx F R C = l)
    (hd : l.map (carrier.contentN F) = d) :
    elecDiag F R C = d := by
  show (carrier.idx F R C).map (carrier.contentN F) = d
  rw [hl]
  exact hd

/-- The pair `(α E : β M)`'s site datum `H([α : β])` at stated
electric and magnetic matrices, `α E = β M + H`. -/
def rayH (E M : Mat) (al be : Pos) : Mat :=
  siteDatum (matScale al E) (matScale be M)

/-- The pencil keeps the members' order. -/
theorem sqAt_rayH (E M : Mat) (o : Nat) (hE : sqAt E o) (hM : sqAt M o)
    (al be : Pos) : sqAt (rayH E M al be) o :=
  sqAt_siteDatum o _ _ (sqAt_matScale o al E hE) (sqAt_matScale o be M hM)

/-- The pencil's degree-one homogeneity: at both weights'
`u`-multiples the site datum is the `u`-rescaled datum, entry by
entry, the join's shape degree one in each weight. -/
theorem rayH_scale (E M : Mat) (u al be : Pos) :
    rayH E M (u * al) (u * be) = matScale u (rayH E M al be) := by
  unfold rayH siteDatum
  rw [matScale_matAdd u, matScale_matSwap u, matScale_matScale al u E,
    matScale_matScale be u M]

end pencil
