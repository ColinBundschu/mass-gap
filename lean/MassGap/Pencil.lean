import MassGap.Carrier
/-!
`def:pencil` — the pencil's electric member at the index layer: `E`
is diagonal in the label index, scaling a configuration's summand by
its content and reading the unit line as its kernel; over a window
the diagonal is the index's content list (`elecDiag`), and `E` is
positive semidefinite with the unit line its kernel by the contents'
positivity (`diagPos`).  The magnetic member `M` with the pair
`(αE : βM)` and its site datum `H`, the floor `ε₀` with the level
gap `Ẽ`, the root coordinate and the word sector land with their
consumers (`def:algebra`'s product at the magnetic matrix,
`def:K`'s cut, `thm:coeffone`'s moments).
-/

namespace pencil
open ground lattice fusion

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

end pencil
