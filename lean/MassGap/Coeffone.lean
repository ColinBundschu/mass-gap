import MassGap.Momentform
/-!
`thm:coeffone` — the moments are read at coefficient one: for a
multiplication word `c` the exact line `[E, c] ψ = Ẽ (c ψ)` at the
join `E = β M + H`, so both moments depend on the probe through
`y = c ψ` alone with the pencil's `λ` the Hamiltonian's own
(`lineRead`, the commutator vector against the level gap's, one
value at every key; `groundRead` the join's ground clause
`H ψ = ε₀ ψ` cleared at a balance-pair floor; the magnetic member's
commutation the algebra's own read, `prop:algebra`'s instance pins
the check module's).  At the free end the ground is the unit line
and the level gap the electric member, the line's read outright —
the batteries' committed windows; the join's composition at a
general coupling — the line read against the pencil's own ground
at `α E = β M + H` — lands with the stage-rooted grounds at the
emitted certificates' tier (`lem:split`'s stored towers), the
free end the tier's own exact case.  The reads run at the unit
gram, the committed windows' own.
-/

namespace coeffone
open ground elim

/-- The exact line at a multiplication word: `[E, c] ψ = Ẽ (c ψ)`,
the commutator's vector against the level gap's, one value at
every key. -/
def lineRead (dg : List Nat) (C Et : SqMat dg.length)
    (psi : Vec dg.length) : Prop :=
  poly.oneValue (matVec (momentform.commE dg C.val) psi.val)
    (matVec Et.val (matVec C.val psi.val))

instance (dg : List Nat) (C Et : SqMat dg.length)
    (psi : Vec dg.length) : Decidable (lineRead dg C Et psi) :=
  poly.decOneValue _ _

/-- The join's ground clause: `H ψ = ε₀ ψ` at a balance-pair floor
`[en : ed]`, cleared. -/
def groundRead {n : Nat} (H : SqMat n) (psi : Vec n) (en : BPair)
    (ed : Pos) : Prop :=
  poly.oneValue (matVec (inertia.matScale ed H.val) psi.val)
    (poly.scaleP en psi.val)

instance {n : Nat} (H : SqMat n) (psi : Vec n) (en : BPair)
    (ed : Pos) : Decidable (groundRead H psi en ed) :=
  poly.decOneValue _ _

/-- The magnetic member's commutation with a multiplication word,
`prop:algebra`'s read at the matrices: the two orders one value
entrywise. -/
def commuteRead {n : Nat} (M C : SqMat n) : Prop :=
  matOneValue (matMul M.val C.val) (matMul C.val M.val)

instance {n : Nat} (M C : SqMat n) : Decidable (commuteRead M C) :=
  inferInstanceAs (Decidable (matOneValue _ _))

end coeffone
