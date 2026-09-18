import MassGap.Momentform
/-!
`thm:coeffone` — the window commutator and its boundary reads.

`lineRead` is the displayed additive join
`K (C ψ) = C (K ψ) + D (C ψ)` at the supplied window Hamiltonian
action, compressed probe and level-gap action. `groundRead` is the ground equation
at its cleared balance-pair level. Both are finite vector reads.

The boundary identity in the tex reads `[K, C]` as the electric
commutator joined to the weighted boundary contraction. At a
contraction reading the sum's unit on the ground the line reads
the electric commutator. `commuteRead` is the stronger matrix read that
the compressed magnetic member commutes with the compressed probe;
its two products read the boundary contraction at equal members.
The full multiplication algebra's commutation is read before the
cutoff projection. At a general Gram the input actions are the solves
`GK = H` and `GD = S` (`def:pencil`); at the unit Gram they read the
form matrices themselves. The vector identities take the actions.
-/

namespace coeffone
open ground elim

/-- The window commutator's line at its additive join
`K (C ψ) = C (K ψ) + D (C ψ)` (`thm:coeffone`), one value at
every key, with `K` and `D` the supplied window's actions. -/
def lineRead {n : Nat} (K C D : SqMat n) (psi : Vec n) : Prop :=
  poly.oneValue (matVec K.val (matVec C.val psi.val))
    (poly.add (matVec C.val (matVec K.val psi.val))
      (matVec D.val (matVec C.val psi.val)))

instance instCoeffone1 {n : Nat} (K C D : SqMat n)
    (psi : Vec n) : Decidable (lineRead K C D psi) :=
  poly.decOneValue _ _

/-- The action's ground clause: `K ψ = ε₀ ψ` at a balance-pair floor
`[en : ed]`, cleared (`def:pencil`'s action from the Gram solve). -/
def groundRead {n : Nat} (K : SqMat n) (psi : Vec n) (en : BPair)
    (ed : Pos) : Prop :=
  poly.oneValue (matVec (inertia.matScale ed K.val) psi.val)
    (poly.scaleP en psi.val)

instance instCoeffone2 {n : Nat} (K : SqMat n) (psi : Vec n) (en : BPair)
    (ed : Pos) : Decidable (groundRead K psi en ed) :=
  poly.decOneValue _ _

/-- The compressed magnetic member's commutation with a compressed
probe: the two matrix products one value entrywise. This is the
boundary contraction's equal-members read (`thm:coeffone`). -/
def commuteRead {n : Nat} (M C : SqMat n) : Prop :=
  matOneValue (matMul M.val C.val) (matMul C.val M.val)

instance instCoeffone3 {n : Nat} (M C : SqMat n) : Decidable (commuteRead M C) :=
  inferInstanceAs (Decidable (matOneValue _ _))

end coeffone
