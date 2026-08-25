import MassGap.Certconstruct
/-!
`lem:statespace` — the word sector is the state's own space:
`ω(Ā B) = ⟨A ψ, B ψ⟩`, both sides the one read at the stated data —
at the window matrices the pairing of the probes' vectors equals
the state's read of the product's action, the transport identity
`⟨A ψ, B ψ⟩ = ⟨ψ, Aᵀ B ψ⟩` (`pairRead`; the involution's matrix at
the label index is the transpose, `prop:repring`'s fourth read
`N^c_{ā b} = N^b_{a c}`, the dual pair's pins the check module's
at three letters).  The reads run at the unit gram, the committed
loop windows' own; the fibered gram rides `prop:wg`'s site.  The sector's cyclicity — `A ↦ A ψ` linear with
`Sect∞ ψ` its image — rides the prose at `def:pencil`'s sector,
the reads the displays'.
-/

namespace statespace
open ground elim

/-- The state's pairing read: `⟨A ψ, B ψ⟩ = ⟨ψ, Aᵀ B ψ⟩`, the
probes' pairing against the state's read of the product, one
value. -/
def pairRead {n : Nat} (A B : SqMat n) (psi : Vec n) : Prop :=
  (dotN (matVec A.val psi.val) (matVec B.val psi.val)).oneValue
    (dotN psi.val
      (matVec (matMul (transposeM A.val) B.val) psi.val))

instance {n : Nat} (A B : SqMat n) (psi : Vec n) :
    Decidable (pairRead A B psi) :=
  inferInstanceAs (Decidable (BPair.oneValue _ _))

end statespace
