import MassGap.Certconstruct
/-!
`thm:momentform` — the two-moment form: a probe's moments depend on
it through `y = A ψ` alone (`probeVec`, the matrix against the
ground), the moments the quadratic reads `μ₁ = ⟨y, Ẽ y⟩` and
`μ₂ = ⟨y, Ẽ² y⟩` (`mu1`, `mu2` at `thm:certconstruct`'s form
fold), and the requirement per probe is one cleared inequality
(`reqRead`, the coupling entering through the state alone).  For a
multiplication probe the commutator is the electric member's,
`[H, f] = [E, f]` (`commE` at the diagonal's gaps, the magnetic
member commuting by `prop:algebra`), and the second moment's
operator is `Q₂(f) = [E, f]† [E, f]` (`q2`); the evaluation
displays `μ₂(f) = ω(Q₂(f))` and `μ₁(f) = ω(f†[E, f])`
(`thm:coeffone`'s exact line read at the state) are the check
module's coherence pins at the free end's ground; the multiplication
family's sufficiency — `A ↦ A ψ` linear with the word sector its
image — is `lem:statespace`'s layer with `def:pencil`'s sector.
The pairings below read at the unit gram, the committed loop
windows' own; the fibered gram rides `prop:wg`'s site.  The
commutator's fold truncates at the shorter operand, the
certificate Props' standing shape convention; the probe's order
is the carrier's own.
-/

namespace momentform
open ground elim

/-- The probe's vector: `y = A ψ` at the carrier, the moments' one
datum. -/
def probeVec {n : Nat} (A : SqMat n) (psi : Vec n) : Vec n :=
  appSq A psi

/-- The first moment `μ₁ = ⟨y, Ẽ y⟩`, the level gap's quadratic
read at the probe's vector. -/
def mu1 {n : Nat} (Et : SqMat n) (y : Vec n) : BPair :=
  inertia.quadForm Et.val y.val

/-- The second moment `μ₂ = ⟨y, Ẽ² y⟩` at the square. -/
def mu2 {n : Nat} (Et : SqMat n) (y : Vec n) : BPair :=
  inertia.quadForm (matMul Et.val Et.val) y.val

/-- The requirement's read at a probe: `μ₂ ≥ γ μ₁` at the level
`[gn : gd]`, cleared at the carrier's one order — the coupling
entering through the state alone. -/
def reqRead {n : Nat} (Et : SqMat n) (y : Vec n) (gn gd : Pos) :
    Prop :=
  ¬ (mu2 Et y).scale gd < (mu1 Et y).scale gn

instance {n : Nat} (Et : SqMat n) (y : Vec n) (gn gd : Pos) :
    Decidable (reqRead Et y gn gd) :=
  inferInstanceAs (Decidable (¬ _ < _))

/-- The electric commutator `[E, f]` at the diagonal member: entry
`(dᵢ + dⱼˇ) Fᵢⱼ`, the diagonal's gaps against the multiplication
matrix. -/
def commE (dg : List Nat) (F : Mat) : Mat :=
  List.zipWith (fun di row =>
    List.zipWith (fun dj e =>
      ((BPair.ofNat di + (BPair.ofNat dj).swap) * e).norm) dg row)
    dg F

/-- The second moment's operator `Q₂(f) = [E, f]† [E, f]`, positive
by its shape. -/
def q2 (dg : List Nat) (F : Mat) : Mat :=
  let c := commE dg F
  matMul (transposeM c) c

end momentform
