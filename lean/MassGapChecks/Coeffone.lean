import MassGap.Coeffone
/-!
The check module for `thm:coeffone`: the window commutator's additive
join at the free-end window `diag(0, 12, 32)`, the ground's equation
at its cleared level, and the compressed commutation read with its
refusal at the truncated fusion matrices.

The one-plaquette `A₁` window at the fundamental cutoff is read at
its doubled Hamiltonian `[[0,-2],[-2,3]]`, ground `(2,1)` at level
`-1`, and the compressed squared-character probe `diag(1,2)`.
Its level gap `[[1,-2],[-2,4]]` is positive semidefinite. The
Hamiltonian commutator reads the level gap's image; the electric
commutator at `diag(0,3)` reads the sum's unit and refuses that
image, the boundary contraction's occupied instance. At the list
`(1, 2f)` the Gram is `diag(1,4)`; its solves give the actions
`K` and `D`. Their line holds, while substituting the form matrices
`H` and `S` refuses it, at the probe `2f` and ground `(4,1)`.
-/

namespace coeffone
set_option maxHeartbeats 4000000

open ground elim

private def u : BPair := BPair.unit

private def et3 : SqMat 3 :=
  ⟨[[u, u, u], [u, ⟨13, 1⟩, u], [u, u, ⟨33, 1⟩]], rfl⟩

private def cF : SqMat 3 :=
  ⟨[[u, ⟨2, 1⟩, u], [⟨2, 1⟩, u, ⟨2, 1⟩], [u, ⟨2, 1⟩, u]], rfl⟩

private def cTh : SqMat 3 :=
  ⟨[[u, u, ⟨2, 1⟩], [u, ⟨2, 1⟩, u], [⟨2, 1⟩, u, ⟨2, 1⟩]], rfl⟩

private def psi0 : Vec 3 := ⟨[⟨2, 1⟩, u, u], rfl⟩

/-! The exact line at the free end: the commutator's vector equals
the level gap's at the multiplied ground, at the fundamental's and
the adjoint's multiplication matrices; an under-dimensioned
diagonal or an off-index ground is unrepresentable at the
carrier. -/

theorem pin1 : lineRead et3 cF et3 psi0 := by decide +kernel
theorem pin2 : lineRead et3 cTh et3 psi0 := by decide +kernel

/-! The ground clause: the free window's unit line at the
equal-membered floor, and `diag(1, 3)`'s ground at its own
level. -/

theorem pin3 : groundRead et3 psi0 u 1 := by decide +kernel
theorem pin4 : groundRead (⟨[[⟨2, 1⟩, u], [u, ⟨4, 1⟩]], rfl⟩ : SqMat 2)
    ⟨[⟨2, 1⟩, u], rfl⟩ ⟨2, 1⟩ 1 := by decide +kernel

/-! The magnetic commutation at the unit multiplication and its
refusal at truncated fusion matrices, with the window line's
Hamiltonian read at an occupied boundary contraction. -/

theorem pin5 : commuteRead cTh (⟨elim.idMat 3, rfl⟩ : SqMat 3) := by
  decide +kernel
theorem pin6 : ¬ commuteRead cF cTh ∧
    (let H : SqMat 2 := ⟨[[u, ⟨1, 3⟩], [⟨1, 3⟩, ⟨4, 1⟩]], rfl⟩
     let C : SqMat 2 := ⟨[[⟨2, 1⟩, u], [u, ⟨3, 1⟩]], rfl⟩
     let Et : SqMat 2 := ⟨[[⟨2, 1⟩, ⟨1, 3⟩], [⟨1, 3⟩, ⟨5, 1⟩]], rfl⟩
     let psi : Vec 2 := ⟨[⟨3, 1⟩, ⟨2, 1⟩], rfl⟩
     groundRead H psi ⟨1, 2⟩ 1
     ∧ inertia.splitRead Et.val (inertia.mkSplit 2 Et.val)
     ∧ inertia.psdAt (inertia.mkSplit 2 Et.val)
     ∧ lineRead H C Et psi
     ∧ ¬ poly.oneValue (matVec (momentform.commE [0, 3] C.val) psi.val)
         (matVec Et.val (matVec C.val psi.val))) ∧
    (let G : Mat := [[⟨2, 1⟩, u], [u, ⟨5, 1⟩]]
     let H : SqMat 2 := ⟨[[u, ⟨1, 5⟩], [⟨1, 5⟩, ⟨13, 1⟩]], rfl⟩
     let S : SqMat 2 := ⟨[[⟨2, 1⟩, ⟨1, 5⟩], [⟨1, 5⟩, ⟨17, 1⟩]], rfl⟩
     let K : SqMat 2 := ⟨[[u, ⟨1, 5⟩], [⟨1, 2⟩, ⟨4, 1⟩]], rfl⟩
     let D : SqMat 2 := ⟨[[⟨2, 1⟩, ⟨1, 5⟩], [⟨1, 2⟩, ⟨5, 1⟩]], rfl⟩
     let C : SqMat 2 := ⟨[[u, ⟨5, 1⟩], [⟨2, 1⟩, u]], rfl⟩
     let psi : Vec 2 := ⟨[⟨5, 1⟩, ⟨2, 1⟩], rfl⟩
     matOneValue (matMul G K.val) H.val
     ∧ matOneValue (matMul G D.val) S.val
     ∧ matOneValue (matMul G C.val) (matMul (transposeM C.val) G)
     ∧ inertia.splitRead S.val (inertia.mkSplit 2 S.val)
     ∧ inertia.psdAt (inertia.mkSplit 2 S.val)
     ∧ groundRead K psi ⟨1, 2⟩ 1
     ∧ lineRead K C D psi
     ∧ ¬ lineRead H C S psi) := by decide +kernel

end coeffone
