import MassGap.Coeffone
/-!
The check module for `thm:coeffone`: the batteries re-read the
exact line by kernel `decide` at the free end's window
`diag(0, 12, 32)` — `[E, c] ψ = Ẽ (c ψ)` at the fundamental's and
the adjoint's multiplication matrices with the unit line's ground,
the level gap the electric member and the floor the equal-membered
class (`groundRead` at the window and at the `diag(1, 3)` pencil's
own ground), and the magnetic commutation's read at the unit
multiplication, the interface's commutativity law the general
statement's own site (`fusion.commLaw`; a truncated index leaks at
its frontier, the closed sub-indices the member tier's). -/
set_option maxHeartbeats 4000000

open ground elim coeffone

private def u : BPair := BPair.unit

private def dg3 : List Nat := [0, 12, 32]

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

example : lineRead dg3 cF et3 psi0 := by decide +kernel
example : lineRead dg3 cTh et3 psi0 := by decide +kernel

/-! The ground clause: the free window's unit line at the
equal-membered floor, and `diag(1, 3)`'s ground at its own
level. -/

example : groundRead et3 psi0 u 1 := by decide +kernel
example : groundRead (⟨[[⟨2, 1⟩, u], [u, ⟨4, 1⟩]], rfl⟩ : SqMat 2)
    ⟨[⟨2, 1⟩, u], rfl⟩ ⟨2, 1⟩ 1 := by decide +kernel

/-! The magnetic commutation at the unit multiplication, the
frontier-closed instance, with the truncated index's frontier leak
a live refusal — the closed sub-indices the member tier's. -/

example : commuteRead cTh (⟨inertia.idMat 3, rfl⟩ : SqMat 3) := by
  decide +kernel
example : ¬ commuteRead cF cTh := by decide +kernel
