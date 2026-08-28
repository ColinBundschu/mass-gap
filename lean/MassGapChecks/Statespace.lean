import MassGap.Statespace
import MassGap.Fusion
/-!
The check module for `lem:statespace`: the batteries re-read the
state's pairing by kernel `decide` at the free window's label
index — `⟨A ψ, B ψ⟩ = ⟨ψ, Aᵀ B ψ⟩` at the fundamental's and the
adjoint's multiplication matrices with the unit line's ground, and
the orthonormality tie: the probes' pairings at the committed list
read the evaluation's deltas, `prop:repring`'s display at the
matrix tier. -/
set_option maxHeartbeats 4000000

open ground elim statespace

private def u : BPair := BPair.unit

private def cF : SqMat 3 :=
  ⟨[[u, ⟨2, 1⟩, u], [⟨2, 1⟩, u, ⟨2, 1⟩], [u, ⟨2, 1⟩, u]], rfl⟩

private def cTh : SqMat 3 :=
  ⟨[[u, u, ⟨2, 1⟩], [u, ⟨2, 1⟩, u], [⟨2, 1⟩, u, ⟨2, 1⟩]], rfl⟩

private def psi0 : Vec 3 := ⟨[⟨2, 1⟩, u, u], rfl⟩

/-! The pairing read at the multiplication matrices. -/

example : pairRead cF cF psi0 := by decide +kernel
example : pairRead cF cTh psi0 := by decide +kernel
example : pairRead cTh cTh psi0 := by decide +kernel

/-! The involution's matrix at three letters, `prop:repring`'s
fourth read: over the dual-closed index `(𝟏, f, f̄, θ)` the dual
label's matrix is the transpose — and is off the label's own — the
self-dual blindness broken, with the pairing read at the dual
pair. -/

private def ix3 : List places.Shape :=
  [labels.unitL 3, [1, 0, 0], [0, 1, 0], adjchar.theta 3]

private def mF3 : Mat :=
  ix3.map (fun x => ix3.map (fun y =>
    BPair.ofNat ((fusion.dataA 3).count [1, 0, 0] y x)))

private def mFb3 : Mat :=
  ix3.map (fun x => ix3.map (fun y =>
    BPair.ofNat ((fusion.dataA 3).count [0, 1, 0] y x)))

example : matOneValue (transposeM mF3) mFb3 := by decide +kernel
example : ¬ matOneValue (transposeM mF3) mF3 := by decide +kernel
example : pairRead (⟨mF3, by decide +kernel⟩ : SqMat 4)
    (⟨mFb3, by decide +kernel⟩ : SqMat 4) ⟨[⟨2, 1⟩, u, u, u], rfl⟩ := by
  decide +kernel

/-! The fourth read's own instances at the shapes. -/

example : repring.invRead [1, 0, 0] [1, 1, 0] [0, 1, 0] := by decide +kernel
example : repring.invRead [1, 0, 0] [1, 0, 0] [1, 1, 0] := by decide +kernel
example : repring.invRead [1, 0, 0] [1, 0, 0] [1, 0, 0] := by decide +kernel

/-! The orthonormality tie: the probes' pairings read the
evaluation's deltas at the committed list. -/

example : (dotN (matVec cF.val psi0.val)
    (matVec cF.val psi0.val)).oneValue ⟨2, 1⟩ := by decide +kernel
example : (dotN (matVec cF.val psi0.val)
    (matVec cTh.val psi0.val)).oneValue u := by decide +kernel
example : (dotN (matVec cTh.val psi0.val)
    (matVec cTh.val psi0.val)).oneValue ⟨2, 1⟩ := by decide +kernel
