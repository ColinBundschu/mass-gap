import MassGap.Momentform
/-!
The check module for `thm:momentform`: the batteries re-read the
two-moment form by kernel `decide` — the probe's vector and the
two moments at the diagonal instance, the requirement read with
its refusal, the electric commutator's entries at the diagonal's
gaps, `Q₂ = [E,f]†[E,f]`, and the evaluation displays at the free
end's window: `μ₂(f) = ω(Q₂(f))` and `μ₁(f) = ω(f†[E,f])`, the
moments reading the probe through `y = f ψ` alone at the unit
line's ground. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground elim momentform

private def u : BPair := BPair.unit

private def hD : SqMat 2 := ⟨[[⟨2, 1⟩, u], [u, ⟨4, 1⟩]], rfl⟩

private def v11 : Vec 2 := ⟨[⟨2, 1⟩, ⟨2, 1⟩], rfl⟩

/-! The moments at the diagonal instance with the probe `(1, 1)`:
`μ₁ = 4`, `μ₂ = 10`, the requirement at the level two with the
refusal at three; a probe off the window's order is
unrepresentable at the carrier. -/

example : (mu1 hD v11).oneValue ⟨5, 1⟩ := by decide +kernel
example : (mu2 hD v11).oneValue ⟨11, 1⟩ := by decide +kernel
example : reqRead hD v11 2 1 := by decide +kernel
example : ¬ reqRead hD v11 3 1 := by decide +kernel

/-! The electric commutator at the diagonal's gaps: entries
`(dᵢ + dⱼˇ) Fᵢⱼ`, and `Q₂`'s square. -/

example : matOneValue (commE [1, 3] [[u, ⟨2, 1⟩], [⟨2, 1⟩, u]])
    [[u, ⟨1, 3⟩], [⟨3, 1⟩, u]] := by decide +kernel
example : matOneValue (q2 [1, 3] [[u, ⟨2, 1⟩], [⟨2, 1⟩, u]])
    [[⟨5, 1⟩, u], [u, ⟨5, 1⟩]] := by decide +kernel

/-! The evaluation displays at the free end's window
`diag(0, 12, 32)` with the fundamental's multiplication matrix and
the unit line's ground: `μ₂(f) = ω(Q₂(f))` and
`μ₁(f) = ω(f†[E, f])`, both moments through `y = f ψ`. -/

private def dg3 : List Nat := [0, 12, 32]

private def et3 : SqMat 3 :=
  ⟨[[u, u, u], [u, ⟨13, 1⟩, u], [u, u, ⟨33, 1⟩]], rfl⟩

private def cF : Mat :=
  [[u, ⟨2, 1⟩, u], [⟨2, 1⟩, u, ⟨2, 1⟩], [u, ⟨2, 1⟩, u]]

private def cFs : SqMat 3 := ⟨cF, rfl⟩

private def psi0 : Vec 3 := ⟨[⟨2, 1⟩, u, u], rfl⟩

example : poly.oneValue (probeVec cFs psi0).val [u, ⟨2, 1⟩, u] := by
  decide +kernel

example : (inertia.quadForm (q2 dg3 cF) psi0.val).oneValue
    (mu2 et3 (probeVec cFs psi0)) := by decide +kernel

example : (dotN psi0.val
    (matVec (matMul (transposeM cF) (commE dg3 cF))
      psi0.val)).oneValue
    (mu1 et3 (probeVec cFs psi0)) := by decide +kernel
