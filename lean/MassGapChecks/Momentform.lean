import MassGap.Momentform
/-!
The check module for `thm:momentform`: the batteries re-read the
two-moment form by kernel `decide` — the probe's vector and the
two moments at the diagonal instance, the requirement read with
its refusal, the electric commutator's entries at the diagonal's
gaps, `Q₂ = [K,f]†[K,f]`, and the evaluation displays at the free
end's window: `μ₂(f) = ω(Q₂(f))` and `μ₁(f) = ω(f†[E,f])`, the
moments reading the probe through `y = f ψ` alone at the unit
line's ground. The one-plaquette boundary instance reads the first
moment at four and the second at twenty at the doubled Hamiltonian,
while the electric commutator's square reads the sum's unit. At the
list `(1,2f)` with Gram `diag(1,4)`, the probe `2f` and ground `(4,1)`
read moments `144` and `720` at the forms `S` and `Cᵀ G C`, with
`GD = S` tying the second form to the gap action's squared image. -/

namespace momentform
set_option maxHeartbeats 4000000

open ground elim

private def u : BPair := BPair.unit

private def hD : SqMat 2 := ⟨[[⟨2, 1⟩, u], [u, ⟨4, 1⟩]], rfl⟩

private def v11 : Vec 2 := ⟨[⟨2, 1⟩, ⟨2, 1⟩], rfl⟩

/-! The moments at the diagonal instance with the probe `(1, 1)`:
`μ₁ = 4`, `μ₂ = 10`, the requirement at the level two with the
refusal at three; a probe off the window's order is
unrepresentable at the carrier. -/

theorem pin1 : (mu1 hD v11).oneValue ⟨5, 1⟩ := by decide +kernel
theorem pin2 : (mu2 hD v11).oneValue ⟨11, 1⟩ := by decide +kernel
theorem pin3 : reqRead hD v11 2 1 := by decide +kernel
theorem pin4 : ¬ reqRead hD v11 3 1 := by decide +kernel

/-! The electric commutator at the diagonal's gaps: entries
`(dᵢ + dⱼˇ) Fᵢⱼ`, and `Q₂`'s square. -/

theorem pin5 : matOneValue (commE [1, 3] [[u, ⟨2, 1⟩], [⟨2, 1⟩, u]])
    [[u, ⟨1, 3⟩], [⟨3, 1⟩, u]] := by decide +kernel
theorem pin6 : matOneValue (q2 hD.val [[u, ⟨2, 1⟩], [⟨2, 1⟩, u]])
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

theorem pin7 : poly.oneValue (probeVec cFs psi0).val [u, ⟨2, 1⟩, u] := by
  decide +kernel

theorem pin8 : (inertia.quadForm (q2 et3.val cF) psi0.val).oneValue
    (mu2 et3 (probeVec cFs psi0)) := by decide +kernel

theorem pin9 : (dotN psi0.val
    (matVec (matMul (transposeM cF) (commE dg3 cF))
      psi0.val)).oneValue
    (mu1 et3 (probeVec cFs psi0)) ∧
    (let H : Mat := [[u, ⟨1, 3⟩], [⟨1, 3⟩, ⟨4, 1⟩]]
     let C : SqMat 2 := ⟨[[⟨2, 1⟩, u], [u, ⟨3, 1⟩]], rfl⟩
     let Et : SqMat 2 := ⟨[[⟨2, 1⟩, ⟨1, 3⟩], [⟨1, 3⟩, ⟨5, 1⟩]], rfl⟩
     let psi : Vec 2 := ⟨[⟨3, 1⟩, ⟨2, 1⟩], rfl⟩
     (mu1 Et (probeVec C psi)).oneValue ⟨5, 1⟩
     ∧ (mu2 Et (probeVec C psi)).oneValue ⟨21, 1⟩
     ∧ (inertia.quadForm (q2 H C.val) psi.val).oneValue
         (mu2 Et (probeVec C psi))
     ∧ (inertia.quadForm
         (q2 [[u, u], [u, ⟨4, 1⟩]] C.val) psi.val).oneValue u) ∧
    (let G : Mat := [[⟨2, 1⟩, u], [u, ⟨5, 1⟩]]
     let S : Mat := [[⟨2, 1⟩, ⟨1, 5⟩], [⟨1, 5⟩, ⟨17, 1⟩]]
     let K : Mat := [[u, ⟨1, 5⟩], [⟨1, 2⟩, ⟨4, 1⟩]]
     let D : Mat := [[⟨2, 1⟩, ⟨1, 5⟩], [⟨1, 2⟩, ⟨5, 1⟩]]
     let A : Mat := [[u, ⟨5, 1⟩], [⟨2, 1⟩, u]]
     let psi := [⟨5, 1⟩, ⟨2, 1⟩]
     let v := matVec A psi
     let c := matAdd (matMul K A) (matSwap (matMul A K))
     matOneValue (matMul G D) S
     ∧ (inertia.quadForm S v).oneValue ⟨145, 1⟩
     ∧ (inertia.quadForm G (matVec D v)).oneValue ⟨721, 1⟩
     ∧ (inertia.quadForm (matMul (transposeM c) (matMul G c)) psi).oneValue
         (inertia.quadForm G (matVec D v))) := by
  decide +kernel

/-! `thm:coeffone`'s commutator display at `commE_read`: the
commutator's action on a vector is the diagonal's action of the
multiplication's read joined to the multiplication's action of the
diagonal's at the memberwise swap, the swap the subtraction — the
cell at the vacant diagonal head `[0, 4]` and the cell at the
occupied head `[1, 3]`, each landed by the theorem route beside its
own `decide`. -/

private def dgV : List Nat := [0, 4]

private def dgO : List Nat := [1, 3]

private def cX : Mat := [[u, ⟨2, 1⟩], [⟨2, 1⟩, u]]

private def vX : List BPair := [⟨2, 1⟩, u]

theorem pin10 : poly.oneValue (matVec (commE dgV cX) vX)
    (poly.add
      (matVec (diagO ground.bpairOps (dgV.map BPair.ofNat)) (matVec cX vX))
      ((matVec cX (matVec (diagO ground.bpairOps
        (dgV.map BPair.ofNat)) vX)).map BPair.swap)) :=
  commE_read dgV cX vX 2 rfl ⟨rfl, rfl, trivial⟩ rfl rfl

theorem pin11 : poly.oneValue (matVec (commE dgV cX) vX)
    (poly.add
      (matVec (diagO ground.bpairOps (dgV.map BPair.ofNat)) (matVec cX vX))
      ((matVec cX (matVec (diagO ground.bpairOps
        (dgV.map BPair.ofNat)) vX)).map BPair.swap)) := by decide +kernel

theorem pin12 : poly.oneValue (matVec (commE dgO cX) vX)
    (poly.add
      (matVec (diagO ground.bpairOps (dgO.map BPair.ofNat)) (matVec cX vX))
      ((matVec cX (matVec (diagO ground.bpairOps
        (dgO.map BPair.ofNat)) vX)).map BPair.swap)) :=
  commE_read dgO cX vX 2 rfl ⟨rfl, rfl, trivial⟩ rfl rfl

theorem pin13 : poly.oneValue (matVec (commE dgO cX) vX)
    (poly.add
      (matVec (diagO ground.bpairOps (dgO.map BPair.ofNat)) (matVec cX vX))
      ((matVec cX (matVec (diagO ground.bpairOps
        (dgO.map BPair.ofNat)) vX)).map BPair.swap)) := by decide +kernel

end momentform
