import MassGap.SO
/-!
The check module for `thm:SO`: the batteries re-read the window
multiplicity by kernel `decide` — the ground bracket at
`diag(1, 3)` (the levels `[15:16] < [17:16]` at width `[1:8]`
below the pencil polynomial's separation, the lower pair positive
semidefinite and the upper count one: the multiplicity), a
two-root refusal at a wide bracket, and the character clause at
the theta window's swap: the plaquette exchange commutes with the
diagonal, is orthogonal, keeps the unit line's ground, and the
state's read is blind to the grading; a ragged or off-order
symmetry datum is unrepresentable at the carrier, the type the
guard. -/
set_option maxHeartbeats 4000000

open ground elim inertia SO

private def u : BPair := BPair.unit

private def hD : Mat := [[⟨2, 1⟩, u], [u, ⟨4, 1⟩]]

private def spLt (a b : BPair) : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.one a, .one b], 0, rfl⟩

/-! The multiplicity at the ground bracket: width `[1:8]` at the
separation read, the lower pair psd, the count one. -/

example : multRead hD (idMat 2) 15 16 17 16 1 8 1
    (spLt ⟨2, 1⟩ ⟨34, 1⟩) (spLt ⟨1, 2⟩ ⟨32, 1⟩) := by decide +kernel

/-! A wide bracket is refused at the separation's width clause:
the whole segment `[1:2, 7:2]` holds both roots, its width beyond
the polynomial's `δ`. -/

example : ¬ multRead hD (idMat 2) 1 2 7 2 3 1 2
    (spLt ⟨2, 1⟩ ⟨6, 1⟩) (spLt ⟨1, 6⟩ ⟨1, 2⟩) := by decide +kernel

/-! The character clause at the theta window's swap: the plaquette
exchange commutes with `diag(0, 12, 18, 12)`, is orthogonal, and
keeps the unit line's ground; the state's read is blind. -/

private def hTh : Mat :=
  [[u, u, u, u], [u, ⟨13, 1⟩, u, u], [u, u, ⟨19, 1⟩, u],
   [u, u, u, ⟨13, 1⟩]]

private def gSwap : Mat :=
  [[⟨2, 1⟩, u, u, u], [u, u, u, ⟨2, 1⟩], [u, u, ⟨2, 1⟩, u],
   [u, ⟨2, 1⟩, u, u]]

private def psi4 : List BPair := [⟨2, 1⟩, u, u, u]

example : symRead (⟨hTh, rfl⟩ : SqMat 4) (⟨gSwap, rfl⟩ : SqMat 4)
    ⟨psi4, rfl⟩ := by decide +kernel

example : (dotN psi4 (matVec (matMul (transposeM gSwap)
      (matMul hTh gSwap)) psi4)).oneValue
    (dotN psi4 (matVec hTh psi4)) := by decide +kernel
