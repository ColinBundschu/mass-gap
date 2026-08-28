import MassGap.Detector
import MassGap.Momentform
/-!
The check module for `thm:detector`: the batteries re-read the
detector's identity instances by kernel `decide` — the factor read
at points on either side of the level, the two neutral points (the
kernel point and the edge at equal members), the side
classification (weight below the level on the lower side, beyond
on the upper), the weight fold with its pass and failure reads,
and the moments' spectral coherence: the cleared `μ₂ - γ μ₁` at a
diagonal instance is the detector fold at the probe's component
weights, `lem:split`'s weights the display's. -/
set_option maxHeartbeats 4000000

open ground elim detector

private def u : BPair := BPair.unit

/-! The factor read at points below, at, and beyond the level. -/

example : factorRead ⟨2, 1⟩ 1 2 1 := by decide +kernel
example : factorRead ⟨4, 1⟩ 1 2 1 := by decide +kernel
example : factorRead ⟨4, 1⟩ 2 3 2 := by decide +kernel
example : factorRead ⟨1, 3⟩ 1 2 1 := by decide +kernel

/-! The two neutral points: the kernel point and the edge read the
datum at equal members. -/

example : (datum u 1 2 1).oneValue u := by decide +kernel
example : (datum ⟨4, 1⟩ 2 3 2).oneValue u := by decide +kernel

/-! The side classification: weight below the level drives the
lower side, weight beyond the upper. -/

example : datum ⟨2, 1⟩ 1 2 1 < u := by decide +kernel
example : u < datum ⟨4, 1⟩ 1 2 1 := by decide +kernel

/-! The weight fold: the pass read at weights riding the upper
side's excess, and the failure at a level beyond the top weight. -/

example : passRead [(1, ⟨2, 1⟩), (1, ⟨4, 1⟩)] 1 2 1 := by decide +kernel
example : ¬ passRead [(1, ⟨2, 1⟩), (1, ⟨4, 1⟩)] 1 3 1 := by decide +kernel

/-! The moments' spectral coherence at the diagonal instance
`diag(1, 3)` with the probe `(1, 1)`: the cleared `μ₂ - γ μ₁` is
the detector fold at unit component weights. -/

private def hD : SqMat 2 := ⟨[[⟨2, 1⟩, u], [u, ⟨4, 1⟩]], rfl⟩

private def v11 : Vec 2 := ⟨[⟨2, 1⟩, ⟨2, 1⟩], rfl⟩

example : ((momentform.mu2 hD v11).scale 1
    + ((momentform.mu1 hD v11).scale 2).swap).oneValue
    (detFold [(1, ⟨2, 1⟩), (1, ⟨4, 1⟩)] 1 2 1) := by decide +kernel
