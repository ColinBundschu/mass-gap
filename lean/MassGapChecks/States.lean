import MassGap.States
/-!
The check module for `con:states`: the batteries re-read the
wiring carrier by kernel `decide` — the wiring read at the
four-place pairing with the repeated-value and off-length
refusals, the trace structure's cycles `con:places`' own reads at
their check module.  The presentation's product beside them: the concatenated site's blocked
wiring read back through the coefficient at its literal key, at the
unit coefficients and at a genuine pair product, the duplicate key's
collection, the product wiring's legality with the unshifted
concatenation's refusal, and the absent key at the sum's unit. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground poly states genericlift

example : permAt [1, 0, 3, 2] 4 := by decide +kernel
example : ¬ permAt [1, 1] 2 := by decide +kernel
example : ¬ permAt [0, 1] 3 := by decide +kernel

/-! The presentation's product: the second site's wiring shifted by
the first's length, the coefficients read at the literal keys.  The
pairs are the Casimir `[t(t+2) : 2(t+1)]` and the negation `[-1 : 1]`,
stated here rather than imported. -/

private def cfP : PPair :=
  ([BPair.unit, ⟨3, 1⟩, ⟨2, 1⟩], [⟨3, 1⟩, ⟨3, 1⟩])
private def negP : PPair := ([⟨1, 2⟩], [⟨2, 1⟩])

example : crossNull (coeffAtW (mulComb [([0, 1], pOne)] [([1, 0], pOne)])
    [0, 1, 3, 2]) pOne := by decide +kernel
example : crossNull (coeffAtW (mulComb [([0, 1], cfP)] [([1, 0], negP)])
    [0, 1, 3, 2])
    ([BPair.unit, ⟨1, 3⟩, ⟨1, 2⟩], [⟨3, 1⟩, ⟨3, 1⟩]) := by decide +kernel
example : crossNull (coeffAtW [([0, 1], cfP), ([0, 1], negP)] [0, 1])
    ([⟨1, 3⟩, BPair.unit, ⟨2, 1⟩], [⟨3, 1⟩, ⟨3, 1⟩]) := by decide +kernel
example : crossNull (coeffAtW (mulComb [([0, 1], pOne)] [([1, 0], pOne)])
    [0, 1, 2, 3]) pZero := by decide +kernel

example : permAt (getAt [] ((mulComb [([0, 1], pOne)]
    [([1, 0], pOne)]).map (fun e => e.1)) 0) 4 := by decide +kernel
example : ¬ permAt ([0, 1] ++ [1, 0]) 4 := by decide +kernel
