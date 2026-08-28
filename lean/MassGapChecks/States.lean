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
concatenation's refusal, and the absent key at the sum's unit.  The
block swap's cells close the file: the three-block relabeling's
entries, its width, and its wiring read with the one-below
refusal. -/
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

/-! The wiring bridges: the width read against the enumeration,
both directions, the entries' bound, and the concatenation at the
shifted block — each decided beside its theorem route. -/

example : 0 < ground.countOf [2, 0, 1] (places.perms 3) := by
  decide +kernel
example : 0 < ground.countOf [2, 0, 1] (places.perms 3) :=
  permAt_member (by decide +kernel)
example : permAt [2, 0, 1] 3 :=
  member_permAt (by decide +kernel)
example : ground.countOf 5 [2, 0, 1] = 0 := by decide +kernel
example : (2 : Nat) < 3 :=
  permAt_entries (π := [2, 0, 1]) (m := 3)
    (by decide +kernel) 2 (by decide +kernel)
example : permAt ([1, 0] ++ shiftW 2 [0, 2, 1]) 5 := by
  decide +kernel
example : permAt ([1, 0] ++ shiftW 2 [0, 2, 1]) 5 :=
  permAt_concat (πa := [1, 0]) (πb := [0, 2, 1]) (la := 2)
    (lb := 3) (by decide +kernel) (by decide +kernel)


/-! The block swap at a three-block site: the head kept, the second
block read across the third and the third read back — the site
`n = 2`, `a = 3`, `b = 1` with the wiring read at each block and the
width refused one below. -/

example : swapW 2 3 1 = [0, 1, 5, 2, 3, 4] := by decide +kernel
example : (swapW 2 3 1).length = 2 + (1 + 3) := by decide +kernel
example : (swapW 2 3 1).length = 2 + (1 + 3) := length_swapW 2 3 1
example : (shiftW 4 [0, 2, 1]).length = [0, 2, 1].length :=
  length_shiftW 4 [0, 2, 1]

example : ground.getAt 0 (swapW 2 3 1) 1 = 1 := by decide +kernel
example : ground.getAt 0 (swapW 2 3 1) 1 = 1 :=
  getAt_swapW_low 2 3 1 1 (by decide +kernel)
example : ground.getAt 0 (swapW 2 3 1) (2 + 0) = 2 + (3 + 0) := by
  decide +kernel
example : ground.getAt 0 (swapW 2 3 1) (2 + 0) = 2 + (3 + 0) :=
  getAt_swapW_mid 2 3 1 0 (by decide +kernel)
example : ground.getAt 0 (swapW 2 3 1) (2 + (1 + 2)) = 2 + 2 := by
  decide +kernel
example : ground.getAt 0 (swapW 2 3 1) (2 + (1 + 2)) = 2 + 2 :=
  getAt_swapW_high 2 3 1 2 (by decide +kernel)

example : permAt (swapW 2 3 1) (2 + (3 + 1)) := by decide +kernel
example : permAt (swapW 2 3 1) (2 + (3 + 1)) := permAt_swapW 2 3 1
example : ¬ permAt (swapW 2 3 1) 5 := by decide +kernel
example : permAt (swapW 1 2 2) (1 + (2 + 2)) := permAt_swapW 1 2 2
