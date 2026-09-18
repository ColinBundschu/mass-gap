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

namespace states
set_option maxHeartbeats 4000000

open ground poly genericlift

theorem pin1 : permAt [1, 0, 3, 2] 4 := by decide +kernel
theorem pin2 : ¬ permAt [1, 1] 2 := by decide +kernel
theorem pin3 : ¬ permAt [0, 1] 3 := by decide +kernel

/-! The presentation's product: the second site's wiring shifted by
the first's length, the coefficients read at the literal keys.  The
pairs are the Casimir `[t(t+2) : 2(t+1)]` and the negation `[-1 : 1]`,
stated here rather than imported. -/

private def cfP : PPair :=
  ([BPair.unit, ⟨3, 1⟩, ⟨2, 1⟩], [⟨3, 1⟩, ⟨3, 1⟩])
private def negP : PPair := ([⟨1, 2⟩], [⟨2, 1⟩])

theorem pin4 : crossNull (coeffAtW (mulComb [([0, 1], pOne)] [([1, 0], pOne)])
    [0, 1, 3, 2]) pOne := by decide +kernel
theorem pin5 : crossNull (coeffAtW (mulComb [([0, 1], cfP)] [([1, 0], negP)])
    [0, 1, 3, 2])
    ([BPair.unit, ⟨1, 3⟩, ⟨1, 2⟩], [⟨3, 1⟩, ⟨3, 1⟩]) := by decide +kernel
theorem pin6 : crossNull (coeffAtW [([0, 1], cfP), ([0, 1], negP)] [0, 1])
    ([⟨1, 3⟩, BPair.unit, ⟨2, 1⟩], [⟨3, 1⟩, ⟨3, 1⟩]) := by decide +kernel
theorem pin7 : crossNull (coeffAtW (mulComb [([0, 1], pOne)] [([1, 0], pOne)])
    [0, 1, 2, 3]) pZero := by decide +kernel

theorem pin8 : permAt (getAt [] ((mulComb [([0, 1], pOne)]
    [([1, 0], pOne)]).map (fun e => e.1)) 0) 4 := by decide +kernel
theorem pin9 : ¬ permAt ([0, 1] ++ [1, 0]) 4 := by decide +kernel

/-! The wiring bridges: the width read against the enumeration,
both directions, the entries' bound, and the concatenation at the
shifted block — each decided beside its theorem route. -/

theorem pin10 : 0 < ground.countOf [2, 0, 1] (places.perms 3) := by
  decide +kernel
theorem pin11 : 0 < ground.countOf [2, 0, 1] (places.perms 3) :=
  permAt_member (by decide +kernel)
theorem pin12 : permAt [2, 0, 1] 3 :=
  member_permAt (by decide +kernel)
theorem pin13 : ground.countOf 5 [2, 0, 1] = 0 := by decide +kernel
theorem pin14 : (2 : Nat) < 3 :=
  permAt_entries (π := [2, 0, 1]) (m := 3)
    (by decide +kernel) 2 (by decide +kernel)
theorem pin15 : permAt ([1, 0] ++ shiftW 2 [0, 2, 1]) 5 := by
  decide +kernel
theorem pin16 : permAt ([1, 0] ++ shiftW 2 [0, 2, 1]) 5 :=
  permAt_concat (πa := [1, 0]) (πb := [0, 2, 1]) (la := 2)
    (lb := 3) (by decide +kernel) (by decide +kernel)


/-! The block swap at a three-block site: the head kept, the second
block read across the third and the third read back — the site
`n = 2`, `a = 3`, `b = 1` with the wiring read at each block and the
width refused one below. -/

theorem pin17 : swapW 2 3 1 = [0, 1, 5, 2, 3, 4] := by decide +kernel
theorem pin18 : (swapW 2 3 1).length = 2 + (1 + 3) := by decide +kernel
theorem pin19 : (swapW 2 3 1).length = 2 + (1 + 3) := length_swapW 2 3 1
theorem pin20 : (shiftW 4 [0, 2, 1]).length = [0, 2, 1].length :=
  length_shiftW 4 [0, 2, 1]

theorem pin21 : ground.getAt 0 (swapW 2 3 1) 1 = 1 := by decide +kernel
theorem pin22 : ground.getAt 0 (swapW 2 3 1) 1 = 1 :=
  getAt_swapW_low 2 3 1 1 (by decide +kernel)
theorem pin23 : ground.getAt 0 (swapW 2 3 1) (2 + 0) = 2 + (3 + 0) := by
  decide +kernel
theorem pin24 : ground.getAt 0 (swapW 2 3 1) (2 + 0) = 2 + (3 + 0) :=
  getAt_swapW_mid 2 3 1 0 (by decide +kernel)
theorem pin25 : ground.getAt 0 (swapW 2 3 1) (2 + (1 + 2)) = 2 + 2 := by
  decide +kernel
theorem pin26 : ground.getAt 0 (swapW 2 3 1) (2 + (1 + 2)) = 2 + 2 :=
  getAt_swapW_high 2 3 1 2 (by decide +kernel)

theorem pin27 : permAt (swapW 2 3 1) (2 + (3 + 1)) := by decide +kernel
theorem pin28 : permAt (swapW 2 3 1) (2 + (3 + 1)) := permAt_swapW 2 3 1
theorem pin29 : ¬ permAt (swapW 2 3 1) 5 := by decide +kernel
theorem pin30 : permAt (swapW 1 2 2) (1 + (2 + 2)) := permAt_swapW 1 2 2

/-! The wiring surgery of the generator insertions (`con:states`'
evaluation contraction and `prop:lap`'s joint insertion).  A chain
`[3, 4]` placed at factor `1`'s row in the two-cycle `[1, 0]` padded
to five positions reads `[1, 4, 2, 0, 3]`, the cycle `M_0 c_3 c_4
M_1`, and after factor `1`'s column reads `[4, 0, 2, 1, 3]`, the
cycle `M_1 c_3 c_4 M_0`; the last position of `[2, 0, 1]` contracts
to the two-cycle `[1, 0]` at no loop, and the self-wired last
position of `[1, 0, 2]` withdraws at one loop.  A letter wired to
itself withdraws: at `[3, 0, 2, 1]`, the first letter self-wired and
the second in the two-cycle, the transposition member reads
`[1, 0]` at no loop and the identity member `[1, 0]` at one loop,
the count against the count's cofactor.  The evaluation contraction
at the two-cycle `tr(U U†)` withdraws both factors at one loop, at
`tr(U0 U1 U1† U0†)` the outer pair withdraws to the inner two-cycle,
and every factor contracts to the vacant list at one loop; a
residual `(U1, U1†)` at the two-cycle keys the site's positions
`[1, 2]` with the wiring in rank coordinates, the relabeling of
`(U1†, U0)` reads `[2, 0]`, and the unit at the word `U0` joins the
two-cycle at the word's own loop, `[1, 0, 3, 2]` at `[1 : d_f]`. -/

theorem pin31 : chainAtRow 1 [3, 4] (padW 3 [1, 0]) = [1, 4, 2, 0, 3] := by decide +kernel
theorem pin32 : chainAtCol 1 [3, 4] (padW 3 [1, 0]) = [4, 0, 2, 1, 3] := by decide +kernel
theorem pin33 : contractLast [2, 0, 1] = ([1, 0], 0) := by decide +kernel
theorem pin34 : contractLast [1, 0, 2] = ([1, 0], 1) := by decide +kernel
theorem pin35 : fierzT [3, 0, 2, 1] = ([1, 0], 0) := by decide +kernel
theorem pin36 : fierzI [3, 0, 2, 1] = ([1, 0], 1) := by decide +kernel
theorem pin37 : evalStep [(0, false), (0, true)] [1, 0] = ([], [], 1) := by decide +kernel
theorem pin38 : evalStep [(0, false), (1, false), (1, true), (0, true)] [3, 0, 1, 2]
    = ([(1, false), (1, true)], [1, 0], 0) := by decide +kernel
theorem pin39 : padState [(0, false), (0, true)] [(0, false)] [([1, 0], poly.pOne)]
    = [([1, 0, 3, 2], poly.pMul poly.pOne invDfP)] := by decide +kernel
theorem pin40 : contractAll [(0, false), (1, false), (1, true), (0, true)] [3, 0, 1, 2]
    = ([], [], 1) := by decide +kernel
theorem pin41 : residualKey [(0, false), (1, false), (1, true), (0, true)]
    [(1, false), (1, true)] [1, 0] = ([1, 2], [1, 0]) := by decide +kernel
theorem pin42 : relabelTo [(0, false), (1, false), (1, true), (0, true)]
    [(1, true), (0, false)] = [2, 0] := by decide +kernel

end states
