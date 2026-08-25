import MassGap.Bridge
/-!
The check module for `thm:bridge`: the count's identity routed at
committed residues, and the pair carrier's committed evaluations —
the `r = 2` value `6`, the pair `[144 : 24]` at one value with
`[6 : 1]`, with the neighboring residues' evaluations beside it.
-/
open ground

/-! The identity through the theorem at committed residues. -/

example : 1 * (1 + 2) * (2 * ((1 + 1) * (1 + 1)))
    = 2 * (1 + 1) * ((1 + 1) * (1 * (1 + 2))) := bridge.count 1
example : 2 * (2 + 2) * (2 * ((2 + 1) * (2 + 1)))
    = 2 * (2 + 1) * ((2 + 1) * (2 * (2 + 2))) := bridge.count 2
example : 3 * (3 + 2) * (2 * ((3 + 1) * (3 + 1)))
    = 2 * (3 + 1) * ((3 + 1) * (3 * (3 + 2))) := bridge.count 3

/-! The pair carrier's committed evaluations: the `r = 2` pair
`[d_adj C₂(adj) : d_f C₂(f)]` cleared is `[144 : 24]`, one value
with `[6 : 1]` — the evaluation `6` — and the `r = 1` pair
`[24 : 6]` reads `4`, the `r = 3` pair `[480 : 60]` reads `8`. -/

example : (Pair.mk (posOfSucc 143) (posOfSucc 23)).oneValue
    (Pair.ofPos (posOfSucc 5)) := by decide +kernel
example : (Pair.mk (posOfSucc 23) (posOfSucc 5)).oneValue
    (Pair.ofPos (posOfSucc 3)) := by decide +kernel
example : (Pair.mk (posOfSucc 479) (posOfSucc 59)).oneValue
    (Pair.ofPos (posOfSucc 7)) := by decide +kernel
