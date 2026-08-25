import MassGap.Contactpair
/-!
The check module for `def:contactpair`: the batteries re-read the
pair's two coordinates by kernel `decide` at the committed bases
and first residues — the channel's order count and the excess's
evaluation, the pair's data the two divisors' reads.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground contactpair

example : (pair 1 0).1 = 3 := by decide +kernel
example : (pair 2 1).1 = 3 := by decide +kernel
example : ((pair 2 1).2).oneValue ⟨3, 2⟩ := by decide +kernel
example : ((pair 1 0).2).oneValue (Pair.ofPos Pos.one) := by decide +kernel
