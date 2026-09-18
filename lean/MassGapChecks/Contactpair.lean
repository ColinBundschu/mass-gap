import MassGap.Contactpair
/-!
The check module for `def:contactpair`: the batteries re-read the
pair's two coordinates by kernel `decide` at the committed bases
and first residues — the channel's order count and the excess's
evaluation, the pair's data the two divisors' reads.
-/

namespace contactpair
set_option maxHeartbeats 4000000

open ground

theorem pin1 : (pair 1 0).1 = 3 := by decide +kernel
theorem pin2 : (pair 2 1).1 = 3 := by decide +kernel
theorem pin3 : ((pair 2 1).2).oneValue ⟨3, 2⟩ := by decide +kernel
theorem pin4 : ((pair 1 0).2).oneValue (Pair.ofPos Pos.one) := by decide +kernel

end contactpair
