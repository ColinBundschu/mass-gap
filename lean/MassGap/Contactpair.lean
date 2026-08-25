import MassGap.Walkresidue
import MassGap.Channelreads
/-!
`def:contactpair` — the contact pair, the two divisors' reads:
the first coordinate the channel's order count at the base
(`def:channelreads`), the second the ruler's excess over the walk
read at one, `A(1)` (`def:excess`), at the successor spelling
`r = g + 1`.
-/

namespace contactpair
open ground

/-- The contact pair at a base and a residue: the channel's order
count with the excess's evaluation at one. -/
def pair (c1 : Pos) (g : Nat) : Nat × Pair :=
  (channelreads.orderCount c1, excess.evalOne g)

end contactpair
