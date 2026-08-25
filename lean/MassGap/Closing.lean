import MassGap.Contactpair
import MassGap.Channeldiv
/-!
`thm:closing` — the constant's assembly: the contact pair reads
`(3, H_r)`, the channel's order count at three and the walk's pole
excess at the harmonic read, factor by factor, with the base
collecting at the orders' sum, `c₁^1 · c₁^2 = c₁^3`
(`thm:channeldiv`'s read at the member's base).  The read takes
the member's base and residue as naturals — the reads off the
tables, `row.supportCount` and `gentable.residue` — occupied
arguments at the successor rows and the unoccupied rows the
falsum, the pair's equality read componentwise: a count, one
cross-multiplication identity, and the base's collection.  The
member instantiations at the twelve committed tables are the
check module's pins.
-/

namespace closing
open ground

/-- The pair's equality read at a base and a residue, both
occupied: the order count at three, `A(1)` at the harmonic read
`H_r`, and the base collecting at the orders' sum, componentwise. -/
def read : Nat → Nat → Prop
  | c + 1, g + 1 =>
    (contactpair.pair (posOfSucc c) g).1 = 3
      ∧ ((contactpair.pair (posOfSucc c) g).2).oneValue
          (harmonic (posOfSucc g))
      ∧ channeldiv.baseRead (posOfSucc c)
  | 0, _ => False
  | _ + 1, 0 => False

instance : (c1 r : Nat) → Decidable (read c1 r)
  | _ + 1, _ + 1 => inferInstanceAs (Decidable (_ ∧ _))
  | 0, _ => inferInstanceAs (Decidable False)
  | _ + 1, 0 => inferInstanceAs (Decidable False)

end closing
