import MassGap.Contactpair
import MassGap.Channeldiv
/-!
`thm:closing` — the contact pair's assembly: the contact pair reads
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

/-- The read at every occupied base and residue: the order count
at three, the excess's evaluation the harmonic number, and the
base's collection — the pair generic in the member's data
(`thm:closing` at the tex's own quantifier), the member
instantiations the check module's pins. -/
theorem read_all (c g : Nat) : read (c + 1) (g + 1) := by
  show (contactpair.pair (posOfSucc c) g).1 = 3
    ∧ ((contactpair.pair (posOfSucc c) g).2).oneValue
        (harmonic (posOfSucc g))
    ∧ channeldiv.baseRead (posOfSucc c)
  refine And.intro (channelreads.orderCount_three _)
    (And.intro ?_ (channeldiv.baseRead_all _))
  show (excess.evalOne g).oneValue (harmonic (posOfSucc g))
  rw [excess.evalOne_harmonic g]
  exact Pair.oneValue_refl _

/-- The read at occupancy witnesses alone: two occupied arguments
reach the universal read, the match's own split. -/
theorem read_pos : ∀ (b r : Nat), 0 < b → 0 < r → read b r
  | b + 1, r + 1, _, _ => read_all b r
  | 0, _, hb, _ => absurd hb (Nat.lt_irrefl 0)
  | _ + 1, 0, _, hr => absurd hr (Nat.lt_irrefl 0)

end closing
