import MassGap.Channelreads
import MassGap.Chordmap
/-!
`thm:channeldiv` — the channel divisor's displayed reads at the
base: the chord at the mass point, the symbol `c₁ w = 1 + c₁²`
carried by the chord's naming `w = [1 + c₁² : c₁]`; the crossing
pair `⟨w² : 4⟩ = [⟨c₁² : 1⟩² : c₁²]`, `crossingRead`, of equal
members exactly at `c₁ = 1`; the mass weight's margin
`⟨1 : z*²⟩ = [⟨c₁² : 1⟩ : c₁²]` with its square the crossing
pair's `z*²`-multiple, `marginRead`, the read `[9:4]` at base two
the check module's pin; the base collecting at the orders' sum,
`c₁^1 · c₁^2 = c₁^3` over `def:channelreads`' order count; and the
lower crossing's level reading its two members at one value
exactly at base two, `crossLo_members` at the crossing's member
pair, the infrared contact — at base one the mass point sits at
the crossing, the crossing read's equal-members outcome with the
order count fixed.
The divisor's derivation — the boundary pivot recursion, the
truncations' error law and the deck involution's orbit — lands
with the decimation layer's consumers; `thm:chordmap` reads the
level joins (the bound-state join `c₁ y₊ + 1 = c₁ y₋`, the two
crossing joins and the band's width four), and the coherence
`chord_bound` reads this theorem's symbol as that theorem's chord
at the bound-state level.  The reads here are the theorem's
displayed identities, `def:channelreads`' objects.
-/

namespace channeldiv
open ground

/-- The chord at the mass point, the symbol's naming:
`w = [1 + c₁² : c₁]` at `c₁ w = 1 + c₁²`. -/
def chord (c1 : Pos) : Pair := ⟨Pos.one + c1 * c1, c1⟩

/-- The symbol's witness, the cross-multiplied read
`c₁ w = 1 + c₁²`. -/
def symbolRead (c1 : Pos) : Prop :=
  (Pair.mul (Pair.ofPos c1) (chord c1)).oneValue
    (Pair.ofPos (Pos.one + c1 * c1))

instance (c1 : Pos) : Decidable (symbolRead c1) :=
  inferInstanceAs (Decidable (_ = _))

/-- The crossing pair `⟨w² : 4⟩` at the chord, the composite
`[⟨(1 + c₁²)² : 4 c₁²⟩ : c₁²]`. -/
def crossPair (c1 : Pos) : CPair :=
  ⟨⟨(Pos.one + c1 * c1) * (Pos.one + c1 * c1), (4 : Pos) * (c1 * c1)⟩,
   c1 * c1⟩

/-- The crossing read `⟨w² : 4⟩ = [⟨c₁² : 1⟩² : c₁²]`, one
cross-multiplied identity, equal members exactly at `c₁ = 1`. -/
def crossingRead (c1 : Pos) : Prop :=
  (crossPair c1).oneValue
    ⟨(⟨c1 * c1, Pos.one⟩ : BPair) * ⟨c1 * c1, Pos.one⟩, c1 * c1⟩

instance (c1 : Pos) : Decidable (crossingRead c1) :=
  inferInstanceAs (Decidable (_ = _))

/-- The mass weight's margin `⟨1 : z*²⟩`, the composite
`[⟨c₁² : 1⟩ : c₁²]` at the mass point's square. -/
def margin (c1 : Pos) : CPair := ⟨⟨c1 * c1, Pos.one⟩, c1 * c1⟩

/-- The margin's square is the crossing pair's `z*²`-multiple. -/
def marginRead (c1 : Pos) : Prop :=
  (CPair.mul (margin c1) (margin c1)).oneValue
    (CPair.mul (crossPair c1) (CPair.ofPair ⟨Pos.one, c1 * c1⟩ Pos.one))

instance (c1 : Pos) : Decidable (marginRead c1) :=
  inferInstanceAs (Decidable (_ = _))

/-- The mass weight's sum with its complement: the pair
`[⟨c₁² : 1⟩ : c₁²]` — the margin's own display — at the
complement `[1 : c₁²]`, the two summing to one. -/
def weightSumRead (c1 : Pos) : Prop :=
  (margin c1 + CPair.ofPair ⟨Pos.one, c1 * c1⟩ Pos.one).oneValue
    (CPair.ofPair (Pair.ofPos Pos.one) Pos.one)

instance (c1 : Pos) : Decidable (weightSumRead c1) :=
  inferInstanceAs (Decidable (_ = _))

/-- The base collects at the orders' sum:
`c₁^1 · c₁^2 = c₁^3` over the order count. -/
def baseRead (c1 : Pos) : Prop :=
  c1 * (c1 * c1) = Pos.pow c1 (channelreads.orderCount c1)

instance (c1 : Pos) : Decidable (baseRead c1) :=
  inferInstanceAs (Decidable (_ = _))

/-- The base collects at every base: `c₁ · c₁² = c₁³` at the order
count's three (`channelreads.orderCount_three`), the display's own
read at the defining fold. -/
theorem baseRead_all (c1 : Pos) : baseRead c1 := by
  show c1 * (c1 * c1) = Pos.pow c1 (channelreads.orderCount c1)
  rw [channelreads.orderCount_three c1]
  show c1 * (c1 * c1) = c1 * (c1 * (c1 * Pos.one))
  rw [mul_one]

/-- The lower crossing's level reads its two members at one value
exactly at base two: at a level on the lower crossing
(`chordmap.crossLo`), the members' one-value read holds exactly at
`c₁ = 2` — the crossing binder is load-bearing, its refusal the
check module's. -/
theorem crossLo_members (c1 : Pos) (yp ym : Pair)
    (h : chordmap.crossLo c1 yp ym) :
    yp.oneValue ym ↔ c1 = 2 := by
  constructor
  · intro hm
    have hcong : (yp + Pair.ofPos 2).oneValue (ym + Pair.ofPos 2) :=
      Pair.add_congr hm (Pair.oneValue_refl (Pair.ofPos 2))
    have h3 : (Pair.ofPos c1 + ym).oneValue (ym + Pair.ofPos 2) :=
      Pair.oneValue_trans (Pair.oneValue_symm h) hcong
    rw [Pair.add_comm (Pair.ofPos c1) ym] at h3
    rw [Pair.add_comm ym (Pair.ofPos c1),
      Pair.add_comm ym (Pair.ofPos 2)] at h3
    have h4 : c1 * Pos.one = (2 : Pos) * Pos.one := Pair.add_cancel h3
    rw [mul_one, mul_one] at h4
    exact h4
  · intro hc
    subst hc
    have h' : (yp + Pair.ofPos 2).oneValue (Pair.ofPos 2 + ym) := h
    rw [Pair.add_comm (Pair.ofPos 2) ym] at h'
    exact Pair.add_cancel h'

/-- The coherence with `thm:chordmap`: at the bound-state join the
mass point's symbol is the chord joining the level's members, the
identity cleared against the base — the join binder is
load-bearing, its refusal the check module's. -/
theorem chord_bound (c1 : Pos) (yp ym : Pair)
    (h : chordmap.boundJoin c1 yp ym) :
    chordmap.chordJoin c1 yp ym (chord c1) := by
  refine Pair.mul_cancel (y := Pair.ofPos c1) ?_
  have hs : (Pair.ofPos c1 * chord c1).oneValue
      (Pair.ofPos Pos.one + Pair.ofPos c1 * Pair.ofPos c1) := by
    show c1 * (Pos.one + c1 * c1) * (Pos.one * (Pos.one * Pos.one))
        = (Pos.one * (Pos.one * Pos.one) + c1 * c1 * Pos.one) * (Pos.one * c1)
    rw [one_mul, one_mul, one_mul, mul_one, mul_one,
      ground.mul_comm c1 (Pos.one + c1 * c1)]
  refine Pair.oneValue_trans
    (Pair.left_distrib (Pair.ofPos c1) (chord c1) yp) ?_
  refine Pair.oneValue_trans (Pair.add_congr hs
    (Pair.oneValue_refl (Pair.ofPos c1 * yp))) ?_
  refine Pair.oneValue_symm (Pair.oneValue_trans
    (Pair.left_distrib (Pair.ofPos c1) (Pair.ofPos c1) ym) ?_)
  rw [Pair.add_comm (Pair.ofPos Pos.one)
      (Pair.ofPos c1 * Pair.ofPos c1),
    Pair.add_assoc (Pair.ofPos c1 * Pair.ofPos c1) (Pair.ofPos Pos.one)
      (Pair.ofPos c1 * yp),
    Pair.add_comm (Pair.ofPos Pos.one) (Pair.ofPos c1 * yp)]
  exact Pair.oneValue_symm (Pair.add_congr
    (Pair.oneValue_refl (Pair.ofPos c1 * Pair.ofPos c1)) h)

end channeldiv
