import MassGap.Poly
/-!
`def:channelreads` — the channel's derived objects at a base `c₁`
as ground reads: the boundary entry `G₀` at its renewal witness
`G₀ = z + c₁ z G₀`, the recursion's series `Σ_k c₁^k z^{k+1}` at
the polynomial carrier (`def:poly`, the coefficient list over the
balance pairs with the base on the positive carrier), the witness
read as its two coefficient lists at one depth offset,
componentwise over the whole window; the mass point `z*` at
`c₁ z* = 1`, `massRead` its witness; the ι-symmetrized weight's
factor list `(⟨1 : c₁z⟩, ⟨z : c₁⟩)` over the second member as
coefficient lists, each reading the base at degree one, with the
conjugation read `z · (⟨1 : c₁z⟩ ∘ ι) = ⟨z : c₁⟩` the coefficient
reversal; the pole order, the clearing factor's multiplicity gap
at the mass point, one, its witness the factor's root there with
the factor's top coefficient off equal members; and the order
count, the pole order added to the factor list's count.
-/

namespace channelreads
open ground poly

/-- The boundary entry's coefficient list to depth `d + 1`, the
renewal witness's series `Σ_k c₁^k z^{k+1}` at the polynomial
carrier: key `0` at the sum's unit, degree `k + 1` at `c₁^k`. -/
def g0List (c1 : Pos) (d : Nat) : Poly :=
  shiftUp 1 ((List.range (d + 1)).map (fun k => BPair.ofPos (Pos.powC c1 k)))

/-- The renewal witness `G₀ = z + c₁ z G₀`: the witness's two
coefficient lists read componentwise over the whole window at one
depth offset, the display's own spelling at the carrier. -/
def renewalRead (c1 : Pos) (d : Nat) : Prop :=
  oneValue (g0List c1 (d + 1))
    (add (mono 1) (scaleP (BPair.ofPos c1) (shiftUp 1 (g0List c1 d))))

instance (c1 : Pos) (d : Nat) : Decidable (renewalRead c1 d) :=
  decOneValue _ _

/-- The mass point `z*` at `c₁ z* = 1`, the clearing factor's
root, its witness the cross-multiplied read. -/
def massRead (c1 : Pos) : Prop :=
  (Pair.mul (Pair.ofPos c1) ⟨Pos.one, c1⟩).oneValue (Pair.ofPos Pos.one)

instance (c1 : Pos) : Decidable (massRead c1) :=
  inferInstanceAs (Decidable (_ = _))

/-- The ι-symmetrized weight's factor list over the second member:
`⟨1 : c₁z⟩` and `⟨z : c₁⟩` as coefficient lists over the balance
pairs, each reading the base at degree one. -/
def factors (c1 : Pos) : List Poly :=
  [[BPair.ofPos Pos.one, (BPair.ofPos c1).swap],
   [(BPair.ofPos c1).swap, BPair.ofPos Pos.one]]

/-- The pole order at the mass point: the clearing factor's root
multiplicity there against the series member's, one. -/
def poleOrder : Nat := 1

/-- The pole order's witness, the multiplicity gap's data: the
clearing factor's root at the mass point (`massRead`) with the
stated factor's top coefficient off equal members (the
multiplicity exactly one), the series member's read at the mass
point off the sum's unit by the pair's own shape. -/
def poleOrderRead (c1 : Pos) : Prop :=
  massRead c1 ∧ (top (getAt [] (factors c1) 0)).offUnit

instance (c1 : Pos) : Decidable (poleOrderRead c1) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The conjugation read: the second factor is the first's
coefficient reversal, the display `z · (⟨1 : c₁z⟩ ∘ ι) = ⟨z : c₁⟩`
at degree one. -/
def conjRead (c1 : Pos) : Prop :=
  oneValue ((getAt [] (factors c1) 0).reverse) (getAt [] (factors c1) 1)

instance (c1 : Pos) : Decidable (conjRead c1) := decOneValue _ _

/-- The order count: the pole order added to the factor list's
count. -/
def orderCount (c1 : Pos) : Nat := poleOrder + (factors c1).length

/-- The order count reads three at every base: the pole order one
with the factor list's two members, each independent of the base
(`thm:channeldiv`'s orders). -/
theorem orderCount_three (c1 : Pos) : orderCount c1 = 3 := rfl

end channelreads
