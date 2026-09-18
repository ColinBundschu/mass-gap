import MassGap.Poly
import MassGap.Deck
/-!
The check module for `def:poly`: the batteries re-read the
polynomial calculus's identity instances by kernel `decide` — the
product's
unit at its two consumptions, the
componentwise sum, the convolution, the Horner read, the
successor-weighted derivative with its Leibniz rule at an instance,
decided and through the theorem, the division
at a monic with its naming identity, the linear factor's remainder
as the Horner read, the root and multiplicity reads (a root's
multiplicity the count of iterated divisions), the product's top at
the summed key with the product's carrier and the integral read,
the roots of a product and of a power, and the remainder
lists' product, and the iterated carrier's reads — the sum, the
convolution, and the outer evaluation at a composite polynomial
point, the band-root substitution's identity at the cleared read
with a forged point refusing.  Integers
enter as one-member balance data, `n` at `⟨n+1 : 1⟩` and its
balance partner at the swap.  The monic linear factor's Horner read
at a value against the root's balance partner and the Horner read
collected to the monomial fold at `5 + 2z + z³` follow,
each decided and through its theorem.  The variable's clearing at
`z² - 2` and the power two follows: the cleared list's
Horner read against the cleared evaluation at the point four, the
derivative of the cleared list against the derivative's clearing
one power down, and the key count kept, each decided and through
its theorem.  The shared-factor withdrawal closes the module: at the occupied
factor `z + 2` the cofactor `z + 1` in two spellings withdraws,
decided and through the theorem, with an off cofactor refused and
the occupancy binder load-bearing at the vacant factor.  The
clearing's ring reads sit before it, at
`z² - 2` against `z + 5`: the sum componentwise at the one stated
power, the memberwise swap entrywise, and the convolution at the
joined power with each factor within its stated power, at the
clearings two and three, each decided and through its theorem, with
the convolution's degree binder refused one power short of the
first factor's own.
-/

namespace poly

open ground

/-! The product's unit at its consumption: the convolution reads a
polynomial off, and the Horner read is the scalar one. -/

theorem pin1 : oneValue (mul one [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩])
    [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩] := by decide +kernel

theorem pin2 : BPair.oneValue (eval one ⟨6, 1⟩) (BPair.ofPos .one) := by
  decide +kernel

/-! The sum and the convolution. -/

theorem pin3 : oneValue (add [⟨2, 1⟩, ⟨3, 1⟩] [⟨1, 2⟩]) [⟨1, 1⟩, ⟨3, 1⟩] := by
  decide +kernel

theorem pin4 : oneValue (mul [⟨2, 1⟩, ⟨2, 1⟩] [⟨2, 1⟩, ⟨1, 2⟩])
    [⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩] := by decide +kernel

/-! The Horner read: `P = 5 + 2z + z^3` at `z = 2` reads `17`. -/

theorem pin5 : BPair.oneValue
    (eval [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩] ⟨3, 1⟩) ⟨18, 1⟩ := by decide +kernel

/-! The derivative and its Leibniz rule. -/

theorem pin6 : oneValue (deriv [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩])
    [⟨3, 1⟩, ⟨1, 1⟩, ⟨4, 1⟩] := by decide +kernel

theorem pin7 : oneValue (deriv (mul [⟨2, 1⟩, ⟨3, 1⟩] [⟨1, 2⟩, ⟨2, 1⟩, ⟨4, 1⟩]))
    (add (mul (deriv [⟨2, 1⟩, ⟨3, 1⟩]) [⟨1, 2⟩, ⟨2, 1⟩, ⟨4, 1⟩])
      (mul [⟨2, 1⟩, ⟨3, 1⟩] (deriv [⟨1, 2⟩, ⟨2, 1⟩, ⟨4, 1⟩]))) := by
  decide +kernel
theorem pin8 : oneValue (deriv (mul [⟨2, 1⟩, ⟨3, 1⟩] [⟨1, 2⟩, ⟨2, 1⟩, ⟨4, 1⟩]))
    (add (mul (deriv [⟨2, 1⟩, ⟨3, 1⟩]) [⟨1, 2⟩, ⟨2, 1⟩, ⟨4, 1⟩])
      (mul [⟨2, 1⟩, ⟨3, 1⟩] (deriv [⟨1, 2⟩, ⟨2, 1⟩, ⟨4, 1⟩]))) :=
  deriv_mul _ _

/-! The division at a monic: `z^3 + 2z + 5 = (z^2 + 1) z + (z + 5)`,
the quotient, the remainder and the naming identity. -/

theorem pin9 : divRead [⟨2, 1⟩, ⟨1, 1⟩] [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩] := by
  decide +kernel

theorem pin10 : oneValue
    (div [⟨2, 1⟩, ⟨1, 1⟩] [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩]).1
    [⟨1, 1⟩, ⟨2, 1⟩] := by decide +kernel

theorem pin11 : oneValue
    (div [⟨2, 1⟩, ⟨1, 1⟩] [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩]).2
    [⟨6, 1⟩, ⟨2, 1⟩] := by decide +kernel

/-! The descent's pair is one value at every solution: a padded
quotient and a shifted remainder representative read the same pair
(`div_unique`), and the below-top dividend reads the vacant
quotient. -/

theorem pin12 : oneValue [⟨1, 1⟩, ⟨2, 1⟩, ⟨4, 4⟩]
      (div [⟨2, 1⟩, ⟨1, 1⟩] [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩]).1
    ∧ oneValue [⟨8, 3⟩, ⟨3, 2⟩]
      (div [⟨2, 1⟩, ⟨1, 1⟩] [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩]).2 :=
  div_unique [⟨2, 1⟩, ⟨1, 1⟩] [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩]
    [⟨1, 1⟩, ⟨2, 1⟩, ⟨4, 4⟩] [⟨8, 3⟩, ⟨3, 2⟩] rfl (by decide +kernel)

theorem pin13 : oneValue [] (div [⟨2, 1⟩, ⟨1, 1⟩] [⟨4, 1⟩]).1
    ∧ oneValue [⟨4, 1⟩, ⟨1, 1⟩] (div [⟨2, 1⟩, ⟨1, 1⟩] [⟨4, 1⟩]).2 :=
  div_unique [⟨2, 1⟩, ⟨1, 1⟩] [⟨4, 1⟩] [] [⟨4, 1⟩, ⟨1, 1⟩] rfl (by decide +kernel)

/-- At the linear factor `z - 2` the remainder is the Horner read at
`2`: `P(2) = 17`. -/
theorem pin14 : oneValue
    (div [⟨1, 3⟩] [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩]).2 [⟨18, 1⟩] := by
  decide +kernel

/-! The linear divisor's remainder is the Horner read at that
divisor's own root (`div_linear_eval`), at two benches: the deck
symbol `P_5` against `⟨x : 3⟩`, whose root is the balance partner
of three, and the degree-two list `5z² + 2z + 7` against
`⟨x : 1̌⟩`, whose root is one.  Each bench sits twice, the kernel's
own read beside the general theorem's. -/

theorem pin15 : oneValue (div [BPair.ofNat 3] (deck.pSum 2)).2
    [eval (deck.pSum 2) (BPair.ofNat 3).swap] := by decide +kernel

theorem pin16 : oneValue (div [BPair.ofNat 3] (deck.pSum 2)).2
    [eval (deck.pSum 2) (BPair.ofNat 3).swap] := by
  exact div_linear_eval (BPair.ofNat 3) (deck.pSum 2)

theorem pin17 : oneValue
    (div [(BPair.ofNat 1).swap]
      [BPair.ofNat 7, BPair.ofNat 2, BPair.ofNat 5]).2
    [eval [BPair.ofNat 7, BPair.ofNat 2, BPair.ofNat 5]
      (BPair.ofNat 1)] := by decide +kernel

theorem pin18 : oneValue
    (div [(BPair.ofNat 1).swap]
      [BPair.ofNat 7, BPair.ofNat 2, BPair.ofNat 5]).2
    [eval [BPair.ofNat 7, BPair.ofNat 2, BPair.ofNat 5]
      (BPair.ofNat 1)] := by
  exact div_linear_eval ((BPair.ofNat 1).swap)
    [BPair.ofNat 7, BPair.ofNat 2, BPair.ofNat 5]

/-! The remainder lists at `z^2 + 1`: `z · z` reads the balance
partner of one. -/

theorem pin19 : oneValue (remMul [⟨2, 1⟩, ⟨1, 1⟩] [⟨1, 1⟩, ⟨2, 1⟩]
    [⟨1, 1⟩, ⟨2, 1⟩]) [⟨1, 2⟩, ⟨1, 1⟩] := by decide +kernel

/-! The division at the edges: the dividend below the top, and the
constant divisor. -/

theorem pin20 : divRead [⟨2, 1⟩, ⟨1, 1⟩] [⟨4, 1⟩] := by decide +kernel
theorem pin21 : divRead [] [⟨6, 1⟩, ⟨3, 1⟩] := by decide +kernel

/-! The root and multiplicity reads at `(z-2)^2 (z-3)`, and the
linear factor's Horner remainder. -/

theorem pin22 : isRoot [⟨1, 13⟩, ⟨17, 1⟩, ⟨1, 8⟩, ⟨2, 1⟩] ⟨3, 1⟩ := by decide +kernel
theorem pin23 : ¬ isRoot [⟨1, 13⟩, ⟨17, 1⟩, ⟨1, 8⟩, ⟨2, 1⟩] ⟨2, 1⟩ := by decide +kernel
theorem pin24 : multAt [⟨1, 3⟩] [⟨1, 13⟩, ⟨17, 1⟩, ⟨1, 8⟩, ⟨2, 1⟩] = 2 := by decide +kernel
theorem pin25 : multAt [⟨1, 4⟩] [⟨1, 13⟩, ⟨17, 1⟩, ⟨1, 8⟩, ⟨2, 1⟩] = 1 := by decide +kernel
theorem pin26 : multAt [⟨1, 2⟩] [⟨1, 13⟩, ⟨17, 1⟩, ⟨1, 8⟩, ⟨2, 1⟩] = 0 := by decide +kernel
theorem pin27 : hornerRead [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩] ⟨3, 1⟩ := by decide +kernel

/-! The product's top tier and the root reads, at the two quadratics
`P = z² + 3z + 2` and `Q = 2z² − z + 1`, whose product is
`2z⁴ + 5z³ + 2z² + z + 2`: the top reads the tops' product `1 · 2`
and the product's carrier five keys against the factors' three and
three, each decided and through the theorem; the top read holds at
every pair, the unit-tail top `[⟨2 : 1⟩, ⟨1 : 1⟩]` against `Q`
pinned beside it, and the carrier read's occupancy binders refuse at
the vacant factor, whose product is vacant against the other
factor's carrier.  The integral read: the product of the two
quadratics sits off the unit tail, and the product against the
unit-tailed `[⟨1 : 1⟩, ⟨1 : 1⟩]` reads the unit tail at that
factor.  The roots at the linear factors `z − 1` and `z − 2`: the
product's root one, the off-root three refused, and the third
power's root one with the off-root two refused. -/

theorem pin28 : oneValue (mul [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩])
    [⟨3, 1⟩, ⟨2, 1⟩, ⟨3, 1⟩, ⟨6, 1⟩, ⟨3, 1⟩] := by decide +kernel

theorem pin29 : BPair.oneValue
    (top (mul [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩]))
    (top [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] * top [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩]) := by
  decide +kernel
theorem pin30 : BPair.oneValue
    (top (mul [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩]))
    (top [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] * top [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩]) :=
  top_mul [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩]

theorem pin31 : (mul [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩]).length + 1
    = ([⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] : Poly).length
      + ([⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩] : Poly).length := by decide +kernel
theorem pin32 : (mul [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩]).length + 1
    = ([⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] : Poly).length
      + ([⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩] : Poly).length :=
  length_mul [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩]
    (by decide +kernel) (by decide +kernel)

theorem pin33 : BPair.oneValue
    (top (mul [⟨2, 1⟩, ⟨1, 1⟩] [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩]))
    (top [⟨2, 1⟩, ⟨1, 1⟩] * top [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩]) := by decide +kernel
theorem pin34 : ¬ ((mul [] [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩]).length + 1
    = ([] : Poly).length + ([⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩] : Poly).length) := by
  decide +kernel

theorem pin35 : ¬ unitTail
    (mul [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩]) := by decide +kernel
theorem pin36 : unitTail (mul [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] [⟨1, 1⟩, ⟨1, 1⟩]) := by decide +kernel
theorem pin37 : unitTail ([⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] : Poly)
    ∨ unitTail ([⟨1, 1⟩, ⟨1, 1⟩] : Poly) :=
  unitTail_mul_of (by decide +kernel)
theorem pin38 : unitTail (mul [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] [⟨1, 1⟩, ⟨1, 1⟩]) :=
  of_unitTail_mul (Or.inr (by decide +kernel))

theorem pin39 : isRoot (mul [⟨1, 2⟩, ⟨2, 1⟩] [⟨1, 3⟩, ⟨2, 1⟩]) ⟨2, 1⟩ := by decide +kernel
theorem pin40 : isRoot (mul [⟨1, 2⟩, ⟨2, 1⟩] [⟨1, 3⟩, ⟨2, 1⟩]) ⟨2, 1⟩ :=
  (isRoot_mul [⟨1, 2⟩, ⟨2, 1⟩] [⟨1, 3⟩, ⟨2, 1⟩] ⟨2, 1⟩).mpr
    (Or.inl (by decide +kernel))
theorem pin41 : ¬ isRoot (mul [⟨1, 2⟩, ⟨2, 1⟩] [⟨1, 3⟩, ⟨2, 1⟩]) ⟨4, 1⟩ := by decide +kernel

theorem pin42 : isRoot (powOf [⟨1, 2⟩, ⟨2, 1⟩] 3) ⟨2, 1⟩ := by decide +kernel
theorem pin43 : isRoot (powOf [⟨1, 2⟩, ⟨2, 1⟩] 3) ⟨2, 1⟩ :=
  (isRoot_powOf [⟨1, 2⟩, ⟨2, 1⟩] ⟨2, 1⟩ 3 (by decide +kernel)).mpr (by decide +kernel)
theorem pin44 : ¬ isRoot (powOf [⟨1, 2⟩, ⟨2, 1⟩] 3) ⟨3, 1⟩ := by decide +kernel

theorem pin45 : ¬ isRoot one ⟨2, 1⟩ := isRoot_one ⟨2, 1⟩

/-! The monic display's own read at a value-one top
(`monic_dropLast_oneValue`): a list whose top reads the scalar one
is its below-top part made monic, at the two-key list here.  The
top binder is load-bearing and the two refusals isolate it — at a
two-key list whose top reads three, and at the one-key list whose
only member reads two — the length binder naming nothing but the
key the top read is taken at, so a refused read is the top's. -/

theorem pin46 : oneValue (monic [BPair.ofNat 3, BPair.ofNat 1].dropLast)
    [BPair.ofNat 3, BPair.ofNat 1] :=
  monic_dropLast_oneValue [BPair.ofNat 3, BPair.ofNat 1] 1 rfl (by decide +kernel)

theorem pin47 : ¬ oneValue (monic [BPair.ofNat 1, BPair.ofNat 3].dropLast)
    [BPair.ofNat 1, BPair.ofNat 3] := by decide +kernel

theorem pin48 : ¬ oneValue (monic ([BPair.ofNat 2] : Poly).dropLast)
    [BPair.ofNat 2] := by decide +kernel

/-! The entry beyond a list's top is the stated default
(`ground.getAt_over`, the ground family's own read), and a scale at
a null pair rescales to a unit tail at every polynomial
(`scaleP_null`) — the pair `⟨3 : 3⟩` reads the sum's unit off the
canonical representative. -/

theorem pin49 : getAt BPair.unit [⟨6, 1⟩, ⟨3, 1⟩] 5 = BPair.unit :=
  getAt_over BPair.unit _ 5 (by decide +kernel)

theorem pin50 : unitTail (scaleP ⟨3, 3⟩ [⟨6, 1⟩, ⟨2, 1⟩]) :=
  scaleP_null (by decide +kernel) _

theorem pin51 : ¬ (⟨3, 3⟩ : BPair) = BPair.unit := by decide +kernel

/-! The value's representative reads one value with its own
polynomial (`vnorm_ov`), and the memberwise swap commutes with
every read the side theorem consumes: the representative
(`vnorm_neg`), the top key's coefficient (`top_neg`) and the Horner
read (`eval_neg`) — the tail of equal-membered coefficients dropped
either way. -/

theorem pin52 : oneValue (vnorm [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩, ⟨5, 5⟩])
    [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩, ⟨5, 5⟩] := by decide +kernel
theorem pin53 : oneValue (vnorm [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩, ⟨5, 5⟩])
    [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩, ⟨5, 5⟩] :=
  vnorm_ov [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩, ⟨5, 5⟩]
theorem pin54 : vnorm [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩, ⟨5, 5⟩]
    = [⟨1, 3⟩, ⟨1, 1⟩, ⟨2, 1⟩] := by decide +kernel

theorem pin55 : vnorm (neg [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩, ⟨5, 5⟩])
    = neg (vnorm [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩, ⟨5, 5⟩]) := by decide +kernel
theorem pin56 : vnorm (neg [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩, ⟨5, 5⟩])
    = neg (vnorm [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩, ⟨5, 5⟩]) :=
  vnorm_neg [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩, ⟨5, 5⟩]

theorem pin57 : top (neg [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩])
    = (top [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩]).swap := by decide +kernel
theorem pin58 : top (neg ([] : Poly)) = (top ([] : Poly)).swap :=
  top_neg []

theorem pin59 : eval (neg [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩]) ⟨4, 1⟩
    = (eval [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩] ⟨4, 1⟩).swap := by decide +kernel
theorem pin60 : eval (neg [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩]) ⟨4, 1⟩
    = (eval [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩] ⟨4, 1⟩).swap :=
  eval_neg [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩] ⟨4, 1⟩

/-! The representative at the cons structure: a further
coefficient above an occupied tail enters as its own
representative (`vnorm_cons_occ`), and above a vacant tail it is
the whole list when it is off the sum's unit (`vnorm_cons_off`),
each decided and through its theorem, with the occupancy binder
refused at a unit-valued head and the vacant read decided beside
it. -/

theorem pin61 : vnorm [⟨1, 4⟩, ⟨3, 1⟩, ⟨2, 2⟩] = [⟨1, 4⟩, ⟨3, 1⟩] := by
  decide +kernel
theorem pin62 : vnorm [⟨1, 4⟩, ⟨3, 1⟩, ⟨2, 2⟩]
    = (⟨1, 4⟩ : BPair).norm :: [⟨3, 1⟩] := by decide +kernel
theorem pin63 : vnorm [⟨1, 4⟩, ⟨3, 1⟩, ⟨2, 2⟩]
    = (⟨1, 4⟩ : BPair).norm :: [⟨3, 1⟩] :=
  vnorm_cons_occ ⟨1, 4⟩ ⟨3, 1⟩ [⟨3, 1⟩, ⟨2, 2⟩] [] (by decide +kernel)

theorem pin64 : vnorm [⟨3, 1⟩, ⟨2, 2⟩] = [(⟨3, 1⟩ : BPair).norm] := by
  decide +kernel
theorem pin65 : vnorm [⟨3, 1⟩, ⟨2, 2⟩] = [(⟨3, 1⟩ : BPair).norm] :=
  vnorm_cons_off ⟨3, 1⟩ [⟨2, 2⟩] (by decide +kernel) (by decide +kernel)

theorem pin66 : vnorm [⟨2, 2⟩, ⟨5, 5⟩] = [] := by decide +kernel

theorem pin67 : ¬ vnorm [⟨2, 2⟩, ⟨5, 5⟩] = [(⟨2, 2⟩ : BPair).norm] := by
  decide +kernel

/-! A coefficient family against a polynomial family (`scaleDot`):
each coefficient rescales its own polynomial and the rescalings sum
key by key — `2·(1 + z) + 3·1` reads `5 + 2 z`. -/

theorem pin68 : oneValue
    (scaleDot [BPair.ofNat 2, BPair.ofNat 3]
      [[BPair.ofNat 1, BPair.ofNat 1], [BPair.ofNat 1]])
    [BPair.ofNat 5, BPair.ofNat 2] := by decide +kernel

/-! The monomial kit's value pins: the monomial, its signed
spelling on both sides, the geometric word and the pair at a
gap. -/

theorem pin69 : oneValue (mono 2) [⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩] := by decide +kernel
theorem pin70 : mono 0 = one := rfl
theorem pin71 : oneValue (smono false 1) [⟨1, 1⟩, ⟨2, 1⟩] := by decide +kernel
theorem pin72 : oneValue (smono true 2) [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩] := by
  decide +kernel
theorem pin73 : oneValue (gword 3) [⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩] := by decide +kernel
theorem pin74 : gword 0 = [] := rfl
theorem pin75 : oneValue (tpair 1) [⟨1, 2⟩, ⟨2, 1⟩] := by decide +kernel
theorem pin76 : oneValue (tpair 2) [⟨1, 2⟩, ⟨1, 1⟩, ⟨2, 1⟩] := by decide +kernel

/-! The geometric word's Horner read at the natural one, and the
pair's split off the word, at the gaps two and three. -/

theorem pin77 : (eval (gword 2) (BPair.ofNat 1)).oneValue (BPair.ofNat 2)
    := by decide +kernel
theorem pin78 : (eval (gword 3) (BPair.ofNat 1)).oneValue (BPair.ofNat 3)
    := by decide +kernel
theorem pin79 : oneValue (tpair 2) (mul (tpair 1) (gword 2)) := by decide +kernel
theorem pin80 : oneValue (tpair 3) (mul (tpair 1) (gword 3)) := by decide +kernel

/-! The signed-monomial fold's coefficient read at a three-member
family, mixed sides with one repeated key: at that key the count
pair reads one even and one odd, and at the other key one even
alone. -/

theorem pin81 : (ground.getAt BPair.unit
    (ground.famFold add [] (fun x : Nat × Bool => smono x.2 x.1)
      [(1, false), (1, true), (2, false)]) 1).oneValue
  (BPair.ofCounts
    (ground.countOf (1, false)
      (([(1, false), (1, true), (2, false)] : List (Nat × Bool)).map
        (fun x => (x.1, x.2))))
    (ground.countOf (1, true)
      (([(1, false), (1, true), (2, false)] : List (Nat × Bool)).map
        (fun x => (x.1, x.2))))) := by decide +kernel

theorem pin82 : (ground.getAt BPair.unit
    (ground.famFold add [] (fun x : Nat × Bool => smono x.2 x.1)
      [(1, false), (1, true), (2, false)]) 2).oneValue
  (BPair.ofCounts 1 0) := by decide +kernel

/-! The monic cancellation exercised theorem-route: two spellings
of `2 - z` at the shared monic factor `z + 1`. -/

theorem pin83 : oneValue [⟨3, 1⟩, ⟨1, 2⟩] [⟨4, 2⟩, ⟨2, 3⟩] :=
  mul_cancel_monic [⟨2, 1⟩] (by decide +kernel)

/-! `cor:weyldim`'s member factors: the pair product over an
occupied-gap family collects one `<t:1>` per member against the
geometric words, and the words' Horner read at the natural one is
the gaps' own product. -/

theorem pin84 : oneValue
    (ground.famFold mul one (fun j => tpair (j + 1)) (List.range 2))
    (mul (powOf (tpair 1) (List.range 2).length)
      (ground.famFold mul one (fun j => gword (j + 1))
        (List.range 2))) := by decide +kernel

theorem pin85 : (eval (ground.famFold mul one (fun j => gword (j + 1))
      (List.range 2)) (BPair.ofNat 1)).oneValue
    (BPair.ofNat (ground.famFold Nat.mul 1 (fun j => j + 1)
      (List.range 2))) := by decide +kernel

/-! The iterated carrier's displayed reads at data, each with an
isolating refusal: the sum's riding tail, the convolution's
recursion, and the outer evaluation at a composite polynomial
point — the band-root substitution at the cleared identity
`4 s² = ⟨4 : t²⟩` with a forged point refusing and the clearing
power's refusal below the degree beside it. -/

private def zVar : Poly := [BPair.unit, BPair.ofPos Pos.one]

theorem pin86 : ppOneValue (pmul [zVar] [zVar, one])
    [mul zVar zVar, zVar] := by decide +kernel
theorem pin87 : ¬ ppOneValue (pmul [zVar] [zVar, one])
    [mul zVar zVar, one] := by decide +kernel
theorem pin88 : ppOneValue (padd [zVar] [[], one]) [zVar, one] := by decide +kernel
theorem pin89 : ¬ ppOneValue (padd [zVar] [[], one]) [zVar, zVar] := by
  decide +kernel

private def qBand : Poly :=
  [BPair.ofNat 4, BPair.unit, (BPair.ofNat 1).swap]

theorem pin90 : oneValue (pevalC [zVar, one] qBand 4 1)
    [BPair.ofNat 4, BPair.ofNat 4, (BPair.ofNat 1).swap] := by decide +kernel
theorem pin91 : ¬ oneValue (pevalC [zVar, one] [BPair.ofNat 4] 4 1)
    [BPair.ofNat 4, BPair.ofNat 4, (BPair.ofNat 1).swap] := by decide +kernel
theorem pin92 : ¬ oneValue (pevalC [zVar, one] qBand 4 0)
    [BPair.ofNat 4, BPair.ofNat 4, (BPair.ofNat 1).swap] := by decide +kernel

/-! The monic linear factor's Horner read: the value against the
root's balance partner, decided and applied through its theorem. -/

theorem pin93 : (eval (linFacM ⟨3, 1⟩) ⟨5, 1⟩).oneValue (⟨5, 1⟩ + (⟨3, 1⟩ : BPair).swap) := by
  decide +kernel

theorem pin94 : (eval (linFacM ⟨3, 1⟩) ⟨5, 1⟩).oneValue (⟨5, 1⟩ + (⟨3, 1⟩ : BPair).swap) :=
  eval_linFacM ⟨3, 1⟩ ⟨5, 1⟩

/-! The Horner read collected to the monomial fold at `5 + 2z + z³`
against the point two, decided and through its theorem. -/

private def pMono : Poly := [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩]

theorem pin95 : (eval pMono ⟨3, 1⟩).oneValue
    (ground.famFold BPair.add BPair.unit
      (fun k => ground.getAt BPair.unit pMono k * ground.bpow ⟨3, 1⟩ k)
      (List.range pMono.length)) := by decide +kernel

theorem pin96 : (eval pMono ⟨3, 1⟩).oneValue
    (ground.famFold BPair.add BPair.unit
      (fun k => ground.getAt BPair.unit pMono k * ground.bpow ⟨3, 1⟩ k)
      (List.range pMono.length)) :=
  eval_famFold pMono ⟨3, 1⟩

/-! The variable's clearing at `z² - 2` and the power two: the
cleared list's Horner read against the cleared evaluation at the
point four, the derivative of the cleared list against the
derivative's clearing one power down, and the key count kept —
each decided and through its theorem. -/

private def sQc : Poly := [⟨1, 3⟩, BPair.unit, ⟨2, 1⟩]

theorem pin97 : (eval (clearVar sQc 2 2) ⟨4, 1⟩).oneValue
    (evalClear sQc ⟨4, 1⟩ 2 2) := by decide +kernel

theorem pin98 : (eval (clearVar sQc 2 2) ⟨4, 1⟩).oneValue
    (evalClear sQc ⟨4, 1⟩ 2 2) :=
  eval_clearVar sQc 2 2 ⟨4, 1⟩

theorem pin99 : oneValue (deriv (clearVar sQc 2 2)) (clearVar (deriv sQc) 2 1) := by
  decide +kernel

theorem pin100 : oneValue (deriv (clearVar sQc 2 2)) (clearVar (deriv sQc) 2 1) :=
  deriv_clearVar sQc 2 2

theorem pin101 : (clearVar sQc 2 2).length = sQc.length :=
  length_clearVar sQc 2 2

/-! The clearing's ring reads at `z² - 2` against `z + 5`: the sum
componentwise at the one stated power, the memberwise swap
entrywise, and the convolution at the joined power with each factor
within its stated power, at the clearings two and three — each
decided and through its theorem — and the convolution's degree
binder refused one power short of the first factor's own, where the
key two reads `5` against `15`. -/

private def pB' : Poly := [⟨6, 1⟩, ⟨2, 1⟩]

theorem pin102 : oneValue (clearVar (add sQc pB') 2 2)
    (add (clearVar sQc 2 2) (clearVar pB' 2 2)) := by decide +kernel

theorem pin103 : oneValue (clearVar (add sQc pB') 2 2)
    (add (clearVar sQc 2 2) (clearVar pB' 2 2)) :=
  clearVar_add sQc pB' 2 2

theorem pin104 : clearVar (neg sQc) 2 2 = neg (clearVar sQc 2 2) := by
  decide +kernel

theorem pin105 : clearVar (neg sQc) 2 2 = neg (clearVar sQc 2 2) :=
  clearVar_neg sQc 2 2

theorem pin106 : oneValue (clearVar (mul sQc pB') 2 (2 + 1))
    (mul (clearVar sQc 2 2) (clearVar pB' 2 1)) := by decide +kernel

theorem pin107 : oneValue (clearVar (mul sQc pB') 2 (2 + 1))
    (mul (clearVar sQc 2 2) (clearVar pB' 2 1)) :=
  clearVar_mul sQc pB' 2 2 1 (Nat.le_refl _) (Nat.le_refl _)

theorem pin108 : oneValue (clearVar (mul sQc pB') 3 (2 + 1))
    (mul (clearVar sQc 3 2) (clearVar pB' 3 1)) := by decide +kernel

theorem pin109 : oneValue (clearVar (mul sQc pB') 3 (2 + 1))
    (mul (clearVar sQc 3 2) (clearVar pB' 3 1)) :=
  clearVar_mul sQc pB' 3 2 1 (Nat.le_refl _) (Nat.le_refl _)

theorem pin110 : ¬ oneValue (clearVar (mul sQc pB') 3 (1 + 1))
    (mul (clearVar sQc 3 1) (clearVar pB' 3 1)) := by decide +kernel

/-! The cleared evaluation at an end-shaped list: at the unit middle
the constant key survives at the clearing's square and the top key
at the point's, `[3, 0, 2]` at the point `⟨4 : 1⟩` over the clearing
two reading `3·4 + 2·9`; an occupied middle refuses the read, its
own term surviving. -/

theorem pin111 : (evalClear [⟨4, 1⟩, BPair.unit, ⟨3, 1⟩] ⟨4, 1⟩ 2 2).oneValue
    (ground.bpow (BPair.ofPos 2) 2 * ⟨4, 1⟩
      + ground.bpow ⟨4, 1⟩ 2 * ⟨3, 1⟩) := by decide +kernel

theorem pin112 : (evalClear [⟨4, 1⟩, BPair.unit, ⟨3, 1⟩] ⟨4, 1⟩ 2 2).oneValue
    (ground.bpow (BPair.ofPos 2) 2 * ⟨4, 1⟩
      + ground.bpow ⟨4, 1⟩ 2 * ⟨3, 1⟩) :=
  evalClear_ends ⟨4, 1⟩ ⟨3, 1⟩ [BPair.unit] (by decide +kernel) ⟨4, 1⟩ 2

theorem pin113 : ¬ (evalClear [⟨4, 1⟩, ⟨2, 1⟩, ⟨3, 1⟩] ⟨4, 1⟩ 2 2).oneValue
    (ground.bpow (BPair.ofPos 2) 2 * ⟨4, 1⟩
      + ground.bpow ⟨4, 1⟩ 2 * ⟨3, 1⟩) := by decide +kernel

/-! `def:poly`'s shared-factor withdrawal: at the occupied factor
`z + 2` the products of the cofactor `z + 1` in two spellings —
`[⟨4:3⟩, ⟨5:4⟩]` against the padded `[⟨2:1⟩, ⟨2:1⟩, ⟨1:1⟩]` —
withdraw to the cofactors' own read, decided and through the
theorem, with an off cofactor refused; and the occupancy binder is
load-bearing — at the vacant factor both products read the sum's
unit while the cofactors read apart. -/

private def dOcc : Poly := [⟨3, 1⟩, ⟨2, 1⟩]

private def uCo : Poly := [⟨4, 3⟩, ⟨5, 4⟩]

private def vCo : Poly := [⟨2, 1⟩, ⟨2, 1⟩, BPair.unit]

theorem pin114 : oneValue (mul dOcc uCo) (mul dOcc vCo) := by decide +kernel

theorem pin115 : oneValue uCo vCo := by decide +kernel

theorem pin116 : oneValue uCo vCo :=
  pmul_cancel dOcc uCo vCo (by decide +kernel) (by decide +kernel)

theorem pin117 : ¬ oneValue (mul dOcc uCo) (mul dOcc [⟨3, 1⟩, ⟨2, 1⟩]) := by
  decide +kernel

theorem pin118 : ¬ (oneValue (mul ([] : Poly) one) (mul ([] : Poly) [])
    → oneValue one ([] : Poly)) := by decide +kernel

theorem pin119 : unitTail ([] : Poly) := by decide +kernel

/-! The inner evaluation at a composite point, at
`P(t, s) = (1 + 2t) + (3 + t) s` and `Q(t, s) = (2 + t) + 4 s`: the
evaluation at `t = 2` (`[5, 5]` at the clearing one, `[10, 10]` at
the representative `[4 : 2]`), the key count kept, the inner-degree
cap decided at the power one and refused at the power nought, the
outer sum and product at the split powers decided and through the
theorem with the product's conclusion parting at a power below a
factor's degree, the inner top read at one and at two on a ragged
list with the cap holding there through its theorem, and the
clearing-one read against the coefficientwise evaluation. -/

private def PQ1 : PPoly := [[BPair.ofNat 1, BPair.ofNat 2], [BPair.ofNat 3, BPair.ofNat 1]]
private def PQ2 : PPoly := [[BPair.ofNat 2, BPair.ofNat 1], [BPair.ofNat 4]]
private def PQ3 : PPoly := [[BPair.ofNat 2], [BPair.ofNat 1, BPair.unit, BPair.ofNat 5], [BPair.ofNat 3]]

theorem pin120 : oneValue (pevalCP PQ1 (BPair.ofNat 2) 1 1)
    [BPair.ofNat 5, BPair.ofNat 5] := by decide +kernel
theorem pin121 : oneValue (pevalCP PQ1 (BPair.ofNat 4) 2 1)
    [BPair.ofNat 10, BPair.ofNat 10] := by decide +kernel
theorem pin122 : (pevalCP PQ1 (BPair.ofNat 2) 1 1).length = PQ1.length := by
  decide +kernel
theorem pin123 : innerLe PQ1 1 := by decide +kernel
theorem pin124 : ¬ innerLe PQ1 0 := by decide +kernel
theorem pin125 : oneValue (pevalCP (padd PQ1 PQ2) (BPair.ofNat 2) 1 1)
    (add (pevalCP PQ1 (BPair.ofNat 2) 1 1) (pevalCP PQ2 (BPair.ofNat 2) 1 1)) := by
  decide +kernel
theorem pin126 : oneValue (pevalCP (pmul PQ1 PQ2) (BPair.ofNat 2) 1 (1 + 1))
    (mul (pevalCP PQ1 (BPair.ofNat 2) 1 1) (pevalCP PQ2 (BPair.ofNat 2) 1 1)) := by
  decide +kernel
theorem pin127 : oneValue (pevalCP (pmul PQ1 PQ2) (BPair.ofNat 3) 2 (1 + 1))
    (mul (pevalCP PQ1 (BPair.ofNat 3) 2 1) (pevalCP PQ2 (BPair.ofNat 3) 2 1)) :=
  pevalCP_pmul PQ1 PQ2 1 1 (by decide +kernel) (by decide +kernel) (BPair.ofNat 3) 2
theorem pin128 : ¬ oneValue (pevalCP (pmul PQ1 PQ2) (BPair.ofNat 3) 2 (0 + 1))
    (mul (pevalCP PQ1 (BPair.ofNat 3) 2 0) (pevalCP PQ2 (BPair.ofNat 3) 2 1)) := by
  decide +kernel
theorem pin129 : innerTop PQ1 = 1 := by decide +kernel
theorem pin130 : innerTop PQ3 = 2 := by decide +kernel
theorem pin131 : innerLe PQ3 (innerTop PQ3) := innerLe_innerTop PQ3
theorem pin132 : ¬ innerLe PQ3 1 := by decide +kernel
theorem pin133 : oneValue (pevalCP PQ1 (BPair.ofNat 2) 1 3) (pevalB PQ1 (BPair.ofNat 2)) := by
  decide +kernel
theorem pin134 : oneValue (pevalCP PQ3 (BPair.ofNat 3) 1 2) (pevalB PQ3 (BPair.ofNat 3)) :=
  pevalCP_one PQ3 (BPair.ofNat 3) 2

end poly
