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

open ground poly

/-! The product's unit at its consumption: the convolution reads a
polynomial off, and the Horner read is the scalar one. -/

example : oneValue (mul one [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩])
    [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩] := by decide +kernel

example : BPair.oneValue (eval one ⟨6, 1⟩) (BPair.ofPos .one) := by
  decide +kernel

/-! The sum and the convolution. -/

example : oneValue (add [⟨2, 1⟩, ⟨3, 1⟩] [⟨1, 2⟩]) [⟨1, 1⟩, ⟨3, 1⟩] := by
  decide +kernel

example : oneValue (mul [⟨2, 1⟩, ⟨2, 1⟩] [⟨2, 1⟩, ⟨1, 2⟩])
    [⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩] := by decide +kernel

/-! The Horner read: `P = 5 + 2z + z^3` at `z = 2` reads `17`. -/

example : BPair.oneValue
    (eval [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩] ⟨3, 1⟩) ⟨18, 1⟩ := by decide +kernel

/-! The derivative and its Leibniz rule. -/

example : oneValue (deriv [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩])
    [⟨3, 1⟩, ⟨1, 1⟩, ⟨4, 1⟩] := by decide +kernel

example : oneValue (deriv (mul [⟨2, 1⟩, ⟨3, 1⟩] [⟨1, 2⟩, ⟨2, 1⟩, ⟨4, 1⟩]))
    (add (mul (deriv [⟨2, 1⟩, ⟨3, 1⟩]) [⟨1, 2⟩, ⟨2, 1⟩, ⟨4, 1⟩])
      (mul [⟨2, 1⟩, ⟨3, 1⟩] (deriv [⟨1, 2⟩, ⟨2, 1⟩, ⟨4, 1⟩]))) := by
  decide +kernel
example : oneValue (deriv (mul [⟨2, 1⟩, ⟨3, 1⟩] [⟨1, 2⟩, ⟨2, 1⟩, ⟨4, 1⟩]))
    (add (mul (deriv [⟨2, 1⟩, ⟨3, 1⟩]) [⟨1, 2⟩, ⟨2, 1⟩, ⟨4, 1⟩])
      (mul [⟨2, 1⟩, ⟨3, 1⟩] (deriv [⟨1, 2⟩, ⟨2, 1⟩, ⟨4, 1⟩]))) :=
  deriv_mul _ _

/-! The division at a monic: `z^3 + 2z + 5 = (z^2 + 1) z + (z + 5)`,
the quotient, the remainder and the naming identity. -/

example : divRead [⟨2, 1⟩, ⟨1, 1⟩] [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩] := by
  decide +kernel

example : oneValue
    (div [⟨2, 1⟩, ⟨1, 1⟩] [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩]).1
    [⟨1, 1⟩, ⟨2, 1⟩] := by decide +kernel

example : oneValue
    (div [⟨2, 1⟩, ⟨1, 1⟩] [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩]).2
    [⟨6, 1⟩, ⟨2, 1⟩] := by decide +kernel

/-! The descent's pair is one value at every solution: a padded
quotient and a shifted remainder representative read the same pair
(`div_unique`), and the below-top dividend reads the vacant
quotient. -/

example : oneValue [⟨1, 1⟩, ⟨2, 1⟩, ⟨4, 4⟩]
      (div [⟨2, 1⟩, ⟨1, 1⟩] [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩]).1
    ∧ oneValue [⟨8, 3⟩, ⟨3, 2⟩]
      (div [⟨2, 1⟩, ⟨1, 1⟩] [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩]).2 :=
  div_unique [⟨2, 1⟩, ⟨1, 1⟩] [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩]
    [⟨1, 1⟩, ⟨2, 1⟩, ⟨4, 4⟩] [⟨8, 3⟩, ⟨3, 2⟩] rfl (by decide +kernel)

example : oneValue [] (div [⟨2, 1⟩, ⟨1, 1⟩] [⟨4, 1⟩]).1
    ∧ oneValue [⟨4, 1⟩, ⟨1, 1⟩] (div [⟨2, 1⟩, ⟨1, 1⟩] [⟨4, 1⟩]).2 :=
  div_unique [⟨2, 1⟩, ⟨1, 1⟩] [⟨4, 1⟩] [] [⟨4, 1⟩, ⟨1, 1⟩] rfl (by decide +kernel)

/-- At the linear factor `z - 2` the remainder is the Horner read at
`2`: `P(2) = 17`. -/
example : oneValue
    (div [⟨1, 3⟩] [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩]).2 [⟨18, 1⟩] := by
  decide +kernel

/-! The linear divisor's remainder is the Horner read at that
divisor's own root (`div_linear_eval`), at two benches: the deck
symbol `P_5` against `⟨x : 3⟩`, whose root is the balance partner
of three, and the degree-two list `5z² + 2z + 7` against
`⟨x : 1̌⟩`, whose root is one.  Each bench sits twice, the kernel's
own read beside the general theorem's. -/

example : oneValue (div [BPair.ofNat 3] (deck.pSum 2)).2
    [eval (deck.pSum 2) (BPair.ofNat 3).swap] := by decide +kernel

example : oneValue (div [BPair.ofNat 3] (deck.pSum 2)).2
    [eval (deck.pSum 2) (BPair.ofNat 3).swap] := by
  exact div_linear_eval (BPair.ofNat 3) (deck.pSum 2)

example : oneValue
    (div [(BPair.ofNat 1).swap]
      [BPair.ofNat 7, BPair.ofNat 2, BPair.ofNat 5]).2
    [eval [BPair.ofNat 7, BPair.ofNat 2, BPair.ofNat 5]
      (BPair.ofNat 1)] := by decide +kernel

example : oneValue
    (div [(BPair.ofNat 1).swap]
      [BPair.ofNat 7, BPair.ofNat 2, BPair.ofNat 5]).2
    [eval [BPair.ofNat 7, BPair.ofNat 2, BPair.ofNat 5]
      (BPair.ofNat 1)] := by
  exact div_linear_eval ((BPair.ofNat 1).swap)
    [BPair.ofNat 7, BPair.ofNat 2, BPair.ofNat 5]

/-! The remainder lists at `z^2 + 1`: `z · z` reads the balance
partner of one. -/

example : oneValue (remMul [⟨2, 1⟩, ⟨1, 1⟩] [⟨1, 1⟩, ⟨2, 1⟩]
    [⟨1, 1⟩, ⟨2, 1⟩]) [⟨1, 2⟩, ⟨1, 1⟩] := by decide +kernel

/-! The division at the edges: the dividend below the top, and the
constant divisor. -/

example : divRead [⟨2, 1⟩, ⟨1, 1⟩] [⟨4, 1⟩] := by decide +kernel
example : divRead [] [⟨6, 1⟩, ⟨3, 1⟩] := by decide +kernel

/-! The root and multiplicity reads at `(z-2)^2 (z-3)`, and the
linear factor's Horner remainder. -/

example : isRoot [⟨1, 13⟩, ⟨17, 1⟩, ⟨1, 8⟩, ⟨2, 1⟩] ⟨3, 1⟩ := by decide +kernel
example : ¬ isRoot [⟨1, 13⟩, ⟨17, 1⟩, ⟨1, 8⟩, ⟨2, 1⟩] ⟨2, 1⟩ := by decide +kernel
example : multAt [⟨1, 3⟩] [⟨1, 13⟩, ⟨17, 1⟩, ⟨1, 8⟩, ⟨2, 1⟩] = 2 := by decide +kernel
example : multAt [⟨1, 4⟩] [⟨1, 13⟩, ⟨17, 1⟩, ⟨1, 8⟩, ⟨2, 1⟩] = 1 := by decide +kernel
example : multAt [⟨1, 2⟩] [⟨1, 13⟩, ⟨17, 1⟩, ⟨1, 8⟩, ⟨2, 1⟩] = 0 := by decide +kernel
example : hornerRead [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩] ⟨3, 1⟩ := by decide +kernel

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

example : oneValue (mul [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩])
    [⟨3, 1⟩, ⟨2, 1⟩, ⟨3, 1⟩, ⟨6, 1⟩, ⟨3, 1⟩] := by decide +kernel

example : BPair.oneValue
    (top (mul [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩]))
    (top [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] * top [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩]) := by
  decide +kernel
example : BPair.oneValue
    (top (mul [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩]))
    (top [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] * top [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩]) :=
  top_mul [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩]

example : (mul [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩]).length + 1
    = ([⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] : Poly).length
      + ([⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩] : Poly).length := by decide +kernel
example : (mul [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩]).length + 1
    = ([⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] : Poly).length
      + ([⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩] : Poly).length :=
  length_mul [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩]
    (by decide +kernel) (by decide +kernel)

example : BPair.oneValue
    (top (mul [⟨2, 1⟩, ⟨1, 1⟩] [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩]))
    (top [⟨2, 1⟩, ⟨1, 1⟩] * top [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩]) := by decide +kernel
example : ¬ ((mul [] [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩]).length + 1
    = ([] : Poly).length + ([⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩] : Poly).length) := by
  decide +kernel

example : ¬ unitTail
    (mul [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] [⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 1⟩]) := by decide +kernel
example : unitTail (mul [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] [⟨1, 1⟩, ⟨1, 1⟩]) := by decide +kernel
example : unitTail ([⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] : Poly)
    ∨ unitTail ([⟨1, 1⟩, ⟨1, 1⟩] : Poly) :=
  unitTail_mul_of (by decide +kernel)
example : unitTail (mul [⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩] [⟨1, 1⟩, ⟨1, 1⟩]) :=
  of_unitTail_mul (Or.inr (by decide +kernel))

example : isRoot (mul [⟨1, 2⟩, ⟨2, 1⟩] [⟨1, 3⟩, ⟨2, 1⟩]) ⟨2, 1⟩ := by decide +kernel
example : isRoot (mul [⟨1, 2⟩, ⟨2, 1⟩] [⟨1, 3⟩, ⟨2, 1⟩]) ⟨2, 1⟩ :=
  (isRoot_mul [⟨1, 2⟩, ⟨2, 1⟩] [⟨1, 3⟩, ⟨2, 1⟩] ⟨2, 1⟩).mpr
    (Or.inl (by decide +kernel))
example : ¬ isRoot (mul [⟨1, 2⟩, ⟨2, 1⟩] [⟨1, 3⟩, ⟨2, 1⟩]) ⟨4, 1⟩ := by decide +kernel

example : isRoot (powOf [⟨1, 2⟩, ⟨2, 1⟩] 3) ⟨2, 1⟩ := by decide +kernel
example : isRoot (powOf [⟨1, 2⟩, ⟨2, 1⟩] 3) ⟨2, 1⟩ :=
  (isRoot_powOf [⟨1, 2⟩, ⟨2, 1⟩] ⟨2, 1⟩ 3 (by decide +kernel)).mpr (by decide +kernel)
example : ¬ isRoot (powOf [⟨1, 2⟩, ⟨2, 1⟩] 3) ⟨3, 1⟩ := by decide +kernel

example : ¬ isRoot one ⟨2, 1⟩ := isRoot_one ⟨2, 1⟩

/-! The monic display's own read at a value-one top
(`monic_dropLast_oneValue`): a list whose top reads the scalar one
is its below-top part made monic, at the two-key list here.  The
top binder is load-bearing and the two refusals isolate it — at a
two-key list whose top reads three, and at the one-key list whose
only member reads two — the length binder naming nothing but the
key the top read is taken at, so a refused read is the top's. -/

example : oneValue (monic [BPair.ofNat 3, BPair.ofNat 1].dropLast)
    [BPair.ofNat 3, BPair.ofNat 1] :=
  monic_dropLast_oneValue [BPair.ofNat 3, BPair.ofNat 1] 1 rfl (by decide +kernel)

example : ¬ oneValue (monic [BPair.ofNat 1, BPair.ofNat 3].dropLast)
    [BPair.ofNat 1, BPair.ofNat 3] := by decide +kernel

example : ¬ oneValue (monic ([BPair.ofNat 2] : Poly).dropLast)
    [BPair.ofNat 2] := by decide +kernel

/-! The entry beyond a list's top is the stated default
(`ground.getAt_over`, the ground family's own read), and a scale at
a null pair rescales to a unit tail at every polynomial
(`scaleP_null`) — the pair `⟨3 : 3⟩` reads the sum's unit off the
canonical representative. -/

example : getAt BPair.unit [⟨6, 1⟩, ⟨3, 1⟩] 5 = BPair.unit :=
  getAt_over BPair.unit _ 5 (by decide +kernel)

example : unitTail (scaleP ⟨3, 3⟩ [⟨6, 1⟩, ⟨2, 1⟩]) :=
  scaleP_null (by decide +kernel) _

example : ¬ (⟨3, 3⟩ : BPair) = BPair.unit := by decide +kernel

/-! The value's representative reads one value with its own
polynomial (`vnorm_ov`), and the memberwise swap commutes with
every read the side theorem consumes: the representative
(`vnorm_neg`), the top key's coefficient (`top_neg`) and the Horner
read (`eval_neg`) — the tail of equal-membered coefficients dropped
either way. -/

example : oneValue (vnorm [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩, ⟨5, 5⟩])
    [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩, ⟨5, 5⟩] := by decide +kernel
example : oneValue (vnorm [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩, ⟨5, 5⟩])
    [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩, ⟨5, 5⟩] :=
  vnorm_ov [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩, ⟨5, 5⟩]
example : vnorm [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩, ⟨5, 5⟩]
    = [⟨1, 3⟩, ⟨1, 1⟩, ⟨2, 1⟩] := by decide +kernel

example : vnorm (neg [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩, ⟨5, 5⟩])
    = neg (vnorm [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩, ⟨5, 5⟩]) := by decide +kernel
example : vnorm (neg [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩, ⟨5, 5⟩])
    = neg (vnorm [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩, ⟨5, 5⟩]) :=
  vnorm_neg [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩, ⟨5, 5⟩]

example : top (neg [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩])
    = (top [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩]).swap := by decide +kernel
example : top (neg ([] : Poly)) = (top ([] : Poly)).swap :=
  top_neg []

example : eval (neg [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩]) ⟨4, 1⟩
    = (eval [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩] ⟨4, 1⟩).swap := by decide +kernel
example : eval (neg [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩]) ⟨4, 1⟩
    = (eval [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩] ⟨4, 1⟩).swap :=
  eval_neg [⟨1, 3⟩, ⟨4, 4⟩, ⟨2, 1⟩] ⟨4, 1⟩

/-! A coefficient family against a polynomial family (`scaleDot`):
each coefficient rescales its own polynomial and the rescalings sum
key by key — `2·(1 + z) + 3·1` reads `5 + 2 z`. -/

example : oneValue
    (scaleDot [BPair.ofNat 2, BPair.ofNat 3]
      [[BPair.ofNat 1, BPair.ofNat 1], [BPair.ofNat 1]])
    [BPair.ofNat 5, BPair.ofNat 2] := by decide +kernel

/-! The monomial kit's value pins: the monomial, its signed
spelling on both sides, the geometric word and the pair at a
gap. -/

example : oneValue (mono 2) [⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩] := by decide +kernel
example : mono 0 = one := rfl
example : oneValue (smono false 1) [⟨1, 1⟩, ⟨2, 1⟩] := by decide +kernel
example : oneValue (smono true 2) [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩] := by
  decide +kernel
example : oneValue (gword 3) [⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩] := by decide +kernel
example : gword 0 = [] := rfl
example : oneValue (tpair 1) [⟨1, 2⟩, ⟨2, 1⟩] := by decide +kernel
example : oneValue (tpair 2) [⟨1, 2⟩, ⟨1, 1⟩, ⟨2, 1⟩] := by decide +kernel

/-! The geometric word's Horner read at the natural one, and the
pair's split off the word, at the gaps two and three. -/

example : (eval (gword 2) (BPair.ofNat 1)).oneValue (BPair.ofNat 2)
    := by decide +kernel
example : (eval (gword 3) (BPair.ofNat 1)).oneValue (BPair.ofNat 3)
    := by decide +kernel
example : oneValue (tpair 2) (mul (tpair 1) (gword 2)) := by decide +kernel
example : oneValue (tpair 3) (mul (tpair 1) (gword 3)) := by decide +kernel

/-! The signed-monomial fold's coefficient read at a three-member
family, mixed sides with one repeated key: at that key the count
pair reads one even and one odd, and at the other key one even
alone. -/

example : (ground.getAt BPair.unit
    (ground.famFold add [] (fun x : Nat × Bool => smono x.2 x.1)
      [(1, false), (1, true), (2, false)]) 1).oneValue
  (BPair.ofCounts
    (ground.countOf (1, false)
      (([(1, false), (1, true), (2, false)] : List (Nat × Bool)).map
        (fun x => (x.1, x.2))))
    (ground.countOf (1, true)
      (([(1, false), (1, true), (2, false)] : List (Nat × Bool)).map
        (fun x => (x.1, x.2))))) := by decide +kernel

example : (ground.getAt BPair.unit
    (ground.famFold add [] (fun x : Nat × Bool => smono x.2 x.1)
      [(1, false), (1, true), (2, false)]) 2).oneValue
  (BPair.ofCounts 1 0) := by decide +kernel

/-! The monic cancellation exercised theorem-route: two spellings
of `2 - z` at the shared monic factor `z + 1`. -/

example : oneValue [⟨3, 1⟩, ⟨1, 2⟩] [⟨4, 2⟩, ⟨2, 3⟩] :=
  mul_cancel_monic [⟨2, 1⟩] (by decide +kernel)

/-! `cor:weyldim`'s member factors: the pair product over an
occupied-gap family collects one `<t:1>` per member against the
geometric words, and the words' Horner read at the natural one is
the gaps' own product. -/

example : oneValue
    (ground.famFold mul one (fun j => tpair (j + 1)) (List.range 2))
    (mul (powOf (tpair 1) (List.range 2).length)
      (ground.famFold mul one (fun j => gword (j + 1))
        (List.range 2))) := by decide +kernel

example : (eval (ground.famFold mul one (fun j => gword (j + 1))
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

example : ppOneValue (pmul [zVar] [zVar, one])
    [mul zVar zVar, zVar] := by decide +kernel
example : ¬ ppOneValue (pmul [zVar] [zVar, one])
    [mul zVar zVar, one] := by decide +kernel
example : ppOneValue (padd [zVar] [[], one]) [zVar, one] := by decide +kernel
example : ¬ ppOneValue (padd [zVar] [[], one]) [zVar, zVar] := by
  decide +kernel

private def qBand : Poly :=
  [BPair.ofNat 4, BPair.unit, (BPair.ofNat 1).swap]

example : oneValue (pevalC [zVar, one] qBand 4 1)
    [BPair.ofNat 4, BPair.ofNat 4, (BPair.ofNat 1).swap] := by decide +kernel
example : ¬ oneValue (pevalC [zVar, one] [BPair.ofNat 4] 4 1)
    [BPair.ofNat 4, BPair.ofNat 4, (BPair.ofNat 1).swap] := by decide +kernel
example : ¬ oneValue (pevalC [zVar, one] qBand 4 0)
    [BPair.ofNat 4, BPair.ofNat 4, (BPair.ofNat 1).swap] := by decide +kernel

/-! The monic linear factor's Horner read: the value against the
root's balance partner, decided and applied through its theorem. -/

example : (eval (linFacM ⟨3, 1⟩) ⟨5, 1⟩).oneValue (⟨5, 1⟩ + (⟨3, 1⟩ : BPair).swap) := by
  decide +kernel

example : (eval (linFacM ⟨3, 1⟩) ⟨5, 1⟩).oneValue (⟨5, 1⟩ + (⟨3, 1⟩ : BPair).swap) :=
  eval_linFacM ⟨3, 1⟩ ⟨5, 1⟩

/-! The Horner read collected to the monomial fold at `5 + 2z + z³`
against the point two, decided and through its theorem. -/

private def pMono : Poly := [⟨6, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩]

example : (eval pMono ⟨3, 1⟩).oneValue
    (ground.famFold BPair.add BPair.unit
      (fun k => ground.getAt BPair.unit pMono k * ground.bpow ⟨3, 1⟩ k)
      (List.range pMono.length)) := by decide +kernel

example : (eval pMono ⟨3, 1⟩).oneValue
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

example : (eval (clearVar sQc 2 2) ⟨4, 1⟩).oneValue
    (evalClear sQc ⟨4, 1⟩ 2 2) := by decide +kernel

example : (eval (clearVar sQc 2 2) ⟨4, 1⟩).oneValue
    (evalClear sQc ⟨4, 1⟩ 2 2) :=
  eval_clearVar sQc 2 2 ⟨4, 1⟩

example : oneValue (deriv (clearVar sQc 2 2)) (clearVar (deriv sQc) 2 1) := by
  decide +kernel

example : oneValue (deriv (clearVar sQc 2 2)) (clearVar (deriv sQc) 2 1) :=
  deriv_clearVar sQc 2 2

example : (clearVar sQc 2 2).length = sQc.length :=
  length_clearVar sQc 2 2

/-! The clearing's ring reads at `z² - 2` against `z + 5`: the sum
componentwise at the one stated power, the memberwise swap
entrywise, and the convolution at the joined power with each factor
within its stated power, at the clearings two and three — each
decided and through its theorem — and the convolution's degree
binder refused one power short of the first factor's own, where the
key two reads `5` against `15`. -/

private def pB' : Poly := [⟨6, 1⟩, ⟨2, 1⟩]

example : oneValue (clearVar (add sQc pB') 2 2)
    (add (clearVar sQc 2 2) (clearVar pB' 2 2)) := by decide +kernel

example : oneValue (clearVar (add sQc pB') 2 2)
    (add (clearVar sQc 2 2) (clearVar pB' 2 2)) :=
  clearVar_add sQc pB' 2 2

example : clearVar (neg sQc) 2 2 = neg (clearVar sQc 2 2) := by
  decide +kernel

example : clearVar (neg sQc) 2 2 = neg (clearVar sQc 2 2) :=
  clearVar_neg sQc 2 2

example : oneValue (clearVar (mul sQc pB') 2 (2 + 1))
    (mul (clearVar sQc 2 2) (clearVar pB' 2 1)) := by decide +kernel

example : oneValue (clearVar (mul sQc pB') 2 (2 + 1))
    (mul (clearVar sQc 2 2) (clearVar pB' 2 1)) :=
  clearVar_mul sQc pB' 2 2 1 (Nat.le_refl _) (Nat.le_refl _)

example : oneValue (clearVar (mul sQc pB') 3 (2 + 1))
    (mul (clearVar sQc 3 2) (clearVar pB' 3 1)) := by decide +kernel

example : oneValue (clearVar (mul sQc pB') 3 (2 + 1))
    (mul (clearVar sQc 3 2) (clearVar pB' 3 1)) :=
  clearVar_mul sQc pB' 3 2 1 (Nat.le_refl _) (Nat.le_refl _)

example : ¬ oneValue (clearVar (mul sQc pB') 3 (1 + 1))
    (mul (clearVar sQc 3 1) (clearVar pB' 3 1)) := by decide +kernel

/-! The cleared evaluation at an end-shaped list: at the unit middle
the constant key survives at the clearing's square and the top key
at the point's, `[3, 0, 2]` at the point `⟨4 : 1⟩` over the clearing
two reading `3·4 + 2·9`; an occupied middle refuses the read, its
own term surviving. -/

example : (evalClear [⟨4, 1⟩, BPair.unit, ⟨3, 1⟩] ⟨4, 1⟩ 2 2).oneValue
    (ground.bpow (BPair.ofPos 2) 2 * ⟨4, 1⟩
      + ground.bpow ⟨4, 1⟩ 2 * ⟨3, 1⟩) := by decide +kernel

example : (evalClear [⟨4, 1⟩, BPair.unit, ⟨3, 1⟩] ⟨4, 1⟩ 2 2).oneValue
    (ground.bpow (BPair.ofPos 2) 2 * ⟨4, 1⟩
      + ground.bpow ⟨4, 1⟩ 2 * ⟨3, 1⟩) :=
  evalClear_ends ⟨4, 1⟩ ⟨3, 1⟩ [BPair.unit] (by decide +kernel) ⟨4, 1⟩ 2

example : ¬ (evalClear [⟨4, 1⟩, ⟨2, 1⟩, ⟨3, 1⟩] ⟨4, 1⟩ 2 2).oneValue
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

example : oneValue (mul dOcc uCo) (mul dOcc vCo) := by decide +kernel

example : oneValue uCo vCo := by decide +kernel

example : oneValue uCo vCo :=
  pmul_cancel dOcc uCo vCo (by decide +kernel) (by decide +kernel)

example : ¬ oneValue (mul dOcc uCo) (mul dOcc [⟨3, 1⟩, ⟨2, 1⟩]) := by
  decide +kernel

example : ¬ (oneValue (mul ([] : Poly) one) (mul ([] : Poly) [])
    → oneValue one ([] : Poly)) := by decide +kernel

example : unitTail ([] : Poly) := by decide +kernel
