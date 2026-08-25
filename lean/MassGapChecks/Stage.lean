import MassGap.Stage
/-!
The check module for `lem:stage`: the batteries re-read the one
adjunction's arithmetic by kernel `decide` at `z² - 2` on the
bracket `(5/4, 3/2)` — the bracket's side exchange with the
isolation at half the separation (the width `[1 : 4]`), the
adjunction's own product read (`√2² = 2`, the remainder
multiplication, `poly.divRead` and `poly.hornerRead` the descent's
recorded consumers arriving beside it), the equal-members read by
reduction, the unit witness cleared at two (`z · z - (z² - 2)`),
and the side reads at the priced brackets (`z` on the upper side,
`z - 3` on the lower, the image-width price against the endpoint
values) with the side kept at a bracket point through the theorem
tier (`sideUpper_all`).  Beside them the priced side read at a
composite bracket and a stated bound, at `z + 5` on the bracket
`(0, 2)` at the bound `[4 : 1]`: the read decided, the side kept at
the interior point `1/2` through its theorem (`keepUpper_all`), a
bracket reaching seven refused and the bound one refused, the
image-width price at the bracket's endpoints decided and through
its theorem, the lower side at `-z - 5`, and the clearing
conjunct's isolation at a bound below the sum's unit.  The
upper-endpoint read (`keepLowerTop`) closes the module at `x - 5`
on `(1, 2)` at the bound `[2 : 1]`, decided with the side kept at
the lower endpoint and the interior point `3/2` through its theorem
(`keepLowerTop_all`); the two endpoints' reads distinguished at
`1 - 2x` on the same bracket, where the upper endpoint's read holds
and the lower endpoint's refuses at its price alone; and the price
conjunct's own isolation at `4 - x` on `(1, 6)` at the bound
`[6 : 1]`, the crossing losing the side while every other conjunct
holds. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground poly windowsep stage

private def u : BPair := BPair.unit

/-- `z² - 2` at its below-top list, the bracket `(5/4, 3/2)`. -/
private def ext2 : Ext := ⟨[⟨1, 3⟩, u], ⟨⟨6, 1⟩, 4⟩, ⟨⟨4, 1⟩, 2⟩⟩

/-! The bracket's side exchange, and the isolation at half the
separation at the width `[1 : 4]`. -/

example : bracketRead ext2 := by decide +kernel
example : isolRead ext2 1 4 := by decide +kernel

/-! The adjunction's own reads: the descent's naming identity at
`z³`, the Horner remainder at `3`, the product read `√2² = 2`, and
the reduction's equal members at the polynomial itself. -/

example : poly.divRead [⟨1, 3⟩, u] [u, u, u, ⟨2, 1⟩] := by decide +kernel
example : poly.hornerRead [⟨1, 3⟩, u, ⟨2, 1⟩] ⟨4, 1⟩ := by decide +kernel
example : poly.oneValue
    (poly.remMul [⟨1, 3⟩, u] [u, ⟨2, 1⟩] [u, ⟨2, 1⟩]) [⟨3, 1⟩] := by
  decide +kernel
example : reduceRead ext2 [⟨1, 3⟩, u, ⟨2, 1⟩] := by decide +kernel
example : ¬ reduceRead ext2 [u, ⟨2, 1⟩] := by decide +kernel

/-! The unit witness cleared at two: `z · z - (z² - 2) = 2`, the
value's inverse the witness against the clearing. -/

example : witnessRead ext2 [u, ⟨2, 1⟩] [u, ⟨2, 1⟩] [⟨1, 2⟩]
    ⟨3, 1⟩ := by decide +kernel

/-! The side reads at the priced brackets: `z` keeps the upper side
and `z - 3` the lower, the endpoint values clearing the width
against the derivative's fold, and the side kept at a bracket point
through the theorem tier. -/

example : sideUpper ext2 [u, ⟨2, 1⟩] 1 4 := by decide +kernel
example : sideLower ext2 [⟨1, 4⟩, ⟨2, 1⟩] 1 4 := by decide +kernel

example : unitC < evalC [u, ⟨2, 1⟩] ⟨⟨5, 1⟩, 3⟩ :=
  sideUpper_all ext2 [u, ⟨2, 1⟩] 1 4 (by decide +kernel) ⟨⟨5, 1⟩, 3⟩
    (by decide +kernel) (by decide +kernel)

/-! The priced side read at a composite bracket and a stated bound,
at `z + 5` on the bracket `(0, 2)` with the bound `[4 : 1]`: the
read decided at its six conjuncts, the side kept at the interior
point `1/2` through the theorem, a bracket reaching seven refused
and the bound one refused; the image-width price at the bracket's
own endpoints decided and through its theorem; and the lower side
at `-z - 5`, decided with the interior point through its theorem. -/

private def pLin : Poly := [⟨6, 1⟩, ⟨2, 1⟩]
private def pLinNeg : Poly := [⟨1, 6⟩, ⟨1, 2⟩]

example : keepUpper pLin ⟨u, 1⟩ ⟨⟨3, 1⟩, 1⟩ ⟨5, 1⟩ ⟨2, 1⟩ := by decide +kernel
example : ¬ keepUpper pLin ⟨u, 1⟩ ⟨⟨8, 1⟩, 1⟩ ⟨5, 1⟩ ⟨2, 1⟩ := by decide +kernel
example : ¬ keepUpper pLin ⟨u, 1⟩ ⟨⟨3, 1⟩, 1⟩ ⟨2, 1⟩ ⟨2, 1⟩ := by decide +kernel

example : unitC < evalC pLin ⟨⟨2, 1⟩, 2⟩ := by decide +kernel
example : unitC < evalC pLin ⟨⟨2, 1⟩, 2⟩ :=
  keepUpper_all pLin ⟨u, 1⟩ ⟨⟨3, 1⟩, 1⟩ ⟨5, 1⟩ ⟨2, 1⟩ (by decide +kernel)
    ⟨⟨2, 1⟩, 2⟩ (by decide +kernel) (by decide +kernel)

example : windowsep.mag (poly.eval pLin ⟨3, 1⟩ + (poly.eval pLin u).swap)
      * ground.bpow (⟨2, 1⟩ : BPair)
          ((poly.vnorm (poly.deriv pLin)).length - 1)
    ≤ windowsep.magFold (poly.deriv pLin) ⟨5, 1⟩ ⟨2, 1⟩
        * (⟨3, 1⟩ + u.swap) := by decide +kernel

example : windowsep.mag (poly.eval pLin ⟨3, 1⟩ + (poly.eval pLin u).swap)
      * ground.bpow (⟨2, 1⟩ : BPair)
          ((poly.vnorm (poly.deriv pLin)).length - 1)
    ≤ windowsep.magFold (poly.deriv pLin) ⟨5, 1⟩ ⟨2, 1⟩
        * (⟨3, 1⟩ + u.swap) :=
  eval_gap_le pLin u ⟨3, 1⟩ ⟨5, 1⟩ ⟨2, 1⟩ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : keepLower pLinNeg ⟨u, 1⟩ ⟨⟨3, 1⟩, 1⟩ ⟨5, 1⟩ ⟨2, 1⟩ := by decide +kernel

example : evalC pLinNeg ⟨⟨2, 1⟩, 2⟩ < unitC :=
  keepLower_all pLinNeg ⟨u, 1⟩ ⟨⟨3, 1⟩, 1⟩ ⟨5, 1⟩ ⟨2, 1⟩ (by decide +kernel)
    ⟨⟨2, 1⟩, 2⟩ (by decide +kernel) (by decide +kernel)

/-! The clearing conjunct's own isolation at `1 + z - z²` on the
bracket `(0, 2)`: at the bound `[0 : -1]` every further conjunct of
the read holds — the ordered endpoints, the lower endpoint's value
above the sum's unit, both endpoints inside the bound's segment,
and the width priced under that value against the derivative's fold
— while the bracket's upper point sits on the lower side, so the
read is the clearing's refusal alone. -/

private def pCtr : Poly := [⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 2⟩]

example : ¬ keepUpper pCtr ⟨u, 1⟩ ⟨⟨3, 1⟩, 1⟩ BPair.unit ⟨1, 2⟩ := by
  decide +kernel
example : evalC pCtr ⟨⟨3, 1⟩, 1⟩ < unitC := by decide +kernel

/-! The upper-endpoint side read (`keepLowerTop`), the same clause
carried at the bracket's other endpoint: `x - 5` on the bracket
`(1, 2)` at the bound `[2 : 1]` decided at its six conjuncts, the
side kept at the lower endpoint and at the interior point `3/2`
through the theorem (`keepLowerTop_all`).  Beside it the two
endpoints' reads distinguished at `1 - 2x` on the same bracket and
bound: the upper endpoint's read holds while the lower endpoint's
refuses — the lower endpoint's own value sits below the sum's unit
and both endpoints sit inside the bound's segment, so the refusal
is the lower endpoint's price alone, the one clause read at two
endpoints carrying two certificates.  The price conjunct's own
isolation closes the pair at `4 - x` on the bracket `(1, 6)` at the
bound `[6 : 1]`: the upper endpoint's value sits on the lower side,
the clearing, the ordered endpoints and both segment reads hold,
and the price refuses at the crossing, where the side is lost —
the conclusion failing at the lower endpoint.  The further three
conjuncts read their own isolations at `x - 20`: the bracket
reaching seven refused at the upper segment read alone (the value,
the price, the clearing and the lower segment read all holding),
the bound one refused there at the shrunk bound alone, and the
clearing refused at `x - 5` at the bound's lower-side second
datum. -/

private def pDrop : Poly := [⟨1, 6⟩, ⟨2, 1⟩]
private def pSlope : Poly := [⟨2, 1⟩, ⟨1, 3⟩]
private def pCross : Poly := [⟨5, 1⟩, ⟨1, 2⟩]

private theorem kltDrop :
    keepLowerTop pDrop ⟨⟨2, 1⟩, 1⟩ ⟨⟨3, 1⟩, 1⟩ ⟨3, 1⟩ ⟨2, 1⟩ := by
  decide +kernel

example : evalC pDrop ⟨⟨2, 1⟩, 1⟩ < unitC :=
  keepLowerTop_all pDrop ⟨⟨2, 1⟩, 1⟩ ⟨⟨3, 1⟩, 1⟩ ⟨3, 1⟩ ⟨2, 1⟩
    kltDrop ⟨⟨2, 1⟩, 1⟩
    (Or.inl (ground.CPair.oneValue_refl _)) (Or.inr (by decide +kernel))

example : evalC pDrop ⟨⟨4, 1⟩, 2⟩ < unitC := by decide +kernel

example : evalC pDrop ⟨⟨4, 1⟩, 2⟩ < unitC :=
  keepLowerTop_all pDrop ⟨⟨2, 1⟩, 1⟩ ⟨⟨3, 1⟩, 1⟩ ⟨3, 1⟩ ⟨2, 1⟩
    kltDrop ⟨⟨4, 1⟩, 2⟩
    (Or.inr (by decide +kernel)) (Or.inr (by decide +kernel))

private theorem kltSlope :
    keepLowerTop pSlope ⟨⟨2, 1⟩, 1⟩ ⟨⟨3, 1⟩, 1⟩ ⟨3, 1⟩ ⟨2, 1⟩ := by
  decide +kernel
example : ¬ keepLower pSlope ⟨⟨2, 1⟩, 1⟩ ⟨⟨3, 1⟩, 1⟩ ⟨3, 1⟩ ⟨2, 1⟩ := by
  decide +kernel

example : evalC pSlope ⟨⟨2, 1⟩, 1⟩ < unitC := by decide +kernel
example : ¬ (ofB (windowsep.magFold (poly.deriv pSlope) ⟨3, 1⟩ ⟨2, 1⟩)
      * ((⟨⟨3, 1⟩, 1⟩ : CPair) + CPair.swap ⟨⟨2, 1⟩, 1⟩)
    < CPair.swap (evalC pSlope ⟨⟨2, 1⟩, 1⟩)
        * ofB (ground.bpow (⟨2, 1⟩ : BPair)
            ((poly.vnorm (poly.deriv pSlope)).length - 1))) := by decide +kernel

example : evalC pSlope ⟨⟨4, 1⟩, 2⟩ < unitC :=
  keepLowerTop_all pSlope ⟨⟨2, 1⟩, 1⟩ ⟨⟨3, 1⟩, 1⟩ ⟨3, 1⟩ ⟨2, 1⟩
    kltSlope ⟨⟨4, 1⟩, 2⟩
    (Or.inr (by decide +kernel)) (Or.inr (by decide +kernel))

example : ¬ keepLowerTop pCross ⟨⟨2, 1⟩, 1⟩ ⟨⟨7, 1⟩, 1⟩ ⟨7, 1⟩ ⟨2, 1⟩ := by
  decide +kernel

example : BPair.unit < (⟨2, 1⟩ : BPair) := by decide +kernel
example : (⟨⟨2, 1⟩, 1⟩ : CPair) < ⟨⟨7, 1⟩, 1⟩ := by decide +kernel
example : evalC pCross ⟨⟨7, 1⟩, 1⟩ < unitC := by decide +kernel
example : cmag (⟨⟨2, 1⟩, 1⟩ : CPair) * ofB ⟨2, 1⟩ ≤ ofB ⟨7, 1⟩ := by decide +kernel
example : cmag (⟨⟨7, 1⟩, 1⟩ : CPair) * ofB ⟨2, 1⟩ ≤ ofB ⟨7, 1⟩ := by decide +kernel
example : ¬ (ofB (windowsep.magFold (poly.deriv pCross) ⟨7, 1⟩ ⟨2, 1⟩)
      * ((⟨⟨7, 1⟩, 1⟩ : CPair) + CPair.swap ⟨⟨2, 1⟩, 1⟩)
    < CPair.swap (evalC pCross ⟨⟨7, 1⟩, 1⟩)
        * ofB (ground.bpow (⟨2, 1⟩ : BPair)
            ((poly.vnorm (poly.deriv pCross)).length - 1))) := by decide +kernel

example : ¬ (evalC pCross ⟨⟨2, 1⟩, 1⟩ < unitC) := by decide +kernel

private def pFar : Poly := [⟨1, 21⟩, ⟨2, 1⟩]

example : ¬ keepLowerTop pFar ⟨⟨2, 1⟩, 1⟩ ⟨⟨8, 1⟩, 1⟩ ⟨6, 1⟩ ⟨2, 1⟩ := by
  decide +kernel
example : evalC pFar ⟨⟨8, 1⟩, 1⟩ < unitC := by decide +kernel
example : ofB (windowsep.magFold (poly.deriv pFar) ⟨6, 1⟩ ⟨2, 1⟩)
      * ((⟨⟨8, 1⟩, 1⟩ : CPair) + CPair.swap ⟨⟨2, 1⟩, 1⟩)
    < CPair.swap (evalC pFar ⟨⟨8, 1⟩, 1⟩)
        * ofB (ground.bpow (⟨2, 1⟩ : BPair)
            ((poly.vnorm (poly.deriv pFar)).length - 1)) := by decide +kernel
example : ¬ (cmag (⟨⟨8, 1⟩, 1⟩ : CPair) * ofB ⟨2, 1⟩ ≤ ofB ⟨6, 1⟩) := by
  decide +kernel

example : ¬ keepLowerTop pFar ⟨⟨2, 1⟩, 1⟩ ⟨⟨3, 1⟩, 1⟩ ⟨2, 1⟩ ⟨2, 1⟩ := by
  decide +kernel
example : cmag (⟨⟨2, 1⟩, 1⟩ : CPair) * ofB ⟨2, 1⟩ ≤ ofB ⟨2, 1⟩ := by
  decide +kernel
example : ¬ (cmag (⟨⟨3, 1⟩, 1⟩ : CPair) * ofB ⟨2, 1⟩ ≤ ofB ⟨2, 1⟩) := by
  decide +kernel

example : ¬ keepLowerTop pDrop ⟨⟨2, 1⟩, 1⟩ ⟨⟨3, 1⟩, 1⟩ ⟨3, 1⟩ ⟨1, 2⟩ := by
  decide +kernel
example : ¬ (BPair.unit < (⟨1, 2⟩ : BPair)) := by decide +kernel
