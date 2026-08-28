import MassGap.Stagesplit
import MassGap.Windowsep
/-!
The check module for `thm:windowsep`: the batteries re-read the
separation arithmetic's identity instances by kernel `decide` — the
magnitude carrier's laws at instances (the sum's cap, the product's
identity, the power's identity with its capped read, the memberwise
swap's blindness) with the two-sided read
and the swap's blindness landed as laws beside them, the height and the
radius pair at `z² - 2` with the beyond-radius evaluations keeping
the leading side at the radius and its balance partner — decided
and through `lead_upper` and `lead_lower`, the cubic `z³ - 2` at
the lower side and the radius binder refused inside the radius —
the coefficient and curvature folds' displayed values with the
coefficient fold's monomial read at the value representative's
keys and its cleared read at the variable's clearing — the bound's
first member taking the clearing two and the fold the clearing's
whole power — the Bézout solve at `(S, S')` (`elim.bezout_all` decided beside its own route,
with `topsUnequal`), and the separation's width read at `z² - 2` —
the width `[1 : 2]` a member with the
displayed clearing `Λ V` at `6` against `8`, a width beyond `δ`
refused.  The division descent is decided at its own output:
`stagesplit.gcdRead` against `gcdD`'s tuple at the chain
`(z-1)²(z+2)` with its derivative (gcd `z - 1`, the Bézout witness
`3P - z P' = -6(z-1)`), at the cleared-top class `2z - 1` against
itself and `(2z-1)²` against its derivative (the tops off the
integer monic, the class the unit-top spelling refused), at a
coprime pair (`z - 1` against `z + 2`, the divisor a constant and
the below-top list vacant), and at a vacant second input (the other
input the divisor outright); at two vacant inputs the tuple refuses,
the Bézout conjunct unsatisfiable against a divisor with a positive
top.  Beside them the walk's own invariant at its first step off
the chain, `3P - z P' = 6(1 - z)` before the content strip. -/
set_option maxHeartbeats 4000000

open ground poly elim windowsep

private def u : BPair := BPair.unit

/-! The magnitude carrier's laws at instances: the sum's magnitude
at or below the magnitudes' sum, the product's the magnitudes'
product, and the swap's blindness. -/

example : mag (⟨5, 1⟩ + ⟨1, 3⟩) ≤ mag ⟨5, 1⟩ + mag ⟨1, 3⟩ := by
  decide +kernel
example : mag (⟨5, 1⟩ + ⟨1, 3⟩) ≤ mag ⟨5, 1⟩ + mag ⟨1, 3⟩ :=
  mag_add_le ⟨5, 1⟩ ⟨1, 3⟩
example : mag (⟨1, 4⟩ + ⟨1, 3⟩) ≤ mag ⟨1, 4⟩ + mag ⟨1, 3⟩ := by
  decide +kernel
example : mag (⟨1, 4⟩ + ⟨1, 3⟩) ≤ mag ⟨1, 4⟩ + mag ⟨1, 3⟩ :=
  mag_add_le ⟨1, 4⟩ ⟨1, 3⟩
example : (mag (⟨1, 4⟩ * ⟨1, 3⟩)).oneValue
    (mag ⟨1, 4⟩ * mag ⟨1, 3⟩) := by decide +kernel
example : (mag (⟨1, 4⟩ * ⟨1, 3⟩)).oneValue
    (mag ⟨1, 4⟩ * mag ⟨1, 3⟩) := mag_mul ⟨1, 4⟩ ⟨1, 3⟩
example : (mag (⟨5, 1⟩ * ⟨1, 3⟩)).oneValue
    (mag ⟨5, 1⟩ * mag ⟨1, 3⟩) := by decide +kernel
example : (mag (⟨5, 1⟩ * ⟨1, 3⟩)).oneValue
    (mag ⟨5, 1⟩ * mag ⟨1, 3⟩) := mag_mul ⟨5, 1⟩ ⟨1, 3⟩
example : (mag (BPair.swap ⟨1, 4⟩)).oneValue (mag ⟨1, 4⟩) := by decide +kernel
example : (mag u).oneValue u := by decide +kernel

/-! The power's magnitude at the magnitude's power, decided and
through the theorem, with the capped read at a bound on the datum's
own magnitude. -/

example : (mag (bpow ⟨1, 3⟩ 3)).oneValue (bpow (mag ⟨1, 3⟩) 3) := by
  decide +kernel
example : (mag (bpow ⟨1, 3⟩ 3)).oneValue (bpow (mag ⟨1, 3⟩) 3) :=
  mag_bpow ⟨1, 3⟩ 3
example : mag (bpow ⟨1, 3⟩ 2) ≤ bpow ⟨4, 1⟩ 2 := by decide +kernel
example : mag (bpow ⟨1, 3⟩ 2) ≤ bpow ⟨4, 1⟩ 2 :=
  mag_bpow_le (by decide +kernel) 2

/-! The carrier's two-sided read and the swap's blindness as
literal equalities: a datum and its balance partner both sit at or
below the magnitude, the magnitude sits at or above the sum's unit,
a datum at or above the unit is its own magnitude, and the swap
leaves the magnitude unchanged on the nose. -/

example : (⟨1, 4⟩ : BPair) ≤ mag ⟨1, 4⟩ := by decide +kernel
example : (⟨1, 4⟩ : BPair) ≤ mag ⟨1, 4⟩ := le_mag ⟨1, 4⟩
example : (⟨5, 1⟩ : BPair).swap ≤ mag ⟨5, 1⟩ := by decide +kernel
example : (⟨5, 1⟩ : BPair).swap ≤ mag ⟨5, 1⟩ := swap_le_mag ⟨5, 1⟩
example : BPair.unit ≤ mag ⟨1, 4⟩ := by decide +kernel
example : BPair.unit ≤ mag ⟨1, 4⟩ := unitLe_mag ⟨1, 4⟩
example : mag ⟨5, 1⟩ = ⟨5, 1⟩ := by decide +kernel
example : mag ⟨5, 1⟩ = ⟨5, 1⟩ := mag_unitLe (by decide +kernel)
example : mag ((⟨1, 4⟩ : BPair).swap) = mag ⟨1, 4⟩ := by decide +kernel
example : mag ((⟨1, 4⟩ : BPair).swap) = mag ⟨1, 4⟩ := mag_swap ⟨1, 4⟩

/-! The height and the radius pair at `S = z² - 2`: the leading
magnitude one, the height two, the radius `[3 : 1]`. -/

private def sQ : Poly := [⟨1, 3⟩, u, ⟨2, 1⟩]

example : (height sQ).oneValue ⟨3, 1⟩ := by decide +kernel
example : (radiusN sQ).oneValue ⟨4, 1⟩ := by decide +kernel
example : (radiusD sQ).oneValue ⟨2, 1⟩ := by decide +kernel

/-! Beyond the radius the leading term dominates: the two sides at
`S = z² - 2` and at `C = z³ - 2`, each decided and through
`lead_upper`/`lead_lower`, at the radius and at its balance
partner. -/

private def cQ : Poly := [⟨1, 3⟩, u, u, ⟨2, 1⟩]   -- z³ − 2

example : radiusN sQ ≤ mag ⟨4, 1⟩ * radiusD sQ := by decide +kernel
example : BPair.unit < poly.eval sQ ⟨4, 1⟩ := by decide +kernel
example : BPair.unit < poly.eval sQ ⟨4, 1⟩ :=
  lead_upper sQ ⟨4, 1⟩ (by decide +kernel) (by decide +kernel)
example : BPair.unit < poly.eval sQ ⟨1, 4⟩ := by decide +kernel
example : BPair.unit < poly.eval sQ ⟨1, 4⟩ :=
  lead_upper sQ ⟨1, 4⟩ (by decide +kernel) (by decide +kernel)
example : poly.eval cQ ⟨1, 4⟩ < BPair.unit := by decide +kernel
example : poly.eval cQ ⟨1, 4⟩ < BPair.unit :=
  lead_lower cQ ⟨1, 4⟩ (by decide +kernel) (by decide +kernel)
-- the radius binder is load-bearing: inside the radius the lead is above the unit and the value below
example : ¬ (radiusN sQ ≤ mag ⟨2, 1⟩ * radiusD sQ) := by decide +kernel
example : BPair.unit < top (poly.vnorm sQ) * ground.bpow ⟨2, 1⟩ ((poly.vnorm sQ).length - 1) := by
  decide +kernel
example : poly.eval sQ ⟨2, 1⟩ < BPair.unit := by decide +kernel

/-! The height prices every coefficient's magnitude at the value's
representative, and the height and the radius pair are blind to the
memberwise swap — the side theorem's lower route reads the negated
polynomial at the same radius. -/

example : mag (⟨1, 3⟩ : BPair) ≤ height sQ :=
  mag_le_height (P := sQ)
    (ground.mem_of_countOf_pos _ _ (by decide +kernel))
example : mag (⟨2, 1⟩ : BPair) ≤ height sQ :=
  mag_le_height (P := sQ)
    (ground.mem_of_countOf_pos _ _ (by decide +kernel))
example : height (poly.neg sQ) = height sQ := by decide +kernel
example : height (poly.neg sQ) = height sQ := height_neg sQ
example : radiusN (poly.neg sQ) = radiusN sQ := by decide +kernel
example : radiusN (poly.neg sQ) = radiusN sQ := radiusN_neg sQ
example : radiusD (poly.neg sQ) = radiusD sQ := by decide +kernel
example : radiusD (poly.neg sQ) = radiusD sQ := radiusD_neg sQ

/-! The folds' displayed values at `S` and its derivative: the
coefficient fold caps the evaluations over the radius, and the
curvature fold reads the one `i = 2` splitting count. -/

example : (magFold sQ ⟨4, 1⟩ ⟨2, 1⟩).oneValue ⟨12, 1⟩ := by decide +kernel
example : (curvFold sQ ⟨4, 1⟩ ⟨2, 1⟩).oneValue ⟨2, 1⟩ := by decide +kernel
example : mag (eval sQ ⟨4, 1⟩) ≤ magFold sQ ⟨4, 1⟩ ⟨2, 1⟩ := by
  decide +kernel

/-! The coefficient fold at the monomial fold over the value
representative's keys, decided and through the theorem. -/

example : (magFold sQ ⟨4, 1⟩ ⟨2, 1⟩).oneValue
    (ground.famFold BPair.add BPair.unit
      (fun i => mag (ground.getAt BPair.unit (poly.vnorm sQ) i)
        * ground.bpow ⟨4, 1⟩ i
        * ground.bpow ⟨2, 1⟩ ((poly.vnorm sQ).length - 1 - i))
      (List.range (poly.vnorm sQ).length)) := by decide +kernel

example : (magFold sQ ⟨4, 1⟩ ⟨2, 1⟩).oneValue
    (ground.famFold BPair.add BPair.unit
      (fun i => mag (ground.getAt BPair.unit (poly.vnorm sQ) i)
        * ground.bpow ⟨4, 1⟩ i
        * ground.bpow ⟨2, 1⟩ ((poly.vnorm sQ).length - 1 - i))
      (List.range (poly.vnorm sQ).length)) :=
  magFold_read sQ ⟨4, 1⟩ ⟨2, 1⟩

/-! The coefficient fold at the cleared list: the bound's first
member takes the clearing two and the fold takes the clearing's
whole power at the representative's top key, decided and through
the theorem. -/

example : (magFold (poly.clearVar (poly.vnorm sQ) 2
      ((poly.vnorm sQ).length - 1)) (⟨5, 1⟩ * BPair.ofPos 2) ⟨2, 1⟩).oneValue
    (ground.bpow (BPair.ofPos 2) ((poly.vnorm sQ).length - 1)
      * magFold sQ ⟨5, 1⟩ ⟨2, 1⟩) := by decide +kernel

example : (magFold (poly.clearVar (poly.vnorm sQ) 2
      ((poly.vnorm sQ).length - 1)) (⟨5, 1⟩ * BPair.ofPos 2) ⟨2, 1⟩).oneValue
    (ground.bpow (BPair.ofPos 2) ((poly.vnorm sQ).length - 1)
      * magFold sQ ⟨5, 1⟩ ⟨2, 1⟩) :=
  magFold_clearVar sQ 2 ⟨5, 1⟩ ⟨2, 1⟩

/-! The Bézout solve at `(S, S')`, the recorded consumer arriving:
the stated site and the adjugate row's identity, with the
resultant's magnitude eight and the cofactor row `-2 z`. -/

example : topsUnequal sQ (deriv sQ) := by decide +kernel
example : poly.oneValue
    (poly.add (poly.mul (bezoutA sQ (deriv sQ)) sQ)
      (poly.mul (bezoutB sQ (deriv sQ)) (deriv sQ)))
    [resultant sQ (deriv sQ)] := by decide +kernel
example : poly.oneValue
    (poly.add (poly.mul (bezoutA sQ (deriv sQ)) sQ)
      (poly.mul (bezoutB sQ (deriv sQ)) (deriv sQ)))
    [resultant sQ (deriv sQ)] := bezout_all sQ (deriv sQ) (by decide +kernel)
example : (mag (resultant sQ (deriv sQ))).oneValue ⟨9, 1⟩ := by decide +kernel
example : (magFold (bezoutB sQ (deriv sQ)) ⟨4, 1⟩ ⟨2, 1⟩).oneValue
    ⟨7, 1⟩ := by decide +kernel

/-! The separation's width read at `S`: the cleared `Λ V` reads six
against the resultant's eight, so the width `[1 : 2]` is a member
— both displayed comparisons — and the width `[3 : 2]` is refused
at the second display. -/

example : sepRead sQ 1 2 := by decide +kernel
example : ¬ sepRead sQ 3 2 := by decide +kernel

/-! The reads at the value's representative: a tail of equal-membered
coefficients moves the representative and every read holds — the
radius pair, the acceptance and the refusal at the moved lists — and
the congruence theorem moves the width read across two
representatives of one value, the walk instance's own route. -/

example : poly.vnorm [⟨1, 3⟩, ⟨2, 2⟩, ⟨3, 3⟩] = [⟨1, 3⟩] := by decide +kernel
example : poly.vnorm sQ = sQ := by decide +kernel
example : (radiusD (sQ ++ [⟨3, 3⟩])).oneValue ⟨2, 1⟩ := by decide +kernel
example : (radiusN (sQ ++ [⟨3, 3⟩])).oneValue ⟨4, 1⟩ := by decide +kernel
example : sepRead (sQ ++ [⟨2, 2⟩]) 1 2 := by decide +kernel
example : ¬ sepRead (sQ ++ [⟨2, 2⟩]) 3 2 := by decide +kernel
example : sepRead ([⟨1, 3⟩, u, ⟨2, 1⟩, ⟨5, 5⟩]) 1 2 ↔ sepRead sQ 1 2 :=
  sepRead_congr (by decide +kernel) 1 2

/-! The division descent, decided at its own output.  The chain
`P = (z-1)²(z+2) = z³ - 3z + 2` against `P'`, the cleared-top pair
`W = 2z - 1` against itself and `W²` against its derivative, the
coprime pair `z - 1` against `z + 2`, and the vacant inputs. -/

private def pC : Poly := [⟨3, 1⟩, ⟨1, 4⟩, u, ⟨2, 1⟩]
private def wC : Poly := [⟨1, 2⟩, ⟨3, 1⟩]
private def w2C : Poly := [⟨2, 1⟩, ⟨1, 5⟩, ⟨5, 1⟩]
private def aC : Poly := [⟨1, 2⟩, ⟨2, 1⟩]
private def bC : Poly := [⟨3, 1⟩, ⟨2, 1⟩]

private def dChain : GcdData := gcdD pC (deriv pC)
private def dSelf : GcdData := gcdD wC wC
private def dSq : GcdData := gcdD w2C (deriv w2C)
private def dCop : GcdData := gcdD aC bC
private def dOne : GcdData := gcdD aC []
private def dNil : GcdData := gcdD [] []

example : stagesplit.gcdRead pC (deriv pC) dChain.g dChain.A dChain.B
    dChain.u dChain.v dChain.top dChain.cA dChain.cB dChain.c := by
  decide +kernel
example : poly.oneValue (poly.topped dChain.g dChain.top) aC := by
  decide +kernel

example : stagesplit.gcdRead wC wC dSelf.g dSelf.A dSelf.B dSelf.u
    dSelf.v dSelf.top dSelf.cA dSelf.cB dSelf.c := by decide +kernel
example : poly.oneValue (poly.topped dSelf.g dSelf.top) wC := by
  decide +kernel

example : stagesplit.gcdRead w2C (deriv w2C) dSq.g dSq.A dSq.B dSq.u
    dSq.v dSq.top dSq.cA dSq.cB dSq.c := by decide +kernel
example : poly.oneValue (poly.topped dSq.g dSq.top) wC := by decide +kernel

example : stagesplit.gcdRead aC bC dCop.g dCop.A dCop.B dCop.u dCop.v
    dCop.top dCop.cA dCop.cB dCop.c := by decide +kernel
example : dCop.g = [] := by decide +kernel

example : stagesplit.gcdRead aC [] dOne.g dOne.A dOne.B dOne.u dOne.v
    dOne.top dOne.cA dOne.cB dOne.c := by decide +kernel
example : poly.oneValue (poly.topped dOne.g dOne.top) aC := by
  decide +kernel

example : ¬ stagesplit.gcdRead [] [] dNil.g dNil.A dNil.B dNil.u dNil.v
    dNil.top dNil.cA dNil.cB dNil.c := by decide +kernel

/-! The walk's row invariant at the chain's first step: the seeded
rows read `3 P - z P' = 6 (1 - z)`, the multiplier `6` the content
the step strips off the remainder. -/

example : poly.oneValue
    (poly.add (poly.mul [⟨4, 1⟩] pC) (poly.mul [u, ⟨1, 2⟩] (deriv pC)))
    (poly.mul [⟨7, 1⟩] [⟨2, 1⟩, ⟨1, 2⟩]) := by decide +kernel
