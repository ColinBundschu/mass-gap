import MassGap.Rankstable
import MassGap.Genericlift
/-!
`lem:chaininstances` — the rank divisors of the chain's
comparisons (`lem:rankstable`(iii)) close on 37 records over the
depth-two charge-one closure, every divisor read at `n := d_f`,
the fundamental count (`con:places`).

Per band family the record is the *excess gap*: at
`lem:rankstable`(i)'s word data the cleared read
`dfQ(member) = dfQ(f) + gap` holds as polynomials in the count
(`gapRead` at `rankstable.casPoly`, the family's two words against
the fundamental's own words `[1]`, `[]`), and the gap itself is
the quadratic `c n (a n + s)` at an upper witness and `c n g` at
`s + g = a n` at a lower one (`gapPolyOf`, the coefficient list
`[0, ±c s, c a]` in the Horner order `casPoly` itself carries).
The eight families are `ω₂+ω₁*` at `2n g`, `1 + g = n`;
`ω₃+2ω₁*` at `4n g`, `1 + g = n`; `ω₃+ω₂*` at `4n g`,
`2 + g = n`; `2ω₁+ω₁*` at `2n (n+1)`; `ω₁+ω₂+2ω₁*` at
`2n (2n+1)`; `ω₁+ω₂+ω₂*` at `2n g`, `1 + g = 2n`; `3ω₁+2ω₁*` at
`4n (n+2)`; and `3ω₁+ω₂*` at `4n (n+1)`, each carrying its reach
clearance read at `n`, the clearance residue's successor
(`lem:rankstable`(ii)): `6, 7, 8, 5, 6, 7, 5, 6`.

The frontier-binding comparisons are the balance pairs
`⟨gap_i : gap_j⟩` over the family pairs (`places.pairsOf` at the
family count, each earlier family against each later one), a
comparison's settled point the upper of its two clearances; and
the stencil cap is `3 g` at `1 + g = n²`, settled from the rank
two.  `recs` is those three tiers in that order, eight records,
twenty-eight and one.

The *classification* is the equal-members reads in the rank
domain, five, every one below a compared family's clearance, one
cross-multiplied evaluation each: `ω₃+ω₂*`'s gap at the rank two
against its clearance eight, and the binding pairs
`(2ω₁+ω₁*, ω₁+ω₂+ω₂*)` at two against seven,
`(ω₂+ω₁*, ω₃+ω₂*)` at three against eight,
`(ω₃+2ω₁*, 2ω₁+ω₁*)` at three against seven, and
`(ω₃+ω₂*, 2ω₁+ω₁*)` at five against eight — the table `classif`,
entered once, each record's root list its lookup at the record's
own family places.

Each record carries two reads.  `sideCert` is the hypothesis pair
of `lem:genericlift`'s side theorems: the divisor's radius cleared
at the settled point (`genericlift.radiusClears`, the leading-term
bound `[c + H : c]`) beside the leading coefficient's own side
(`genericlift.topUpper` or `genericlift.topLower`, the top read at
the value's representative), so `genericlift.sideUpper` and
`genericlift.sideLower` hold the divisor's leading side at every
rank at or beyond that point.  `rootsCert` reads the window below
it, the ranks from the domain's floor, here two: a counted rank
ties the sum's unit, a cleared rank off the roots sits on the
divisor's own leading side, and a below-clearance rank off the
roots sits off the sum's unit, so the classification's five
entries are the domain's whole equal-members list and the leading
side holds at every cleared rank of the window.  `recsRead` joins the
record count, the eight families' cleared reads, and the two
certificates over the whole list.
-/

namespace chaininstances
open ground

/-- The excess gap as a quadratic in the count: the coefficient
list `[0, ±c s, c a]` at the Horner order, the linear key on the
leading side at an upper witness `c n (a n + s)` and on the
trailing side at a lower one, `c n g` at `s + g = a n`. -/
def gapPolyOf (c a s : Nat) (up : Bool) : poly.Poly :=
  [⟨ground.posOfSucc 0, ground.posOfSucc 0⟩,
   if up then ⟨ground.posOfSucc (c * s), ground.posOfSucc 0⟩
   else ⟨ground.posOfSucc 0, ground.posOfSucc (c * s)⟩,
   ⟨ground.posOfSucc (c * a), ground.posOfSucc 0⟩]

set_option genInjectivity false in
/-- A band family's committed datum: `lem:rankstable`(i)'s two
words, the gap's three naturals with its witness side, and the
reach clearance read at the count. -/
structure Fam where
  P : List Nat
  Q : List Nat
  c : Nat
  a : Nat
  s : Nat
  up : Bool
  cl : Nat

/-- The eight band families of the depth-two charge-one closure,
in the displayed order `ω₂+ω₁*`, `ω₃+2ω₁*`, `ω₃+ω₂*`,
`2ω₁+ω₁*`, `ω₁+ω₂+2ω₁*`, `ω₁+ω₂+ω₂*`, `3ω₁+2ω₁*`,
`3ω₁+ω₂*`. -/
def fams : List Fam :=
  [⟨[0, 1], [1], 2, 1, 1, false, 6⟩,
   ⟨[0, 0, 1], [2], 4, 1, 1, false, 7⟩,
   ⟨[0, 0, 1], [0, 1], 4, 1, 2, false, 8⟩,
   ⟨[2], [1], 2, 1, 1, true, 5⟩,
   ⟨[1, 1], [2], 2, 2, 1, true, 6⟩,
   ⟨[1, 1], [0, 1], 2, 2, 1, false, 7⟩,
   ⟨[3], [2], 4, 1, 2, true, 5⟩,
   ⟨[3], [0, 1], 4, 1, 1, true, 6⟩]

/-- A family's excess gap. -/
def gapOf (F : Fam) : poly.Poly := gapPolyOf F.c F.a F.s F.up

/-- The cleared read `dfQ(member) = dfQ(f) + gap` at
`lem:rankstable`(i)'s quadratic, the family's member against the
fundamental's raised by the gap. -/
def gapRead (F : Fam) : Prop :=
  poly.oneValue (rankstable.casPoly F.P F.Q)
    (poly.add (rankstable.casPoly [1] []) (gapOf F))

instance (F : Fam) : Decidable (gapRead F) :=
  inferInstanceAs (Decidable (poly.oneValue _ _))

set_option genInjectivity false in
/-- A rank-divisor record: the divisor, its domain's floor, its
own clearance (a comparison's ranks are those clearing its
families' reaches), its settled point, and the domain's
equal-members ranks below the settled point. -/
structure Rec where
  div : poly.Poly
  lo : Nat
  cl : Nat
  an : Nat
  roots : List Nat

/-- The classification, entered once: the family places and the
rank at each of the five equal-members reads. -/
def classif : List (Nat × Nat × Nat) :=
  [(2, 2, 2), (0, 2, 3), (1, 3, 3), (2, 3, 5), (3, 5, 2)]

/-- The classification's lookup at a record's family places. -/
private def rootsAt (i j : Nat) : List Nat :=
  (classif.filter
    (fun t => decide (t.1 = i) && decide (t.2.1 = j))).map
    (fun t => t.2.2)

/-- The upper of two counts. -/
private def maxNat (x y : Nat) : Nat := if x ≤ y then y else x

/-- The family at a place. -/
private def famAt (i : Nat) : Fam :=
  ground.getAt ⟨[], [], 0, 0, 0, false, 0⟩ fams i

/-- The stencil cap `3 g` at `1 + g = n²`, the quadratic
`3 n² - 3`. -/
def capPoly : poly.Poly :=
  [⟨ground.posOfSucc 0, ground.posOfSucc 3⟩,
   ⟨ground.posOfSucc 0, ground.posOfSucc 0⟩,
   ⟨ground.posOfSucc 3, ground.posOfSucc 0⟩]

/-- The 37 records: the eight families' excess gaps at their own
clearances, the twenty-eight frontier-binding comparisons over
`places.pairsOf` at the family count, each settled at the upper of
its two clearances, and the stencil cap settled from the rank
two. -/
def recs : List Rec :=
  (List.range fams.length).map
      (fun i => ⟨gapOf (famAt i), 2, (famAt i).cl, (famAt i).cl,
        rootsAt i i⟩)
    ++ (places.pairsOf fams.length).map
      (fun pr =>
        ⟨poly.add (gapOf (famAt pr.1)) (poly.neg (gapOf (famAt pr.2))),
         2, maxNat (famAt pr.1).cl (famAt pr.2).cl,
         maxNat (famAt pr.1).cl (famAt pr.2).cl,
         rootsAt pr.1 pr.2⟩)
    ++ [⟨capPoly, 2, 2, 2, []⟩]

/-- The settled side's certificate, `lem:genericlift`'s side
theorems' hypothesis pair: the radius cleared at the settled point
beside the leading coefficient's own side. -/
def sideCert (R : Rec) : Prop :=
  genericlift.radiusClears R.div (ground.posOfSucc (R.an - 1))
  ∧ (genericlift.topUpper R.div ∨ genericlift.topLower R.div)

instance (R : Rec) : Decidable (sideCert R) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The window below the settled point, the ranks from the
domain's floor: at a counted rank the divisor's evaluation ties
the sum's unit; at a cleared rank off the roots it sits on the
divisor's own leading side; below the clearance off the roots it
sits off the sum's unit. -/
def rootsCert (R : Rec) : Prop :=
  ((List.range R.an).filter (fun k => R.lo ≤ k)).all (fun k =>
    if 0 < ground.countOf k R.roots then
      decide ((poly.eval R.div
        ⟨ground.posOfSucc k, ground.posOfSucc 0⟩).oneValue
          ground.BPair.unit)
    else if R.cl ≤ k then
      (decide (genericlift.topUpper R.div)
        && decide (ground.BPair.unit < poly.eval R.div
          ⟨ground.posOfSucc k, ground.posOfSucc 0⟩))
      || (decide (genericlift.topLower R.div)
        && decide (poly.eval R.div
          ⟨ground.posOfSucc k, ground.posOfSucc 0⟩ < ground.BPair.unit))
    else
      !(decide ((poly.eval R.div
        ⟨ground.posOfSucc k, ground.posOfSucc 0⟩).oneValue
          ground.BPair.unit))) = true

instance (R : Rec) : Decidable (rootsCert R) :=
  inferInstanceAs (Decidable (_ = _))

/-- The lemma's whole read: the record count, the eight families'
cleared reads, and both certificates over the record list. -/
def recsRead : Prop :=
  recs.length = 37
  ∧ (fams.all (fun F => decide (gapRead F))) = true
  ∧ (recs.all (fun R => decide (sideCert R))) = true
  ∧ (recs.all (fun R => decide (rootsCert R))) = true

instance : Decidable recsRead :=
  inferInstanceAs (Decidable (_ ∧ _))

end chaininstances
