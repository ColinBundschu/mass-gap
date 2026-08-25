import MassGap.Elim
/-!
The check module for `def:elim`: the batteries re-read the
elimination's identity instances by kernel `decide` — the first-row
fold's minors, Sylvester's identity at the pivot-bordered minors
(the first naming among the steps), the resultant at the shift
matrix with its stated site, and the adjugate row's solve (the
rank instances land with the descent's consumer).

The vector-valued index fold closes the module: a committed
two-member family at width two, its fold against the hand value,
and each read of the kit decided beside its own theorem instance —
the width, the head split, the pointwise congruence and split, the
pairing and the action against the fold, the double range's
exchange and the delta pick, with the refusal at a guard off its
key.

The descent's own scale pins close the module at a committed
matrix, the `B_2` stacked simple raisings over the unit-content
monomials: the leading blocks at 8, 16, 24, 32 and 48 keys read
their pivot counts, a doubled row dropping the count by one at the
dependent row, and the whole 76-by-61 shape reads its pivot count
and its kernel dimension 3 — `sertables`' own invariant count.  The
stacked shape's larger partner, `C_3` at 124 rows and 90 keys,
reads its pivot count 87 beside its kernel dimension 3.

The descent runs on sparse rows, each working row the column-keyed
list of its off-unit entries, so the merge's three keys take their
own pins above: the pivot-row-alone key's fill-in, the row-alone
key's scaling and the joint key's whole arithmetic, each at a shape
whose pivot count moves when its case is withdrawn, beside the two
entry identities the sparse reads take off the dense step and
`step_unit`'s discharge at a row reading the sum's unit in the
pivot column.

Budget exception: the at-scale pins at the two committed shapes —
the rank reads with the kernel tier's back solves, each length pin
re-running the forward descent before its solve (the double walk
`descGo`'s two seeds at one recursion) — are the module's cost,
the elimination walked whole at the stated data.

The null-collection reads close the module: at unit-tailed rows
the collection is vacant, its rows binder isolated at one off-unit
row, and the span read's own rows binder isolated at a single
off-unit row carrying itself.

The determinant kit's reads ride at the end: every row scaled at
a `2 × 2` list reading the scale's square against the determinant,
the block-triangular list at a `2 + 1` split reading its blocks'
product, and the slab reduction at a `1 + 1` split reading the
scale against the reduced list's determinant, its positive-order
binder refused at a vacant leading slab where the reduced trailing
slab truncates away.

The pivot's places close the module: at a symmetric order-3 datum
the selection at the places `[2, 0]` read against its literal, the
join's assembled block datum at the places `[1]` and `[2, 0]`
decided beside the theorem's own read, and the conjugation at the
places' permutation matrix reading the selected block, decided and
through the theorem; the selection's exchange at the symmetric
datum rides beside them, with the occupied-row binder isolated at
the order-1 datum where the vacant row key list parts the exchange
and every other hypothesis reads true.

The determinant product tier closes the module: the square lists'
product at its factors' determinants, the stated diagonal's running
product, the polynomial diagonal's and the embedded scalar list's
minors, the polynomial product's minor and the entrywise
congruence, each decided and through its theorem; with the shared
order's binder refused at the order-one list against the order-two
one and at its polynomial twin, the embedded list's square binder
at a two-by-three rectangle, and the entrywise binder at one
doubled entry.
-/

set_option maxRecDepth 8192

open ground poly elim

/-! The first-row fold. -/

example : BPair.oneValue
    (minor [[⟨2, 1⟩, ⟨3, 1⟩], [⟨4, 1⟩, ⟨5, 1⟩]]) ⟨1, 3⟩ := by decide +kernel

example : BPair.oneValue
    (minor [[⟨2, 1⟩, ⟨3, 1⟩, ⟨4, 1⟩],
            [⟨5, 1⟩, ⟨6, 1⟩, ⟨7, 1⟩],
            [⟨8, 1⟩, ⟨9, 1⟩, ⟨11, 1⟩]]) ⟨1, 4⟩ := by decide +kernel

/-- A repeated row reads equal members. -/
example : BPair.oneValue
    (minor [[⟨2, 1⟩, ⟨3, 1⟩], [⟨2, 1⟩, ⟨3, 1⟩]]) BPair.unit := by decide +kernel

/-! Sylvester's identity at the pivot-bordered minors of one 4x4:
the displayed first naming `b(1)_ij + a_i1 a_1j = a_11 a_ij` at the
empty leading lists, then the first and the second step. -/

example : sylvesterRead
    [[⟨2, 1⟩, ⟨3, 1⟩, ⟨1, 2⟩, ⟨4, 1⟩],
     [⟨5, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 3⟩],
     [⟨1, 2⟩, ⟨6, 1⟩, ⟨3, 1⟩, ⟨2, 1⟩],
     [⟨4, 1⟩, ⟨1, 4⟩, ⟨5, 1⟩, ⟨1, 1⟩]] 0 2 3 := by decide +kernel

example : sylvesterRead
    [[⟨2, 1⟩, ⟨3, 1⟩, ⟨1, 2⟩, ⟨4, 1⟩],
     [⟨5, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 3⟩],
     [⟨1, 2⟩, ⟨6, 1⟩, ⟨3, 1⟩, ⟨2, 1⟩],
     [⟨4, 1⟩, ⟨1, 4⟩, ⟨5, 1⟩, ⟨1, 1⟩]] 1 2 3 := by decide +kernel

example : sylvesterRead
    [[⟨2, 1⟩, ⟨3, 1⟩, ⟨1, 2⟩, ⟨4, 1⟩],
     [⟨5, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 3⟩],
     [⟨1, 2⟩, ⟨6, 1⟩, ⟨3, 1⟩, ⟨2, 1⟩],
     [⟨4, 1⟩, ⟨1, 4⟩, ⟨5, 1⟩, ⟨1, 1⟩]] 2 2 3 := by decide +kernel

example : sylvesterRead
    [[⟨2, 1⟩, ⟨3, 1⟩, ⟨1, 2⟩, ⟨4, 1⟩],
     [⟨5, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 3⟩],
     [⟨1, 2⟩, ⟨6, 1⟩, ⟨3, 1⟩, ⟨2, 1⟩],
     [⟨4, 1⟩, ⟨1, 4⟩, ⟨5, 1⟩, ⟨1, 1⟩]] 2 3 3 := by decide +kernel

/-! The resultant: `Res(z - 2, z - 3)` reads the balance partner of
one, and `Res(z^2 - 1, z - 2) = q(1) q(-1) = 3`. -/

example : BPair.oneValue
    (resultant [⟨1, 3⟩, ⟨2, 1⟩] [⟨1, 4⟩, ⟨2, 1⟩]) ⟨1, 2⟩ := by decide +kernel

example : BPair.oneValue
    (resultant [⟨1, 2⟩, ⟨1, 1⟩, ⟨2, 1⟩] [⟨1, 3⟩, ⟨2, 1⟩]) ⟨4, 1⟩ := by
  decide +kernel

/-! The adjugate row's solve `A p + B q = Res`, each instance
decided beside the theorem's own route, and the solve refused at
the vacant shift matrix: at two polynomials of vanishing degree
the matrix is empty, its determinant the product's one against the
solve's own unit. -/

private def zMinusTwo : poly.Poly := [⟨1, 3⟩, ⟨2, 1⟩]
private def zMinusThree : poly.Poly := [⟨1, 4⟩, ⟨2, 1⟩]
private def zSqMinusOne : poly.Poly := [⟨1, 2⟩, ⟨1, 1⟩, ⟨2, 1⟩]

example : poly.oneValue
    (poly.add (poly.mul (bezoutA zMinusTwo zMinusThree) zMinusTwo)
      (poly.mul (bezoutB zMinusTwo zMinusThree) zMinusThree))
    [resultant zMinusTwo zMinusThree] := by decide +kernel

example : poly.oneValue
    (poly.add (poly.mul (bezoutA zMinusTwo zMinusThree) zMinusTwo)
      (poly.mul (bezoutB zMinusTwo zMinusThree) zMinusThree))
    [resultant zMinusTwo zMinusThree] :=
  bezout_all zMinusTwo zMinusThree (by decide +kernel)

example : poly.oneValue
    (poly.add (poly.mul (bezoutA zSqMinusOne zMinusTwo) zSqMinusOne)
      (poly.mul (bezoutB zSqMinusOne zMinusTwo) zMinusTwo))
    [resultant zSqMinusOne zMinusTwo] := by decide +kernel

example : poly.oneValue
    (poly.add (poly.mul (bezoutA zSqMinusOne zMinusTwo) zSqMinusOne)
      (poly.mul (bezoutB zSqMinusOne zMinusTwo) zMinusTwo))
    [resultant zSqMinusOne zMinusTwo] :=
  bezout_all zSqMinusOne zMinusTwo (by decide +kernel)

example : ¬ poly.oneValue
    (poly.add (poly.mul (bezoutA [⟨3, 1⟩] [⟨4, 1⟩]) [⟨3, 1⟩])
      (poly.mul (bezoutB [⟨3, 1⟩] [⟨4, 1⟩]) [⟨4, 1⟩]))
    [resultant [⟨3, 1⟩] [⟨4, 1⟩]] := by decide +kernel

/-! The Bezout row at the descent: the walk row against the fold
row at the value, decided and read through the theorem's route at
the decided square frame. -/

example : poly.oneValue
    (bezoutBD [⟨1, 2⟩, ⟨1, 1⟩, ⟨2, 1⟩] [⟨1, 3⟩, ⟨2, 1⟩])
    (bezoutB [⟨1, 2⟩, ⟨1, 1⟩, ⟨2, 1⟩] [⟨1, 3⟩, ⟨2, 1⟩]) := by decide +kernel

example : poly.oneValue
    (bezoutBD [⟨1, 2⟩, ⟨1, 1⟩, ⟨2, 1⟩] [⟨1, 3⟩, ⟨2, 1⟩])
    (bezoutB [⟨1, 2⟩, ⟨1, 1⟩, ⟨2, 1⟩] [⟨1, 3⟩, ⟨2, 1⟩]) :=
  bezoutBD_eq _ _ (by decide +kernel)

/-! The pair carrier's descent: the walk against the fold at the
cross-multiplied read on an occupied square site, decided and read
through the theorem's route, with the occupancy fold refusing a
vacant second member. -/

private def qM : List (List poly.PPair) :=
  [[(poly.one, poly.one), ([⟨1, 3⟩], poly.one)],
   [([⟨2, 1⟩], [⟨3, 1⟩]), (poly.one, [⟨2, 1⟩])]]

example : elim.matOcc qM = true := by decide +kernel
example : elim.matOcc [[(poly.one, [])]] = false := by decide +kernel

example : poly.oneValue
    (poly.mul (elim.pairDetD qM).1
      (elim.minorO poly.ppairOps poly.pnormPair id qM).2)
    (poly.mul (elim.minorO poly.ppairOps poly.pnormPair id qM).1
      (elim.pairDetD qM).2) := by decide +kernel

example : poly.oneValue
    (poly.mul (elim.pairDetD qM).1
      (elim.minorO poly.ppairOps poly.pnormPair id qM).2)
    (poly.mul (elim.minorO poly.ppairOps poly.pnormPair id qM).1
      (elim.pairDetD qM).2) :=
  elim.pairDetD_eq qM (by decide +kernel)

/-! The square binder isolated at an occupied ragged frame, the
walk at a genuine second pivot at the three-by-three, and the
occupancy binder of the walk value's second-member read. -/

private def qRag : List (List poly.PPair) :=
  [[(poly.one, poly.one), ([⟨1, 3⟩], poly.one)],
   [([⟨2, 1⟩], [⟨3, 1⟩])]]

example : elim.matOcc qRag = true := by decide +kernel
example : ¬ poly.oneValue
    (poly.mul (elim.pairDetD qRag).1
      (elim.minorO poly.ppairOps poly.pnormPair id qRag).2)
    (poly.mul (elim.minorO poly.ppairOps poly.pnormPair id qRag).1
      (elim.pairDetD qRag).2) := by decide +kernel

private def qM3 : List (List poly.PPair) :=
  [[(poly.one, poly.one), ([⟨2, 1⟩], poly.one), ([⟨1, 2⟩], poly.one)],
   [([⟨3, 1⟩], [⟨2, 1⟩]), (poly.one, [⟨3, 1⟩]), (poly.pZero)],
   [([⟨1, 3⟩], poly.one), (poly.pZero), ([⟨2, 1⟩], [⟨2, 1⟩])]]

example : elim.matOcc qM3 = true := by decide +kernel
example : poly.oneValue
    (poly.mul (elim.pairDetD qM3).1
      (elim.minorO poly.ppairOps poly.pnormPair id qM3).2)
    (poly.mul (elim.minorO poly.ppairOps poly.pnormPair id qM3).1
      (elim.pairDetD qM3).2) := by decide +kernel

example : poly.unitTail (elim.pairDetD [[(poly.one, [])]]).2 := by
  decide +kernel

/-! The resultant's stated site. -/

example : topsUnequal [⟨1, 2⟩, ⟨1, 1⟩, ⟨2, 1⟩] [⟨1, 3⟩, ⟨2, 1⟩] := by
  decide +kernel
example : ¬ topsUnequal [⟨1, 2⟩, ⟨2, 1⟩, ⟨5, 5⟩] [⟨1, 3⟩, ⟨2, 1⟩] := by
  decide +kernel

/-! The descent's rank and kernel reads: pivot exchanges, the
fraction-free steps' exact cofactors (the second pivot's division
exercised), and the kernel dimension at the stated column count. -/

example : rank [[⟨2, 1⟩, ⟨3, 1⟩], [⟨3, 1⟩, ⟨5, 1⟩]] = 1 := by decide +kernel
example : rank [[⟨2, 1⟩, ⟨3, 1⟩], [⟨4, 1⟩, ⟨5, 1⟩]] = 2 := by decide +kernel
example : rank [[⟨1, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨1, 1⟩]] = 2 := by decide +kernel
example : rank [[⟨3, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩],
                [⟨2, 1⟩, ⟨3, 1⟩, ⟨2, 1⟩],
                [⟨2, 1⟩, ⟨2, 1⟩, ⟨3, 1⟩]] = 3 := by decide +kernel
example : rank [[⟨2, 1⟩, ⟨3, 1⟩, ⟨4, 1⟩],
                [⟨5, 1⟩, ⟨6, 1⟩, ⟨7, 1⟩],
                [⟨6, 1⟩, ⟨8, 1⟩, ⟨10, 1⟩]] = 2 := by decide +kernel
example : kernelDim 3 [[⟨2, 1⟩, ⟨3, 1⟩, ⟨4, 1⟩],
                       [⟨5, 1⟩, ⟨6, 1⟩, ⟨7, 1⟩],
                       [⟨6, 1⟩, ⟨8, 1⟩, ⟨10, 1⟩]] = 1 := by decide +kernel

/-! The exact cofactor's value pins, one per sign quadrant and the
kernel case: the rank pins alone are blind to the cofactor's
values (the count reads the zero pattern), so the values pin
here. -/

example : cofactorAt ⟨1, 9⟩ ⟨1, 3⟩ = ⟨5, 1⟩ := rfl
example : cofactorAt ⟨9, 1⟩ ⟨1, 3⟩ = ⟨1, 5⟩ := rfl
example : cofactorAt ⟨1, 9⟩ ⟨5, 1⟩ = ⟨1, 3⟩ := rfl
example : cofactorAt ⟨13, 1⟩ ⟨4, 1⟩ = ⟨5, 1⟩ := rfl
example : cofactorAt ⟨7, 7⟩ ⟨4, 1⟩ = BPair.unit := rfl

/-- Dependent rows proportional rather than equal: the descent's
per-entry arithmetic keeps the dependence. -/
example : rank [[⟨2, 1⟩, ⟨3, 1⟩, ⟨4, 1⟩],
                [⟨3, 1⟩, ⟨5, 1⟩, ⟨7, 1⟩],
                [⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩]] = 2 := by decide +kernel

/-! The descent's guard read (`step_unit`), the step at the sum's
unit under each disjunct beside the value it answers, and the
general form (`step_unit_gen`) at an equal-membered datum the
canonical-unit read refuses. -/

example : cofactorAt (⟨5, 1⟩ * BPair.unit + (BPair.unit * ⟨4, 1⟩).swap) ⟨3, 1⟩
    = BPair.unit :=
  step_unit ⟨3, 1⟩ ⟨5, 1⟩ ⟨4, 1⟩ BPair.unit BPair.unit rfl (Or.inl rfl)

example : cofactorAt (⟨5, 1⟩ * BPair.unit + (⟨1, 4⟩ * BPair.unit).swap) ⟨3, 1⟩
    = BPair.unit :=
  step_unit ⟨3, 1⟩ ⟨5, 1⟩ BPair.unit ⟨1, 4⟩ BPair.unit rfl (Or.inr rfl)

/-- An occupied row entry with both partners occupied reaches the
descent's arithmetic, the guard's own refusal. -/
example : cofactorAt ((⟨5, 1⟩ : BPair) * ⟨3, 1⟩
    + ((⟨1, 4⟩ : BPair) * ⟨1, 3⟩).swap) ⟨3, 1⟩ = ⟨2, 1⟩ := rfl

/-- The datum `⟨4:4⟩` sits at equal members off the canonical unit:
`isUnitRep` refuses it, so the landed `step_unit`'s hypotheses are
unavailable here and the general form alone discharges. -/
example : (⟨4, 4⟩ : BPair).isUnitRep = false := by decide +kernel

/-- The general guard at that datum, the row entry and the pivot
row's entry both there: the step answers the sum's unit. -/
example : cofactorAt ((⟨5, 1⟩ : BPair) * ⟨4, 4⟩
    + ((⟨1, 4⟩ : BPair) * ⟨4, 4⟩).swap) ⟨3, 1⟩ = BPair.unit :=
  step_unit_gen ⟨3, 1⟩ ⟨5, 1⟩ ⟨4, 4⟩ ⟨1, 4⟩ ⟨4, 4⟩ rfl (Or.inr rfl)

/-- The general guard's other disjunct at the same datum, the pivot
column at equal members instead. -/
example : cofactorAt ((⟨5, 1⟩ : BPair) * ⟨4, 4⟩
    + ((⟨4, 4⟩ : BPair) * ⟨1, 3⟩).swap) ⟨3, 1⟩ = BPair.unit :=
  step_unit_gen ⟨3, 1⟩ ⟨5, 1⟩ ⟨1, 3⟩ ⟨4, 4⟩ ⟨4, 4⟩ rfl (Or.inl rfl)

/-! The sparse rows' merge, its three keys.  The descent's working
row is the column-keyed list of its off-unit entries, so a key
absent from a row reads the sum's unit there.  The dense step reads
`cofactorAt (pivot * e + (r0 * t).swap) prev` at the pivot row's
entry `t`, the pivot column's entry `r0` and the row's own entry
`e`, and `cofactorAt` reads its stated pair through `BPair.side`,
the pair's value; so at a key of the row alone the swapped product
reads the sum's unit and the step's value is `pivot * e`, while at
a key of the pivot row alone the pivot product reads the sum's unit
and the value is the swapped product.  The two identities pin
exactly those reductions at data whose cofactors are occupied, and
each of the three keys pins beside them at a shape whose pivot
count moves when its case is withdrawn. -/

example : cofactorAt ((⟨5, 1⟩ : BPair) * ⟨1, 4⟩
    + ((⟨2, 1⟩ : BPair) * BPair.unit).swap) ⟨3, 1⟩
    = cofactorAt ((⟨5, 1⟩ : BPair) * ⟨1, 4⟩) ⟨3, 1⟩ := rfl

example : cofactorAt ((⟨5, 1⟩ : BPair) * ⟨1, 4⟩) ⟨3, 1⟩ = ⟨1, 7⟩ := rfl

example : cofactorAt ((⟨5, 1⟩ : BPair) * BPair.unit
    + ((⟨1, 4⟩ : BPair) * ⟨3, 1⟩).swap) ⟨3, 1⟩
    = cofactorAt (((⟨1, 4⟩ : BPair) * ⟨3, 1⟩).swap) ⟨3, 1⟩ := rfl

example : cofactorAt (((⟨1, 4⟩ : BPair) * ⟨3, 1⟩).swap) ⟨3, 1⟩
    = ⟨4, 1⟩ := rfl

/-- A key of the pivot row alone at an occupied pivot column: the
second row is occupied in the pivot column and reads the sum's unit
at the second key, where the pivot row is occupied, so the fill-in
is the whole of what the second pivot reads.  Withdrawing the
fill-in reads the count 1 here. -/
example : rank [[⟨3, 1⟩, ⟨4, 1⟩], [⟨6, 1⟩, ⟨1, 1⟩]] = 2 := by decide +kernel

/-- A key of the row alone: the second row reads the sum's unit in
the pivot column, so its own key scales by the pivot against
`prev`'s cofactor and survives as the second pivot.  Withdrawing
the scaling reads the count 1 here. -/
example : rank [[⟨3, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨4, 1⟩]] = 2 := by decide +kernel

/-- A key of both rows: the step's arithmetic read whole answers
the sum's unit at a dependent pair, so the second pivot is absent.
The swapped product entering at the join's other side reads the
count 2 here. -/
example : rank [[⟨3, 1⟩, ⟨4, 1⟩], [⟨5, 1⟩, ⟨7, 1⟩]] = 1 := by decide +kernel

/-- The joint key at three keys and two descent rounds, its
cofactor exact against the prior pivot.  The join's other side
reads the count 3 here. -/
example : rank [[⟨3, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩],
                [⟨5, 1⟩, ⟨7, 1⟩, ⟨6, 1⟩],
                [⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 1⟩]] = 2 := by decide +kernel

/-- A row reading the sum's unit in the pivot column meets
`step_unit`'s discharge at every key of the pivot row, so its
update is a scaling of its own keys alone. -/
example : rank [[⟨3, 1⟩, ⟨4, 1⟩], [⟨1, 1⟩, ⟨6, 1⟩]] = 2 := by decide +kernel

/-! The per-round truncation width, at ragged shapes.  Each round
reads its key count as the lesser of the pivot row's and the row's,
both peeled, and drops every entry at that count or above; at a
rectangular shape the two counts agree at every round, so every
rank pin above and every stacked read below is blind to the width's
spelling.  These three shapes are not, each isolating one mutation
that passes the whole rectangular suite: the width at the pivot
row's count alone reads 2 at the third, the width at the row's own
count alone reads 2 at the first, and `sPeel`'s count guard at
`Nat.ble` in place of `Nat.blt` reads 1 at the second. -/

/-- The pivot row narrower than the row: the row's surviving key
sits at the pivot row's withdrawn count and drops. -/
example : rank [[⟨2, 1⟩], [BPair.unit, ⟨2, 1⟩]] = 1 := by decide +kernel

/-- The pivot column at the narrower row's own count, so outside
it: that count stands unmoved through the peel and the row's key
survives as the second pivot. -/
example : rank [[BPair.unit, ⟨2, 1⟩], [⟨2, 1⟩]] = 2 := by decide +kernel

/-- The row narrower than the pivot row: the pivot row's fill-in
sits at the row's withdrawn count and drops. -/
example : rank [[⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩]] = 1 := by decide +kernel

/-! The descent at the stacked raisings' own scale.  The committed
matrix is the `B_2` pair count's stacked simple-raising images over
the unit-content monomials of the doubled degree — 76 rows at 61
column keys, entries of magnitude at most three and the sum's unit
at better than nineteen keys in twenty — with its leading square
blocks the profile's own ladder.  The rank reads the pivot count at
each block and the kernel dimension reads the invariant count at the
full shape. -/

/-- The stacked raisings' leading 8-by-8 block. -/
private def stackedB8 : Mat :=
  [[⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨2, 3⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

/-- The stacked raisings' leading 16-by-16 block. -/
private def stackedB16 : Mat :=
  [[⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨2, 3⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

/-- The stacked raisings' leading 24-by-24 block. -/
private def stackedB24 : Mat :=
  [[⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨2, 3⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

/-- The stacked raisings' leading 32-by-32 block. -/
private def stackedB32 : Mat :=
  [[⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨2, 3⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

/-- The stacked raisings' leading 48-by-48 block. -/
private def stackedB48 : Mat :=
  [[⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨2, 3⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

/-- The stacked raisings' whole shape, 76 rows at 61 column keys. -/
private def stackedB : Mat :=
  [[⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨2, 3⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨4, 2⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨3, 2⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨3, 2⟩]]


/-- The stacked raisings' larger partner, the `C_3` shape at 124
rows and 90 column keys. -/
private def stackedC : Mat :=
  [[⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨2, 3⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨3, 2⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨3, 2⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
  [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 2⟩]]

example : rank stackedB8 = 7 := by decide +kernel
example : rank stackedB16 = 14 := by decide +kernel
example : rank stackedB24 = 15 := by decide +kernel
example : rank stackedB32 = 23 := by decide +kernel
example : rank stackedB48 = 38 := by decide +kernel

/-- A row of the block replaced by its own doubling: the pivot count
drops by one at the dependent row, the descent's exact cofactors
keeping the dependence across every step. -/
example : rank (stackedB16.set 3 ((ground.getAt [] stackedB16 5).map
    (fun x => x * ⟨3, 1⟩))) = 13 := by decide +kernel

/-- The whole shape's pivot count and its invariant count at one
descent, the heavy pin: kernel `decide` at the committed 76-by-61
matrix, the kernel dimension the column count's gap at the rank's
own read. -/
example : rank stackedB = 58 ∧ kernelDim 61 stackedB = 3 := by
  have h : rank stackedB = 58 := by decide +kernel
  exact ⟨h, kernelDim_at 61 58 3 stackedB h (by decide +kernel)⟩

/-- The larger partner's two counts at one descent, the heavy pin
at the committed 124-by-90 matrix. -/
example : rank stackedC = 87 ∧ kernelDim 90 stackedC = 3 := by
  have h : rank stackedC = 87 := by decide +kernel
  exact ⟨h, kernelDim_at 90 87 3 stackedC h (by decide +kernel)⟩

/-- The back solve at the committed 76-by-61 shape: the kernel
list's member count at scale with one committed member annihilated
at scale, the tier's own heavy pin beside the rank's — the read
prices the forward descent a second time, the two walks one
recursion at two seeds (`descGo`). -/
example : (kernelList 61 stackedB).length = 3
    ∧ poly.unitTail (matVec stackedB
      (ground.getAt [] (kernelList 61 stackedB) 0)) := by
  decide +kernel

/-- The back solve at the committed 124-by-90 shape: the kernel
list's member count at scale with one committed member annihilated
at scale, the larger partner's own walk. -/
example : (kernelList 90 stackedC).length = 3
    ∧ poly.unitTail (matVec stackedC
      (ground.getAt [] (kernelList 90 stackedC) 0)) := by
  decide +kernel

/-! The matrix product's fold. -/

example : matOneValue
    (matMul [[⟨2, 1⟩, ⟨3, 1⟩], [⟨4, 1⟩, ⟨5, 1⟩]]
      [[⟨6, 1⟩, ⟨7, 1⟩], [⟨8, 1⟩, ⟨9, 1⟩]])
    [[⟨20, 1⟩, ⟨23, 1⟩], [⟨44, 1⟩, ⟨51, 1⟩]] := by decide +kernel

/-! The determinant's row tier: the signed permutation fold beside
the first-row fold at shared instances, the equal-rows alternation
as a theorem instance beside its decided value, and the expansion's
cofactor reads. -/

example : BPair.oneValue
    (detL [[⟨2, 1⟩, ⟨3, 1⟩], [⟨4, 1⟩, ⟨5, 1⟩]]) ⟨1, 3⟩ := by decide +kernel

example : assignRead [[⟨2, 1⟩, ⟨3, 1⟩], [⟨4, 1⟩, ⟨5, 1⟩]] := by
  decide +kernel
example : assignRead [[⟨2, 1⟩, ⟨3, 1⟩, ⟨4, 1⟩],
    [⟨5, 1⟩, ⟨7, 1⟩, ⟨11, 1⟩],
    [⟨13, 1⟩, ⟨17, 1⟩, ⟨19, 1⟩]] := by decide +kernel
example : assignRead [[⟨2, 1⟩, ⟨1, 3⟩, ⟨1, 4⟩, ⟨5, 1⟩],
    [⟨1, 1⟩, ⟨6, 1⟩, ⟨1, 7⟩, ⟨2, 1⟩],
    [⟨3, 1⟩, ⟨1, 2⟩, ⟨8, 1⟩, ⟨1, 5⟩],
    [⟨1, 6⟩, ⟨4, 1⟩, ⟨1, 1⟩, ⟨9, 1⟩]] := by decide +kernel

example : BPair.oneValue
    (detL [[⟨2, 1⟩, ⟨3, 1⟩], [⟨2, 1⟩, ⟨3, 1⟩]]) BPair.unit := by
  decide +kernel

example : BPair.oneValue
    (detL [[⟨2, 1⟩, ⟨3, 1⟩], [⟨2, 1⟩, ⟨3, 1⟩]]) BPair.unit :=
  detL_rows_equal (Nat.lt_succ_self 0) (Nat.lt_succ_self 1) rfl

/-! The adjugate row solve and the membership residual: the solve
identity's decided instance, a span member's passing residual, and
an outside vector's refusal. -/

example : BPair.oneValue
    (dotP (ground.getAt [] [[⟨3, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨4, 1⟩]] 0)
      (adjP [[⟨3, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨4, 1⟩]]
        [⟨5, 1⟩, ⟨6, 1⟩]))
    (⟨5, 1⟩ * detL [[⟨3, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨4, 1⟩]]) := by
  decide +kernel

example : poly.unitTail
    (residV 2 [[⟨2, 1⟩, ⟨1, 1⟩]] [⟨3, 1⟩, ⟨1, 1⟩]) := by decide +kernel

example : ¬ poly.unitTail
    (residV 2 [[⟨2, 1⟩, ⟨1, 1⟩]] [⟨1, 1⟩, ⟨2, 1⟩]) := by decide +kernel

example : poly.unitTail
    (residV 2 [[⟨2, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]]
      [⟨4, 1⟩, ⟨3, 1⟩]) := by decide +kernel

/-! The residual's defining join read back: the cleared member is
its residual joined to the projection combination, decided outright
and read again off `residV_expand` applied whole. -/

example : poly.oneValue
    (vecScale (detL (gramM [[BPair.ofNat 1, BPair.unit]]))
      [BPair.unit, BPair.ofNat 1])
    (vecAdd (residV 2 [[BPair.ofNat 1, BPair.unit]]
        [BPair.unit, BPair.ofNat 1])
      (combo 2 (adjP (gramM [[BPair.ofNat 1, BPair.unit]])
          ([[BPair.ofNat 1, BPair.unit]].map
            (fun r => dotP r [BPair.unit, BPair.ofNat 1])))
        [[BPair.ofNat 1, BPair.unit]])) := by decide +kernel

example : poly.oneValue
    (vecScale (detL (gramM [[BPair.ofNat 1, BPair.unit]]))
      [BPair.unit, BPair.ofNat 1])
    (vecAdd (residV 2 [[BPair.ofNat 1, BPair.unit]]
        [BPair.unit, BPair.ofNat 1])
      (combo 2 (adjP (gramM [[BPair.ofNat 1, BPair.unit]])
          ([[BPair.ofNat 1, BPair.unit]].map
            (fun r => dotP r [BPair.unit, BPair.ofNat 1])))
        [[BPair.ofNat 1, BPair.unit]])) :=
  elim.residV_expand 2 [[BPair.ofNat 1, BPair.unit]]
    [BPair.unit, BPair.ofNat 1] (by decide +kernel) (by decide +kernel)

/-! The independence and span-linearity tier's pins: the dimension
bound composed through the one-member independence read, the
transports' instances, and the span's combination read at listed
rows. -/

example : ([[BPair.ofNat 1, BPair.unit]] : elim.Mat).length ≤ 2 :=
  elim.indep_bound 2 [[BPair.ofNat 1, BPair.unit]] ⟨rfl, trivial⟩
    (elim.indep_single 2 [BPair.ofNat 1, BPair.unit] rfl (by decide +kernel))

example : elim.indepRows 2
    (ground.adjSwap 0 [[BPair.ofNat 1, BPair.unit],
      [BPair.unit, BPair.ofNat 1]]) :=
  elim.indep_swapAdj 2 0 _
    (elim.indep_extend 2 [[BPair.ofNat 1, BPair.unit]]
      [BPair.unit, BPair.ofNat 1] ⟨rfl, trivial⟩ rfl
      (elim.indep_single 2 _ rfl (by decide +kernel))
      (fun hsp => by
        have := elim.resid_complete 2 [[BPair.ofNat 1, BPair.unit]]
          [BPair.unit, BPair.ofNat 1] ⟨rfl, trivial⟩ rfl hsp
        exact absurd this (by decide +kernel)))

example : elim.spanRel 1 [[BPair.ofNat 1]]
    (elim.vecAdd [BPair.ofNat 1] [BPair.ofNat 1]) :=
  elim.spanRel_add 1 [[BPair.ofNat 1]] [BPair.ofNat 1]
    [BPair.ofNat 1] ⟨rfl, trivial⟩ rfl rfl
    (elim.spanRel_getAt 1 _ 0 (by decide +kernel) ⟨rfl, trivial⟩)
    (elim.spanRel_getAt 1 _ 0 (by decide +kernel) ⟨rfl, trivial⟩)

example : elim.spanRel 1 [[BPair.ofNat 1]] [BPair.unit] :=
  elim.spanRel_null 1 [[BPair.ofNat 1]] [BPair.unit] (by decide +kernel)
    ⟨rfl, trivial⟩ rfl

example : elim.spanRel 1 [[BPair.ofNat 1]]
    (elim.vecScale (BPair.ofNat 2) [BPair.ofNat 1]) :=
  elim.spanRel_scale 1 [[BPair.ofNat 1]] [BPair.ofNat 1]
    (BPair.ofNat 2) ⟨rfl, trivial⟩ rfl
    (elim.spanRel_getAt 1 _ 0 (by decide +kernel) ⟨rfl, trivial⟩)

/-- The bound's bite: a family longer than its width refuses
independence outright, and the two-member instance reads the bound
tight. -/
example : ¬ elim.indepRows 2
    [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.ofNat 1],
      [BPair.ofNat 1, BPair.ofNat 1]] := fun h =>
  absurd (elim.indep_bound 2
    [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.ofNat 1],
      [BPair.ofNat 1, BPair.ofNat 1]] ⟨rfl, rfl, rfl, trivial⟩ h)
    (by decide +kernel)

example : ([[BPair.ofNat 1, BPair.unit],
      [BPair.unit, BPair.ofNat 1]] : elim.Mat).length ≤ 2 :=
  elim.indep_bound 2 _ ⟨rfl, rfl, trivial⟩
    (elim.indep_extend 2 [[BPair.ofNat 1, BPair.unit]]
      [BPair.unit, BPair.ofNat 1] ⟨rfl, trivial⟩ rfl
      (elim.indep_single 2 _ rfl (by decide +kernel))
      (fun hsp => by
        have := elim.resid_complete 2 [[BPair.ofNat 1, BPair.unit]]
          [BPair.unit, BPair.ofNat 1] ⟨rfl, trivial⟩ rfl hsp
        exact absurd this (by decide +kernel)))

/-! The span's join reads: a member is kept under rows joined in
front, and the join splits back at a perpendicular tail — the
member perpendicular to the tail's rows with the head's rows
perpendicular to them as well sits in the head's span alone. -/

example : elim.spanRel 2 ([[BPair.ofNat 1, BPair.unit]]
    ++ [[BPair.unit, BPair.ofNat 1]]) [BPair.unit, BPair.ofNat 1] :=
  elim.spanRel_mono_left 2 [[BPair.ofNat 1, BPair.unit]]
    [[BPair.unit, BPair.ofNat 1]] [BPair.unit, BPair.ofNat 1]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : elim.spanRel 2 [[BPair.ofNat 1, BPair.unit]]
    [BPair.ofNat 1, BPair.unit] :=
  elim.span_perp_split 2 [[BPair.ofNat 1, BPair.unit]]
    [[BPair.unit, BPair.ofNat 1]] [BPair.ofNat 1, BPair.unit]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The tail-perpendicular binder is load-bearing: at a member
pairing off the unit against the tail's row, every surviving
co-binder holds, the binder refuses, and the head's span refuses
with it. -/
example : (elim.rowsLen 2 [[BPair.ofNat 1, BPair.unit]]
      ∧ elim.rowsLen 2 [[BPair.unit, BPair.ofNat 1]]
      ∧ (∀ j, j < [[BPair.ofNat 1, BPair.unit]].length →
        ∀ k, k < [[BPair.unit, BPair.ofNat 1]].length →
          (elim.dotP
            (ground.getAt [] [[BPair.ofNat 1, BPair.unit]] j)
            (ground.getAt [] [[BPair.unit, BPair.ofNat 1]]
              k)).oneValue BPair.unit)
      ∧ elim.spanRel 2 ([[BPair.ofNat 1, BPair.unit]]
          ++ [[BPair.unit, BPair.ofNat 1]])
          [BPair.unit, BPair.ofNat 1])
    ∧ ¬ (∀ k, k < [[BPair.unit, BPair.ofNat 1]].length →
      (elim.dotP [BPair.unit, BPair.ofNat 1]
        (ground.getAt [] [[BPair.unit, BPair.ofNat 1]]
          k)).oneValue BPair.unit)
    ∧ ¬ elim.spanRel 2 [[BPair.ofNat 1, BPair.unit]]
      [BPair.unit, BPair.ofNat 1] := by decide +kernel

/-- The head-perpendicular binder is load-bearing: at a head row
pairing off the unit against the tail's row, every surviving
co-binder holds, the binder refuses, and the head's span refuses
with it. -/
example : (elim.rowsLen 2 [[BPair.ofNat 1, BPair.ofNat 1]]
      ∧ elim.rowsLen 2 [[BPair.unit, BPair.ofNat 1]]
      ∧ (∀ k, k < [[BPair.unit, BPair.ofNat 1]].length →
        (elim.dotP [BPair.ofNat 1, BPair.unit]
          (ground.getAt [] [[BPair.unit, BPair.ofNat 1]]
            k)).oneValue BPair.unit)
      ∧ elim.spanRel 2 ([[BPair.ofNat 1, BPair.ofNat 1]]
          ++ [[BPair.unit, BPair.ofNat 1]])
          [BPair.ofNat 1, BPair.unit])
    ∧ ¬ (∀ j, j < [[BPair.ofNat 1, BPair.ofNat 1]].length →
      ∀ k, k < [[BPair.unit, BPair.ofNat 1]].length →
        (elim.dotP
          (ground.getAt [] [[BPair.ofNat 1, BPair.ofNat 1]] j)
          (ground.getAt [] [[BPair.unit, BPair.ofNat 1]]
            k)).oneValue BPair.unit)
    ∧ ¬ elim.spanRel 2 [[BPair.ofNat 1, BPair.ofNat 1]]
      [BPair.ofNat 1, BPair.unit] := by decide +kernel

/-! The exchange read's pins: two independent lists spanning one
plane read one count, each member of either solved in the other's
span through the residual's decided pass, and a one-member list
inside the plane reads the count's bound. -/

example : ([[BPair.ofNat 1, BPair.unit],
      [BPair.unit, BPair.ofNat 1]] : elim.Mat).length
    = ([[⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨1, 2⟩]] : elim.Mat).length :=
  elim.span_count_eq 2
    [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.ofNat 1]]
    [[⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨1, 2⟩]]
    ⟨rfl, rfl, trivial⟩ ⟨rfl, rfl, trivial⟩
    (elim.indep_extend 2 [[BPair.ofNat 1, BPair.unit]]
      [BPair.unit, BPair.ofNat 1] ⟨rfl, trivial⟩ rfl
      (elim.indep_single 2 _ rfl (by decide +kernel))
      (fun hsp => by
        have := elim.resid_complete 2 [[BPair.ofNat 1, BPair.unit]]
          [BPair.unit, BPair.ofNat 1] ⟨rfl, trivial⟩ rfl hsp
        exact absurd this (by decide +kernel)))
    (elim.indep_extend 2 [[⟨2, 1⟩, ⟨2, 1⟩]] [⟨2, 1⟩, ⟨1, 2⟩]
      ⟨rfl, trivial⟩ rfl
      (elim.indep_single 2 _ rfl (by decide +kernel))
      (fun hsp => by
        have := elim.resid_complete 2 [[⟨2, 1⟩, ⟨2, 1⟩]]
          [⟨2, 1⟩, ⟨1, 2⟩] ⟨rfl, trivial⟩ rfl hsp
        exact absurd this (by decide +kernel)))
    (by decide +kernel)
    (by decide +kernel)

example : ([[⟨3, 1⟩, ⟨1, 1⟩]] : elim.Mat).length
    ≤ ([[⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨1, 2⟩]] : elim.Mat).length :=
  elim.span_count_le 2 [[⟨3, 1⟩, ⟨1, 1⟩]]
    [[⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨1, 2⟩]]
    ⟨rfl, trivial⟩ ⟨rfl, rfl, trivial⟩
    (elim.indep_single 2 _ rfl (by decide +kernel))
    (by decide +kernel)

/-! The action kit's pins: the reverse read's bite at the exchange
count, and the composed actions against the matrix product. -/

/-- The one-sided membership reads the bound alone: the listed row
sits in the longer list's span, so `span_count_le` closes, while
the counts themselves differ — `span_count_eq`'s reverse
hypothesis `hBA` is what carries the equality. -/
example : ([[⟨2, 1⟩, ⟨1, 1⟩]] : elim.Mat).length
    ≤ ([[⟨2, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]] : elim.Mat).length :=
  elim.span_count_le 2 [[⟨2, 1⟩, ⟨1, 1⟩]]
    [[⟨2, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]]
    ⟨rfl, trivial⟩ ⟨rfl, rfl, trivial⟩
    (elim.indep_single 2 _ rfl (by decide +kernel))
    (by decide +kernel)

example : ¬ (([[⟨2, 1⟩, ⟨1, 1⟩]] : elim.Mat).length
    = ([[⟨2, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]] : elim.Mat).length) := by
  decide +kernel

/-- The composed actions at the product's own action, the decided
value beside `matVec_comp`'s instance. -/
example : poly.oneValue
    (elim.matVec [[⟨2, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]]
      (elim.matVec [[⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨1, 2⟩]]
        [⟨3, 1⟩, ⟨1, 2⟩]))
    (elim.matVec (elim.matMul [[⟨2, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]]
        [[⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨1, 2⟩]])
      [⟨3, 1⟩, ⟨1, 2⟩]) := by decide +kernel

example : poly.oneValue
    (elim.matVec [[⟨2, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]]
      (elim.matVec [[⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨1, 2⟩]]
        [⟨3, 1⟩, ⟨1, 2⟩]))
    (elim.matVec (elim.matMul [[⟨2, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]]
        [[⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨1, 2⟩]])
      [⟨3, 1⟩, ⟨1, 2⟩]) :=
  elim.matVec_comp [[⟨2, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]]
    [[⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨1, 2⟩]] [⟨3, 1⟩, ⟨1, 2⟩] 2
    ⟨rfl, rfl, trivial⟩ rfl ⟨rfl, rfl, trivial⟩

/-! The vector-valued index fold: a committed two-member family at
width two, its fold against the hand value, with each read of the
kit decided beside its own theorem instance — the head split, the
pointwise congruence and split, the pairing and the action against
the fold, the double range's exchange and the delta pick. -/

private def famA : Nat → List BPair :=
  fun k => [BPair.ofNat (k + 1), BPair.ofNat k]

private def famB : Nat → List BPair :=
  fun k => [BPair.ofNat k, BPair.ofNat (k + 2)]

private def famF : Nat → Nat → List BPair :=
  fun a b => [BPair.ofNat (a + b), BPair.ofNat a]

private theorem lenA : ∀ k, (famA k).length = 2 := fun _ => rfl

private theorem lenB : ∀ k, (famB k).length = 2 := fun _ => rfl

private theorem lenF : ∀ a b, (famF a b).length = 2 := fun _ _ => rfl

example : (elim.vsum 2 famA (List.range 2)).length = 2 := by decide +kernel

example : (elim.vsum 2 famA (List.range 2)).length = 2 :=
  elim.length_vsum 2 famA (List.range 2) (fun k _ => lenA k)

/-! The fold's own value: the unit seed against the two members. -/

example : poly.oneValue (elim.vsum 2 famA (List.range 2))
    [BPair.ofNat 3, BPair.ofNat 1] := by decide +kernel

example : poly.oneValue (elim.vsum 2 famA (List.range 3))
    [BPair.ofNat 6, BPair.ofNat 3] := by decide +kernel

/-! The head split. -/

example : poly.oneValue (elim.vsum 2 famA (List.range 2))
    (elim.vecAdd (famA 0) (elim.vsum 2 famA [1])) := by decide +kernel

example : poly.oneValue (elim.vsum 2 famA (0 :: [1]))
    (elim.vecAdd (famA 0) (elim.vsum 2 famA [1])) :=
  elim.vsum_cons 2 famA lenA 0 [1]

/-! The pointwise congruence at a family reading one value. -/

example : poly.oneValue (elim.vsum 2 famA (List.range 2))
    (elim.vsum 2 (fun k => (famA k).map (fun z => z + BPair.unit))
      (List.range 2)) :=
  elim.vsum_congr 2 famA
    (fun k => (famA k).map (fun z => z + BPair.unit)) lenA
    (fun _ => rfl)
    (fun _ => ⟨BPair.oneValue_symm (BPair.add_unit _),
      BPair.oneValue_symm (BPair.add_unit _), trivial⟩)
    (List.range 2)

/-! The pointwise split. -/

example : poly.oneValue
    (elim.vsum 2 (fun k => elim.vecAdd (famA k) (famB k))
      (List.range 2))
    (elim.vecAdd (elim.vsum 2 famA (List.range 2))
      (elim.vsum 2 famB (List.range 2))) := by decide +kernel

example : poly.oneValue
    (elim.vsum 2 (fun k => elim.vecAdd (famA k) (famB k))
      (List.range 2))
    (elim.vecAdd (elim.vsum 2 famA (List.range 2))
      (elim.vsum 2 famB (List.range 2))) :=
  elim.vsum_vecAdd 2 famA famB lenA lenB (List.range 2)

/-! The pairing and the action against the fold. -/

example : (elim.dotP [BPair.ofNat 1, BPair.ofNat 2]
      (elim.vsum 2 famA (List.range 2))).oneValue
    (ground.bsum (fun k => elim.dotP [BPair.ofNat 1, BPair.ofNat 2]
      (famA k)) (List.range 2)) := by decide +kernel

example : (elim.dotP [BPair.ofNat 1, BPair.ofNat 2]
      (elim.vsum 2 famA (List.range 2))).oneValue
    (ground.bsum (fun k => elim.dotP [BPair.ofNat 1, BPair.ofNat 2]
      (famA k)) (List.range 2)) :=
  elim.dotP_vsum 2 famA lenA [BPair.ofNat 1, BPair.ofNat 2] rfl
    (List.range 2)

example : poly.oneValue
    (elim.matVec [[⟨2, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]]
      (elim.vsum 2 famA (List.range 2)))
    (elim.vsum 2 (fun k =>
      elim.matVec [[⟨2, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]] (famA k))
      (List.range 2)) := by decide +kernel

example : poly.oneValue
    (elim.matVec [[⟨2, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]]
      (elim.vsum 2 famA (List.range 2)))
    (elim.vsum
      ([[(⟨2, 1⟩ : BPair), ⟨1, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]] :
        elim.Mat).length
      (fun k =>
        elim.matVec [[⟨2, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]] (famA k))
      (List.range 2)) :=
  elim.matVec_vsum 2 [[⟨2, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]]
    famA lenA (List.range 2)

/-! The double range's exchange. -/

example : poly.oneValue
    (elim.vsum 2 (fun a => elim.vsum 2 (fun b => famF a b)
      (List.range 2)) (List.range 3))
    (elim.vsum 2 (fun b => elim.vsum 2 (fun a => famF a b)
      (List.range 3)) (List.range 2)) := by decide +kernel

example : poly.oneValue
    (elim.vsum 2 (fun a => elim.vsum 2 (fun b => famF a b)
      (List.range 2)) (List.range 3))
    (elim.vsum 2 (fun b => elim.vsum 2 (fun a => famF a b)
      (List.range 3)) (List.range 2)) :=
  elim.vsum_swap 2 famF lenF (List.range 2) (List.range 3)

/-! The delta pick at a guarded family. -/

example : poly.oneValue
    (elim.vsum 2 (fun k => if 1 = k then famA k
      else List.replicate 2 BPair.unit) (List.range 3)) (famA 1) := by
  decide +kernel

example : poly.oneValue
    (elim.vsum 2 (fun k => if 1 = k then famA k
      else List.replicate 2 BPair.unit) (List.range 3)) (famA 1) :=
  elim.vsum_pick 2 famA lenA (List.range 3) 1 (by decide +kernel)

/-! The refusal: a guarded family off its key reads the unit
family, not the member. -/

example : ¬ poly.oneValue
    (elim.vsum 2 (fun k => if 2 = k then famA k
      else List.replicate 2 BPair.unit) (List.range 2)) (famA 2) := by
  decide +kernel

/-! The shape algebra of the sum, the key-list exchange and the
product: each read decided at a committed rectangle and discharged
beside its own theorem instance, with the refusals isolating the
shape hypotheses.  The rectangle is `A : 2×3`, `B : 3×2`,
`C : 2×2` — the one shape where the association's three orders are
all distinct and the exchange's reversal is visible. -/

private def mA : Mat :=
  [[BPair.ofNat 1, BPair.ofNat 2, (BPair.ofNat 1).swap],
   [BPair.unit, BPair.ofNat 3, BPair.ofNat 1]]

private def mB : Mat :=
  [[BPair.ofNat 2, BPair.ofNat 1],
   [(BPair.ofNat 3).swap, BPair.unit],
   [BPair.ofNat 1, BPair.ofNat 4]]

private def mC : Mat :=
  [[BPair.ofNat 1, (BPair.ofNat 2).swap],
   [BPair.ofNat 5, BPair.ofNat 1]]

example : transposeM (transposeM mA) = mA :=
  elim.transposeM_transposeM (n := 3) mA (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : transposeM (matAdd mA mA) = matAdd (transposeM mA) (transposeM mA) :=
  elim.transposeM_matAdd (n := 3) mA mA (by decide +kernel) (by decide +kernel) rfl (by decide +kernel)

example : matOneValue (transposeM (matMul mB mC))
    (matMul (transposeM mC) (transposeM mB)) :=
  elim.transposeM_matMul (r := 3) (n := 2) (k := 2) mB mC (by decide +kernel)
    (by decide +kernel) rfl rfl (by decide +kernel) (by decide +kernel)

example : matOneValue (matMul (matMul mA mB) mC)
    (matMul mA (matMul mB mC)) :=
  elim.matMul_assoc (n := 3) (k := 2) (s := 2) mA mB mC (by decide +kernel)
    (by decide +kernel) (by decide +kernel) rfl rfl (by decide +kernel) (by decide +kernel)

example : matOneValue (matMul (matMul mA mB) mC)
    (matMul mA (matMul mB mC)) := by decide +kernel

example : matOneValue (matMul mC (matAdd mA mA))
    (matAdd (matMul mC mA) (matMul mC mA)) :=
  elim.matMul_addR (n := 3) mA mA (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) mC
    (by decide +kernel)

example : matOneValue (matMul (matAdd mB mB) mC)
    (matAdd (matMul mB mC) (matMul mB mC)) :=
  elim.matMul_addL 2 mC (by decide +kernel) mB mB (by decide +kernel) (by decide +kernel)

example : matSwap (matSwap mA) = mA := elim.matSwap_matSwap mA
example : matMul (matSwap mA) mB = matSwap (matMul mA mB) :=
  elim.matMul_swapL mA mB
example : matOneValue (matAdd (matSwap mC) (matAdd mC mC)) mC :=
  elim.matSwap_double mC

/-! The refusals: the association fails at a mismatched inner
shape — the product read against the wrong factor order — and the
exchange's reversal is not the unreversed product. -/

example : ¬ matOneValue (transposeM (matMul mB mC)) (matMul (transposeM mB)
    (transposeM mC)) := by decide +kernel

example : ¬ matOneValue (matMul (matMul mA mB) mC)
    (matMul mA (matMul mB (matSwap mC))) := by decide +kernel

/-! The matrix-valued index fold at a stated family: the head and
snoc splits, the shift read, the wrapped fold and the product
against it, discharged at the two-key family over the square datum
`mC` and its memberwise swap — the null seed's own product read
beside them.  The product's left congruence rides here too, and the
wrap is shown load-bearing by a family whose key at the range's
length misses its head. -/

private def gFam : Nat → Mat := fun k => if k == 0 then mC else matSwap mC

private def hFam : Nat → Mat := fun k => if k == 1 then matSwap mC else mC

private theorem gShape : ∀ k, elim.rowsLen 2 (gFam k)
    ∧ (gFam k).length = 2 := by
  intro k
  cases h : k == 0 <;>
    · show elim.rowsLen 2 (if k == 0 then mC else matSwap mC)
        ∧ (if k == 0 then mC else matSwap mC).length = 2
      rw [h]
      exact ⟨by decide +kernel, by decide +kernel⟩

private theorem hShape : ∀ k, elim.rowsLen 2 (hFam k)
    ∧ (hFam k).length = 2 := by
  intro k
  cases h : k == 1 <;>
    · show elim.rowsLen 2 (if k == 1 then matSwap mC else mC)
        ∧ (if k == 1 then matSwap mC else mC).length = 2
      rw [h]
      exact ⟨by decide +kernel, by decide +kernel⟩

example : elim.msum 2 gFam [0, 1]
    = matAdd (gFam 0) (matAdd (gFam 1) (elim.nullMat 2 2)) :=
  (elim.msum_cons 2 gFam 0 [1]).trans
    (congrArg (matAdd (gFam 0)) (elim.msum_cons 2 gFam 1 []))

example : elim.msum 2 gFam ([0] ++ [1])
    = matAdd (elim.msum 2 gFam [0]) (gFam 1) :=
  elim.msum_append 2 gFam [0] 1

example : matOneValue (elim.msum 2 gFam [0, 1]) (matAdd mC (matSwap mC)) := by
  decide +kernel

example : matOneValue (matMul mC (elim.msum 2 gFam [0, 1]))
    (elim.msum 2 (fun k => matMul mC (gFam k)) [0, 1]) :=
  elim.matMul_msum 2 mC (by decide +kernel) rfl (by decide +kernel) gFam gShape [0, 1]

example : matOneValue (matMul mC (elim.nullMat 2 2)) (elim.nullMat 2 2) :=
  elim.matMul_nullMat 2 mC rfl

example : matOneValue (matMul (matSwap (matSwap mC)) mC) (matMul mC mC) :=
  elim.matMul_congrL (matSwap (matSwap mC)) mC mC (by decide +kernel)

example : matAdd (gFam 0) (elim.msum 2 (fun b => gFam (b + 1)) (List.range 2))
    = matAdd (elim.msum 2 gFam (List.range 2)) (gFam 2) :=
  elim.msum_shift 2 gFam 2

example : matOneValue (elim.msum 2 (fun b => hFam (b + 1)) (List.range 2))
    (elim.msum 2 hFam (List.range 2)) :=
  elim.msum_wrap 2 hFam hShape 2 (by decide +kernel)

/-! The refusals: the wrapped key's own read is load-bearing — the
family `gFam` reads its swap at every key beyond the head, so its
key at the range's length is off equal members with the head and
the shifted fold is not the family's. -/

example : ¬ matOneValue (gFam 2) (gFam 0) := by decide +kernel
example : ¬ matOneValue (elim.msum 2 (fun b => gFam (b + 1)) (List.range 2))
    (elim.msum 2 gFam (List.range 2)) := by decide +kernel

/-! The joined span's order read and the perpendicular
withdrawal: the append-commuted membership applied whole with its
direct pin, and the unit-tail sum's two perpendicular parts read
the unit tail each, the crossed pairing's binder at its isolating
refusal. -/

example : elim.spanRel 2 ([[⟨2, 1⟩, ⟨1, 1⟩]] ++ [[⟨1, 1⟩, ⟨3, 1⟩]])
      [⟨5, 1⟩, ⟨6, 2⟩]
    ∧ elim.spanRel 2 ([[⟨1, 1⟩, ⟨3, 1⟩]] ++ [[⟨2, 1⟩, ⟨1, 1⟩]])
      [⟨5, 1⟩, ⟨6, 2⟩] := by decide +kernel

example : elim.spanRel 2 ([[⟨1, 1⟩, ⟨3, 1⟩]] ++ [[⟨2, 1⟩, ⟨1, 1⟩]])
    [⟨5, 1⟩, ⟨6, 2⟩] :=
  elim.spanRel_append_comm 2 [[⟨2, 1⟩, ⟨1, 1⟩]] [[⟨1, 1⟩, ⟨3, 1⟩]]
    [⟨5, 1⟩, ⟨6, 2⟩] (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : poly.unitTail [(⟨2, 2⟩ : BPair), ⟨1, 1⟩]
    ∧ poly.unitTail [(⟨3, 3⟩ : BPair), ⟨4, 4⟩] :=
  elim.vecAdd_perp_null [(⟨2, 2⟩ : BPair), ⟨1, 1⟩]
    [(⟨3, 3⟩ : BPair), ⟨4, 4⟩] rfl (by decide +kernel) (by decide +kernel)

/-- The crossed pairing's binder is load-bearing: two off-unit
parts summing to the unit tail cross at an occupied pairing, and
the parts read off the unit tail. -/
example : poly.unitTail (elim.vecAdd [BPair.ofNat 1]
      [(BPair.ofNat 1).swap])
    ∧ ¬ (elim.dotP [BPair.ofNat 1]
      [(BPair.ofNat 1).swap]).oneValue BPair.unit
    ∧ ¬ poly.unitTail [(BPair.ofNat 1 : BPair)] := by decide +kernel

/-- The length tie is load-bearing: the memberwise sum truncates
at the shorter list, so an unmatched off-unit part reads the
summed unit tail and the crossed unit pairing with its own tail
off the unit — both orientations forged. -/
example : (poly.unitTail (elim.vecAdd [BPair.ofNat 1]
        ([] : List BPair))
      ∧ (elim.dotP [BPair.ofNat 1]
        ([] : List BPair)).oneValue BPair.unit
      ∧ ¬ poly.unitTail [(BPair.ofNat 1 : BPair)])
    ∧ (poly.unitTail (elim.vecAdd ([] : List BPair)
        [BPair.ofNat 1])
      ∧ (elim.dotP ([] : List BPair)
        [BPair.ofNat 1]).oneValue BPair.unit
      ∧ ¬ poly.unitTail [(BPair.ofNat 1 : BPair)]) := by decide +kernel

/-! The determinant against the exchanged key lists: the theorem
applied whole at asymmetric squares of orders two through four,
the kernel's own pins at orders three and four, and the squareness
binder at its isolating refusals in both non-square orientations
with the ragged shape beside them. -/

example : detL (transposeM [[⟨2, 1⟩, ⟨3, 1⟩], [⟨1, 2⟩, ⟨5, 1⟩]])
    = detL [[⟨2, 1⟩, ⟨3, 1⟩], [⟨1, 2⟩, ⟨5, 1⟩]] :=
  detL_transpose [[⟨2, 1⟩, ⟨3, 1⟩], [⟨1, 2⟩, ⟨5, 1⟩]] (by decide +kernel)

example : detL (transposeM
      [[⟨3, 1⟩, ⟨1, 4⟩, ⟨2, 1⟩],
       [⟨1, 1⟩, ⟨2, 5⟩, ⟨7, 1⟩],
       [⟨5, 2⟩, ⟨1, 1⟩, ⟨1, 3⟩]])
    = detL
      [[⟨3, 1⟩, ⟨1, 4⟩, ⟨2, 1⟩],
       [⟨1, 1⟩, ⟨2, 5⟩, ⟨7, 1⟩],
       [⟨5, 2⟩, ⟨1, 1⟩, ⟨1, 3⟩]] :=
  detL_transpose
    [[⟨3, 1⟩, ⟨1, 4⟩, ⟨2, 1⟩],
     [⟨1, 1⟩, ⟨2, 5⟩, ⟨7, 1⟩],
     [⟨5, 2⟩, ⟨1, 1⟩, ⟨1, 3⟩]] (by decide +kernel)

example : detL (transposeM
      [[⟨2, 1⟩, ⟨1, 3⟩, ⟨4, 1⟩, ⟨1, 1⟩],
       [⟨1, 2⟩, ⟨3, 1⟩, ⟨1, 5⟩, ⟨2, 1⟩],
       [⟨5, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩],
       [⟨1, 4⟩, ⟨6, 1⟩, ⟨2, 2⟩, ⟨1, 7⟩]])
    = detL
      [[⟨2, 1⟩, ⟨1, 3⟩, ⟨4, 1⟩, ⟨1, 1⟩],
       [⟨1, 2⟩, ⟨3, 1⟩, ⟨1, 5⟩, ⟨2, 1⟩],
       [⟨5, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩],
       [⟨1, 4⟩, ⟨6, 1⟩, ⟨2, 2⟩, ⟨1, 7⟩]] :=
  detL_transpose
    [[⟨2, 1⟩, ⟨1, 3⟩, ⟨4, 1⟩, ⟨1, 1⟩],
     [⟨1, 2⟩, ⟨3, 1⟩, ⟨1, 5⟩, ⟨2, 1⟩],
     [⟨5, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩],
     [⟨1, 4⟩, ⟨6, 1⟩, ⟨2, 2⟩, ⟨1, 7⟩]] (by decide +kernel)

example : detL (transposeM
      [[⟨2, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩],
       [⟨1, 2⟩, ⟨5, 1⟩, ⟨2, 3⟩],
       [⟨4, 1⟩, ⟨1, 3⟩, ⟨2, 2⟩]])
    = detL
      [[⟨2, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩],
       [⟨1, 2⟩, ⟨5, 1⟩, ⟨2, 3⟩],
       [⟨4, 1⟩, ⟨1, 3⟩, ⟨2, 2⟩]] := by decide +kernel

example : detL (transposeM
      [[⟨2, 1⟩, ⟨1, 3⟩, ⟨4, 1⟩, ⟨1, 1⟩],
       [⟨1, 2⟩, ⟨3, 1⟩, ⟨1, 5⟩, ⟨2, 1⟩],
       [⟨5, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩],
       [⟨1, 4⟩, ⟨6, 1⟩, ⟨2, 2⟩, ⟨1, 7⟩]])
    = detL
      [[⟨2, 1⟩, ⟨1, 3⟩, ⟨4, 1⟩, ⟨1, 1⟩],
       [⟨1, 2⟩, ⟨3, 1⟩, ⟨1, 5⟩, ⟨2, 1⟩],
       [⟨5, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩],
       [⟨1, 4⟩, ⟨6, 1⟩, ⟨2, 2⟩, ⟨1, 7⟩]] := by decide +kernel

/-- The squareness binder is load-bearing: at a single row of
width two the transpose's determinant reads the sum's unit over
its two-row fold while the row's own reads its first entry, the
two off equal members. -/
example : (¬ rowsLen ([[(⟨2, 1⟩ : BPair), ⟨3, 1⟩]] : Mat).length
      [[(⟨2, 1⟩ : BPair), ⟨3, 1⟩]])
    ∧ ¬ ((detL (transposeM [[(⟨2, 1⟩ : BPair), ⟨3, 1⟩]])).oneValue
      (detL [[(⟨2, 1⟩ : BPair), ⟨3, 1⟩]])) := by decide +kernel

/-- The other orientation's refusal: at three rows of width two
the row count exceeds the width, the shape read refusing with the
two determinants off one value. -/
example : (¬ rowsLen
      ([[(⟨2, 1⟩ : BPair), ⟨3, 1⟩], [⟨1, 2⟩, ⟨5, 1⟩],
        [⟨4, 1⟩, ⟨1, 3⟩]] : Mat).length
      [[(⟨2, 1⟩ : BPair), ⟨3, 1⟩], [⟨1, 2⟩, ⟨5, 1⟩],
        [⟨4, 1⟩, ⟨1, 3⟩]])
    ∧ ¬ ((detL (transposeM
        [[(⟨2, 1⟩ : BPair), ⟨3, 1⟩], [⟨1, 2⟩, ⟨5, 1⟩],
          [⟨4, 1⟩, ⟨1, 3⟩]])).oneValue
      (detL [[(⟨2, 1⟩ : BPair), ⟨3, 1⟩], [⟨1, 2⟩, ⟨5, 1⟩],
        [⟨4, 1⟩, ⟨1, 3⟩]])) := by decide +kernel

/-- The ragged shape's refusal: rows of differing widths sit off
the shape read. -/
example : ¬ rowsLen
    ([[(⟨2, 1⟩ : BPair), ⟨3, 1⟩],
      [⟨1, 2⟩, ⟨5, 1⟩, ⟨4, 1⟩]] : Mat).length
    [[(⟨2, 1⟩ : BPair), ⟨3, 1⟩],
      [⟨1, 2⟩, ⟨5, 1⟩, ⟨4, 1⟩]] := by decide +kernel
/-! Sylvester's identity at the pivot-bordered sublists: the
committed three-by-three and four-by-four read the theorem whole at
one instance each and the full key sweeps by kernel `decide`, with
the exact-cofactor display beside them.  The exact-cofactor display
is `elim.divExact`'s own conclusion, read whole at the
three-by-three below: its `cofactorAt` reads `ground.divMod`'s
quotient through the general naming theorem
`ground.divModRead_all`, the division answering at the quotient
alone wherever the divisor's margin divides the stated pair's.  The
sweeps below are that theorem's instances. -/

private def sylM3 : Mat :=
  [[⟨3, 1⟩, ⟨1, 4⟩, ⟨2, 1⟩],
   [⟨1, 1⟩, ⟨2, 5⟩, ⟨7, 1⟩],
   [⟨5, 2⟩, ⟨1, 1⟩, ⟨1, 3⟩]]

private def sylM4 : Mat :=
  [[⟨2, 1⟩, ⟨1, 3⟩, ⟨4, 1⟩, ⟨1, 1⟩],
   [⟨1, 2⟩, ⟨3, 1⟩, ⟨1, 5⟩, ⟨2, 1⟩],
   [⟨5, 1⟩, ⟨2, 3⟩, ⟨1, 1⟩, ⟨3, 2⟩],
   [⟨1, 4⟩, ⟨6, 1⟩, ⟨2, 2⟩, ⟨1, 7⟩]]

/-- The identity's display at a key triple, the theorem's own
conclusion. -/
private def sylRead (m : Mat) (k i j : Nat) : Prop :=
  (BPair.add
      (BPair.mul (detL (leadAt k m)) (detL (borderAt (k + 1) i j m)))
      (BPair.mul (detL (borderAt k i k m))
        (detL (borderAt k k j m)))).oneValue
    (BPair.mul (detL (borderAt k k k m)) (detL (borderAt k i j m)))

private instance (m : Mat) (k i j : Nat) : Decidable (sylRead m k i j) :=
  inferInstanceAs (Decidable (_ = _))

/-- The exact-cofactor display at a key triple: the leading minor
against the join's cofactor reads the join. -/
private def divExactRead (m : Mat) (k i j : Nat) : Prop :=
  (BPair.mul (detL (leadAt k m))
    (cofactorAt
      (BPair.add
        (BPair.mul (detL (borderAt k k k m)) (detL (borderAt k i j m)))
        (BPair.swap (BPair.mul (detL (borderAt k i k m))
          (detL (borderAt k k j m)))))
      (detL (leadAt k m)))).oneValue
    (BPair.add
      (BPair.mul (detL (borderAt k k k m)) (detL (borderAt k i j m)))
      (BPair.swap (BPair.mul (detL (borderAt k i k m))
        (detL (borderAt k k j m)))))

private instance (m : Mat) (k i j : Nat) :
    Decidable (divExactRead m k i j) :=
  inferInstanceAs (Decidable (_ = _))

example : sylRead sylM3 1 2 2 :=
  sylvester sylM3 (by decide +kernel) 1 2 2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

example : sylRead sylM4 1 2 2 :=
  sylvester sylM4 (by decide +kernel) 1 2 2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- The three-by-three's whole key sweep, each triple inside the
pivot's range. -/
example : sylRead sylM3 0 1 1 ∧ sylRead sylM3 0 1 2
    ∧ sylRead sylM3 0 2 1 ∧ sylRead sylM3 0 2 2
    ∧ sylRead sylM3 1 2 2 := by decide +kernel

/-- The four-by-four's whole key sweep at the second and third
steps. -/
example : sylRead sylM4 1 2 2 ∧ sylRead sylM4 1 2 3
    ∧ sylRead sylM4 1 3 2 ∧ sylRead sylM4 1 3 3
    ∧ sylRead sylM4 2 3 3 := by decide +kernel

/-- The exact-cofactor display at the three-by-three's own
step. -/
example : divExactRead sylM3 1 2 2 := by decide +kernel

/-- The theorem read whole at the three-by-three's own step: the
shape, range and off-unit binders discharged at the datum, the
conclusion `divExactRead`'s own display. -/
example : divExactRead sylM3 1 2 2 :=
  divExact sylM3 (by decide +kernel) 1 2 2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- The exact-cofactor display over the four-by-four's key
sweep. -/
example : divExactRead sylM4 1 2 2 ∧ divExactRead sylM4 1 2 3
    ∧ divExactRead sylM4 1 3 2 ∧ divExactRead sylM4 1 3 3
    ∧ divExactRead sylM4 2 3 3 := by decide +kernel

/-- The singular pivot is not an isolating refusal for the exact
cofactor: at a leading one-by-one reading equal members the whole
display holds, and holds at every such datum.  Sylvester's identity
names the join as the leading minor's multiple, so an
equal-membered pivot sends the join to the sum's unit and both
sides of the cofactor display read there — the refusal the binder
would need is unavailable at this shape, not merely unfound. -/
private def sylMS : Mat :=
  [[⟨2, 2⟩, ⟨1, 4⟩, ⟨2, 1⟩],
   [⟨1, 1⟩, ⟨2, 5⟩, ⟨7, 1⟩],
   [⟨5, 2⟩, ⟨1, 1⟩, ⟨1, 3⟩]]

example : ((detL (leadAt 1 sylMS)).oneValue BPair.unit)
    ∧ divExactRead sylMS 1 2 2 := by decide +kernel

/-- The exactness at an equal-membered pivot, the theorem applied
whole where the identity's both members read the sum's unit. -/
example : divExactRead sylMS 1 2 2 :=
  divExact sylMS (by decide +kernel) 1 2 2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- The discriminating equal-membered-pivot witness: the pivot at
the unit with all four crossing minors off it, the join at the
unit by genuine cancellation, the theorem applied whole. -/
private def sylNM : Mat :=
  [[⟨1, 1⟩, ⟨2, 1⟩, ⟨3, 1⟩],
   [⟨4, 1⟩, ⟨5, 1⟩, ⟨6, 1⟩],
   [⟨7, 1⟩, ⟨8, 1⟩, ⟨10, 1⟩]]

example : ((detL (leadAt 1 sylNM)).oneValue BPair.unit)
    ∧ (¬ (detL (borderAt 1 1 1 sylNM)).oneValue BPair.unit)
    ∧ (¬ (detL (borderAt 1 2 2 sylNM)).oneValue BPair.unit)
    ∧ (¬ (detL (borderAt 1 1 2 sylNM)).oneValue BPair.unit)
    ∧ (¬ (detL (borderAt 1 2 1 sylNM)).oneValue BPair.unit) := by
  decide +kernel

example : divExactRead sylNM 1 2 2 :=
  divExact sylNM (by decide +kernel) 1 2 2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- The first-row fold's own read discharged whole: the minor
collects to the assignment fold and the identity reads at the
collected determinants. -/
example : sylvesterRead sylM3 1 2 2 :=
  sylvesterRead_holds sylM3 (by decide +kernel) 1 2 2 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

example : sylvesterRead sylM4 2 3 3 :=
  sylvesterRead_holds sylM4 (by decide +kernel) 2 3 3 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- The identity at a border row among the leading keys: the
widened read's own instance, the repeated row collapsing both
sides (the former `k < i` binder derivable, its refusal
unconstructible). -/
example : sylvesterRead sylM4 2 1 3 :=
  sylvesterRead_holds sylM4 (by decide +kernel) 2 1 3 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- The identity at a border column among the leading keys, the
column repeat's collapse. -/
example : sylvesterRead sylM4 2 3 0 :=
  sylvesterRead_holds sylM4 (by decide +kernel) 2 3 0 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)


/-- The join at the singular pivot reads the sum's unit, the
identity's own consequence read at the datum. -/
example : (BPair.add
      (BPair.mul (detL (borderAt 1 1 1 sylMS))
        (detL (borderAt 1 2 2 sylMS)))
      (BPair.swap (BPair.mul (detL (borderAt 1 2 1 sylMS))
        (detL (borderAt 1 1 2 sylMS))))).oneValue BPair.unit := by
  decide +kernel

/-! The diagonal-Gram residual: the perpendicular family's Gram
determinant against the self-pairings' product, and the membership
residual against its one-pass spelling entry for entry.  The bench
carries four families at width three — `LP` a perpendicular pair,
`LM` that pair's first row beside an all-unit row, `LZ` one
all-unit row — with `LN` at width two the perpendicularity's own
refusal, and two vectors at `LP`: `vin` its rows' combination and
`vout` off their span.

The bridge is entrywise and takes no read off the unit class: a
unit self-pairing row is itself unit-tail by the pairing's
positivity, so both spellings degenerate together and `LZ`/`LM`
agree exactly where `LP` does.  Three binders bite, each with its
own committed refusal here.  The perpendicularity sits at `LN`,
where the rows pair at the occupied datum: the two spellings part
on the bridge and every row pairs the residual off the sum's unit.
The two shape reads sit at `vwide`, a vector off the stated width
against the empty family on the bridge, and at `LW`, the same read
on `residD_perp` at one occupied row; the rows' width read refuses
on `residD_perp` alone, at the ragged `LR`, and is the bridge's own
frame there — a family ragged below the stated width truncates both
spellings at one length and one value.

The separation between the two residuals is the derived operation
count, priced by arithmetic rather than read off a clock: at `L`
rows the assignment fold walks the `L!` permutations for the
determinant and `g!` more per cofactor entry at the join
`g + 1 = L`, where `residD` walks the family once for `2L` pairings
— each row's self-pairing and its pairing against the vector, every
withheld product the pass's own running datum — factorial against
linear in the pairings.  `L7` below, seven mutually perpendicular
rows of width seven with `perpAll` decided (four signed rows on the
first four keys, two on the next two, one on the last, the supports
meeting at the unit), is the shape the derivation reads at `5040`
against `14`. -/

private def LP : elim.Mat :=
  [[BPair.ofNat 2, BPair.ofNat 1, BPair.unit],
   [BPair.ofNat 1, (BPair.ofNat 2).swap, BPair.unit]]

private def vin : List BPair :=
  [BPair.ofNat 4, (BPair.ofNat 3).swap, BPair.unit]

private def vout : List BPair := [BPair.unit, BPair.unit, BPair.ofNat 1]

private def LM : elim.Mat :=
  [[BPair.ofNat 2, BPair.ofNat 1, BPair.unit],
   [BPair.unit, BPair.unit, BPair.unit]]

private def LZ : elim.Mat := [[BPair.unit, BPair.unit, BPair.unit]]

private def vZ : List BPair :=
  [BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1]

private def LN : elim.Mat :=
  [[BPair.ofNat 1, BPair.unit], [BPair.ofNat 1, BPair.ofNat 1]]

private def vN : List BPair := [BPair.ofNat 2, BPair.ofNat 1]

/-! The shape binders' own families: `LW` one occupied row at width
three against a vector two wide, and `LR` a ragged pair whose head
row alone reads the stated width. -/

private def LW : elim.Mat :=
  [[BPair.ofNat 3, (BPair.ofNat 2).swap, BPair.ofNat 3]]

private def vshort : List BPair :=
  [BPair.ofNat 3, (BPair.ofNat 1).swap]

private def LR : elim.Mat :=
  [[BPair.ofNat 1, BPair.unit, BPair.ofNat 5],
   [BPair.unit, BPair.ofNat 1]]

private def vR : List BPair :=
  [BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1]

private def vwide : List BPair := [BPair.ofNat 1, BPair.ofNat 1]

example : perpAll LP ∧ perpAll LM ∧ perpAll LZ := by decide +kernel
example : ¬ perpAll LN := by decide +kernel

example : rowsLen 3 LP ∧ rowsLen 3 LM ∧ rowsLen 3 LZ := by decide +kernel

/-! The two spellings' verdicts agree: the member passes at both
and the vector off the span refuses at both. -/

example : poly.unitTail (residV 3 LP vin)
    ∧ poly.unitTail (residD LP vin) := by decide +kernel

example : ¬ poly.unitTail (residV 3 LP vout)
    ∧ ¬ poly.unitTail (residD LP vout) := by decide +kernel

example : poly.unitTail (residV 3 LZ vZ)
    ∧ poly.unitTail (residD LZ vZ) := by decide +kernel

example : poly.unitTail (residV 3 LM vin)
    ∧ poly.unitTail (residD LM vin) := by decide +kernel

/-! The entrywise bridge itself, at the member, at the vector off
the span, and at the two degenerate families — with the
perpendicularity binder's refusal beside them. -/

example : poly.oneValue (residV 3 LP vin) (residD LP vin) := by decide +kernel
example : poly.oneValue (residV 3 LP vout) (residD LP vout) := by decide +kernel
example : poly.oneValue (residV 3 LM vin) (residD LM vin) := by decide +kernel
example : poly.oneValue (residV 3 LZ vZ) (residD LZ vZ) := by decide +kernel

/-- The perpendicularity binder is load-bearing: at a family whose
rows pair off the unit every surviving co-binder holds — the width
reads decide — and the entrywise bridge refuses, the determinant
parting from the product with it. -/
example : (rowsLen 2 LN ∧ vN.length = 2)
    ∧ ¬ perpAll LN
    ∧ ¬ poly.oneValue (residV 2 LN vN) (residD LN vN)
    ∧ ¬ (detL (gramM LN)).oneValue (selfProd LN) := by decide +kernel

/-! The bridge's vector-width binder, at the empty family: both
surviving co-binders decide at the stated width one, and a vector
two wide parts the two spellings. -/

example : perpAll ([] : elim.Mat) := by decide +kernel
example : rowsLen 1 ([] : elim.Mat) := by decide +kernel

example : ¬ (vwide.length = 1)
    ∧ ¬ poly.oneValue (residV 1 [] vwide) (residD [] vwide) := by
  decide +kernel

/-- The two shape binders on `residD_perp`, each isolated: at `LW`
the family reads the stated width and pairs perpendicularly while
the vector is two wide, and at `LR` the vector reads that width
while the family runs ragged below it — the head row's own pairing
against the residual off the sum's unit at both. -/
example : (rowsLen 3 LW ∧ perpAll LW ∧ 0 < LW.length)
    ∧ ¬ (vshort.length = 3)
    ∧ ¬ (dotP (ground.getAt [] LW 0) (residD LW vshort)).oneValue
      BPair.unit := by decide +kernel

example : (vR.length = 3 ∧ perpAll LR ∧ 0 < LR.length)
    ∧ ¬ rowsLen 3 LR
    ∧ ¬ (dotP (ground.getAt [] LR 0) (residD LR vR)).oneValue
      BPair.unit := by decide +kernel

/-- The perpendicularity binder on `residD_perp`, isolated at `LN`:
both width reads decide, the family sits below its row count, and
each row's pairing against the residual reads off the sum's
unit. -/
example : (rowsLen 2 LN ∧ vN.length = 2 ∧ 0 < LN.length)
    ∧ ¬ perpAll LN
    ∧ ¬ (dotP (ground.getAt [] LN 0) (residD LN vN)).oneValue
      BPair.unit
    ∧ ¬ (dotP (ground.getAt [] LN 1) (residD LN vN)).oneValue
      BPair.unit := by decide +kernel

/-- The rows' width read is the bridge's frame: at the same ragged
family both spellings truncate to the family's own shorter row and
read one value there, the refusal above sitting at `residD_perp`
alone. -/
example : poly.oneValue (residV 3 LR vR) (residD LR vR) := by decide +kernel

/-! The determinant's own read at the perpendicular families,
kernel twin beside theorem route. -/

example : (detL (gramM LP)).oneValue (selfProd LP) := by decide +kernel
example : (detL (gramM LP)).oneValue (selfProd LP) :=
  elim.detL_perp LP (by decide +kernel)

example : (detL (gramM LM)).oneValue (selfProd LM) := by decide +kernel
example : (detL (gramM LM)).oneValue (selfProd LM) :=
  elim.detL_perp LM (by decide +kernel)

example : (detL (gramM LZ)).oneValue (selfProd LZ) :=
  elim.detL_perp LZ (by decide +kernel)

/-! The residual's perpendicularity and the bridge, each kernel
twin beside its theorem route at `LP`. -/

example : (dotP (ground.getAt [] LP 0) (residD LP vin)).oneValue
    BPair.unit := by decide +kernel
example : (dotP (ground.getAt [] LP 0) (residD LP vin)).oneValue
    BPair.unit :=
  elim.residD_perp 3 LP vin (by decide +kernel) rfl (by decide +kernel) 0 (by decide +kernel)

example : (dotP (ground.getAt [] LP 1) (residD LP vout)).oneValue
    BPair.unit := by decide +kernel
example : (dotP (ground.getAt [] LP 1) (residD LP vout)).oneValue
    BPair.unit :=
  elim.residD_perp 3 LP vout (by decide +kernel) rfl (by decide +kernel) 1 (by decide +kernel)

example : poly.oneValue (residV 3 LP vin) (residD LP vin) :=
  elim.residD_residV 3 LP vin (by decide +kernel) rfl (by decide +kernel)

example : poly.oneValue (residV 3 LP vout) (residD LP vout) :=
  elim.residD_residV 3 LP vout (by decide +kernel) rfl (by decide +kernel)

/-! The degenerate families' bridge, kernel twin above and theorem
route here: the unit self-pairing rows read the binder set the
statement carries, so the theorem itself pins what the kernel
decides. -/

example : poly.oneValue (residV 3 LM vin) (residD LM vin) :=
  elim.residD_residV 3 LM vin (by decide +kernel) rfl (by decide +kernel)

example : poly.oneValue (residV 3 LZ vZ) (residD LZ vZ) :=
  elim.residD_residV 3 LZ vZ (by decide +kernel) rfl (by decide +kernel)

/-! The measured shape: seven mutually perpendicular rows at width
seven, the family's read decided and the one-pass spelling's own
pin inside the budget. -/

private def L7 : elim.Mat :=
  [[BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1,
    BPair.unit, BPair.unit, BPair.unit],
   [BPair.ofNat 1, (BPair.ofNat 1).swap, BPair.ofNat 1,
    (BPair.ofNat 1).swap, BPair.unit, BPair.unit, BPair.unit],
   [BPair.ofNat 1, BPair.ofNat 1, (BPair.ofNat 1).swap,
    (BPair.ofNat 1).swap, BPair.unit, BPair.unit, BPair.unit],
   [BPair.ofNat 1, (BPair.ofNat 1).swap, (BPair.ofNat 1).swap,
    BPair.ofNat 1, BPair.unit, BPair.unit, BPair.unit],
   [BPair.unit, BPair.unit, BPair.unit, BPair.unit,
    BPair.ofNat 1, BPair.ofNat 1, BPair.unit],
   [BPair.unit, BPair.unit, BPair.unit, BPair.unit,
    BPair.ofNat 1, (BPair.ofNat 1).swap, BPair.unit],
   [BPair.unit, BPair.unit, BPair.unit, BPair.unit,
    BPair.unit, BPair.unit, BPair.ofNat 1]]

private def v7 : List BPair :=
  [BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1,
   BPair.ofNat 2, BPair.ofNat 2, BPair.unit]

example : perpAll L7 ∧ rowsLen 7 L7 ∧ v7.length = 7 := by decide +kernel

example : poly.unitTail (residD L7 v7) := by decide +kernel

example : (dotP (ground.getAt [] L7 3) (residD L7 v7)).oneValue
    BPair.unit :=
  elim.residD_perp 7 L7 v7 (by decide +kernel) rfl (by decide +kernel) 3 (by decide +kernel)

/-! The full-length independent family spans (`lem:lowerspan`'s
own sentence, the width bound read forward at the membership's
refusal): at width two the two coordinate rows read
every vector of the width, the theorem beside the decision.  The
two load-bearing binders carry their refusals at the one width: a
one-member independent family is short of the width and misses a
vector outright, and a full-length family with its row repeated is
dependent and misses one too — the count and the independence each
isolated at its own witness. -/

private def F2 : elim.Mat :=
  [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.ofNat 1]]

private def F2short : elim.Mat := [[BPair.ofNat 1, BPair.unit]]

private def F2dep : elim.Mat :=
  [[BPair.ofNat 1, BPair.unit], [BPair.ofNat 1, BPair.unit]]

private def w2 : List BPair := [BPair.ofNat 1, BPair.ofNat 1]

private def e2 : List BPair := [BPair.unit, BPair.ofNat 1]

example : elim.spanRel 2 F2 w2 := by decide +kernel

example : elim.spanRel 2 F2 w2 :=
  elim.span_of_full 2 F2 w2 (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : elim.spanRel 2 F2 (List.replicate 2 BPair.unit) :=
  elim.span_of_full 2 F2 (List.replicate 2 BPair.unit)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : elim.indepRows 2 F2short ∧ ¬ (F2short.length = 2) := by decide +kernel

example : ¬ elim.spanRel 2 F2short e2 := by decide +kernel

example : F2dep.length = 2 ∧ ¬ elim.indepRows 2 F2dep := by decide +kernel

example : ¬ elim.spanRel 2 F2dep e2 := by decide +kernel

/-! The kernel list at the back solve: value and instance pins at
committed matrices, the reads the decidable instances' own.  The
binder classifications: `kernelList_members`' frame carries the
ragged refusal below (`kerRag`), `kernelList_span`'s the over-width
pivot refusal (`kerLong`), `kernelList_length`'s the under-stated
width refusal (`kerNS` at one column key); `kernelList_indep`'s
frame is the tex's own — the matrix total over its stated key
lists — cited with no refusal at the searched region (every ragged
forgery through three rows and four column keys reads independent
regardless), the three refusals beside it the frame's committed
discriminations. -/

/-- The dependent square: the second row the first doubled, the
kernel the `(-2, 1)` line. -/
private def kerM1 : elim.Mat :=
  [[BPair.ofNat 1, BPair.ofNat 2], [BPair.ofNat 2, BPair.ofNat 4]]

/-- The full-column-rank square: the unit family's own matrix, the
kernel empty. -/
private def kerId : elim.Mat :=
  [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.ofNat 1]]

/-- The matrix at the sum's unit throughout: two rows at three
column keys, the kernel everything. -/
private def kerZ : elim.Mat :=
  [[BPair.unit, BPair.unit, BPair.unit],
   [BPair.unit, BPair.unit, BPair.unit]]

/-- The tall shape: three rows at two column keys and full column
rank, the kernel empty. -/
private def kerT : elim.Mat :=
  [[BPair.ofNat 1, BPair.ofNat 1], [BPair.ofNat 1, BPair.ofNat 2],
   [BPair.ofNat 2, BPair.ofNat 3]]

/-- The wide shape: two rows at three column keys, the kernel the
`(1, -2, 1)` line. -/
private def kerW : elim.Mat :=
  [[BPair.ofNat 1, BPair.ofNat 2, BPair.ofNat 3],
   [BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1]]

/-- The rank-one square at three column keys: every row a multiple
of the first, the kernel two-dimensional. -/
private def kerR1 : elim.Mat :=
  [[BPair.ofNat 1, BPair.ofNat 2, BPair.ofNat 3],
   [BPair.ofNat 2, BPair.ofNat 4, BPair.ofNat 6],
   [BPair.ofNat 3, BPair.ofNat 6, BPair.ofNat 9]]

/-- The ragged shape, the dropped-frame probe: the rows carry
unequal key counts and no shape read guards the back solve. -/
private def kerRag : elim.Mat :=
  [[BPair.ofNat 1], [BPair.ofNat 1, BPair.ofNat 2]]

/-- The dependent square's kernel counts one member, the
pivot-free column's own. -/
example : (elim.kernelList 2 kerM1).length = 1 := by decide +kernel

/-- Its pivot count beside the member count. -/
example : elim.rank kerM1 = 1 := by decide +kernel

/-- The member is annihilated: the action reads the sum's unit at
every row. -/
example : poly.unitTail (elim.matVec kerM1
    (ground.getAt [] (elim.kernelList 2 kerM1) 0)) := by decide +kernel

/-- The one-member family is independent, the Gram determinant off
the sum's unit. -/
example : elim.indepRows 2 (elim.kernelList 2 kerM1) := by decide +kernel

/-- The hand kernel `(-2, 1)` sits in the member's span. -/
example : elim.spanRel 2 (elim.kernelList 2 kerM1)
    [(BPair.ofNat 2).swap, BPair.ofNat 1] := by decide +kernel

/-- A vector off that line is refused, the span read discriminating
rather than accepting outright. -/
example : ¬ elim.spanRel 2 (elim.kernelList 2 kerM1)
    [BPair.ofNat 1, BPair.unit] := by decide +kernel

/-- Full column rank empties the kernel list outright. -/
example : elim.kernelList 2 kerId = [] := by decide +kernel

/-- Its pivot count reads the column-key count. -/
example : elim.rank kerId = 2 := by decide +kernel

/-- The matrix at the sum's unit pivots nowhere, so the terminal
seed stands whole: one member per column key. -/
example : (elim.kernelList 3 kerZ).length = 3 := by decide +kernel

/-- Its pivot count is nought. -/
example : elim.rank kerZ = 0 := by decide +kernel

/-- The seed's first member is annihilated. -/
example : poly.unitTail (elim.matVec kerZ
    (ground.getAt [] (elim.kernelList 3 kerZ) 0)) := by decide +kernel

/-- The seed's second member is annihilated. -/
example : poly.unitTail (elim.matVec kerZ
    (ground.getAt [] (elim.kernelList 3 kerZ) 1)) := by decide +kernel

/-- The seed's third member is annihilated. -/
example : poly.unitTail (elim.matVec kerZ
    (ground.getAt [] (elim.kernelList 3 kerZ) 2)) := by decide +kernel

/-- The seed is independent, the unit family at each column's own
key. -/
example : elim.indepRows 3 (elim.kernelList 3 kerZ) := by decide +kernel

/-- The tall shape's kernel is empty. -/
example : (elim.kernelList 2 kerT).length = 0 := by decide +kernel

/-- Its pivot count reads the column-key count. -/
example : elim.rank kerT = 2 := by decide +kernel

/-- The wide shape's kernel counts one member. -/
example : (elim.kernelList 3 kerW).length = 1 := by decide +kernel

/-- Its pivot count sits one below the column-key count. -/
example : elim.rank kerW = 2 := by decide +kernel

/-- The wide shape's member is annihilated. -/
example : poly.unitTail (elim.matVec kerW
    (ground.getAt [] (elim.kernelList 3 kerW) 0)) := by decide +kernel

/-- The rank-one square's kernel counts two members. -/
example : (elim.kernelList 3 kerR1).length = 2 := by decide +kernel

/-- Its pivot count is one. -/
example : elim.rank kerR1 = 1 := by decide +kernel

/-- The two members are independent, the two rounds' extensions
separating them. -/
example : elim.indepRows 3 (elim.kernelList 3 kerR1) := by decide +kernel

/-- The first member is annihilated. -/
example : poly.unitTail (elim.matVec kerR1
    (ground.getAt [] (elim.kernelList 3 kerR1) 0)) := by decide +kernel

/-- The second member is annihilated. -/
example : poly.unitTail (elim.matVec kerR1
    (ground.getAt [] (elim.kernelList 3 kerR1) 1)) := by decide +kernel

/-- The dropped-frame probe: the members sit at the stated width at
ragged data, `kernelList_rowsLen` stating it hypothesis-free. -/
example : elim.rowsLen 2 (elim.kernelList 2 kerRag) := by decide +kernel

/-! The length bridge: the dimension read hypothesis-free with the
sum form's frame refusal — an under-stated width over-counts
pivots against it, the truncated read absorbing what the sum form
must not. -/

/-- The nonsingular square: full column rank at two column keys,
the kernel empty. -/
private def kerNS : elim.Mat :=
  [[BPair.ofNat 1, BPair.ofNat 2], [BPair.ofNat 3, BPair.ofNat 4]]

/-- Under-stated width: the back solve's terminal seed is already
empty, so the member count is nought. -/
example : (elim.kernelList 1 kerNS).length = 0 := by decide +kernel

/-- Its pivot count reads two, past the under-stated width. -/
example : elim.rank kerNS = 2 := by decide +kernel

/-- The frame refusal for `kernelList_length`'s `hm`: at the
under-stated width the sum form fails outright, the pivot count
over-running the width the rows do not carry. -/
example : ¬ ((elim.kernelList 1 kerNS).length + elim.rank kerNS
    = 1) := by decide +kernel

/-- The dropped binder's probe: the dimension read holds at that
same forgery, the truncation absorbing the over-run. -/
example : (elim.kernelList 1 kerNS).length
    = elim.kernelDim 1 kerNS := by decide +kernel

/-- Over-stated width: the extra column is a genuine kernel
direction and the dimension read counts it. -/
example : (elim.kernelList 3 kerNS).length
    = elim.kernelDim 3 kerNS := by decide +kernel

/-- The over-stated width's member is annihilated. -/
example : poly.unitTail (elim.matVec kerNS
    (ground.getAt [] (elim.kernelList 3 kerNS) 0)) := by decide +kernel

/-- The frame instance at the committed singular matrix: the sum
form reads the stated width whole. -/
example : (elim.kernelList 2 kerM1).length + elim.rank kerM1 = 2 :=
  by decide +kernel

/-! The kernel tier's reads applied whole, with the frame's
refusals: the members, independence and span theorems at the
committed matrices, the ragged forgery breaking the members read
exactly where the stated width's frame is withdrawn.  The span
read's `hker` binder is already refused above, the non-kernel
`(1, unit)` line at `kerM1` discriminated by the read itself, so
nothing is duplicated here. -/

/-- The dependent square's member annihilated by the theorem, the
value pin's own read at its proof. -/
example : poly.unitTail (elim.matVec kerM1
    (ground.getAt [] (elim.kernelList 2 kerM1) 0)) :=
  elim.kernelList_members 2 kerM1 (by decide +kernel) 0 (by decide +kernel)

/-- The rank-one square's first member at the theorem. -/
example : poly.unitTail (elim.matVec kerR1
    (ground.getAt [] (elim.kernelList 3 kerR1) 0)) :=
  elim.kernelList_members 3 kerR1 (by decide +kernel) 0 (by decide +kernel)

/-- Its second member at the theorem, the two rounds' extensions
both annihilated. -/
example : poly.unitTail (elim.matVec kerR1
    (ground.getAt [] (elim.kernelList 3 kerR1) 1)) :=
  elim.kernelList_members 3 kerR1 (by decide +kernel) 1 (by decide +kernel)

/-- The wide shape's member at the theorem. -/
example : poly.unitTail (elim.matVec kerW
    (ground.getAt [] (elim.kernelList 3 kerW) 0)) :=
  elim.kernelList_members 3 kerW (by decide +kernel) 0 (by decide +kernel)

/-- The rank-one square's kernel list independent at the theorem,
the two members separated at their own pivot-free columns. -/
example : elim.indepRows 3 (elim.kernelList 3 kerR1) :=
  elim.kernelList_indep 3 kerR1 (by decide +kernel)

/-- The hand kernel `(-2, 1)` joins the member's span at the
theorem, the decided hypotheses discharging the frame, the width
and the annihilation. -/
example : elim.spanRel 2 (elim.kernelList 2 kerM1)
    [(BPair.ofNat 2).swap, BPair.ofNat 1] :=
  elim.kernelList_span 2 kerM1 (by decide +kernel)
    [(BPair.ofNat 2).swap, BPair.ofNat 1] (by decide +kernel) (by decide +kernel)

/-- The members frame refusal, `kernelList_members`' `hm` binder:
at the ragged matrix the computed member reads `2` against the
second row, so the action carries an off-unit entry and the
theorem's conclusion fails outright where the stated width is
withdrawn. -/
example : ¬ poly.unitTail (elim.matVec kerRag
    (ground.getAt [] (elim.kernelList 2 kerRag) 0)) := by decide +kernel

/-- The over-long row: one occupied key past the stated width, the
row list otherwise at the sum's unit. -/
private def kerLong : elim.Mat :=
  [[BPair.unit, BPair.unit, BPair.ofNat 1], [BPair.unit]]

/-- The `(unit, 1)` line is annihilated at that shape, the action
truncating at the stated width. -/
example : poly.unitTail (elim.matVec kerLong
    [BPair.unit, BPair.ofNat 1]) := by decide +kernel

/-- The span frame refusal, `kernelList_span`'s `hm` binder: the
descent pivots at the occupied key past the stated width, burning a
pivot the stated frame does not carry, so the back solve under-counts
and the annihilated line above sits outside the kernel list's span
— the hypothesis withdrawn, the conclusion false. -/
example : ¬ elim.spanRel 2 (elim.kernelList 2 kerLong)
    [BPair.unit, BPair.ofNat 1] := by decide +kernel
/-! `def:elim`'s pivot descent read against the assignment fold
(`detD_eq`): the coherence pins at committed square lists with
their hand values, the row exchange at a leading entry sitting at
the sum's unit, the stall clause at a pivot column whose bordered
minors read the unit — at the seeded step and at the step past it
— and the Gram's square frame beside its own decision.  The square
binder carries its refusal at a list whose border row is short of
the width: the step's row truncates at the shorter tail, so the
descent reads the sum's unit where the fold reads six against it. -/

private def Dsq2 : Mat :=
  [[BPair.ofNat 1, BPair.ofNat 2], [BPair.ofNat 3, BPair.ofNat 4]]

private def Dsq3 : Mat :=
  [[BPair.ofNat 1, BPair.ofNat 2, BPair.ofNat 3],
   [BPair.ofNat 4, (BPair.ofNat 5).swap, BPair.ofNat 6],
   [BPair.ofNat 7, BPair.ofNat 8, BPair.ofNat 2]]

/-- The exchange's own list: the leading entry at the sum's unit
with the entry below it occupied, the pivot row moved up. -/
private def Dexch : Mat :=
  [[BPair.unit, BPair.ofNat 1], [BPair.ofNat 1, BPair.unit]]

/-- The stall at the seeded step: the leading column at the sum's
unit throughout. -/
private def Dstall : Mat :=
  [[BPair.unit, BPair.unit], [BPair.unit, BPair.ofNat 1]]

/-- The stall one step in: the seeded step pivots at the leading
entry and the surviving block's own leading column reads the sum's
unit at both rows. -/
private def Dstall3 : Mat :=
  [[BPair.ofNat 1, BPair.unit, BPair.unit],
   [BPair.unit, BPair.unit, BPair.ofNat 1],
   [BPair.unit, BPair.unit, BPair.ofNat 2]]

/-- The stall clause's off-unit hypothesis isolated: the cyclic
list's every bordered minor at pivot column one reads the unit and
the leading minor reads it with them, while the determinant sits
off it: the clause's conclusion refused exactly where its stated
off-unit read fails, the descent's own read untouched. -/
private def Dcyc : Mat :=
  [[BPair.unit, BPair.unit, BPair.ofNat 1],
   [BPair.ofNat 1, BPair.unit, BPair.unit],
   [BPair.unit, BPair.ofNat 1, BPair.unit]]

example : (detL (borderAt 1 0 1 Dcyc)).oneValue BPair.unit
    ∧ (detL (borderAt 1 1 1 Dcyc)).oneValue BPair.unit
    ∧ (detL (borderAt 1 2 1 Dcyc)).oneValue BPair.unit := by decide +kernel

example : (detL (leadAt 1 Dcyc)).oneValue BPair.unit := by decide +kernel

example : ¬ (detL Dcyc).oneValue BPair.unit := by decide +kernel

example : (detD Dcyc).oneValue (detL Dcyc) := by decide +kernel

/-- The square frame's refusal: a ragged list, the border row
short of the width.  A uniform-width rectangle satisfies the
equality, the fold and the descent both reading the leading square
block; the refusal is raggedness. -/
private def Dshort : Mat :=
  [[BPair.ofNat 1, BPair.ofNat 2], [BPair.ofNat 3]]

example : (detD Dsq2).oneValue (detL Dsq2) := by decide +kernel

example : (detD Dsq2).oneValue (BPair.ofNat 2).swap := by decide +kernel

example : (detD Dsq3).oneValue (detL Dsq3) := by decide +kernel

example : (detD Dsq3).oneValue (BPair.ofNat 211) := by decide +kernel

example : (detD Dsq3).oneValue (detL Dsq3) := detD_eq Dsq3 (by decide +kernel)

example : (detD Dexch).oneValue (detL Dexch) := by decide +kernel

example : (detD Dexch).oneValue (BPair.ofNat 1).swap := by decide +kernel

example : (detD Dstall).oneValue (detL Dstall) := by decide +kernel

example : (detD Dstall).oneValue BPair.unit := by decide +kernel

example : (detD Dstall3).oneValue (detL Dstall3) := by decide +kernel

example : (detD Dstall3).oneValue BPair.unit := by decide +kernel

example : rowsLen (gramM Dsq3).length (gramM Dsq3) := by decide +kernel

example : rowsLen (gramM Dsq3).length (gramM Dsq3) := gramM_sq Dsq3

example : ¬ rowsLen Dshort.length Dshort := by decide +kernel

example : (detL Dshort).oneValue (BPair.ofNat 6).swap := by decide +kernel

example : (detD Dshort).oneValue BPair.unit := by decide +kernel

example : ¬ (detD Dshort).oneValue (detL Dshort) := by decide +kernel

/-! The kernel-join tier (`lem:blockcount`(ii)'s arriving sum): the
two sides' kernel dimensions and the joined datum's own, the
dimensions' addition at `kernelDim_rowJoin` applied whole with its
split hypothesis discharged at the committed pair, and the two
refusals isolating the theorem's binders — the row-count tie and
the split hypothesis itself.  The basis-freedom pin closes it,
`kernelDim_congr`'s display at two committed bases of one span. -/

/-- The sides' kernel dimensions at the committed pair: the
occupied row at two column keys carries one pivot, the unit row
none. -/
example : elim.kernelDim 2 [[BPair.ofNat 1, BPair.unit]] = 1 := by decide +kernel

example : elim.kernelDim 1 [[BPair.unit]] = 1 := by decide +kernel

/-- The sum's dimension is the sides' sum at the joined datum. -/
example : elim.kernelDim 3
    (elim.rowJoin [[BPair.ofNat 1, BPair.unit]] [[BPair.unit]])
    = 2 := by decide +kernel

/-- `kernelDim_rowJoin` applied whole: the second side's unit row
makes every joined kernel read the first side's own, the split
hypothesis's committed instance.  The discharge splits the joined
row's pairing at the seam (`dotP_append` at the first side's own
width), reads the second summand off the unit row
(`dotP_null_tail_left`, the ROW the left argument), and returns the
first side's fold by the sum's unit law. -/
example : elim.kernelDim 2 [[BPair.ofNat 1, BPair.unit]]
    + elim.kernelDim 1 [[BPair.unit]]
    = elim.kernelDim 3
      (elim.rowJoin [[BPair.ofNat 1, BPair.unit]] [[BPair.unit]]) :=
  elim.kernelDim_rowJoin 2 1 _ _ (by decide +kernel) (by decide +kernel) rfl
    (fun v w hv _ hker => by
      refine ⟨BPair.oneValue_trans
        (elim.dotN_dotP [BPair.ofNat 1, BPair.unit] v) ?_, trivial⟩
      refine BPair.oneValue_trans
        (BPair.oneValue_symm (BPair.add_unit _)) ?_
      refine BPair.oneValue_trans
        (BPair.oneValue_symm (BPair.add_congr (BPair.oneValue_refl _)
          (elim.dotP_null_tail_left [BPair.unit] w (by decide +kernel)))) ?_
      exact BPair.oneValue_trans
        (BPair.oneValue_symm (elim.dotP_append
          [BPair.ofNat 1, BPair.unit] v [BPair.unit] w hv.symm))
        (BPair.oneValue_trans
          (BPair.oneValue_symm (elim.dotN_dotP
            ([BPair.ofNat 1, BPair.unit] ++ [BPair.unit]) (v ++ w)))
          hker.1))

/-- Refusal at the row-count tie, `kernelDim_rowJoin`'s `hl`
binder: the second side's surplus row drops from the truncating
join, the joined datum reads empty at two column keys against the
sides' one, and the dimensions do not add — while the split
hypothesis survives at the empty first side, pinned beside, so the
refusal isolates the tie alone. -/
example : ¬ (elim.kernelDim 1 ([] : elim.Mat)
    + elim.kernelDim 1 [[BPair.ofNat 1]]
    = elim.kernelDim 2
      (elim.rowJoin ([] : elim.Mat) [[BPair.ofNat 1]])) := by decide +kernel

/-- The split hypothesis's survival at the refusal's shape: the
first side's action is the vacant fold. -/
example : ∀ v w : List BPair, v.length = 1 → w.length = 1 →
    poly.unitTail (elim.matVec
      (elim.rowJoin ([] : elim.Mat) [[BPair.ofNat 1]]) (v ++ w)) →
    poly.unitTail (elim.matVec ([] : elim.Mat) v) :=
  fun _ _ _ _ _ => trivial

/-- Refusal at the split hypothesis, `kernelDim_rowJoin`'s `hyp`
binder: a coupled row's kernel mixes the sides — each side alone
carries its own pivot while the joined row carries one — and the
dimensions do not add. -/
example : ¬ (elim.kernelDim 1 [[BPair.ofNat 1]]
    + elim.kernelDim 1 [[BPair.ofNat 1]]
    = elim.kernelDim 2
      (elim.rowJoin [[BPair.ofNat 1]] [[BPair.ofNat 1]])) := by decide +kernel

/-- Two bases of one span read one kernel dimension at the stacked
row, `kernelDim_congr`'s display: the committed basis and its
column-added partner span one plane, the two cross data differ —
pinned beside — and the kernel counts one at both, so the pin
discriminates the bases while the count reads through them. -/
example : elim.kernelDim 2
      (elim.crossM [[BPair.ofNat 1, BPair.ofNat 1]]
        [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.ofNat 1]])
    = elim.kernelDim 2
      (elim.crossM [[BPair.ofNat 1, BPair.ofNat 1]]
        [[BPair.ofNat 1, BPair.ofNat 1],
          [BPair.unit, BPair.ofNat 1]]) := by decide +kernel

/-- The two cross data differ at the stacked row, the pin's own
discrimination. -/
example : ¬ (elim.crossM [[BPair.ofNat 1, BPair.ofNat 1]]
      [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.ofNat 1]]
    = elim.crossM [[BPair.ofNat 1, BPair.ofNat 1]]
      [[BPair.ofNat 1, BPair.ofNat 1],
        [BPair.unit, BPair.ofNat 1]]) := by decide +kernel

/-- Both committed bases are independent, the display's frame. -/
example : elim.indepRows 2
      [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.ofNat 1]]
    ∧ elim.indepRows 2
      [[BPair.ofNat 1, BPair.ofNat 1],
        [BPair.unit, BPair.ofNat 1]] := by decide +kernel

/-! The identity datum's and the collection's binder classifications
at their committed refusals: the width frames refuse at the
truncating folds, the rank's hypothesis at one occupied entry. -/

/-- Refusal at `collect_single`'s width frame: off the stated width
the residual truncates and the collection drops the member. -/
example : ¬ (elim.collectOf 0 [[BPair.ofNat 1]]
    = [[BPair.ofNat 1]]) := by decide +kernel

/-- Refusal at `matVec_idList`'s width frame: the identity at a
narrower width truncates the vector. -/
example : ¬ (poly.oneValue (elim.matVec (elim.idList 1)
    [BPair.ofNat 1, BPair.ofNat 2])
    [BPair.ofNat 1, BPair.ofNat 2]) := by decide +kernel

/-- Refusal at `rank_null`'s hypothesis: one off-unit entry reads
one pivot. -/
example : elim.rank [[BPair.unit, BPair.ofNat 1]] = 1 := by decide +kernel

/-- The value pins beside the refusals: the unit-tailed rows'
rank, the kept one-member collection, the identity's action at
the stated width. -/
example : elim.rank [[BPair.unit, BPair.unit],
    [BPair.unit, BPair.unit]] = 0 := by decide +kernel

example : elim.collectOf 2 [[BPair.ofNat 1, BPair.unit]]
    = [[BPair.ofNat 1, BPair.unit]] := by decide +kernel

example : poly.oneValue (elim.matVec (elim.idList 2)
    [BPair.ofNat 1, BPair.ofNat 2])
    [BPair.ofNat 1, BPair.ofNat 2] := by decide +kernel

/-! The identity family's independence and its cross reading
(`indepRows_idList`, `kernelDim_idList`): the family decided
independent at a committed width beside its theorem route, the
cross datum returning the stacked row entry by entry, the two
kernel dimensions decided one count beside their theorem route,
and the refusal isolating the stacked family's width binder. -/

/-- The identity family at three column keys is independent, the
Gram determinant the self-pairings' product. -/
example : elim.indepRows 3 (elim.idList 3) := by decide +kernel

example : elim.indepRows 3 (elim.idList 3) := elim.indepRows_idList 3

/-- The cross datum at the identity family is the stacked row
itself, entry by entry at the representatives. -/
example : elim.crossM [[BPair.ofNat 1, BPair.ofNat 2]]
    (elim.idList 2) = [[BPair.ofNat 1, BPair.ofNat 2]] := by decide +kernel

/-- The two kernel dimensions are one count at a committed stacked
row. -/
example : elim.kernelDim 2
    (elim.crossM [[BPair.ofNat 1, BPair.ofNat 1]] (elim.idList 2))
    = elim.kernelDim 2 [[BPair.ofNat 1, BPair.ofNat 1]] := by decide +kernel

example : elim.kernelDim 2
    (elim.crossM [[BPair.ofNat 1, BPair.ofNat 1]] (elim.idList 2))
    = elim.kernelDim 2 [[BPair.ofNat 1, BPair.ofNat 1]] :=
  elim.kernelDim_idList 2 _ ⟨rfl, trivial⟩

/-- Refusal at `kernelDim_idList`'s width binder: a stacked row
wider than the stated key count meets the identity family at a
truncating fold, the cross row reads the sum's unit throughout and
loses the row's own pivot, so the counts part. -/
example : ¬ (elim.kernelDim 1
    (elim.crossM [[BPair.unit, BPair.ofNat 1]] (elim.idList 1))
    = elim.kernelDim 1 [[BPair.unit, BPair.ofNat 1]]) := by decide +kernel

/-! The adjugate at the committed squares: both products read the
determinant's diagonal at the occupied 3-by-3 and at the singular
square outright, the identity binder-free at either side
(`def:elim`'s adjugate identity at the exchanged row and column
lists).  The diagonal partners are spelled at the values the
determinants read, the scaled identity in the entry carrier's own
letters. -/

/-- The occupied committed square, determinant 8. -/
private def adjG3 : Mat :=
  [[BPair.ofNat 2, BPair.ofNat 1, BPair.unit],
   [BPair.ofNat 1, BPair.ofNat 3, BPair.ofNat 1],
   [BPair.unit, BPair.ofNat 1, BPair.ofNat 2]]

/-- The occupied square's diagonal partner, the determinant at each
diagonal key. -/
private def adjD3 : Mat :=
  [[BPair.ofNat 8, BPair.unit, BPair.unit],
   [BPair.unit, BPair.ofNat 8, BPair.unit],
   [BPair.unit, BPair.unit, BPair.ofNat 8]]

example : (detL adjG3).oneValue (BPair.ofNat 8) := by decide +kernel

example : matOneValue (matMul adjG3 (adjM adjG3)) adjD3 := by decide +kernel

example : matOneValue (matMul (adjM adjG3) adjG3) adjD3 := by decide +kernel

/-- The singular committed square: its rows are proportional. -/
private def adjG2s : Mat :=
  [[BPair.ofNat 1, BPair.ofNat 2],
   [BPair.ofNat 2, BPair.ofNat 4]]

/-- The singular square's diagonal partner, the sum's unit at every
key. -/
private def adjD2s : Mat :=
  [[BPair.unit, BPair.unit], [BPair.unit, BPair.unit]]

example : (detL adjG2s).oneValue BPair.unit := by decide +kernel

example : matOneValue (matMul adjG2s (adjM adjG2s)) adjD2s := by decide +kernel

example : matOneValue (matMul (adjM adjG2s) adjG2s) adjD2s := by decide +kernel

example : indepRows 3 adjG3 := by decide +kernel

example : (detL adjG3).offUnit := by decide +kernel

/-! The theorem routes: each identity applied whole at the occupied
square, every binder decided bare. -/

example : (ground.getAt BPair.unit
    (ground.getAt [] (matMul adjG3 (adjM adjG3)) 1) 1).oneValue
    (detL adjG3) :=
  adjM_row_diag adjG3 (n := 3) (by decide +kernel) 1 (by decide +kernel)

example : (ground.getAt BPair.unit
    (ground.getAt [] (matMul adjG3 (adjM adjG3)) 0) 2).oneValue
    BPair.unit :=
  adjM_row_off adjG3 (n := 3) (by decide +kernel) 0 2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : (ground.getAt BPair.unit
    (ground.getAt [] (matMul (adjM adjG3) adjG3) 2) 2).oneValue
    (detL adjG3) :=
  adjM_col_diag adjG3 (n := 3) (by decide +kernel) 2 (by decide +kernel)

example : (ground.getAt BPair.unit
    (ground.getAt [] (matMul (adjM adjG3) adjG3) 2) 0).oneValue
    BPair.unit :=
  adjM_col_off adjG3 (n := 3) (by decide +kernel) 2 0 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- The column side at the singular square, applied whole: the
identity with every binder decided bare and the diagonal the
determinant's own unit read. -/
example : (ground.getAt BPair.unit
    (ground.getAt [] (matMul (adjM adjG2s) adjG2s) 1) 1).oneValue
    (detL adjG2s) :=
  adjM_col_diag adjG2s (n := 2) (by decide +kernel) 1 (by decide +kernel)

/-- The row side at the singular square, applied whole: the
determinant's read at the diagonal with no independence binder. -/
example : (ground.getAt BPair.unit
    (ground.getAt [] (matMul adjG2s (adjM adjG2s)) 0) 0).oneValue
    (detL adjG2s) :=
  adjM_row_diag adjG2s (n := 2) (by decide +kernel) 0 (by decide +kernel)


/-! The null collection's pins: at unit-tailed rows every residual
passes and the collection is vacant, the refusal-shaped control at
one off-unit row, and the span read's own binder isolated at a
single off-unit row carrying itself. -/

/-- The collection at a two-row unit matrix of width two is
vacant, the theorem's instance with the value beside it. -/
example : elim.collectOf 2
    [[BPair.unit, BPair.unit], [BPair.unit, BPair.unit]] = [] :=
  elim.collect_nil_of_units 2
    [[BPair.unit, BPair.unit], [BPair.unit, BPair.unit]] (by decide +kernel)

example : elim.collectOf 2
    [[BPair.unit, BPair.unit], [BPair.unit, BPair.unit]] = [] := by decide +kernel

/-- Refusal isolating `collect_nil_of_units`' rows binder: one
off-unit row joins the collection and the read parts from the
vacant list. -/
example : ¬ (elim.collectOf 2
    [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.unit]] = []) := by
  decide +kernel

/-- Refusal isolating `spanRel_unit_of_units`' rows binder: an
off-unit single row sits in its own span while its tail reads off
the sum's unit, so the conclusion parts at the dropped binder. -/
example : elim.spanRel 2 [[BPair.ofNat 1, BPair.unit]]
    [BPair.ofNat 1, BPair.unit] := by decide +kernel

example : ¬ poly.unitTail [BPair.ofNat 1, BPair.unit] := by decide +kernel
/-! The Gram's two reads, applied whole: the row at an occupied key
is the stated row's pairings against every row, and the entry at
two occupied keys is the two rows' own pairing. -/

example : ground.getAt [] (gramM Dsq2) 1
    = Dsq2.map (fun c => dotP (ground.getAt [] Dsq2 1) c) :=
  gramM_row Dsq2 1 (by decide +kernel)

example : ground.getAt BPair.unit
    (ground.getAt [] (gramM Dsq2) 1) 0
    = dotP (ground.getAt [] Dsq2 1) (ground.getAt [] Dsq2 0) :=
  gramM_entry Dsq2 1 0 (by decide +kernel) (by decide +kernel)

/-! `lem:lowerspan`'s independence reads at committed data: a
combination pairing every row at the sum's unit reads its
coefficients at the unit family, and an independent list stands as
its own collection — each pinned through its theorem with the value
beside it, and one refusal per binder. -/

private def Lperp : elim.Mat :=
  [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.ofNat 1]]

private def fperp : List BPair := [BPair.unit, BPair.unit]

private def Ldbl : elim.Mat := [[BPair.ofNat 2], [BPair.ofNat 2]]

private def fdbl : List BPair :=
  [BPair.ofNat 1, (BPair.ofNat 1).swap]

private def Lone : elim.Mat := [[BPair.ofNat 2]]

private def fwide : List BPair := [BPair.unit, BPair.ofNat 2]

/-- The unit family's combination pairs both rows of an independent
pair at the sum's unit, so the coefficients read at the unit family
— the theorem applied whole beside its conclusion's own value. -/
example : poly.unitTail fperp :=
  indep_perp_null 2 Lperp (by decide +kernel) fperp (by decide +kernel) (by decide +kernel)

example : (combo 2 fperp Lperp).map BPair.norm
    = [BPair.unit, BPair.unit] := by decide +kernel

/-- Refusal isolating `indep_perp_null`'s independence binder: at a
doubled row the balanced coefficient family's combination pairs
every row at the sum's unit while the family itself sits off the
unit tail. -/
example : ¬ indepRows 1 Ldbl := by decide +kernel

example : fdbl.length = Ldbl.length := by decide +kernel

example : ∀ l, l < Ldbl.length →
    (dotP (combo 1 fdbl Ldbl)
      (ground.getAt [] Ldbl l)).oneValue BPair.unit := by decide +kernel

example : ¬ poly.unitTail fdbl := by decide +kernel

/-- Refusal isolating `indep_perp_null`'s count binder: a
coefficient family one past the rows' count pairs the single row at
the sum's unit while the family sits off the unit tail. -/
example : indepRows 1 Lone := by decide +kernel

example : ¬ (fwide.length = Lone.length) := by decide +kernel

example : ∀ l, l < Lone.length →
    (dotP (combo 1 fwide Lone)
      (ground.getAt [] Lone l)).oneValue BPair.unit := by decide +kernel

example : ¬ poly.unitTail fwide := by decide +kernel

/-- Refusal isolating `indep_perp_null`'s perpendicularity binder:
an off-unit coefficient at an independent one-row family pairs the
combination against the row off the unit, and the conclusion
refuses. -/
private def Lone2 : Mat := [[BPair.ofNat 2]]

private def fbad : List BPair := [BPair.ofNat 1]

example : indepRows 1 Lone2 := by decide +kernel

example : fbad.length = Lone2.length := by decide +kernel

example : ¬ (∀ l, l < Lone2.length →
    (dotP (combo 1 fbad Lone2)
      (ground.getAt [] Lone2 l)).oneValue BPair.unit) := by decide +kernel

example : ¬ poly.unitTail fbad := by decide +kernel

/-- An independent pair stands as its own collection, every row
refused by the accumulator's residual — the theorem applied whole
beside the collection's own value. -/
example : collectOf 2 Lperp = Lperp :=
  collect_keep 2 Lperp (by decide +kernel)

example : collectOf 2 Lperp = Lperp := by decide +kernel

/-- Refusal isolating `collect_keep`'s independence binder: the
doubled row passes the accumulator's residual and the collection
parts from the listed rows. -/
example : ¬ (collectOf 1 Ldbl = Ldbl) := by decide +kernel

/-! The matched-Gram kernel engine's own data (`kernelDim_gram`):
one stacked family at width two, the plain pair beside the turned
pair whose stacked images' Gram doubles it, and the three families
that withdraw one binder each. -/

/-- The stacked family the Gram batteries read against: the width's
own pair, so each row's image is that row. -/
private def gramStack : Mat :=
  [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.ofNat 1]]

/-- The turned pair: perpendicular still, each self-pairing twice
the plain pair's, so the two Grams agree at the scales two and
one. -/
private def gramTurn : Mat :=
  [[BPair.ofNat 1, BPair.ofNat 1], [BPair.ofNat 1, (BPair.ofNat 1).swap]]

/-- The unit family: every stacked image at the sum's unit, so its
whole Gram sits there. -/
private def gramNull : Mat :=
  [[BPair.unit, BPair.unit], [BPair.unit, BPair.unit]]

/-- The pair with its second row withdrawn to the sum's unit: one
Gram entry parts from the plain pair's. -/
private def gramDrop : Mat :=
  [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.unit]]

/-- The one-row family: the withdrawn row is exactly the one
`gramDrop` reads at the sum's unit, so the two Grams still agree
while the counts part. -/
private def gramShort : Mat := [[BPair.ofNat 1, BPair.unit]]

/-- The engine applied whole: the turned pair's Gram against the
plain pair's at the scales two and one, one kernel dimension across
the two families. -/
example : kernelDim gramTurn.length (crossM gramStack gramTurn)
    = kernelDim gramStack.length (crossM gramStack gramStack) :=
  kernelDim_gram 2 gramStack gramStack gramTurn
    (BPair.ofNat 2) (BPair.ofNat 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

example : kernelDim gramTurn.length (crossM gramStack gramTurn)
    = kernelDim gramStack.length (crossM gramStack gramStack) := by
  decide +kernel

/-- Refusal isolating `kernelDim_gram`'s first scale binder: at the
sum's unit the scaled read collapses, the unit family answers the
displayed agreement at every key pair, and the two counts part at
two against nought. -/
example : BPair.unit.oneValue BPair.unit := by decide +kernel

example : ∀ k, k < gramStack.length → ∀ l, l < gramStack.length →
    (BPair.ofNat 1 * dotP (matVec gramStack (ground.getAt [] gramNull k))
        (matVec gramStack (ground.getAt [] gramNull l))).oneValue
      (BPair.unit * dotP (matVec gramStack (ground.getAt [] gramStack k))
        (matVec gramStack (ground.getAt [] gramStack l))) := by decide +kernel

example : ¬ (kernelDim gramNull.length (crossM gramStack gramNull)
    = kernelDim gramStack.length (crossM gramStack gramStack)) := by
  decide +kernel

/-- Refusal isolating `kernelDim_gram`'s second scale binder: the
mirror of the first, the unit family now the read-against family,
and the two counts part at nought against two. -/
example : ∀ k, k < gramNull.length → ∀ l, l < gramNull.length →
    (BPair.unit * dotP (matVec gramStack (ground.getAt [] gramStack k))
        (matVec gramStack (ground.getAt [] gramStack l))).oneValue
      (BPair.ofNat 1 * dotP (matVec gramStack (ground.getAt [] gramNull k))
        (matVec gramStack (ground.getAt [] gramNull l))) := by decide +kernel

example : ¬ (kernelDim gramStack.length (crossM gramStack gramStack)
    = kernelDim gramNull.length (crossM gramStack gramNull)) := by
  decide +kernel

-- The three width binders `hR`, `hL`, `hL'` stand at the stated
-- shape carrier, `def:elim`'s stated-key-list frame — the same
-- frame `matVec_crossM` carries.  Eight ragged probes at width two
-- found no refusal: at [[1, 0], [1]] and at [[1], [0, 1]] for the
-- stacked family, and at [[1, 0], [0]], [[1, 0], []], [[], []],
-- [[1, 0, 1], [0, 1]], [[1], [0, 1]] for either read family, every
-- probe whose displayed Gram agreement survives the raggedness
-- reads the two counts equal, and every probe that parts the counts
-- parts the Gram agreement first.  The probes are recorded here,
-- not committed as pins.

/-- Refusal isolating `kernelDim_gram`'s Gram binder: the withdrawn
row parts the self-pairing at the second key, and the counts part
at one against nought. -/
example : ¬ (∀ k, k < gramStack.length → ∀ l, l < gramStack.length →
    (BPair.ofNat 1 * dotP (matVec gramStack (ground.getAt [] gramDrop k))
        (matVec gramStack (ground.getAt [] gramDrop l))).oneValue
      (BPair.ofNat 1 * dotP (matVec gramStack (ground.getAt [] gramStack k))
        (matVec gramStack (ground.getAt [] gramStack l)))) := by decide +kernel

example : ¬ (kernelDim gramDrop.length (crossM gramStack gramDrop)
    = kernelDim gramStack.length (crossM gramStack gramStack)) := by
  decide +kernel

/-- Refusal isolating `kernelDim_gram`'s count binder: the one-row
family answers the displayed Gram agreement at every key pair of
the two-row family — the withdrawn row reads the sum's unit on both
sides — while the kernel counts part at nought against one. -/
example : ¬ (gramShort.length = gramDrop.length) := by decide +kernel

example : ∀ k, k < gramDrop.length → ∀ l, l < gramDrop.length →
    (BPair.ofNat 1 * dotP (matVec gramStack (ground.getAt [] gramShort k))
        (matVec gramStack (ground.getAt [] gramShort l))).oneValue
      (BPair.ofNat 1 * dotP (matVec gramStack (ground.getAt [] gramDrop k))
        (matVec gramStack (ground.getAt [] gramDrop l))) := by decide +kernel

example : ¬ (kernelDim gramShort.length (crossM gramStack gramShort)
    = kernelDim gramDrop.length (crossM gramStack gramDrop)) := by
  decide +kernel

/-! The pointwise-kernel engine's own data (`kernelDim_kerIff`):
two bases of unequal width carrying one cross datum, so the two
kernel reads agree at every coefficient family outright, and the
count binder's refusal at the two bases whose counts part. -/

/-- The stacked family read against the width-two basis. -/
private def kerR : Mat := [[BPair.ofNat 1, BPair.ofNat 1]]

/-- The width-two basis: the two keys' own family. -/
private def kerL : Mat :=
  [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.ofNat 1]]

/-- The stacked family read against the width-one basis. -/
private def kerR' : Mat := [[BPair.ofNat 1]]

/-- The width-one basis at two members, each the one key's own: its
cross datum against `kerR'` is `kerL`'s against `kerR`, entry for
entry, at the same coefficient count. -/
private def kerL' : Mat := [[BPair.ofNat 1], [BPair.ofNat 1]]

example : crossM kerR kerL = crossM kerR' kerL' := by decide +kernel

/-- The engine applied whole: the two cross data one matrix, so
every coefficient family reads the two kernels together, and the
two counts read one dimension. -/
example : kernelDim kerL.length (crossM kerR kerL)
    = kernelDim kerL'.length (crossM kerR' kerL') :=
  kernelDim_kerIff kerR kerL kerR' kerL' rfl (fun _ _ => Iff.rfl)

example : kernelDim kerL.length (crossM kerR kerL) = 1 := by decide +kernel
example : kernelDim kerL'.length (crossM kerR' kerL') = 1 := by decide +kernel

/-- Refusal isolating `kernelDim_kerIff`'s count binder: at the
vacant stacked family both cross data are vacant, so the kernel
reads agree at every coefficient family, while the one-member basis
and the vacant basis part the counts at one against nought. -/
example : (∀ x : List BPair, x.length = ([[]] : Mat).length →
      (poly.unitTail (matVec (crossM [] [[]]) x)
        ↔ poly.unitTail (matVec (crossM [] ([] : Mat)) x)))
    ∧ ¬ ([[]] : Mat).length = ([] : Mat).length :=
  ⟨fun _ _ => Iff.rfl, by decide +kernel⟩

example : ¬ (kernelDim ([[]] : Mat).length (crossM [] [[]])
    = kernelDim ([] : Mat).length (crossM [] ([] : Mat))) := by
  decide +kernel

/-! The descent at polynomial entries: the walk's value pins at
stated lists against the first-row fold, the theorem route beside
the kernel's own reads, the refusal isolating the read, and the
iterated carrier's pin one level up.  The two-key list reads the
constant determinant `2·3 − 1·1`, the chord-entried list the
symbol `z² − 1`, and the iterated list its outer mirror. -/

example : poly.oneValue
    (elim.pdetD [[[⟨3, 1⟩], [⟨2, 1⟩]], [[⟨2, 1⟩], [⟨4, 1⟩]]])
    [⟨6, 1⟩] := by decide +kernel

example : ¬ poly.oneValue
    (elim.pdetD [[[⟨3, 1⟩], [⟨2, 1⟩]], [[⟨2, 1⟩], [⟨4, 1⟩]]])
    [⟨5, 1⟩] := by decide +kernel

example : poly.oneValue
    (elim.pdetD [[[⟨1, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩]],
      [[⟨2, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]]])
    [⟨1, 2⟩, ⟨1, 1⟩, ⟨2, 1⟩] := by decide +kernel

example : poly.oneValue
    (elim.pdetD [[[⟨3, 1⟩], [⟨2, 1⟩]], [[⟨2, 1⟩], [⟨4, 1⟩]]])
    (elim.minorO poly.polyOps poly.pnorm id
      [[[⟨3, 1⟩], [⟨2, 1⟩]], [[⟨2, 1⟩], [⟨4, 1⟩]]]) :=
  elim.pdetD_eq _ (by decide +kernel)

example : poly.ppOneValue
    (elim.ppdetD [[[[], [⟨2, 1⟩]], [[⟨2, 1⟩]]],
      [[[⟨2, 1⟩]], [[], [⟨2, 1⟩]]]])
    [[⟨1, 2⟩], [], [⟨2, 1⟩]] := by decide +kernel

example : poly.ppOneValue
    (elim.ppdetD [[[[], [⟨2, 1⟩]], [[⟨2, 1⟩]]],
      [[[⟨2, 1⟩]], [[], [⟨2, 1⟩]]]])
    (elim.minorO (poly.polyO poly.polyOps) poly.pnormP id
      [[[[], [⟨2, 1⟩]], [[⟨2, 1⟩]]],
        [[[⟨2, 1⟩]], [[], [⟨2, 1⟩]]]]) :=
  elim.ppdetD_eq _ (by decide +kernel)

/-! The descent's division tier at its own strata: a genuine
second pivot at a degree-one divisor, an off-one pivot top, the
pivot-free column's stall, a scan at trailing unit coefficients,
and the ragged refusal pair isolating the square binder. -/

example : poly.oneValue
    (elim.pdetD [[[⟨1, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩], []],
      [[⟨2, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩]],
      [[], [⟨2, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]]])
    [⟨1, 1⟩, ⟨1, 3⟩, ⟨1, 1⟩, ⟨2, 1⟩] := by decide +kernel

example : poly.oneValue
    (elim.pdetD [[[⟨1, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩], []],
      [[⟨2, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩]],
      [[], [⟨2, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]]])
    (elim.minorO poly.polyOps poly.pnorm id
      [[[⟨1, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩], []],
        [[⟨2, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩]],
        [[], [⟨2, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]]]) :=
  elim.pdetD_eq _ (by decide +kernel)

example : poly.oneValue
    (elim.pdetD [[[⟨1, 1⟩, ⟨3, 1⟩], [⟨2, 1⟩], []],
      [[⟨2, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩]],
      [[], [⟨2, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]]])
    [⟨1, 1⟩, ⟨1, 4⟩, ⟨1, 1⟩, ⟨3, 1⟩] := by decide +kernel

example : poly.oneValue
    (elim.pdetD [[[], [⟨2, 1⟩]], [[], [⟨2, 1⟩]]]) [] := by decide +kernel

example : poly.oneValue
    (elim.pdetD [[[⟨3, 1⟩, ⟨1, 1⟩], [⟨2, 1⟩]],
      [[⟨2, 1⟩], [⟨4, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]])
    [⟨6, 1⟩] := by decide +kernel

private def raggedP : List (List poly.Poly) :=
  [[[⟨1, 1⟩, ⟨2, 1⟩]], [[⟨2, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]]]

example : (¬ elim.rowsLen raggedP.length raggedP)
    ∧ ¬ poly.oneValue (elim.pdetD raggedP)
      (elim.minorO poly.polyOps poly.pnorm id raggedP) := by decide +kernel

example : ¬ poly.ppOneValue
    (elim.ppdetD [[[[], [⟨2, 1⟩]], [[⟨2, 1⟩]]],
      [[[⟨2, 1⟩]], [[], [⟨2, 1⟩]]]])
    [[⟨1, 2⟩], [], [⟨3, 1⟩]] := by decide +kernel

/-! The dot against the indicator reads the key's own entry, the
off-key read refusing. -/

example : (elim.dotP [⟨3,1⟩, ⟨1,4⟩, ⟨5,2⟩] (elim.idRow 3 1)).oneValue
    (ground.getAt BPair.unit [⟨3,1⟩, ⟨1,4⟩, ⟨5,2⟩] 1) := by decide +kernel
example : ¬ (elim.dotP [⟨3,1⟩, ⟨1,4⟩, ⟨5,2⟩] (elim.idRow 3 1)).oneValue
    (ground.getAt BPair.unit [⟨3,1⟩, ⟨1,4⟩, ⟨5,2⟩] 0) := by decide +kernel

/-! The combination's coefficient laws at stated data: the
additivity at one coefficient count, refused at unequal counts; the
scale crossing the combination; the swap crossing the combination
and the memberwise sum; and the four summands' middle exchange. -/

private def eL1 : elim.Mat :=
  [[ground.BPair.ofNat 1], [ground.BPair.ofNat 1]]
private def eC1 : List ground.BPair :=
  [ground.BPair.ofNat 1, ground.BPair.ofNat 2]
private def eC2 : List ground.BPair :=
  [ground.BPair.ofNat 3, ground.BPair.ofNat 1]

example : poly.oneValue (elim.combo 1 (elim.vecAdd eC1 eC2) eL1)
    (elim.vecAdd (elim.combo 1 eC1 eL1) (elim.combo 1 eC2 eL1)) :=
  elim.combo_vecAdd 1 eC1 eC2 eL1 rfl
example : poly.oneValue (elim.combo 1 (elim.vecAdd eC1 eC2) eL1)
    (elim.vecAdd (elim.combo 1 eC1 eL1) (elim.combo 1 eC2 eL1)) := by
  decide +kernel
example : ¬ poly.oneValue
    (elim.combo 1 (elim.vecAdd [ground.BPair.ofNat 1] eC1) eL1)
    (elim.vecAdd (elim.combo 1 [ground.BPair.ofNat 1] eL1)
      (elim.combo 1 eC1 eL1)) := by decide +kernel
example : poly.oneValue
    (elim.vecScale (ground.BPair.ofNat 2) (elim.combo 1 eC1 eL1))
    (elim.combo 1 (elim.vecScale (ground.BPair.ofNat 2) eC1) eL1) :=
  elim.vecScale_combo _ 1 eC1 eL1
example : poly.oneValue
    (elim.vecScale (ground.BPair.ofNat 2) (elim.combo 1 eC1 eL1))
    (elim.combo 1 (elim.vecScale (ground.BPair.ofNat 2) eC1) eL1) := by
  decide +kernel
example : elim.combo 1 (eC1.map ground.BPair.swap) eL1
    = (elim.combo 1 eC1 eL1).map ground.BPair.swap := rfl
example : (elim.vecAdd eC1 eC2).map ground.BPair.swap
    = elim.vecAdd (eC1.map ground.BPair.swap)
      (eC2.map ground.BPair.swap) := rfl
example : elim.vecAdd (elim.vecAdd [ground.BPair.ofNat 1]
      [ground.BPair.ofNat 2])
    (elim.vecAdd [ground.BPair.ofNat 3] [ground.BPair.ofNat 4])
    = elim.vecAdd (elim.vecAdd [ground.BPair.ofNat 1]
      [ground.BPair.ofNat 3])
    (elim.vecAdd [ground.BPair.ofNat 2] [ground.BPair.ofNat 4]) := rfl

/-! The determinant kit: the scaled list, the block-triangular list
and the slab reduction, with the reduction's order binder refused
at a vacant leading slab. -/

private def dkM : elim.Mat :=
  [[ground.BPair.ofNat 1, ground.BPair.ofNat 2],
   [ground.BPair.ofNat 3, ground.BPair.ofNat 4]]

example : (elim.detL (dkM.map (elim.vecScale (ground.BPair.ofNat 2)))).oneValue
    (ground.bpow (ground.BPair.ofNat 2) 2 * elim.detL dkM) := by decide +kernel
example : (elim.detL (dkM.map (elim.vecScale (ground.BPair.ofNat 2)))).oneValue
    ⟨1, 9⟩ := by decide +kernel

private def dkP : elim.Mat :=
  [[ground.BPair.ofNat 2, ground.BPair.unit],
   [ground.BPair.ofNat 1, ground.BPair.ofNat 3]]
private def dkB : elim.Mat := [[ground.BPair.ofNat 1], [ground.BPair.ofNat 2]]
private def dkR : elim.Mat := [[ground.BPair.ofNat 5]]

example : (elim.detL (elim.rowJoin dkP dkB
    ++ elim.rowJoin (List.replicate 1 (List.replicate 2 ground.BPair.unit))
      dkR)).oneValue (elim.detL dkP * elim.detL dkR) := by decide +kernel
example : (elim.detL (elim.rowJoin dkP dkB
    ++ elim.rowJoin (List.replicate 1 (List.replicate 2 ground.BPair.unit))
      dkR)).oneValue (ground.BPair.ofNat 30) := by decide +kernel

private def dkO : elim.Mat := [[ground.BPair.ofNat 1]]
private def dkT : elim.Mat := [[ground.BPair.ofNat 2]]

example : (ground.bpow (ground.BPair.ofNat 2) 1
    * elim.detL (elim.rowJoin dkT dkO ++ elim.rowJoin dkO dkO)).oneValue
    (elim.detL (elim.rowJoin dkT dkO
      ++ elim.rowJoin
        (elim.matAdd (dkO.map (elim.vecScale (ground.BPair.ofNat 2)))
          (elim.matSwap (elim.matMul (elim.transposeM dkO) dkT)))
        (elim.matAdd (dkO.map (elim.vecScale (ground.BPair.ofNat 2)))
          (elim.matSwap (elim.matMul (elim.transposeM dkO) dkO))))) := by
  decide +kernel
example : (ground.bpow (ground.BPair.ofNat 2) 1
    * elim.detL (elim.rowJoin dkT dkO ++ elim.rowJoin dkO dkO)).oneValue
    (ground.BPair.ofNat 2) := by decide +kernel
example : ¬ (ground.bpow (ground.BPair.ofNat 2) 1
    * elim.detL (elim.rowJoin [] [] ++ elim.rowJoin [[]] dkT)).oneValue
    (elim.detL (elim.rowJoin [] []
      ++ elim.rowJoin
        (elim.matAdd
          (([[]] : elim.Mat).map (elim.vecScale (ground.BPair.ofNat 2)))
          (elim.matSwap (elim.matMul (elim.transposeM []) [])))
        (elim.matAdd (dkT.map (elim.vecScale (ground.BPair.ofNat 2)))
          (elim.matSwap (elim.matMul (elim.transposeM []) []))))) := by
  decide +kernel

/-! The kernel-equivalence binder's isolating refusal: two cross
data over one family at the lengths tied by `rfl`, the kernel
reads parting at one coefficient family, the counts with them. -/

private def kR : elim.Mat := [[BPair.ofNat 1, BPair.ofNat 1]]
private def kL : elim.Mat :=
  [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.ofNat 1]]
private def kR2 : elim.Mat :=
  [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.ofNat 1]]

example : ¬ (∀ x : List BPair, x.length = kL.length →
    (poly.unitTail (elim.matVec (elim.crossM kR kL) x)
      ↔ poly.unitTail (elim.matVec (elim.crossM kR2 kL) x))) := by
  intro h
  exact absurd ((h [BPair.ofNat 1, (BPair.ofNat 1).swap] rfl).mp
    (by decide +kernel)) (by decide +kernel)
example : ¬ (elim.kernelDim kL.length (elim.crossM kR kL)
    = elim.kernelDim kL.length (elim.crossM kR2 kL)) := by decide +kernel

/-! The pivot's places: the selection at stated row and column key
lists read against its literal, the join's assembled block datum,
and the conjugation at the places' permutation matrix — decided and
through the theorem at the places `[2, 0]` of a symmetric order-3
datum. -/

private def pS3 : elim.Mat :=
  [[BPair.ofNat 1, BPair.ofNat 2, BPair.ofNat 3],
   [BPair.ofNat 2, BPair.ofNat 4, BPair.ofNat 5],
   [BPair.ofNat 3, BPair.ofNat 5, BPair.ofNat 6]]

example : elim.selM [2, 0] [2, 0] pS3
    = [[BPair.ofNat 6, BPair.ofNat 3],
       [BPair.ofNat 3, BPair.ofNat 1]] := by decide +kernel

example : elim.selM ([1] ++ [2, 0]) ([1] ++ [2, 0]) pS3
    = List.zipWith (· ++ ·) (elim.selM [1] [1] pS3)
        (elim.selM [1] [2, 0] pS3)
      ++ List.zipWith (· ++ ·) (elim.selM [2, 0] [1] pS3)
        (elim.selM [2, 0] [2, 0] pS3) := by decide +kernel
example : elim.selM ([1] ++ [2, 0]) ([1] ++ [2, 0]) pS3
    = List.zipWith (· ++ ·) (elim.selM [1] [1] pS3)
        (elim.selM [1] [2, 0] pS3)
      ++ List.zipWith (· ++ ·) (elim.selM [2, 0] [1] pS3)
        (elim.selM [2, 0] [2, 0] pS3) := elim.selM_append [1] [2, 0] pS3

example : elim.matOneValue
    (elim.matMul (elim.permM 3 [2, 0])
      (elim.matMul pS3 (elim.transposeM (elim.permM 3 [2, 0]))))
    (elim.selM [2, 0] [2, 0] pS3) := by decide +kernel
example : elim.matOneValue
    (elim.matMul (elim.permM 3 [2, 0])
      (elim.matMul pS3 (elim.transposeM (elim.permM 3 [2, 0]))))
    (elim.selM [2, 0] [2, 0] pS3) :=
  elim.permM_conj 3 [2, 0] pS3 (by decide +kernel) (by decide +kernel)

/-! The transpose identity at the places' permutation matrix: a
distinct full key list against its transpose reads the identity on
both sides, decided and through the theorem; the short list refuses
the length binder and the repeated place the distinctness, each
with every further binder decided true beside it.  The covering
binder of the transposed order is implied at a distinct full list
inside the order, its refusal off the theorem's reach: the frame's
own read. -/

example : elim.matOneValue
    (elim.matMul (elim.permM 3 [2, 0, 1])
      (elim.transposeM (elim.permM 3 [2, 0, 1])))
    (elim.permM 3 (List.range 3)) := by decide +kernel

example : elim.matOneValue
    (elim.matMul (elim.permM 3 [2, 0, 1])
      (elim.transposeM (elim.permM 3 [2, 0, 1])))
    (elim.permM 3 (List.range 3)) :=
  elim.permM_orthL 3 [2, 0, 1] (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : elim.matOneValue
    (elim.matMul (elim.transposeM (elim.permM 3 [2, 0, 1]))
      (elim.permM 3 [2, 0, 1]))
    (elim.permM 3 (List.range 3)) := by decide +kernel

example : elim.matOneValue
    (elim.matMul (elim.transposeM (elim.permM 3 [2, 0, 1]))
      (elim.permM 3 [2, 0, 1]))
    (elim.permM 3 (List.range 3)) :=
  elim.permM_orthR 3 [2, 0, 1] (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (fun j hj => ground.bltLt
      (ground.all_range_read
        (f := fun j => Nat.blt 0 (ground.countOf j [2, 0, 1]))
        3 (by decide +kernel) j hj))

example : ground.distinctList ([0] : List Nat)
    ∧ (([0] : List Nat).all (fun i => Nat.blt i 2)) = true
    ∧ ¬ elim.matOneValue
      (elim.matMul (elim.permM 2 [0])
        (elim.transposeM (elim.permM 2 [0])))
      (elim.permM 2 (List.range 2)) := by decide +kernel

example : ([0, 0] : List Nat).length = 2
    ∧ (([0, 0] : List Nat).all (fun i => Nat.blt i 2)) = true
    ∧ ¬ elim.matOneValue
      (elim.matMul (elim.permM 2 [0, 0])
        (elim.transposeM (elim.permM 2 [0, 0])))
      (elim.permM 2 (List.range 2)) := by decide +kernel


example : elim.matOneValue
    (elim.transposeM (elim.selM [2, 0] [1] pS3)) (elim.selM [1] [2, 0] pS3) := by
  decide +kernel
example : elim.matOneValue
    (elim.transposeM (elim.selM [2, 0] [1] pS3)) (elim.selM [1] [2, 0] pS3) :=
  elim.transposeM_selM [2, 0] [1] pS3 3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The occupied-row binder's isolation: at the order-1 symmetric
datum every other hypothesis reads true and the exchange still
parts, the vacant row key list leaving the transpose no column
count to read. -/

example : sqAt [[BPair.unit]] 1 := by decide +kernel
example : matOneValue (transposeM [[BPair.unit]]) [[BPair.unit]] := by
  decide +kernel
example : (([] : List Nat).all (fun i => Nat.blt i 1)) = true := by
  decide +kernel
example : (([0] : List Nat).all (fun j => Nat.blt j 1)) = true := by
  decide +kernel
example : ¬ matOneValue (transposeM (selM [] [0] [[BPair.unit]]))
    (selM [0] [] [[BPair.unit]]) := by decide +kernel

/-! The determinant product tier at committed data: two square
lists' product reads its determinant at the factors' own
(`detL_mul`) at `[[1, 2], [-1, 3]]` against `[[2, 1], [1, 1]]`;
the stated diagonal's own running product (`detL_diag`) at
`2, -1, 3`; the polynomial diagonal's minor (`pminor_diag`) at
`diag(x - 1, x + 2)`; the embedded scalar list's minor
(`pminor_embed`) at the first square list, the constant
polynomial at its determinant; the polynomial product's minor
(`pminor_mul`) at `[[x, 1], [0, x]]` against `[[x + 1, 0], [1, 1]]`,
the product's minor `x²(x + 1)`; and the entrywise congruence
(`minorP_congr`) at one entry respelled by a trailing sum's unit —
each decided and run through its theorem. -/

private def aFix : elim.Mat := [[⟨2, 1⟩, ⟨3, 1⟩], [⟨1, 2⟩, ⟨4, 1⟩]]
private def bFix : elim.Mat := [[⟨3, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]]

private theorem saFix : elim.sqAt aFix 2 := by decide +kernel
private theorem sbFix : elim.sqAt bFix 2 := by decide +kernel

example : (elim.detL (elim.matMul aFix bFix)).oneValue
    (elim.detL aFix * elim.detL bFix) := by decide +kernel

example : (elim.detL (elim.matMul aFix bFix)).oneValue
    (elim.detL aFix * elim.detL bFix) :=
  elim.detL_mul aFix bFix 2 saFix sbFix

private def dFix : List BPair := [⟨3, 1⟩, ⟨1, 2⟩, ⟨4, 1⟩]

example : (elim.detL (elim.diagO ground.bpairOps dFix)).oneValue
    (dFix.foldl (fun a d => a * d) (BPair.ofNat 1)) := by decide +kernel

example : (elim.detL (elim.diagO ground.bpairOps dFix)).oneValue
    (dFix.foldl (fun a d => a * d) (BPair.ofNat 1)) :=
  elim.detL_diag dFix

private def pdFix : List poly.Poly := [[⟨1, 2⟩, ⟨2, 1⟩], [⟨3, 1⟩, ⟨2, 1⟩]]

example : poly.oneValue
    (elim.minorO poly.polyOps poly.pnorm id (elim.diagO poly.polyOps pdFix))
    (poly.prodFold pdFix) := by decide +kernel

example : poly.oneValue
    (elim.minorO poly.polyOps poly.pnorm id (elim.diagO poly.polyOps pdFix))
    (poly.prodFold pdFix) :=
  elim.pminor_diag pdFix

example : poly.oneValue
    (elim.minorO poly.polyOps poly.pnorm id (elim.embedP aFix))
    [elim.detL aFix] := by decide +kernel

example : poly.oneValue
    (elim.minorO poly.polyOps poly.pnorm id (elim.embedP aFix))
    [elim.detL aFix] :=
  elim.pminor_embed aFix 2 saFix

private def pmA : List (List poly.Poly) :=
  [[[BPair.unit, ⟨2, 1⟩], [⟨2, 1⟩]], [[BPair.unit], [BPair.unit, ⟨2, 1⟩]]]
private def pmB : List (List poly.Poly) :=
  [[[⟨2, 1⟩, ⟨2, 1⟩], [BPair.unit]], [[⟨2, 1⟩], [⟨2, 1⟩]]]

private theorem pmAl : pmA.length = 2 := by decide +kernel
private theorem pmAr : elim.rowsLen 2 pmA := by decide +kernel

example : poly.oneValue
    (elim.minorO poly.polyOps poly.pnorm id (elim.matMulO poly.polyOps pmA pmB))
    (poly.mul (elim.minorO poly.polyOps poly.pnorm id pmA)
      (elim.minorO poly.polyOps poly.pnorm id pmB)) := by decide +kernel

example : poly.oneValue
    (elim.minorO poly.polyOps poly.pnorm id (elim.matMulO poly.polyOps pmA pmB))
    (poly.mul (elim.minorO poly.polyOps poly.pnorm id pmA)
      (elim.minorO poly.polyOps poly.pnorm id pmB)) :=
  elim.pminor_mul pmA pmB 2 pmAl pmAr
    (by decide +kernel) (by decide +kernel)

private def pmPad : List (List poly.Poly) :=
  [[[BPair.unit, ⟨2, 1⟩, BPair.unit], [⟨2, 1⟩]],
   [[BPair.unit], [BPair.unit, ⟨2, 1⟩]]]

example : poly.oneValue (elim.minorO poly.polyOps poly.pnorm id pmA)
    (elim.minorO poly.polyOps poly.pnorm id pmPad) := by decide +kernel

example : poly.oneValue (elim.minorO poly.polyOps poly.pnorm id pmA)
    (elim.minorO poly.polyOps poly.pnorm id pmPad) := by
  have hent : ((List.range 2).all (fun a => (List.range 2).all
      (fun b => decide (poly.oneValue
        (ground.getAt ([] : poly.Poly) (ground.getAt [] pmA a) b)
        (ground.getAt ([] : poly.Poly) (ground.getAt [] pmPad a) b))))) = true := by
    decide +kernel
  exact elim.minorP_congr pmA pmPad 2 pmAl (by decide +kernel)
    pmAr (by decide +kernel)
    (fun a ha b hb => of_decide_eq_true
      (ground.all_range_read 2 (ground.all_range_read 2 hent a ha) b hb))


/-! The frame refusals.  The shared order is the product tier's own
binder: the order-one list `[[2]]` against the order-two
`[[2, 1], [1, 1]]` reads determinant `4` at the product where the
factors' own read `2`, each shape read true at its own order and
false at the other's, so no order carries both; the polynomial twin
reads the product's minor `2x` against the factors' own `2x²`, the
two lengths fixing distinct orders.  The embedded list's square
binder refuses at the two-by-three rectangle, whose minor reads the
sum's unit against the determinant's `3`, the length read fixing
the only order at which the shape read could hold and the row read
refusing there.  The entrywise binder refuses at one doubled entry,
the minors reading `x²` against `2x²` with every frame read true
beside it.  The row read is its own isolated binder at the right
factor: a short right row at a matched length drops a column of the
product, the scalar and polynomial refusals below, while the left
factor's row read is refusal-free, a short left row truncating the
fold exactly as the unit padding reads it. -/

private def aOne : elim.Mat := [[⟨3, 1⟩]]

example : elim.sqAt aOne 1 := by decide +kernel
example : ¬ elim.sqAt aOne 2 := by decide +kernel
example : ¬ elim.sqAt bFix 1 := by decide +kernel
example : ¬ (elim.detL (elim.matMul aOne bFix)).oneValue
    (elim.detL aOne * elim.detL bFix) := by decide +kernel

private def pmOne : List (List poly.Poly) := [[[⟨3, 1⟩]]]

example : pmOne.length = 1 := by decide +kernel
example : elim.rowsLen 1 pmOne := by decide +kernel
example : ¬ poly.oneValue
    (elim.minorO poly.polyOps poly.pnorm id (elim.matMulO poly.polyOps pmOne pmA))
    (poly.mul (elim.minorO poly.polyOps poly.pnorm id pmOne)
      (elim.minorO poly.polyOps poly.pnorm id pmA)) := by decide +kernel

private def mRect : elim.Mat :=
  [[⟨2, 1⟩, ⟨3, 1⟩, ⟨4, 1⟩], [⟨1, 2⟩, ⟨2, 1⟩, ⟨3, 1⟩]]

example : mRect.length = 2 := by decide +kernel
example : ¬ elim.sqAt mRect 2 := by decide +kernel
example : ¬ elim.sqAt mRect 3 := by decide +kernel
example : ¬ poly.oneValue
    (elim.minorO poly.polyOps poly.pnorm id (elim.embedP mRect))
    [elim.detL mRect] := by decide +kernel

private def pmOff : List (List poly.Poly) :=
  [[[BPair.unit, ⟨2, 1⟩], [⟨2, 1⟩]], [[BPair.unit], [BPair.unit, ⟨3, 1⟩]]]

example : pmOff.length = 2 := by decide +kernel
example : elim.rowsLen 2 pmOff := by decide +kernel
example : ¬ poly.oneValue
    (ground.getAt ([] : poly.Poly) (ground.getAt [] pmA 1) 1)
    (ground.getAt ([] : poly.Poly) (ground.getAt [] pmOff 1) 1) := by
  decide +kernel
example : ¬ poly.oneValue (elim.minorO poly.polyOps poly.pnorm id pmA)
    (elim.minorO poly.polyOps poly.pnorm id pmOff) := by decide +kernel

private def rShort : elim.Mat := [[⟨2, 1⟩], [⟨1, 2⟩, ⟨4, 1⟩]]

example : rShort.length = 2 := by decide +kernel
example : ¬ elim.rowsLen 2 rShort := by decide +kernel
example : ¬ (elim.detL (elim.matMul bFix rShort)).oneValue
    (elim.detL bFix * elim.detL rShort) := by decide +kernel

private def pmRShort : List (List poly.Poly) :=
  [[[⟨2, 1⟩, ⟨2, 1⟩]], [[⟨2, 1⟩], [⟨2, 1⟩]]]

example : pmRShort.length = 2 := by decide +kernel
example : ¬ elim.rowsLen 2 pmRShort := by decide +kernel
example : ¬ poly.oneValue
    (elim.minorO poly.polyOps poly.pnorm id
      (elim.matMulO poly.polyOps pmA pmRShort))
    (poly.mul (elim.minorO poly.polyOps poly.pnorm id pmA)
      (elim.minorO poly.polyOps poly.pnorm id pmRShort)) := by decide +kernel

private def mRag : List (List poly.Poly) :=
  [[[⟨2, 1⟩], [⟨3, 1⟩], [⟨5, 1⟩]], [[⟨1, 2⟩], [⟨4, 1⟩]]]
private def mSq : List (List poly.Poly) :=
  [[[⟨2, 1⟩], [⟨3, 1⟩]], [[⟨1, 2⟩], [⟨4, 1⟩]]]

example : mSq.length = 2 := by decide +kernel
example : mRag.length = 2 := by decide +kernel
example : elim.rowsLen 2 mSq := by decide +kernel
example : ¬ elim.rowsLen 2 mRag := by decide +kernel
example : ((List.range 2).all (fun a => (List.range 2).all (fun b =>
    decide (poly.oneValue
      (ground.getAt ([] : poly.Poly) (ground.getAt [] mSq a) b)
      (ground.getAt ([] : poly.Poly) (ground.getAt [] mRag a) b))))) = true := by
  decide +kernel
example : ¬ poly.oneValue (elim.minorO poly.polyOps poly.pnorm id mSq)
    (elim.minorO poly.polyOps poly.pnorm id mRag) := by decide +kernel
