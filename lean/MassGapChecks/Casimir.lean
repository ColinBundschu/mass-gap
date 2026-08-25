import MassGap.Casimir
import MassGapChecks.Strings
/-!
The check module for `lem:casimir`'s trace tier: the fold's own
values at a committed orthonormal pair of coordinates — the two
self-pairing products, the identity operator's fold reading the
count and a diagonal operator's reading its entries' sum — with
the additivity read decided beside its theorem instance, and the
count read at a scalar operator.  The one-value theorem runs at
two genuinely different orthogonal spanning lists of one plane
(the coordinates against the diagonal pair), every hypothesis one
`decide` and the conclusion decided beside the theorem's own
instance, with the isolating refusals at the broken
perpendicular read and the broken spanning read.  The first list's
off-unit self-pairing binder — the theorem's only one — admits no
isolating refusal: a unit
self-pairing is a null member (the pairing's definiteness), which
sends the list's whole product and its trace fold to the sum's
unit together, so both sides read the unit whatever the operator:
the exhibit below decides that coupling rather than a refusal.

`con:units`' table join opens the closing sections: the uniform
read decided at a three-letter content with one live delta and one
refused, its theorem instance beside it, and the both-refused
instance the swap read's own shape — the battery sits here rather
than at the theorem's owner because its content hypotheses are
`blockcount.out_gen`'s, which Units' own check module cannot reach.

The `C` family's own battery closes the module: the matrix decided
against its hand-computed value at three contents (the composition
order the pin — a term composed the other way round leaves the
content's own enumeration), the shape read decided beside its
theorem instance, the block scalar decided at three contents, and
the top read decided beside its theorem instance at the one-row
shapes and at the shape whose second row is vacant (the pair
fold's unoccupied letter, the exchange's degenerate side).  One
isolating refusal: the diagonal squares alone miss the top read,
the pair fold load-bearing.  The descent restriction admits no
isolating refusal — a content off the row list's weak descent has
no exhibit, so the vector at which the read is tested is not that
content's own top and the refusal breaks the vector's topness and
the descent together; the pair below is that coupling's exhibit,
the non-descending content refusing and its descending mirror
deciding true at the same vector.  The fold's own collection is
pinned beside them: the moved read holds of the whole matrix at a
raising between two contents and fails at the single letter pair
whose composite the fold collects, so the delta families cancel
across the fold and never term by term.  The moved reads' own
battery closes the module: the commutation decided at the walk's
contents with every vacant-letter branch reached, the theorem
discharged at three instances, the range binders' refusal
committed at a unit letter inside the content at the fold's
range, and the three unrefused couplings decided as exhibits.
`thm:weylchar`'s per-pair string traces close the module: at the
two-letter block's one string the two ordered words' folds over
the collected members are decided against their own theorem
instances at the block's middle content, the two weights' sum the
display's coefficient, and a content the span never carries reads
the vacant fold at the empty product.  The trace recursion's own
discharge closes the module: the display is decided at the
one-letter shape and at the two-letter shape whose span carries a
genuine lowering, with the theorem's instances beside them, and
the recursion and symmetry reads decided at three letters at the
low-degree shapes whose key lists the kernel affords.
-/
set_option maxRecDepth 8192

open ground places blockcount casimir

/-! The committed list: the two coordinates at the balance
carrier's one, an orthonormal pair — the perpendicular reads at
the sum's unit with the self-pairings off it. -/

example : elim.rowsLen 2 [[BPair.ofNat 1, BPair.unit],
    [BPair.unit, BPair.ofNat 1]] := by decide +kernel

example : ∀ p < 2, ∀ q < 2, ¬ p = q →
    (elim.dotP
      (getAt [] [[BPair.ofNat 1, BPair.unit],
        [BPair.unit, BPair.ofNat 1]] p)
      (getAt [] [[BPair.ofNat 1, BPair.unit],
        [BPair.unit, BPair.ofNat 1]] q)).oneValue BPair.unit := by
  decide +kernel

example : ∀ p < 2, ¬ (elim.dotP
    (getAt [] [[BPair.ofNat 1, BPair.unit],
      [BPair.unit, BPair.ofNat 1]] p)
    (getAt [] [[BPair.ofNat 1, BPair.unit],
      [BPair.unit, BPair.ofNat 1]] p)).oneValue BPair.unit := by
  decide +kernel

/-! The two self-pairing products at that list, and the folds: the
identity operator reads the count, a diagonal operator its
entries' sum. -/

example : (prodAll [[BPair.ofNat 1, BPair.unit],
    [BPair.unit, BPair.ofNat 1]]).oneValue (BPair.ofNat 1) := by
  decide +kernel

example : (prodOff [[BPair.ofNat 1, BPair.unit],
    [BPair.unit, BPair.ofNat 1]] 0).oneValue (BPair.ofNat 1) := by
  decide +kernel

example : (trFold [[BPair.ofNat 1, BPair.unit],
      [BPair.unit, BPair.ofNat 1]]
    [[BPair.ofNat 1, BPair.unit],
      [BPair.unit, BPair.ofNat 1]]).oneValue (BPair.ofNat 2) := by
  decide +kernel

example : (trFold [[BPair.ofNat 2, BPair.unit],
      [BPair.unit, BPair.ofNat 3]]
    [[BPair.ofNat 1, BPair.unit],
      [BPair.unit, BPair.ofNat 1]]).oneValue (BPair.ofNat 5) := by
  decide +kernel

/-! The additivity read: the decided value beside the theorem's
own instance at the same data. -/

example : (trFold (elim.matAdd
      [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.ofNat 1]]
      [[BPair.ofNat 2, BPair.unit], [BPair.unit, BPair.ofNat 3]])
    [[BPair.ofNat 1, BPair.unit],
      [BPair.unit, BPair.ofNat 1]]).oneValue
    (BPair.ofNat 7) := by decide +kernel

example : (trFold (elim.matAdd
      [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.ofNat 1]]
      [[BPair.ofNat 2, BPair.unit], [BPair.unit, BPair.ofNat 3]])
    [[BPair.ofNat 1, BPair.unit],
      [BPair.unit, BPair.ofNat 1]]).oneValue
    (trFold [[BPair.ofNat 1, BPair.unit],
        [BPair.unit, BPair.ofNat 1]]
      [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.ofNat 1]]
      + trFold [[BPair.ofNat 2, BPair.unit],
          [BPair.unit, BPair.ofNat 3]]
        [[BPair.ofNat 1, BPair.unit],
          [BPair.unit, BPair.ofNat 1]]) :=
  trFold_add 2
    [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.ofNat 1]]
    [[BPair.ofNat 2, BPair.unit], [BPair.unit, BPair.ofNat 3]]
    [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.ofNat 1]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The fold at the vacant list and at a one-member list: the
seeds' own reads. -/

example : (trFold [] ([] : elim.Mat)).oneValue BPair.unit := by
  decide +kernel

example : (prodAll ([] : elim.Mat)).oneValue (BPair.ofNat 1) := by
  decide +kernel

example : (trFold [[BPair.ofNat 3]] [[BPair.ofNat 1]]).oneValue
    (BPair.ofNat 3) := by decide +kernel

/-! The product kit's reads at the committed list: the withdrawn
key's factor rejoining its guarded product, and the whole product
off the sum's unit. -/

example : (elim.dotP
      (getAt [] [[BPair.ofNat 1, BPair.unit],
        [BPair.unit, BPair.ofNat 1]] 0)
      (getAt [] [[BPair.ofNat 1, BPair.unit],
        [BPair.unit, BPair.ofNat 1]] 0)
    * prodOff [[BPair.ofNat 1, BPair.unit],
        [BPair.unit, BPair.ofNat 1]] 0).oneValue
    (prodAll [[BPair.ofNat 1, BPair.unit],
      [BPair.unit, BPair.ofNat 1]]) := by decide +kernel

example : (elim.dotP
      (getAt [] [[BPair.ofNat 2, BPair.unit],
        [BPair.unit, BPair.ofNat 3]] 1)
      (getAt [] [[BPair.ofNat 2, BPair.unit],
        [BPair.unit, BPair.ofNat 3]] 1)
    * prodOff [[BPair.ofNat 2, BPair.unit],
        [BPair.unit, BPair.ofNat 3]] 1).oneValue
    (prodAll [[BPair.ofNat 2, BPair.unit],
      [BPair.unit, BPair.ofNat 3]]) :=
  prodOff_mul_self [[BPair.ofNat 2, BPair.unit],
    [BPair.unit, BPair.ofNat 3]] 1 (by decide +kernel)

example : ¬ (prodAll [[BPair.ofNat 2, BPair.unit],
    [BPair.unit, BPair.ofNat 3]]).oneValue BPair.unit :=
  prodAll_off [[BPair.ofNat 2, BPair.unit],
    [BPair.unit, BPair.ofNat 3]] (by decide +kernel)

example : (prodAll [[BPair.ofNat 2, BPair.unit],
    [BPair.unit, BPair.ofNat 3]]).oneValue
    (BPair.ofNat 36) := by decide +kernel

/-! The count read: the doubling operator at the committed list,
its fold the count against the scalar at the whole product. -/

example : ∀ j < 2, poly.oneValue
    (elim.matVec [[BPair.ofNat 2, BPair.unit],
        [BPair.unit, BPair.ofNat 2]]
      (getAt [] [[BPair.ofNat 1, BPair.unit],
        [BPair.unit, BPair.ofNat 1]] j))
    (elim.vecScale (BPair.ofNat 2)
      (getAt [] [[BPair.ofNat 1, BPair.unit],
        [BPair.unit, BPair.ofNat 1]] j)) := by decide +kernel

example : (trFold [[BPair.ofNat 2, BPair.unit],
      [BPair.unit, BPair.ofNat 2]]
    [[BPair.ofNat 1, BPair.unit],
      [BPair.unit, BPair.ofNat 1]]).oneValue
    (BPair.ofNat 2 * BPair.ofNat 2
      * prodAll [[BPair.ofNat 1, BPair.unit],
        [BPair.unit, BPair.ofNat 1]]) :=
  trFold_scalar [[BPair.ofNat 2, BPair.unit],
      [BPair.unit, BPair.ofNat 2]]
    [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.ofNat 1]]
    (BPair.ofNat 2) (by decide +kernel)

example : (trFold [[BPair.ofNat 2, BPair.unit],
      [BPair.unit, BPair.ofNat 2]]
    [[BPair.ofNat 1, BPair.unit],
      [BPair.unit, BPair.ofNat 1]]).oneValue
    (BPair.ofNat 4) := by decide +kernel

/-! The one-value theorem at two orthogonal spanning lists: the
coordinates and the diagonal pair, one plane read twice.  The
operator is a stated square; every hypothesis decides, the
conclusion decides, and the theorem's own instance discharges
it. -/

private def coords : elim.Mat :=
  [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.ofNat 1]]

private def diags : elim.Mat :=
  [[BPair.ofNat 1, BPair.ofNat 1],
   [BPair.ofNat 1, (BPair.ofNat 1).swap]]

private def opT : elim.Mat :=
  [[BPair.ofNat 1, BPair.ofNat 2],
   [BPair.ofNat 3, BPair.ofNat 4]]

/-! The second list's own data: perpendicular at the sum's unit,
the self-pairings off it, and the two spanning reads. -/

example : elim.rowsLen 2 diags := by decide +kernel

example : ∀ p < diags.length, ∀ q < diags.length, ¬ p = q →
    (elim.dotP (getAt [] diags p)
      (getAt [] diags q)).oneValue BPair.unit := by decide +kernel

example : ∀ q < diags.length,
    ¬ (elim.dotP (getAt [] diags q)
      (getAt [] diags q)).oneValue BPair.unit := by decide +kernel

example : ∀ p < coords.length,
    elim.spanRel 2 diags (getAt [] coords p) := by decide +kernel

example : ∀ q < diags.length,
    elim.spanRel 2 coords (getAt [] diags q) := by decide +kernel

/-! The two folds and products at that data, then the theorem. -/

example : (prodAll diags).oneValue (BPair.ofNat 4) := by decide +kernel

example : (trFold opT coords).oneValue (BPair.ofNat 5) := by decide +kernel

example : (trFold opT diags).oneValue (BPair.ofNat 20) := by decide +kernel

example : (trFold opT coords * prodAll diags).oneValue
    (trFold opT diags * prodAll coords) := by decide +kernel

example : (trFold opT coords * prodAll diags).oneValue
    (trFold opT diags * prodAll coords) :=
  trace_eq 2 opT coords diags (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The refusals.  The perpendicular read broken: the second list
keeps every other hypothesis and the traces part. -/

private def skewed : elim.Mat :=
  [[BPair.ofNat 1, BPair.ofNat 1], [BPair.ofNat 1, BPair.unit]]

example : ¬ (∀ p < skewed.length, ∀ q < skewed.length, ¬ p = q →
    (elim.dotP (getAt [] skewed p)
      (getAt [] skewed q)).oneValue BPair.unit) := by decide +kernel

example : elim.sqAt opT 2 ∧ elim.rowsLen 2 coords
    ∧ elim.rowsLen 2 skewed
    ∧ (∀ p < coords.length, ∀ q < coords.length, ¬ p = q →
      (elim.dotP (getAt [] coords p)
        (getAt [] coords q)).oneValue BPair.unit)
    ∧ (∀ p < coords.length,
      ¬ (elim.dotP (getAt [] coords p)
        (getAt [] coords p)).oneValue BPair.unit)
    ∧ (∀ p < coords.length,
      elim.spanRel 2 skewed (getAt [] coords p))
    ∧ (∀ q < skewed.length,
      elim.spanRel 2 coords (getAt [] skewed q)) := by decide +kernel

example : ¬ (trFold opT coords * prodAll skewed).oneValue
    (trFold opT skewed * prodAll coords) := by decide +kernel

/-! The spanning read broken: one member spans no plane, and at
the projecting operator the traces part. -/

private def halfSpan : elim.Mat := [[BPair.ofNat 1, BPair.ofNat 1]]

private def opP : elim.Mat :=
  [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.unit]]

example : ¬ (∀ p < coords.length,
    elim.spanRel 2 halfSpan (getAt [] coords p)) := by decide +kernel

example : elim.sqAt opP 2 ∧ elim.rowsLen 2 coords
    ∧ elim.rowsLen 2 halfSpan
    ∧ (∀ p < coords.length, ∀ q < coords.length, ¬ p = q →
      (elim.dotP (getAt [] coords p)
        (getAt [] coords q)).oneValue BPair.unit)
    ∧ (∀ p < halfSpan.length, ∀ q < halfSpan.length, ¬ p = q →
      (elim.dotP (getAt [] halfSpan p)
        (getAt [] halfSpan q)).oneValue BPair.unit)
    ∧ (∀ p < coords.length,
      ¬ (elim.dotP (getAt [] coords p)
        (getAt [] coords p)).oneValue BPair.unit)
    ∧ (∀ q < halfSpan.length,
      elim.spanRel 2 coords (getAt [] halfSpan q)) := by decide +kernel

example : ¬ (trFold opP coords * prodAll halfSpan).oneValue
    (trFold opP halfSpan * prodAll coords) := by decide +kernel

/-! The off-unit self-pairings: a null member breaks that read and
the conclusion holds anyway, both sides at the sum's unit — the
binder's coupling, not a refusal. -/

private def nulled : elim.Mat :=
  [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.unit]]

private def axisOne : elim.Mat := [[BPair.ofNat 1, BPair.unit]]

example : ¬ (∀ p < nulled.length,
    ¬ (elim.dotP (getAt [] nulled p)
      (getAt [] nulled p)).oneValue BPair.unit) := by decide +kernel

example : elim.sqAt opT 2 ∧ elim.rowsLen 2 nulled
    ∧ elim.rowsLen 2 axisOne
    ∧ (∀ p < nulled.length, ∀ q < nulled.length, ¬ p = q →
      (elim.dotP (getAt [] nulled p)
        (getAt [] nulled q)).oneValue BPair.unit)
    ∧ (∀ p < axisOne.length, ∀ q < axisOne.length, ¬ p = q →
      (elim.dotP (getAt [] axisOne p)
        (getAt [] axisOne q)).oneValue BPair.unit)
    ∧ (∀ p < nulled.length,
      elim.spanRel 2 axisOne (getAt [] nulled p))
    ∧ (∀ q < axisOne.length,
      elim.spanRel 2 nulled (getAt [] axisOne q)) := by decide +kernel

example : (prodAll nulled).oneValue BPair.unit := by decide +kernel

example : (trFold opT nulled).oneValue BPair.unit := by decide +kernel

example : (trFold opT nulled * prodAll axisOne).oneValue
    (trFold opT axisOne * prodAll nulled) := by decide +kernel

/-! The `C` family: the matrix at three contents against its hand
computation — the two-letter pair at one place each, the single
letter doubled, and the three-place content whose off-diagonal
entries are the pair terms' own crossings. -/

example : elim.matOneValue (casimirM 2 [1,1])
    [[BPair.ofNat 4, BPair.ofNat 2],
     [BPair.ofNat 2, BPair.ofNat 4]] := by decide +kernel

example : elim.matOneValue (casimirM 2 [2,0])
    [[BPair.ofNat 6]] := by decide +kernel

example : elim.matOneValue (casimirM 2 [2,1])
    [[BPair.ofNat 8, BPair.ofNat 2, BPair.ofNat 2],
     [BPair.ofNat 2, BPair.ofNat 8, BPair.ofNat 2],
     [BPair.ofNat 2, BPair.ofNat 2, BPair.ofNat 8]] := by decide +kernel

/-! The shape read at those contents, decided beside the theorem's
own instance. -/

example : elim.sqAt (casimirM 2 [1,1])
    (monomialsAt [1,1]).length := by decide +kernel

example : elim.sqAt (casimirM 2 [1,1])
    (monomialsAt [1,1]).length := casimirM_sq 2 [1,1]

example : elim.sqAt (casimirM 2 [2,1])
    (monomialsAt [2,1]).length := casimirM_sq 2 [2,1]

/-! The block scalar's values: the squares' fold with the ordered
pairs' balance reads. -/

example : (casScalar [1,1]).oneValue (BPair.ofNat 2) := by decide +kernel

example : (casScalar [2,0]).oneValue (BPair.ofNat 6) := by decide +kernel

example : (casScalar [3,1]).oneValue (BPair.ofNat 12) := by decide +kernel

/-! The top read at the one-row shapes and at the shape with a
vacant second row, decided beside the theorem's own instance. -/

example : poly.oneValue
    (elim.matVec (casimirM [1].length (rowList [1]))
      (exhibit [1]).coords)
    (elim.vecScale (casScalar (rowList [1]))
      (exhibit [1]).coords) := by decide +kernel

example : poly.oneValue
    (elim.matVec (casimirM [1].length (rowList [1]))
      (exhibit [1]).coords)
    (elim.vecScale (casScalar (rowList [1]))
      (exhibit [1]).coords) := by apply casimirM_top

example : poly.oneValue
    (elim.matVec (casimirM [2].length (rowList [2]))
      (exhibit [2]).coords)
    (elim.vecScale (casScalar (rowList [2]))
      (exhibit [2]).coords) := by decide +kernel

example : poly.oneValue
    (elim.matVec (casimirM [2].length (rowList [2]))
      (exhibit [2]).coords)
    (elim.vecScale (casScalar (rowList [2]))
      (exhibit [2]).coords) := by apply casimirM_top

example : poly.oneValue
    (elim.matVec (casimirM [1,0].length (rowList [1,0]))
      (exhibit [1,0]).coords)
    (elim.vecScale (casScalar (rowList [1,0]))
      (exhibit [1,0]).coords) := by decide +kernel

example : poly.oneValue
    (elim.matVec (casimirM [1,0].length (rowList [1,0]))
      (exhibit [1,0]).coords)
    (elim.vecScale (casScalar (rowList [1,0]))
      (exhibit [1,0]).coords) := by apply casimirM_top

example : poly.oneValue
    (elim.matVec (casimirM [2,1].length (rowList [2,1]))
      (exhibit [2,1]).coords)
    (elim.vecScale (casScalar (rowList [2,1]))
      (exhibit [2,1]).coords) := by decide +kernel

/-! The refusal.  The diagonal squares alone miss the top read at
the vacant second row: the pair fold carries the difference. -/

example : ¬ poly.oneValue
    (elim.matVec (casimirM [1,0].length (rowList [1,0]))
      (exhibit [1,0]).coords)
    (elim.vecScale (BPair.ofNat 1)
      (exhibit [1,0]).coords) := by decide +kernel

/-! The row list's weak descent is the top read's own restriction,
exhibited rather than isolated: `[0,1]` is off the descent, so it
carries no exhibit and the vector below is not its own top — the
refusal breaks the vector's topness and the descent at once, with
the descending mirror deciding true at the same vector.  A
coupling exhibit, not an isolating refusal. -/

example : ¬ poly.oneValue
    (elim.matVec (casimirM 2 [0,1]) [BPair.ofNat 1])
    (elim.vecScale (casScalar [0,1]) [BPair.ofNat 1]) := by decide +kernel

example : poly.oneValue
    (elim.matVec (casimirM 2 [1,0]) [BPair.ofNat 1])
    (elim.vecScale (casScalar [1,0]) [BPair.ofNat 1]) := by decide +kernel

/-! The fold's collection is load-bearing: the moved read holds of
the whole matrix and of no single term.  `E_01` carries the
content `[1,1]` to `[2,0]`; at the first coordinate of that
content's enumeration the raising after `C` at `[1,1]` and `C` at
`[2,0]` after the raising read one value, while the naive
per-term reads at the letter pair
`(1,1)` — the composite `E_11 E_11` through the moved content
`moveAt 1 1` on each side — differ outright: the letter is
occupied at `[1,1]` and vacant at `[2,0]`, so the two composites
carry the raising's image to different values.  The delta families
cancel across the fold and never term by term, which is what the
tex's collection at `casimirM` states. -/

example : poly.oneValue
    (elim.matVec (units.matUnitAt [2,0] [1,1] 0 1)
      (elim.matVec (casimirM 2 [1,1]) [BPair.ofNat 1, BPair.unit]))
    (elim.matVec (casimirM 2 [2,0])
      (elim.matVec (units.matUnitAt [2,0] [1,1] 0 1)
        [BPair.ofNat 1, BPair.unit])) := by decide +kernel

example : ¬ poly.oneValue
    (elim.matVec (units.matUnitAt [2,0] [1,1] 0 1)
      (elim.matVec (elim.matMul
          (units.matUnitAt [1,1] (moveAt 1 1 [1,1]) 1 1)
          (units.matUnitAt (moveAt 1 1 [1,1]) [1,1] 1 1))
        [BPair.ofNat 1, BPair.unit]))
    (elim.matVec (elim.matMul
        (units.matUnitAt [2,0] (moveAt 1 1 [2,0]) 1 1)
        (units.matUnitAt (moveAt 1 1 [2,0]) [2,0] 1 1))
      (elim.matVec (units.matUnitAt [2,0] [1,1] 0 1)
        [BPair.ofNat 1, BPair.unit])) := by decide +kernel

/-! `con:units`' table at the coordinate vectors: the join decided
at a three-letter content with one live delta and one refused, and
its theorem instance, then the both-refused instance — the swap
read's own shape.  The content hypotheses are `blockcount.out_gen`'s,
so the battery sits with its consumer's module rather than at the
theorem's owner, whose check module cannot reach them. -/

example : poly.oneValue
      (elim.vecAdd
        (elim.matVec (units.matUnitAt [1,0,2] [0,1,2] 0 1)
          (elim.matVec (units.matUnitAt [0,1,2] [1,1,1] 2 0)
            [BPair.ofNat 1, BPair.unit, BPair.unit, BPair.unit,
              BPair.unit, BPair.unit]))
        (if (0 : Nat) = 0 then
          elim.matVec (units.matUnitAt [1,0,2] [1,1,1] 2 1)
            [BPair.ofNat 1, BPair.unit, BPair.unit, BPair.unit,
              BPair.unit, BPair.unit]
        else List.replicate (monomialsAt [1,0,2]).length BPair.unit))
      (elim.vecAdd
        (elim.matVec (units.matUnitAt [1,0,2] [2,0,1] 2 0)
          (elim.matVec (units.matUnitAt [2,0,1] [1,1,1] 0 1)
            [BPair.ofNat 1, BPair.unit, BPair.unit, BPair.unit,
              BPair.unit, BPair.unit]))
        (if (1 : Nat) = 2 then
          elim.matVec (units.matUnitAt [1,0,2] [1,1,1] 0 0)
            [BPair.ofNat 1, BPair.unit, BPair.unit, BPair.unit,
              BPair.unit, BPair.unit]
        else List.replicate (monomialsAt [1,0,2]).length
          BPair.unit)) := by decide +kernel

-- both deltas dead: the swap read's own shape
example : ∀ x : List BPair,
    x.length = (monomialsAt [1,1,1]).length →
    poly.oneValue
      (elim.vecAdd
        (elim.matVec (units.matUnitAt [3,0,0] [2,1,0] 0 1)
          (elim.matVec (units.matUnitAt [2,1,0] [1,1,1] 0 2) x))
        (if (0 : Nat) = 2 then
          elim.matVec (units.matUnitAt [3,0,0] [1,1,1] 0 1) x
        else List.replicate (monomialsAt [3,0,0]).length BPair.unit))
      (elim.vecAdd
        (elim.matVec (units.matUnitAt [3,0,0] [2,0,1] 0 2)
          (elim.matVec (units.matUnitAt [2,0,1] [1,1,1] 0 1) x))
        (if (1 : Nat) = 0 then
          elim.matVec (units.matUnitAt [3,0,0] [1,1,1] 0 2) x
        else List.replicate (monomialsAt [3,0,0]).length
          BPair.unit)) :=
  units.matVec_table_read [2,1,0] [2,0,1] [3,0,0] [1,1,1] 0 1 0 2
    (out_gen [1,1,1] 0 2 (by decide +kernel) (by decide +kernel))
    (out_gen [2,1,0] 0 1 (by decide +kernel) (by decide +kernel))
    (out_gen [1,1,1] 0 1 (by decide +kernel) (by decide +kernel))
    (out_gen [2,0,1] 0 2 (by decide +kernel) (by decide +kernel))
    (fun h => absurd h (by decide +kernel))
    (fun h => absurd h (by decide +kernel))

-- live/dead delta instance: a = d live, b = c dead
example : ∀ x : List BPair,
    x.length = (monomialsAt [1,1,1]).length →
    poly.oneValue
      (elim.vecAdd
        (elim.matVec (units.matUnitAt [1,0,2] [0,1,2] 0 1)
          (elim.matVec (units.matUnitAt [0,1,2] [1,1,1] 2 0) x))
        (if (0 : Nat) = 0 then
          elim.matVec (units.matUnitAt [1,0,2] [1,1,1] 2 1) x
        else List.replicate (monomialsAt [1,0,2]).length BPair.unit))
      (elim.vecAdd
        (elim.matVec (units.matUnitAt [1,0,2] [2,0,1] 2 0)
          (elim.matVec (units.matUnitAt [2,0,1] [1,1,1] 0 1) x))
        (if (1 : Nat) = 2 then
          elim.matVec (units.matUnitAt [1,0,2] [1,1,1] 0 0) x
        else List.replicate (monomialsAt [1,0,2]).length
          BPair.unit)) :=
  units.matVec_table_read [0,1,2] [2,0,1] [1,0,2] [1,1,1] 0 1 2 0
    (out_gen [1,1,1] 2 0 (by decide +kernel) (by decide +kernel))
    (out_gen [0,1,2] 0 1 (by decide +kernel) (by decide +kernel))
    (out_gen [1,1,1] 0 1 (by decide +kernel) (by decide +kernel))
    (out_gen [2,0,1] 2 0 (by decide +kernel) (by decide +kernel))
    (fun _ => out_gen [1,1,1] 2 1 (by decide +kernel) (by decide +kernel))
    (fun h => absurd h (by decide +kernel))

/-! The moved reads' battery: the commutation decided at the walk's
own contents — among them the configurations whose per-pair joins
go through every vacant-letter branch (the raised letter vacant in
the moved content at `[1,1]` with the letters reversed, the vacant
unit letter at `[1,0]`, and the raising's own letter vacant at
`[0,1]` and `[0,1,0]`) — and the theorem discharged at its
instances.  The committed per-term refusal above is this battery's
counterpart: the join fails per term at `[1,1]`'s reversed pair
while the fold's total commutes, the collection load-bearing.  The
range binders are load-bearing and their refusal is committed: at
a unit letter inside the content but at the fold's range the picks
at that letter's guards go unreached, the delta folds keep their
residue, and the commutation fails outright.  Three couplings
decide true at their forgeries and are committed as exhibits
rather than refusals — the range beyond the content's letters acts
at the unit tail on both members, the diagonal letters commute at
the grading, and a vector off the enumeration's width truncates
both members together. -/

-- the commutation decided at the falsification's own content: the
-- per-term join fails at the reversed pair while the total holds
example : poly.oneValue
    (elim.matVec (units.matUnitAt (moveAt 0 1 [1,1]) [1,1] 0 1)
      (elim.matVec (casimirM 2 [1,1]) [BPair.ofNat 1, BPair.unit]))
    (elim.matVec (casimirM 2 (moveAt 0 1 [1,1]))
      (elim.matVec (units.matUnitAt (moveAt 0 1 [1,1]) [1,1] 0 1)
        [BPair.ofNat 1, BPair.unit])) := by decide +kernel

-- the letters reversed: the raised letter vacant in the moved
-- content, the shorter-instance branch's own configuration
example : poly.oneValue
    (elim.matVec (units.matUnitAt (moveAt 1 0 [1,1]) [1,1] 1 0)
      (elim.matVec (casimirM 2 [1,1]) [BPair.unit, BPair.ofNat 1]))
    (elim.matVec (casimirM 2 (moveAt 1 0 [1,1]))
      (elim.matVec (units.matUnitAt (moveAt 1 0 [1,1]) [1,1] 1 0)
        [BPair.unit, BPair.ofNat 1])) := by decide +kernel

-- the unit letter vacant: both members at the unit tail
example : poly.oneValue
    (elim.matVec (units.matUnitAt (moveAt 0 1 [1,0]) [1,0] 0 1)
      (elim.matVec (casimirM 2 [1,0]) [BPair.ofNat 1]))
    (elim.matVec (casimirM 2 (moveAt 0 1 [1,0]))
      (elim.matVec (units.matUnitAt (moveAt 0 1 [1,0]) [1,0] 0 1)
        [BPair.ofNat 1])) := by decide +kernel

-- the commutation decided at a general vector of [2,1]'s enumeration
example : poly.oneValue
    (elim.matVec (units.matUnitAt (moveAt 0 1 [2,1]) [2,1] 0 1)
      (elim.matVec (casimirM 2 [2,1])
        [BPair.ofNat 1, BPair.ofNat 2, BPair.ofNat 3]))
    (elim.matVec (casimirM 2 (moveAt 0 1 [2,1]))
      (elim.matVec (units.matUnitAt (moveAt 0 1 [2,1]) [2,1] 0 1)
        [BPair.ofNat 1, BPair.ofNat 2, BPair.ofNat 3])) := by decide +kernel

-- the theorem discharged at the falsification content's instance
example : poly.oneValue
    (elim.matVec (units.matUnitAt (moveAt 0 1 [1,1]) [1,1] 0 1)
      (elim.matVec (casimirM 2 [1,1]) [BPair.ofNat 1, BPair.unit]))
    (elim.matVec (casimirM 2 (moveAt 0 1 [1,1]))
      (elim.matVec (units.matUnitAt (moveAt 0 1 [1,1]) [1,1] 0 1)
        [BPair.ofNat 1, BPair.unit])) :=
  casimirM_comm 2 [1,1] 0 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    rfl [BPair.ofNat 1, BPair.unit] rfl

-- the theorem discharged at the reversed letters' instance
example : poly.oneValue
    (elim.matVec (units.matUnitAt (moveAt 1 0 [1,1]) [1,1] 1 0)
      (elim.matVec (casimirM 2 [1,1]) [BPair.unit, BPair.ofNat 1]))
    (elim.matVec (casimirM 2 (moveAt 1 0 [1,1]))
      (elim.matVec (units.matUnitAt (moveAt 1 0 [1,1]) [1,1] 1 0)
        [BPair.unit, BPair.ofNat 1])) :=
  casimirM_comm 2 [1,1] 1 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    rfl [BPair.unit, BPair.ofNat 1] rfl

-- the exhibits at the unrefused couplings: the range beyond the
-- content's letters, and the diagonal letters
example : poly.oneValue
    (elim.matVec (units.matUnitAt (moveAt 0 1 [1,1]) [1,1] 0 1)
      (elim.matVec (casimirM 3 [1,1]) [BPair.ofNat 1, BPair.unit]))
    (elim.matVec (casimirM 3 (moveAt 0 1 [1,1]))
      (elim.matVec (units.matUnitAt (moveAt 0 1 [1,1]) [1,1] 0 1)
        [BPair.ofNat 1, BPair.unit])) := by decide +kernel

example : poly.oneValue
    (elim.matVec (units.matUnitAt (moveAt 0 0 [2,1]) [2,1] 0 0)
      (elim.matVec (casimirM 2 [2,1])
        [BPair.ofNat 1, BPair.unit, BPair.unit]))
    (elim.matVec (casimirM 2 (moveAt 0 0 [2,1]))
      (elim.matVec (units.matUnitAt (moveAt 0 0 [2,1]) [2,1] 0 0)
        [BPair.ofNat 1, BPair.unit, BPair.unit])) := by decide +kernel

-- the range binders' refusal: the unit letter inside the content
-- at the fold's range — the picks at its guards unreached, the
-- delta folds keeping their residue
example : ¬ poly.oneValue
    (elim.matVec (units.matUnitAt (moveAt 0 1 [1,1]) [1,1] 0 1)
      (elim.matVec (casimirM 1 [1,1]) [BPair.ofNat 1, BPair.unit]))
    (elim.matVec (casimirM 1 (moveAt 0 1 [1,1]))
      (elim.matVec (units.matUnitAt (moveAt 0 1 [1,1]) [1,1] 0 1)
        [BPair.ofNat 1, BPair.unit])) := by decide +kernel

-- the raising's own letter vacant: the branch at the unit's raise
example : poly.oneValue
    (elim.matVec (units.matUnitAt (moveAt 0 1 [0,1]) [0,1] 0 1)
      (elim.matVec (casimirM 2 [0,1]) [BPair.ofNat 1]))
    (elim.matVec (casimirM 2 (moveAt 0 1 [0,1]))
      (elim.matVec (units.matUnitAt (moveAt 0 1 [0,1]) [0,1] 0 1)
        [BPair.ofNat 1])) := by decide +kernel

-- the theorem discharged where the dispatch reaches all four
-- branches at once
example : poly.oneValue
    (elim.matVec (units.matUnitAt (moveAt 0 1 [0,1,0]) [0,1,0] 0 1)
      (elim.matVec (casimirM 3 [0,1,0]) [BPair.ofNat 1]))
    (elim.matVec (casimirM 3 (moveAt 0 1 [0,1,0]))
      (elim.matVec (units.matUnitAt (moveAt 0 1 [0,1,0]) [0,1,0]
        0 1) [BPair.ofNat 1])) :=
  casimirM_comm 3 [0,1,0] 0 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    rfl [BPair.ofNat 1] rfl

/-! The eigen tier's own battery: the block read decided at the
one-letter shape and at a two-letter one — the `C` family acting on
every span member as the block scalar — with the theorem instance
beside it, and the trace read decided at that shape's first letter
pair, at an occupied content and at a content the span never
carries (the collected list empty, the fold and the product at
their vacant reads and the count the sum's unit), each beside its
own theorem instance. -/

example : ∀ w ∈ blockSpan [1],
    poly.oneValue
      (elim.matVec (casimirM ([1] : Shape).length w.content)
        w.coords)
      (elim.vecScale (casScalar (rowList [1])) w.coords) := by
  decide +kernel

example : ∀ w ∈ blockSpan [2, 1],
    poly.oneValue
      (elim.matVec (casimirM ([2, 1] : Shape).length w.content)
        w.coords)
      (elim.vecScale (casScalar (rowList [2, 1])) w.coords) := by
  rw [blockcount.span21_pin]; decide +kernel

example : ∀ w ∈ blockSpan [2, 1],
    poly.oneValue
      (elim.matVec (casimirM ([2, 1] : Shape).length w.content)
        w.coords)
      (elim.vecScale (casScalar (rowList [2, 1])) w.coords) :=
  casimirM_member [2, 1]

example : (trFold (casimirM ([2, 1] : Shape).length [2, 2])
      (strings.membersAt 0 1
        (strings.walk 0 1 (blockSpan [2, 1])) [2, 2])).oneValue
    (BPair.ofNat (strings.stringCount 0 1
        (strings.walk 0 1 (blockSpan [2, 1])) [2, 2])
      * casScalar (rowList [2, 1])
      * prodAll (strings.membersAt 0 1
          (strings.walk 0 1 (blockSpan [2, 1])) [2, 2])) := by
  rw [strings.walk21_pin]; decide +kernel

example : (trFold (casimirM ([2, 1] : Shape).length [2, 2])
      (strings.membersAt 0 1
        (strings.walk 0 1 (blockSpan [2, 1])) [2, 2])).oneValue
    (BPair.ofNat (strings.stringCount 0 1
        (strings.walk 0 1 (blockSpan [2, 1])) [2, 2])
      * casScalar (rowList [2, 1])
      * prodAll (strings.membersAt 0 1
          (strings.walk 0 1 (blockSpan [2, 1])) [2, 2])) :=
  casimirM_trace [2, 1] 0 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [2, 2]

example : (trFold (casimirM ([2, 1] : Shape).length [5, 5])
      (strings.membersAt 0 1
        (strings.walk 0 1 (blockSpan [2, 1])) [5, 5])).oneValue
    (BPair.ofNat (strings.stringCount 0 1
        (strings.walk 0 1 (blockSpan [2, 1])) [5, 5])
      * casScalar (rowList [2, 1])
      * prodAll (strings.membersAt 0 1
          (strings.walk 0 1 (blockSpan [2, 1])) [5, 5])) := by
  rw [strings.walk21_pin]; decide +kernel

/-! `thm:weylchar`'s per-pair string traces close the module: at
the two-letter block's one string the two ordered words' folds
over the collected members read the two side weights, each decided
against its own theorem instance at the block's middle content —
the raising word `E_ij E_ji` at `stringWeightUp` and the lowering
word `E_ji E_ij` at `stringWeightDn`, the two weights' sum the
display's coefficient — and a content the span never carries reads
the vacant fold on both sides, the count at the sum's unit against
the empty product. -/

example : (trFold
    (elim.matMul (units.matUnitAt [2, 2] (moveAt 1 0 [2, 2]) 0 1)
      (units.matUnitAt (moveAt 1 0 [2, 2]) [2, 2] 1 0))
    (strings.membersAt 0 1
      (strings.walk 0 1 (blockSpan [2, 1])) [2, 2])).oneValue
  (BPair.ofNat (strings.stringWeightUp 0 1
      (strings.walk 0 1 (blockSpan [2, 1])) [2, 2])
    * prodAll (strings.membersAt 0 1
        (strings.walk 0 1 (blockSpan [2, 1])) [2, 2])) := by
  rw [strings.walk21_pin]; decide +kernel

example : (trFold
    (elim.matMul (units.matUnitAt [2, 2] (moveAt 1 0 [2, 2]) 0 1)
      (units.matUnitAt (moveAt 1 0 [2, 2]) [2, 2] 1 0))
    (strings.membersAt 0 1
      (strings.walk 0 1 (blockSpan [2, 1])) [2, 2])).oneValue
  (BPair.ofNat (strings.stringWeightUp 0 1
      (strings.walk 0 1 (blockSpan [2, 1])) [2, 2])
    * prodAll (strings.membersAt 0 1
        (strings.walk 0 1 (blockSpan [2, 1])) [2, 2])) :=
  stringTraceUp [2, 1] 0 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [2, 2]

example : (trFold
    (elim.matMul (units.matUnitAt [2, 2] (moveAt 0 1 [2, 2]) 1 0)
      (units.matUnitAt (moveAt 0 1 [2, 2]) [2, 2] 0 1))
    (strings.membersAt 0 1
      (strings.walk 0 1 (blockSpan [2, 1])) [2, 2])).oneValue
  (BPair.ofNat (strings.stringWeightDn 0 1
      (strings.walk 0 1 (blockSpan [2, 1])) [2, 2])
    * prodAll (strings.membersAt 0 1
        (strings.walk 0 1 (blockSpan [2, 1])) [2, 2])) := by
  rw [strings.walk21_pin]; decide +kernel

example : (trFold
    (elim.matMul (units.matUnitAt [2, 2] (moveAt 0 1 [2, 2]) 1 0)
      (units.matUnitAt (moveAt 0 1 [2, 2]) [2, 2] 0 1))
    (strings.membersAt 0 1
      (strings.walk 0 1 (blockSpan [2, 1])) [2, 2])).oneValue
  (BPair.ofNat (strings.stringWeightDn 0 1
      (strings.walk 0 1 (blockSpan [2, 1])) [2, 2])
    * prodAll (strings.membersAt 0 1
        (strings.walk 0 1 (blockSpan [2, 1])) [2, 2])) :=
  stringTraceDn [2, 1] 0 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [2, 2]

example : (trFold
    (elim.matMul (units.matUnitAt [5, 5] (moveAt 1 0 [5, 5]) 0 1)
      (units.matUnitAt (moveAt 1 0 [5, 5]) [5, 5] 1 0))
    (strings.membersAt 0 1
      (strings.walk 0 1 (blockSpan [2, 1])) [5, 5])).oneValue
  (BPair.ofNat (strings.stringWeightUp 0 1
      (strings.walk 0 1 (blockSpan [2, 1])) [5, 5])
    * prodAll (strings.membersAt 0 1
        (strings.walk 0 1 (blockSpan [2, 1])) [5, 5])) := by
  rw [strings.walk21_pin]; decide +kernel

/-! `lem:casimir`'s second discharge theorem: the trace recursion
at the span's contents.  The display is decided at the one-letter
shape (its letter pairs vacant, so the moved folds die and the
display is the count's own) and at the two-letter shape whose
span carries a genuine lowering, and the theorem's own instances
sit beside them by mechanical extraction.  At three letters the
degree prices the decide: the shape `[1,1,1]` exceeds the whnf
heartbeat budget while its lower-degree sibling `[1,1,0]`, the
same content set, decides directly — the three-letter reads run
there and at `[2,1,0]`, the first shapes whose letter-pair folds
hold more than one member. -/

example : weylchar.recRead [1]
    ((blockSpan [1]).map HVec.content) := by
  decide +kernel

example : weylchar.recRead [1]
    ((blockSpan [1]).map HVec.content) :=
  recRead_def [1]

example : weylchar.recRead [2, 1]
    ((blockSpan [2, 1]).map HVec.content) := by
  rw [blockcount.span21_pin]; decide +kernel

example : weylchar.recRead [2, 1]
    ((blockSpan [2, 1]).map HVec.content) :=
  recRead_def [2, 1]

example : weylchar.recRead [1, 1, 1]
    ((blockSpan [1, 1, 1]).map HVec.content) :=
  recRead_def [1, 1, 1]

-- the recursion read at three letters: the first shapes whose
-- letter-pair folds hold more than one member
example : weylchar.recRead [1,1,0]
    ((blockSpan [1,1,0]).map HVec.content) := by
  rw [blockcount.span110_pin]; decide +kernel

example : weylchar.recRead [2,1,0]
    ((blockSpan [2,1,0]).map HVec.content) := by decide +kernel

-- the symmetry read at three letters
example : weylchar.symRead (List.length [1,1,0])
    ((blockSpan [1,1,0]).map HVec.content) := by
  rw [blockcount.span110_pin]; decide +kernel
