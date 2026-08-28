import MassGap.Assembly
import MassGapChecks.Sertables
/-!
The check module for `thm:assembly`'s read layer: the batteries
re-read the assembly coefficients by kernel `decide` at `B_2` and
`G_2`, the two members whose Weyl folds are stated outright.  Per
member the graded image list of `ρ` enters with its witness list
and closes at three reads — the closure at the letters, each
member's reflection image sitting in the list at the flipped side
at the member's own count; the support, each member's key joining
its witness fold over the simples back to `ρ`; and the regular
read, `ρ` once at the even side and off the odd — and the
identity's per-key balance `Φ = a_ρ` is read through the general
theorem: `balanceRead` applied whole at the stated fundamental
data of both members, every hypothesis read discharged by kernel
decide, at the top key, at a key off both folds, at a list member
whose first entry sits on its lower side — the walk's raise — and
at an occupied key holding a simple coroot pair the unit, the
fixed-key pin.  The committed refusals isolate the reads at the
theorem's own conclusion: a forged witness at the top member,
which the support read alone refuses; the list joined to the
reflection closure of a regular dominant key off `ρ`, which the
support read alone refuses with the balance failing at the
adjoined orbit's key; one further member's side flipped, which
the closure read alone refuses; the list doubled, which the
regular read alone refuses; and a forged side at the top member,
which the closure, the regular read and the balance at `ρ` all
refuse while the support read, blind to the sides, stays green.
The graded image list's shape read closes at both members with
its refusal at a key off the rank's order, and the Weyl fold's
transport is read at its own conclusion — the count at a
reflected key against the count at the key on the other side, at
both letters of `B_2` and at a key the list misses entirely.

The eigen tier's batteries follow: the Euler collections at `B_2`
and `G_2` with the moved form's two shape refusals off the
`ρ`-key, the line telescope's application with its decide twin and
cap refusal, and the bridge at the `ρ`-membership count with the
long-keyed, doubled and flipped families' refusals.
-/

open ground places gentable sertables assembly

/-! The stated data per member: the graded image list of `ρ` with
its witness list over the simples — `G_2`'s here, `B_2`'s the
shared data at `MassGapChecks/Sertables.lean`. -/

private def wG2 : List (List BPair × Bool) := [([(BPair.ofNat 1), (BPair.ofNat 1)], false), ([(BPair.ofNat 1).swap, (BPair.ofNat 2)], true), ([(BPair.ofNat 4), (BPair.ofNat 1).swap], true), ([(BPair.ofNat 4).swap, (BPair.ofNat 3)], false), ([(BPair.ofNat 5), (BPair.ofNat 3).swap], true), ([(BPair.ofNat 5).swap, (BPair.ofNat 2)], false), ([(BPair.ofNat 1), (BPair.ofNat 2).swap], true), ([(BPair.ofNat 1).swap, (BPair.ofNat 1).swap], false), ([(BPair.ofNat 4).swap, (BPair.ofNat 1)], true), ([(BPair.ofNat 4), (BPair.ofNat 3).swap], false), ([(BPair.ofNat 5).swap, (BPair.ofNat 3)], true), ([(BPair.ofNat 5), (BPair.ofNat 2).swap], false)]
private def witsG2 : List (List Nat) := [[0, 0], [1, 0], [0, 1], [4, 1], [4, 4], [9, 4], [9, 6], [10, 6], [10, 5], [6, 5], [6, 2], [1, 2]]

/-! The three reads of the graded image list per member: the
closure at the letters, the support at the stated witnesses, and
the regular read at `ρ`. -/

example : wCloseRead tB2 wB2 := by decide +kernel
example : wDomRead tB2 wB2 witsB2 := by decide +kernel
example : wTopRead tB2 wB2 := by decide +kernel

example : wCloseRead tableG2 wG2 := by decide +kernel
example : wDomRead tableG2 wG2 witsG2 := by decide +kernel
example : wTopRead tableG2 wG2 := by decide +kernel

/-! The general theorem applied whole: `balanceRead` at the stated
fundamental data, every hypothesis read discharged by kernel
decide, at the top key of both members and at a key off both
folds. -/

example : balanceAt tB2 wB2 (poly.pnorm (rhoV tB2)) :=
  balanceRead tB2 fundB2 wB2 witsB2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (poly.pnorm (rhoV tB2)) (by decide +kernel) (by decide +kernel)

example : balanceAt tB2 wB2 [BPair.ofNat 5, BPair.ofNat 5] :=
  balanceRead tB2 fundB2 wB2 witsB2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [BPair.ofNat 5, BPair.ofNat 5] (by decide +kernel) (by decide +kernel)

example : balanceAt tableG2 wG2 (poly.pnorm (rhoV tableG2)) :=
  balanceRead tableG2 fundG2 wG2 witsG2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (poly.pnorm (rhoV tableG2)) (by decide +kernel) (by decide +kernel)

/- the walk's raise branch: a list member at a lower-side first
entry, the reflection walking it to its dominant image -/
example : balanceAt tB2 wB2 [(BPair.ofNat 1).swap, BPair.ofNat 3] :=
  balanceRead tB2 fundB2 wB2 witsB2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(BPair.ofNat 1).swap, BPair.ofNat 3] (by decide +kernel) (by decide +kernel)

example : balanceAt tableG2 wG2 [(BPair.ofNat 4).swap, BPair.ofNat 3] :=
  balanceRead tableG2 fundG2 wG2 witsG2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(BPair.ofNat 4).swap, BPair.ofNat 3] (by decide +kernel) (by decide +kernel)

/- pin (a): an occupied dominant key at a simple coroot pair the
unit, the letter's own fix pairing each fold's sides -/
example : subsetCount tB2 [BPair.unit, BPair.ofNat 1] false = 1 := by
  decide +kernel
example : balanceAt tB2 wB2 [BPair.unit, BPair.ofNat 1] :=
  balanceRead tB2 fundB2 wB2 witsB2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [BPair.unit, BPair.ofNat 1] (by decide +kernel) (by decide +kernel)

/-! The graded image list's isolating refusals at the general
theorem's own conclusion, one read each.  The support read alone:
the list joined to the reflection closure of a regular dominant
key off `ρ` — closure, regular and shape reads green, the support
read refusing, and the balance failing at the adjoined orbit's
dominant key.  The closure read alone: one further member's side
flipped, the regular and support reads green.  The regular read
alone: the list doubled, the closure and support reads green. -/

private def muBad : List BPair := [BPair.ofNat 3, BPair.ofNat 1]

private def orbitBad : List (List BPair × Bool) :=
  ([[], [0], [1], [0, 1], [1, 0], [0, 1, 0], [1, 0, 1],
    [0, 1, 0, 1]] : List (List Nat)).map
    (fun l => (l.foldl (fun a i => reflAt tB2 i a) (poly.pnorm muBad),
               places.parityOf l.length))

private def wBad : List (List BPair × Bool) := wB2 ++ orbitBad
private def witsPad : List (List Nat) :=
  witsB2 ++ [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0],
    [0, 0], [0, 0]]

example : wCloseRead tB2 wBad := by decide +kernel
example : wTopRead tB2 wBad := by decide +kernel
example : wShapeRead tB2 wBad := by decide +kernel
example : ¬ wDomRead tB2 wBad witsPad := by decide +kernel
example : ¬ balanceAt tB2 wBad (poly.pnorm muBad) := by decide +kernel
example : wCount wBad (poly.pnorm muBad) false = 1 := by decide +kernel
example : subsetCount tB2 (poly.pnorm muBad) false = 0 := by decide +kernel

private def wFlip : List (List BPair × Bool) :=
  [([(BPair.ofNat 1), (BPair.ofNat 1)], false),
   ([(BPair.ofNat 1).swap, (BPair.ofNat 3)], false),
   ([(BPair.ofNat 2), (BPair.ofNat 1).swap], true),
   ([(BPair.ofNat 2).swap, (BPair.ofNat 3)], false),
   ([(BPair.ofNat 1), (BPair.ofNat 3).swap], true),
   ([(BPair.ofNat 1).swap, (BPair.ofNat 1).swap], false),
   ([(BPair.ofNat 2).swap, (BPair.ofNat 1)], true),
   ([(BPair.ofNat 2), (BPair.ofNat 3).swap], false)]

example : ¬ wCloseRead tB2 wFlip := by decide +kernel
example : wTopRead tB2 wFlip := by decide +kernel
example : wDomRead tB2 wFlip witsB2 := by decide +kernel
example : ¬ balanceAt tB2 wFlip
    [(BPair.ofNat 1).swap, BPair.ofNat 3] := by decide +kernel

private def wDbl : List (List BPair × Bool) := wB2 ++ wB2
private def witsDbl : List (List Nat) := witsB2 ++ witsB2

example : wCloseRead tB2 wDbl := by decide +kernel
example : wDomRead tB2 wDbl witsDbl := by decide +kernel
example : ¬ wTopRead tB2 wDbl := by decide +kernel
example : ¬ balanceAt tB2 wDbl (poly.pnorm (rhoV tB2)) := by decide +kernel

/-! The committed refusals at the graded image list, each
isolating one datum with the reads it leaves untouched pinned
beside it. -/

-- the top member's witness forged off the unit fold: the support
-- read refuses, the closure and the regular read carrying no
-- witness datum
private def forgedWitsB2 : List (List Nat) :=
  [[1, 0], [1, 0], [0, 1], [2, 1], [2, 4], [3, 4], [3, 3], [1, 3]]

example : ¬ wDomRead tB2 wB2 forgedWitsB2 := by decide +kernel

-- the top member's side forged odd: the closure refuses at the
-- flipped counts, the regular read at `ρ`'s own count and the
-- identity at the top key, while the support read, blind to the
-- sides, stays green
private def forgedWB2 : List (List BPair × Bool) :=
  [([(BPair.ofNat 1), (BPair.ofNat 1)], true), ([(BPair.ofNat 1).swap, (BPair.ofNat 3)], true), ([(BPair.ofNat 2), (BPair.ofNat 1).swap], true), ([(BPair.ofNat 2).swap, (BPair.ofNat 3)], false), ([(BPair.ofNat 1), (BPair.ofNat 3).swap], true), ([(BPair.ofNat 1).swap, (BPair.ofNat 1).swap], false), ([(BPair.ofNat 2).swap, (BPair.ofNat 1)], true), ([(BPair.ofNat 2), (BPair.ofNat 3).swap], false)]

example : ¬ wCloseRead tB2 forgedWB2 := by decide +kernel
example : ¬ wTopRead tB2 forgedWB2 := by decide +kernel
example : ¬ balanceAt tB2 forgedWB2
    [BPair.ofNat 1, BPair.ofNat 1] := by decide +kernel
example : wDomRead tB2 forgedWB2 witsB2 := by decide +kernel
example : ¬ (wCount forgedWB2
      (reflAt tB2 0 (poly.pnorm (rhoV tB2))) false
    = wCount forgedWB2 (poly.pnorm (rhoV tB2)) true) := by decide +kernel

/-! The graded image list's shape read at both members — every
member's key at the rank, normed — with the refusal at a key off
the rank's order, the closure refusing with it at the shapeless
member's own count. -/

example : wShapeRead tB2 wB2 := by decide +kernel
example : wShapeRead tableG2 wG2 := by decide +kernel

example : ¬ wShapeRead tB2 (wB2 ++ [([BPair.ofNat 1], false)]) := by decide +kernel
example : ¬ wCloseRead tB2 (wB2 ++ [([BPair.ofNat 1], false)]) := by decide +kernel

/-! The Weyl fold's transport at its own conclusion: the graded
count at a reflected key against the count at the key on the other
side, read at both letters of `B_2` at the top key and once at a
normed key the list misses entirely (both counts the sum's
unit). -/

example : wCount wB2 (reflAt tB2 0 (poly.pnorm (rhoV tB2))) false
    = wCount wB2 (poly.pnorm (rhoV tB2)) true := by decide +kernel
example : wCount wB2 (reflAt tB2 1 (poly.pnorm (rhoV tB2))) true
    = wCount wB2 (poly.pnorm (rhoV tB2)) false := by decide +kernel

example : wCount wB2
      (reflAt tB2 0 (poly.pnorm [BPair.ofNat 5, BPair.ofNat 5])) false
    = wCount wB2 (poly.pnorm [BPair.ofNat 5, BPair.ofNat 5]) true := by decide +kernel

/-! The subset fold's transport at its own conclusion: the graded
count at a reflected key against the count at the key on the other
side, read at both letters of `B_2` at the top key and once at a
normed key off every family's read (both counts the sum's
unit). -/

example : subsetCount tB2 (reflAt tB2 0 (poly.pnorm (rhoV tB2))) false
    = subsetCount tB2 (poly.pnorm (rhoV tB2)) true := by decide +kernel
example : subsetCount tB2 (reflAt tB2 1 (poly.pnorm (rhoV tB2))) true
    = subsetCount tB2 (poly.pnorm (rhoV tB2)) false := by decide +kernel

example : subsetCount tB2
      (reflAt tB2 0 (poly.pnorm [BPair.ofNat 5, BPair.ofNat 5])) false
    = subsetCount tB2 (poly.pnorm [BPair.ofNat 5, BPair.ofNat 5]) true := by
  decide +kernel

/-! The collection's read against the subset fold at committed
keys and values: the expansion identity's instances at counts the
merge's addition path reaches (`B_3`'s seven at the occupied key),
with `G_2` at the `ρ` key on both spellings.  The `B_3` reads sit
at `maxRecDepth 2048`, the running table's recursion depth at the
five-hundred-family enumeration. -/

private def tB3 : gentable.Table := tableB 3

example : ground.tabRead (fun k => decide
      (k = [BPair.unit, BPair.ofNat 1, (BPair.ofNat 1).swap])) false
    (subsetTable tB3) = 7 := by decide +kernel
example : subsetCount tB3
    [BPair.unit, BPair.ofNat 1, (BPair.ofNat 1).swap] false = 7 := by
  decide +kernel
example : subsetCount tB3
    [BPair.unit, BPair.ofNat 1, (BPair.ofNat 1).swap] true = 7 := by
  decide +kernel

example : ground.tabRead (fun k => decide
      (k = poly.pnorm (rhoV tableG2))) false
    (subsetTable tableG2) = 1 := by decide +kernel
example : subsetCount tableG2 (poly.pnorm (rhoV tableG2)) false
    = 1 := by decide +kernel

/-! The transport's table refusals: the conclusion binds no field of
the fundamental data, so a forged table is the isolating shape. -/

-- the rho-dot read isolated: rank one, the genuine simple beside a
-- "positive" at the simple's balance partner — the five further
-- hypotheses hold, the ρ-dot read refuses, and the conclusion fails
-- at the ρ key on one side (the other side agrees, both counts
-- pinned)
private def rhoForgeT : gentable.Table :=
  ⟨1, [2], 1,
   [[BPair.ofNat 2], [(BPair.ofNat 4).swap]],
   [[1], [1, 1]],
   [1]⟩
private def rhoForgeF : FundData := ⟨[[BPair.ofNat 1]], 1, [0], [[1, 0]]⟩

example : fundShape rhoForgeT rhoForgeF := by decide +kernel
example : simplePosRead rhoForgeT rhoForgeF := by decide +kernel
example : reflSquareRead rhoForgeT := by decide +kernel
example : permSquareRead rhoForgeT rhoForgeF := by decide +kernel
example : permImageRead rhoForgeT rhoForgeF := by decide +kernel
example : ¬ rhoDotRead rhoForgeT rhoForgeF := by decide +kernel
example : ¬ (subsetCount rhoForgeT
      (reflAt rhoForgeT 0 (poly.pnorm (rhoV rhoForgeT))) true
    = subsetCount rhoForgeT (poly.pnorm (rhoV rhoForgeT)) false) := by decide +kernel
example : subsetCount rhoForgeT
    (reflAt rhoForgeT 0 (poly.pnorm (rhoV rhoForgeT))) true = 1 := by decide +kernel
example : subsetCount rhoForgeT
    (poly.pnorm (rhoV rhoForgeT)) false = 2 := by decide +kernel
example : subsetCount rhoForgeT
      (reflAt rhoForgeT 0 (poly.pnorm (rhoV rhoForgeT))) false
    = subsetCount rhoForgeT (poly.pnorm (rhoV rhoForgeT)) true := by decide +kernel

-- the permutation-square read isolated: A2 with the highest root
-- listed twice, so the image read pins the datum only up to the
-- duplicated member and a 3-cycle survives it — every further read
-- holds, the square read refuses, and the conclusion fails at the
-- unit key
private def permForgeT : gentable.Table :=
  ⟨2, [2, 2], 1,
   [[BPair.ofNat 2, (BPair.ofNat 1).swap],
    [(BPair.ofNat 1).swap, BPair.ofNat 2]],
   [[1, 0], [0, 1], [1, 1], [1, 1]],
   [1, 1]⟩
private def permForgeF : FundData :=
  ⟨[[BPair.ofNat 4, BPair.ofNat 2], [BPair.ofNat 2, BPair.ofNat 4]], 3,
   [0, 1], [[0, 2, 1, 1], [2, 1, 0, 0]]⟩

example : fundShape permForgeT permForgeF := by decide +kernel
example : simplePosRead permForgeT permForgeF := by decide +kernel
example : reflSquareRead permForgeT := by decide +kernel
example : permImageRead permForgeT permForgeF := by decide +kernel
example : rhoDotRead permForgeT permForgeF := by decide +kernel
example : gramRead permForgeT permForgeF := by decide +kernel
example : gramSymRead permForgeF := by decide +kernel
example : ¬ permSquareRead permForgeT permForgeF := by decide +kernel
example : (poly.pnorm [BPair.unit, BPair.unit] : List BPair)
    = [BPair.unit, BPair.unit] := by decide +kernel
example : ¬ (subsetCount permForgeT
      (reflAt permForgeT 0 [BPair.unit, BPair.unit]) true
    = subsetCount permForgeT [BPair.unit, BPair.unit] false) := by decide +kernel
example : subsetCount permForgeT
    (reflAt permForgeT 0 [BPair.unit, BPair.unit]) true = 2 := by decide +kernel
example : subsetCount permForgeT
    [BPair.unit, BPair.unit] false = 1 := by decide +kernel

/-! The withdrawn-index subset fold and its split
(`thm:memberchar`'s cofactor `Q_j`): the fold off an index at
committed counts, the split read through the general theorem at
`B_2`'s top key, and the committed refusal at a key off the
representative spelling — where the moved key still lands on an
occupied family while the key itself lands on none, so the
identity's normed-key binder is load-bearing. -/

example : subsetCountOff tB2 0 (poly.pnorm (rhoV tB2)) false = 1 := by
  decide +kernel
example : subsetCountOff tB2 0 (poly.pnorm (rhoV tB2)) true = 0 := by
  decide +kernel
example : subsetCountOff tB2 1 [BPair.unit, BPair.ofNat 1] false = 1 := by
  decide +kernel
example : subsetCountOff tB2 1 [BPair.unit, BPair.ofNat 1] true = 1 := by
  decide +kernel

example : subsetCount tB2 (poly.pnorm (rhoV tB2)) false
    = subsetCountOff tB2 0 (poly.pnorm (rhoV tB2)) false
      + subsetCountOff tB2 0 (poly.pnorm (elim.vecAdd
          (poly.pnorm (rhoV tB2)) (posCorootV tB2 0))) true :=
  subsetCount_off_split tB2 0 (by decide +kernel) (poly.pnorm (rhoV tB2))
    (by decide +kernel) (by decide +kernel) false

example : subsetCount tB2 (eKey tB2 [2]) true
    = subsetCountOff tB2 1 (eKey tB2 [2]) true
      + subsetCountOff tB2 1 (poly.pnorm (elim.vecAdd
          (eKey tB2 [2]) (posCorootV tB2 1))) false :=
  subsetCount_off_split tB2 1 (by decide +kernel) (eKey tB2 [2])
    (by decide +kernel) (by decide +kernel) true

private def yUnn : List BPair :=
  elim.vecAdd (eKey tB2 [2])
    (elim.vecAdd (posCorootV tB2 0) (poly.neg (posCorootV tB2 0)))

example : ¬ poly.pnorm yUnn = yUnn := by decide +kernel
example : yUnn.length = tB2.rank := by decide +kernel
example : subsetCount tB2 yUnn false = 0 := by decide +kernel
example : subsetCountOff tB2 0 yUnn false
    + subsetCountOff tB2 0 (poly.pnorm (elim.vecAdd yUnn
        (posCorootV tB2 0))) true = 1 := by decide +kernel

/-! The unbalanced key's dot square applied whole at `B_2`'s stated
Weyl fold: every member's two graded counts part there, so each key
carries `ρ`'s own dot square — read at the top key and at a member
whose first entry sits on its lower side. -/

example : BPair.oneValue
    (dotB fundB2 [BPair.ofNat 1, BPair.ofNat 1]
      [BPair.ofNat 1, BPair.ofNat 1])
    (dotB fundB2 (rhoV tB2) (rhoV tB2)) :=
  wOff_dotSq tB2 fundB2 wB2 witsB2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [BPair.ofNat 1, BPair.ofNat 1] false (List.Mem.head _)
    (by decide +kernel)

example : BPair.oneValue
    (dotB fundB2 [(BPair.ofNat 1).swap, BPair.ofNat 3]
      [(BPair.ofNat 1).swap, BPair.ofNat 3])
    (dotB fundB2 (rhoV tB2) (rhoV tB2)) :=
  wOff_dotSq tB2 fundB2 wB2 witsB2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(BPair.ofNat 1).swap, BPair.ofNat 3] true
    (List.Mem.tail _ (List.Mem.head _)) (by decide +kernel)

example : ground.countOf ([BPair.ofNat 1, BPair.ofNat 1], true) wB2
    ≠ ground.countOf ([BPair.ofNat 1, BPair.ofNat 1], false) wB2 := by
  decide +kernel

/-! The Euler collection applied whole at `B_2` and `G_2`: the
per-root fold of dots against withdrawn-fold count pairs reads the
key's dot joined to `ρ`'s own at the subset counts, at an occupied
key and at `ρ` itself. -/

example : (ground.famFold BPair.add BPair.unit (fun j =>
      BPair.mul (dotB fundB2 (rhoV tB2) (posCorootV tB2 j))
        (BPair.ofCounts (subsetCountOff tB2 j (eKey tB2 [0]) false)
          (subsetCountOff tB2 j (eKey tB2 [0]) true)))
      (List.range tB2.posFolds.length)).oneValue
    (BPair.mul
      (BPair.add (dotB fundB2 (rhoV tB2) (eKey tB2 [0]))
        (dotB fundB2 (rhoV tB2) (rhoV tB2)))
      (BPair.ofCounts (subsetCount tB2 (eKey tB2 [0]) false)
        (subsetCount tB2 (eKey tB2 [0]) true))) :=
  subsetCountOff_euler tB2 fundB2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (rhoV tB2) (eKey tB2 [0]) (by decide +kernel)

private def tG2 : gentable.Table := tableG2

example : (ground.famFold BPair.add BPair.unit (fun j =>
      BPair.mul (dotB fundG2 (rhoV tG2) (posCorootV tG2 j))
        (BPair.ofCounts
          (subsetCountOff tG2 j (poly.pnorm (rhoV tG2)) false)
          (subsetCountOff tG2 j (poly.pnorm (rhoV tG2)) true)))
      (List.range tG2.posFolds.length)).oneValue
    (BPair.mul
      (BPair.add (dotB fundG2 (rhoV tG2) (poly.pnorm (rhoV tG2)))
        (dotB fundG2 (rhoV tG2) (rhoV tG2)))
      (BPair.ofCounts (subsetCount tG2 (poly.pnorm (rhoV tG2)) false)
        (subsetCount tG2 (poly.pnorm (rhoV tG2)) true))) :=
  subsetCountOff_euler tG2 fundG2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (rhoV tG2) (poly.pnorm (rhoV tG2)) (by decide +kernel)

/-! The split's two shape binders at their forged refusals: a key
truncated past the rank and a fold key off the positive list each
refuse the split's display. -/

private def yLong : List BPair := eKey tB2 [2] ++ [BPair.unit]

example : ¬ yLong.length = tB2.rank := by decide +kernel
example : poly.pnorm yLong = yLong := by decide +kernel
example : ¬ (subsetCount tB2 yLong false
    = subsetCountOff tB2 0 yLong false
      + subsetCountOff tB2 0
          (poly.pnorm (elim.vecAdd yLong (posCorootV tB2 0)))
          true) := by decide +kernel

example : ¬ (4 < tB2.posFolds.length) := by decide +kernel
example : ¬ (subsetCount tB2 (eKey tB2 [2]) true
    = subsetCountOff tB2 4 (eKey tB2 [2]) true
      + subsetCountOff tB2 4
          (poly.pnorm (elim.vecAdd (eKey tB2 [2])
            (posCorootV tB2 4)))
          false) := by decide +kernel

/-! The line telescope applied at `B_2`: the withdrawn pair at the
stepped key collects the subset pairs along the line at an occupied
first key, the decide twin beside the theorem route, and a cap
short of the height refuses. -/

example : (BPair.ofCounts
      (subsetCountOff tB2 0 (poly.pnorm (elim.vecAdd (eKey tB2 [0])
        (posCorootV tB2 0))) false)
      (subsetCountOff tB2 0 (poly.pnorm (elim.vecAdd (eKey tB2 [0])
        (posCorootV tB2 0))) true)).oneValue
    (ground.famFold BPair.add BPair.unit (fun l =>
      BPair.ofCounts
        (subsetCount tB2 (poly.pnorm (elim.vecAdd (eKey tB2 [0])
          (elim.vecScale (BPair.ofNat (l + 1))
            (posCorootV tB2 0)))) false)
        (subsetCount tB2 (poly.pnorm (elim.vecAdd (eKey tB2 [0])
          (elim.vecScale (BPair.ofNat (l + 1))
            (posCorootV tB2 0)))) true))
      (List.range 2)) :=
  subsetCountOff_line tB2 fundB2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (eKey tB2 [0]) (by decide +kernel) 2 (by decide +kernel)

example : (BPair.ofCounts
      (subsetCountOff tB2 0 (poly.pnorm (elim.vecAdd (eKey tB2 [0])
        (posCorootV tB2 0))) false)
      (subsetCountOff tB2 0 (poly.pnorm (elim.vecAdd (eKey tB2 [0])
        (posCorootV tB2 0))) true)).oneValue
    (ground.famFold BPair.add BPair.unit (fun l =>
      BPair.ofCounts
        (subsetCount tB2 (poly.pnorm (elim.vecAdd (eKey tB2 [0])
          (elim.vecScale (BPair.ofNat (l + 1))
            (posCorootV tB2 0)))) false)
        (subsetCount tB2 (poly.pnorm (elim.vecAdd (eKey tB2 [0])
          (elim.vecScale (BPair.ofNat (l + 1))
            (posCorootV tB2 0)))) true))
      (List.range 2)) := by decide +kernel

example : ¬ (dotB fundB2 (rhoV tB2) (rhoV tB2)
    < dotB fundB2 (rhoV tB2) (poly.pnorm (elim.vecAdd (eKey tB2 [0])
        (elim.vecScale (BPair.ofNat (0 + 1))
          (posCorootV tB2 0)))))  := by decide +kernel

example : ¬ (BPair.ofCounts
      (subsetCountOff tB2 0 (poly.pnorm (elim.vecAdd (eKey tB2 [0])
        (posCorootV tB2 0))) false)
      (subsetCountOff tB2 0 (poly.pnorm (elim.vecAdd (eKey tB2 [0])
        (posCorootV tB2 0))) true)).oneValue
    (ground.famFold BPair.add BPair.unit (fun l =>
      BPair.ofCounts
        (subsetCount tB2 (poly.pnorm (elim.vecAdd (eKey tB2 [0])
          (elim.vecScale (BPair.ofNat (l + 1))
            (posCorootV tB2 0)))) false)
        (subsetCount tB2 (poly.pnorm (elim.vecAdd (eKey tB2 [0])
          (elim.vecScale (BPair.ofNat (l + 1))
            (posCorootV tB2 0)))) true))
      (List.range 0)) := by decide +kernel

/-! The moved Euler collection and the bridge applied whole at
`B_2`: the stepped keys' pairs against the roots' dots at an
occupied key, and the alternant fold against the subset fold at
the `ρ`-membership count, the value off the unit with its refusal
pinned beside it. -/

example : (ground.famFold BPair.add BPair.unit (fun j =>
      BPair.mul (dotB fundB2 (rhoV tB2) (posCorootV tB2 j))
        (BPair.ofCounts
          (subsetCountOff tB2 j (poly.pnorm (elim.vecAdd
            (eKey tB2 [0]) (posCorootV tB2 j))) false)
          (subsetCountOff tB2 j (poly.pnorm (elim.vecAdd
            (eKey tB2 [0]) (posCorootV tB2 j))) true)))
      (List.range tB2.posFolds.length)).oneValue
    (BPair.mul
      (BPair.add (dotB fundB2 (rhoV tB2) (eKey tB2 [0]))
        ((dotB fundB2 (rhoV tB2) (rhoV tB2)).swap))
      (BPair.ofCounts (subsetCount tB2 (eKey tB2 [0]) false)
        (subsetCount tB2 (eKey tB2 [0]) true))) :=
  subsetCountOff_euler_moved tB2 fundB2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (rhoV tB2) (eKey tB2 [0]) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : (ground.famFold BPair.add BPair.unit
      (fun vp => ground.signedAt vp.2
        (BPair.ofNat (ground.countOf vp.1 [rhoV tB2])))
      wB2).oneValue
    (ground.famFold BPair.add BPair.unit
      (fun S => ground.signedAt (sideOf S)
        (BPair.ofNat (ground.countOf (eKey tB2 S) [rhoV tB2])))
      (sublistsOf (List.range tB2.posFolds.length))) :=
  wFold_subsets tB2 fundB2 wB2 witsB2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun k => BPair.ofNat (ground.countOf k [rhoV tB2]))

example : ¬ (ground.famFold BPair.add BPair.unit
    (fun S => ground.signedAt (sideOf S)
      (BPair.ofNat (ground.countOf (eKey tB2 S) [rhoV tB2])))
    (sublistsOf (List.range tB2.posFolds.length))).oneValue
    BPair.unit := by decide +kernel

/-! The moved collection's two shape binders at their isolating
refusals off the `ρ`-key, each forge failing exactly one binder;
and the bridge's four read binders at theirs — the long-keyed
family, the doubled list, and the flipped grading. -/

private def kU : List BPair := [(⟨2, 3⟩ : BPair), ⟨5, 2⟩]
private def kL : List BPair := eKey tB2 [0] ++ [BPair.unit]

example : kU.length = tB2.rank := by decide +kernel
example : ¬ poly.pnorm kU = kU := by decide +kernel
example : ¬ (ground.famFold BPair.add BPair.unit (fun j =>
      BPair.mul (dotB fundB2 (rhoV tB2) (posCorootV tB2 j))
        (BPair.ofCounts
          (subsetCountOff tB2 j (poly.pnorm (elim.vecAdd
            kU (posCorootV tB2 j))) false)
          (subsetCountOff tB2 j (poly.pnorm (elim.vecAdd
            kU (posCorootV tB2 j))) true)))
      (List.range tB2.posFolds.length)).oneValue
    (BPair.mul
      (BPair.add (dotB fundB2 (rhoV tB2) kU)
        ((dotB fundB2 (rhoV tB2) (rhoV tB2)).swap))
      (BPair.ofCounts (subsetCount tB2 kU false)
        (subsetCount tB2 kU true))) := by decide +kernel

example : poly.pnorm kL = kL := by decide +kernel
example : ¬ kL.length = tB2.rank := by decide +kernel
example : ¬ (ground.famFold BPair.add BPair.unit (fun j =>
      BPair.mul (dotB fundB2 (rhoV tB2) (posCorootV tB2 j))
        (BPair.ofCounts
          (subsetCountOff tB2 j (poly.pnorm (elim.vecAdd
            kL (posCorootV tB2 j))) false)
          (subsetCountOff tB2 j (poly.pnorm (elim.vecAdd
            kL (posCorootV tB2 j))) true)))
      (List.range tB2.posFolds.length)).oneValue
    (BPair.mul
      (BPair.add (dotB fundB2 (rhoV tB2) kL)
        ((dotB fundB2 (rhoV tB2) (rhoV tB2)).swap))
      (BPair.ofCounts (subsetCount tB2 kL false)
        (subsetCount tB2 kL true))) := by decide +kernel

private def wLong : List (List BPair × Bool) :=
  wB2 ++ [([BPair.ofNat 1, BPair.ofNat 1, BPair.unit], false)]
private def witsLong : List (List Nat) := witsB2 ++ [[0, 0]]

example : ¬ wShapeRead tB2 wLong := by decide +kernel
example : wCloseRead tB2 wLong := by decide +kernel
example : wDomRead tB2 wLong witsLong := by decide +kernel
example : wTopRead tB2 wLong := by decide +kernel
example : ¬ (ground.famFold BPair.add BPair.unit
    (fun vp => ground.signedAt vp.2
      (dotB fundB2 vp.1 vp.1)) wLong).oneValue
    (ground.famFold BPair.add BPair.unit
      (fun S => ground.signedAt (sideOf S)
        (dotB fundB2 (eKey tB2 S) (eKey tB2 S)))
      (sublistsOf (List.range tB2.posFolds.length))) := by decide +kernel

example : wShapeRead tB2 wDbl := by decide +kernel
example : ¬ (ground.famFold BPair.add BPair.unit
    (fun vp => ground.signedAt vp.2
      (BPair.ofNat (ground.countOf vp.1 [rhoV tB2]))) wDbl).oneValue
    (ground.famFold BPair.add BPair.unit
      (fun S => ground.signedAt (sideOf S)
        (BPair.ofNat (ground.countOf (eKey tB2 S) [rhoV tB2])))
      (sublistsOf (List.range tB2.posFolds.length))) := by decide +kernel

example : wShapeRead tB2 wFlip := by decide +kernel
example : ¬ (ground.famFold BPair.add BPair.unit
    (fun vp => ground.signedAt vp.2
      (BPair.ofNat (ground.countOf vp.1
        [[(BPair.ofNat 1).swap, BPair.ofNat 3]]))) wFlip).oneValue
    (ground.famFold BPair.add BPair.unit
      (fun S => ground.signedAt (sideOf S)
        (BPair.ofNat (ground.countOf (eKey tB2 S)
          [[(BPair.ofNat 1).swap, BPair.ofNat 3]])))
      (sublistsOf (List.range tB2.posFolds.length))) := by decide +kernel

/-! `cor:weyldim`'s subset bridges: the pair product over a distinct
index expands over the occupancy families at the complement-guarded
degree folds, and at a weight whose positive dots sit at or beyond
the sum's unit a family's degree fold solves to the shifted key's
own margin — read here at the two-member index and at `B_2`'s
`ρ`-weight against the family holding the second positive member. -/

example : poly.oneValue
    (ground.famFold poly.mul poly.one
      (fun j => poly.tpair (j + 1)) (List.range 2))
    (ground.famFold poly.add []
      (fun S => poly.smono (sideOf S)
        (ground.famFold Nat.add 0
          (fun j => if 0 < ground.countOf j S then 0 else j + 1)
          (List.range 2)))
      (sublistsOf (List.range 2))) := by decide +kernel

example : ground.famFold Nat.add 0
      (fun j => if 0 < ground.countOf j [1] then 0
        else gapsAt tB2 fundB2 (rhoV tB2) j)
      (List.range tB2.posFolds.length)
    = BPair.marginN (BPair.add (dotB fundB2 (rhoV tB2) (rhoV tB2))
        (dotB fundB2 (eKey tB2 [1]) (rhoV tB2))) :=
  gapFold_eKey tB2 fundB2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (rhoV tB2) (by decide +kernel) [1] (by decide +kernel)
