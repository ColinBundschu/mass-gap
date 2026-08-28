import MassGap.Rankstable
import MassGap.Channels
/-!
The check module for `lem:rankstable`(i)'s `casPoly` tier: the
batteries read the banded family's member and the Casimir's
cleared quadratic by kernel `decide` — the member at the adjoint's
own family and at `2θ`'s row, its full-column bump against the
stored `θ` row and the vacuum's vacant shape; the bottom block's
prefix sums and the successor-weighted fold at a padded word; the
polynomial's value against `c2hat.dfQ` at the adjoint, at a padded
family and at an asymmetric one, each decided beside the general
theorem's own route; the below-floor refusal, the structural floor
load-bearing; and the vacuum's whole-domain read at its own floor.
The dimension tier's batteries read the two members against
`weyldim.dimOf` the same way — the pair's cross-multiplied
agreement decided at the adjoint's family and at a padded one with
the dimensions pinned beside them, the general theorem's route at
those two and at an asymmetric family, the below-floor refusal,
and the vacuum's pair at its own floor.  The diagonal tier's
batteries read the two graded sums at the adjoint's own member with
the display's unit-gap count decided beside them and the join
through the general theorem; the width binder is load-bearing — off
the stated width both sums read the fold's unit while the join
demands the residue, the refusal decided; and the member's diagonal
routes at the adjoint's family, at an asymmetric one, at the floor
and at the vacuum, each beside its own decided key count with the
two counts' own reads pinned.  The off-diagonal tier's batteries
read the two sums at an occupied target and at a vacant one, each
decided beside the theorem's own route — the adjoint's member
against `2θ`'s row, a padded family at width four — with the
diagonal's exclusion and the width binder each isolated by its own
refusal, the mismatched shape's own bump pinned beside it.  The
confinement window's batteries read an occupied target's
clear-window keys vacant through the theorem, the whole window at
the vacuum's member and one key at the adjoint's, beside their
decided pins; the two margins are load-bearing, the same occupied
target carrying occupancy at the key just below the floor and at
the key just above the ceiling.  The row tier's batteries display
`adjRow` at the unit label and at the adjoint itself at the two
counts, and at a one-box shape; the count agreement runs both ways
there, through `adjCount_eq`'s route and decided.  The whole row
reads against the definitional enumeration at the same one-box
shape — `adjRow_eq`'s own route at an occupied label, the count
equation decided at that label, at a second one and at a label off
the row, with the definitional side's own list value beside the
landed `adjRow` pin, the two orders parting and the counts
agreeing.  The width and floor binders are load-bearing with
committed isolating refusals, at the row tie and at the count
agreement alike: off the stated width the definitional row is
vacant while the fast row reads its junk members, and at the
width one the definitional row is occupied at the vacuum while
the fast row is vacant.
-/
set_option maxHeartbeats 4000000

open ground places rankstable

/-! The carrier ties: the member against the committed shapes. -/

example : member [1] [1] 6 = adjchar.theta 6 := by decide +kernel

example : member [2] [2] 6 = channels.rowTwoTheta 6 := by decide +kernel

example : ground.bumpAt 5 (member [1] [1] 6) = channels.rowTheta 6 := by
  decide +kernel

example : member [] [] 5 = List.replicate 5 0 := by decide +kernel

/-! The bottom block's prefix sums and the successor-weighted fold
at a padded word, each at its own public spelling. -/

example : (places.rowList ([4, 0, 2].reverse ++ [0])).tail = [4, 4, 0] := by
  decide +kernel

example : ground.sumNat (places.rowList [4, 0, 2]) = 10 := by decide +kernel

/-! The evaluation at the adjoint's family, the decided value
beside the theorem's route. -/

example : (poly.eval (casPoly [1] [1]) (ground.BPair.ofNat 6)).oneValue
    (ground.BPair.ofNat 72) := by decide +kernel

example : (poly.eval (casPoly [1] [1]) (ground.BPair.ofNat 6)).oneValue
    (ground.BPair.ofNat (c2hat.dfQ (member [1] [1] 6))) :=
  casPoly_eval [1] [1] 6 (by decide +kernel)

example : c2hat.dfQ (member [1] [1] 6) = 72 := by decide +kernel

/-! A padded family and an asymmetric one. -/

example : (poly.eval (casPoly [0, 1] [0, 1]) (ground.BPair.ofNat 9)).oneValue
    (ground.BPair.ofNat (c2hat.dfQ (member [0, 1] [0, 1] 9))) := by decide +kernel

example : (poly.eval (casPoly [2, 1, 1] [1, 2])
    (ground.BPair.ofNat 11)).oneValue
    (ground.BPair.ofNat (c2hat.dfQ (member [2, 1, 1] [1, 2] 11))) :=
  casPoly_eval [2, 1, 1] [1, 2] 11 (by decide +kernel)

example : c2hat.dfQ (member [2, 1, 1] [1, 2] 11) = 1558 := by decide +kernel

/-! The floor is load-bearing: below it the reads part. -/

example : ¬ (poly.eval (casPoly [1] [1]) (ground.BPair.ofNat 2)).oneValue
    (ground.BPair.ofNat (c2hat.dfQ (member [1] [1] 2))) := by decide +kernel

/-! The vacuum's whole-domain read at its own floor. -/

example : (poly.eval (casPoly [] []) (ground.BPair.ofNat 1)).oneValue
    (ground.BPair.ofNat (c2hat.dfQ (member [] [] 1))) :=
  casPoly_eval [] [] 1 (by decide +kernel)

example : c2hat.dfQ (member [] [] 1) = 0 := by decide +kernel

/-! The dimension pair at the adjoint's family and at the padded
one, each decided value beside the theorem's own route. -/

example : weyldim.dimOf (member [1] [1] 6) = 35 := by decide +kernel

example : (poly.eval (dimNum [1] [1]) (ground.BPair.ofNat 6)).oneValue
    (ground.BPair.ofNat 35
      * poly.eval (dimDen [1] [1]) (ground.BPair.ofNat 6)) := by decide +kernel

example : (poly.eval (dimNum [1] [1]) (ground.BPair.ofNat 6)).oneValue
    (ground.BPair.ofNat (weyldim.dimOf (member [1] [1] 6))
      * poly.eval (dimDen [1] [1]) (ground.BPair.ofNat 6)) :=
  dimPair_eval [1] [1] 6 (by decide +kernel)

example : weyldim.dimOf (member [0, 1] [0, 1] 7) = 392 := by decide +kernel

example : (poly.eval (dimNum [0, 1] [0, 1])
    (ground.BPair.ofNat 7)).oneValue
    (ground.BPair.ofNat 392
      * poly.eval (dimDen [0, 1] [0, 1]) (ground.BPair.ofNat 7)) := by
  decide +kernel

example : (poly.eval (dimNum [0, 1] [0, 1])
    (ground.BPair.ofNat 7)).oneValue
    (ground.BPair.ofNat (weyldim.dimOf (member [0, 1] [0, 1] 7))
      * poly.eval (dimDen [0, 1] [0, 1]) (ground.BPair.ofNat 7)) :=
  dimPair_eval [0, 1] [0, 1] 7 (by decide +kernel)

/-! An asymmetric family's route. -/

example : (poly.eval (dimNum [2, 1, 1] [1, 2])
    (ground.BPair.ofNat 9)).oneValue
    (ground.BPair.ofNat (weyldim.dimOf (member [2, 1, 1] [1, 2] 9))
      * poly.eval (dimDen [2, 1, 1] [1, 2]) (ground.BPair.ofNat 9)) :=
  dimPair_eval [2, 1, 1] [1, 2] 9 (by decide +kernel)

/-! The floor is load-bearing: below it the pair parts. -/

example : ¬ (poly.eval (dimNum [1] [1]) (ground.BPair.ofNat 2)).oneValue
    (ground.BPair.ofNat (weyldim.dimOf (member [1] [1] 2))
      * poly.eval (dimDen [1] [1]) (ground.BPair.ofNat 2)) := by decide +kernel

/-! The vacuum's pair at its own floor. -/

example : (poly.eval (dimNum [] []) (ground.BPair.ofNat 1)).oneValue
    (ground.BPair.ofNat (weyldim.dimOf (member [] [] 1))
      * poly.eval (dimDen [] []) (ground.BPair.ofNat 1)) :=
  dimPair_eval [] [] 1 (by decide +kernel)

/-! The diagonal tier: the two graded sums at the adjoint's own
member with the display's unit-gap count beside them, the join
through the general theorem, and the width binder's refusal. -/

example : steinberg.sumsWith (adjchar.multRead 6) 6 (member [1] [1] 6)
    (ground.bumpAt (6 - 1) (member [1] [1] 6)) = (5, 3) := by decide +kernel

example : clearGaps (places.display (member [1] [1] 6)) = 3 := by decide +kernel

example : (steinberg.sumsWith (adjchar.multRead 6) 6 (member [1] [1] 6)
      (ground.bumpAt (6 - 1) (member [1] [1] 6))).1
    + clearGaps (places.display (member [1] [1] 6))
  = (steinberg.sumsWith (adjchar.multRead 6) 6 (member [1] [1] 6)
      (ground.bumpAt (6 - 1) (member [1] [1] 6))).2 + 5 :=
  diagJoin 6 (member [1] [1] 6)
    (by decide +kernel : (member [1] [1] 6).length = 6)

/-! The width is load-bearing: at a shape off the stated width both
sums read the fold's unit while the join demands the residue. -/

example : ¬ ((steinberg.sumsWith (adjchar.multRead 3) 3 [1, 0]
      (ground.bumpAt (3 - 1) [1, 0])).1 + clearGaps (places.display [1, 0])
    = (steinberg.sumsWith (adjchar.multRead 3) 3 [1, 0]
      (ground.bumpAt (3 - 1) [1, 0])).2 + 2) := by decide +kernel

/-! The member's diagonal at the adjoint's family, at an asymmetric
one and at the floor, each route beside its own decided key
count. -/

example : suppCount [1] + suppCount [1] = 2 := by decide +kernel

example : (steinberg.sumsWith (adjchar.multRead 6) 6 (member [1] [1] 6)
      (ground.bumpAt (6 - 1) (member [1] [1] 6))).1
    = (steinberg.sumsWith (adjchar.multRead 6) 6 (member [1] [1] 6)
        (ground.bumpAt (6 - 1) (member [1] [1] 6))).2
      + (suppCount [1] + suppCount [1]) :=
  rowDiag [1] [1] 6 (by decide +kernel)

example : suppCount [2, 1, 1] + suppCount [1, 2] = 5 := by decide +kernel

example : (steinberg.sumsWith (adjchar.multRead 9) 9
      (member [2, 1, 1] [1, 2] 9)
      (ground.bumpAt (9 - 1) (member [2, 1, 1] [1, 2] 9))).1
    = (steinberg.sumsWith (adjchar.multRead 9) 9
        (member [2, 1, 1] [1, 2] 9)
        (ground.bumpAt (9 - 1) (member [2, 1, 1] [1, 2] 9))).2
      + (suppCount [2, 1, 1] + suppCount [1, 2]) :=
  rowDiag [2, 1, 1] [1, 2] 9 (by decide +kernel)

example : steinberg.sumsWith (adjchar.multRead 3) 3 (member [1] [1] 3)
    (ground.bumpAt (3 - 1) (member [1] [1] 3)) = (2, 0) := by decide +kernel

example : (steinberg.sumsWith (adjchar.multRead 3) 3 (member [1] [1] 3)
      (ground.bumpAt (3 - 1) (member [1] [1] 3))).1
    = (steinberg.sumsWith (adjchar.multRead 3) 3 (member [1] [1] 3)
        (ground.bumpAt (3 - 1) (member [1] [1] 3))).2
      + (suppCount [1] + suppCount [1]) :=
  rowDiag [1] [1] 3 (by decide +kernel)

/-! The vacuum's own read: the two sums agree and the diagonal is
vacant, the member's defect. -/

example : steinberg.sumsWith (adjchar.multRead 5) 5 (member [] [] 5)
    (ground.bumpAt (5 - 1) (member [] [] 5)) = (4, 4) := by decide +kernel

example : (steinberg.sumsWith (adjchar.multRead 5) 5 (member [] [] 5)
      (ground.bumpAt (5 - 1) (member [] [] 5))).1
    = (steinberg.sumsWith (adjchar.multRead 5) 5 (member [] [] 5)
        (ground.bumpAt (5 - 1) (member [] [] 5))).2
      + (suppCount [] + suppCount []) :=
  rowDiag [] [] 5 (by decide +kernel)

/-! The two counts' own reads. -/

example : suppCount [2, 0, 1] = 2 := by decide +kernel

example : clearGaps [5, 4, 2, 1] = 2 := by decide +kernel

/-! The off-diagonal tier: the two sums at an occupied off-diagonal
target and at a vacant one, each decided beside the theorem's own
route — the adjoint's member against `2θ`'s row at the width, a
padded family at width four — with the diagonal's exclusion and the
width binder each isolated by its own refusal. -/

example : steinberg.sumsWith (adjchar.multRead 6) 6 (member [1] [1] 6)
    (member [2] [2] 6) = (1, 0) := by decide +kernel

example : (steinberg.sumsWith (adjchar.multRead 6) 6 (member [1] [1] 6)
      (member [2] [2] 6)).1
    ≤ (steinberg.sumsWith (adjchar.multRead 6) 6 (member [1] [1] 6)
        (member [2] [2] 6)).2 + 1 :=
  rowOffOne 6 (member [1] [1] 6) (member [2] [2] 6) (by decide +kernel) (by decide +kernel)

example : steinberg.sumsWith (adjchar.multRead 4) 4 (member [1] [] 4)
    [2, 0, 1, 0] = (1, 0) := by decide +kernel

example : (steinberg.sumsWith (adjchar.multRead 4) 4 (member [1] [] 4)
      [2, 0, 1, 0]).1
    ≤ (steinberg.sumsWith (adjchar.multRead 4) 4 (member [1] [] 4)
        [2, 0, 1, 0]).2 + 1 :=
  rowOffOne 4 (member [1] [] 4) [2, 0, 1, 0] (by decide +kernel) (by decide +kernel)

/-! A vacant off-diagonal target: both sums read the fold's unit and
the theorem's route stands there too. -/

example : steinberg.sumsWith (adjchar.multRead 4) 4 (member [1] [] 4)
    [1, 2, 0, 0] = (0, 0) := by decide +kernel

example : (steinberg.sumsWith (adjchar.multRead 4) 4 (member [1] [] 4)
      [1, 2, 0, 0]).1
    ≤ (steinberg.sumsWith (adjchar.multRead 4) 4 (member [1] [] 4)
        [1, 2, 0, 0]).2 + 1 :=
  rowOffOne 4 (member [1] [] 4) [1, 2, 0, 0] (by decide +kernel) (by decide +kernel)

/-! The diagonal's exclusion is load-bearing: at the full-column
bump the residue's count parts the two sums by more than one. -/

example : steinberg.sumsWith (adjchar.multRead 5) 5 (member [1] [1] 5)
    (ground.bumpAt (5 - 1) (member [1] [1] 5)) = (4, 2) := by decide +kernel

example : ¬ ((steinberg.sumsWith (adjchar.multRead 5) 5 (member [1] [1] 5)
      (ground.bumpAt (5 - 1) (member [1] [1] 5))).1
    ≤ (steinberg.sumsWith (adjchar.multRead 5) 5 (member [1] [1] 5)
        (ground.bumpAt (5 - 1) (member [1] [1] 5))).2 + 1) := by decide +kernel

/-! The width binder is load-bearing: at a shape off the stated
width the permuted display still ties, and the even sum runs away
from the odd — the target off the shape's own bump. -/

example : ground.bumpAt (3 - 1) [1, 1] = [1, 1] := by decide +kernel

example : steinberg.sumsWith (adjchar.multRead 3) 3 [1, 1] [1, 1, 0]
    = (2, 0) := by decide +kernel

example : ¬ ((steinberg.sumsWith (adjchar.multRead 3) 3 [1, 1] [1, 1, 0]).1
    ≤ (steinberg.sumsWith (adjchar.multRead 3) 3 [1, 1] [1, 1, 0]).2 + 1) := by
  decide +kernel

/-! The member's confinement window: at an occupied target the
clear-window keys read the target vacant through the theorem, beside
their own decided pins — the whole window at the vacuum's member and
one key at the adjoint's — and the window's two margins are load-
bearing, the same occupied target carrying occupancy at the key just
below the floor and at the key just above the ceiling. -/

example : steinberg.sumsWith (adjchar.multRead 5) 5 (member [] [] 5)
    (member [1] [1] 5) = (1, 0) := by decide +kernel

example : ground.getAt 0 (member [1] [1] 5) 1 = 0 := by decide +kernel

example : ground.getAt 0 (member [1] [1] 5) 2 = 0 := by decide +kernel

example : ∀ k, ([] : List Nat).length + 1 ≤ k →
    k + ([] : List Nat).length + 3 ≤ 5 →
    ground.getAt 0 (member [1] [1] 5) k = 0 :=
  rowConfined [] [] 5 (member [1] [1] 5) (by decide +kernel)

example : ¬ ground.getAt 0 (member [1] [1] 5) 0 = 0 := by decide +kernel

example : ¬ ground.getAt 0 (member [1] [1] 5) 3 = 0 := by decide +kernel

/-! The adjoint's own member at its single window key. -/

example : ground.getAt 0 (member [2] [2] 6) 2 = 0 := by decide +kernel

example : ground.getAt 0 (member [2] [2] 6) 2 = 0 :=
  rowConfined [1] [1] 6 (member [2] [2] 6) (by decide +kernel) 2
    (by decide +kernel) (by decide +kernel)

/-! The floor and the occupancy binders are load-bearing: below the
member's structural floor the sums part from the key count, and at
a vacant gap the window read fails. -/

example : ¬ ((steinberg.sumsWith (adjchar.multRead 2) 2
      (member [1] [1] 2)
      (ground.bumpAt (2 - 1) (member [1] [1] 2))).1
    = (steinberg.sumsWith (adjchar.multRead 2) 2
      (member [1] [1] 2)
      (ground.bumpAt (2 - 1) (member [1] [1] 2))).2
      + (suppCount [1] + suppCount [1])) := by decide +kernel

example : ¬ ((steinberg.sumsWith (adjchar.multRead 5) 5
      (member [] [] 5) [1, 1, 0, 0, 0]).2
    < (steinberg.sumsWith (adjchar.multRead 5) 5
      (member [] [] 5) [1, 1, 0, 0, 0]).1) := by decide +kernel

example : ¬ ground.getAt 0 ([1, 1, 0, 0, 0] : places.Shape) 1 = 0 := by
  decide +kernel

/-! The adjoint fusion row: the word list at the unit label and at
the adjoint itself, at the two counts, and at a one-box shape.
The count agreement runs both ways at the one-box shape — through
the theorem's own route and decided. -/

example : adjRow 2 (labels.unitL 2) = [[2, 0]] := by decide +kernel

example : adjRow 3 (labels.unitL 3) = [[1, 1, 0]] := by decide +kernel

example : adjRow 2 (adjchar.theta 2) = [[2, 0], [4, 0], [0, 0]] := by decide +kernel

example : adjRow 3 (adjchar.theta 3)
    = [[1, 1, 0], [3, 0, 0], [2, 2, 0], [0, 3, 0], [0, 0, 0]] := by decide +kernel

example : adjRow 3 ([1, 0, 0] : Shape)
    = [[1, 0, 0], [2, 1, 0], [0, 2, 0]] := by decide +kernel

example : steinberg.count ([1, 0, 0] : Shape) (adjchar.theta 3) [2, 1, 0]
    = channels.adjCount 3 [1, 0, 0] [2, 1, 0] :=
  adjCount_eq 3 [1, 0, 0] [2, 1, 0] (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : steinberg.count ([1, 0, 0] : Shape) (adjchar.theta 3) [2, 1, 0]
    = channels.adjCount 3 [1, 0, 0] [2, 1, 0] := by decide +kernel

/-! The whole row against the definitional enumeration: the
theorem's route at an occupied label, the count equation decided
there, at a second label and at a label off the row, and the
definitional side's own list value.  The width binder's frame:
off the stated width both rows are vacant. -/

example : ground.countOf ([2, 1, 0] : Shape)
      ((places.allShapes 3 (places.degree ([1, 0, 0] : Shape)
          + places.degree (adjchar.theta 3))).filterMap
        (fun c => if 0 < steinberg.count [1, 0, 0] (adjchar.theta 3) c
          then some (labels.reduce c) else none))
    = ground.countOf ([2, 1, 0] : Shape) (adjRow 3 [1, 0, 0]) :=
  adjRow_eq 3 [1, 0, 0] (by decide +kernel) (by decide +kernel) [2, 1, 0]

example : ground.countOf ([2, 1, 0] : Shape)
      ((places.allShapes 3 (places.degree ([1, 0, 0] : Shape)
          + places.degree (adjchar.theta 3))).filterMap
        (fun c => if 0 < steinberg.count [1, 0, 0] (adjchar.theta 3) c
          then some (labels.reduce c) else none))
    = ground.countOf ([2, 1, 0] : Shape) (adjRow 3 [1, 0, 0]) := by decide +kernel

example : ground.countOf ([0, 2, 0] : Shape)
      ((places.allShapes 3 (places.degree ([1, 0, 0] : Shape)
          + places.degree (adjchar.theta 3))).filterMap
        (fun c => if 0 < steinberg.count [1, 0, 0] (adjchar.theta 3) c
          then some (labels.reduce c) else none))
    = ground.countOf ([0, 2, 0] : Shape) (adjRow 3 [1, 0, 0]) := by decide +kernel

example : ground.countOf ([3, 0, 0] : Shape)
      ((places.allShapes 3 (places.degree ([1, 0, 0] : Shape)
          + places.degree (adjchar.theta 3))).filterMap
        (fun c => if 0 < steinberg.count [1, 0, 0] (adjchar.theta 3) c
          then some (labels.reduce c) else none)) = 0 := by decide +kernel

example : ground.countOf ([3, 0, 0] : Shape) (adjRow 3 [1, 0, 0]) = 0 := by
  decide +kernel

example : (places.allShapes 3 (places.degree ([1, 0, 0] : Shape)
      + places.degree (adjchar.theta 3))).filterMap
    (fun c => if 0 < steinberg.count [1, 0, 0] (adjchar.theta 3) c
      then some (labels.reduce c) else none)
    = [[2, 1, 0], [0, 2, 0], [1, 0, 0]] := by decide +kernel

example : ¬ ([1, 0] : Shape).length = 3 := by decide +kernel

example : (places.allShapes 3 (places.degree ([1, 0] : Shape)
      + places.degree (adjchar.theta 3))).filterMap
    (fun c => if 0 < steinberg.count [1, 0] (adjchar.theta 3) c
      then some (labels.reduce c) else none) = [] := by decide +kernel

example : ¬ ground.countOf ([2, 0] : Shape)
      ((places.allShapes 3 (places.degree ([1, 0] : Shape)
          + places.degree (adjchar.theta 3))).filterMap
        (fun c => if 0 < steinberg.count [1, 0] (adjchar.theta 3) c
          then some (labels.reduce c) else none))
    = ground.countOf ([2, 0] : Shape) (adjRow 3 [1, 0]) := by decide +kernel

/-! The floor binder's refusal: at the width one the definitional
row is occupied at the vacuum while the fast row is vacant. -/

example : ¬ ground.countOf ([0] : Shape)
      ((places.allShapes 1 (places.degree ([0] : Shape)
          + places.degree (adjchar.theta 1))).filterMap
        (fun c => if 0 < steinberg.count [0] (adjchar.theta 1) c
          then some (labels.reduce c) else none))
    = ground.countOf ([0] : Shape) (adjRow 1 [0]) := by decide +kernel

/-! The count agreement's width and floor refusals at their
recorded data. -/

example : ¬ steinberg.count ([1, 0] : Shape) (adjchar.theta 3)
    [1, 0, 0] = channels.adjCount 3 [1, 0] [1, 0, 0] := by decide +kernel

example : ¬ steinberg.count ([0] : Shape) (adjchar.theta 1) [2]
    = channels.adjCount 1 [0] [2] := by decide +kernel
