import MassGap.Weylchar
import MassGap.Blockcount
import MassGapChecks.Blockcount
/-!
The check module for `thm:weylchar`'s carrier: the batteries re-read
the graded counts by kernel `decide` — the strictly decreasing
display's one even count at its own key, the further keys' counts at
the permuted displays, and the repeat read's instances at a repeated
exponent, the two sides equal at every sampled key.
-/
set_option maxRecDepth 8192

open ground places weylchar

/-! The strictly decreasing display reads one even count at its own
key, the identity permutation's, the even class at `false`. -/

example : sideCount 3 [2, 1, 0] [2, 1, 0] false = 1 := by decide +kernel
example : sideCount 3 [2, 1, 0] [2, 1, 0] true = 0 := by decide +kernel

/-! A permuted key reads its permutation's side. -/

example : sideCount 3 [2, 1, 0] [1, 2, 0] true = 1 := by decide +kernel
example : sideCount 3 [2, 1, 0] [1, 2, 0] false = 0 := by decide +kernel
example : sideCount 3 [2, 1, 0] [0, 1, 2] true = 1 := by decide +kernel
example : sideCount 3 [2, 1, 0] [0, 1, 2] false = 0 := by decide +kernel

-- the fast route's reads beside the graded enumeration's: the odd
-- side at the top key and a key off the table, the coherence
-- theorem's committed refuse-side instances
example : ground.tabRead (fun k => decide (k = [2, 1, 0])) true
    (alternantTable 3 [2, 1, 0]) = 0 := by decide +kernel
example : ground.tabRead (fun k => decide (k = [9, 9, 9])) false
    (alternantTable 3 [2, 1, 0]) = 0 := by decide +kernel
example : sideCount 3 [2, 1, 0] [1, 0, 2] false = 1 := by decide +kernel
example : sideCount 3 [2, 1, 0] [3, 1, 0] true = 0 := by decide +kernel
example : sideCount 3 [2, 1, 0] [3, 1, 0] false = 0 := by decide +kernel

/-! The repeat read's instances: at a repeated exponent the two
sides' counts are equal at every key, the sampled keys' reads. -/

example : sideCount 3 [1, 1, 0] [1, 1, 0] true
    = sideCount 3 [1, 1, 0] [1, 1, 0] false := by decide +kernel
example : sideCount 3 [1, 1, 0] [1, 0, 1] true
    = sideCount 3 [1, 1, 0] [1, 0, 1] false := by decide +kernel
example : sideCount 3 [1, 1, 0] [0, 1, 1] true
    = sideCount 3 [1, 1, 0] [0, 1, 1] false := by decide +kernel
example : sideCount 4 [2, 0, 2, 1] [2, 2, 1, 0] true
    = sideCount 4 [2, 0, 2, 1] [2, 2, 1, 0] false := by decide +kernel

/-! The repeat family's value pins, the equality reads off the
vacuous class. -/

example : sideCount 3 [1, 1, 0] [1, 1, 0] true = 1 := by decide +kernel
example : sideCount 3 [1, 1, 0] [1, 1, 0] false = 1 := by decide +kernel
example : sideCount 3 [1, 1, 0] [0, 1, 1] true = 1 := by decide +kernel

/-! The theorem's own instance beside the decided values. -/

example : sideCount 3 [1, 1, 0] [1, 1, 0] true
    = sideCount 3 [1, 1, 0] [1, 1, 0] false :=
  repeat_read 3 [1, 1, 0] [1, 1, 0] (Nat.lt_succ_self 0)
    (Nat.lt_succ_of_lt (Nat.lt_succ_self 1)) rfl

/-! The keyed table, the fast route: one pass over the enumeration,
the whole alternant at the budget the per-key refolds priced out of
— the d = 5 table's 120 keys in one decide — with the coherence
read's own instance beside the decided values. -/

example : (alternantTable 4 [3, 2, 1, 0]).length = 24 := by decide +kernel
example : (alternantTable 5 [4, 3, 2, 1, 0]).length = 120 := by
  decide +kernel
example : ground.tabRead (fun k => decide (k = [2, 1, 0])) false
    (alternantTable 3 [2, 1, 0]) = 1 := by decide +kernel
example : ground.tabRead (fun k => decide (k = [1, 2, 0])) true
    (alternantTable 3 [2, 1, 0]) = 1 := by decide +kernel
example : (alternantTable 3 [1, 1, 0]).length = 3 := by decide +kernel
example : ((alternantTable 3 [1, 1, 0]).all
    (fun r => r.2.1 == r.2.2)) = true := by decide +kernel

/-! The exchange read at instances: the permuted exponent list's
counts on the exchanged sides, odd and even permutations each. -/

example : sideCount 3 (expo [2, 1, 0] [1, 0, 2]) [1, 2, 0] false
    = sideCount 3 [2, 1, 0] [1, 2, 0] true := by decide +kernel
example : sideCount 3 (expo [2, 1, 0] [1, 2, 0]) [2, 1, 0] false
    = sideCount 3 [2, 1, 0] [2, 1, 0] false := by decide +kernel
example : places.invPerm 3 [1, 2, 0] = [2, 0, 1] := by decide +kernel
example : parity (places.invPerm 3 [1, 0, 2]) = parity [1, 0, 2] := by
  decide +kernel


/-! The identity's statement tier at the definitional
multiplicity, `def:blockcount`'s span occupancy: the tie fold's
reads, the dominance walk, and the identity's read `identityAt`
decided at the top key, at permuted and interior keys, and at a
repeated key — the `d = 2` symmetric square and the `d = 3`
adjoint the instances. -/

example : tieGap [5, 3, 1] [3, 2, 1] = some [2, 1, 0] := by decide +kernel
example : tieGap [5, 3, 1] [1, 2, 3] = none := by decide +kernel

example : domBy [1, 1, 1] [2, 1, 0] := by decide +kernel
example : domBy [0, 1, 2] [2, 1, 0] := by decide +kernel
example : ¬ domBy [3, 0, 0] [2, 1, 0] := by decide +kernel
example : ¬ domBy [1, 1] [2, 1, 0] := by decide +kernel

example : blockcount.occupancyAt (blockcount.blockSpan [1, 1, 0])
    [2, 1, 0] = 1 := by
  rw [blockcount.span110_pin]; decide +kernel
example : blockcount.occupancyAt (blockcount.blockSpan [1, 1, 0])
    [1, 1, 1] = 2 := by
  rw [blockcount.span110_pin]; decide +kernel
example : blockcount.occupancyAt (blockcount.blockSpan [1, 1, 0])
    [0, 1, 2]
  = blockcount.occupancyAt (blockcount.blockSpan [1, 1, 0])
    [2, 1, 0] := by
  rw [blockcount.span110_pin]; decide +kernel

/-! The trace recursion's display at the adjoint's contents: the
zero weight, the top, the move-free dominance-maximal corner, and
the reversed content — an unoccupied content at occupied moves,
the display's string-cancellation side. -/

example : stdSq (display [1, 1, 0])
      * blockcount.occupancyAt (blockcount.blockSpan [1, 1, 0])
        [1, 1, 1]
    + 2 * movedSnd (fun nu => blockcount.occupancyAt
        (blockcount.blockSpan [1, 1, 0]) nu) [1, 1, 1]
  = stdSq (List.zipWith (fun a b => a + b) [1, 1, 1] (unitDisp 3))
      * blockcount.occupancyAt (blockcount.blockSpan [1, 1, 0])
        [1, 1, 1]
    + 2 * movedFst (fun nu => blockcount.occupancyAt
        (blockcount.blockSpan [1, 1, 0]) nu) [1, 1, 1] := by
  rw [blockcount.span110_pin]; decide +kernel

example : stdSq (display [1, 1, 0])
      * blockcount.occupancyAt (blockcount.blockSpan [1, 1, 0])
        [2, 1, 0]
    + 2 * movedSnd (fun nu => blockcount.occupancyAt
        (blockcount.blockSpan [1, 1, 0]) nu) [2, 1, 0]
  = stdSq (List.zipWith (fun a b => a + b) [2, 1, 0] (unitDisp 3))
      * blockcount.occupancyAt (blockcount.blockSpan [1, 1, 0])
        [2, 1, 0]
    + 2 * movedFst (fun nu => blockcount.occupancyAt
        (blockcount.blockSpan [1, 1, 0]) nu) [2, 1, 0] := by
  rw [blockcount.span110_pin]; decide +kernel

example : stdSq (display [1, 1, 0])
      * blockcount.occupancyAt (blockcount.blockSpan [1, 1, 0])
        [3, 0, 0]
    + 2 * movedSnd (fun nu => blockcount.occupancyAt
        (blockcount.blockSpan [1, 1, 0]) nu) [3, 0, 0]
  = stdSq (List.zipWith (fun a b => a + b) [3, 0, 0] (unitDisp 3))
      * blockcount.occupancyAt (blockcount.blockSpan [1, 1, 0])
        [3, 0, 0]
    + 2 * movedFst (fun nu => blockcount.occupancyAt
        (blockcount.blockSpan [1, 1, 0]) nu) [3, 0, 0] := by
  rw [blockcount.span110_pin]; decide +kernel

example : stdSq (display [1, 1, 0])
      * blockcount.occupancyAt (blockcount.blockSpan [1, 1, 0])
        [0, 0, 3]
    + 2 * movedSnd (fun nu => blockcount.occupancyAt
        (blockcount.blockSpan [1, 1, 0]) nu) [0, 0, 3]
  = stdSq (List.zipWith (fun a b => a + b) [0, 0, 3] (unitDisp 3))
      * blockcount.occupancyAt (blockcount.blockSpan [1, 1, 0])
        [0, 0, 3]
    + 2 * movedFst (fun nu => blockcount.occupancyAt
        (blockcount.blockSpan [1, 1, 0]) nu) [0, 0, 3] := by
  rw [blockcount.span110_pin]; decide +kernel

example : movedSnd (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) [0, 0, 3] = 12 := by
  rw [blockcount.span110_pin]; decide +kernel

/-! The identity's read at the symmetric square and the adjoint:
the top key, permuted keys, an interior key at the eigen
vanishing, a repeated key, and an off-degree key. -/

example : identityAt (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [2, 0]) nu) [2, 0] [4, 1] := by decide +kernel
example : identityAt (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [2, 0]) nu) [2, 0] [3, 2] := by decide +kernel
example : identityAt (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [2, 0]) nu) [2, 0] [1, 4] := by decide +kernel
example : identityAt (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [2, 0]) nu) [2, 0] [5, 1] := by decide +kernel

example : identityAt (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) [1, 1, 0]
    [5, 3, 1] := by
  rw [blockcount.span110_pin]; decide +kernel
example : identityAt (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) [1, 1, 0]
    [3, 5, 1] := by
  rw [blockcount.span110_pin]; decide +kernel
example : identityAt (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) [1, 1, 0]
    [4, 3, 2] := by
  rw [blockcount.span110_pin]; decide +kernel
example : identityAt (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) [1, 1, 0]
    [3, 3, 3] := by
  rw [blockcount.span110_pin]; decide +kernel

/-! The separation's decided instance beside the theorem. -/

example : stdSq (List.zipWith (fun l u => l + u) [1, 1, 1]
    (unitDisp 3)) < stdSq (display [1, 1, 0]) := by decide +kernel

/-! The top coefficient's decided instances beside the theorem:
the product's coefficient at the top key, one on the even side and
the count's unit on the odd, at both committed blocks. -/

example : prodCount (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [2, 0]) nu) 2 (display [2, 0])
    false = 1 := by decide +kernel
example : prodCount (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [2, 0]) nu) 2 (display [2, 0])
    true = 0 := by decide +kernel
example : prodCount (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) 3 (display [1, 1, 0])
    false = 1 := by
  rw [blockcount.span110_pin]; decide +kernel
example : prodCount (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) 3 (display [1, 1, 0])
    true = 0 := by
  rw [blockcount.span110_pin]; decide +kernel

/-! The eigen-read's statement tier: `eigenAt` decided at the
committed blocks' keys — the vanishing interior key, the top, a
repeated key at equal members, and an off-degree key — with the
telescope's per-key read `stepRead` pinned at decided instances
beside the theorem. -/

example : eigenAt (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) [1, 1, 0]
    [4, 3, 2] := by
  rw [blockcount.span110_pin]; decide +kernel
example : eigenAt (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) [1, 1, 0]
    [5, 3, 1] := by
  rw [blockcount.span110_pin]; decide +kernel
example : eigenAt (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) [1, 1, 0]
    [3, 3, 3] := by
  rw [blockcount.span110_pin]; decide +kernel
example : eigenAt (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) [1, 1, 0]
    [5, 3, 2] := by
  rw [blockcount.span110_pin]; decide +kernel
example : eigenAt (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [2, 0]) nu) [2, 0] [3, 2] := by decide +kernel
example : eigenAt (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [2, 0]) nu) [2, 0] [4, 1] := by decide +kernel

example : gFst (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) [1, 0, 2] 0 2
      + gSnd (fun nu => blockcount.occupancyAt
        (blockcount.blockSpan [1, 1, 0]) nu) [2, 0, 1] 0 2
      + 1 * blockcount.occupancyAt (blockcount.blockSpan [1, 1, 0])
        [2, 0, 1]
    = gFst (fun nu => blockcount.occupancyAt
        (blockcount.blockSpan [1, 1, 0]) nu) [2, 0, 1] 0 2
      + gSnd (fun nu => blockcount.occupancyAt
        (blockcount.blockSpan [1, 1, 0]) nu) [1, 0, 2] 0 2
      + (1 + 1) * blockcount.occupancyAt
        (blockcount.blockSpan [1, 1, 0]) [2, 0, 1] := by
  rw [blockcount.span110_pin]; decide +kernel

example : gFst (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) [1, 0, 2] 0 2
      + gSnd (fun nu => blockcount.occupancyAt
        (blockcount.blockSpan [1, 1, 0]) nu) [2, 0, 1] 0 2
      + 1 * blockcount.occupancyAt (blockcount.blockSpan [1, 1, 0])
        [2, 0, 1]
    = gFst (fun nu => blockcount.occupancyAt
        (blockcount.blockSpan [1, 1, 0]) nu) [2, 0, 1] 0 2
      + gSnd (fun nu => blockcount.occupancyAt
        (blockcount.blockSpan [1, 1, 0]) nu) [1, 0, 2] 0 2
      + (1 + 1) * blockcount.occupancyAt
        (blockcount.blockSpan [1, 1, 0]) [2, 0, 1] :=
  stepRead (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) [1, 0, 1]
    (Nat.lt_succ_of_lt (Nat.lt_succ_self 0))
    (Nat.lt_succ_self 2)

/-! The boundary read at the adjoint's occupancy: at a key reading
the first letter at the count's unit the moved weights collect to
the second exponent's count, the one-sided string's palindrome —
decided at both letter pairs off the first letter — with a
committed refusal at a first letter reading beyond the unit,
scoping the clause, and the theorem's own instance beside its
decided value at the constant multiplicity. -/

example : gFst (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) [0, 1, 2] 0 1
    = ground.getAt 0 [0, 1, 2] 1
        * blockcount.occupancyAt (blockcount.blockSpan [1, 1, 0])
          [0, 1, 2]
      + gSnd (fun nu => blockcount.occupancyAt
          (blockcount.blockSpan [1, 1, 0]) nu) [0, 1, 2] 0 1 := by
  rw [blockcount.span110_pin]; decide +kernel

example : gFst (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) [0, 1, 2] 0 2
    = ground.getAt 0 [0, 1, 2] 2
        * blockcount.occupancyAt (blockcount.blockSpan [1, 1, 0])
          [0, 1, 2]
      + gSnd (fun nu => blockcount.occupancyAt
          (blockcount.blockSpan [1, 1, 0]) nu) [0, 1, 2] 0 2 := by
  rw [blockcount.span110_pin]; decide +kernel

example : ¬ (gFst (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) [1, 2, 0] 0 1
    = ground.getAt 0 [1, 2, 0] 1
        * blockcount.occupancyAt (blockcount.blockSpan [1, 1, 0])
          [1, 2, 0]
      + gSnd (fun nu => blockcount.occupancyAt
          (blockcount.blockSpan [1, 1, 0]) nu) [1, 2, 0] 0 1) := by
  rw [blockcount.span110_pin]; decide +kernel

example : gFst (fun _ => 1) [0, 2, 1] 0 1 = 6 := by decide +kernel

example : gFst (fun _ => 1) [0, 2, 1] 0 1
    = ground.getAt 0 [0, 2, 1] 1 * 1
      + gSnd (fun _ => 1) [0, 2, 1] 0 1 :=
  boundaryRead (fun _ => 1) [0, 2, 1] (Nat.lt_succ_self 0)
    (Nat.lt_succ_of_lt (Nat.lt_succ_self 1))
    (fun _ _ _ _ _ _ => rfl) rfl

/-! The cofactor tier: the guarded reads at a key against a moved
display, the per-key telescope `stepAt`, and the cleared telescope
at the cofactor `cofRead` — decided at the adjoint's occupancy at
the interior key, the theorems' own instances beside the decided
values at the constant multiplicity. -/

example : dAtGap (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) 0 [4, 3, 2] [2, 3, 1]
    = 2 := by
  rw [blockcount.span110_pin]; decide +kernel
example : dAtGap (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) 1 [4, 3, 2] [2, 3, 1]
    = 0 := by
  rw [blockcount.span110_pin]; decide +kernel
example : gAtGap (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) 0 1 [4, 3, 2] [3, 2, 1]
    true = 1 := by
  rw [blockcount.span110_pin]; decide +kernel
example : gAtGap (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) 0 1 [4, 3, 2] [3, 2, 1]
    false = 3 := by
  rw [blockcount.span110_pin]; decide +kernel
example : gAtGap (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) 0 1 [4, 3, 2] [9, 9, 9]
    false = 0 := by
  rw [blockcount.span110_pin]; decide +kernel

example : dAtGap (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 0 [4, 3, 2] [2, 3, 1]
    + gAtGap (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 0 1 [4, 3, 2]
      (moveBy 0 1 1 [2, 3, 1]) true
    + gAtGap (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 0 1 [4, 3, 2]
      [2, 3, 1] false
  = dAtGap (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 1 [4, 3, 2] [2, 3, 1]
    + gAtGap (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 0 1 [4, 3, 2]
      (moveBy 0 1 1 [2, 3, 1]) false
    + gAtGap (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 0 1 [4, 3, 2]
      [2, 3, 1] true := by
  rw [blockcount.span110_pin]; decide +kernel

example : dAtGap (fun _ => 1) 0 [4, 3, 2] [2, 3, 1]
    + gAtGap (fun _ => 1) 0 1 [4, 3, 2]
      (moveBy 0 1 1 [2, 3, 1]) true
    + gAtGap (fun _ => 1) 0 1 [4, 3, 2] [2, 3, 1] false
  = dAtGap (fun _ => 1) 1 [4, 3, 2] [2, 3, 1]
    + gAtGap (fun _ => 1) 0 1 [4, 3, 2]
      (moveBy 0 1 1 [2, 3, 1]) false
    + gAtGap (fun _ => 1) 0 1 [4, 3, 2] [2, 3, 1] true :=
  stepAt (fun _ => 1) (Nat.lt_succ_self 0) [4, 3, 2] [2, 3, 1]
    (by decide +kernel) (by decide +kernel) rfl (fun _ _ _ _ _ _ => rfl)

example : ground.famFold Nat.add 0
      (fun k => dAtGap (fun nu => blockcount.occupancyAt
        (blockcount.blockSpan [1, 1, 0]) nu) 0 [4, 3, 2]
        (moveBy 1 0 k [3, 2, 1]))
      ((List.range 3).map (fun k => k + 1))
    + gAtGap (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 0 1 [4, 3, 2]
      [3, 2, 1] true
    + gAtGap (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 0 1 [4, 3, 2]
      (moveBy 1 0 3 [3, 2, 1]) false
  = ground.famFold Nat.add 0
      (fun k => dAtGap (fun nu => blockcount.occupancyAt
        (blockcount.blockSpan [1, 1, 0]) nu) 1 [4, 3, 2]
        (moveBy 1 0 k [3, 2, 1]))
      ((List.range 3).map (fun k => k + 1))
    + gAtGap (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 0 1 [4, 3, 2]
      [3, 2, 1] false
    + gAtGap (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 0 1 [4, 3, 2]
      (moveBy 1 0 3 [3, 2, 1]) true := by
  rw [blockcount.span110_pin]; decide +kernel

example : ground.famFold Nat.add 0
      (fun k => dAtGap (fun _ => 1) 0 [4, 3, 2]
        (moveBy 1 0 k [3, 2, 1]))
      ((List.range (ground.getAt 0 [3, 2, 1] 0)).map
        (fun k => k + 1))
    + gAtGap (fun _ => 1) 0 1 [4, 3, 2] [3, 2, 1] true
    + gAtGap (fun _ => 1) 0 1 [4, 3, 2]
      (moveBy 1 0 (ground.getAt 0 [3, 2, 1] 0) [3, 2, 1]) false
  = ground.famFold Nat.add 0
      (fun k => dAtGap (fun _ => 1) 1 [4, 3, 2]
        (moveBy 1 0 k [3, 2, 1]))
      ((List.range (ground.getAt 0 [3, 2, 1] 0)).map
        (fun k => k + 1))
    + gAtGap (fun _ => 1) 0 1 [4, 3, 2] [3, 2, 1] false
    + gAtGap (fun _ => 1) 0 1 [4, 3, 2]
      (moveBy 1 0 (ground.getAt 0 [3, 2, 1] 0) [3, 2, 1]) true :=
  cofRead (fun _ => 1) (Nat.lt_succ_self 0) [4, 3, 2] [3, 2, 1]
    (by decide +kernel) rfl (fun _ _ _ _ _ _ => rfl)

/-! The telescope's boundary branch at decided instances: an
occupied tie reading the first letter at the count's unit — the
`boundaryRead`-consuming arm of `stepAt` — at the `d = 3` adjoint,
and the boundary read at `d = 4` at a further letter pair on the
standard square's multiplicity, symmetric and cheap — the `d = 4`
span occupancies priced out by the module budget, their content
pinned at the `d = 3` adjoint. -/

example : dAtGap (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 0 [1, 3, 2] [1, 1, 1]
    + gAtGap (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 0 1 [1, 3, 2]
      (moveBy 0 1 1 [1, 1, 1]) true
    + gAtGap (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 0 1 [1, 3, 2]
      [1, 1, 1] false
  = dAtGap (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 1 [1, 3, 2] [1, 1, 1]
    + gAtGap (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 0 1 [1, 3, 2]
      (moveBy 0 1 1 [1, 1, 1]) false
    + gAtGap (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 0 1 [1, 3, 2]
      [1, 1, 1] true := by
  rw [blockcount.span110_pin]; decide +kernel

example : gFst (fun nu => stdSq nu) [2, 0, 1, 2] 1 3
    = ground.getAt 0 [2, 0, 1, 2] 3 * stdSq [2, 0, 1, 2]
      + gSnd (fun nu => stdSq nu) [2, 0, 1, 2] 1 3 := by decide +kernel

example : gFst (fun nu => stdSq nu) [2, 0, 1, 2] 1 3 = 50 := by
  decide +kernel

/-! The perm-fold assembly's first display: the product's graded
coefficient against the telescope family reads the cofactor's
shift fold at every key — decided at the adjoint occupancy's
interior key with the theorem's own instance at the constant
multiplicity beside the decided values. -/

example : prodG (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) 0 1 3 [4, 3, 2] false
    = 5 := by
  rw [blockcount.span110_pin]; decide +kernel
example : prodG (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) 0 1 3 [4, 3, 2] true
    = 4 := by
  rw [blockcount.span110_pin]; decide +kernel
example : cofFold (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) 0 1 3 [4, 3, 2] false
    = 3 := by
  rw [blockcount.span110_pin]; decide +kernel
example : cofFold (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) 0 1 3 [4, 3, 2] true
    = 2 := by
  rw [blockcount.span110_pin]; decide +kernel

example : prodG (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 0 1 3 [4, 3, 2] false
    + cofFold (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 0 1 3 [4, 3, 2] true
  = prodG (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 0 1 3 [4, 3, 2] true
    + cofFold (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 0 1 3 [4, 3, 2]
      false := by
  rw [blockcount.span110_pin]; decide +kernel

example : prodG (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 0 2 3 [5, 3, 1] false
    + cofFold (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 0 2 3 [5, 3, 1] true
  = prodG (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 0 2 3 [5, 3, 1] true
    + cofFold (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 0 2 3 [5, 3, 1]
      false := by
  rw [blockcount.span110_pin]; decide +kernel

example : prodG (fun _ => 1) 0 1 3 [4, 3, 2] false
      + cofFold (fun _ => 1) 0 1 3 [4, 3, 2] true
    = prodG (fun _ => 1) 0 1 3 [4, 3, 2] true
      + cofFold (fun _ => 1) 0 1 3 [4, 3, 2] false :=
  cofProd (fun _ => 1) (Nat.lt_succ_self 0)
    (Nat.lt_succ_of_lt (Nat.lt_succ_self 1)) [4, 3, 2] rfl
    (fun _ _ _ _ _ _ => rfl)

/-! The cofactor's coefficient as data: the division's
back-substitution pinned against the product form's own reads —
`e·Q_01 = x_0x_1x_2 (x_0x_1 - x_0x_2 - x_1x_2 + x_2^2)` at `d = 3`,
one graded unit per occupied key, the off keys at the count's
unit. -/

example : cofAt 0 1 3 [2, 2, 1] false = 1 := by decide +kernel
example : cofAt 0 1 3 [2, 2, 1] true = 0 := by decide +kernel
example : cofAt 0 1 3 [2, 1, 2] true = 1 := by decide +kernel
example : cofAt 0 1 3 [1, 2, 2] true = 1 := by decide +kernel
example : cofAt 0 1 3 [1, 1, 3] false = 1 := by decide +kernel
example : cofAt 0 1 3 [1, 1, 1] false = 0 := by decide +kernel
example : cofAt 0 1 3 [1, 1, 1] true = 0 := by decide +kernel

/-! The interior first letter: the descent and the display at the
pair off letter one, `e·Q_12 = x_0x_1x_2 (x_0^2 - x_0x_1 - x_0x_2
+ x_1x_2)`'s four keys with the summed display decided. -/

example : cofAt 1 2 3 [3, 1, 1] false = 1 := by decide +kernel
example : cofAt 1 2 3 [2, 1, 2] true = 1 := by decide +kernel
example : cofAt 1 2 3 [2, 2, 1] true = 1 := by decide +kernel
example : cofAt 1 2 3 [1, 2, 2] false = 1 := by decide +kernel

example : prodG (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 1 2 3 [4, 3, 2] false
    + cofFold (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 1 2 3 [4, 3, 2] true
  = prodG (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 1 2 3 [4, 3, 2] true
    + cofFold (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 1 2 3 [4, 3, 2]
      false := by
  rw [blockcount.span110_pin]; decide +kernel

/-! The product-rule read's display detection: the arrangement
test, the complement permutation, and the graded counts' one unit
at an arrangement's own permutation — with the theorem's own
instance beside the decided values. -/

example : arrB 3 [2, 3, 1] = true := by decide +kernel
example : arrB 3 [2, 2, 1] = false := by decide +kernel
example : arrB 3 [4, 2, 1] = false := by decide +kernel
example : permOf 3 [2, 3, 1] = [1, 0, 2] := by decide +kernel
example : parity (permOf 3 [2, 3, 1]) = true := by decide +kernel
example : sideCount 3 (unitDisp 3) [2, 3, 1] true = 1 := by decide +kernel
example : sideCount 3 (unitDisp 3) [2, 3, 1] false = 0 := by decide +kernel
example : sideCount 3 (unitDisp 3) [2, 3, 1] true
    = if true = parity (permOf 3 [2, 3, 1]) then 1 else 0 :=
  sideCount_arr (by decide +kernel) true
example : sideCount 3 (unitDisp 3) [2, 2, 1] false = 0 :=
  sideCount_off (by decide +kernel) false

/-! The value's places split at an arrangement: the letter's value
with its rising comparisons joins the count with the falling
comparisons, decided beside the theorem's own instance. -/

example : upFold 1 3 [2, 3, 1] = 0 := by decide +kernel
example : downFold 1 3 [2, 3, 1] = 1 := by decide +kernel
example : 1 + (ground.getAt 0 [2, 3, 1] 1 + upFold 1 3 [2, 3, 1])
    = 3 + downFold 1 3 [2, 3, 1] := by decide +kernel
example : 1 + (ground.getAt 0 [2, 3, 1] 1 + upFold 1 3 [2, 3, 1])
    = 3 + downFold 1 3 [2, 3, 1] :=
  placesSplit (Nat.lt_succ_of_lt (Nat.lt_succ_self 1)) (by decide +kernel)

/-! The cofactor fold at the letter: the pairs beyond the letter
at the stated side, the pairs below it at the members exchanged —
decided at display keys on both sides of the letter and at the
`d = 4` off-display key whose one-sided hits pair across the
letter, the three-cycle partner at the kept grading. -/

example : cofSum 0 3 [2, 2, 1] false = 2 := by decide +kernel
example : cofSum 0 3 [2, 2, 1] true = 0 := by decide +kernel
example : cofSum 0 3 [1, 3, 1] false = 1 := by decide +kernel
example : cofSum 0 3 [1, 3, 1] true = 2 := by decide +kernel
example : cofSum 1 3 [3, 1, 1] false = 1 := by decide +kernel
example : cofSum 1 3 [3, 1, 1] true = 0 := by decide +kernel
example : arrB 4 [3, 2, 3, 2] = false := by decide +kernel
example : cofSum 1 4 [3, 1, 3, 2] false = 1 := by decide +kernel
example : cofSum 1 4 [3, 1, 3, 2] true = 1 := by decide +kernel

/-! The same-side pairing's instance: at the off-display key
`(2, 2, 2)` both further letters hold one-sided hits partnering
each other on the letter's own side, the places' transposition at
the exchanged grading. -/

example : arrB 3 (ground.bumpAt 0 [1, 2, 2]) = false := by decide +kernel
example : cofSum 0 3 [1, 2, 2] false = 1 := by decide +kernel
example : cofSum 0 3 [1, 2, 2] true = 1 := by decide +kernel

/-! The product-rule read: the crossed equation decided at the
display keys, at the even and odd displays, and at both
off-display pairing shapes — the same-side transposition and the
cross-boundary exchange — with the theorem's own instances beside
the decided values. -/

example : ground.getAt 0 (ground.bumpAt 0 [1, 2, 2]) 0
      * sideCount 3 (unitDisp 3) (ground.bumpAt 0 [1, 2, 2]) false
    + sideCount 3 (unitDisp 3) (ground.bumpAt 0 [1, 2, 2]) true
    + cofSum 0 3 [1, 2, 2] true
  = ground.getAt 0 (ground.bumpAt 0 [1, 2, 2]) 0
      * sideCount 3 (unitDisp 3) (ground.bumpAt 0 [1, 2, 2]) true
    + sideCount 3 (unitDisp 3) (ground.bumpAt 0 [1, 2, 2]) false
    + cofSum 0 3 [1, 2, 2] false := by decide +kernel

example : ground.getAt 0 (ground.bumpAt 0 [1, 2, 2]) 0
      * sideCount 3 (unitDisp 3) (ground.bumpAt 0 [1, 2, 2]) false
    + sideCount 3 (unitDisp 3) (ground.bumpAt 0 [1, 2, 2]) true
    + cofSum 0 3 [1, 2, 2] true
  = ground.getAt 0 (ground.bumpAt 0 [1, 2, 2]) 0
      * sideCount 3 (unitDisp 3) (ground.bumpAt 0 [1, 2, 2]) true
    + sideCount 3 (unitDisp 3) (ground.bumpAt 0 [1, 2, 2]) false
    + cofSum 0 3 [1, 2, 2] false :=
  prodRule 0 3 (Nat.succ_pos 2) [1, 2, 2] rfl false

example : ground.getAt 0 (ground.bumpAt 0 [1, 3, 1]) 0
      * sideCount 3 (unitDisp 3) (ground.bumpAt 0 [1, 3, 1]) false
    + sideCount 3 (unitDisp 3) (ground.bumpAt 0 [1, 3, 1]) true
    + cofSum 0 3 [1, 3, 1] true
  = ground.getAt 0 (ground.bumpAt 0 [1, 3, 1]) 0
      * sideCount 3 (unitDisp 3) (ground.bumpAt 0 [1, 3, 1]) true
    + sideCount 3 (unitDisp 3) (ground.bumpAt 0 [1, 3, 1]) false
    + cofSum 0 3 [1, 3, 1] false := by decide +kernel

example : ground.getAt 0 (ground.bumpAt 1 [3, 1, 3, 2]) 1
      * sideCount 4 (unitDisp 4) (ground.bumpAt 1 [3, 1, 3, 2])
        false
    + sideCount 4 (unitDisp 4) (ground.bumpAt 1 [3, 1, 3, 2]) true
    + cofSum 1 4 [3, 1, 3, 2] true
  = ground.getAt 0 (ground.bumpAt 1 [3, 1, 3, 2]) 1
      * sideCount 4 (unitDisp 4) (ground.bumpAt 1 [3, 1, 3, 2])
        true
    + sideCount 4 (unitDisp 4) (ground.bumpAt 1 [3, 1, 3, 2])
      false
    + cofSum 1 4 [3, 1, 3, 2] false := by decide +kernel

example : ground.getAt 0 (ground.bumpAt 0 [2, 2, 1]) 0
      * sideCount 3 (unitDisp 3) (ground.bumpAt 0 [2, 2, 1]) false
    + sideCount 3 (unitDisp 3) (ground.bumpAt 0 [2, 2, 1]) true
    + cofSum 0 3 [2, 2, 1] true
  = ground.getAt 0 (ground.bumpAt 0 [2, 2, 1]) 0
      * sideCount 3 (unitDisp 3) (ground.bumpAt 0 [2, 2, 1]) true
    + sideCount 3 (unitDisp 3) (ground.bumpAt 0 [2, 2, 1]) false
    + cofSum 0 3 [2, 2, 1] false :=
  prodRule 0 3 (Nat.succ_pos 2) [2, 2, 1] rfl false

example : ground.getAt 0 (ground.bumpAt 1 [3, 1, 3, 2]) 1
      * sideCount 4 (unitDisp 4) (ground.bumpAt 1 [3, 1, 3, 2])
        false
    + sideCount 4 (unitDisp 4) (ground.bumpAt 1 [3, 1, 3, 2]) true
    + cofSum 1 4 [3, 1, 3, 2] true
  = ground.getAt 0 (ground.bumpAt 1 [3, 1, 3, 2]) 1
      * sideCount 4 (unitDisp 4) (ground.bumpAt 1 [3, 1, 3, 2])
        true
    + sideCount 4 (unitDisp 4) (ground.bumpAt 1 [3, 1, 3, 2])
      false
    + cofSum 1 4 [3, 1, 3, 2] false :=
  prodRule 1 4 (Nat.lt_succ_of_lt (Nat.lt_succ_of_lt
    (Nat.lt_succ_self 1))) [3, 1, 3, 2] rfl false

/-! The committed refusal: the swapped cofactor's memberwise
exchange is load-bearing — the crossed equation at the fold with
the pairs below the letter read at the stated side rather than the
exchanged members refuses. -/

example : ¬ (ground.getAt 0 (ground.bumpAt 1 [1, 1, 3]) 1
      * sideCount 3 (unitDisp 3) (ground.bumpAt 1 [1, 1, 3]) false
    + sideCount 3 (unitDisp 3) (ground.bumpAt 1 [1, 1, 3]) true
    + (cofAt 0 1 3 [1, 1, 3] true + cofAt 1 2 3 [1, 1, 3] true)
  = ground.getAt 0 (ground.bumpAt 1 [1, 1, 3]) 1
      * sideCount 3 (unitDisp 3) (ground.bumpAt 1 [1, 1, 3]) true
    + sideCount 3 (unitDisp 3) (ground.bumpAt 1 [1, 1, 3]) false
    + (cofAt 0 1 3 [1, 1, 3] false
      + cofAt 1 2 3 [1, 1, 3] false)) := by decide +kernel

/-! The display-1 reorganization per pair: the pair-weighted
cofactor fold against the product's `G`-read and Euler read —
value pins at the adjoint occupancy's interior key, the crossed
equation decided there at the interior letter pair, the pair off
the `G`-read's support at the constant multiplicity, and the
theorem's own instance beside the decided values. -/

example : cofDFold (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) 0 1 3 [4, 3, 2] false
    = 5 := by
  rw [blockcount.span110_pin]; decide +kernel
example : cofDFold (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) 0 1 3 [4, 3, 2] true
    = 5 := by
  rw [blockcount.span110_pin]; decide +kernel
example : prodD (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) 0 3 [4, 3, 2] false
    = 2 := by
  rw [blockcount.span110_pin]; decide +kernel
example : prodD (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) 0 3 [4, 3, 2] true
    = 3 := by
  rw [blockcount.span110_pin]; decide +kernel

example : cofDFold (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 1 2 3 [4, 3, 2] false
    + prodG (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 1 2 3 [4, 3, 2] true
    + prodD (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 1 3 [4, 3, 2] true
  = cofDFold (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 1 2 3 [4, 3, 2] true
    + prodG (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 1 2 3 [4, 3, 2] false
    + prodD (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu) 1 3 [4, 3, 2]
      false := by
  rw [blockcount.span110_pin]; decide +kernel

example : cofDFold (fun _ => 1) 0 2 3 [5, 3, 1] false = 2 := by
  decide +kernel
example : cofDFold (fun _ => 1) 0 2 3 [5, 3, 1] true = 3 := by
  decide +kernel
example : prodG (fun _ => 1) 0 2 3 [5, 3, 1] false = 0 := by
  decide +kernel
example : prodG (fun _ => 1) 0 2 3 [5, 3, 1] true = 0 := by
  decide +kernel
example : prodD (fun _ => 1) 0 3 [5, 3, 1] false = 2 := by decide +kernel
example : prodD (fun _ => 1) 0 3 [5, 3, 1] true = 3 := by decide +kernel

example : cofDFold (fun _ => 1) 0 1 3 [4, 3, 2] false
      + prodG (fun _ => 1) 0 1 3 [4, 3, 2] true
      + prodD (fun _ => 1) 0 3 [4, 3, 2] true
    = cofDFold (fun _ => 1) 0 1 3 [4, 3, 2] true
      + prodG (fun _ => 1) 0 1 3 [4, 3, 2] false
      + prodD (fun _ => 1) 0 3 [4, 3, 2] false :=
  cofDProd (fun _ => 1) (Nat.lt_succ_self 0)
    (Nat.lt_succ_of_lt (Nat.lt_succ_self 1)) [4, 3, 2] rfl
    (fun _ _ _ _ _ _ => rfl)

example : cofDFold (fun _ => 1) 0 1 3 [4, 3, 2] false = 7 := by
  decide +kernel
example : cofDFold (fun _ => 1) 0 1 3 [4, 3, 2] true = 8 := by
  decide +kernel
example : prodD (fun _ => 1) 0 3 [4, 3, 2] false = 4 := by decide +kernel
example : prodD (fun _ => 1) 0 3 [4, 3, 2] true = 3 := by decide +kernel

/-! The eigen-read's closure: the committed refusals — a
symmetric multiplicity off the trace recursion, the one-key
concentration, breaks the eigen equation at a stated key, and a
recursion-keeping multiplicity off the symmetry, the one-key
concentration whose moves sit unoccupied with the letter raise
blocking every move onto it, breaks the equation at its own key —
each of `eigenRead`'s two hypotheses the load-bearing one at its
refusal — and the off-length keys read the count's unit on both
sides through the tie's refusal, the shorter and the longer key
each decided at the adjoint's occupancy. -/

example : ¬ eigenAt (fun nu => if nu = [0, 0] then 1 else 0)
    [1, 0] [1, 2] := by decide +kernel
example : ¬ eigenAt (fun nu => if nu = [0, 2] then 1 else 0)
    [0, 1] [1, 4] := by decide +kernel

example : eigenAt (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) [1, 1, 0]
    [2, 1] := by
  rw [blockcount.span110_pin]; decide +kernel
example : eigenAt (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) [1, 1, 0]
    [4, 3, 2, 1] := by
  rw [blockcount.span110_pin]; decide +kernel

/-! The conclusion's closure: the committed refusals — each of
`identityRead`'s four hypothesis displays the load-bearing one at
its own refusal.  The recursion: the occupancy bumped at the
interior content keeps the symmetry, the support and the top and
breaks at a stated key.  The symmetry: the occupancy joined by
the recursion's non-symmetric degree-three solution keeps the
recursion with the support and the top and breaks at an unsorted
key alone, the walk's own branch.  The support: at the shared
display square the occupancy joined by the further block's own
table — its recursion riding the one square — keeps the
recursion with the symmetry and the top and breaks at the
further display, the degenerate-square carrier (at a shape off the degeneracy the
recursion with the symmetry and the top force the occupancy
outright, so the support's refusal lives at the shared squares
alone).  The top: the doubled table breaks at the display itself
with every further clause kept.  Beside them the fully ascending
key decided at the genuine occupancy, the walk's longest
transport, and the shared-square key at the genuine occupancy,
the equal-squares branch's read with both product sides the
count's unit. -/

example : ¬ identityAt (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu
      + (if nu = [1, 1, 1] then 1 else 0))
    [1, 1, 0] [4, 3, 2] := by
  rw [blockcount.span110_pin]; decide +kernel

example : ¬ identityAt (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu
      + (if nu = [0, 0, 3] then 1 else if nu = [0, 1, 2] then 1
        else if nu = [0, 2, 1] then 1
        else if nu = [0, 3, 0] then 1 else 0))
    [1, 1, 0] [1, 2, 6] := by
  rw [blockcount.span110_pin]; decide +kernel

example : ¬ identityAt (fun nu => blockcount.occupancyAt
      (blockcount.blockSpan [6, 0]) nu
      + (if nu = [5, 3] then 1 else if nu = [4, 4] then 1
        else if nu = [3, 5] then 1 else 0))
    [6, 0] [7, 4] := by
  rw [blockcount.span60_pin]; decide +kernel

example : ¬ identityAt (fun nu => 2 * blockcount.occupancyAt
      (blockcount.blockSpan [1, 1, 0]) nu)
    [1, 1, 0] [5, 3, 1] := by
  rw [blockcount.span110_pin]; decide +kernel

example : identityAt (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [1, 1, 0]) nu) [1, 1, 0]
    [1, 3, 5] := by
  rw [blockcount.span110_pin]; decide +kernel

example : identityAt (fun nu => blockcount.occupancyAt
    (blockcount.blockSpan [6, 0]) nu) [6, 0]
    [7, 4] := by
  rw [blockcount.span60_pin]; decide +kernel

/-! The dominance antisymmetry: the two-directions read at a
distinct pair refuses one way, and the theorem route identifies
at both walks. -/

example : ([1, 1, 1] : List Nat) = [1, 1, 1] :=
  weylchar.domBy_antisymm [1, 1, 1] [1, 1, 1] (by decide +kernel) (by decide +kernel)
example : weylchar.domBy [1, 1, 1] [2, 1, 0] := by decide +kernel
example : ¬ weylchar.domBy [2, 1, 0] [1, 1, 1] := by decide +kernel

/-! The dominance order's flip at the reversals: a walk's pair
reads again with the two lists exchanged and each reversed, the
theorem applied there, and the walk binder isolated at a pair off
the order whose flipped read refuses with it. -/

example : weylchar.domBy [0, 2] [1, 1] := by decide +kernel
example : weylchar.domBy [1, 1] [2, 0] := by decide +kernel
example : weylchar.domBy [1, 1] [2, 0] :=
  weylchar.domBy_reverse [0, 2] [1, 1] (by decide +kernel)

/-- Refusal isolating `h`: off the order the walk refuses, and the
flipped read refuses with it.  The two-letter pair is its own flip
(`[1, 0]`, `[0, 1]` exchange to themselves), so the three-letter
pair carries the refusal at a flipped read distinct from the
walk's. -/
example : ¬ weylchar.domBy [1, 0] [0, 1] := by decide +kernel
example : ¬ weylchar.domBy (([0, 1] : List Nat).reverse)
    (([1, 0] : List Nat).reverse) := by decide +kernel
example : ¬ weylchar.domBy [2, 0, 0] [1, 1, 1] := by decide +kernel
example : ¬ weylchar.domBy [1, 1, 1] [0, 0, 2] := by decide +kernel
example : ¬ weylchar.domBy (([1, 1, 1] : List Nat).reverse)
    (([2, 0, 0] : List Nat).reverse) := by decide +kernel

/-! The occupied tie multiplicity names its tie: the read decided
at an instance, and the theorem applied there — the existential
consumed as the application's own conclusion. -/

example : 0 < weylchar.multAtGap (fun m => ground.countOf 1 m)
    [3, 2] [2, 2] := by decide +kernel

example : ∃ m, ground.tieGap [3, 2] [2, 2] = some m
    ∧ 0 < ground.countOf 1 m :=
  weylchar.multAtGap_pos (fun m => ground.countOf 1 m) [3, 2] [2, 2]
    (by decide +kernel)
