import MassGap.Places
/-!
The check module for `con:places`: the batteries re-read the shape
calculus's identity instances by kernel reduction — the row list as
the derived display, the degree, the beta-set with the tex's row
read `x_i = λ_i + (d_f - i) + 1` and the complement pairing, the
unit set, the swap grading's parity, the content read, and the
monomial enumerations; the column union's row read joins them with
its width binder's two ragged refusals.  The display's own two
reads close it: the shape read back off its display, and the full
column's raise of every display member by one successor.
-/

open ground places

/-! The shape `(2, 1)` at `d_f = 3`, the column multiset `[1, 1, 0]`. -/

example : rowList [1, 1, 0] = [2, 1, 0] := rfl
example : degree [1, 1, 0] = 3 := rfl
example : betaSet [1, 1, 0] = [5, 3, 1] := by decide +kernel
example : unitSet 3 = [3, 2, 1] := by decide +kernel
example : betaSet [2, 1] = [5, 2] := by decide +kernel

/-- The complement pairing at two columns: `x_1(λ*) + x_3(λ) = c +
d_f + 1` at the self-complementary `(2, 1)`. -/
example : ground.getAt 1 (betaSet [1, 1, 0]) 0
    + ground.getAt 1 (betaSet [1, 1, 0]) 2 = 6 := by decide +kernel

/-! The swap grading. -/

example : inversions [2, 0, 1] = 2 := rfl
example : parity [2, 0, 1] = false := rfl
example : parity [1, 0] = true := rfl
example : parity [1, 2, 0] = false := rfl

/-! Contents and the monomial enumerations. -/

example : content 3 [0, 1, 0, 2] = [2, 1, 1] := rfl
example : monomialsAt [1, 1] = [[0, 1], [1, 0]] := rfl
example : (monomialsAt [2, 1, 0]).length = 3 := rfl
example : (allMon 2 3).length = 8 := rfl
example : idxOf [1, 0] (monomialsAt [1, 1]) = 1 := rfl

/-- The arithmetic rank agrees with the enumeration's own index at
every monomial of a content. -/
example : (monomialsAt [2, 1, 1]).map (fun m => rankOf m [2, 1, 1])
    = (monomialsAt [2, 1, 1]).map
      (fun m => idxOf m (monomialsAt [2, 1, 1])) := rfl

/-! The enumerators: the contents at the composition counts, the
shapes at the partition counts, every member at the stated length
and box total — the exhaustive table reads ride these families. -/

example : (allContents 3 3).length = 10 := by decide +kernel
example : ((allContents 3 3).all (fun m =>
    m.length == 3 && m.foldl (fun a b => a + b) 0 == 3)) = true := by
  decide +kernel
example : (allShapes 2 4).length = 3 := by decide +kernel
example : (allShapes 3 6).length = 7 := by decide +kernel
example : (allShapes 4 8).length = 15 := by decide +kernel
example : (allShapes 6 12).length = 58 := by decide +kernel
example : ((allShapes 4 8).all (fun s =>
    s.length == 4 && degree s == 8)) = true := by decide +kernel

/-! The complement pairing at a non-self-complementary shape:
`(2)` against `(2, 2)` at two columns, every index pair joining to
`d_f + 1` reading `c + d_f + 1 = 6`. -/

example : betaSet [2, 0, 0] = [5, 2, 1] := by decide +kernel
example : betaSet [0, 2, 0] = [5, 4, 1] := by decide +kernel
example : List.zipWith (fun a b => a + b) (betaSet [0, 2, 0])
    ((betaSet [2, 0, 0]).reverse) = [6, 6, 6] := by decide +kernel

/-! The enumeration's coherence at instances: the count equation's
member and off-member reads. -/

example : ground.countOf [1, 0] (monomialsAt [1, 1]) = 1 := by decide +kernel
example : ground.countOf [0, 1] (monomialsAt [1, 1]) = 1 := by decide +kernel
example : ground.countOf [0, 0] (monomialsAt [1, 1]) = 0 := by decide +kernel
example : ground.countOf [0, 5] (monomialsAt [1]) = 0 := by decide +kernel
example : ground.countOf [0, 1, 0] (monomialsAt [2, 1]) = 1 := by
  decide +kernel
example : ground.countOf [1, 0, 1] (monomialsAt [2, 1]) = 0 := by
  decide +kernel
example : (monomialsAt [1, 1, 1]).length = 6 := by decide +kernel

/-! The word clause at an instance: the letter count joins the
start's inversion count to the end's at twice the returning count,
and the word's parity is the end list's. -/

example : applyWord [0, 1, 0] [0, 1, 2] = [2, 1, 0] := by decide +kernel
example : ([0, 1, 0] : List Nat).length + inversions [0, 1, 2]
    = inversions (applyWord [0, 1, 0] [0, 1, 2])
      + 2 * returns [0, 1, 0] [0, 1, 2] := by decide +kernel
example : returns [0, 1, 0] [0, 1, 2] = 0 := by decide +kernel
example : returns [0, 0] [1, 0, 2] = 1 := by decide +kernel
example : parityOf (([0, 1, 0] : List Nat).length
      + inversions [0, 1, 2])
    = parity (applyWord [0, 1, 0] [0, 1, 2]) := by decide +kernel

/-! The transposition's inversion count at instances: its own place
pair with two pairs per place between its two, one pair beyond an
even family (the general count's deferral pins). -/

example : inversions (swapPair 2 3 (List.range 4)) = 1 := by decide +kernel
example : inversions (swapPair 0 2 (List.range 4)) = 3 := by decide +kernel
example : inversions (swapPair 1 3 (List.range 5)) = 3 := by decide +kernel
example : inversions (swapPair 0 3 (List.range 4)) = 5 := by decide +kernel
example : parity (swapPair 0 3 (List.range 4)) = true := by decide +kernel

/-! The descent and the additivity at instances: the sort's word,
the classification's read, and the composed parities. -/

example : sortWord (inversions [2, 0, 1]) [2, 0, 1] = [0, 1] := by
  decide +kernel
example : applyWord (sortWord (inversions [2, 0, 1]) [2, 0, 1])
    [2, 0, 1] = List.range 3 := by decide +kernel
example : (sortWord (inversions [3, 1, 2, 0]) [3, 1, 2, 0]).length
    = inversions [3, 1, 2, 0] := by decide +kernel
example : parity ([1, 2, 0].map (ground.getAt 0 [0, 2, 1]))
    = xor (parity [1, 2, 0]) (parity [0, 2, 1]) := by decide +kernel
example : parity ([1, 0, 2].map (ground.getAt 0 [2, 1, 0]))
    = xor (parity [1, 0, 2]) (parity [2, 1, 0]) := by decide +kernel

/-! The rank tier's pins (`con:places`): the arrangement count
against the enumeration's length, and the arithmetic rank's
positional read — theorem instances beside the decided values. -/

example : countMon [1, 2, 0] = (monomialsAt [1, 2, 0]).length :=
  countMon_read [1, 2, 0]
example : countMon [1, 2, 0] = 3 := by decide +kernel
example : rankOf [1, 1, 0] [1, 2] < (monomialsAt [1, 2]).length
    ∧ ground.getAt [] (monomialsAt [1, 2])
        (rankOf [1, 1, 0] [1, 2]) = [1, 1, 0] :=
  rankOf_read [1, 1, 0] [1, 2] (by decide +kernel) (by decide +kernel)
example : rankOf [1, 1, 0] [1, 2] = 2 := by decide +kernel
example : ground.getAt [] (monomialsAt [1, 2]) 2 = [1, 1, 0] := by
  decide +kernel

/-! The column union's row read (`con:places`): the shapes'
composition by column union sends the row lists to their key-by-key
sum, at the symmetric pair, at an asymmetric pair, and at three
letters — decided values beside the theorem's own applications. -/

example : rowList (addS [1, 0] [1, 0])
    = List.zipWith (fun x y => x + y) (rowList [1, 0])
      (rowList [1, 0]) := by decide +kernel
example : rowList (addS [2, 0] [0, 1])
    = List.zipWith (fun x y => x + y) (rowList [2, 0])
      (rowList [0, 1]) := by decide +kernel
example : rowList (addS [1, 2, 0] [2, 0, 1])
    = List.zipWith (fun x y => x + y) (rowList [1, 2, 0])
      (rowList [2, 0, 1]) := by decide +kernel
example : rowList (addS [2, 0] [0, 1])
    = List.zipWith (fun x y => x + y) (rowList [2, 0])
      (rowList [0, 1]) :=
  rowList_addS [2, 0] [0, 1] (by decide +kernel)
example : rowList (addS [1, 2, 0] [2, 0, 1])
    = List.zipWith (fun x y => x + y) (rowList [1, 2, 0])
      (rowList [2, 0, 1]) :=
  rowList_addS [1, 2, 0] [2, 0, 1] (by decide +kernel)

/-! The width binder's refusals: at a ragged pair the truncating
fold drops the longer side's tail while the row list has already
read it into every earlier key, and the display fails in both
orientations — the one letter width is load-bearing, not
plumbing. -/

example : ¬ (rowList (addS [1, 2] [3])
    = List.zipWith (fun x y => x + y) (rowList [1, 2])
      (rowList [3])) := by decide +kernel
example : ¬ (rowList (addS [3] [1, 2])
    = List.zipWith (fun x y => x + y) (rowList [3])
      (rowList [1, 2])) := by decide +kernel

/-! The unit-content family's letter binder is load-bearing: at a
letter off the width the unit family is vacant, so its enumeration
misses the letter's own word, and a place beyond the enumeration
reads its rank off itself — each refusal beside the read that
holds, the content's own display binder-free. -/

example : ¬ (monomialsAt (unitAt 2 5) = [[5]]) := by decide +kernel
example : ¬ (rankOf (ground.getAt [] (monomialsAt [1, 1]) 7) [1, 1]
    = 7) := by decide +kernel
example : rankOf (ground.getAt [] (monomialsAt [1, 1]) 1) [1, 1]
    = 1 := rankOf_getAt [1, 1] 1 (by decide +kernel)
example : content 2 [5] = unitAt 2 5 := by decide +kernel

/-! The cycles at the identity, the transposition, the three-cycle
and the double transposition, the orbit words in place order. -/

example : cyclesOf [0, 1] = [[0], [1]] := by decide +kernel
example : cyclesOf [1, 0] = [[0, 1]] := by decide +kernel
example : cyclesOf [1, 2, 0] = [[0, 1, 2]] := by decide +kernel
example : cyclesOf [1, 0, 3, 2] = [[0, 1], [2, 3]] := by decide +kernel

/-! The adjacent transposition's list-kit instance, and the
count-family identification at adjacent-sorted lists
(`lem:strings`' sorting vocabulary). -/

example : swapPair 1 2 [5, 6, 7] = ground.adjSwap 1 [5, 6, 7] :=
  swapPair_adjacent 1 [5, 6, 7]
example : swapPair 1 2 [5, 6, 7] = [5, 7, 6] := by decide +kernel
example : ([1, 3, 5] : List Nat) = [1, 3, 5] :=
  sorted_eq_of_counts [1, 3, 5] [1, 3, 5] (by decide +kernel) (by decide +kernel)
    (fun _ => rfl)
example : firstRev [1, 3, 5] = none := by decide +kernel
example : ¬ firstRev [5, 3, 1] = none := by decide +kernel

/-! The pointed and scaled occupancy kit: the replicate split at a
stated key, the bump at the split, the pointed family's sum and
rows, the scaled rows, and the full column's raise. -/

example : List.replicate (2 + (1 + 1)) 7
    = List.replicate 2 7 ++ 7 :: List.replicate 1 7 :=
  places.replicate_split 7 2 1
example : ground.bumpAt 2 (List.replicate 2 0 ++ 5 :: [9])
    = List.replicate 2 0 ++ 6 :: [9] :=
  places.bumpAt_split 2 5 [9]
example : ground.sumNat (List.replicate 2 0 ++ 3 :: List.replicate 4 0)
    = 3 := places.sumNat_pointAt 2 4 3
example : places.rowList (List.replicate 2 0 ++ 3 :: List.replicate 1 0)
    = List.replicate (2 + 1) 3 ++ List.replicate 1 0 :=
  places.rowList_pointAt 2 1 3
example : places.rowList (([1, 0, 1, 0] : places.Shape).map
      (fun n => n * 3))
    = (places.rowList [1, 0, 1, 0]).map (fun n => n * 3) :=
  places.rowList_scale 3 [1, 0, 1, 0]
example : places.rowList (ground.bumpAt (([1, 1, 0] :
      places.Shape).length - 1) [1, 1, 0])
    = (places.rowList [1, 1, 0]).map (fun x => x + 1) :=
  places.rowList_full [1, 1, 0]

/-! The display's shape read and the full column's raise. -/

example : places.display (ground.bumpAt
      (([1, 0, 2] : places.Shape).length - 1) [1, 0, 2])
    = [7, 5, 4] := by decide +kernel

example : (places.display [1, 0, 2]).map (fun x => x + 1)
    = [7, 5, 4] := by decide +kernel

example : places.display (ground.bumpAt
      (([1, 0, 2] : places.Shape).length - 1) [1, 0, 2])
    = (places.display [1, 0, 2]).map (fun x => x + 1) :=
  places.display_full [1, 0, 2]

example : places.display [1, 1, 0] = [5, 3, 1] := by decide +kernel
example : places.display [2, 0, 0] = [5, 2, 1] := by decide +kernel

/-- The two shapes of one degree part at their displays: the shape
read back refuses the joined display. -/
example : ¬ places.display [1, 1, 0] = places.display [2, 0, 0] :=
  fun h => absurd (places.display_inj [1, 1, 0] [2, 0, 0] h) (by decide +kernel)

/-! The permuted display's entry at the assignment's key, and the
adjacent exchange's membership in the place enumeration. -/

example : ground.getAt 0 (places.expo [7, 5, 2] [2, 0, 1]) 0 = 2 := by
  decide +kernel

example : ground.getAt 0 (places.expo [7, 5, 2] [2, 0, 1]) 0
    = ground.getAt 0 [7, 5, 2] (ground.getAt 0 [2, 0, 1] 0) :=
  places.getAt_expo [7, 5, 2] [2, 0, 1] 0 (by decide +kernel)

example : 0 < ground.countOf (ground.adjSwap 1 [2, 0, 1])
    (places.perms 3) :=
  places.perm_member_adjSwap (by decide +kernel) 1

example : ground.countOf (ground.adjSwap 1 [2, 0, 1])
    (places.perms 3) = 1 := by decide +kernel

/-! The tie tier at strictly descending displays: the unit-content
gap read at both directions, and the raise's rigidity — the
permuted raise forced back to the identity with the raise the
source's own. -/

example : ground.tieGap [3, 2] [2, 2] = some (ground.unitAt 2 0) :=
  (places.tieGap_unit 2 [3, 2] [2, 2] (by decide +kernel) (by decide +kernel) 0
    (by decide +kernel)).mpr (by decide +kernel)

example : [4, 2, 1] = ground.bumpAt 0 [3, 2, 1] :=
  (places.tieGap_unit 3 [4, 2, 1] [3, 2, 1] (by decide +kernel) (by decide +kernel) 0
    (by decide +kernel)).mp (by decide +kernel)

example : ([0, 1, 2] : List Nat) = List.range 3 ∧ [7, 4, 2]
    = ground.bumpAt 0 [6, 4, 2] :=
  places.tie_rigid 3 [6, 4, 2] [7, 4, 2] (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) [0, 1, 2] (by decide +kernel) 0 (by decide +kernel)
    (by decide +kernel)

/-! The tie squeeze at a general source display: the all-ones tie's
identity permutation with the raised target, and the letter-pair
move's adjacent exchange at a unit gap. -/

example : ([0, 1, 2] : List Nat) = List.range 3
    ∧ places.display [1, 0, 1]
        = (places.display [1, 0, 0]).map (fun x => x + 1) :=
  places.tieOnes 3 [1, 0, 0] [1, 0, 1] (by decide +kernel) [0, 1, 2]
    (by decide +kernel) [1, 1, 1] (by decide +kernel) (by decide +kernel)

/-- The letter-pair move's gap at the exchanged assignment: one
doubled place against one vacant place, the rest at the unit. -/
example : ground.tieGap (places.display [1, 0, 3])
    (places.expo (places.display [1, 0, 2]) [0, 2, 1])
      = some [1, 2, 0] := by decide +kernel

example : ground.getAt 0 (places.display [1, 0, 2]) 1
    = ground.getAt 0 (places.display [1, 0, 2]) 2 + 1 := by decide +kernel

example : ∃ k, k + 1 < 3
    ∧ ground.getAt 0 (places.display [1, 0, 2]) k
        = ground.getAt 0 (places.display [1, 0, 2]) (k + 1) + 1
    ∧ ([0, 2, 1] : List Nat) = ground.adjSwap k (List.range 3)
    ∧ places.display [1, 0, 3]
        = (places.display [1, 0, 2]).map (fun x => x + 1) :=
  places.tieMove 3 [1, 0, 2] [1, 0, 3] (by decide +kernel) [0, 2, 1]
    (by decide +kernel) (by decide +kernel) [1, 2, 0] (by decide +kernel) 1 2 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-! The unit assignment's adjacent exchange is odd, the grading
read decided at an instance beside the theorem's route. -/

example : places.parity (ground.adjSwap 1 (List.range 3)) = true := by
  decide +kernel

example : places.parity (ground.adjSwap 1 (List.range 3)) = true :=
  places.parity_adjSwap_range 3 1 (by decide +kernel)

/-! The unit assignment and its adjacent exchange each sit in the
place enumeration once, decided at an instance beside the
theorem's route. -/

example : ground.countOf (List.range 3) (places.perms 3) = 1 := by
  decide +kernel

example : ground.countOf (List.range 3) (places.perms 3) = 1 :=
  places.countRangePerms 3

example : ground.countOf (ground.adjSwap 1 (List.range 3))
    (places.perms 3) = 1 := by decide +kernel

example : ground.countOf (ground.adjSwap 1 (List.range 3))
    (places.perms 3) = 1 :=
  places.countOf_adjSwap_perms 3 1

/-! The letter-pair move's three reads at a stated gap family: the
cap, the doubled place and the vacant place each read off the
family's entries. -/

example : ∀ t, t < 4 → ground.getAt 0 [1, 2, 0, 1] t ≤ 2 := by decide +kernel

example : ∀ t, t < 4 → ground.getAt 0 [1, 2, 0, 1] t ≤ 2 :=
  fun t ht =>
    places.moveCap 4 [1, 2, 0, 1] 1 2 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) t ht

example : ∀ t, t < 4 → ground.getAt 0 [1, 2, 0, 1] t = 2 → t = 1 := by
  decide +kernel

example : ∀ t, t < 4 → ground.getAt 0 [1, 2, 0, 1] t = 2 → t = 1 :=
  fun t ht hv =>
    places.movePlaceTwo 4 [1, 2, 0, 1] 1 2 (by decide +kernel) (by decide +kernel)
      t ht hv

example : ∀ t, t < 4 → ground.getAt 0 [1, 2, 0, 1] t = 0 → t = 2 := by
  decide +kernel

example : ∀ t, t < 4 → ground.getAt 0 [1, 2, 0, 1] t = 0 → t = 2 :=
  fun t ht hv =>
    places.movePlaceZero 4 [1, 2, 0, 1] 1 2 (by decide +kernel) (by decide +kernel)
      t ht hv
