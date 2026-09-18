import MassGap.Gentable
import MassGap.Elim
import MassGap.Units
import MassGap.Inertia
/-!
`con:sertables` — the member weight tables, the instantiations
filling `con:gentable`'s fields.  The series' tables are functions
of the rank: the displayed simple data evaluate to the Cartan rows
(`B` with the short last key at the doubled edge toward it, `C` its
mirror, `D` the fork at the last two keys), the length lists read
the displayed form scales, and the positive lists enter at the
displayed family folds — the difference, sum and short or long
families — with the highest root the stated family's first member.
The fixed members enter at their simple keys: the Cartan rows off
the displayed edge lists (`G_2` and `F_4` at their displayed
doubled edges), the length lists the displayed data, `G_2`'s six
folds displayed outright, and `F_4`'s and the `E`-members' positive
lists the displayed coordinate families (the doubled-coordinate
realizations, `E_7` and `E_6` the balance-partner selections of
`E_8`'s list) read to their natural folds by the fold descent, the
walk at a positive-dot simple key with the fold witness collected
along it, `famRead` the naming identity's round trip
(`foldCoords` returning the member) joined to the root fold's
coroot reads at one fold list; the `E`-members' fold lists are the
committed literals (`posE6`, `posE7`, `posE8`), each the descent's
own output at its certifying equation in the check module.  The adjugate rows are the
five displayed matrices at their fold keys, `adjRead` the coroot
witness `Σ_k a_ik α_k(α_j^∨) = e δ_ij` and `thetaRowRead` the
θ-fold row's `e`-multiple.  The derived residues are
`gentable.residue`'s reads, the series' values at every rank the
displayed residue folds' own (`residue_tableB`, `residue_tableC`,
`residue_tableD`) with the θ-coroot's support key off the unit beside
them (`corootB_off`, `corootC_off`, `corootD_off`, `prop:row`'s single
keys), and the residue folds pinned per member in the check
module. The displayed Weyl lists are the signed place
permutations (`serWeylB`, `serWeylC`, `serWeylD`), at the full
sign count for B and C and its even half for D. Their keys have
the coroot width, their even member includes the canonical seed,
and the series' keys are distinct at strictly dominant seeds
(`serWeylB_regular`, `serWeylC_regular`, `serWeylD_regular`).
At every dominant seed, including chamber walls, the displayed
orbit has one dominant key (`serWeylB_dominant_top`,
`serWeylC_dominant_top`, `serWeylD_dominant_top`). Weak order
identifies the coordinate magnitudes by their counts; D's even
sign parity keeps the coordinate product, which determines the
final coordinate after the earlier upper-side coordinates.
G2's twelve matrices have the corresponding chamber read
(`weylMatG2_chamber`, `weylG2_dominant_top`), including singular
seeds at the negative rows' forced unit coordinates. At a strictly
dominant G2 seed the twelve images are distinct
(`weylG2_regular`), the matrix pairs separated by an entrywise
ordered row with a strict entry (`weylMatG2_separation`). The
adjugate gap matrices `weylFoldG2` read natural simple-fold
coefficients and rejoin each word to the identity
(`weylFoldG2_read`). The coordinate solves
read back at one value, the doubled displays at the signed half's
even margins; permutation of sign places keeps the parity and
one coordinate flip exchanges it. The defining tables enter
at their key encodings — the paired keys with `B`'s further null
key — the simple raisings and lowerings the displayed unit moves at
the form's twist (`B`'s short pair through the null key at the
cleared weights), each triple display one read (`memtable.tripleRead` at the
generating tables, the weighted transpose joined to the commutator
displays at the coroot diagonal), and the invariant count the stacked raisings' kernel
over the unit-content monomials (`invCountB` and its partners,
`prop:wg` the pairing's consumer).  The coordinate tier closes the
construction at the coroot presentation: `FundData` carries the
fundamentals' cleared Gram with its scale, the simple members'
positions in the positive list and the reflections' permutations
of it, and the reads pin them — the shape conjuncts, the Gram's
defining read against the Cartan rows with its symmetry, the
simple positions, the involution reads at the reflection matrices
and at the permutation data, the form-keeping read, the
permutation of the positive list, the `ρ`-dot positivity, and the
graded image list's own shape at the keys —
the reflection matrices off the Cartan rows at `con:gentable`'s
reflection join. Their squares read the identity at the Cartan
diagonal two (`reflSquareRead_of_diagonal`), for every series rank
and at the fixed members. The split certificates are `inertia`'s own reads
in the check module.

Every B/C/D positive fold has the rank's width and an occupied
coefficient sum (`foldsB_occupied`, `foldsC_occupied`,
`foldsD_occupied`), and every simple fold belongs to that list
(`simpleFold_mem_B`, `simpleFold_mem_C`, `simpleFold_mem_D`). G2's
word-reversal index `weylInvG2` is an involution preserving the
grading. Its matrix identity moves each word across the Gram
(`weylInvG2_read`, `weylMatG2_dot`).
-/

namespace sertables
open ground gentable

/-! The series' fold families, functions of the rank: the occupancy
window `ind l a b`, one on the keys of `[a, b)`, is the families'
one constructor. -/

/-- The occupancy window: one on the keys of `[a, b)`, the fold
families' one constructor. -/
def ind (l a b : Nat) : List Nat :=
  (List.range l).map (fun k => if a ≤ k && k < b then 1 else 0)

/-- The window keeps the stated length. -/
theorem ind_len (l a b : Nat) : (ind l a b).length = l :=
  ground.length_mapRange _ l

/-- The window's entry: one on the keys of the stated interval,
the count's unit off it. -/
theorem ind_at (l a b k : Nat) (hk : k < l) :
    ground.getAt 0 (ind l a b) k
      = if a ≤ k && k < b then 1 else 0 := by
  show ground.getAt 0 ((List.range l).map
    (fun x => if a ≤ x && x < b then 1 else 0)) k = _
  rw [ground.getAt_map_range 0 _ l k, if_pos hk]

private def addN (v w : List Nat) : List Nat :=
  List.zipWith (fun a b => a + b) v w

private def two (v : List Nat) : List Nat := addN v v

/-- The difference family, one at the keys between the pair. -/
def diffFold (l a b : Nat) : List Nat := ind l a b

/-- The `B` sum family: one on `[a, b)`, two on `[b, l)`. -/
def sumFoldB (l a b : Nat) : List Nat := addN (ind l a b) (two (ind l b l))

/-- The `B` short family: one on `[a, l)`. -/
def shortFold (l a : Nat) : List Nat := ind l a l

/-- The `C` sum family: one on `[a, b)`, two on `[b, l-1)`, one at
the last key. -/
def sumFoldC (l a b : Nat) : List Nat :=
  addN (ind l a b) (addN (two (ind l b (l - 1))) (ind l (l - 1) l))

/-- The `C` long family: two on `[a, l-1)`, one at the last key. -/
def longFold (l a : Nat) : List Nat :=
  addN (two (ind l a (l - 1))) (ind l (l - 1) l)

/-- The `D` sum family at a coordinate pair: the generic member one
on `[a, b)`, two on `[b, l-2)`, one on the last two keys, and the
last-coordinate member one on `[a, l-2)` with one on the last
key. -/
def sumFoldD (l a b : Nat) : List Nat :=
  if b + 1 == l then addN (ind l a (l - 2)) (ind l (l - 1) l)
  else
    addN (ind l a b) (addN (two (ind l b (l - 2))) (ind l (l - 2) l))

/-- The `B` positive list at its folds. -/
def foldsB (l : Nat) : List (List Nat) :=
  (places.pairsOf l).map (fun p => diffFold l p.1 p.2)
    ++ (places.pairsOf l).map (fun p => sumFoldB l p.1 p.2)
    ++ (List.range l).map (shortFold l)

/-- The `C` positive list at its folds. -/
def foldsC (l : Nat) : List (List Nat) :=
  (places.pairsOf l).map (fun p => diffFold l p.1 p.2)
    ++ (places.pairsOf l).map (fun p => sumFoldC l p.1 p.2)
    ++ (List.range l).map (longFold l)

/-- The `D` positive list at its folds. -/
def foldsD (l : Nat) : List (List Nat) :=
  (places.pairsOf l).map (fun p => diffFold l p.1 p.2)
    ++ (places.pairsOf l).map (fun p => sumFoldD l p.1 p.2)

/-- An occupied interval contributes one at its first key. -/
private theorem ind_occupied (l a b : Nat) (ha : a < l) (hab : a < b) :
    0 < ground.sumNat (ind l a b) := by
  have he : ground.getAt 0 (ind l a b) a = 1 := by
    rw [ind_at l a b a ha, decide_eq_true (Nat.le_refl a), decide_eq_true hab]
    rfl
  have hm := ground.mem_getAt 0 (ind l a b) a (by rw [ind_len]; exact ha)
  rw [he] at hm
  exact ground.mem_le_sumNat _ 1 hm

private theorem last_ind_occupied (l : Nat) (hl : 0 < l) :
    0 < ground.sumNat (ind l (l - 1) l) := by
  have h := Nat.lt_succ_self (l - 1)
  change l - 1 < (l - 1) + 1 at h
  rw [ground.subAdd hl] at h
  exact ind_occupied l (l - 1) l h h

private theorem sumFoldB_occupied (l a b : Nat) (hab : a < b) (hb : b < l) :
    (sumFoldB l a b).length = l ∧ 0 < ground.sumNat (sumFoldB l a b) := by
  have htwo : (two (ind l b l)).length = l :=
    ground.length_zipWith _ _ _ l (ind_len _ _ _) (ind_len _ _ _)
  refine ⟨ground.length_zipWith _ _ _ l (ind_len _ _ _) htwo, ?_⟩
  change 0 < ground.sumNat (List.zipWith (fun a b => a + b) (ind l a b) (two (ind l b l)))
  rw [ground.sumNat_zipWith_add _ _ ((ind_len _ _ _).trans htwo.symm)]
  exact Nat.lt_of_lt_of_le (ind_occupied l a b (Nat.lt_trans hab hb) hab) (Nat.le_add_right _ _)

private theorem sumFoldC_occupied (l a b : Nat) (hab : a < b) (hb : b < l) :
    (sumFoldC l a b).length = l ∧ 0 < ground.sumNat (sumFoldC l a b) := by
  have htwo : (two (ind l b (l - 1))).length = l :=
    ground.length_zipWith _ _ _ l (ind_len _ _ _) (ind_len _ _ _)
  have htail : (addN (two (ind l b (l - 1))) (ind l (l - 1) l)).length = l :=
    ground.length_zipWith _ _ _ l htwo (ind_len _ _ _)
  refine ⟨ground.length_zipWith _ _ _ l (ind_len _ _ _) htail, ?_⟩
  change 0 < ground.sumNat (List.zipWith (fun a b => a + b) (ind l a b) _)
  rw [ground.sumNat_zipWith_add _ _ ((ind_len _ _ _).trans htail.symm)]
  exact Nat.lt_of_lt_of_le (ind_occupied l a b (Nat.lt_trans hab hb) hab) (Nat.le_add_right _ _)

private theorem longFold_occupied (l a : Nat) (ha : a < l) :
    (longFold l a).length = l ∧ 0 < ground.sumNat (longFold l a) := by
  have htwo : (two (ind l a (l - 1))).length = l :=
    ground.length_zipWith _ _ _ l (ind_len _ _ _) (ind_len _ _ _)
  refine ⟨ground.length_zipWith _ _ _ l htwo (ind_len _ _ _), ?_⟩
  change 0 < ground.sumNat (List.zipWith (fun a b => a + b) _ (ind l (l - 1) l))
  rw [ground.sumNat_zipWith_add _ _ (htwo.trans (ind_len _ _ _).symm)]
  exact Nat.lt_of_lt_of_le (last_ind_occupied l (Nat.lt_of_le_of_lt (Nat.zero_le a) ha))
    (Nat.le_add_left _ _)

private theorem sumFoldD_occupied (l a b : Nat) (hab : a < b) (hb : b < l) :
    (sumFoldD l a b).length = l ∧ 0 < ground.sumNat (sumFoldD l a b) := by
  unfold sumFoldD
  by_cases he : b + 1 = l
  · rw [ground.eqBeqOf he]
    refine ⟨ground.length_zipWith _ _ _ l (ind_len _ _ _) (ind_len _ _ _), ?_⟩
    change 0 < ground.sumNat (List.zipWith (fun a b => a + b) _ _)
    rw [ground.sumNat_zipWith_add _ _ ((ind_len l a (l - 2)).trans (ind_len _ _ _).symm)]
    exact Nat.lt_of_lt_of_le (last_ind_occupied l (Nat.lt_of_le_of_lt (Nat.zero_le b) hb))
      (Nat.le_add_left _ _)
  · rw [ground.neBeqOf he]
    have htwo : (two (ind l b (l - 2))).length = l :=
      ground.length_zipWith _ _ _ l (ind_len _ _ _) (ind_len _ _ _)
    have htail : (addN (two (ind l b (l - 2))) (ind l (l - 2) l)).length = l :=
      ground.length_zipWith _ _ _ l htwo (ind_len _ _ _)
    refine ⟨ground.length_zipWith _ _ _ l (ind_len _ _ _) htail, ?_⟩
    change 0 < ground.sumNat (List.zipWith (fun a b => a + b) (ind l a b) _)
    rw [ground.sumNat_zipWith_add _ _ ((ind_len _ _ _).trans htail.symm)]
    exact Nat.lt_of_lt_of_le (ind_occupied l a b (Nat.lt_trans hab hb) hab) (Nat.le_add_right _ _)

/-- B's three positive-root families have the rank's width and
an occupied coefficient sum, at every rank. -/
theorem foldsB_occupied (l : Nat) (f : List Nat) (hf : f ∈ foldsB l) :
    f.length = l ∧ 0 < ground.sumNat f := by
  cases ground.mem_append_of _ _ hf with
  | inl h =>
    cases ground.mem_append_of _ _ h with
    | inl h =>
      obtain ⟨p, hp, he⟩ := ground.mem_map_of _ _ f h
      have hr := places.pairs_mem l p (ground.countOf_pos_of_mem hp)
      rw [← he]
      exact ⟨ind_len _ _ _, ind_occupied l p.1 p.2 (Nat.lt_trans hr.1 hr.2) hr.1⟩
    | inr h =>
      obtain ⟨p, hp, he⟩ := ground.mem_map_of _ _ f h
      have hr := places.pairs_mem l p (ground.countOf_pos_of_mem hp)
      rw [← he]
      exact sumFoldB_occupied l p.1 p.2 hr.1 hr.2
  | inr h =>
    obtain ⟨a, ha, he⟩ := ground.mem_map_of _ _ f h
    rw [← he]
    exact ⟨ind_len _ _ _, ind_occupied l a l (ground.ltOfMemRange ha) (ground.ltOfMemRange ha)⟩

/-- C's difference, sum and long-root families have the rank's
width and an occupied coefficient sum, at every rank. -/
theorem foldsC_occupied (l : Nat) (f : List Nat) (hf : f ∈ foldsC l) :
    f.length = l ∧ 0 < ground.sumNat f := by
  cases ground.mem_append_of _ _ hf with
  | inl h =>
    cases ground.mem_append_of _ _ h with
    | inl h =>
      obtain ⟨p, hp, he⟩ := ground.mem_map_of _ _ f h
      have hr := places.pairs_mem l p (ground.countOf_pos_of_mem hp)
      rw [← he]
      exact ⟨ind_len _ _ _, ind_occupied l p.1 p.2 (Nat.lt_trans hr.1 hr.2) hr.1⟩
    | inr h =>
      obtain ⟨p, hp, he⟩ := ground.mem_map_of _ _ f h
      have hr := places.pairs_mem l p (ground.countOf_pos_of_mem hp)
      rw [← he]
      exact sumFoldC_occupied l p.1 p.2 hr.1 hr.2
  | inr h =>
    obtain ⟨a, ha, he⟩ := ground.mem_map_of _ _ f h
    rw [← he]
    exact longFold_occupied l a (ground.ltOfMemRange ha)

/-- D's difference and forked sum families have the rank's width
and an occupied coefficient sum, including the two-tip case. -/
theorem foldsD_occupied (l : Nat) (f : List Nat) (hf : f ∈ foldsD l) :
    f.length = l ∧ 0 < ground.sumNat f := by
  cases ground.mem_append_of _ _ hf with
  | inl h =>
    obtain ⟨p, hp, he⟩ := ground.mem_map_of _ _ f h
    have hr := places.pairs_mem l p (ground.countOf_pos_of_mem hp)
    rw [← he]
    exact ⟨ind_len _ _ _, ind_occupied l p.1 p.2 (Nat.lt_trans hr.1 hr.2) hr.1⟩
  | inr h =>
    obtain ⟨p, hp, he⟩ := ground.mem_map_of _ _ f h
    have hr := places.pairs_mem l p (ground.countOf_pos_of_mem hp)
    rw [← he]
    exact sumFoldD_occupied l p.1 p.2 hr.1 hr.2

/-- A singleton interval is the unit simple-root coefficient
list at its key. -/
private theorem ind_one (l i : Nat) :
    ind l i (i + 1) = (List.range l).map (fun k => if k == i then 1 else 0) := by
  unfold ind
  apply ground.map_congr_all
  intro k
  by_cases he : k = i
  · rw [he, decide_eq_true (Nat.le_refl i), decide_eq_true (Nat.lt_succ_self i), ground.eqBeqOf rfl]
    rfl
  · rw [ground.neBeqOf he]
    by_cases hlo : i ≤ k
    · have hhi : ¬ k < i + 1 := fun h => he (Nat.le_antisymm (Nat.le_of_lt_succ h) hlo)
      rw [decide_eq_false hhi, Bool.and_false]
    · rw [decide_eq_false hlo]
      rfl

/-- An interval at equal ends is the vacant coefficient list. -/
private theorem ind_vacant (l i : Nat) : ind l i i = List.replicate l 0 := by
  unfold ind
  have he : (List.range l).map (fun k => if i ≤ k && k < i then 1 else 0)
      = (List.range l).map (fun _ => 0) := by
    apply ground.map_congr_all
    intro k
    by_cases h : i ≤ k
    · rw [decide_eq_false (Nat.not_lt_of_ge h), Bool.and_false]; rfl
    · rw [decide_eq_false h]; rfl
  rw [he, ground.map_const, ground.length_range]

private theorem longFold_last (k : Nat) : longFold (k + 1) k = ind (k + 1) k (k + 1) := by
  change List.zipWith (fun a b => a + b)
    (List.zipWith (fun a b => a + b) (ind (k + 1) k k) (ind (k + 1) k k)) _ = _
  rw [ind_vacant, ground.zipWith_zero_left _ _ (ground.length_replicate _ _),
    ground.zipWith_zero_left _ _ (ind_len _ _ _), ground.addSubSelfR]

private theorem sumFoldD_last (k : Nat) :
    sumFoldD (k + 2) k (k + 1) = ind (k + 2) (k + 1) (k + 2) := by
  unfold sumFoldD
  rw [ground.eqBeqOf (show k + 1 + 1 = k + 2 from rfl)]
  change List.zipWith (fun a b => a + b) (ind (k + 2) k k) _ = _
  rw [ind_vacant, ground.zipWith_zero_left _ _ (ind_len _ _ _)]
  rw [show k + 2 - 1 = k + 1 from ground.addSubSelfR (k + 1) 1]

/-- Every B simple fold is a member of its positive-root list,
the last key in the short family and the earlier keys in the
consecutive difference family. -/
theorem simpleFold_mem_B (l i : Nat) (hi : i < l) :
    ((List.range l).map (fun k => if k == i then 1 else 0)) ∈ foldsB l := by
  rw [← ind_one]
  by_cases hnext : i + 1 < l
  · exact ground.mem_append_left _ (ground.mem_append_left _
      (ground.mem_map_to (fun p => diffFold l p.1 p.2)
        (ground.mem_of_countOf_pos _ _ (places.pairs_complete l (Nat.lt_succ_self i) hnext))))
  · have he : i + 1 = l := Nat.le_antisymm (Nat.succ_le_of_lt hi) (Nat.le_of_not_lt hnext)
    rw [he]
    exact ground.mem_append_right _ (ground.mem_map_to (shortFold l) (ground.memRange hi))

/-- Every C simple fold is a member of its positive-root list,
the last key in the long family. -/
theorem simpleFold_mem_C (l i : Nat) (hi : i < l) :
    ((List.range l).map (fun k => if k == i then 1 else 0)) ∈ foldsC l := by
  rw [← ind_one]
  by_cases hnext : i + 1 < l
  · exact ground.mem_append_left _ (ground.mem_append_left _
      (ground.mem_map_to (fun p => diffFold l p.1 p.2)
        (ground.mem_of_countOf_pos _ _ (places.pairs_complete l (Nat.lt_succ_self i) hnext))))
  · have he : i + 1 = l := Nat.le_antisymm (Nat.succ_le_of_lt hi) (Nat.le_of_not_lt hnext)
    rw [← he]
    rw [← longFold_last]
    exact ground.mem_append_right _ (ground.mem_map_to (longFold (i + 1)) (ground.memRange (Nat.lt_succ_self i)))

/-- Every D simple fold is in the positive list, including the
last fork key's sum root at ranks from two. -/
theorem simpleFold_mem_D (l i : Nat) (hl : 2 ≤ l) (hi : i < l) :
    ((List.range l).map (fun k => if k == i then 1 else 0)) ∈ foldsD l := by
  rw [← ind_one]
  by_cases hnext : i + 1 < l
  · exact ground.mem_append_left _
      (ground.mem_map_to (fun p => diffFold l p.1 p.2)
        (ground.mem_of_countOf_pos _ _ (places.pairs_complete l (Nat.lt_succ_self i) hnext)))
  · have he : i + 1 = l := Nat.le_antisymm (Nat.succ_le_of_lt hi) (Nat.le_of_not_lt hnext)
    cases i with
    | zero => rw [← he] at hl; exact absurd hl (Nat.not_succ_le_self 1)
    | succ k =>
      rw [← he]
      change ind (k + 2) (k + 1) (k + 2) ∈ foldsD (k + 2)
      rw [← sumFoldD_last]
      exact ground.mem_append_right _ (ground.mem_map_to (fun p => sumFoldD (k + 2) p.1 p.2)
        (ground.mem_of_countOf_pos _ _ (places.pairs_complete (k + 2) (Nat.lt_succ_self k)
          (Nat.lt_succ_self (k + 1)))))

/-! The series' Cartan rows, the displayed coroot formulas at the
displayed simples. -/

private def b2 : BPair := BPair.ofNat 2
private def m1 : BPair := (BPair.ofNat 1).swap
private def m2 : BPair := (BPair.ofNat 2).swap
private def m3 : BPair := (BPair.ofNat 3).swap

/-- The `B` Cartan rows: the chain at the doubled edge into the
short last key. -/
def cartanB (l : Nat) : List (List BPair) :=
  ground.matOf l l (fun i j =>
    if j == i then b2
    else if i + 2 == l && j == i + 1 then m2
    else if j + 1 == i || j == i + 1 then m1
    else BPair.unit)

/-- The `C` Cartan rows: the chain at the doubled edge out of the
long last key. -/
def cartanC (l : Nat) : List (List BPair) :=
  ground.matOf l l (fun i j =>
    if j == i then b2
    else if i + 1 == l && j + 2 == l then m2
    else if j + 1 == i || j == i + 1 then m1
    else BPair.unit)

/-- The `D` Cartan rows: the fork, the last two keys joined to the
key before them and off each other. -/
def cartanD (l : Nat) : List (List BPair) :=
  ground.matOf l l (fun i j =>
    if j == i then b2
    else if i + 1 == l then (if j + 3 == l then m1 else BPair.unit)
    else if j + 1 == l then (if i + 3 == l then m1 else BPair.unit)
    else if j + 1 == i || j == i + 1 then m1
    else BPair.unit)

private def lensB (l : Nat) : List Nat :=
  (List.range l).map (fun i => if i + 1 == l then 1 else 2)

private def lensC (l : Nat) : List Nat :=
  (List.range l).map (fun i => if i + 1 == l then 2 else 1)

/-- The `B` member's table at the rank. -/
def tableB (l : Nat) : Table :=
  ⟨l, lensB l, 1, cartanB l, foldsB l, sumFoldB l 0 1⟩

/-- The `C` member's table at the rank. -/
def tableC (l : Nat) : Table :=
  ⟨l, lensC l, 1, cartanC l, foldsC l, longFold l 0⟩

/-- The `B` table's length entry: one at the last key, two below
it. -/
theorem lensB_at (l i : Nat) (hi : i < l) :
    ground.getAt 0 (tableB l).lenNums i
      = if i + 1 == l then 1 else 2 := by
  show ground.getAt 0 ((List.range l).map
    (fun x => if x + 1 == l then 1 else 2)) i = _
  rw [ground.getAt_map_range 0 _ l i, if_pos hi]

/-- The `C` table's length entry: two at the last key, one below
it. -/
theorem lensC_at (l i : Nat) (hi : i < l) :
    ground.getAt 0 (tableC l).lenNums i
      = if i + 1 == l then 2 else 1 := by
  show ground.getAt 0 ((List.range l).map
    (fun x => if x + 1 == l then 2 else 1)) i = _
  rw [ground.getAt_map_range 0 _ l i, if_pos hi]

/-- The `D` member's table at the rank. -/
def tableD (l : Nat) : Table :=
  ⟨l, List.replicate l 2, 1, cartanD l, foldsD l, sumFoldD l 0 1⟩

/-! ## The `B` Cartan column entries -/

/-- The `B` Cartan entry at a row and a column, the chain with the
doubled edge into the short last key. -/
def cartB (l i j : Nat) : BPair :=
  if j == i then BPair.ofNat 2
  else if j == i + 1 then
    (if i + 2 == l then (BPair.ofNat 2).swap else (BPair.ofNat 1).swap)
  else if j + 1 == i then (BPair.ofNat 1).swap
  else BPair.unit

private theorem cartB_cell (l i j : Nat) :
    (if j == i then BPair.ofNat 2
      else if (i + 2 == l && j == i + 1) then (BPair.ofNat 2).swap
      else if (j + 1 == i || j == i + 1) then (BPair.ofNat 1).swap
      else BPair.unit) = cartB l i j := by
  show _ = (if (j == i) = true then _ else _)
  cases h1 : (j == i) with
  | true => rfl
  | false =>
    cases h2 : (j == i + 1) with
    | true =>
      rw [Bool.and_true, Bool.or_true]
      rfl
    | false =>
      rw [Bool.and_false, Bool.or_false]
      rfl

/-- The `B` table's Cartan list is the entry function's square. -/
theorem cartB_eq (l : Nat) :
    (sertables.tableB l).cartan
      = ground.matOf l l (fun i j => cartB l i j) :=
  ground.map_congr_all _ _ (fun i =>
    ground.map_congr_all _ _ (fun j => cartB_cell l i j) (List.range l))
    (List.range l)

/-- The `B` Cartan's diagonal entry is two. -/
theorem cartBd (l i : Nat) : cartB l i i = BPair.ofNat 2 := by
  show (if (i == i) = true then _ else _) = _
  rw [ground.eqBeqOf (rfl : i = i)]
  rfl

/-- The `B` Cartan's entry one key up, off the short last edge, is
the swapped one. -/
theorem cartBup1 (l i : Nat) (h : ¬ i + 2 = l) :
    cartB l i (i + 1) = (BPair.ofNat 1).swap := by
  show (if (i + 1 == i) = true then _ else _) = _
  rw [ground.neBeqOf (fun he => (Nat.ne_of_lt (ground.ltAddSucc i 0)) he.symm),
    ground.eqBeqOf (rfl : i + 1 = i + 1), ground.neBeqOf h]
  rfl

/-- The `B` Cartan's entry one key up at the short last edge is the
swapped two. -/
theorem cartBup2 (l i : Nat) (h : i + 2 = l) :
    cartB l i (i + 1) = (BPair.ofNat 2).swap := by
  show (if (i + 1 == i) = true then _ else _) = _
  rw [ground.neBeqOf (fun he => (Nat.ne_of_lt (ground.ltAddSucc i 0)) he.symm),
    ground.eqBeqOf (rfl : i + 1 = i + 1), ground.eqBeqOf h]
  rfl

/-- The `B` Cartan's entry one key down is the swapped one. -/
theorem cartBdn (l i : Nat) :
    cartB l (i + 1) i = (BPair.ofNat 1).swap := by
  show (if (i == i + 1) = true then _ else _) = _
  rw [ground.neBeqOf (Nat.ne_of_lt (ground.ltAddSucc i 0)), ground.neBeqOf (Nat.ne_of_lt (ground.ltAddSucc i 1)),
    ground.eqBeqOf (rfl : i + 1 = i + 1)]
  rfl

/-- The `B` Cartan's entry off the diagonal and its two chain
neighbours is vacant. -/
theorem cartBoff (l i j : Nat) (h1 : ¬ j = i) (h2 : ¬ j = i + 1)
    (h3 : ¬ j + 1 = i) : cartB l i j = BPair.unit := by
  show (if (j == i) = true then _ else _) = _
  rw [ground.neBeqOf h1, ground.neBeqOf h2, ground.neBeqOf h3]
  rfl


/-! ## The `C` Cartan column entries -/

/-- The `C` Cartan entry at a row and a column, the chain with the
doubled edge out of the long last key. -/
def cartC (l i j : Nat) : BPair :=
  if j == i then BPair.ofNat 2
  else if i + 1 == l && j + 2 == l then (BPair.ofNat 2).swap
  else if j + 1 == i || j == i + 1 then (BPair.ofNat 1).swap
  else BPair.unit

/-- The `C` table's Cartan list is the entry function's square. -/
theorem cartC_eq (l : Nat) :
    (sertables.tableC l).cartan
      = ground.matOf l l (fun i j => cartC l i j) :=
  rfl

/-- The `C` Cartan's diagonal entry is two. -/
theorem cartCd (l i : Nat) : cartC l i i = BPair.ofNat 2 := by
  show (if (i == i) = true then _ else _) = _
  rw [ground.eqBeqOf (rfl : i = i)]
  rfl

/-- The `C` Cartan's entry one key down at the long last edge is
the swapped two. -/
theorem cartCdn2 (l i : Nat) (h : i + 2 = l) :
    cartC l (i + 1) i = (BPair.ofNat 2).swap := by
  show (if (i == i + 1) = true then _ else _) = _
  rw [ground.neBeqOf (Nat.ne_of_lt (ground.ltAddSucc i 0)),
    ground.eqBeqOf (show i + 1 + 1 = l from h)]
  rfl

/-- The `C` Cartan's entry one key down, off the long last edge, is
the swapped one. -/
theorem cartCdn1 (l i : Nat) (h : ¬ i + 2 = l) :
    cartC l (i + 1) i = (BPair.ofNat 1).swap := by
  show (if (i == i + 1) = true then _ else _) = _
  rw [ground.neBeqOf (Nat.ne_of_lt (ground.ltAddSucc i 0)),
    ground.neBeqOf (show ¬ i + 1 + 1 = l from h),
    ground.eqBeqOf (rfl : i + 1 = i + 1)]
  rfl

/-- The `C` Cartan's entry one key up is the swapped one. -/
theorem cartCup (l i : Nat) :
    cartC l i (i + 1) = (BPair.ofNat 1).swap := by
  show (if (i + 1 == i) = true then _ else _) = _
  rw [ground.neBeqOf (fun he => (Nat.ne_of_lt (ground.ltAddSucc i 0)) he.symm)]
  cases hb : (i + 1 == l) with
  | true =>
    rw [ground.neBeqOf (fun he : i + 1 + 2 = l =>
        (Nat.ne_of_lt (ground.ltAddSucc (i + 1) 1)) (he.trans (ground.beqEqOf hb).symm).symm),
      ground.eqBeqOf (rfl : i + 1 = i + 1), Bool.or_true]
    rfl
  | false =>
    rw [ground.eqBeqOf (rfl : i + 1 = i + 1), Bool.or_true]
    rfl

/-- The `C` Cartan's entry off the diagonal and its two chain
neighbours is vacant. -/
theorem cartCoff (l i j : Nat) (h1 : ¬ j = i) (h2 : ¬ j + 1 = i)
    (h3 : ¬ j = i + 1) : cartC l i j = BPair.unit := by
  show (if (j == i) = true then _ else _) = _
  rw [ground.neBeqOf h1]
  cases hb : (i + 1 == l) with
  | true =>
    rw [ground.neBeqOf (fun he : j + 2 = l =>
        h2 (Nat.succ.inj (he.trans (ground.beqEqOf hb).symm))),
      ground.neBeqOf h2, ground.neBeqOf h3]
    rfl
  | false =>
    rw [ground.neBeqOf h2, ground.neBeqOf h3]
    rfl


/-! ## The `D` Cartan column entries -/

/-- The `D` Cartan entry at a row and a column, the fork joining
the last two keys to the key before them. -/
def cartD (l i j : Nat) : BPair :=
  if j == i then BPair.ofNat 2
  else if i + 1 == l then
    (if j + 3 == l then (BPair.ofNat 1).swap else BPair.unit)
  else if j + 1 == l then
    (if i + 3 == l then (BPair.ofNat 1).swap else BPair.unit)
  else if j + 1 == i || j == i + 1 then (BPair.ofNat 1).swap
  else BPair.unit

/-- The `D` table's Cartan list is the entry function's square. -/
theorem cartD_eq (l : Nat) :
    (sertables.tableD l).cartan
      = ground.matOf l l (fun i j => cartD l i j) :=
  rfl

/-- Away from the final row and column, D and C have the chain's
Cartan entries. -/
theorem cartD_C_chain (l i j : Nat) (hi : i + 1 < l) (hj : j + 1 < l) :
    cartD l i j = cartC l i j := by
  unfold cartD cartC
  rw [ground.neBeqOf (Nat.ne_of_lt hi), ground.neBeqOf (Nat.ne_of_lt hj)]
  cases h : (j == i) <;> rfl

/-- The `D` Cartan's diagonal entry is two. -/
theorem cartDd (l i : Nat) : cartD l i i = BPair.ofNat 2 := by
  show (if (i == i) = true then _ else _) = _
  rw [ground.eqBeqOf (rfl : i = i)]
  rfl

/-- The `D` Cartan's entry one key up, along the chain below the
fork, is the swapped one. -/
theorem cartDup (l i : Nat) (h2 : ¬ i + 1 = l)
    (h3 : ¬ i + 2 = l) : cartD l i (i + 1) = (BPair.ofNat 1).swap := by
  show (if (i + 1 == i) = true then _ else _) = _
  rw [ground.neBeqOf (fun he => (Nat.ne_of_lt (ground.ltAddSucc i 0)) he.symm),
    ground.neBeqOf h2, ground.neBeqOf (show ¬ i + 1 + 1 = l from h3),
    ground.eqBeqOf (rfl : i + 1 = i + 1), Bool.or_true]
  rfl

/-- The `D` Cartan's entry one key down, along the chain below the
fork, is the swapped one. -/
theorem cartDdn (l i : Nat) (h2 : ¬ i + 2 = l)
    (h3 : ¬ i + 1 = l) : cartD l (i + 1) i = (BPair.ofNat 1).swap := by
  show (if (i == i + 1) = true then _ else _) = _
  rw [ground.neBeqOf (Nat.ne_of_lt (ground.ltAddSucc i 0)),
    ground.neBeqOf (show ¬ i + 1 + 1 = l from h2), ground.neBeqOf h3,
    ground.eqBeqOf (rfl : i + 1 = i + 1)]
  rfl

/-- The `D` Cartan's entry at the last key against the key three
below the rank is the swapped one. -/
theorem cartDfork (l i j : Nat) (h1 : ¬ j = i) (h2 : i + 1 = l)
    (h3 : j + 3 = l) : cartD l i j = (BPair.ofNat 1).swap := by
  show (if (j == i) = true then _ else _) = _
  rw [ground.neBeqOf h1, ground.eqBeqOf h2, ground.eqBeqOf h3]
  rfl

/-- The `D` Cartan's entry at the key three below the rank against
the last key is the swapped one. -/
theorem cartDforkT (l i j : Nat) (h1 : ¬ j = i) (h2 : ¬ i + 1 = l)
    (h3 : j + 1 = l) (h4 : i + 3 = l) :
    cartD l i j = (BPair.ofNat 1).swap := by
  show (if (j == i) = true then _ else _) = _
  rw [ground.neBeqOf h1, ground.neBeqOf h2, ground.eqBeqOf h3,
    ground.eqBeqOf h4]
  rfl

/-- The `D` Cartan's entry off the diagonal, off the fork's two
edges and off the chain's two neighbours is vacant. -/
theorem cartDoff (l i j : Nat) (h1 : ¬ j = i)
    (h2 : i + 1 = l → ¬ j + 3 = l)
    (h3 : ¬ i + 1 = l → j + 1 = l → ¬ i + 3 = l)
    (h4 : ¬ i + 1 = l → ¬ j + 1 = l → ¬ j + 1 = i)
    (h5 : ¬ i + 1 = l → ¬ j + 1 = l → ¬ j = i + 1) :
    cartD l i j = BPair.unit := by
  show (if (j == i) = true then _ else _) = _
  rw [ground.neBeqOf h1]
  cases hb : (i + 1 == l) with
  | true =>
    rw [ground.neBeqOf (h2 (ground.beqEqOf hb))]
    rfl
  | false =>
    have hbn : ¬ i + 1 = l := fun he =>
      Bool.noConfusion (hb.symm.trans (ground.eqBeqOf he))
    cases hc : (j + 1 == l) with
    | true =>
      rw [ground.neBeqOf (h3 hbn (ground.beqEqOf hc))]
      rfl
    | false =>
      have hcn : ¬ j + 1 = l := fun he =>
        Bool.noConfusion (hc.symm.trans (ground.eqBeqOf he))
      rw [ground.neBeqOf (h4 hbn hcn), ground.neBeqOf (h5 hbn hcn)]
      rfl


/-! The series' Cartan rows at the reflecting key: each row sits at
the rank's order and carries the coroot pair two on its own key. -/

/-- The `B` rows' own coroot pair, the stored Cartan row's
diagonal two. -/
theorem cartanBDiag (l i : Nat) (hi : i < l) :
    (ground.getAt BPair.unit
      (ground.getAt [] (sertables.cartanB l) i) i).oneValue
      (BPair.ofNat 2) := by
  unfold sertables.cartanB
  rw [ground.matOf_entry ([] : List BPair) BPair.unit l l _ i i hi hi,
    if_pos (ground.eqBeqOf rfl)]
  exact BPair.oneValue_refl _

/-- The `C` rows' own coroot pair, the stored Cartan row's
diagonal two. -/
theorem cartanCDiag (l i : Nat) (hi : i < l) :
    (ground.getAt BPair.unit
      (ground.getAt [] (sertables.cartanC l) i) i).oneValue
      (BPair.ofNat 2) := by
  unfold sertables.cartanC
  rw [ground.matOf_entry ([] : List BPair) BPair.unit l l _ i i hi hi,
    if_pos (ground.eqBeqOf rfl)]
  exact BPair.oneValue_refl _

/-- The `D` rows' own coroot pair, the stored Cartan row's
diagonal two. -/
theorem cartanDDiag (l i : Nat) (hi : i < l) :
    (ground.getAt BPair.unit
      (ground.getAt [] (sertables.cartanD l) i) i).oneValue
      (BPair.ofNat 2) := by
  unfold sertables.cartanD
  rw [ground.matOf_entry ([] : List BPair) BPair.unit l l _ i i hi hi,
    if_pos (ground.eqBeqOf rfl)]
  exact BPair.oneValue_refl _


/-- The `B` rows off their own key: every further coroot pair of
the stored Cartan row sits at or below the sum's unit. -/
theorem cartanBOff (l i j : Nat) (hi : i < l) (hj : j < l)
    (hij : ¬ j = i) :
    ground.getAt BPair.unit
      (ground.getAt [] (sertables.cartanB l) i) j ≤ BPair.unit := by
  unfold sertables.cartanB
  rw [ground.matOf_entry ([] : List BPair) BPair.unit l l _ i j hi hj,
    if_neg (fun hb : (j == i) = true => hij (ground.beqEqOf hb))]
  by_cases h1 : (i + 2 == l && j == i + 1) = true
  · rw [if_pos h1]
    decide +kernel
  · rw [if_neg h1]
    by_cases h2 : (j + 1 == i || j == i + 1) = true
    · rw [if_pos h2]
      decide +kernel
    · rw [if_neg h2]
      exact ground.leB_refl _

/-- The `C` rows off their own key: every further coroot pair of
the stored Cartan row sits at or below the sum's unit. -/
theorem cartanCOff (l i j : Nat) (hi : i < l) (hj : j < l)
    (hij : ¬ j = i) :
    ground.getAt BPair.unit
      (ground.getAt [] (sertables.cartanC l) i) j ≤ BPair.unit := by
  unfold sertables.cartanC
  rw [ground.matOf_entry ([] : List BPair) BPair.unit l l _ i j hi hj,
    if_neg (fun hb : (j == i) = true => hij (ground.beqEqOf hb))]
  by_cases h1 : (i + 1 == l && j + 2 == l) = true
  · rw [if_pos h1]
    decide +kernel
  · rw [if_neg h1]
    by_cases h2 : (j + 1 == i || j == i + 1) = true
    · rw [if_pos h2]
      decide +kernel
    · rw [if_neg h2]
      exact ground.leB_refl _

/-- The `D` rows off their own key: every further coroot pair of
the stored Cartan row sits at or below the sum's unit. -/
theorem cartanDOff (l i j : Nat) (hi : i < l) (hj : j < l)
    (hij : ¬ j = i) :
    ground.getAt BPair.unit
      (ground.getAt [] (sertables.cartanD l) i) j ≤ BPair.unit := by
  unfold sertables.cartanD
  rw [ground.matOf_entry ([] : List BPair) BPair.unit l l _ i j hi hj,
    if_neg (fun hb : (j == i) = true => hij (ground.beqEqOf hb))]
  by_cases h1 : (i + 1 == l) = true
  · rw [if_pos h1]
    by_cases h2 : (j + 3 == l) = true
    · rw [if_pos h2]
      decide +kernel
    · rw [if_neg h2]
      exact ground.leB_refl _
  · rw [if_neg h1]
    by_cases h2 : (j + 1 == l) = true
    · rw [if_pos h2]
      by_cases h3 : (i + 3 == l) = true
      · rw [if_pos h3]
        decide +kernel
      · rw [if_neg h3]
        exact ground.leB_refl _
    · rw [if_neg h2]
      by_cases h3 : (j + 1 == i || j == i + 1) = true
      · rw [if_pos h3]
        decide +kernel
      · rw [if_neg h3]
        exact ground.leB_refl _


/-- The `D` table's length entry: two at every key. -/
theorem lensD_at (l i : Nat) (hi : i < l) :
    ground.getAt 0 (tableD l).lenNums i = 2 :=
  ground.getAt_replicate 0 2 l i hi

/-! The series' occupancy tier: the θ-coroot's support key off the
unit at every rank (`prop:row`'s single key per series) and the
derived residues at the displayed residue folds' own values
(`con:sertables`).  The θ-folds enter at their entry reads and,
at the floor spellings, at their closed list forms — the `B` fold
one at the first key and two above it against its lengths' short
last key, the `C` fold two below the long last key against its
lengths' mirror, and the `D` fold one at the first key, two
between, and one at each of the fork's keys against the constant
lengths. -/

/-- The `B` table's highest-root fold at a key: the head window
joined to the doubled tail window. -/
theorem thetaB_read (l i : Nat) (h : i < l) :
    ground.getAt 0 (tableB l).thetaFold i
      = (if 0 ≤ i && i < 1 then 1 else 0)
        + ((if 1 ≤ i && i < l then 1 else 0)
          + (if 1 ≤ i && i < l then 1 else 0)) := by
  have e1 : (ind l 0 1).length = l := ind_len l 0 1
  have e2 : (ind l 1 l).length = l := ind_len l 1 l
  have e3 : (List.zipWith (fun a b => a + b) (ind l 1 l)
      (ind l 1 l)).length = l :=
    ground.length_zipWith _ _ _ l e2 e2
  show ground.getAt 0 (List.zipWith (fun a b => a + b)
      (ind l 0 1)
      (List.zipWith (fun a b => a + b) (ind l 1 l)
        (ind l 1 l))) i = _
  rw [ground.getAt_zipWith 0 0 0 (fun a b => a + b) _ _ i
        (by rw [e1]; exact h) (by rw [e3]; exact h),
    ground.getAt_zipWith 0 0 0 (fun a b => a + b) _ _ i
        (by rw [e2]; exact h) (by rw [e2]; exact h),
    ind_at l 0 1 i h, ind_at l 1 l i h]

/-- The `C` table's highest-root fold at a key: the doubled
leading window joined to the last key's own. -/
theorem thetaC_read (l i : Nat) (h : i < l) :
    ground.getAt 0 (tableC l).thetaFold i
      = ((if 0 ≤ i && i < l - 1 then 1 else 0)
          + (if 0 ≤ i && i < l - 1 then 1 else 0))
        + (if l - 1 ≤ i && i < l then 1 else 0) := by
  have e1 : (ind l 0 (l - 1)).length = l := ind_len l 0 (l - 1)
  have e2 : (ind l (l - 1) l).length = l := ind_len l (l - 1) l
  have e3 : (List.zipWith (fun a b => a + b) (ind l 0 (l - 1))
      (ind l 0 (l - 1))).length = l :=
    ground.length_zipWith _ _ _ l e1 e1
  show ground.getAt 0 (List.zipWith (fun a b => a + b)
      (List.zipWith (fun a b => a + b) (ind l 0 (l - 1))
        (ind l 0 (l - 1)))
      (ind l (l - 1) l)) i = _
  rw [ground.getAt_zipWith 0 0 0 (fun a b => a + b) _ _ i
        (by rw [e3]; exact h) (by rw [e2]; exact h),
    ground.getAt_zipWith 0 0 0 (fun a b => a + b) _ _ i
        (by rw [e1]; exact h) (by rw [e1]; exact h),
    ind_at l 0 (l - 1) i h, ind_at l (l - 1) l i h]

/-- The `D` table's highest-root fold at a key, past the fork
rank: the head window, the doubled interior window and the last
two keys' own. -/
theorem thetaD_read (l i : Nat) (h3 : 3 ≤ l) (h : i < l) :
    ground.getAt 0 (tableD l).thetaFold i
      = (if 0 ≤ i && i < 1 then 1 else 0)
        + (((if 1 ≤ i && i < l - 2 then 1 else 0)
            + (if 1 ≤ i && i < l - 2 then 1 else 0))
          + (if l - 2 ≤ i && i < l then 1 else 0)) := by
  have hne : ¬ ((1 + 1 == l) = true) := by
    intro hb
    have he : 1 + 1 = l := ground.beqEqOf hb
    rw [← he] at h3
    exact absurd h3 (Nat.lt_irrefl 2)
  have e1 : (ind l 0 1).length = l := ind_len l 0 1
  have e2 : (ind l 1 (l - 2)).length = l := ind_len l 1 (l - 2)
  have e4 : (ind l (l - 2) l).length = l := ind_len l (l - 2) l
  have e3 : (List.zipWith (fun a b => a + b) (ind l 1 (l - 2))
      (ind l 1 (l - 2))).length = l :=
    ground.length_zipWith _ _ _ l e2 e2
  have e5 : (List.zipWith (fun a b => a + b)
      (List.zipWith (fun a b => a + b) (ind l 1 (l - 2))
        (ind l 1 (l - 2)))
      (ind l (l - 2) l)).length = l :=
    ground.length_zipWith _ _ _ l e3 e4
  have hth : (tableD l).thetaFold
      = List.zipWith (fun a b => a + b) (ind l 0 1)
          (List.zipWith (fun a b => a + b)
            (List.zipWith (fun a b => a + b) (ind l 1 (l - 2))
              (ind l 1 (l - 2)))
            (ind l (l - 2) l)) := by
    show (if (1 + 1 == l) = true then
        List.zipWith (fun a b => a + b) (ind l 0 (l - 2))
          (ind l (l - 1) l)
      else List.zipWith (fun a b => a + b) (ind l 0 1)
          (List.zipWith (fun a b => a + b)
            (List.zipWith (fun a b => a + b) (ind l 1 (l - 2))
              (ind l 1 (l - 2)))
            (ind l (l - 2) l))) = _
    exact if_neg hne
  rw [hth,
    ground.getAt_zipWith 0 0 0 (fun a b => a + b) _ _ i
        (by rw [e1]; exact h) (by rw [e5]; exact h),
    ground.getAt_zipWith 0 0 0 (fun a b => a + b) _ _ i
        (by rw [e3]; exact h) (by rw [e4]; exact h),
    ground.getAt_zipWith 0 0 0 (fun a b => a + b) _ _ i
        (by rw [e2]; exact h) (by rw [e2]; exact h),
    ind_at l 0 1 i h, ind_at l 1 (l - 2) i h,
    ind_at l (l - 2) l i h]

/-- A repeated family's suffix reads at the joined key: the
leading count joined to a key reads the further list at the
key. -/
private theorem getAt_repApp (x : Nat) (v : List Nat) :
    ∀ n m : Nat,
      ground.getAt 0 (List.replicate n x ++ v) (n + m)
        = ground.getAt 0 v m
  | 0, m => by
    show ground.getAt 0 v (0 + m) = ground.getAt 0 v m
    rw [Nat.zero_add]
  | n + 1, m => by
    rw [Nat.add_right_comm n 1 m]
    show ground.getAt 0 (List.replicate n x ++ v) (n + m)
      = ground.getAt 0 v m
    exact getAt_repApp x v n m

/-- The `B` length list at the floor: the twos with the short last
key's one. -/
private theorem lensB_form (g : Nat) :
    (tableB (g + 2)).lenNums = List.replicate (g + 1) 2 ++ [1] := by
  have hlen : (tableB (g + 2)).lenNums.length = g + 2 :=
    ground.length_mapRange _ (g + 2)
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [hlen, ground.length_append, ground.length_replicate]
    rfl
  · intro i hi
    rw [hlen] at hi
    rw [lensB_at (g + 2) i hi]
    by_cases he : i + 1 = g + 2
    · rw [ground.eqBeqOf he, show i = g + 1 from Nat.succ.inj he]
      exact (getAt_repApp 2 [1] (g + 1) 0).symm
    · have hlt : i < g + 1 :=
        Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi)
          (fun h' => he (by rw [h']))
      rw [ground.neBeqOf he,
        ground.getAt_append 0 (List.replicate (g + 1) 2) [1] i,
        ground.length_replicate, if_pos hlt,
        ground.getAt_replicate 0 2 (g + 1) i hlt]
      rfl

/-- The `C` length list at the floor: the ones with the long last
key's two. -/
private theorem lensC_form (g : Nat) :
    (tableC (g + 3)).lenNums = List.replicate (g + 2) 1 ++ [2] := by
  have hlen : (tableC (g + 3)).lenNums.length = g + 3 :=
    ground.length_mapRange _ (g + 3)
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [hlen, ground.length_append, ground.length_replicate]
    rfl
  · intro i hi
    rw [hlen] at hi
    rw [lensC_at (g + 3) i hi]
    by_cases he : i + 1 = g + 3
    · rw [ground.eqBeqOf he, show i = g + 2 from Nat.succ.inj he]
      exact (getAt_repApp 1 [2] (g + 2) 0).symm
    · have hlt : i < g + 2 :=
        Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi)
          (fun h' => he (by rw [h']))
      rw [ground.neBeqOf he,
        ground.getAt_append 0 (List.replicate (g + 2) 1) [2] i,
        ground.length_replicate, if_pos hlt,
        ground.getAt_replicate 0 1 (g + 2) i hlt]
      rfl

/-- The `B` highest root's fold at the floor: one at the first key
and two above it. -/
private theorem thetaB_form (g : Nat) :
    (tableB (g + 2)).thetaFold = 1 :: List.replicate (g + 1) 2 := by
  have hlen : (tableB (g + 2)).thetaFold.length = g + 2 :=
    ground.length_zipWith _ _ _ (g + 2) (ind_len (g + 2) 0 1)
      (ground.length_zipWith _ _ _ (g + 2) (ind_len (g + 2) 1 (g + 2))
        (ind_len (g + 2) 1 (g + 2)))
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [hlen]
    show g + 2 = (List.replicate (g + 1) 2).length + 1
    rw [ground.length_replicate]
  · intro i hi
    rw [hlen] at hi
    rw [thetaB_read (g + 2) i hi]
    match i, hi with
    | 0, _ => rfl
    | j + 1, hj =>
      rw [decide_eq_true hj]
      exact (ground.getAt_replicate 0 2 (g + 1) j
        (Nat.lt_of_succ_lt_succ hj)).symm

/-- The `C` highest root's fold at the floor: two below the long
last key and one at it. -/
private theorem thetaC_form (g : Nat) :
    (tableC (g + 3)).thetaFold = List.replicate (g + 2) 2 ++ [1] := by
  have hlen : (tableC (g + 3)).thetaFold.length = g + 3 :=
    ground.length_zipWith _ _ _ (g + 3)
      (ground.length_zipWith _ _ _ (g + 3) (ind_len (g + 3) 0 (g + 2))
        (ind_len (g + 3) 0 (g + 2)))
      (ind_len (g + 3) (g + 2) (g + 3))
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [hlen, ground.length_append, ground.length_replicate]
    rfl
  · intro i hi
    rw [hlen] at hi
    rw [thetaC_read (g + 3) i hi]
    by_cases he : i + 1 = g + 3
    · rw [show i = g + 2 from Nat.succ.inj he,
        decide_eq_false (show ¬ (g + 2 < g + 3 - 1) from
          Nat.lt_irrefl (g + 2)),
        decide_eq_true (show g + 3 - 1 ≤ g + 2 from Nat.le_refl (g + 2)),
        decide_eq_true (show g + 2 < g + 3 from Nat.le_refl (g + 3))]
      exact (getAt_repApp 2 [1] (g + 2) 0).symm
    · have hlt : i < g + 2 :=
        Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi)
          (fun h' => he (by rw [h']))
      rw [decide_eq_true (show i < g + 3 - 1 from hlt),
        decide_eq_false (show ¬ (g + 3 - 1 ≤ i) from fun hle =>
          Nat.lt_irrefl i (Nat.lt_of_lt_of_le hlt hle)),
        ground.getAt_append 0 (List.replicate (g + 2) 2) [1] i,
        ground.length_replicate, if_pos hlt,
        ground.getAt_replicate 0 2 (g + 2) i hlt]
      rfl

/-- The `D` highest root's fold at the floor: one at the first key,
two between, and one at each of the fork's keys. -/
private theorem thetaD_form (g : Nat) :
    (tableD (g + 4)).thetaFold
      = 1 :: (List.replicate (g + 1) 2 ++ [1, 1]) := by
  have hlen : (tableD (g + 4)).thetaFold.length = g + 4 :=
    ground.length_zipWith _ _ _ (g + 4) (ind_len (g + 4) 0 1)
      (ground.length_zipWith _ _ _ (g + 4)
        (ground.length_zipWith _ _ _ (g + 4) (ind_len (g + 4) 1 (g + 2))
          (ind_len (g + 4) 1 (g + 2)))
        (ind_len (g + 4) (g + 2) (g + 4)))
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [hlen]
    show g + 4 = (List.replicate (g + 1) 2 ++ [1, 1]).length + 1
    rw [ground.length_append, ground.length_replicate]
    rfl
  · intro i hi
    rw [hlen] at hi
    rw [thetaD_read (g + 4) i (Nat.le_add_left 3 (g + 1)) hi]
    match i, hi with
    | 0, _ => rfl
    | j + 1, hj =>
      cases Nat.lt_or_ge (j + 1) (g + 2) with
      | inl hlt =>
        rw [decide_eq_true (show j + 1 < g + 4 - 2 from hlt),
          decide_eq_false (show ¬ (g + 4 - 2 ≤ j + 1) from fun hle =>
            Nat.lt_irrefl (j + 1) (Nat.lt_of_lt_of_le hlt hle))]
        have hjg : j < g + 1 := Nat.lt_of_succ_lt_succ hlt
        rw [show ground.getAt 0
            (1 :: (List.replicate (g + 1) 2 ++ [1, 1])) (j + 1)
            = ground.getAt 0 (List.replicate (g + 1) 2 ++ [1, 1]) j
            from rfl,
          ground.getAt_append 0 (List.replicate (g + 1) 2) [1, 1] j,
          ground.length_replicate, if_pos hjg,
          ground.getAt_replicate 0 2 (g + 1) j hjg]
        rfl
      | inr hge =>
        obtain ⟨m, hm⟩ := Nat.le.dest (Nat.le_of_succ_le_succ hge)
        have hj2 : m < 2 := by
          have h4 : g + 1 + (m + 2) ≤ g + 1 + 3 := by
            rw [← Nat.add_assoc]
            show g + 1 + m + 1 < g + 4
            rw [hm]
            exact hj
          exact Nat.le_of_succ_le_succ (ground.leCancelL (g + 1) h4)
        rw [decide_eq_false (show ¬ (j + 1 < g + 4 - 2) from fun hlt =>
            Nat.lt_irrefl (j + 1) (Nat.lt_of_lt_of_le hlt hge)),
          decide_eq_true (show g + 4 - 2 ≤ j + 1 from hge),
          decide_eq_true (show j + 1 < g + 4 from hj),
          show ground.getAt 0
            (1 :: (List.replicate (g + 1) 2 ++ [1, 1])) (j + 1)
            = ground.getAt 0 [1, 1] m from by
              rw [show j = g + 1 + m from hm.symm]
              exact getAt_repApp 2 [1, 1] (g + 1) m]
        match m, hj2 with
        | 0, _ => rfl
        | 1, _ => rfl
        | m + 2, h2 =>
          exact absurd
            (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h2))
            (Nat.not_lt_zero m)

/-- A matched repeated prefix folds off at its count: the dot of
two joins reads the count's scale with the tails' own fold. -/
private theorem dotRepApp (a b : Nat) : ∀ (n : Nat) (X Y : List Nat),
    ground.dotNat (List.replicate n a ++ X) (List.replicate n b ++ Y)
      = n * (a * b) + ground.dotNat X Y
  | 0, X, Y => by
    show ground.dotNat X Y = 0 * (a * b) + ground.dotNat X Y
    rw [Nat.zero_mul, Nat.zero_add]
  | n + 1, X, Y => by
    show a * b + ground.dotNat (List.replicate n a ++ X)
        (List.replicate n b ++ Y)
      = (n + 1) * (a * b) + ground.dotNat X Y
    rw [dotRepApp a b n X Y,
      show (n + 1) * (a * b) = n * (a * b) + a * b from
        Nat.succ_mul n (a * b),
      ← Nat.add_assoc (a * b) (n * (a * b)) (ground.dotNat X Y),
      Nat.add_comm (a * b) (n * (a * b))]

/-- The `B` residue fold's value at the floor, cleared. -/
private theorem valB : ∀ g : Nat, 2 + (g * 4 + 2) = (2 * (g + 1)) * 2
  | 0 => rfl
  | g + 1 => by
    show 2 + ((g + 1) * 4 + 2) = (2 * (g + 1) + 2) * 2
    rw [show (2 * (g + 1) + 2) * 2 = (2 * (g + 1)) * 2 + 4 from by
        rw [show (2 * (g + 1) + 2) * 2 = (2 * (g + 1) + 1) * 2 + 2 from
            Nat.succ_mul (2 * (g + 1) + 1) 2,
          show (2 * (g + 1) + 1) * 2 = (2 * (g + 1)) * 2 + 2 from
            Nat.succ_mul (2 * (g + 1)) 2],
      ← valB g, Nat.add_assoc 2 (g * 4 + 2) 4,
      show (g + 1) * 4 = g * 4 + 4 from Nat.succ_mul g 4]

/-- The `D` residue fold's value at the floor, cleared. -/
private theorem valD : ∀ g : Nat, 2 + (g * 4 + 8) = (2 * g + 5) * 2
  | 0 => rfl
  | g + 1 => by
    show 2 + ((g + 1) * 4 + 8) = (2 * g + 2 + 5) * 2
    rw [show (2 * g + 2 + 5) * 2 = (2 * g + 5) * 2 + 4 from by
        rw [show (2 * g + 2 + 5) * 2 = (2 * g + 6) * 2 + 2 from
            Nat.succ_mul (2 * g + 6) 2,
          show (2 * g + 6) * 2 = (2 * g + 5) * 2 + 2 from
            Nat.succ_mul (2 * g + 5) 2],
      ← valD g, Nat.add_assoc 2 (g * 4 + 8) 4,
      show (g + 1) * 4 = g * 4 + 4 from Nat.succ_mul g 4]

/-- The three-head fold read at a key: at matched counts with every
deeper row entry the unit, the fold reads its three head terms'
sum. -/
private theorem zipHead3 (j : Nat) : ∀ (f : List Nat)
    (M : List (List BPair)), M.length = f.length →
    (∀ k, 3 ≤ k → k < f.length →
      (getAt BPair.unit (getAt [] M k) j).oneValue BPair.unit) →
    (BPair.sum (List.zipWith
      (fun c row => BPair.ofNat c * getAt BPair.unit row j)
      f M)).oneValue
      (BPair.ofNat (getAt 0 f 0) * getAt BPair.unit (getAt [] M 0) j
        + (BPair.ofNat (getAt 0 f 1) * getAt BPair.unit (getAt [] M 1) j
          + BPair.ofNat (getAt 0 f 2)
            * getAt BPair.unit (getAt [] M 2) j))
  | [], [], _, _ =>
    BPair.oneValue_symm (BPair.oneValue_trans
      (BPair.add_congr (BPair.unit_mul _)
        (BPair.oneValue_trans
          (BPair.add_congr (BPair.unit_mul _) (BPair.unit_mul _))
          (BPair.unit_add _)))
      (BPair.unit_add _))
  | [], _ :: _, hl, _ => Nat.noConfusion hl
  | [_], [], hl, _ => Nat.noConfusion hl
  | [_], [_], _, _ => by
    refine BPair.oneValue_trans (BPair.sum_cons _ _) ?_
    refine BPair.add_congr (BPair.oneValue_refl _) ?_
    exact BPair.oneValue_symm (BPair.oneValue_trans
      (BPair.add_congr (BPair.unit_mul _) (BPair.unit_mul _))
      (BPair.unit_add _))
  | [_], _ :: _ :: _, hl, _ => Nat.noConfusion (Nat.succ.inj hl)
  | [_, _], [], hl, _ => Nat.noConfusion hl
  | [_, _], [_], hl, _ => Nat.noConfusion (Nat.succ.inj hl)
  | [_, _], [_, _], _, _ => by
    refine BPair.oneValue_trans (BPair.sum_cons _ _) ?_
    refine BPair.add_congr (BPair.oneValue_refl _) ?_
    refine BPair.oneValue_trans (BPair.sum_cons _ _) ?_
    refine BPair.add_congr (BPair.oneValue_refl _) ?_
    exact BPair.oneValue_symm (BPair.unit_mul _)
  | [_, _], _ :: _ :: _ :: _, hl, _ =>
    Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hl))
  | _ :: _ :: _ :: _, [], hl, _ => Nat.noConfusion hl
  | _ :: _ :: _ :: _, [_], hl, _ => Nat.noConfusion (Nat.succ.inj hl)
  | _ :: _ :: _ :: _, [_, _], hl, _ =>
    Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hl))
  | c0 :: c1 :: c2 :: f, r0 :: r1 :: r2 :: M, _, hent => by
    show (BPair.sum ((BPair.ofNat c0 * getAt BPair.unit r0 j)
      :: (BPair.ofNat c1 * getAt BPair.unit r1 j)
      :: (BPair.ofNat c2 * getAt BPair.unit r2 j)
      :: List.zipWith
        (fun c row => BPair.ofNat c * getAt BPair.unit row j)
        f M)).oneValue
      (BPair.ofNat c0 * getAt BPair.unit r0 j
        + (BPair.ofNat c1 * getAt BPair.unit r1 j
          + BPair.ofNat c2 * getAt BPair.unit r2 j))
    refine BPair.oneValue_trans (BPair.sum_cons _ _) ?_
    refine BPair.add_congr (BPair.oneValue_refl _) ?_
    refine BPair.oneValue_trans (BPair.sum_cons _ _) ?_
    refine BPair.add_congr (BPair.oneValue_refl _) ?_
    refine BPair.oneValue_trans (BPair.sum_cons _ _) ?_
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
      (zipTermUnit j f M (fun k hk =>
        BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat (getAt 0 f k)))
            (hent (k + 3) (Nat.le_add_left 3 k)
              (Nat.succ_lt_succ (Nat.succ_lt_succ
                (Nat.succ_lt_succ hk)))))
          (BPair.mul_unit _)))) ?_
    exact BPair.add_unit _

/-- The `B` table's θ-coroot at the support key sits off the unit:
two at the floor rank, the doubled edge's read, and one above it,
the first and third rows' partners against the second row's two,
the deeper rows' entries the unit (`prop:row`'s single key at the
`B`-series). -/
theorem corootB_off (g : Nat) :
    ¬ (corootAt (tableB (g + 2)) (tableB (g + 2)).thetaFold 1).oneValue
      BPair.unit :=
  match g with
  | 0 => by decide +kernel
  | g + 1 => fun hu => by
    have hflen : ((tableB (g + 1 + 2)).thetaFold).length = g + 1 + 2 := by
      rw [thetaB_form (g + 1)]
      show (List.replicate (g + 1 + 1) 2).length + 1 = g + 1 + 2
      rw [ground.length_replicate]
    have hsum : (corootAt (tableB (g + 1 + 2))
        (tableB (g + 1 + 2)).thetaFold 1).oneValue
        (BPair.ofNat 1 * m1
          + (BPair.ofNat 2 * b2 + BPair.ofNat 2 * m1)) := by
      refine BPair.oneValue_trans
        (zipHead3 1 (tableB (g + 1 + 2)).thetaFold
          (ground.matOf (g + 1 + 2) (g + 1 + 2) _)
          (by rw [ground.matOf_length, hflen])
          (fun k hk3 hkl => ?_)) ?_
      · obtain ⟨n, hn⟩ := Nat.le.dest hk3
        have hk : k = n + 3 := by
          rw [← hn, Nat.add_comm]
        subst hk
        rw [hflen] at hkl
        rw [ground.matOf_entry [] BPair.unit (g + 1 + 2) (g + 1 + 2) _
            (n + 3) 1 hkl (Nat.succ_lt_succ (Nat.succ_pos _)),
          show ((1 : Nat) == n + 3 + 1) = false from rfl, Bool.and_false]
        exact BPair.oneValue_refl _
      · rw [thetaB_form (g + 1),
          ground.matOf_entry [] BPair.unit (g + 1 + 2) (g + 1 + 2) _ 0 1
            (Nat.succ_pos _) (Nat.succ_lt_succ (Nat.succ_pos _)),
          ground.matOf_entry [] BPair.unit (g + 1 + 2) (g + 1 + 2) _ 1 1
            (Nat.succ_lt_succ (Nat.succ_pos _))
            (Nat.succ_lt_succ (Nat.succ_pos _)),
          ground.matOf_entry [] BPair.unit (g + 1 + 2) (g + 1 + 2) _ 2 1
            (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos _)))
            (Nat.succ_lt_succ (Nat.succ_pos _)),
          show ((1 : Nat) == 2 + 1) = false from rfl, Bool.and_false]
        exact BPair.oneValue_refl _
    exact absurd
      (BPair.oneValue_trans (BPair.oneValue_symm hsum) hu)
      (by decide +kernel)

/-- The `C` table's θ-coroot at the support key sits off the unit:
the first row's two against the second row's balance partner, the
third row's entry and the deeper rows' the unit (`prop:row`'s
single key at the `C`-series). -/
theorem corootC_off (g : Nat) :
    ¬ (corootAt (tableC (g + 3)) (tableC (g + 3)).thetaFold 0).oneValue
      BPair.unit := fun hu => by
  have hflen : ((tableC (g + 3)).thetaFold).length = g + 3 := by
    rw [thetaC_form g, ground.length_append, ground.length_replicate]
    rfl
  have hsum : (corootAt (tableC (g + 3))
      (tableC (g + 3)).thetaFold 0).oneValue
      (BPair.ofNat 2 * b2 + (BPair.ofNat 2 * m1 + BPair.unit)) := by
    refine BPair.oneValue_trans
      (zipHead3 0 (tableC (g + 3)).thetaFold
        (ground.matOf (g + 3) (g + 3) _)
        (by rw [ground.matOf_length, hflen])
        (fun k hk3 hkl => ?_)) ?_
    · obtain ⟨n, hn⟩ := Nat.le.dest hk3
      have hk : k = n + 3 := by
        rw [← hn, Nat.add_comm]
      subst hk
      rw [hflen] at hkl
      rw [ground.matOf_entry [] BPair.unit (g + 3) (g + 3) _
          (n + 3) 0 hkl (Nat.succ_pos _),
        show ((0 : Nat) + 2 == g + 3) = false from rfl,
        Bool.and_false (n + 3 + 1 == g + 3)]
      exact BPair.oneValue_refl _
    · rw [thetaC_form g,
        ground.matOf_entry [] BPair.unit (g + 3) (g + 3) _ 0 0
          (Nat.succ_pos _) (Nat.succ_pos _),
        ground.matOf_entry [] BPair.unit (g + 3) (g + 3) _ 1 0
          (Nat.succ_lt_succ (Nat.succ_pos _)) (Nat.succ_pos _),
        ground.matOf_entry [] BPair.unit (g + 3) (g + 3) _ 2 0
          (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos _)))
          (Nat.succ_pos _),
        show ((0 : Nat) + 2 == g + 3) = false from rfl,
        Bool.and_false (2 + 1 == g + 3)]
      exact BPair.add_congr (BPair.oneValue_refl _)
        (BPair.add_congr (BPair.oneValue_refl _) (BPair.mul_unit _))
  exact absurd
    (BPair.oneValue_trans (BPair.oneValue_symm hsum) hu)
    (by decide +kernel)

/-- The `D` table's θ-coroot at the support key sits off the unit,
the read one at every rank: at the floor the fork's two rows'
partners join the head pair's read at single fold coefficients,
above it the first and third rows' partners sit against the second
row's two with the fork's and the deeper rows' entries the unit
(`prop:row`'s single key at the `D`-series). -/
theorem corootD_off (g : Nat) :
    ¬ (corootAt (tableD (g + 4)) (tableD (g + 4)).thetaFold 1).oneValue
      BPair.unit :=
  match g with
  | 0 => by decide +kernel
  | g + 1 => fun hu => by
    have hflen : ((tableD (g + 1 + 4)).thetaFold).length = g + 1 + 4 := by
      rw [thetaD_form (g + 1)]
      show (List.replicate (g + 1 + 1) 2 ++ [1, 1]).length + 1 = g + 1 + 4
      rw [ground.length_append, ground.length_replicate]
      rfl
    have hsum : (corootAt (tableD (g + 1 + 4))
        (tableD (g + 1 + 4)).thetaFold 1).oneValue
        (BPair.ofNat 1 * m1
          + (BPair.ofNat 2 * b2 + BPair.ofNat 2 * m1)) := by
      refine BPair.oneValue_trans
        (zipHead3 1 (tableD (g + 1 + 4)).thetaFold
          (ground.matOf (g + 1 + 4) (g + 1 + 4) _)
          (by rw [ground.matOf_length, hflen])
          (fun k hk3 hkl => ?_)) ?_
      · obtain ⟨n, hn⟩ := Nat.le.dest hk3
        have hk : k = n + 3 := by
          rw [← hn, Nat.add_comm]
        subst hk
        rw [hflen] at hkl
        rw [ground.matOf_entry [] BPair.unit (g + 1 + 4) (g + 1 + 4) _
          (n + 3) 1 hkl (Nat.succ_lt_succ (Nat.succ_pos _))]
        cases hx : (n + 3 + 1 == g + 1 + 4) with
        | false => exact BPair.oneValue_refl _
        | true => exact BPair.oneValue_refl _
      · rw [thetaD_form (g + 1),
          ground.matOf_entry [] BPair.unit (g + 1 + 4) (g + 1 + 4) _ 0 1
            (Nat.succ_pos _) (Nat.succ_lt_succ (Nat.succ_pos _)),
          ground.matOf_entry [] BPair.unit (g + 1 + 4) (g + 1 + 4) _ 1 1
            (Nat.succ_lt_succ (Nat.succ_pos _))
            (Nat.succ_lt_succ (Nat.succ_pos _)),
          ground.matOf_entry [] BPair.unit (g + 1 + 4) (g + 1 + 4) _ 2 1
            (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos _)))
            (Nat.succ_lt_succ (Nat.succ_pos _))]
        exact BPair.oneValue_refl _
    exact absurd
      (BPair.oneValue_trans (BPair.oneValue_symm hsum) hu)
      (by decide +kernel)

/-- The `B` residue at the floor reads the displayed fold's value
at every rank, `r = 2ℓ - 2` at `ℓ = g + 2` (`con:sertables`' `B`
residue fold), the division's witnessed cancel. -/
theorem residue_tableB (g : Nat) : residue (tableB (g + 2)) = 2 * (g + 1) := by
  show ground.dotNat (tableB (g + 2)).thetaFold (tableB (g + 2)).lenNums
      / (2 * 1) = 2 * (g + 1)
  rw [thetaB_form g, lensB_form g]
  show (1 * 2 + ground.dotNat (List.replicate (g + 1) 2)
      (List.replicate g 2 ++ [1])) / (2 * 1) = 2 * (g + 1)
  rw [show List.replicate (g + 1) 2 = List.replicate g 2 ++ [2] from
      (ground.replicate_snoc 2 g).symm,
    dotRepApp 2 2 g [2] [1]]
  show (2 + (g * 4 + 2)) / (2 * 1) = 2 * (g + 1)
  rw [valB g]
  exact ground.divMulSelf (2 * (g + 1)) 2 (Nat.zero_lt_succ 1)

/-- The `B` residue's occupancy at every rank, the value read's
own. -/
theorem residue_tableB_pos (g : Nat) : 0 < residue (tableB (g + 2)) := by
  rw [residue_tableB g]
  exact Nat.succ_pos _

/-- The `C` residue at the floor reads the displayed fold's value
at every rank, `r = ℓ` at `ℓ = g + 3` (`con:sertables`' `C`
residue fold), the division's witnessed cancel. -/
theorem residue_tableC (g : Nat) : residue (tableC (g + 3)) = g + 3 := by
  show ground.dotNat (tableC (g + 3)).thetaFold (tableC (g + 3)).lenNums
      / (2 * 1) = g + 3
  rw [thetaC_form g, lensC_form g, dotRepApp 2 1 (g + 2) [1] [2]]
  show ((g + 2) * 2 + 2) / (2 * 1) = g + 3
  rw [show (g + 2) * 2 + 2 = (g + 3) * 2 from (Nat.succ_mul (g + 2) 2).symm]
  exact ground.divMulSelf (g + 3) 2 (Nat.zero_lt_succ 1)

/-- The `C` residue's occupancy at every rank, the value read's
own. -/
theorem residue_tableC_pos (g : Nat) : 0 < residue (tableC (g + 3)) := by
  rw [residue_tableC g]
  exact Nat.succ_pos _

/-- The `D` residue at the floor reads the displayed fold's value
at every rank, `r = 2ℓ - 3` at `ℓ = g + 4` (`con:sertables`' `D`
residue fold), the division's witnessed cancel. -/
theorem residue_tableD (g : Nat) : residue (tableD (g + 4)) = 2 * g + 5 := by
  show ground.dotNat (tableD (g + 4)).thetaFold (tableD (g + 4)).lenNums
      / (2 * 1) = 2 * g + 5
  rw [thetaD_form g]
  show (1 * 2 + ground.dotNat (List.replicate (g + 1) 2 ++ [1, 1])
      (List.replicate (g + 1 + 2) 2)) / (2 * 1) = 2 * g + 5
  rw [ground.replicate_append 2 (g + 1) 2,
    dotRepApp 2 2 (g + 1) [1, 1] (List.replicate 2 2),
    show (g + 1) * (2 * 2) = g * 4 + 4 from Nat.succ_mul g 4]
  show (2 + (g * 4 + 8)) / (2 * 1) = 2 * g + 5
  rw [valD g]
  exact ground.divMulSelf (2 * g + 5) 2 (Nat.zero_lt_succ 1)

/-- The `D` residue's occupancy at every rank, the value read's
own. -/
theorem residue_tableD_pos (g : Nat) : 0 < residue (tableD (g + 4)) := by
  rw [residue_tableD g]
  exact Nat.succ_pos _

/-! The fixed members' coordinate families and the fold descent. -/

private def isPosB (x : BPair) : Bool :=
  match x.side with
  | .gt _ _ => true
  | .lt _ _ => false
  | .eq _ => false

private def eqB (x y : BPair) : Bool :=
  if x.oneValue y then true else false

private def allUnit : List BPair → Bool
  | [] => true
  | a :: t => a.isUnitRep && allUnit t

private def findPosIdx : List BPair → Nat → Option Nat
  | [], _ => none
  | a :: t, k => if isPosB a then some k else findPosIdx t (k + 1)

private def subRow (v w : List BPair) : List BPair :=
  List.zipWith (fun a b => (a + b.swap).norm) v w

private def descGo (g : List (List BPair)) :
    Nat → List BPair → List Nat → List Nat
  | 0, dv, acc => if allUnit dv then acc else []
  | fuel + 1, dv, acc =>
    if allUnit dv then acc
    else
      match findPosIdx dv 0 with
      | some j => descGo g fuel (subRow dv (getAt [] g j)) (bumpAt j acc)
      | none => []

/-- The fold descent (`con:sertables`' fixed-member walk), run for
the whole family at one Gram read: the walk's state is the member's
dot list against the simples, a step subtracts the positive-dot
key's Gram row and collects the fold witness, and the walk closes
at the unit reads, the last step the ending simple's own key (the
simples' mutual dots off the diagonal sit at or below the unit, so
a simple's one positive read is its own); a starved or stuck walk's
output is caught by `descentRead`'s round trip. -/
def descentAll (simples : List (List BPair)) (fuel : Nat)
    (fam : List (List BPair)) : List (List Nat) :=
  let g := simples.map (fun s => simples.map (fun s' => elim.dotN s s'))
  fam.map (fun v =>
    descGo g fuel (simples.map (fun s => elim.dotN v s))
      (simples.map (fun _ => 0)))

/-- A fold's coordinate content, `Σ_k f_k α_k` at the coordinate
simples. -/
def foldCoords (simples : List (List BPair)) (f : List Nat) :
    List BPair :=
  match simples with
  | [] => []
  | s :: _ =>
    (List.zipWith (fun c => elim.vecScale (BPair.ofNat c)) f simples).foldl
      elim.vecAdd (s.map (fun _ => BPair.unit))

/-- The family read at one traversal, the table's own positive
list against the displayed coordinate family, three reads off one
forcing: the counts agree, every stored fold reads back to its
family member through `foldCoords` (the descent's round trip, the
fold witness's whole verification), and the root fold's coroot
reads `(2ρ)(α_i^∨) = 2` hold at every simple index — the round
trip carries each fold's key count beside it (`foldCoords` reads
the fold against the simples at matched keys alone), and a fold of
the unit family refuses at the round trip against its occupied
member, so the occupancy and shape clauses ride the same read. -/
def famRead (t : Table) (simples fam : List (List BPair)) : Prop :=
  (let folds := t.posFolds
   (folds.length == fam.length)
     && ((List.zipWith (fun f v =>
       decide (ground.matchedOV ground.bpairRead
         (foldCoords simples f) v) && f.length == t.rank)
       folds fam).all (fun b => b))
     && ((List.range t.rank).all (fun j =>
       if (BPair.sum (folds.map (fun f => corootAt t f j))).oneValue
           (BPair.ofNat 2)
       then true else false))) = true

instance instSertables1 (t : Table) (s fam : List (List BPair)) :
    Decidable (famRead t s fam) :=
  inferInstanceAs (Decidable (_ = _))

private def pB (n : Nat) : BPair := BPair.ofNat n
private def mB (n : Nat) : BPair := (BPair.ofNat n).swap

/-- The three `E`-members' shared eight doubled coordinates: the
displayed simple list, `α_1` at the first and eighth keys against
the six between, `α_2` two on the first two keys, and the
letter-pair moves. -/
def e8Simples : List (List BPair) :=
  [pB 1, mB 1, mB 1, mB 1, mB 1, mB 1, mB 1, pB 1]
    :: [pB 2, pB 2, BPair.unit, BPair.unit, BPair.unit, BPair.unit,
        BPair.unit, BPair.unit]
    :: ground.matOf 6 8 (fun k j =>
        if j == k then m2 else if j == k + 1 then b2 else BPair.unit)

/-- The `E_8` coordinate families: the difference, sum and half-sum
families at the displayed counts `28 + 28 + 64`. -/
def e8Family : List (List BPair) :=
  (places.pairsOf 8).map (fun p => (List.range 8).map (fun j =>
      if j == p.1 then m2 else if j == p.2 then b2 else BPair.unit))
    ++ (places.pairsOf 8).map (fun p => (List.range 8).map (fun j =>
        if j == p.1 || j == p.2 then b2 else BPair.unit))
    ++ (List.range 128).filterMap (fun n =>
        let v := (List.range 7).map (fun k =>
          if baseDigit 2 k n == 1 then mB 1 else pB 1)
        if (v.filter (fun x => eqB x (mB 1))).length % 2 == 0 then
          some (v ++ [pB 1])
        else none)

/-- A member's read at the `E_7` selection, the seventh and eighth
entries' sum of equal members. -/
def selE7 (v : List BPair) : Bool :=
  eqB (getAt BPair.unit v 6 + getAt BPair.unit v 7) BPair.unit

/-- A member's read at the further `E_6` selection, the sixth and
eighth entries' sum of equal members as well. -/
def selE6 (v : List BPair) : Bool :=
  selE7 v && eqB (getAt BPair.unit v 5 + getAt BPair.unit v 7) BPair.unit

/-- The `F_4` displayed coordinates: four keys at the doubled
scale, the simple list as displayed. -/
def f4Simples : List (List BPair) :=
  [[BPair.unit, b2, m2, BPair.unit],
   [BPair.unit, BPair.unit, b2, m2],
   [BPair.unit, BPair.unit, BPair.unit, b2],
   [pB 1, mB 1, mB 1, mB 1]]

/-- The `F_4` coordinate families: the singles, the difference and
sum family, and the half-sums, at the displayed counts
`4 + 12 + 8`. -/
def f4Family : List (List BPair) :=
  ground.matOf 4 4 (fun a j => if j == a then b2 else BPair.unit)
    ++ (places.pairsOf 4).flatMap (fun p =>
        [(List.range 4).map (fun j =>
            if j == p.1 then b2 else if j == p.2 then m2 else BPair.unit),
         (List.range 4).map (fun j =>
            if j == p.1 || j == p.2 then b2 else BPair.unit)])
    ++ (List.range 8).map (fun n =>
        pB 1 :: (List.range 3).map (fun k =>
          if baseDigit 2 k n == 1 then mB 1 else pB 1))

/-- The `E`-members' edge lists, the chain `1–3–4–5–6` with the
branch `2–4`, grown by `7` and by `7–8`. -/
def slCartan (n : Nat) (edges : List (Nat × Nat)) :
    List (List BPair) :=
  ground.matOf n n (fun i j =>
    if j == i then b2
    else if edges.any (fun e =>
        (e.1 == i && e.2 == j) || (e.1 == j && e.2 == i)) then m1
    else BPair.unit)

def edgesE6 : List (Nat × Nat) := [(0, 2), (2, 3), (3, 4), (4, 5), (1, 3)]
def edgesE7 : List (Nat × Nat) := edgesE6 ++ [(5, 6)]
def edgesE8 : List (Nat × Nat) := edgesE7 ++ [(6, 7)]

/-- The `G_2` table: the displayed edge reads, lengths `[2:3]` and
`2` at the cleared second member three, and the six displayed
folds. -/
def tableG2 : Table :=
  ⟨2, [2, 6], 3, [[b2, m1], [m3, b2]],
   [[1, 0], [0, 1], [1, 1], [2, 1], [3, 1], [3, 2]], [3, 2]⟩

/-- The `F_4` table: the chain at the middle edge doubled toward
the short pair, the displayed lengths, and the positive list the
coordinate families' descent. -/
def tableF4 : Table :=
  ⟨4, [2, 2, 1, 1], 1,
   [[b2, m1, BPair.unit, BPair.unit],
    [m1, b2, m2, BPair.unit],
    [BPair.unit, m1, b2, m1],
    [BPair.unit, BPair.unit, m1, b2]],
   descentAll f4Simples 32 f4Family, [2, 3, 4, 2]⟩

/-- The `E_6` positive list at its simple folds, the descent's output committed literal. -/
def posE6 : List (List Nat) :=
  [[0,0,1,0,0,0], [0,0,1,1,0,0], [0,0,0,1,0,0], [0,0,1,1,1,0],
   [0,0,0,1,1,0], [0,0,0,0,1,0], [0,0,1,1,1,1], [0,0,0,1,1,1],
   [0,0,0,0,1,1], [0,0,0,0,0,1], [0,1,0,0,0,0], [0,1,0,1,0,0],
   [0,1,1,1,0,0], [0,1,0,1,1,0], [0,1,1,1,1,0], [0,1,1,2,1,0],
   [0,1,0,1,1,1], [0,1,1,1,1,1], [0,1,1,2,1,1], [0,1,1,2,2,1],
   [1,2,2,3,2,1], [1,1,2,3,2,1], [1,1,2,2,2,1], [1,1,1,2,2,1],
   [1,1,2,2,1,1], [1,1,1,2,1,1], [1,1,1,1,1,1], [1,0,1,1,1,1],
   [1,1,2,2,1,0], [1,1,1,2,1,0], [1,1,1,1,1,0], [1,0,1,1,1,0],
   [1,1,1,1,0,0], [1,0,1,1,0,0], [1,0,1,0,0,0], [1,0,0,0,0,0]]

/-- The `E_7` positive list at its simple folds, the descent's output committed literal. -/
def posE7 : List (List Nat) :=
  [[0,0,1,0,0,0,0], [0,0,1,1,0,0,0], [0,0,0,1,0,0,0], [0,0,1,1,1,0,0],
   [0,0,0,1,1,0,0], [0,0,0,0,1,0,0], [0,0,1,1,1,1,0], [0,0,0,1,1,1,0],
   [0,0,0,0,1,1,0], [0,0,0,0,0,1,0], [0,0,1,1,1,1,1], [0,0,0,1,1,1,1],
   [0,0,0,0,1,1,1], [0,0,0,0,0,1,1], [0,0,0,0,0,0,1], [2,2,3,4,3,2,1],
   [0,1,0,0,0,0,0], [0,1,0,1,0,0,0], [0,1,1,1,0,0,0], [0,1,0,1,1,0,0],
   [0,1,1,1,1,0,0], [0,1,1,2,1,0,0], [0,1,0,1,1,1,0], [0,1,1,1,1,1,0],
   [0,1,1,2,1,1,0], [0,1,1,2,2,1,0], [0,1,0,1,1,1,1], [0,1,1,1,1,1,1],
   [0,1,1,2,1,1,1], [0,1,1,2,2,1,1], [0,1,1,2,2,2,1], [1,2,3,4,3,2,1],
   [1,2,2,4,3,2,1], [1,2,2,3,3,2,1], [1,1,2,3,3,2,1], [1,2,2,3,2,2,1],
   [1,1,2,3,2,2,1], [1,1,2,2,2,2,1], [1,1,1,2,2,2,1], [1,2,2,3,2,1,1],
   [1,1,2,3,2,1,1], [1,1,2,2,2,1,1], [1,1,1,2,2,1,1], [1,1,2,2,1,1,1],
   [1,1,1,2,1,1,1], [1,1,1,1,1,1,1], [1,0,1,1,1,1,1], [1,2,2,3,2,1,0],
   [1,1,2,3,2,1,0], [1,1,2,2,2,1,0], [1,1,1,2,2,1,0], [1,1,2,2,1,1,0],
   [1,1,1,2,1,1,0], [1,1,1,1,1,1,0], [1,0,1,1,1,1,0], [1,1,2,2,1,0,0],
   [1,1,1,2,1,0,0], [1,1,1,1,1,0,0], [1,0,1,1,1,0,0], [1,1,1,1,0,0,0],
   [1,0,1,1,0,0,0], [1,0,1,0,0,0,0], [1,0,0,0,0,0,0]]

/-- The `E_8` positive list at its simple folds, the descent's output committed literal. -/
def posE8 : List (List Nat) :=
  [[0,0,1,0,0,0,0,0], [0,0,1,1,0,0,0,0], [0,0,0,1,0,0,0,0],
   [0,0,1,1,1,0,0,0], [0,0,0,1,1,0,0,0], [0,0,0,0,1,0,0,0],
   [0,0,1,1,1,1,0,0], [0,0,0,1,1,1,0,0], [0,0,0,0,1,1,0,0],
   [0,0,0,0,0,1,0,0], [0,0,1,1,1,1,1,0], [0,0,0,1,1,1,1,0],
   [0,0,0,0,1,1,1,0], [0,0,0,0,0,1,1,0], [0,0,0,0,0,0,1,0],
   [0,0,1,1,1,1,1,1], [0,0,0,1,1,1,1,1], [0,0,0,0,1,1,1,1],
   [0,0,0,0,0,1,1,1], [0,0,0,0,0,0,1,1], [0,0,0,0,0,0,0,1],
   [2,2,4,5,4,3,2,1], [2,2,3,5,4,3,2,1], [2,2,3,4,4,3,2,1],
   [2,2,3,4,3,3,2,1], [2,2,3,4,3,2,2,1], [2,2,3,4,3,2,1,1],
   [2,2,3,4,3,2,1,0], [0,1,0,0,0,0,0,0], [0,1,0,1,0,0,0,0],
   [0,1,1,1,0,0,0,0], [0,1,0,1,1,0,0,0], [0,1,1,1,1,0,0,0],
   [0,1,1,2,1,0,0,0], [0,1,0,1,1,1,0,0], [0,1,1,1,1,1,0,0],
   [0,1,1,2,1,1,0,0], [0,1,1,2,2,1,0,0], [0,1,0,1,1,1,1,0],
   [0,1,1,1,1,1,1,0], [0,1,1,2,1,1,1,0], [0,1,1,2,2,1,1,0],
   [0,1,1,2,2,2,1,0], [0,1,0,1,1,1,1,1], [0,1,1,1,1,1,1,1],
   [0,1,1,2,1,1,1,1], [0,1,1,2,2,1,1,1], [0,1,1,2,2,2,1,1],
   [0,1,1,2,2,2,2,1], [2,3,3,5,4,3,2,1], [2,3,4,5,4,3,2,1],
   [2,3,4,6,4,3,2,1], [2,3,4,6,5,3,2,1], [2,3,4,6,5,4,2,1],
   [2,3,4,6,5,4,3,1], [2,3,4,6,5,4,3,2], [1,3,3,5,4,3,2,1],
   [1,2,3,5,4,3,2,1], [1,2,3,4,4,3,2,1], [1,2,2,4,4,3,2,1],
   [1,2,3,4,3,3,2,1], [1,2,2,4,3,3,2,1], [1,2,2,3,3,3,2,1],
   [1,1,2,3,3,3,2,1], [1,2,3,4,3,2,2,1], [1,2,2,4,3,2,2,1],
   [1,2,2,3,3,2,2,1], [1,1,2,3,3,2,2,1], [1,2,2,3,2,2,2,1],
   [1,1,2,3,2,2,2,1], [1,1,2,2,2,2,2,1], [1,1,1,2,2,2,2,1],
   [1,2,3,4,3,2,1,1], [1,2,2,4,3,2,1,1], [1,2,2,3,3,2,1,1],
   [1,1,2,3,3,2,1,1], [1,2,2,3,2,2,1,1], [1,1,2,3,2,2,1,1],
   [1,1,2,2,2,2,1,1], [1,1,1,2,2,2,1,1], [1,2,2,3,2,1,1,1],
   [1,1,2,3,2,1,1,1], [1,1,2,2,2,1,1,1], [1,1,1,2,2,1,1,1],
   [1,1,2,2,1,1,1,1], [1,1,1,2,1,1,1,1], [1,1,1,1,1,1,1,1],
   [1,0,1,1,1,1,1,1], [1,2,3,4,3,2,1,0], [1,2,2,4,3,2,1,0],
   [1,2,2,3,3,2,1,0], [1,1,2,3,3,2,1,0], [1,2,2,3,2,2,1,0],
   [1,1,2,3,2,2,1,0], [1,1,2,2,2,2,1,0], [1,1,1,2,2,2,1,0],
   [1,2,2,3,2,1,1,0], [1,1,2,3,2,1,1,0], [1,1,2,2,2,1,1,0],
   [1,1,1,2,2,1,1,0], [1,1,2,2,1,1,1,0], [1,1,1,2,1,1,1,0],
   [1,1,1,1,1,1,1,0], [1,0,1,1,1,1,1,0], [1,2,2,3,2,1,0,0],
   [1,1,2,3,2,1,0,0], [1,1,2,2,2,1,0,0], [1,1,1,2,2,1,0,0],
   [1,1,2,2,1,1,0,0], [1,1,1,2,1,1,0,0], [1,1,1,1,1,1,0,0],
   [1,0,1,1,1,1,0,0], [1,1,2,2,1,0,0,0], [1,1,1,2,1,0,0,0],
   [1,1,1,1,1,0,0,0], [1,0,1,1,1,0,0,0], [1,1,1,1,0,0,0,0],
   [1,0,1,1,0,0,0,0], [1,0,1,0,0,0,0,0], [1,0,0,0,0,0,0,0]]

/-- The `E_6` table: the first six simples, the positive list the
committed literal `posE6`. -/
def tableE6 : Table :=
  ⟨6, List.replicate 6 2, 1, slCartan 6 edgesE6,
   posE6,
   [1, 2, 2, 3, 2, 1]⟩

/-- The `E_7` table: the first seven simples, the positive list
the committed literal `posE7`. -/
def tableE7 : Table :=
  ⟨7, List.replicate 7 2, 1, slCartan 7 edgesE7,
   posE7,
   [2, 2, 3, 4, 3, 2, 1]⟩

/-- The `E_8` table: the whole simple list, the positive list the
committed literal `posE8`. -/
def tableE8 : Table :=
  ⟨8, List.replicate 8 2, 1, slCartan 8 edgesE8,
   posE8,
   [2, 3, 4, 6, 5, 4, 3, 2]⟩

/-! The adjugate rows: the five displayed matrices at their fold
keys, the coroot witness and the θ-fold row. -/

def adjG2 : List (List Nat) := [[2, 1], [3, 2]]

def adjF4 : List (List Nat) :=
  [[2, 3, 4, 2], [3, 6, 8, 4], [2, 4, 6, 3], [1, 2, 3, 2]]

def adjE6 : List (List Nat) :=
  [[4, 3, 5, 6, 4, 2], [3, 6, 6, 9, 6, 3], [5, 6, 10, 12, 8, 4],
   [6, 9, 12, 18, 12, 6], [4, 6, 8, 12, 10, 5], [2, 3, 4, 6, 5, 4]]

def adjE7 : List (List Nat) :=
  [[4, 4, 6, 8, 6, 4, 2], [4, 7, 8, 12, 9, 6, 3],
   [6, 8, 12, 16, 12, 8, 4], [8, 12, 16, 24, 18, 12, 6],
   [6, 9, 12, 18, 15, 10, 5], [4, 6, 8, 12, 10, 8, 4],
   [2, 3, 4, 6, 5, 4, 3]]

def adjE8 : List (List Nat) :=
  [[4, 5, 7, 10, 8, 6, 4, 2], [5, 8, 10, 15, 12, 9, 6, 3],
   [7, 10, 14, 20, 16, 12, 8, 4], [10, 15, 20, 30, 24, 18, 12, 6],
   [8, 12, 16, 24, 20, 15, 10, 5], [6, 9, 12, 18, 15, 12, 8, 4],
   [4, 6, 8, 12, 10, 8, 6, 3], [2, 3, 4, 6, 5, 4, 3, 2]]

/-- The adjugate rows' coroot witness
`Σ_k a_ik α_k(α_j^∨) = e δ_ij` over the member's Cartan reads, one
fold per key pair. -/
def adjRead (t : Table) (e : Nat) (rows : List (List Nat)) : Prop :=
  ((List.range t.rank).all (fun i => (List.range t.rank).all (fun j =>
    if (corootAt t (getAt [] rows i) j).oneValue
        (if i == j then BPair.ofNat e else BPair.unit)
    then true else false))) = true

instance instSertables2 (t : Table) (e : Nat) (rows : List (List Nat)) :
    Decidable (adjRead t e rows) :=
  inferInstanceAs (Decidable (_ = _))

/-- The θ-fold row: one adjugate row is the highest root's fold at
the fold key's multiple, the highest root the fundamental at that
key. -/
def thetaRowRead (t : Table) (e : Nat) (rows : List (List Nat))
    (k : Nat) : Prop :=
  (getAt [] rows k == t.thetaFold.map (fun c => e * c)) = true

instance instSertables3 (t : Table) (e : Nat) (rows : List (List Nat)) (k : Nat) :
    Decidable (thetaRowRead t e rows k) :=
  inferInstanceAs (Decidable (_ = _))

/-! The defining tables: the paired key encodings, the simple moves
as matrices at the form's twist, the coroot diagonals, and the
invariant count at the unit-content monomials. -/

/-- The `B` defining key count: the paired keys with the further
null key. -/
def vcountB (l : Nat) : Nat := 2 * l + 1

/-- The `C` defining key count: the paired keys. -/
def vcountC (l : Nat) : Nat := 2 * l

/-- The `D` defining key count: the paired keys. -/
def vcountD (l : Nat) : Nat := 2 * l

/-- The `B` pairing weight cleared at two: the null key at one,
every paired key at two. -/
def pw2B (l a : Nat) : Nat := if a == 2 * l then 1 else 2

private def diagOf (n : Nat) (f : Nat → BPair) : elim.Mat :=
  ground.matOf n n (fun a b => if a == b then f a else BPair.unit)

/-- The `B` cleared pairing as a matrix: the diagonal at the
cleared weights. -/
def wB (l : Nat) : elim.Mat :=
  diagOf (vcountB l) (fun a => BPair.ofNat (pw2B l a))

/-- The `B` simple raising: the difference move on a paired key
pair, the last key's short move through the null key at the
doubled return. -/
def raiseB (l i : Nat) : elim.Mat :=
  ground.matOf (vcountB l) (vcountB l) (fun r c =>
    if i + 2 ≤ l then
      if r == i && c == i + 1 then pB 1
      else if r == i + 1 + l && c == i + l then mB 1
      else BPair.unit
    else if i + 1 == l then
      if r == i && c == 2 * l then pB 1
      else if r == 2 * l && c == i + l then b2
      else BPair.unit
    else BPair.unit)

/-- The `C` simple raising: the difference move on a paired key
pair, the last key's long move across to its partner. -/
def raiseC (l i : Nat) : elim.Mat :=
  ground.matOf (vcountC l) (vcountC l) (fun r c =>
    if i + 2 ≤ l then
      if r == i && c == i + 1 then pB 1
      else if r == i + 1 + l && c == i + l then mB 1
      else BPair.unit
    else if i + 1 == l then
      if r == i && c == i + l then pB 1
      else BPair.unit
    else BPair.unit)

/-- The `D` simple raising: the difference move on a paired key
pair, the last key's sum move at the last coordinate pair. -/
def raiseD (l i : Nat) : elim.Mat :=
  ground.matOf (vcountD l) (vcountD l) (fun r c =>
    if i + 2 ≤ l then
      if r == i && c == i + 1 then pB 1
      else if r == i + 1 + l && c == i + l then mB 1
      else BPair.unit
    else if i + 1 == l then
      if r == i - 1 && c == i + l then pB 1
      else if r == i && c == i - 1 + l then mB 1
      else BPair.unit
    else BPair.unit)

/-- The `B` simple lowering, spelled at its own entries: the
difference move's plain transpose, the short move reweighted
through the null key, the doubled entry crossing to the transpose's
partner slot. -/
def lowerB (l i : Nat) : elim.Mat :=
  ground.matOf (vcountB l) (vcountB l) (fun r c =>
    if i + 2 ≤ l then
      if r == i + 1 && c == i then pB 1
      else if r == i + l && c == i + 1 + l then mB 1
      else BPair.unit
    else if i + 1 == l then
      if r == 2 * l && c == i then b2
      else if r == i + l && c == 2 * l then pB 1
      else BPair.unit
    else BPair.unit)

/-- The `C` simple lowering: the difference move's plain transpose,
the long move's return across the last pair. -/
def lowerC (l i : Nat) : elim.Mat :=
  ground.matOf (vcountC l) (vcountC l) (fun r c =>
    if i + 2 ≤ l then
      if r == i + 1 && c == i then pB 1
      else if r == i + l && c == i + 1 + l then mB 1
      else BPair.unit
    else if i + 1 == l then
      if r == i + l && c == i then pB 1
      else BPair.unit
    else BPair.unit)

/-- The `D` simple lowering: the difference move's plain transpose,
the sum move's return at the last coordinate pair. -/
def lowerD (l i : Nat) : elim.Mat :=
  ground.matOf (vcountD l) (vcountD l) (fun r c =>
    if i + 2 ≤ l then
      if r == i + 1 && c == i then pB 1
      else if r == i + l && c == i + 1 + l then mB 1
      else BPair.unit
    else if i + 1 == l then
      if r == i + l && c == i - 1 then pB 1
      else if r == i - 1 + l && c == i then mB 1
      else BPair.unit
    else BPair.unit)

private def kcuDiff (j i : Nat) : BPair :=
  if j == i then pB 1 else if j == i + 1 then mB 1 else BPair.unit

private def kcuB (l j i : Nat) : BPair :=
  if i + 2 ≤ l then kcuDiff j i
  else if i + 1 == l then (if j == i then b2 else BPair.unit)
  else BPair.unit

private def kcuC (l j i : Nat) : BPair :=
  if i + 2 ≤ l then kcuDiff j i
  else if i + 1 == l then (if j == i then pB 1 else BPair.unit)
  else BPair.unit

private def kcuD (l j i : Nat) : BPair :=
  if i + 2 ≤ l then kcuDiff j i
  else if i + 1 == l then
    (if j == i - 1 || j == i then pB 1 else BPair.unit)
  else BPair.unit

/-- The `B` key content at a simple coroot: the unprimed keys read
the coroot's differences with the short key doubled, the primed
keys negate their partners, and the null key reads the unit. -/
def kcorootB (l a i : Nat) : BPair :=
  if a == 2 * l then BPair.unit
  else if a < l then kcuB l a i
  else (kcuB l (a - l) i).swap

/-- The `C` key content at a simple coroot: the unprimed keys read
the coroot's differences with the long key single, the primed keys
negate their partners. -/
def kcorootC (l a i : Nat) : BPair :=
  if a < l then kcuC l a i else (kcuC l (a - l) i).swap

/-- The `D` key content at a simple coroot: the unprimed keys read
the coroot's differences with the sum move on the last coordinate
pair, the primed keys negate their partners. -/
def kcorootD (l a i : Nat) : BPair :=
  if a < l then kcuD l a i else (kcuD l (a - l) i).swap

/-- The `B` coroot diagonal at a simple key: the key contents on
the diagonal. -/
def hDiagB (l i : Nat) : elim.Mat :=
  diagOf (vcountB l) (fun a => kcorootB l a i)

/-- The `C` coroot diagonal at a simple key: the key contents on
the diagonal. -/
def hDiagC (l i : Nat) : elim.Mat :=
  diagOf (vcountC l) (fun a => kcorootC l a i)

/-- The `D` coroot diagonal at a simple key: the key contents on
the diagonal. -/
def hDiagD (l i : Nat) : elim.Mat :=
  diagOf (vcountD l) (fun a => kcorootD l a i)

/-- The unit-content read at a rank: each unprimed key's count in
the monomial meets its partner's, the null key unconstrained. -/
def unitContentAt (l : Nat) (m : List Nat) : Bool :=
  (List.range l).all (fun c => countOf c m == countOf (c + l) m)

/-- The Leibniz image of a monomial under a key matrix: per nonunit
matrix entry, the unit move's Leibniz outputs (`units.unitAct`)
scatter at the entry's coefficient, the coordinates over the stated
basis. -/
def actMat (M : elim.Mat) (mons : List (List Nat))
    (m : List Nat) : List BPair :=
  (List.range M.length).foldl (fun acc a =>
    (List.range (getAt [] M a).length).foldl (fun acc2 b =>
      let x := getAt BPair.unit (getAt [] M a) b
      if x.isUnitRep then acc2
      else (units.unitAct a b m).foldl
        (fun acc3 mon => units.scatterAt (places.idxOf mon mons) x acc3)
        acc2)
      acc)
    (mons.map (fun _ => BPair.unit))

private def stackedDef (rs : List elim.Mat)
    (full ucols : List (List Nat)) : elim.Mat :=
  rs.flatMap (fun M =>
    (elim.transposeM (ucols.map (actMat M full))).filter
      (fun r => !allUnit r))

/-- The `B` invariant count at a pair count: the stacked simple
raisings' kernel over the unit-content monomials of the doubled
degree, the raised images' coordinates over the full monomial
list. -/
def invCountB (l k : Nat) : Nat :=
  let full := places.allMon (vcountB l) (2 * k)
  let ucols := full.filter (unitContentAt l)
  elim.kernelDim ucols.length
    (stackedDef ((List.range l).map (raiseB l)) full ucols)

/-- The `C` invariant count at a pair count: the stacked simple
raisings' kernel over the unit-content monomials of the doubled
degree. -/
def invCountC (l k : Nat) : Nat :=
  let full := places.allMon (vcountC l) (2 * k)
  let ucols := full.filter (unitContentAt l)
  elim.kernelDim ucols.length
    (stackedDef ((List.range l).map (raiseC l)) full ucols)

/-- The `D` invariant count at a pair count: the stacked simple
raisings' kernel over the unit-content monomials of the doubled
degree. -/
def invCountD (l k : Nat) : Nat :=
  let full := places.allMon (vcountD l) (2 * k)
  let ucols := full.filter (unitContentAt l)
  elim.kernelDim ucols.length
    (stackedDef ((List.range l).map (raiseD l)) full ucols)

/-! The coordinate tier at the coroot presentation: the keys are
coroot lists, the reflections the integer matrices off the Cartan
rows, `ρ` the all-ones key, and the form the stated cleared Gram
with its defining read. -/

set_option genInjectivity false in
/-- The fundamental data at the coroot presentation
(`con:sertables`' adjugate-row form reads): the cleared Gram of the
fundamentals, its scale, the simple members' positions in the
positive list, and per simple index the reflection's permutation of
the positive list — the keys the contents at the member's coroot
solve. -/
structure FundData where
  gram : elim.Mat
  scale : Nat
  simplePos : List Nat
  perms : List (List Nat)

/-- The reflection's matrix at a simple index, off the Cartan row:
`(s_i μ)_j = μ_j − μ_i · α_i(α_j^∨)` (`con:gentable`'s reflection
join `μ = s_i μ + μ(α_i^∨) α_i`). -/
def reflM (t : gentable.Table) (i : Nat) : elim.Mat :=
  ground.matOf t.rank t.rank (fun j k =>
    BPair.add (if j == k then BPair.ofNat 1 else BPair.unit)
      (if k == i then
        (getAt BPair.unit (getAt [] t.cartan i) j).swap
      else BPair.unit))

/-- A positive member's coroot vector, `corootAt` over the keys
(`con:gentable`'s coroot pairs at `con:sertables`' positive
list). -/
def posCorootV (t : gentable.Table) (j : Nat) : List BPair :=
  (List.range t.rank).map
    (gentable.corootAt t (getAt [] t.posFolds j))

/-- A positive member's coroot vector reads the rank's order. -/
theorem posCorootV_length (t : gentable.Table) (j : Nat) :
    (posCorootV t j).length = t.rank :=
  ground.length_mapRange _ t.rank

/-- `ρ`'s coroot vector, one at every key (`con:sertables`' root
fold at its halved coroot read `(2ρ)(α_i^∨) = 2`). -/
def rhoV (t : gentable.Table) : List BPair :=
  List.replicate t.rank (BPair.ofNat 1)

/-- The form's pairing at a stated cleared Gram (`con:sertables`'
form displays at the adjugate-row solve). -/
def dotG (G : elim.Mat) (x y : List BPair) : BPair := elim.dotAt G x y

/-- The form's pairing at the fundamental data, `dotG` at the
carried Gram. -/
def dotB (F : FundData) (x y : List BPair) : BPair :=
  dotG F.gram x y

/-- A reflection's image of a key, normed (`con:sertables`: `s_i`
permutes the positive list off `α_i`). -/
def reflAt (t : gentable.Table) (i : Nat) (v : List BPair) :
    List BPair :=
  poly.pnorm (elim.matVec (reflM t i) v)

/-- The shape conjuncts: the stated lists' orders against the rank
and the positive list (`con:sertables`' displayed data). -/
def fundShape (t : gentable.Table) (F : FundData) : Prop :=
  F.gram.length = t.rank
    ∧ (F.gram.all (fun r => r.length == t.rank)) = true
    ∧ 0 < F.scale
    ∧ F.simplePos.length = t.rank
    ∧ F.perms.length = t.rank
    ∧ (F.simplePos.all (fun j => j < t.posFolds.length)) = true
    ∧ (F.perms.all (fun p => p.length == t.posFolds.length
        && p.all (fun j => j < t.posFolds.length))) = true

instance instSertables4 (t : gentable.Table) (F : FundData) :
    Decidable (fundShape t F) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The pairing's congruence at the second slot. -/
theorem dotB_congrR (F : FundData) (x u u' : List BPair)
    (h : poly.oneValue u u') :
    (dotB F x u).oneValue (dotB F x u') := by
  show (elim.dotP x (elim.matVec F.gram u)).oneValue
    (elim.dotP x (elim.matVec F.gram u'))
  rw [elim.dotP_comm x (elim.matVec F.gram u),
    elim.dotP_comm x (elim.matVec F.gram u')]
  exact elim.dotP_oneValue_left _ _ x
    (elim.matVec_congr F.gram u u' h)

/-- The pairing's additivity at the second slot. -/
theorem dotB_addR (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (x u v : List BPair)
    (hx : x.length = t.rank) (hu : u.length = t.rank)
    (hv : v.length = t.rank) :
    (dotB F x (elim.vecAdd u v)).oneValue
      (dotB F x u + dotB F x v) := by
  show (elim.dotP x
    (elim.matVec F.gram (elim.vecAdd u v))).oneValue _
  rw [elim.dotP_comm x (elim.matVec F.gram (elim.vecAdd u v))]
  refine BPair.oneValue_trans
    (elim.dotP_oneValue_left _
      (elim.vecAdd (elim.matVec F.gram u) (elim.matVec F.gram v)) x
      (elim.matVec_vecAdd F.gram t.rank
        (elim.rowsLen_of_allP (fun _ hr => ground.beqEqOf hr)
          F.gram hshape.2.1) u v hu hv)) ?_
  refine BPair.oneValue_trans
    (elim.dotP_vecAdd_left (elim.matVec F.gram u)
      (elim.matVec F.gram v) x
      (by rw [elim.matVec_length, hshape.1, hx]; exact Nat.le_refl _)
      (by rw [elim.matVec_length, hshape.1, hx]; exact Nat.le_refl _)) ?_
  rw [elim.dotP_comm (elim.matVec F.gram u) x,
    elim.dotP_comm (elim.matVec F.gram v) x]
  exact BPair.oneValue_refl _

/-- The pairing's scale at the second slot. -/
theorem dotB_scaleR (F : FundData) (c : BPair) (x v : List BPair) :
    (dotB F x (elim.vecScale c v)).oneValue (c * dotB F x v) := by
  show (elim.dotP x (elim.matVec F.gram
    (elim.vecScale c v))).oneValue _
  refine BPair.oneValue_trans
    (elim.dotP_oneValue_right x _ _
      (elim.matVec_vecScale_free F.gram c v)) ?_
  exact elim.dotP_vecScale_right x (elim.matVec F.gram v) c


/-- The pairing's congruence at the first slot. -/
theorem dotB_congrL (F : FundData) (u u' x : List BPair)
    (h : poly.oneValue u u') : (dotB F u x).oneValue (dotB F u' x) :=
  elim.dotP_oneValue_left u u' (elim.matVec F.gram x) h


/-- The pairing's additivity at the first slot. -/
theorem dotB_addL (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (u v x : List BPair)
    (hu : u.length = t.rank) (hv : v.length = t.rank) :
    (dotB F (elim.vecAdd u v) x).oneValue
      (dotB F u x + dotB F v x) := by
  have hG : (elim.matVec F.gram x).length = t.rank :=
    (elim.matVec_length F.gram x).trans hshape.1
  exact elim.dotP_vecAdd_left u v (elim.matVec F.gram x)
    (by rw [hG, hu]; exact Nat.le_refl _)
    (by rw [hG, hv]; exact Nat.le_refl _)

/-- A balance partner's square is the member's own, the two swaps
composing to the identity. -/
theorem dotB_negSq (F : FundData) (u : List BPair) :
    dotB F (poly.neg u) (poly.neg u) = dotB F u u := by
  show elim.dotP (poly.neg u) (elim.matVec F.gram (poly.neg u)) = _
  rw [elim.dotP_swap_left,
    show poly.neg u = u.map BPair.swap from rfl,
    elim.matVec_swapArg u F.gram, elim.dotP_swapMap,
    BPair.swap_swap]
  rfl


/-- The Gram's defining read at a stated cleared Gram and scale:
the Cartan rows against the Gram read the scaled length diagonal,
`⟨α_k, ω_j⟩` cleared (`con:sertables`' adjugate-row form
reads). -/
def gramReadG (t : gentable.Table) (G : elim.Mat) (s : Nat) : Prop :=
  elim.matOneValue (elim.matMul t.cartan G)
    (ground.matOf t.rank t.rank (fun k j =>
      if k == j then BPair.ofNat (s * getAt 0 t.lenNums k)
      else BPair.unit))

instance instSertables5 (t : gentable.Table) (G : elim.Mat) (s : Nat) :
    Decidable (gramReadG t G s) :=
  inferInstanceAs (Decidable (elim.matOneValue _ _))

/-- The Gram's defining read at the fundamental data, `gramReadG`
at the carried Gram and scale. -/
def gramRead (t : gentable.Table) (F : FundData) : Prop :=
  gramReadG t F.gram F.scale

instance instSertables6 (t : gentable.Table) (F : FundData) :
    Decidable (gramRead t F) :=
  inferInstanceAs (Decidable (elim.matOneValue _ _))

/-- A stated Gram's symmetry (`con:sertables`' form displays, the
symmetric pair read per content pair). -/
def gramSymReadG (G : elim.Mat) : Prop :=
  elim.matOneValue (elim.transposeM G) G

instance instSertables7 (G : elim.Mat) : Decidable (gramSymReadG G) :=
  inferInstanceAs (Decidable (elim.matOneValue _ _))

/-- The symmetry at the fundamental data, `gramSymReadG` at the
carried Gram. -/
def gramSymRead (F : FundData) : Prop :=
  gramSymReadG F.gram

instance instSertables8 (F : FundData) : Decidable (gramSymRead F) :=
  inferInstanceAs (Decidable (elim.matOneValue _ _))

/-- The simple positions' read: the positive list holds each simple
at its stated position, the one-key fold (`con:sertables`' positive
lists at their displayed folds). -/
def simplePosRead (t : gentable.Table) (F : FundData) : Prop :=
  ∀ i, i < t.rank →
    getAt [] t.posFolds (getAt 0 F.simplePos i)
      = (List.range t.rank).map (fun k => if k == i then 1 else 0)

instance instSertables9 (t : gentable.Table) (F : FundData) :
    Decidable (simplePosRead t F) :=
  inferInstanceAs (Decidable (∀ i, i < t.rank → _ = _))

/-- The involution read at the matrices: each reflection squares to
the identity, the table's own read (`con:sertables`: each letter an
involution, `s_i s_i μ = μ`). -/
def reflSquareRead (t : gentable.Table) : Prop :=
  ∀ i, i < t.rank →
    elim.matOneValue (elim.matMul (reflM t i) (reflM t i))
      (elim.idMat t.rank)

instance instSertables10 (t : gentable.Table) : Decidable (reflSquareRead t) :=
  inferInstanceAs (Decidable (∀ i, i < t.rank →
    elim.matOneValue _ _))

/-- A Cartan diagonal of two makes every displayed simple
reflection square to the identity at its matrix entries. -/
theorem reflSquareRead_of_diagonal (t : gentable.Table)
    (hd : ∀ i, i < t.rank → (getAt BPair.unit (getAt [] t.cartan i) i).oneValue (BPair.ofNat 2)) :
    reflSquareRead t := by
  intro i hi
  let M := reflM t i
  let a := fun j => getAt BPair.unit (getAt [] t.cartan i) j
  let e := fun j k => (if j == k then BPair.ofNat 1 else BPair.unit)
    + (if k == i then (a j).swap else BPair.unit)
  have hMl : M.length = t.rank := ground.matOf_length _ _ _
  have hMr : elim.rowsLen t.rank M := elim.rowsLen_matOf _ _ _
  have hMt : (elim.transposeM M).length = t.rank :=
    elim.length_transposeM M hMr (by rw [hMl]; exact Nat.lt_of_le_of_lt (Nat.zero_le i) hi)
  have hentry (j k : Nat) (hj : j < t.rank) (hk : k < t.rank) :
      getAt BPair.unit (getAt [] M j) k = e j k :=
    ground.matOf_entry [] BPair.unit _ _ _ j k hj hk
  apply elim.matOne_of_entries _ _ t.rank ((elim.length_matMul _ _).trans hMl)
    (elim.rowsLen_cast hMt (elim.rowsLen_matMul M M))
    (elim.length_idMat _) (elim.rowsLen_idMat _)
  intro j k hj hk
  rw [elim.entry_matMul M M j k (by rw [hMl]; exact hj) (by rw [hMt]; exact hk), elim.getAt_idMat _ _ _ hj hk]
  refine BPair.oneValue_trans (elim.dotN_read _ _) ?_
  rw [elim.dotP_fold t.rank _ _ (elim.rowsLen_getAt M j hMr (by rw [hMl]; exact hj))
    (by rw [elim.rowsLen_getAt (elim.transposeM M) k (elim.rowsLen_transposeM M) (by rw [hMt]; exact hk), hMl])]
  have hfold : (ground.famFold BPair.add BPair.unit
      (fun q => getAt BPair.unit (getAt [] M j) q * getAt BPair.unit (getAt [] (elim.transposeM M) k) q)
      (List.range t.rank)).oneValue (e j k + (a j).swap * e i k) := by
    refine BPair.oneValue_trans (ground.foldB_congr_members _
      (fun q => (if q == j then e j k else BPair.unit)
        + (if q == i then (a j).swap * e i k else BPair.unit)) (List.range t.rank) ?_) ?_
    · intro q hq
      have hq' := ground.ltOfMem hq
      rw [hentry j q hj hq', elim.getAt_transposeM BPair.unit M hMr k q hk (by rw [hMl]; exact hq'),
        hentry q k hq' hk]
      change (((if j == q then BPair.ofNat 1 else BPair.unit) + (if q == i then (a j).swap else BPair.unit)) * e q k).oneValue _
      rw [BPair.right_distrib]
      apply BPair.add_congr
      · by_cases hqj : q = j
        · rw [hqj, if_pos (ground.eqBeqOf rfl), if_pos (ground.eqBeqOf rfl)]
          exact BPair.ofNat_one_mul _
        · rw [if_neg (fun h => hqj (ground.beqEqOf h).symm), if_neg (fun h => hqj (ground.beqEqOf h))]
          exact BPair.unit_mul _
      · by_cases hqi : q = i
        · rw [hqi, if_pos (ground.eqBeqOf rfl), if_pos (ground.eqBeqOf rfl)]
          exact BPair.oneValue_refl _
        · rw [if_neg (fun h => hqi (ground.beqEqOf h)), if_neg (fun h => hqi (ground.beqEqOf h))]
          exact BPair.unit_mul _
    · exact BPair.oneValue_trans (ground.foldB_add _ _ _)
        (BPair.add_congr (ground.foldB_pickBeq j (e j k) _ (ground.countOf_range_one hj))
          (ground.foldB_pickBeq i ((a j).swap * e i k) _ (ground.countOf_range_one hi)))
  refine BPair.oneValue_trans hfold ?_
  have hid : (if j == k then BPair.ofNat 1 else BPair.unit)
      = (if k = j then BPair.ofNat 1 else BPair.unit) := by
    by_cases hkj : k = j
    · rw [hkj, if_pos rfl, if_pos (ground.eqBeqOf rfl)]
    · rw [if_neg hkj, if_neg (fun h => hkj (ground.beqEqOf h).symm)]
  by_cases hki : k = i
  · have hii : (e i i).oneValue (BPair.ofNat 1).swap := by
      change ((if i == i then BPair.ofNat 1 else BPair.unit) + (if i == i then (a i).swap else BPair.unit)).oneValue _
      rw [if_pos (ground.eqBeqOf rfl), if_pos (ground.eqBeqOf rfl)]
      exact BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) (ground.swap_congr (hd i hi))) (by decide +kernel)
    have hprod : ((a j).swap * e i k).oneValue (a j) := by
      rw [hki]
      exact BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) hii)
        (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.swap_mul_swap _ _)) (BPair.mul_ofNat_one _))
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) hprod) ?_
    change (((if j == k then BPair.ofNat 1 else BPair.unit) + (if k == i then (a j).swap else BPair.unit)) + a j).oneValue _
    rw [if_pos (ground.eqBeqOf hki), hid]
    exact BPair.add_swap_self _ _
  · have hik : i ≠ k := fun h => hki h.symm
    have hik0 : (e i k).oneValue BPair.unit := by
      change ((if i == k then BPair.ofNat 1 else BPair.unit) + (if k == i then (a i).swap else BPair.unit)).oneValue _
      rw [if_neg (fun h => hik (ground.beqEqOf h)), if_neg (fun h => hki (ground.beqEqOf h))]
      exact BPair.unit_add _
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) hik0) (BPair.mul_unit _))) ?_
    refine BPair.oneValue_trans (BPair.add_unit _) ?_
    change ((if j == k then BPair.ofNat 1 else BPair.unit) + (if k == i then (a j).swap else BPair.unit)).oneValue _
    rw [if_neg (fun h => hki (ground.beqEqOf h)), hid]
    exact BPair.add_unit _


/-- Every B simple reflection squares to the identity at every
rank, the Cartan diagonal's read at two. -/
theorem reflSquareRead_B (l : Nat) : reflSquareRead (tableB l) := by
  apply reflSquareRead_of_diagonal
  intro i hi
  change (getAt BPair.unit (getAt [] (tableB l).cartan i) i).oneValue _
  rw [cartB_eq, ground.matOf_entry [] BPair.unit l l (cartB l) i i hi hi, cartBd]
  exact BPair.oneValue_refl _

/-- Every C simple reflection squares to the identity at every
rank, the Cartan diagonal's read at two. -/
theorem reflSquareRead_C (l : Nat) : reflSquareRead (tableC l) := by
  apply reflSquareRead_of_diagonal
  intro i hi
  change (getAt BPair.unit (getAt [] (tableC l).cartan i) i).oneValue _
  rw [cartC_eq, ground.matOf_entry [] BPair.unit l l (cartC l) i i hi hi, cartCd]
  exact BPair.oneValue_refl _

/-- Every D simple reflection squares to the identity at every
rank, the Cartan diagonal's read at two. -/
theorem reflSquareRead_D (l : Nat) : reflSquareRead (tableD l) := by
  apply reflSquareRead_of_diagonal
  intro i hi
  change (getAt BPair.unit (getAt [] (tableD l).cartan i) i).oneValue _
  rw [cartD_eq, ground.matOf_entry [] BPair.unit l l (cartD l) i i hi hi, cartDd]
  exact BPair.oneValue_refl _


/-- The involution read at the permutation data: each permutation of
the positive list is its own involution (`con:sertables`: each
letter an involution, read at the stated positions). -/
def permSquareRead (t : gentable.Table) (F : FundData) : Prop :=
  ∀ i, i < t.rank → ∀ j, j < t.posFolds.length →
    getAt 0 (getAt [] F.perms i)
      (getAt 0 (getAt [] F.perms i) j) = j

instance instSertables11 (t : gentable.Table) (F : FundData) :
    Decidable (permSquareRead t F) :=
  inferInstanceAs (Decidable (∀ i, i < t.rank →
    ∀ j, j < t.posFolds.length → _ = _))

/-- The form-keeping read: each reflection is a congruence of the
Gram (`con:sertables`: a reflection keeps the form). -/
def reflFormRead (t : gentable.Table) (F : FundData) : Prop :=
  ∀ i, i < t.rank →
    elim.matOneValue
      (elim.matMul (elim.transposeM (reflM t i))
        (elim.matMul F.gram (reflM t i)))
      F.gram

instance instSertables12 (t : gentable.Table) (F : FundData) :
    Decidable (reflFormRead t F) :=
  inferInstanceAs (Decidable (∀ i, i < t.rank →
    elim.matOneValue _ _))

/-- The permutation read: each reflection maps each positive member
off its own simple to the permuted position's member, and its own
simple to the balance partner (`con:sertables`' first shared read,
`s_i` permuting the positive list off `α_i`). -/
def permImageRead (t : gentable.Table) (F : FundData) : Prop :=
  ∀ i, i < t.rank →
    (∀ j, j < t.posFolds.length → j ≠ getAt 0 F.simplePos i →
      reflAt t i (posCorootV t j)
        = poly.pnorm (posCorootV t (getAt 0 (getAt [] F.perms i) j)))
    ∧ reflAt t i (posCorootV t (getAt 0 F.simplePos i))
        = poly.pnorm (poly.neg (posCorootV t (getAt 0 F.simplePos i)))

instance instSertables13 (t : gentable.Table) (F : FundData) :
    Decidable (permImageRead t F) :=
  inferInstanceAs (Decidable (∀ i, i < t.rank →
    (∀ j, j < t.posFolds.length → j ≠ _ → _ = _) ∧ _ = _))

/-- The `ρ`-dot read: every positive member's Gram pairing against
`ρ` is positive (`con:sertables`' regular reads, the `ρ`-fold's
members at positive root-fold dots). -/
def rhoDotRead (t : gentable.Table) (F : FundData) : Prop :=
  ∀ j, j < t.posFolds.length →
    BPair.unit < dotB F (posCorootV t j) (rhoV t)

instance instSertables14 (t : gentable.Table) (F : FundData) :
    Decidable (rhoDotRead t F) :=
  inferInstanceAs (Decidable (∀ j, j < t.posFolds.length →
    _ < _))

/-- A fixed member's cleared Gram at its displayed adjugate rows:
`⟨ω_i, ω_j⟩` cleared as `a_ij · len_j` (`con:sertables`' adjugate
rows' form reads, `2e⟨ω_i,ω_j⟩ = a_ij⟨α_j,α_j⟩`), one stated list
against the table's lengths. -/
def gramRows (t : gentable.Table) (rows : List (List Nat)) : elim.Mat :=
  rows.map (fun r => (List.zipWith Nat.mul r t.lenNums).map BPair.ofNat)

/-- `B_2`'s fundamental data at the coroot presentation: the
cleared Gram off the adjugate solve at the displayed Cartan rows,
the simple positions, and the reflections' permutations of the
positive list (`con:sertables`' member data). -/
def fundB2 : FundData :=
  ⟨[[(BPair.ofNat 2), (BPair.ofNat 1)], [(BPair.ofNat 1), (BPair.ofNat 1)]],
   1, [0, 3], [[0, 1, 3, 2], [1, 0, 2, 3]]⟩

/-- `G_2`'s fundamental data at the coroot presentation
(`con:sertables`' displayed folds and lengths). -/
def fundG2 : FundData :=
  ⟨[[(BPair.ofNat 4), (BPair.ofNat 6)], [(BPair.ofNat 6), (BPair.ofNat 12)]],
   1, [0, 1], [[0, 4, 3, 2, 1, 5], [2, 1, 0, 3, 5, 4]]⟩

/-! The series' displayed Weyl lists (`con:sertables`: a series
member's list is the signed place permutations of its coordinates,
every sign vector at `B` and `C` and the even flip counts at `D`,
the displayed list, with distinct signed permutations at distinct
coordinate images, one list member each; the grading `sgn σ`
against the flip count's parity at `B` and `C` and `sgn σ` alone
at `D`).  The producers run at the coroot presentation: the
coordinate display enters by the displayed coroot pairs' own
solve, the suffix folds at the doubled coordinates (`B` and `D`)
or the plain ones (`C`), each image reads back through the
displayed pairs, and the halving is the doubled display's read,
the entries one parity across a signed image. -/

/-- The signed half at an even balance pair, the doubled
coordinate display's coroot read. -/
def halfB (x : BPair) : BPair :=
  if x < BPair.unit then (BPair.ofNat (BPair.marginN x / 2)).swap
  else BPair.ofNat (BPair.marginN x / 2)

/-- The suffix coordinate display, its last key unscaled. -/
private def coordsSuffix (scale : BPair → BPair) (m : List BPair) : List BPair :=
  match m.reverse with
  | [] => []
  | a :: rest =>
    rest.foldl (fun acc x =>
      (scale x + ground.getAt BPair.unit acc 0) :: acc) [a]

/-- The `B` coordinate display of a coroot vector: the doubled
suffix fold, the last key the last coroot read itself. -/
def coordsB (m : List BPair) : List BPair :=
  coordsSuffix (fun x => x + x) m

/-- The `C` coordinate display: the plain suffix fold. -/
def coordsC (m : List BPair) : List BPair :=
  coordsSuffix (fun x => x) m

/-- The `D` coordinate display: the doubled suffix fold seeded at
the fork keys' sum and gap. -/
def coordsD (m : List BPair) : List BPair :=
  match m.reverse with
  | [] => []
  | [_] => []
  | a :: b :: rest =>
    rest.foldl (fun acc x =>
      (x + x + ground.getAt BPair.unit acc 0) :: acc)
      [b + a, a + b.swap]

/-- The `B` coroot read of a coordinate display: the halved
consecutive gaps with the last key's own read. -/
def corootsB (v : List BPair) : List BPair :=
  (List.zipWith (fun a b => halfB (a + b.swap)) v (v.drop 1))
    ++ [ground.getAt BPair.unit v (v.length - 1)]

/-- The `C` coroot read: the consecutive gaps with the last key's
own read. -/
def corootsC (v : List BPair) : List BPair :=
  (List.zipWith (fun a b => a + b.swap) v (v.drop 1))
    ++ [ground.getAt BPair.unit v (v.length - 1)]

/-- The `D` coroot read: the halved consecutive gaps with the
fork's halved sum. -/
def corootsD (v : List BPair) : List BPair :=
  (List.zipWith (fun a b => halfB (a + b.swap)) v (v.drop 1))
    ++ [halfB (ground.getAt BPair.unit v (v.length - 2)
          + ground.getAt BPair.unit v (v.length - 1))]

/-- A signed permutation's image of a coordinate display: the
permuted display at the flipped places. -/
def signedImage (l : Nat) (D : List BPair) (p : List Nat)
    (n : Nat) : List BPair :=
  (List.range l).map (fun q =>
    let x := ground.getAt BPair.unit D (ground.getAt 0 p q)
    if baseDigit 2 q n == 1 then x.swap else x)

/-- A sign vector's flip parity. -/
def flipParity (l n : Nat) : Bool :=
  ((List.range l).foldl (fun a q => a + baseDigit 2 q n) 0) % 2 == 1

private def serWeylGo (coords coroots : List BPair → List BPair)
    (flipsAll : Bool) (l : Nat) (v : List BPair) :
    List (List BPair × Bool) :=
  let D := coords v
  (places.perms l).flatMap (fun p =>
    (List.range (2 ^ l)).filterMap (fun n =>
      if flipsAll || !(flipParity l n) then
        some (poly.pnorm (coroots (signedImage l D p n)),
          if flipsAll then places.parity p != flipParity l n
          else places.parity p)
      else none))

/-- The `B` member's displayed Weyl list at a coroot key: every
sign vector, the grading `sgn σ` against the flip parity. -/
def serWeylB (l : Nat) (v : List BPair) : List (List BPair × Bool) :=
  serWeylGo coordsB corootsB true l v

/-- The `C` member's displayed Weyl list at a coroot key. -/
def serWeylC (l : Nat) (v : List BPair) : List (List BPair × Bool) :=
  serWeylGo coordsC corootsC true l v

/-- The `D` member's displayed Weyl list at a coroot key: the even
flip counts, the grading `sgn σ` alone. -/
def serWeylD (l : Nat) (v : List BPair) : List (List BPair × Bool) :=
  serWeylGo coordsD corootsD false l v

/-- The Weyl list's shape read: every member's key at the rank,
normed (`con:sertables`' graded image list at the coordinate tier's
presentation, the keys the reflections' own carrier). -/
def wShapeRead (t : gentable.Table)
    (W : List (List BPair × Bool)) : Prop :=
  ∀ vp ∈ W, vp.1.length = t.rank ∧ poly.pnorm vp.1 = vp.1

instance instSertables15 (t : gentable.Table) (W : List (List BPair × Bool)) :
    Decidable (wShapeRead t W) :=
  inferInstanceAs (Decidable (∀ vp ∈ W, _ ∧ _ = _))

/-! The displayed signed families at symbolic coordinate lists. -/

/-- The signed halving reads the balance value alone. -/
theorem halfB_congr {x y : BPair} (h : x.oneValue y) : halfB x = halfB y := by
  unfold halfB
  have hm := BPair.marginN_congr h
  by_cases hx : x < BPair.unit
  · have hy := BPair.lt_congr h (BPair.oneValue_refl _) hx
    rw [if_pos hx, if_pos hy, hm]
  · have hy : ¬ y < BPair.unit := fun hy => hx
      (BPair.lt_congr (BPair.oneValue_symm h) (BPair.oneValue_refl _) hy)
    rw [if_neg hx, if_neg hy, hm]

/-- Halving a natural entry reads its quotient at two. -/
theorem halfB_ofNat (n : Nat) : halfB (BPair.ofNat n) = BPair.ofNat (n / 2) := by
  have h : ¬ BPair.ofNat n < BPair.unit :=
    ground.leB_not_lt (ground.leB_ofNat (Nat.zero_le n))
  unfold halfB
  rw [if_neg h, BPair.marginN_ofNat]

/-- Halving a natural entry's partner reads the quotient's partner. -/
theorem halfB_swap_ofNat : ∀ n : Nat,
    halfB (BPair.ofNat n).swap = (BPair.ofNat (n / 2)).swap
  | 0 => rfl
  | n + 1 => by
    have h : (BPair.ofNat (n + 1)).swap < BPair.unit :=
      ground.ltB_swap (ground.unitLtNat (Nat.succ_pos n))
    unfold halfB
    rw [if_pos h]
    have hm : (BPair.ofNat (n + 1)).swap.marginN = n + 1 := rfl
    rw [hm]

/-- The signed half returns the original value at a doubled pair. -/
theorem halfB_double (x : BPair) : (halfB (x + x)).oneValue x := by
  have hdiv : ∀ n : Nat, (n + n) / 2 = n := by
    intro n
    have h := ground.divMulSelf n 2 (by decide)
    rw [Nat.mul_succ, Nat.mul_one] at h
    exact h
  by_cases hx : x < BPair.unit
  · have hp : BPair.unit ≤ x.swap := ground.leB_of_lt (ground.ltB_swap hx)
    have hrep : x.oneValue (BPair.ofNat x.swap.marginN).swap :=
      ground.swap_congr (BPair.ofNat_marginN hp)
    have hs := ground.swap_congr (BPair.ofNat_add x.swap.marginN x.swap.marginN)
    rw [← BPair.swap_add] at hs
    have hd := BPair.oneValue_trans (BPair.add_congr hrep hrep) (BPair.oneValue_symm hs)
    rw [halfB_congr hd, halfB_swap_ofNat, hdiv]
    exact BPair.oneValue_symm hrep
  · have hrep := BPair.ofNat_marginN (ground.leB_of_not_lt hx)
    have hd := BPair.oneValue_trans (BPair.add_congr hrep hrep)
      (BPair.oneValue_symm (BPair.ofNat_add x.marginN x.marginN))
    rw [halfB_congr hd, halfB_ofNat, hdiv]
    exact BPair.oneValue_symm hrep

/-- At an even margin, doubling the signed half reads the pair
back. -/
theorem halfB_read (x : BPair) (heven : x.marginN % 2 = 0) :
    (halfB x + halfB x).oneValue x := by
  have hdiv : ∀ n : Nat, n % 2 = 0 → n / 2 + n / 2 = n := by
    intro n hn
    have h := (ground.natDivRead n 2 (by decide)).1
    rw [hn, Nat.add_zero, Nat.two_mul] at h
    exact h
  by_cases hx : x < BPair.unit
  · have hp : BPair.unit ≤ x.swap := ground.leB_of_lt (ground.ltB_swap hx)
    have hrep : x.oneValue (BPair.ofNat x.marginN).swap := by
      have h := ground.swap_congr (BPair.ofNat_marginN hp)
      rw [BPair.marginN_swap] at h
      exact h
    rw [halfB_congr hrep, halfB_swap_ofNat, BPair.swap_add]
    refine BPair.oneValue_trans (ground.swap_congr (BPair.oneValue_symm
      (BPair.ofNat_add (x.marginN / 2) (x.marginN / 2)))) ?_
    rw [hdiv x.marginN heven]
    exact BPair.oneValue_symm hrep
  · have hrep := BPair.ofNat_marginN (ground.leB_of_not_lt hx)
    rw [halfB_congr hrep, halfB_ofNat]
    refine BPair.oneValue_trans (BPair.oneValue_symm
      (BPair.ofNat_add (x.marginN / 2) (x.marginN / 2))) ?_
    rw [hdiv x.marginN heven]
    exact BPair.oneValue_symm hrep
/-- Every suffix step adds one coordinate. -/
private theorem coordsFold_length (scale : BPair → BPair) :
    ∀ (v acc : List BPair),
      (v.foldl (fun acc x => (scale x + ground.getAt BPair.unit acc 0) :: acc) acc).length
        = v.length + acc.length
  | [], acc => (Nat.zero_add acc.length).symm
  | x :: v, acc => by
    change (v.foldl (fun acc x => (scale x + ground.getAt BPair.unit acc 0) :: acc)
      ((scale x + ground.getAt BPair.unit acc 0) :: acc)).length = _
    rw [coordsFold_length scale v]
    change v.length + (acc.length + 1) = (v.length + 1) + acc.length
    exact (Nat.add_right_comm v.length 1 acc.length).symm

private theorem coordsSuffix_length (scale : BPair → BPair) (m : List BPair) :
    (coordsSuffix scale m).length = m.length := by
  have hlen := ground.length_reverse m
  unfold coordsSuffix
  cases hr : m.reverse with
  | nil => rw [hr] at hlen; exact hlen
  | cons a rest =>
    rw [hr] at hlen
    rw [coordsFold_length]
    exact hlen

/-- B's suffix display keeps the coroot width. -/
theorem coordsB_length (m : List BPair) : (coordsB m).length = m.length :=
  coordsSuffix_length _ m

/-- C's suffix display keeps the coroot width. -/
theorem coordsC_length (m : List BPair) : (coordsC m).length = m.length :=
  coordsSuffix_length _ m

/-- D's fork seeds two coordinates, with every earlier coroot
adding one. -/
theorem coordsD_length (m : List BPair) (hm : 2 ≤ m.length) :
    (coordsD m).length = m.length := by
  have hlen := ground.length_reverse m
  unfold coordsD
  cases hr : m.reverse with
  | nil => rw [hr] at hlen; rw [← hlen] at hm; exact absurd hm (by decide)
  | cons a rest =>
    cases rest with
    | nil => rw [hr] at hlen; rw [← hlen] at hm; exact absurd hm (by decide : ¬ 2 ≤ 1)
    | cons b rest =>
      rw [hr] at hlen
      rw [coordsFold_length]
      exact hlen

private theorem coordsSuffix_cons (scale : BPair → BPair) (a : BPair)
    (m : List BPair) (hm : 0 < m.length) :
    coordsSuffix scale (a :: m)
      = (scale a + ground.getAt BPair.unit (coordsSuffix scale m) 0) :: coordsSuffix scale m := by
  have hlen := ground.length_reverse m
  unfold coordsSuffix
  rw [ground.reverse_cons]
  cases hr : m.reverse with
  | nil =>
    rw [hr] at hlen
    rw [← hlen] at hm
    exact absurd hm (Nat.lt_irrefl 0)
  | cons b rest =>
    change ((rest ++ [a]).foldl _ [b]) = _
    rw [ground.foldl_append]
    rfl

/-- A B coroot extends the coordinate display by its doubled
read joined to the prior head. -/
theorem coordsB_cons (a : BPair) (m : List BPair) (hm : 0 < m.length) :
    coordsB (a :: m) = (a + a + ground.getAt BPair.unit (coordsB m) 0) :: coordsB m :=
  coordsSuffix_cons _ a m hm

/-- A C coroot extends the coordinate display by its read joined
to the prior head. -/
theorem coordsC_cons (a : BPair) (m : List BPair) (hm : 0 < m.length) :
    coordsC (a :: m) = (a + ground.getAt BPair.unit (coordsC m) 0) :: coordsC m :=
  coordsSuffix_cons _ a m hm

/-- D's fork display extends by the doubled preceding coroot. -/
theorem coordsD_cons (a : BPair) (m : List BPair) (hm : 2 ≤ m.length) :
    coordsD (a :: m) = (a + a + ground.getAt BPair.unit (coordsD m) 0) :: coordsD m := by
  have hlen := ground.length_reverse m
  unfold coordsD
  rw [ground.reverse_cons]
  cases hr : m.reverse with
  | nil => rw [hr] at hlen; rw [← hlen] at hm; exact absurd hm (by decide)
  | cons b rest =>
    cases rest with
    | nil => rw [hr] at hlen; rw [← hlen] at hm; exact absurd hm (by decide : ¬ 2 ≤ 1)
    | cons c rest =>
      change (rest ++ [a]).foldl _ _ = _
      rw [ground.foldl_append]
      rfl

/-- B's coroot display reads the first half gap and the tail. -/
theorem corootsB_cons (a b : BPair) (m : List BPair) :
    corootsB (a :: b :: m) = halfB (a + b.swap) :: corootsB (b :: m) := rfl

/-- D's coroot display reads the first half gap before its fork. -/
theorem corootsD_cons (a b c : BPair) (m : List BPair) :
    corootsD (a :: b :: c :: m) = halfB (a + b.swap) :: corootsD (b :: c :: m) := rfl

/-- D's entries before the final key are the consecutive half
gaps in the displayed coordinates. -/
theorem corootsD_gap : ∀ (D : List BPair) (i : Nat), i + 1 < D.length →
    ground.getAt BPair.unit (corootsD D) i
      = halfB (ground.getAt BPair.unit D i + (ground.getAt BPair.unit D (i + 1)).swap)
  | [], i, h => absurd h (Nat.not_lt_zero (i + 1))
  | [_], i, h => absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero i)
  | [a, b], 0, _ => rfl
  | [_, _], i + 1, h => absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h)) (Nat.not_lt_zero i)
  | a :: b :: c :: D, 0, _ => rfl
  | a :: b :: c :: D, i + 1, h => by
    rw [corootsD_cons]
    exact corootsD_gap (b :: c :: D) i (Nat.lt_of_succ_lt_succ h)

/-- D's final coroot is the half sum of the final two displayed
coordinates. -/
theorem corootsD_fork : ∀ (D : List BPair) (i : Nat), i + 2 = D.length →
    ground.getAt BPair.unit (corootsD D) (i + 1)
      = halfB (ground.getAt BPair.unit D i + ground.getAt BPair.unit D (i + 1))
  | [], i, h => Nat.noConfusion h
  | [_], i, h => Nat.noConfusion (Nat.succ.inj h)
  | [a, b], i, h => by
    have hi : i = 0 := Nat.succ.inj (Nat.succ.inj h)
    rw [hi]
    rfl
  | _ :: _ :: _ :: _, 0, h => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj h))
  | a :: b :: c :: D, i + 1, h => by
    rw [corootsD_cons]
    exact corootsD_fork (b :: c :: D) i (Nat.succ.inj h)

/-- Doubling a D chain entry returns its coordinate gap on the
half read's even-margin domain. -/
theorem corootsD_gap_read (D : List BPair) (i : Nat) (hi : i + 1 < D.length)
    (he : (ground.getAt BPair.unit D i + (ground.getAt BPair.unit D (i + 1)).swap).marginN % 2 = 0) :
    (BPair.ofNat 2 * ground.getAt BPair.unit (corootsD D) i).oneValue
      (ground.getAt BPair.unit D i + (ground.getAt BPair.unit D (i + 1)).swap) := by
  rw [corootsD_gap D i hi]
  exact BPair.oneValue_trans (BPair.ofNat_two_mul _) (halfB_read _ he)

/-- Doubling D's final entry returns its coordinate sum. The
final gap's even margin also gives the sum's even margin. -/
theorem corootsD_fork_read (D : List BPair) (i : Nat) (hi : i + 2 = D.length)
    (he : (ground.getAt BPair.unit D i + (ground.getAt BPair.unit D (i + 1)).swap).marginN % 2 = 0) :
    (BPair.ofNat 2 * ground.getAt BPair.unit (corootsD D) (i + 1)).oneValue
      (ground.getAt BPair.unit D i + ground.getAt BPair.unit D (i + 1)) := by
  rw [corootsD_fork D i hi]
  apply BPair.oneValue_trans (BPair.ofNat_two_mul _) (halfB_read _ ?_)
  rw [BPair.marginN_add_mod_two, BPair.marginN_swap] at he
  rw [BPair.marginN_add_mod_two]
  exact he

/-- The C coroot display reads its first gap and then the tail's
own display. -/
theorem corootsC_cons (a b : BPair) (m : List BPair) :
    corootsC (a :: b :: m) = (a + b.swap) :: corootsC (b :: m) := rfl

/-- C's coroot entry is the consecutive coordinate gap, with the
sum's unit beyond the final coordinate. -/
theorem corootsC_getAt : ∀ (D : List BPair) (i : Nat), i < D.length →
    (ground.getAt BPair.unit (corootsC D) i).oneValue
      (ground.getAt BPair.unit D i + (ground.getAt BPair.unit D (i + 1)).swap)
  | [], i, h => absurd h (Nat.not_lt_zero i)
  | [a], 0, _ => BPair.oneValue_symm (BPair.add_unit a)
  | [_], i + 1, h => absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero i)
  | a :: b :: D, 0, _ => BPair.oneValue_refl _
  | a :: b :: D, i + 1, h => by
    rw [corootsC_cons]
    exact corootsC_getAt (b :: D) i (Nat.lt_of_succ_lt_succ h)

/-- C's coroot solve reads back every occupied coroot list, at
the balance carrier's one-value relation. -/
theorem corootsC_coordsC : ∀ m : List BPair, 0 < m.length →
    poly.oneValue (corootsC (coordsC m)) m
  | [], h => absurd h (Nat.lt_irrefl 0)
  | [a], _ => ⟨BPair.oneValue_refl a, trivial⟩
  | a :: b :: m, _ => by
    rw [coordsC_cons a (b :: m) (Nat.succ_pos _)]
    have ih := corootsC_coordsC (b :: m) (Nat.succ_pos _)
    have hw := coordsC_length (b :: m)
    cases hc : coordsC (b :: m) with
    | nil => rw [hc] at hw; exact Nat.noConfusion hw
    | cons c cs =>
      rw [hc] at ih
      rw [corootsC_cons]
      refine ⟨?_, ih⟩
      change (a + c + c.swap).oneValue a
      rw [BPair.add_right_comm]
      exact BPair.add_swap_self a c

/-- B's coroot solve returns every occupied coroot list at one
value; the signed half reads its doubled consecutive gap. -/
theorem corootsB_coordsB : ∀ m : List BPair, 0 < m.length →
    poly.oneValue (corootsB (coordsB m)) m
  | [], h => absurd h (Nat.lt_irrefl 0)
  | [a], _ => ⟨BPair.oneValue_refl a, trivial⟩
  | a :: b :: m, _ => by
    rw [coordsB_cons a (b :: m) (Nat.succ_pos _)]
    have ih := corootsB_coordsB (b :: m) (Nat.succ_pos _)
    have hw := coordsB_length (b :: m)
    cases hc : coordsB (b :: m) with
    | nil => rw [hc] at hw; exact Nat.noConfusion hw
    | cons c cs =>
      rw [hc] at ih
      rw [corootsB_cons]
      refine ⟨?_, ih⟩
      have hd : (a + a + c + c.swap).oneValue (a + a) := by
        rw [BPair.add_right_comm (a + a) c c.swap]
        exact BPair.add_swap_self (a + a) c
      change (halfB (a + a + c + c.swap)).oneValue a
      rw [halfB_congr hd]
      exact halfB_double a

/-- The fork's two half reads return its two coroot coordinates. -/
private theorem corootsD_pair (a b : BPair) :
    poly.oneValue (corootsD (coordsD [a, b])) [a, b] := by
  have h1 : (a + b + (b + a.swap).swap).oneValue (a + a) := by
    rw [← BPair.swap_add, BPair.swap_swap, ← BPair.add_assoc]
    have h : (a + b + b.swap).oneValue a := by
      rw [BPair.add_right_comm]
      exact BPair.add_swap_self a b
    exact BPair.add_congr h (BPair.oneValue_refl a)
  have h2 : (a + b + (b + a.swap)).oneValue (b + b) := by
    rw [BPair.add_assoc a b (b + a.swap), ← BPair.add_assoc b b a.swap]
    exact BPair.add_swap_cancel a (b + b)
  change (halfB (a + b + (b + a.swap).swap)).oneValue a
    ∧ (halfB (a + b + (b + a.swap))).oneValue b ∧ True
  rw [halfB_congr h1, halfB_congr h2]
  exact ⟨halfB_double a, halfB_double b, trivial⟩

/-- D's coroot solve returns the input list at the fork's width. -/
theorem corootsD_coordsD : ∀ m : List BPair, 2 ≤ m.length →
    poly.oneValue (corootsD (coordsD m)) m
  | [], h => absurd h (by decide)
  | [_], h => absurd h (by decide : ¬ 2 ≤ 1)
  | [a, b], _ => corootsD_pair a b
  | a :: b :: c :: m, _ => by
    rw [coordsD_cons a (b :: c :: m) (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _)))]
    have ih := corootsD_coordsD (b :: c :: m)
      (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _)))
    have hw := coordsD_length (b :: c :: m)
      (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _)))
    cases hc : coordsD (b :: c :: m) with
    | nil => rw [hc] at hw; exact Nat.noConfusion hw
    | cons d ds =>
      cases ds with
      | nil => rw [hc] at hw; exact Nat.noConfusion (Nat.succ.inj hw)
      | cons e es =>
        rw [hc] at ih
        rw [corootsD_cons]
        refine ⟨?_, ih⟩
        have hd : (a + a + d + d.swap).oneValue (a + a) := by
          rw [BPair.add_right_comm (a + a) d d.swap]
          exact BPair.add_swap_self (a + a) d
        change (halfB (a + a + d + d.swap)).oneValue a
        rw [halfB_congr hd]
        exact halfB_double a

/-- The consecutive-pair fold has one fewer entry than an occupied
coordinate list. -/
private theorem consecutive_length {α β : Type} (f : α → α → β) :
    ∀ (a : α) (v : List α), (List.zipWith f (a :: v) v).length = v.length
  | _, [] => rfl
  | _, b :: v => congrArg Nat.succ (consecutive_length f b v)

/-- The coroot read keeps the width of an occupied coordinate
display. -/
theorem corootsB_length (v : List BPair) (hv : 0 < v.length) :
    (corootsB v).length = v.length := by
  cases v with
  | nil => exact absurd hv (Nat.lt_irrefl 0)
  | cons a v =>
    change (List.zipWith (fun a b : BPair => halfB (a + b.swap)) (a :: v) v ++ [_]).length = _
    rw [ground.length_append, consecutive_length]
    rfl

/-- The C coroot read keeps the coordinate width. -/
theorem corootsC_length (v : List BPair) (hv : 0 < v.length) :
    (corootsC v).length = v.length := by
  cases v with
  | nil => exact absurd hv (Nat.lt_irrefl 0)
  | cons a v =>
    change (List.zipWith (fun a b : BPair => a + b.swap) (a :: v) v ++ [_]).length = _
    rw [ground.length_append, consecutive_length]
    rfl

/-- The D coroot read keeps the coordinate width. -/
theorem corootsD_length (v : List BPair) (hv : 0 < v.length) :
    (corootsD v).length = v.length := by
  cases v with
  | nil => exact absurd hv (Nat.lt_irrefl 0)
  | cons a v =>
    change (List.zipWith (fun a b : BPair => halfB (a + b.swap)) (a :: v) v ++ [_]).length = _
    rw [ground.length_append, consecutive_length]
    rfl

/-- C's coordinate round trip returns the canonical coroot key. -/
theorem corootsC_coordsC_norm (m : List BPair) (hm : 0 < m.length) :
    poly.pnorm (corootsC (coordsC m)) = poly.pnorm m :=
  poly.pnorm_congr _ _
    ((corootsC_length (coordsC m) (by rw [coordsC_length]; exact hm)).trans (coordsC_length m))
    (corootsC_coordsC m hm)

/-- A signed image has one coordinate per place. -/
theorem signedImage_length (l : Nat) (D : List BPair) (p : List Nat) (n : Nat) :
    (signedImage l D p n).length = l := ground.length_mapRange _ _

/-- A signed image's entry is the chosen coordinate on its bit's
side. -/
theorem signedImage_getAt (l : Nat) (D : List BPair) (p : List Nat) (n i : Nat)
    (hi : i < l) :
    ground.getAt BPair.unit (signedImage l D p n) i
      = if baseDigit 2 i n == 1 then (ground.getAt BPair.unit D (ground.getAt 0 p i)).swap
        else ground.getAt BPair.unit D (ground.getAt 0 p i) := by
  rw [signedImage, ground.getAt_map_range, if_pos hi]

/-- The sign code at the sum's unit keeps every coordinate. -/
theorem signedImage_zero (l : Nat) (D : List BPair) (p : List Nat) :
    signedImage l D p 0 = (List.range l).map (fun i => ground.getAt BPair.unit D (ground.getAt 0 p i)) := by
  refine ground.map_congr_members _ _ _ (fun i _ => ?_)
  rw [baseDigit_of_lt 2 i 0 (by decide) (Nat.pow_pos (by decide))]
  rfl

/-- The unit place assignment and the unit sign code read the
coordinate display itself. -/
theorem signedImage_id (D : List BPair) :
    signedImage D.length D (List.range D.length) 0 = D := by
  rw [signedImage_zero]
  have h : (List.range D.length).map (fun i => ground.getAt BPair.unit D (ground.getAt 0 (List.range D.length) i))
      = (List.range D.length).map (ground.getAt BPair.unit D) := by
    refine ground.map_congr_members _ _ _ (fun i hi => ?_)
    rw [ground.getAt_range D.length i (ground.ltOfMem hi)]
  rw [h, ground.range_map_getAt BPair.unit D.length D rfl]

/-- B's coordinate round trip returns the canonical coroot key. -/
theorem corootsB_coordsB_norm (m : List BPair) (hm : 0 < m.length) :
    poly.pnorm (corootsB (coordsB m)) = poly.pnorm m :=
  poly.pnorm_congr _ _
    ((corootsB_length (coordsB m) (by rw [coordsB_length]; exact hm)).trans (coordsB_length m))
    (corootsB_coordsB m hm)

/-- D's coordinate round trip returns the canonical coroot key. -/
theorem corootsD_coordsD_norm (m : List BPair) (hm : 2 ≤ m.length) :
    poly.pnorm (corootsD (coordsD m)) = poly.pnorm m := by
  have hp : 0 < (coordsD m).length := by
    rw [coordsD_length m hm]
    exact Nat.lt_of_lt_of_le (by decide : 0 < 2) hm
  exact poly.pnorm_congr _ _
    ((corootsD_length (coordsD m) hp).trans (coordsD_length m hm))
    (corootsD_coordsD m hm)

private theorem coordsSuffix_congr (scale : BPair → BPair)
    (hs : ∀ a b, a.oneValue b → (scale a).oneValue (scale b)) :
    ∀ u v : List BPair, u.length = v.length → poly.oneValue u v →
      poly.oneValue (coordsSuffix scale u) (coordsSuffix scale v)
  | [], [], _, _ => trivial
  | [], _ :: _, hw, _ => Nat.noConfusion hw
  | _ :: _, [], hw, _ => Nat.noConfusion hw
  | a :: u, b :: v, hw, h => by
    cases u with
    | nil =>
      cases v with
      | nil => exact ⟨h.1, trivial⟩
      | cons c v => exact Nat.noConfusion (Nat.succ.inj hw)
    | cons c u =>
      cases v with
      | nil => exact Nat.noConfusion (Nat.succ.inj hw)
      | cons d v =>
        have ih := coordsSuffix_congr scale hs (c :: u) (d :: v) (Nat.succ.inj hw) h.2
        rw [coordsSuffix_cons scale a (c :: u) (Nat.succ_pos _),
          coordsSuffix_cons scale b (d :: v) (Nat.succ_pos _)]
        exact ⟨BPair.add_congr (hs a b h.1) (poly.oneValue_getAt 0 ih), ih⟩

private theorem coordsFold_parity (scale : BPair → BPair)
    (hs : ∀ x, (scale x).marginN % 2 = 0) :
    ∀ (m acc : List BPair) (c : Nat), 0 < acc.length →
      (∀ i, i < acc.length → (ground.getAt BPair.unit acc i).marginN % 2 = c) →
      ∀ i, i < (m.foldl (fun acc x => (scale x + ground.getAt BPair.unit acc 0) :: acc) acc).length →
        (ground.getAt BPair.unit
          (m.foldl (fun acc x => (scale x + ground.getAt BPair.unit acc 0) :: acc) acc) i).marginN % 2 = c
  | [], _, _, _, h => h
  | x :: m, acc, c, ha, h => by
    refine coordsFold_parity scale hs m
      ((scale x + ground.getAt BPair.unit acc 0) :: acc) c (Nat.succ_pos _) ?_
    intro i hi
    cases i with
    | zero =>
      change (scale x + ground.getAt BPair.unit acc 0).marginN % 2 = c
      rw [BPair.marginN_add_mod_two, ← ground.modAdd, hs x, Nat.zero_add, ground.modMod]
      exact h 0 ha
    | succ i => exact h i (Nat.lt_of_succ_lt_succ hi)

/-- At dominant D coroots the coordinates before the last read
on their upper sides, each earlier coordinate at or beyond a
later coordinate and its balance partner. -/
theorem coordsD_dominant : ∀ (m : List BPair), 2 ≤ m.length →
    (∀ i, i < m.length → BPair.unit ≤ ground.getAt BPair.unit m i) →
    (∀ i, i + 1 < m.length → BPair.unit ≤ ground.getAt BPair.unit (coordsD m) i)
    ∧ (∀ i j, i < j → j < m.length →
      ground.getAt BPair.unit (coordsD m) j ≤ ground.getAt BPair.unit (coordsD m) i
        ∧ (ground.getAt BPair.unit (coordsD m) j).swap ≤ ground.getAt BPair.unit (coordsD m) i)
  | [], h, _ => absurd h (by decide +kernel)
  | [_], h, _ => absurd h (by decide +kernel : ¬ 2 ≤ 1)
  | [a, b], _, hp => by
    have ha : BPair.unit ≤ a := hp 0 (by decide +kernel : 0 < 2)
    have hb : BPair.unit ≤ b := hp 1 (by decide +kernel : 1 < 2)
    have has : a.swap ≤ a := ground.leB_trans (ground.leB_swap ha) ha
    have hbs : b.swap ≤ b := ground.leB_trans (ground.leB_swap hb) hb
    refine ⟨?_, ?_⟩
    · intro i hi
      have he : i = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ hi))
      rw [he]
      exact ground.unitLeAdd ha hb
    · intro i j hij hj
      cases j with
      | zero => exact absurd hij (Nat.not_lt_zero i)
      | succ j =>
        have hej : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ hj))
        rw [hej] at hij ⊢
        have hei : i = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hij)
        rw [hei]
        change b + a.swap ≤ a + b ∧ (b + a.swap).swap ≤ a + b
        constructor
        · rw [BPair.add_comm b a.swap]
          exact ground.leB_add has (ground.leB_refl b)
        · rw [← BPair.swap_add, BPair.swap_swap, BPair.add_comm a b]
          exact ground.leB_add hbs (ground.leB_refl a)
  | a :: b :: c :: m, _, hp => by
    have ih := coordsD_dominant (b :: c :: m)
      (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _)))
      (fun i hi => hp (i + 1) (Nat.succ_lt_succ hi))
    have ha : BPair.unit ≤ a := hp 0 (Nat.succ_pos _)
    have hhead := ih.1 0 (Nat.succ_lt_succ (Nat.succ_pos _))
    have hgap : ground.getAt BPair.unit (coordsD (b :: c :: m)) 0
        ≤ a + a + ground.getAt BPair.unit (coordsD (b :: c :: m)) 0 :=
      ground.leB_congr_left (BPair.unit_add _) (ground.leB_add (ground.unitLeAdd ha ha) (ground.leB_refl _))
    rw [coordsD_cons a (b :: c :: m) (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _)))]
    refine ⟨?_, ?_⟩
    · intro i hi
      cases i with
      | zero => exact ground.leB_trans hhead hgap
      | succ i => exact ih.1 i (Nat.lt_of_succ_lt_succ hi)
    · intro i j hij hj
      cases j with
      | zero => exact absurd hij (Nat.not_lt_zero i)
      | succ j =>
        cases i with
        | succ i => exact ih.2 i j (Nat.lt_of_succ_lt_succ hij) (Nat.lt_of_succ_lt_succ hj)
        | zero =>
          cases j with
          | zero => exact ⟨hgap, ground.leB_trans (ground.leB_swap hhead) (ground.leB_trans hhead hgap)⟩
          | succ j =>
            have h := ih.2 0 (j + 1) (Nat.succ_pos _) (Nat.lt_of_succ_lt_succ hj)
            exact ⟨ground.leB_trans h.1 hgap, ground.leB_trans h.2 hgap⟩

/-- At strictly positive D coroots, every coordinate before the
last is positive, and an earlier coordinate exceeds both a later
coordinate and its balance partner. -/
theorem coordsD_regular : ∀ (m : List BPair), 2 ≤ m.length →
    (∀ i, i < m.length → BPair.unit < ground.getAt BPair.unit m i) →
    (∀ i, i + 1 < m.length → BPair.unit < ground.getAt BPair.unit (coordsD m) i)
    ∧ (∀ i j, i < j → j < m.length →
      ground.getAt BPair.unit (coordsD m) j < ground.getAt BPair.unit (coordsD m) i
        ∧ (ground.getAt BPair.unit (coordsD m) j).swap < ground.getAt BPair.unit (coordsD m) i)
  | [], h, _ => absurd h (by decide)
  | [_], h, _ => absurd h (by decide : ¬ 2 ≤ 1)
  | [a, b], _, hp => by
    have ha : BPair.unit < a := hp 0 (by decide : 0 < 2)
    have hb : BPair.unit < b := hp 1 (by decide : 1 < 2)
    have has : a.swap < a := ground.ltB_trans_le (ground.ltB_swap ha) (ground.leB_of_lt ha)
    have hbs : b.swap < b := ground.ltB_trans_le (ground.ltB_swap hb) (ground.leB_of_lt hb)
    refine ⟨?_, ?_⟩
    · intro i hi
      have he : i = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ hi))
      rw [he]
      exact ground.unitLtAdd ha (ground.leB_of_lt hb)
    · intro i j hij hj
      cases j with
      | zero => exact absurd hij (Nat.not_lt_zero i)
      | succ j =>
        have hej : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ hj))
        rw [hej] at hij ⊢
        have hei : i = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hij)
        rw [hei]
        change b + a.swap < a + b ∧ (b + a.swap).swap < a + b
        constructor
        · rw [BPair.add_comm b a.swap]
          exact ground.ltB_add has (ground.leB_refl b)
        · rw [← BPair.swap_add, BPair.swap_swap, BPair.add_comm a b]
          exact ground.ltB_add hbs (ground.leB_refl a)
  | a :: b :: c :: m, _, hp => by
    have ih := coordsD_regular (b :: c :: m)
      (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _)))
      (fun i hi => hp (i + 1) (Nat.succ_lt_succ hi))
    have ha : BPair.unit < a := hp 0 (Nat.succ_pos _)
    have hhead := ih.1 0 (Nat.succ_lt_succ (Nat.succ_pos _))
    have hgap : ground.getAt BPair.unit (coordsD (b :: c :: m)) 0
        < a + a + ground.getAt BPair.unit (coordsD (b :: c :: m)) 0 := by
      rw [BPair.add_comm (a + a)]
      exact ground.ltB_addPos (ground.unitLtAdd ha (ground.leB_of_lt ha))
    rw [coordsD_cons a (b :: c :: m) (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _)))]
    refine ⟨?_, ?_⟩
    · intro i hi
      cases i with
      | zero => exact ground.ltB_trans_le hhead (ground.leB_of_lt hgap)
      | succ i => exact ih.1 i (Nat.lt_of_succ_lt_succ hi)
    · intro i j hij hj
      cases j with
      | zero => exact absurd hij (Nat.not_lt_zero i)
      | succ j =>
        cases i with
        | succ i => exact ih.2 i j (Nat.lt_of_succ_lt_succ hij) (Nat.lt_of_succ_lt_succ hj)
        | zero =>
          cases j with
          | zero => exact ⟨hgap, ground.ltB_trans_le (ground.ltB_swap hhead)
              (ground.leB_of_lt (ground.ltB_trans_le hhead (ground.leB_of_lt hgap)))⟩
          | succ j =>
            have h := ih.2 0 (j + 1) (Nat.succ_pos _) (Nat.lt_of_succ_lt_succ hj)
            exact ⟨ground.ltB_trans_le h.1 (ground.leB_of_lt hgap),
              ground.ltB_trans_le h.2 (ground.leB_of_lt hgap)⟩

/-- B's doubled coordinate display has one margin parity at
every key. -/
theorem coordsB_parity (m : List BPair) (i j : Nat) (hi : i < m.length) (hj : j < m.length) :
    (ground.getAt BPair.unit (coordsB m) i).marginN % 2
      = (ground.getAt BPair.unit (coordsB m) j).marginN % 2 := by
  have hlen := ground.length_reverse m
  unfold coordsB coordsSuffix
  cases hr : m.reverse with
  | nil => rw [hr] at hlen; rw [← hlen] at hi; exact absurd hi (Nat.not_lt_zero i)
  | cons a rest =>
    rw [hr] at hlen
    have h := coordsFold_parity (fun x => x + x) BPair.marginN_double rest [a]
      (a.marginN % 2) (Nat.succ_pos 0) (fun k hk => by
        have he : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
        rw [he]; rfl)
    exact (h i (by rw [coordsFold_length]; rw [← hlen] at hi; exact hi)).trans
      (h j (by rw [coordsFold_length]; rw [← hlen] at hj; exact hj)).symm

/-- D's doubled fork display has one margin parity at every key. -/
theorem coordsD_parity (m : List BPair) (hm : 2 ≤ m.length)
    (i j : Nat) (hi : i < m.length) (hj : j < m.length) :
    (ground.getAt BPair.unit (coordsD m) i).marginN % 2
      = (ground.getAt BPair.unit (coordsD m) j).marginN % 2 := by
  have hlen := ground.length_reverse m
  unfold coordsD
  cases hr : m.reverse with
  | nil => rw [hr] at hlen; rw [← hlen] at hi; exact absurd hi (Nat.not_lt_zero i)
  | cons a rest =>
    cases rest with
    | nil => rw [hr] at hlen; rw [← hlen] at hm; exact absurd hm (by decide : ¬ 2 ≤ 1)
    | cons b rest =>
      rw [hr] at hlen
      have h := coordsFold_parity (fun x => x + x) BPair.marginN_double rest
        [b + a, a + b.swap] ((b + a).marginN % 2) (Nat.succ_pos 1) (fun k hk => by
          cases k with
          | zero => rfl
          | succ k =>
            cases k with
            | zero =>
              change (a + b.swap).marginN % 2 = (b + a).marginN % 2
              rw [BPair.marginN_add_mod_two, BPair.marginN_swap,
                BPair.marginN_add_mod_two, Nat.add_comm]
            | succ k => exact absurd hk (Nat.not_lt_of_ge (Nat.succ_le_succ
                (Nat.succ_le_succ (Nat.zero_le k)))))
      exact (h i (by rw [coordsFold_length]; rw [← hlen] at hi; exact hi)).trans
        (h j (by rw [coordsFold_length]; rw [← hlen] at hj; exact hj)).symm

/-- C's suffix solve reads one value across representatives. -/
theorem coordsC_congr (u v : List BPair) (hw : u.length = v.length)
    (h : poly.oneValue u v) : poly.oneValue (coordsC u) (coordsC v) :=
  coordsSuffix_congr _ (fun _ _ h => h) u v hw h

/-- B's doubled suffix solve reads one value across representatives. -/
theorem coordsB_congr (u v : List BPair) (hw : u.length = v.length)
    (h : poly.oneValue u v) : poly.oneValue (coordsB u) (coordsB v) :=
  coordsSuffix_congr _ (fun _ _ h => BPair.add_congr h h) u v hw h

/-- C's coordinate solve returns every occupied coordinate display. -/
theorem coordsC_corootsC : ∀ D : List BPair, 0 < D.length →
    poly.oneValue (coordsC (corootsC D)) D
  | [], h => absurd h (Nat.lt_irrefl 0)
  | [a], _ => ⟨BPair.oneValue_refl a, trivial⟩
  | a :: b :: D, _ => by
    have ih := coordsC_corootsC (b :: D) (Nat.succ_pos _)
    rw [corootsC_cons, coordsC_cons _ _ (by
      rw [corootsC_length (b :: D) (Nat.succ_pos _)]; exact Nat.succ_pos _)]
    exact ⟨BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _) (poly.oneValue_getAt 0 ih))
      (BPair.add_swap_self a b), ih⟩

/-- B's coordinate solve returns a display with even consecutive
gaps, the domain of its signed half reads. -/
theorem coordsB_corootsB : ∀ D : List BPair, 0 < D.length →
    (∀ i, i + 1 < D.length →
      (ground.getAt BPair.unit D i + (ground.getAt BPair.unit D (i + 1)).swap).marginN % 2 = 0) →
    poly.oneValue (coordsB (corootsB D)) D
  | [], h, _ => absurd h (Nat.lt_irrefl 0)
  | [a], _, _ => ⟨BPair.oneValue_refl a, trivial⟩
  | a :: b :: D, _, heven => by
    have ih := coordsB_corootsB (b :: D) (Nat.succ_pos _)
      (fun i hi => heven (i + 1) (Nat.succ_lt_succ hi))
    rw [corootsB_cons, coordsB_cons _ _ (by
      rw [corootsB_length (b :: D) (Nat.succ_pos _)]; exact Nat.succ_pos _)]
    exact ⟨BPair.oneValue_trans
      (BPair.add_congr (halfB_read (a + b.swap) (heven 0 (Nat.succ_lt_succ (Nat.succ_pos _))))
        (poly.oneValue_getAt 0 ih)) (BPair.add_swap_self a b), ih⟩

/-- B's canonical coroot keys identify coordinate displays whose
consecutive gaps have even margins. -/
theorem corootsB_inj (D E : List BPair) (hw : D.length = E.length)
    (hD : 0 < D.length)
    (hd : ∀ i, i + 1 < D.length →
      (ground.getAt BPair.unit D i + (ground.getAt BPair.unit D (i + 1)).swap).marginN % 2 = 0)
    (he : ∀ i, i + 1 < E.length →
      (ground.getAt BPair.unit E i + (ground.getAt BPair.unit E (i + 1)).swap).marginN % 2 = 0)
    (h : poly.pnorm (corootsB D) = poly.pnorm (corootsB E)) : poly.oneValue D E := by
  have hE : 0 < E.length := by rw [← hw]; exact hD
  have hkey : poly.oneValue (corootsB D) (corootsB E) := by
    refine poly.oneValue_trans (poly.oneValue_symm (poly.pnorm_oneValue _)) ?_
    rw [h]
    exact poly.pnorm_oneValue _
  exact poly.oneValue_trans (poly.oneValue_symm (coordsB_corootsB D hD hd))
    (poly.oneValue_trans (coordsB_congr _ _
      ((corootsB_length D hD).trans (hw.trans (corootsB_length E hE).symm)) hkey)
      (coordsB_corootsB E hE he))

/-- D's fork solve reads one value across representatives. -/
theorem coordsD_congr : ∀ u v : List BPair, u.length = v.length → poly.oneValue u v →
    poly.oneValue (coordsD u) (coordsD v)
  | [], [], _, _ => trivial
  | [], _ :: _, h, _ => Nat.noConfusion h
  | _ :: _, [], h, _ => Nat.noConfusion h
  | a :: u, b :: v, hw, h => by
    cases u with
    | nil =>
      cases v with
      | nil => trivial
      | cons _ _ => exact Nat.noConfusion (Nat.succ.inj hw)
    | cons c u =>
      cases v with
      | nil => exact Nat.noConfusion (Nat.succ.inj hw)
      | cons d v =>
        cases u with
        | nil =>
          cases v with
          | nil => exact ⟨BPair.add_congr h.1 h.2.1,
              BPair.add_congr h.2.1 (ground.swap_congr h.1), trivial⟩
          | cons _ _ => exact Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hw))
        | cons e u =>
          cases v with
          | nil => exact Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hw))
          | cons f v =>
            have ih := coordsD_congr (c :: e :: u) (d :: f :: v) (Nat.succ.inj hw) h.2
            rw [coordsD_cons a (c :: e :: u) (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))),
              coordsD_cons b (d :: f :: v) (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _)))]
            exact ⟨BPair.add_congr (BPair.add_congr h.1 h.1) (poly.oneValue_getAt 0 ih), ih⟩

private theorem coordsD_corootsD_pair (a b : BPair)
    (hd : (a + b.swap).marginN % 2 = 0) :
    poly.oneValue (coordsD (corootsD [a, b])) [a, b] := by
  have hs : (a + b).marginN % 2 = 0 := by
    rw [BPair.marginN_add_mod_two, BPair.marginN_swap] at hd
    rw [BPair.marginN_add_mod_two]
    exact hd
  let x := halfB (a + b.swap)
  let y := halfB (a + b)
  have hx : (x + x).oneValue (a + b.swap) := halfB_read _ hd
  have hy : (y + y).oneValue (a + b) := halfB_read _ hs
  have hfirst : (x + y + (x + y)).oneValue (a + a) := by
    rw [BPair.add_add_comm x y x y]
    refine BPair.oneValue_trans (BPair.add_congr hx hy) ?_
    rw [BPair.add_add_comm a b.swap a b]
    exact BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _) (BPair.swap_add_null (BPair.oneValue_refl b)))
      (BPair.add_unit _)
  have hsecond : (y + x.swap + (y + x.swap)).oneValue (b + b) := by
    rw [BPair.add_add_comm y x.swap y x.swap, BPair.swap_add]
    refine BPair.oneValue_trans (BPair.add_congr hy (ground.swap_congr hx)) ?_
    rw [← BPair.swap_add, BPair.swap_swap, BPair.add_add_comm a b a.swap b]
    exact BPair.oneValue_trans
      (BPair.add_congr (BPair.add_swap_null a) (BPair.oneValue_refl _))
      (BPair.unit_add _)
  rw [← BPair.scale_two (x + y), ← BPair.scale_two a] at hfirst
  rw [← BPair.scale_two (y + x.swap), ← BPair.scale_two b] at hsecond
  exact ⟨BPair.scale_cancel hfirst, BPair.scale_cancel hsecond, trivial⟩

/-- D's coordinate solve returns a display with even consecutive
gaps; the last gap's parity also gives the fork sum's parity. -/
theorem coordsD_corootsD : ∀ D : List BPair, 2 ≤ D.length →
    (∀ i, i + 1 < D.length →
      (ground.getAt BPair.unit D i + (ground.getAt BPair.unit D (i + 1)).swap).marginN % 2 = 0) →
    poly.oneValue (coordsD (corootsD D)) D
  | [], h, _ => absurd h (by decide)
  | [_], h, _ => absurd h (by decide : ¬ 2 ≤ 1)
  | [a, b], _, hd => coordsD_corootsD_pair a b (hd 0 (Nat.succ_lt_succ (Nat.succ_pos 0)))
  | a :: b :: c :: D, _, hd => by
    have ih := coordsD_corootsD (b :: c :: D)
      (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _)))
      (fun i hi => hd (i + 1) (Nat.succ_lt_succ hi))
    rw [corootsD_cons, coordsD_cons _ _ (by
      rw [corootsD_length (b :: c :: D) (Nat.succ_pos _)]
      exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _)))]
    exact ⟨BPair.oneValue_trans
      (BPair.add_congr (halfB_read (a + b.swap) (hd 0 (Nat.succ_lt_succ (Nat.succ_pos _))))
        (poly.oneValue_getAt 0 ih)) (BPair.add_swap_self a b), ih⟩

/-- D's canonical coroot keys identify the doubled-coordinate
displays at the half reads' even margins. -/
theorem corootsD_inj (D E : List BPair) (hw : D.length = E.length) (hD : 2 ≤ D.length)
    (hd : ∀ i, i + 1 < D.length →
      (ground.getAt BPair.unit D i + (ground.getAt BPair.unit D (i + 1)).swap).marginN % 2 = 0)
    (he : ∀ i, i + 1 < E.length →
      (ground.getAt BPair.unit E i + (ground.getAt BPair.unit E (i + 1)).swap).marginN % 2 = 0)
    (h : poly.pnorm (corootsD D) = poly.pnorm (corootsD E)) : poly.oneValue D E := by
  have hE : 2 ≤ E.length := by rw [← hw]; exact hD
  have hpD : 0 < D.length := Nat.lt_of_lt_of_le (by decide : 0 < 2) hD
  have hpE : 0 < E.length := Nat.lt_of_lt_of_le (by decide : 0 < 2) hE
  have hkey : poly.oneValue (corootsD D) (corootsD E) := by
    refine poly.oneValue_trans (poly.oneValue_symm (poly.pnorm_oneValue _)) ?_
    rw [h]
    exact poly.pnorm_oneValue _
  exact poly.oneValue_trans (poly.oneValue_symm (coordsD_corootsD D hD hd))
    (poly.oneValue_trans (coordsD_congr _ _
      ((corootsD_length D hpD).trans (hw.trans (corootsD_length E hpE).symm)) hkey)
      (coordsD_corootsD E hE he))

/-- C's canonical coroot keys identify their coordinate displays. -/
theorem corootsC_inj (D E : List BPair) (hw : D.length = E.length)
    (hD : 0 < D.length) (h : poly.pnorm (corootsC D) = poly.pnorm (corootsC E)) :
    poly.oneValue D E := by
  have hE : 0 < E.length := by rw [← hw]; exact hD
  have hkey : poly.oneValue (corootsC D) (corootsC E) := by
    refine poly.oneValue_trans (poly.oneValue_symm (poly.pnorm_oneValue _)) ?_
    rw [h]
    exact poly.pnorm_oneValue _
  exact poly.oneValue_trans (poly.oneValue_symm (coordsC_corootsC D hD))
    (poly.oneValue_trans (coordsC_congr _ _
      ((corootsC_length D hD).trans (hw.trans (corootsC_length E hE).symm)) hkey)
      (coordsC_corootsC E hE))

/-- Nonnegative coroots give nonnegative suffix coordinates in
weakly decreasing order, at any nonnegative scaling read. -/
private theorem coordsSuffix_weak (scale : BPair → BPair)
    (hs : ∀ x, BPair.unit ≤ x → BPair.unit ≤ scale x) :
    ∀ m : List BPair, (∀ i, i < m.length → BPair.unit ≤ ground.getAt BPair.unit m i) →
      (∀ i, i < m.length → BPair.unit ≤ ground.getAt BPair.unit (coordsSuffix scale m) i)
      ∧ (∀ i j, i < j → j < m.length →
        ground.getAt BPair.unit (coordsSuffix scale m) j
          ≤ ground.getAt BPair.unit (coordsSuffix scale m) i)
  | [], _ => ⟨fun i hi => absurd hi (Nat.not_lt_zero i),
      fun _ j _ hj => absurd hj (Nat.not_lt_zero j)⟩
  | [a], hp => by
    refine ⟨?_, ?_⟩
    · intro i hi
      have he : i = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hi)
      rw [he]
      exact hp 0 (Nat.succ_pos 0)
    · intro i j hij hj
      have he : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj)
      rw [he] at hij
      exact absurd hij (Nat.not_lt_zero i)
  | a :: b :: m, hp => by
    have ih := coordsSuffix_weak scale hs (b :: m)
      (fun i hi => hp (i + 1) (Nat.succ_lt_succ hi))
    have hgap : ground.getAt BPair.unit (coordsSuffix scale (b :: m)) 0
        ≤ scale a + ground.getAt BPair.unit (coordsSuffix scale (b :: m)) 0 :=
      ground.leB_congr_left (BPair.unit_add _)
        (ground.leB_add (hs a (hp 0 (Nat.succ_pos _))) (ground.leB_refl _))
    rw [coordsSuffix_cons scale a (b :: m) (Nat.succ_pos _)]
    refine ⟨?_, ?_⟩
    · intro i hi
      cases i with
      | zero => exact ground.leB_trans (ih.1 0 (Nat.succ_pos _)) hgap
      | succ i => exact ih.1 i (Nat.lt_of_succ_lt_succ hi)
    · intro i j hij hj
      cases j with
      | zero => exact absurd hij (Nat.not_lt_zero i)
      | succ j =>
        cases i with
        | zero =>
          cases j with
          | zero => exact hgap
          | succ j =>
            exact ground.leB_trans
              (ih.2 0 (j + 1) (Nat.succ_pos _) (Nat.lt_of_succ_lt_succ hj)) hgap
        | succ i => exact ih.2 i j (Nat.lt_of_succ_lt_succ hij) (Nat.lt_of_succ_lt_succ hj)

/-- Dominant C coroots have nonnegative weakly decreasing
coordinates, including walls and the unit content. -/
theorem coordsC_dominant (m : List BPair)
    (hp : ∀ i, i < m.length → BPair.unit ≤ ground.getAt BPair.unit m i) :
    (∀ i, i < m.length → BPair.unit ≤ ground.getAt BPair.unit (coordsC m) i)
    ∧ (∀ i j, i < j → j < m.length →
      ground.getAt BPair.unit (coordsC m) j ≤ ground.getAt BPair.unit (coordsC m) i) :=
  coordsSuffix_weak _ (fun _ h => h) m hp

/-- Dominant B coroots have nonnegative weakly decreasing
doubled coordinates, including walls and the unit content. -/
theorem coordsB_dominant (m : List BPair)
    (hp : ∀ i, i < m.length → BPair.unit ≤ ground.getAt BPair.unit m i) :
    (∀ i, i < m.length → BPair.unit ≤ ground.getAt BPair.unit (coordsB m) i)
    ∧ (∀ i j, i < j → j < m.length →
      ground.getAt BPair.unit (coordsB m) j ≤ ground.getAt BPair.unit (coordsB m) i) :=
  coordsSuffix_weak _ (fun _ h => ground.leB_congr_left (BPair.unit_add _) (ground.leB_add h h)) m hp

private theorem coordsSuffix_regular (scale : BPair → BPair)
    (hs : ∀ x, BPair.unit < x → BPair.unit < scale x) :
    ∀ m : List BPair, (∀ i, i < m.length → BPair.unit < ground.getAt BPair.unit m i) →
      (∀ i, i < m.length → BPair.unit < ground.getAt BPair.unit (coordsSuffix scale m) i)
      ∧ (∀ i j, i < j → j < m.length →
        ground.getAt BPair.unit (coordsSuffix scale m) j
          < ground.getAt BPair.unit (coordsSuffix scale m) i)
  | [], _ => ⟨fun i hi => absurd hi (Nat.not_lt_zero i),
      fun _ j _ hj => absurd hj (Nat.not_lt_zero j)⟩
  | [a], hp => by
    refine ⟨?_, ?_⟩
    · intro i hi
      have he : i = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hi)
      rw [he]
      exact hp 0 (Nat.succ_pos 0)
    · intro i j hij hj
      have he : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj)
      rw [he] at hij
      exact absurd hij (Nat.not_lt_zero i)
  | a :: b :: m, hp => by
    have ih := coordsSuffix_regular scale hs (b :: m)
      (fun i hi => hp (i + 1) (Nat.succ_lt_succ hi))
    have hgap : ground.getAt BPair.unit (coordsSuffix scale (b :: m)) 0
        < scale a + ground.getAt BPair.unit (coordsSuffix scale (b :: m)) 0 := by
      rw [BPair.add_comm]
      exact ground.ltB_addPos (hs a (hp 0 (Nat.succ_pos _)))
    have hhead : BPair.unit < scale a + ground.getAt BPair.unit (coordsSuffix scale (b :: m)) 0 :=
      ground.ltB_trans_le (ih.1 0 (Nat.succ_pos _)) (ground.leB_of_lt hgap)
    rw [coordsSuffix_cons scale a (b :: m) (Nat.succ_pos _)]
    refine ⟨?_, ?_⟩
    · intro i hi
      cases i with
      | zero => exact hhead
      | succ i => exact ih.1 i (Nat.lt_of_succ_lt_succ hi)
    · intro i j hij hj
      cases j with
      | zero => exact absurd hij (Nat.not_lt_zero i)
      | succ j =>
        cases i with
        | zero =>
          cases j with
          | zero => exact hgap
          | succ j =>
            exact ground.ltB_trans_le
              (ih.2 0 (j + 1) (Nat.succ_pos _) (Nat.lt_of_succ_lt_succ hj))
              (ground.leB_of_lt hgap)
        | succ i => exact ih.2 i j (Nat.lt_of_succ_lt_succ hij) (Nat.lt_of_succ_lt_succ hj)

/-- A strictly dominant C coroot list has positive, strictly
decreasing coordinates. -/
theorem coordsC_regular (m : List BPair)
    (hp : ∀ i, i < m.length → BPair.unit < ground.getAt BPair.unit m i) :
    (∀ i, i < m.length → BPair.unit < ground.getAt BPair.unit (coordsC m) i)
    ∧ (∀ i j, i < j → j < m.length →
      ground.getAt BPair.unit (coordsC m) j < ground.getAt BPair.unit (coordsC m) i) :=
  coordsSuffix_regular _ (fun _ h => h) m hp

/-- A strictly dominant B coroot list has positive, strictly
decreasing doubled coordinates. -/
theorem coordsB_regular (m : List BPair)
    (hp : ∀ i, i < m.length → BPair.unit < ground.getAt BPair.unit m i) :
    (∀ i, i < m.length → BPair.unit < ground.getAt BPair.unit (coordsB m) i)
    ∧ (∀ i j, i < j → j < m.length →
      ground.getAt BPair.unit (coordsB m) j < ground.getAt BPair.unit (coordsB m) i) := by
  refine coordsSuffix_regular _ (fun x hx => ?_) m hp
  exact BPair.lt_congr (BPair.add_unit _) (BPair.oneValue_refl _)
    (ground.ltB_add hx (ground.leB_of_lt hx))

/-- The sign code at the sum's unit has even parity. -/
theorem flipParity_zero (l : Nat) : flipParity l 0 = false := by
  unfold flipParity
  rw [ground.foldlSum, Nat.zero_add, ground.famFold_zero (fun q => baseDigit 2 q 0)
    (fun q => baseDigit_of_lt 2 q 0 (by decide) (Nat.pow_pos (by decide)))]
  rfl

private theorem serWeylGo_mem (coords coroots : List BPair → List BPair)
    (flipsAll : Bool) (l : Nat) (v : List BPair) (p : List Nat) (n : Nat)
    (hp : p ∈ places.perms l) (hn : n < 2 ^ l)
    (ha : (flipsAll || !(flipParity l n)) = true) :
    (poly.pnorm (coroots (signedImage l (coords v) p n)),
      if flipsAll then places.parity p != flipParity l n else places.parity p)
        ∈ serWeylGo coords coroots flipsAll l v := by
  refine ground.mem_flatMap_to _ hp (ground.mem_filterMap_to _ (a := n) ?_ ?_)
  · exact ground.mem_of_countOf_pos n _ (by
      rw [ground.countOf_range, if_pos hn]; exact Nat.succ_pos 0)
  · rw [if_pos ha]

private theorem serWeylGo_of_mem (coords coroots : List BPair → List BPair)
    (flipsAll : Bool) (l : Nat) (v : List BPair) (w : List BPair × Bool)
    (hw : w ∈ serWeylGo coords coroots flipsAll l v) :
    ∃ p, p ∈ places.perms l ∧ ∃ n, n < 2 ^ l
      ∧ (flipsAll || !(flipParity l n)) = true
      ∧ w = (poly.pnorm (coroots (signedImage l (coords v) p n)),
        if flipsAll then places.parity p != flipParity l n else places.parity p) := by
  obtain ⟨p, hp, hw⟩ := ground.mem_flatMap_of _ _ w hw
  obtain ⟨n, hn, he⟩ := ground.mem_filterMap_of _ _ w hw
  by_cases h : (flipsAll || !(flipParity l n)) = true
  · rw [if_pos h] at he
    exact ⟨p, hp, n, ground.ltOfMem (ground.countOf_pos_of_mem hn), h, (Option.some.inj he).symm⟩
  · rw [if_neg h] at he
    exact nomatch he

/-- Permuting a sign code's places keeps its flip parity. -/
theorem flipParity_reindex (l n m : Nat) (q : List Nat)
    (hq : 0 < ground.countOf q (places.perms l))
    (hd : ∀ i, i < l → baseDigit 2 i m = baseDigit 2 (ground.getAt 0 q i) n) :
    flipParity l m = flipParity l n := by
  have hlen := (places.perm_member_reads hq).1
  have hs : ground.famFold Nat.add 0 (fun i => baseDigit 2 i m) (List.range l)
      = ground.famFold Nat.add 0 (fun i => baseDigit 2 i n) (List.range l) := by
    rw [ground.famFold_congr_members Nat.add 0 _
      (fun i => baseDigit 2 (ground.getAt 0 q i) n) (List.range l)
      (fun i hi => hd i (ground.ltOfMem hi)),
      ← ground.famFold_map Nat.add 0 (fun i => baseDigit 2 i n) (ground.getAt 0 q),
      ground.range_map_getAt 0 l q hlen]
    exact ground.famFold_relist Nat.add 0 Nat.add_comm Nat.add_assoc _ q (List.range l)
      (places.perm_counts_range l hq)
  unfold flipParity
  rw [ground.foldlSum, ground.foldlSum, Nat.zero_add, Nat.zero_add, hs]

/-- A permutation of the output coordinates is another signed
image with the sign code's parity kept. -/
theorem signedImage_permute (l : Nat) (D : List BPair) (p q : List Nat) (n : Nat)
    (hq : 0 < ground.countOf q (places.perms l)) :
    ∃ m, m < 2 ^ l ∧ flipParity l m = flipParity l n
      ∧ signedImage l D (places.expo p q) m
        = (List.range l).map (fun i =>
          ground.getAt BPair.unit (signedImage l D p n) (ground.getAt 0 q i)) := by
  obtain ⟨m, hm, hd⟩ := ground.baseDigit_exists 2 (by decide) l
    (fun i => baseDigit 2 (ground.getAt 0 q i) n)
    (fun _ _ => ground.baseDigit_lt 2 _ n (by decide))
  refine ⟨m, hm, flipParity_reindex l n m q hq hd, ?_⟩
  have hlen := (places.perm_member_reads hq).1
  refine ground.map_congr_members _ _ _ (fun i hi => ?_)
  have hil := ground.ltOfMem hi
  rw [signedImage_getAt l D p n _ (places.perm_lt l hq i hil), hd i hil]
  change (if baseDigit 2 (ground.getAt 0 q i) n == 1 then
      (ground.getAt BPair.unit D (ground.getAt 0 (q.map (ground.getAt 0 p)) i)).swap
    else ground.getAt BPair.unit D (ground.getAt 0 (q.map (ground.getAt 0 p)) i)) = _
  rw [ground.getAt_map 0 0 _ q i (by rw [hlen]; exact hil)]

/-- At distinct positive coordinates, a signed image identifies
both its permutation and its sign code. -/
theorem signedImage_inj (l : Nat) (D : List BPair)
    (hpos : ∀ i, i < l → BPair.unit < ground.getAt BPair.unit D i)
    (hsep : ∀ i j, i < l → j < l →
      (ground.getAt BPair.unit D i).oneValue (ground.getAt BPair.unit D j) → i = j)
    (p q : List Nat) (n m : Nat)
    (hp : 0 < ground.countOf p (places.perms l))
    (hq : 0 < ground.countOf q (places.perms l))
    (hn : n < 2 ^ l) (hm : m < 2 ^ l)
    (he : poly.oneValue (signedImage l D p n) (signedImage l D q m)) :
    p = q ∧ n = m := by
  have hentry : ∀ i, i < l → ground.getAt 0 p i = ground.getAt 0 q i
      ∧ baseDigit 2 i n = baseDigit 2 i m := by
    intro i hi
    have hip := places.perm_lt l hp i hi
    have hiq := places.perm_lt l hq i hi
    have h := poly.oneValue_getAt i he
    rw [signedImage_getAt l D p n i hi, signedImage_getAt l D q m i hi] at h
    have hbits : ∀ a, a < 2 → ∀ b, b < 2 → (a == 1) = (b == 1) → a = b := by
      decide +kernel
    cases hn' : (baseDigit 2 i n == 1) with
    | false =>
      cases hm' : (baseDigit 2 i m == 1) with
      | false =>
        rw [hn', hm'] at h
        exact ⟨hsep _ _ hip hiq h,
          hbits _ (ground.baseDigit_lt 2 i n (by decide))
            _ (ground.baseDigit_lt 2 i m (by decide)) (hn'.trans hm'.symm)⟩
      | true =>
        rw [hn', hm'] at h
        have hneg : (ground.getAt BPair.unit D (ground.getAt 0 q i)).swap < BPair.unit :=
          ground.ltB_swap (hpos _ hiq)
        exact False.elim ((ground.leB_not_lt (ground.leB_of_lt (hpos _ hip)))
          (BPair.lt_congr (BPair.oneValue_symm h) (BPair.oneValue_refl _) hneg))
    | true =>
      cases hm' : (baseDigit 2 i m == 1) with
      | false =>
        rw [hn', hm'] at h
        have hneg : (ground.getAt BPair.unit D (ground.getAt 0 p i)).swap < BPair.unit :=
          ground.ltB_swap (hpos _ hip)
        exact False.elim ((ground.leB_not_lt (ground.leB_of_lt (hpos _ hiq)))
          (BPair.lt_congr h (BPair.oneValue_refl _) hneg))
      | true =>
        rw [hn', hm'] at h
        exact ⟨hsep _ _ hip hiq (ground.swap_congr h),
          hbits _ (ground.baseDigit_lt 2 i n (by decide))
            _ (ground.baseDigit_lt 2 i m (by decide)) (hn'.trans hm'.symm)⟩
  have hpl := (places.perm_member_reads hp).1
  have hql := (places.perm_member_reads hq).1
  exact ⟨ground.getAt_ext 0 p q (hpl.trans hql.symm)
      (fun i hi => (hentry i (by rw [← hpl]; exact hi)).1),
    ground.baseDigit_ext 2 (by decide) l n m hn hm (fun i hi => (hentry i hi).2)⟩

/-- A sign code keeps each selected coordinate's magnitude. -/
theorem signedImage_margin (l : Nat) (D : List BPair) (p : List Nat) (n i : Nat)
    (hi : i < l) :
    (ground.getAt BPair.unit (signedImage l D p n) i).marginN
      = (ground.getAt BPair.unit D (ground.getAt 0 p i)).marginN := by
  rw [signedImage_getAt l D p n i hi]
  cases h : (baseDigit 2 i n == 1) with
  | false => rfl
  | true => exact BPair.marginN_swap _

/-- A signed permutation of coordinates at one parity has even
consecutive gaps, the domain of the doubled coroot reads. -/
theorem signedImage_even_gaps (l : Nat) (D : List BPair) (p : List Nat) (n : Nat)
    (hp : 0 < ground.countOf p (places.perms l))
    (hpar : ∀ i j, i < l → j < l →
      (ground.getAt BPair.unit D i).marginN % 2 = (ground.getAt BPair.unit D j).marginN % 2) :
    ∀ i, i + 1 < l →
      (ground.getAt BPair.unit (signedImage l D p n) i
        + (ground.getAt BPair.unit (signedImage l D p n) (i + 1)).swap).marginN % 2 = 0 := by
  intro i hi
  apply BPair.marginN_add_even
  rw [BPair.marginN_swap, signedImage_margin l D p n i (Nat.lt_of_succ_lt hi),
    signedImage_margin l D p n (i + 1) hi]
  exact hpar _ _ (places.perm_lt l hp i (Nat.lt_of_succ_lt hi)) (places.perm_lt l hp (i + 1) hi)

private theorem parityMod_succ (a : Nat) :
    ((a + 1) % 2 == 1) = !(a % 2 == 1) := by
  rw [← ground.modAdd a 1 2]
  have h : ∀ r, r < 2 → ((r + 1) % 2 == 1) = !(r == 1) := by decide +kernel
  exact h (a % 2) (Nat.mod_lt a (by decide))

private theorem parityMod_add (a b : Nat) :
    ((a + b) % 2 == 1) = xor (a % 2 == 1) (b % 2 == 1) := by
  rw [← ground.modAdd a b 2]
  have h : ∀ a, a < 2 → ∀ b, b < 2 →
      ((a + b) % 2 == 1) = xor (a == 1) (b == 1) := by decide +kernel
  exact h _ (Nat.mod_lt a (by decide)) _ (Nat.mod_lt b (by decide))

/-- Signed images compose at the composed place assignment. The
flip parity is the sum of the two sign parities. -/
theorem signedImage_compose (l : Nat) (D : List BPair) (p q : List Nat) (n m : Nat)
    (hq : 0 < ground.countOf q (places.perms l)) :
    ∃ k, k < 2 ^ l ∧ flipParity l k = xor (flipParity l n) (flipParity l m)
      ∧ signedImage l (signedImage l D p n) q m = signedImage l D (places.expo p q) k := by
  let dn := fun i => baseDigit 2 (ground.getAt 0 q i) n
  let dm := fun i => baseDigit 2 i m
  obtain ⟨k, hk, hd⟩ := ground.baseDigit_exists 2 (by decide) l
    (fun i => (dn i + dm i) % 2) (fun i _ => Nat.mod_lt _ (by decide))
  have hlen := (places.perm_member_reads hq).1
  have hperm : ground.famFold Nat.add 0 dn (List.range l)
      = ground.famFold Nat.add 0 (fun i => baseDigit 2 i n) (List.range l) := by
    rw [show ground.famFold Nat.add 0 dn (List.range l)
      = ground.famFold Nat.add 0 (fun i => baseDigit 2 i n)
        ((List.range l).map (ground.getAt 0 q)) from
      (ground.famFold_map Nat.add 0 (fun i => baseDigit 2 i n) (ground.getAt 0 q) (List.range l)).symm,
      ground.range_map_getAt 0 l q hlen]
    exact ground.famFold_relist Nat.add 0 Nat.add_comm Nat.add_assoc _ q (List.range l)
      (places.perm_counts_range l hq)
  have hsum := ground.famFold_mod_congr 2 (fun i => baseDigit 2 i k)
    (fun i => dn i + dm i) (List.range l) (fun i hi => by
      rw [hd i (ground.ltOfMem (ground.countOf_pos_of_mem hi)), ground.modMod])
  rw [ground.famFold_add_split, hperm] at hsum
  refine ⟨k, hk, ?_, ?_⟩
  · unfold flipParity
    rw [ground.foldlSum, ground.foldlSum, ground.foldlSum,
      Nat.zero_add, Nat.zero_add, Nat.zero_add, hsum, parityMod_add]
  · refine ground.map_congr_members _ _ _ (fun i hi => ?_)
    have hil := ground.ltOfMem hi
    have hiq := places.perm_lt l hq i hil
    have hcode := hd i hil
    change (if baseDigit 2 i m == 1 then
        (ground.getAt BPair.unit (signedImage l D p n) (ground.getAt 0 q i)).swap
      else ground.getAt BPair.unit (signedImage l D p n) (ground.getAt 0 q i))
      = if baseDigit 2 i k == 1 then
          (ground.getAt BPair.unit D (ground.getAt 0 (q.map (ground.getAt 0 p)) i)).swap
        else ground.getAt BPair.unit D (ground.getAt 0 (q.map (ground.getAt 0 p)) i)
    rw [signedImage_getAt l D p n _ hiq,
      ground.getAt_map 0 0 _ q i (by rw [hlen]; exact hil), hcode]
    rw [parityMod_add, ground.modOfLt (dn i) 2 (ground.baseDigit_lt 2 _ n (by decide)),
      ground.modOfLt (dm i) 2 (ground.baseDigit_lt 2 i m (by decide))]
    change (if dm i == 1 then
        (if dn i == 1 then (ground.getAt BPair.unit D (ground.getAt 0 p (ground.getAt 0 q i))).swap
          else ground.getAt BPair.unit D (ground.getAt 0 p (ground.getAt 0 q i))).swap
      else (if dn i == 1 then (ground.getAt BPair.unit D (ground.getAt 0 p (ground.getAt 0 q i))).swap
          else ground.getAt BPair.unit D (ground.getAt 0 p (ground.getAt 0 q i)))) = _
    cases hn' : (dn i == 1) <;> cases hm' : (dm i == 1) <;> rfl

/-- A signed permutation keeps the coordinate pairing, at a
common sign code on its two arguments. -/
theorem signedImage_dot (l : Nat) (D E : List BPair) (p : List Nat) (n : Nat)
    (hD : D.length = l) (hE : E.length = l)
    (hp : 0 < ground.countOf p (places.perms l)) :
    (elim.dotP (signedImage l D p n) (signedImage l E p n)).oneValue (elim.dotP D E) := by
  have hpl := (places.perm_member_reads hp).1
  have he : elim.dotP (signedImage l D p n) (signedImage l E p n)
      = ground.famFold BPair.add BPair.unit
        (fun i => ground.getAt BPair.unit D (ground.getAt 0 p i)
          * ground.getAt BPair.unit E (ground.getAt 0 p i)) (List.range l) := by
    rw [signedImage, signedImage, elim.dotP_map_pair]
    refine ground.famFold_congr_all _ _ _ _ (fun i => ?_) _
    cases h : (baseDigit 2 i n == 1) with
    | false => rfl
    | true => exact BPair.swap_mul_swap _ _
  rw [he, ← ground.famFold_map BPair.add BPair.unit
      (fun i => ground.getAt BPair.unit D i * ground.getAt BPair.unit E i) (ground.getAt 0 p),
    ground.range_map_getAt 0 l p hpl]
  have hr := ground.famFold_relist_ov ground.bpairFoldLaws.toCommLaws BPair.unit
    (fun i => ground.getAt BPair.unit D i * ground.getAt BPair.unit E i) p (List.range l)
    (places.perm_counts_range l hp)
  refine BPair.oneValue_trans hr ?_
  have hD' := ground.range_map_getAt BPair.unit l D hD
  have hE' := ground.range_map_getAt BPair.unit l E hE
  have hdot := elim.dotP_map_pair (ground.getAt BPair.unit D) (ground.getAt BPair.unit E) (List.range l)
  rw [hD', hE'] at hdot
  exact BPair.oneValue_of_eq hdot.symm

/-- Joining one unoccupied bit flips the sign code's parity. -/
theorem flipParity_step (l i n : Nat) (hi : i < l) (hz : baseDigit 2 i n = 0) :
    flipParity l (n + 2 ^ i) = !(flipParity l n) := by
  have hb : baseDigit 2 i n + 1 < 2 := by rw [hz]; decide
  have hd : ∀ j, j < l → baseDigit 2 j (n + 2 ^ i)
      = baseDigit 2 j n + (if j = i then 1 else 0) := by
    intro j _
    by_cases hj : j = i
    · rw [hj, if_pos rfl, ground.baseDigit_step 2 i n (by decide) hb]
    · rw [if_neg hj, Nat.add_zero]
      cases Nat.lt_or_ge j i with
      | inl hji =>
        have h := ground.baseDigit_add_high 2 j i n 1 (by decide) hji
        rw [Nat.one_mul] at h
        exact h
      | inr hij =>
        exact ground.baseDigit_step_high 2 i j n (by decide) hb
          (Nat.lt_of_le_of_ne hij (fun he => hj he.symm))
  have hs : ground.famFold Nat.add 0 (fun j => baseDigit 2 j (n + 2 ^ i)) (List.range l)
      = ground.famFold Nat.add 0 (fun j => baseDigit 2 j n) (List.range l) + 1 := by
    rw [ground.famFold_congr_members Nat.add 0 _
      (fun j => baseDigit 2 j n + (if j = i then 1 else 0)) (List.range l)
      (fun j hj => hd j (ground.ltOfMem hj)), ground.famFold_add_split]
    rw [ground.famFold_pick (fun _ => 1) i (List.range l) (by
      rw [ground.countOf_range, if_pos hi])]
  unfold flipParity
  rw [ground.foldlSum, ground.foldlSum, Nat.zero_add, Nat.zero_add, hs, parityMod_succ]

/-- Every code has a code with exactly one bit flipped, and its
parity is the opposite one. -/
theorem flipParity_flip (l i n : Nat) (hi : i < l) (hn : n < 2 ^ l) :
    ∃ m, m < 2 ^ l ∧ flipParity l m = !(flipParity l n)
      ∧ baseDigit 2 i m + baseDigit 2 i n = 1
      ∧ ∀ j, j < l → j ≠ i → baseDigit 2 j m = baseDigit 2 j n := by
  cases hz : baseDigit 2 i n with
  | zero =>
    have hb : baseDigit 2 i n + 1 < 2 := by rw [hz]; decide
    refine ⟨n + 2 ^ i, ground.stepLtPow 2 i l n (by decide) hn hi hb,
      flipParity_step l i n hi hz, ?_, ?_⟩
    · rw [ground.baseDigit_step 2 i n (by decide) hb, hz]
    · intro j _ hji
      cases Nat.lt_or_ge j i with
      | inl hlt =>
        have h := ground.baseDigit_add_high 2 j i n 1 (by decide) hlt
        rw [Nat.one_mul] at h
        exact h
      | inr hle =>
        exact ground.baseDigit_step_high 2 i j n (by decide) hb
          (Nat.lt_of_le_of_ne hle (fun he => hji he.symm))
  | succ k =>
    have hone : baseDigit 2 i n = 1 := Nat.le_antisymm
      (Nat.le_of_lt_succ (ground.baseDigit_lt 2 i n (by decide)))
      (by rw [hz]; exact Nat.succ_pos k)
    obtain ⟨hjoin, hbit, hother⟩ := ground.stepBack 2 i n (by decide) (by rw [hone]; decide)
    have hzero : baseDigit 2 i (n - 2 ^ i) = 0 := by
      rw [hone] at hbit
      exact Nat.succ.inj hbit
    have hp := flipParity_step l i (n - 2 ^ i) hi hzero
    rw [hjoin] at hp
    refine ⟨n - 2 ^ i, Nat.lt_of_le_of_lt (Nat.sub_le _ _) hn, ?_, ?_,
      fun j _ hj => hother j hj⟩
    · rw [hp, Bool.not_not]
    · rw [hzero, Nat.zero_add]
      exact hz.symm.trans hone

/-- Flipping one output coordinate is another signed image, at
the opposite flip parity. -/
theorem signedImage_flip (l i n : Nat) (D : List BPair) (p : List Nat)
    (hi : i < l) (hn : n < 2 ^ l) :
    ∃ m, m < 2 ^ l ∧ flipParity l m = !(flipParity l n)
      ∧ signedImage l D p m = (List.range l).map (fun j =>
        if j = i then (ground.getAt BPair.unit (signedImage l D p n) j).swap
        else ground.getAt BPair.unit (signedImage l D p n) j) := by
  obtain ⟨m, hm, hp, hbit, hrest⟩ := flipParity_flip l i n hi hn
  refine ⟨m, hm, hp, ?_⟩
  refine ground.map_congr_members _ _ _ (fun j hj => ?_)
  have hjl := ground.ltOfMem hj
  rw [signedImage_getAt l D p n j hjl]
  by_cases hji : j = i
  · rw [if_pos hji, hji]
    have h : ∀ a, a < 2 → ∀ b, b < 2 → a + b = 1 → (a == 1) = !(b == 1) := by
      decide +kernel
    rw [h _ (ground.baseDigit_lt 2 i m (by decide))
      _ (ground.baseDigit_lt 2 i n (by decide)) hbit]
    cases hb : (baseDigit 2 i n == 1) <;> rfl
  · rw [if_neg hji, hrest j hjl hji]

/-- Equal sign-code parity determines one bit when every other
bit agrees, at codes inside the displayed width. -/
theorem flipParity_one_bit (l i n m : Nat) (hi : i < l) (hn : n < 2 ^ l) (hm : m < 2 ^ l)
    (hpar : flipParity l n = flipParity l m)
    (hrest : ∀ j, j < l → j ≠ i → baseDigit 2 j n = baseDigit 2 j m) : n = m := by
  by_cases hsame : baseDigit 2 i n = baseDigit 2 i m
  · apply ground.baseDigit_ext 2 (by decide) l n m hn hm
    intro j hj
    by_cases hji : j = i
    · rw [hji]; exact hsame
    · exact hrest j hj hji
  · obtain ⟨k, hk, hflip, hbit, hkeep⟩ := flipParity_flip l i n hi hn
    have hkm : k = m := by
      apply ground.baseDigit_ext 2 (by decide) l k m hk hm
      intro j hj
      by_cases hji : j = i
      · rw [hji]
        have h : ∀ a, a < 2 → ∀ b, b < 2 → ∀ c, c < 2 → a + b = 1 → a ≠ c → b = c := by
          decide +kernel
        exact h _ (ground.baseDigit_lt 2 i n (by decide)) _ (ground.baseDigit_lt 2 i k (by decide))
          _ (ground.baseDigit_lt 2 i m (by decide)) (by rw [Nat.add_comm]; exact hbit) hsame
      · exact (hkeep j hj hji).trans (hrest j hj hji)
    rw [hkm] at hflip
    have hbad := hpar.trans hflip
    cases hb : flipParity l n <;> rw [hb] at hbad <;> cases hbad

/-- At coordinates distinct up to memberwise swap, signed images
with one sign-code parity identify the permutation and the code.
The coordinates may include one value at the sum's unit. -/
theorem signedImage_even_inj (l : Nat) (D : List BPair)
    (hsep : ∀ i j, i < l → j < l →
      (ground.getAt BPair.unit D i).oneValue (ground.getAt BPair.unit D j)
        ∨ (ground.getAt BPair.unit D i).oneValue (ground.getAt BPair.unit D j).swap → i = j)
    (p q : List Nat) (n m : Nat)
    (hp : 0 < ground.countOf p (places.perms l))
    (hq : 0 < ground.countOf q (places.perms l))
    (hn : n < 2 ^ l) (hm : m < 2 ^ l) (hpar : flipParity l n = flipParity l m)
    (he : poly.oneValue (signedImage l D p n) (signedImage l D q m)) :
    p = q ∧ n = m := by
  have hplaces : p = q := by
    refine ground.getAt_ext 0 p q ((places.perm_member_reads hp).1.trans (places.perm_member_reads hq).1.symm) ?_
    intro i hi
    have hil : i < l := by rw [← (places.perm_member_reads hp).1]; exact hi
    have h := poly.oneValue_getAt i he
    rw [signedImage_getAt l D p n i hil, signedImage_getAt l D q m i hil] at h
    apply hsep _ _ (places.perm_lt l hp i hil) (places.perm_lt l hq i hil)
    cases hn' : (baseDigit 2 i n == 1) <;> cases hm' : (baseDigit 2 i m == 1) <;>
      rw [hn', hm'] at h
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr (ground.swap_congr h)
    · exact Or.inl (ground.swap_congr h)
  refine ⟨hplaces, ?_⟩
  rw [← hplaces] at he
  have hbits : ∀ a, a < 2 → ∀ b, b < 2 → (a == 1) = (b == 1) → a = b := by decide +kernel
  have hunit : ∀ i, i < l → baseDigit 2 i n ≠ baseDigit 2 i m →
      (ground.getAt BPair.unit D (ground.getAt 0 p i)).oneValue BPair.unit := by
    intro i hi hdiff
    have h := poly.oneValue_getAt i he
    rw [signedImage_getAt l D p n i hi, signedImage_getAt l D p m i hi] at h
    cases hn' : (baseDigit 2 i n == 1) <;> cases hm' : (baseDigit 2 i m == 1) <;>
      rw [hn', hm'] at h
    · exact False.elim (hdiff (hbits _ (ground.baseDigit_lt 2 i n (by decide))
        _ (ground.baseDigit_lt 2 i m (by decide)) (hn'.trans hm'.symm)))
    · exact BPair.unitOfSwap h
    · exact BPair.unitOfSwap (BPair.oneValue_symm h)
    · exact False.elim (hdiff (hbits _ (ground.baseDigit_lt 2 i n (by decide))
        _ (ground.baseDigit_lt 2 i m (by decide)) (hn'.trans hm'.symm)))
  apply ground.baseDigit_ext 2 (by decide) l n m hn hm
  intro i hi
  by_cases hsame : baseDigit 2 i n = baseDigit 2 i m
  · exact hsame
  · have hz := hunit i hi hsame
    have hrest : ∀ j, j < l → j ≠ i → baseDigit 2 j n = baseDigit 2 j m := by
      intro j hj hji
      by_cases hs : baseDigit 2 j n = baseDigit 2 j m
      · exact hs
      · have hz' := hunit j hj hs
        have hk := hsep _ _ (places.perm_lt l hp j hj) (places.perm_lt l hp i hi)
          (Or.inl (BPair.oneValue_trans hz' (BPair.oneValue_symm hz)))
        exact False.elim (hji (places.perm_inj l hp j i hj hi hk))
    exact congrArg (baseDigit 2 i) (flipParity_one_bit l i n m hi hn hm hpar hrest)

/-- Exchanging adjacent coordinate places stays in the signed
permutation family and flips its permutation grading. -/
theorem signedImage_adjSwap (l i : Nat) (D : List BPair) (p : List Nat) (n : Nat)
    (hp : 0 < ground.countOf p (places.perms l)) (hi : i + 1 < l) :
    ∃ q, 0 < ground.countOf q (places.perms l) ∧ ∃ m, m < 2 ^ l
      ∧ flipParity l m = flipParity l n ∧ places.parity q = !(places.parity p)
      ∧ signedImage l D q m = ground.adjSwap i (signedImage l D p n) := by
  let q := ground.adjSwap i (List.range l)
  have hq : 0 < ground.countOf q (places.perms l) := by
    rw [places.countOf_adjSwap_perms]
    exact Nat.succ_pos 0
  obtain ⟨m, hm, hpar, hmove⟩ := signedImage_permute l D p q n hq
  refine ⟨places.expo p q, places.expo_member l hp hq, m, hm, hpar, ?_, ?_⟩
  · change places.parity (q.map (ground.getAt 0 p)) = _
    rw [places.parity_comp l q p hq hp, places.parity_adjSwap_range l i hi]
    cases places.parity p <;> rfl
  · refine hmove.trans ?_
    rw [← ground.map_map (ground.getAt 0 q) (ground.getAt BPair.unit (signedImage l D p n)),
      ground.range_map_getAt 0 l q (by rw [ground.length_adjSwap, ground.length_range])]
    change (ground.adjSwap i (List.range l)).map (ground.getAt BPair.unit (signedImage l D p n)) = _
    rw [← ground.adjSwap_map, ground.range_map_getAt BPair.unit l _ (signedImage_length _ _ _ _)]

/-- Flipping one coordinate stays in the signed permutation
family and reverses its sign-code parity. -/
theorem signedImage_flip_set (l i n : Nat) (D : List BPair) (p : List Nat)
    (hi : i < l) (hn : n < 2 ^ l) :
    ∃ m, m < 2 ^ l ∧ flipParity l m = !(flipParity l n)
      ∧ signedImage l D p m = (signedImage l D p n).set i
        (ground.getAt BPair.unit (signedImage l D p n) i).swap := by
  obtain ⟨m, hm, hpar, hmove⟩ := signedImage_flip l i n D p hi hn
  refine ⟨m, hm, hpar, hmove.trans ?_⟩
  refine ground.getAt_ext BPair.unit _ _
    (by rw [ground.length_mapRange, ground.length_set, signedImage_length]) ?_
  intro j hj
  rw [ground.length_mapRange] at hj
  rw [ground.getAt_map_range, if_pos hj]
  by_cases hji : j = i
  · rw [if_pos hji, hji, ground.getAt_set_self BPair.unit _ _ i (by rw [signedImage_length]; exact hi)]
  · rw [if_neg hji, ground.getAt_set_ne BPair.unit _ i j _ hji]

/-- Exchanging two adjacent coordinates and flipping both keeps
the sign-code parity and reverses the permutation grading. -/
theorem signedImage_adjSwap_flip (l i : Nat) (D : List BPair) (p : List Nat) (n : Nat)
    (hp : 0 < ground.countOf p (places.perms l)) (hi : i + 1 < l) :
    ∃ q, 0 < ground.countOf q (places.perms l) ∧ ∃ m, m < 2 ^ l
      ∧ flipParity l m = flipParity l n ∧ places.parity q = !(places.parity p)
      ∧ signedImage l D q m = ((signedImage l D p n).set i
        (ground.getAt BPair.unit (signedImage l D p n) (i + 1)).swap).set (i + 1)
          (ground.getAt BPair.unit (signedImage l D p n) i).swap := by
  obtain ⟨q, hq, a, ha, hpa, hg, hea⟩ := signedImage_adjSwap l i D p n hp hi
  obtain ⟨b, hb, hpb, heb⟩ := signedImage_flip_set l i a D q (Nat.lt_of_succ_lt hi) ha
  obtain ⟨m, hm, hpm, hem⟩ := signedImage_flip_set l (i + 1) b D q hi hb
  refine ⟨q, hq, m, hm, ?_, hg, ?_⟩
  · rw [hpm, hpb, Bool.not_not, hpa]
  · rw [hem, heb, hea]
    have hil : i + 1 < (signedImage l D p n).length := by rw [signedImage_length]; exact hi
    rw [ground.getAt_set_ne BPair.unit _ i (i + 1) _ (Nat.succ_ne_self i),
      ground.getAt_adjSwap_fst BPair.unit i _ hil, ground.getAt_adjSwap_snd BPair.unit i _ hil]
    refine ground.getAt_ext BPair.unit _ _
      (by rw [ground.length_set, ground.length_set, ground.length_adjSwap,
        ground.length_set, ground.length_set]) ?_
    intro j hj
    rw [ground.length_set, ground.length_set, ground.length_adjSwap] at hj
    by_cases hj' : j = i + 1
    · rw [hj', ground.getAt_set_self BPair.unit _ _ (i + 1)
        (by rw [ground.length_set, ground.length_adjSwap]; exact hil),
        ground.getAt_set_self BPair.unit _ _ (i + 1) (by rw [ground.length_set]; exact hil)]
    · rw [ground.getAt_set_ne BPair.unit _ (i + 1) j _ hj',
        ground.getAt_set_ne BPair.unit _ (i + 1) j _ hj']
      by_cases hj'' : j = i
      · rw [hj'', ground.getAt_set_self BPair.unit _ _ i
          (by rw [ground.length_adjSwap]; exact Nat.lt_of_succ_lt hil),
          ground.getAt_set_self BPair.unit _ _ i (Nat.lt_of_succ_lt hil)]
      · rw [ground.getAt_set_ne BPair.unit _ i j _ hj'', ground.getAt_set_ne BPair.unit _ i j _ hj'',
          ground.getAt_adjSwap_ne BPair.unit i _ j hj'' hj']

/-- A leading vacant bit keeps the parity; an occupied leading
bit flips it. -/
theorem flipParity_extend (l n : Nat) (hn : n < 2 ^ l) :
    flipParity (l + 1) n = flipParity l n
      ∧ flipParity (l + 1) (2 ^ l + n) = !(flipParity l n) := by
  have hz := ground.baseDigit_of_lt 2 l n (by decide) hn
  have hsame : flipParity (l + 1) n = flipParity l n := by
    unfold flipParity
    rw [ground.foldlSum, ground.foldlSum, Nat.zero_add, Nat.zero_add,
      ground.range_succ l, ground.famFold_snoc, hz, Nat.add_zero]
  refine ⟨hsame, ?_⟩
  rw [Nat.add_comm (2 ^ l) n,
    flipParity_step (l + 1) l n (Nat.lt_succ_self l) hz, hsame]

/-- Half of the sign codes at a positive width have even parity. -/
theorem evenSigns_length (l : Nat) :
    ((List.range (2 ^ (l + 1))).filter (fun n => !(flipParity (l + 1) n))).length = 2 ^ l := by
  rw [Nat.pow_succ, Nat.mul_succ, Nat.mul_one,
    ground.range_split (2 ^ l) (2 ^ l), ground.filter_append,
    ground.length_append, ground.filter_map, ground.length_map]
  rw [ground.filter_congr_mem _ (fun n => !(flipParity l n)) (List.range (2 ^ l))
    (fun n hn => congrArg Bool.not (flipParity_extend l n (ground.ltOfMem hn)).1)]
  rw [ground.filter_congr_mem (fun n => !(flipParity (l + 1) (2 ^ l + n)))
    (fun n => flipParity l n) (List.range (2 ^ l))
    (fun n hn => by
      rw [(flipParity_extend l n (ground.ltOfMem hn)).2, Bool.not_not])]
  rw [Nat.add_comm, ground.length_filter_split, ground.length_range]

private theorem serWeylGo_seed (coords coroots : List BPair → List BPair)
    (flipsAll : Bool) (l : Nat) (v : List BPair)
    (hc : (coords v).length = l)
    (hr : poly.pnorm (coroots (coords v)) = poly.pnorm v) :
    (poly.pnorm v, false) ∈ serWeylGo coords coroots flipsAll l v := by
  have hp : List.range l ∈ places.perms l := ground.mem_of_countOf_pos _ _ (by
    rw [places.countRangePerms]; exact Nat.succ_pos 0)
  have h := serWeylGo_mem coords coroots flipsAll l v (List.range l) 0 hp
    (Nat.pow_pos (by decide)) (by rw [flipParity_zero]; cases flipsAll <;> rfl)
  have hid : signedImage l (coords v) (List.range l) 0 = coords v := by
    rw [← hc]
    exact signedImage_id _
  rw [hid, hr, places.parity_range, flipParity_zero] at h
  cases flipsAll <;> exact h

private theorem serWeylGo_keys (coords coroots : List BPair → List BPair)
    (flipsAll : Bool) (l : Nat) (v : List BPair) :
    (serWeylGo coords coroots flipsAll l v).map Prod.fst
      = (places.perms l).flatMap (fun p =>
        ((List.range (2 ^ l)).filter (fun n => flipsAll || !(flipParity l n))).map
          (fun n => poly.pnorm (coroots (signedImage l (coords v) p n)))) := by
  unfold serWeylGo
  rw [ground.map_flatMap]
  exact ground.flatMap_congr_all _ _ (fun p => by
    rw [ground.filterMap_ite, ground.map_map]) _

private theorem serWeylGo_distinct (coords coroots : List BPair → List BPair)
    (flipsAll : Bool) (l : Nat) (v : List BPair)
    (hinj : ∀ p ∈ places.perms l, ∀ q ∈ places.perms l,
      ∀ n, n < 2 ^ l → (flipsAll || !(flipParity l n)) = true →
      ∀ m, m < 2 ^ l → (flipsAll || !(flipParity l m)) = true →
      poly.pnorm (coroots (signedImage l (coords v) p n))
        = poly.pnorm (coroots (signedImage l (coords v) q m)) → p = q ∧ n = m) :
    ground.distinctList ((serWeylGo coords coroots flipsAll l v).map Prod.fst) := by
  rw [serWeylGo_keys]
  let codes := (List.range (2 ^ l)).filter (fun n => flipsAll || !(flipParity l n))
  let key := fun p n => poly.pnorm (coroots (signedImage l (coords v) p n))
  have hcode : ∀ n ∈ codes, n < 2 ^ l := fun n hn =>
    ground.ltOfMem (ground.countOf_pos_of_mem (ground.mem_filter_of _ _ n hn).1)
  have hadmit : ∀ n ∈ codes, (flipsAll || !(flipParity l n)) = true :=
    fun n hn => (ground.mem_filter_of _ _ n hn).2
  have hcodes : ground.distinctList codes :=
    ground.distinctList_filter _ _ (ground.distinctList_range _)
  intro y hy
  obtain ⟨p, hp, hy⟩ := ground.mem_flatMap_of _ _ y hy
  obtain ⟨n, hn, hny⟩ := ground.mem_map_of _ _ y hy
  rw [← hny, ground.countOf_flatMap]
  have hinner : ∀ q ∈ places.perms l,
      ground.countOf (key p n) (codes.map (key q)) = if q = p then 1 else 0 := by
    intro q hq
    by_cases hqp : q = p
    · rw [if_pos hqp, hqp, ground.countOf_map_inj (key p) n codes
        (fun m hm he => (hinj p hp p hp m
          (hcode m (ground.mem_of_countOf_pos m codes hm)) (hadmit m (ground.mem_of_countOf_pos m codes hm))
          n (hcode n hn) (hadmit n hn) he).2)]
      exact ground.countOf_distinct_one hcodes hn
    · rw [if_neg hqp]
      exact ground.countOf_map_none (key q) (key p n) codes (fun m hm he =>
        hqp (hinj q hq p hp m (hcode m (ground.mem_of_countOf_pos m codes hm))
          (hadmit m (ground.mem_of_countOf_pos m codes hm)) n (hcode n hn) (hadmit n hn) he).1)
  change ground.famFold Nat.add 0 (fun q => ground.countOf (key p n) (codes.map (key q)))
    (places.perms l) ≤ 1
  rw [ground.famFold_congr_mem Nat.add 0 _ (fun q => if q = p then 1 else 0)
    (places.perms l) hinner,
    ground.famFold_pick (fun _ => 1) p (places.perms l)
      (ground.countOf_distinct_one (places.perms_distinct l) hp)]
  exact Nat.le_refl 1

/-- At distinct positive coordinate values, C's displayed Weyl
family has one member per coroot key. -/
theorem serWeylC_distinct (l : Nat) (hl : 0 < l) (v : List BPair)
    (hpos : ∀ i, i < l → BPair.unit < ground.getAt BPair.unit (coordsC v) i)
    (hsep : ∀ i j, i < l → j < l →
      (ground.getAt BPair.unit (coordsC v) i).oneValue
        (ground.getAt BPair.unit (coordsC v) j) → i = j) :
    ground.distinctList ((serWeylC l v).map Prod.fst) := by
  refine serWeylGo_distinct coordsC corootsC true l v ?_
  intro p hp q hq n hn _ m hm _ he
  apply signedImage_inj l (coordsC v) hpos hsep p q n m
    (ground.countOf_pos_of_mem hp) (ground.countOf_pos_of_mem hq) hn hm
  exact corootsC_inj _ _
    ((signedImage_length _ _ _ _).trans (signedImage_length _ _ _ _).symm)
    (by rw [signedImage_length]; exact hl) he

/-- Every strictly dominant C seed has a displayed Weyl family
with distinct coroot keys. -/
theorem serWeylC_regular (l : Nat) (hl : 0 < l) (v : List BPair)
    (hv : v.length = l)
    (hp : ∀ i, i < l → BPair.unit < ground.getAt BPair.unit v i) :
    ground.distinctList ((serWeylC l v).map Prod.fst) := by
  have hc := coordsC_regular v (fun i hi => hp i (by rw [← hv]; exact hi))
  refine serWeylC_distinct l hl v (fun i hi => hc.1 i (by rw [hv]; exact hi)) ?_
  exact ground.bDesc_inj (coordsC v) l (fun i j hij hj => hc.2 i j hij (by rw [hv]; exact hj))

/-- At distinct positive coordinate values, B's displayed Weyl
family has one member per coroot key. -/
theorem serWeylB_distinct (l : Nat) (hl : 0 < l) (v : List BPair) (hv : v.length = l)
    (hpos : ∀ i, i < l → BPair.unit < ground.getAt BPair.unit (coordsB v) i)
    (hsep : ∀ i j, i < l → j < l →
      (ground.getAt BPair.unit (coordsB v) i).oneValue
        (ground.getAt BPair.unit (coordsB v) j) → i = j) :
    ground.distinctList ((serWeylB l v).map Prod.fst) := by
  have hpar : ∀ i j, i < l → j < l →
      (ground.getAt BPair.unit (coordsB v) i).marginN % 2
        = (ground.getAt BPair.unit (coordsB v) j).marginN % 2 :=
    fun i j hi hj => coordsB_parity v i j (by rw [hv]; exact hi) (by rw [hv]; exact hj)
  refine serWeylGo_distinct coordsB corootsB true l v ?_
  intro p hp q hq n hn _ m hm _ he
  apply signedImage_inj l (coordsB v) hpos hsep p q n m
    (ground.countOf_pos_of_mem hp) (ground.countOf_pos_of_mem hq) hn hm
  refine corootsB_inj _ _
    ((signedImage_length _ _ _ _).trans (signedImage_length _ _ _ _).symm)
    (by rw [signedImage_length]; exact hl) ?_ ?_ he
  · intro i hi
    rw [signedImage_length] at hi
    exact signedImage_even_gaps l (coordsB v) p n (ground.countOf_pos_of_mem hp) hpar i hi
  · intro i hi
    rw [signedImage_length] at hi
    exact signedImage_even_gaps l (coordsB v) q m (ground.countOf_pos_of_mem hq) hpar i hi

/-- Every strictly dominant B seed has a displayed Weyl family
with distinct coroot keys. -/
theorem serWeylB_regular (l : Nat) (hl : 0 < l) (v : List BPair)
    (hv : v.length = l)
    (hp : ∀ i, i < l → BPair.unit < ground.getAt BPair.unit v i) :
    ground.distinctList ((serWeylB l v).map Prod.fst) := by
  have hc := coordsB_regular v (fun i hi => hp i (by rw [← hv]; exact hi))
  refine serWeylB_distinct l hl v hv (fun i hi => hc.1 i (by rw [hv]; exact hi)) ?_
  exact ground.bDesc_inj (coordsB v) l (fun i j hij hj => hc.2 i j hij (by rw [hv]; exact hj))

/-- Every strictly dominant D seed has distinct displayed coroot
keys at the even sign codes, including the final coordinate's
equal-membered read. -/
theorem serWeylD_regular (l : Nat) (hl : 2 ≤ l) (v : List BPair) (hv : v.length = l)
    (hp : ∀ i, i < l → BPair.unit < ground.getAt BPair.unit v i) :
    ground.distinctList ((serWeylD l v).map Prod.fst) := by
  have hv2 : 2 ≤ v.length := by rw [hv]; exact hl
  have hc := coordsD_regular v hv2 (fun i hi => hp i (by rw [← hv]; exact hi))
  have hsep := ground.bDesc_swap_inj (coordsD v) l
    (fun i j hij hj => hc.2 i j hij (by rw [hv]; exact hj))
  have hpar : ∀ i j, i < l → j < l →
      (ground.getAt BPair.unit (coordsD v) i).marginN % 2
        = (ground.getAt BPair.unit (coordsD v) j).marginN % 2 :=
    fun i j hi hj => coordsD_parity v hv2 i j (by rw [hv]; exact hi) (by rw [hv]; exact hj)
  refine serWeylGo_distinct coordsD corootsD false l v ?_
  intro p hp' q hq n hn han m hm ham he
  have hflip : flipParity l n = flipParity l m := by
    cases hn' : flipParity l n <;> cases hm' : flipParity l m
    · rfl
    · rw [hm'] at ham; cases ham
    · rw [hn'] at han; cases han
    · rfl
  apply signedImage_even_inj l (coordsD v) hsep p q n m
    (ground.countOf_pos_of_mem hp') (ground.countOf_pos_of_mem hq) hn hm hflip
  refine corootsD_inj _ _
    ((signedImage_length _ _ _ _).trans (signedImage_length _ _ _ _).symm)
    (by rw [signedImage_length]; exact hl) ?_ ?_ he
  · intro i hi
    rw [signedImage_length] at hi
    exact signedImage_even_gaps l (coordsD v) p n (ground.countOf_pos_of_mem hp') hpar i hi
  · intro i hi
    rw [signedImage_length] at hi
    exact signedImage_even_gaps l (coordsD v) q m (ground.countOf_pos_of_mem hq) hpar i hi

/-- The displayed Weyl family's count is the place count times
the admitted sign count. -/
private theorem serWeylGo_length (coords coroots : List BPair → List BPair)
    (flipsAll : Bool) (l : Nat) (v : List BPair) :
    (serWeylGo coords coroots flipsAll l v).length
      = ground.factorial l * ((List.range (2 ^ l)).filter
        (fun n => flipsAll || !(flipParity l n))).length := by
  unfold serWeylGo
  rw [ground.length_flatMap]
  rw [ground.famFold_congr_all Nat.add 0 _
    (fun _ => ((List.range (2 ^ l)).filter (fun n => flipsAll || !(flipParity l n))).length)
    (fun p => by rw [ground.filterMap_ite, ground.length_map])]
  rw [ground.famFold_const, places.length_perms]

/-- B's displayed list has every sign at every permutation. -/
theorem serWeylB_length (l : Nat) (v : List BPair) :
    (serWeylB l v).length = 2 ^ l * ground.factorial l := by
  rw [serWeylB, serWeylGo_length,
    ground.filter_all _ _ (fun _ _ => Bool.true_or _)]
  rw [ground.length_range, Nat.mul_comm]

/-- C's displayed list has every sign at every permutation. -/
theorem serWeylC_length (l : Nat) (v : List BPair) :
    (serWeylC l v).length = 2 ^ l * ground.factorial l := by
  rw [serWeylC, serWeylGo_length,
    ground.filter_all _ _ (fun _ _ => Bool.true_or _)]
  rw [ground.length_range, Nat.mul_comm]

/-- D's even-sign list is bounded by the full signed list's count. -/
theorem serWeylD_length_le (l : Nat) (v : List BPair) :
    (serWeylD l v).length ≤ 2 ^ l * ground.factorial l := by
  rw [serWeylD, serWeylGo_length, Nat.mul_comm]
  exact Nat.mul_le_mul_right _ (by
    have h := ground.length_filter_le (fun n => false || !(flipParity l n)) (List.range (2 ^ l))
    rw [ground.length_range] at h
    exact h)

/-- D's displayed Weyl family uses exactly the even half of the
sign codes at every positive width. -/
theorem serWeylD_length (l : Nat) (v : List BPair) :
    (serWeylD (l + 1) v).length = 2 ^ l * ground.factorial (l + 1) := by
  rw [serWeylD, serWeylGo_length]
  rw [ground.filter_congr _ (fun n => !(flipParity (l + 1) n))
    (fun n => Bool.false_or _) (List.range (2 ^ (l + 1))), evenSigns_length, Nat.mul_comm]

/-- The distinct key list of B's displayed family is bounded by
the signed-permutation count, at singular seeds as well. -/
theorem serWeylB_keys_length (l : Nat) (v : List BPair) :
    (ground.dedupF ((serWeylB l v).map Prod.fst)).length ≤ 2 ^ l * ground.factorial l := by
  have h := ground.length_dedupF_le ((serWeylB l v).map Prod.fst)
  rw [ground.length_map, serWeylB_length] at h
  exact h

/-- The distinct key list of C's displayed family is bounded by
the signed-permutation count. -/
theorem serWeylC_keys_length (l : Nat) (v : List BPair) :
    (ground.dedupF ((serWeylC l v).map Prod.fst)).length ≤ 2 ^ l * ground.factorial l := by
  have h := ground.length_dedupF_le ((serWeylC l v).map Prod.fst)
  rw [ground.length_map, serWeylC_length] at h
  exact h

/-- The distinct key list of D's displayed family is bounded by
the signed-permutation count. -/
theorem serWeylD_keys_length (l : Nat) (v : List BPair) :
    (ground.dedupF ((serWeylD l v).map Prod.fst)).length ≤ 2 ^ l * ground.factorial l := by
  have h := ground.length_dedupF_le ((serWeylD l v).map Prod.fst)
  rw [ground.length_map] at h
  exact Nat.le_trans h (serWeylD_length_le l v)

/-- The displayed B family contains its canonical seed at even parity. -/
theorem serWeylB_seed (l : Nat) (v : List BPair) (hv : v.length = l) (hl : 0 < l) :
    (poly.pnorm v, false) ∈ serWeylB l v :=
  serWeylGo_seed coordsB corootsB true l v ((coordsB_length v).trans hv)
    (corootsB_coordsB_norm v (by rw [hv]; exact hl))

/-- The displayed C family contains its canonical seed at even parity. -/
theorem serWeylC_seed (l : Nat) (v : List BPair) (hv : v.length = l) (hl : 0 < l) :
    (poly.pnorm v, false) ∈ serWeylC l v :=
  serWeylGo_seed coordsC corootsC true l v ((coordsC_length v).trans hv)
    (corootsC_coordsC_norm v (by rw [hv]; exact hl))

/-- The displayed D family contains its canonical seed at even parity. -/
theorem serWeylD_seed (l : Nat) (v : List BPair) (hv : v.length = l) (hl : 2 ≤ l) :
    (poly.pnorm v, false) ∈ serWeylD l v :=
  serWeylGo_seed coordsD corootsD false l v
    ((coordsD_length v (by rw [hv]; exact hl)).trans hv)
    (corootsD_coordsD_norm v (by rw [hv]; exact hl))

/-- Each displayed member is a canonical coroot list at the
coordinate width. -/
private theorem serWeylGo_shape (coords coroots : List BPair → List BPair)
    (flipsAll : Bool) (l : Nat) (v : List BPair)
    (hcor : ∀ D, D.length = l → (coroots D).length = l) :
    ∀ p ∈ serWeylGo coords coroots flipsAll l v,
      p.1.length = l ∧ poly.pnorm p.1 = p.1 := by
  intro p hp
  obtain ⟨q, _, n, _, _, he⟩ := serWeylGo_of_mem coords coroots flipsAll l v p hp
  rw [he]
  exact ⟨(poly.pnorm_length _).trans (hcor _ (signedImage_length _ _ _ _)), poly.pnorm_pnorm _⟩

/-- B's Weyl family has the table's coroot shape at every seed. -/
theorem serWeylB_shape (l : Nat) (hl : 0 < l) (v : List BPair) :
    wShapeRead (tableB l) (serWeylB l v) :=
  serWeylGo_shape coordsB corootsB true l v (fun D hD =>
    (corootsB_length D (by rw [hD]; exact hl)).trans hD)

/-- C's Weyl family has the table's coroot shape at every seed. -/
theorem serWeylC_shape (l : Nat) (hl : 0 < l) (v : List BPair) :
    wShapeRead (tableC l) (serWeylC l v) :=
  serWeylGo_shape coordsC corootsC true l v (fun D hD =>
    (corootsC_length D (by rw [hD]; exact hl)).trans hD)

/-- D's Weyl family has the table's coroot shape at every seed. -/
theorem serWeylD_shape (l : Nat) (hl : 0 < l) (v : List BPair) :
    wShapeRead (tableD l) (serWeylD l v) :=
  serWeylGo_shape coordsD corootsD false l v (fun D hD =>
    (corootsD_length D (by rw [hD]; exact hl)).trans hD)

/-- Each permutation and sign code contributes its graded C
coordinate image to the displayed family. -/
theorem serWeylC_mem (l : Nat) (v : List BPair) (p : List Nat) (n : Nat)
    (hp : 0 < ground.countOf p (places.perms l)) (hn : n < 2 ^ l) :
    (poly.pnorm (corootsC (signedImage l (coordsC v) p n)), places.parity p != flipParity l n)
      ∈ serWeylC l v :=
  serWeylGo_mem coordsC corootsC true l v p n (ground.mem_of_countOf_pos p _ hp) hn (Bool.true_or _)

/-- A displayed C member reads at one permutation and sign code. -/
theorem serWeylC_of_mem (l : Nat) (v : List BPair) (w : List BPair × Bool)
    (hw : w ∈ serWeylC l v) :
    ∃ p, p ∈ places.perms l ∧ ∃ n, n < 2 ^ l
      ∧ w = (poly.pnorm (corootsC (signedImage l (coordsC v) p n)), places.parity p != flipParity l n) := by
  obtain ⟨p, hp, n, hn, _, he⟩ := serWeylGo_of_mem coordsC corootsC true l v w hw
  exact ⟨p, hp, n, hn, he⟩

/-- Each permutation and sign code contributes its graded B
coordinate image to the displayed family. -/
theorem serWeylB_mem (l : Nat) (v : List BPair) (p : List Nat) (n : Nat)
    (hp : 0 < ground.countOf p (places.perms l)) (hn : n < 2 ^ l) :
    (poly.pnorm (corootsB (signedImage l (coordsB v) p n)), places.parity p != flipParity l n)
      ∈ serWeylB l v :=
  serWeylGo_mem coordsB corootsB true l v p n (ground.mem_of_countOf_pos p _ hp) hn (Bool.true_or _)

/-- A displayed B member reads at one permutation and sign code. -/
theorem serWeylB_of_mem (l : Nat) (v : List BPair) (w : List BPair × Bool)
    (hw : w ∈ serWeylB l v) :
    ∃ p, p ∈ places.perms l ∧ ∃ n, n < 2 ^ l
      ∧ w = (poly.pnorm (corootsB (signedImage l (coordsB v) p n)), places.parity p != flipParity l n) := by
  obtain ⟨p, hp, n, hn, _, he⟩ := serWeylGo_of_mem coordsB corootsB true l v w hw
  exact ⟨p, hp, n, hn, he⟩

/-- Each permutation and even sign code contributes its graded D
coordinate image to the displayed family. -/
theorem serWeylD_mem (l : Nat) (v : List BPair) (p : List Nat) (n : Nat)
    (hp : 0 < ground.countOf p (places.perms l)) (hn : n < 2 ^ l) (he : flipParity l n = false) :
    (poly.pnorm (corootsD (signedImage l (coordsD v) p n)), places.parity p) ∈ serWeylD l v :=
  serWeylGo_mem coordsD corootsD false l v p n (ground.mem_of_countOf_pos p _ hp) hn (by rw [he]; rfl)

/-- A displayed D member reads at one permutation and even sign
code, its grading the permutation's. -/
theorem serWeylD_of_mem (l : Nat) (v : List BPair) (w : List BPair × Bool)
    (hw : w ∈ serWeylD l v) :
    ∃ p, p ∈ places.perms l ∧ ∃ n, n < 2 ^ l ∧ flipParity l n = false
      ∧ w = (poly.pnorm (corootsD (signedImage l (coordsD v) p n)), places.parity p) := by
  obtain ⟨p, hp, n, hn, ha, he⟩ := serWeylGo_of_mem coordsD corootsD false l v w hw
  refine ⟨p, hp, n, hn, ?_, he⟩
  cases h : flipParity l n
  · rfl
  · rw [h] at ha; cases ha

private theorem cartC_pair_lt (l i j : Nat) (hij : i < j) :
    ¬ (cartC l i j * cartC l j i).oneValue (BPair.ofNat 4) := by
  by_cases h : j = i + 1
  · rw [h, cartCup]
    by_cases he : i + 2 = l
    · rw [cartCdn2 l i he]
      decide +kernel
    · rw [cartCdn1 l i he]
      decide +kernel
  · rw [cartCoff l i j (Nat.ne_of_gt hij) (Nat.ne_of_gt (Nat.lt_succ_of_lt hij)) h]
    intro he
    exact (by decide +kernel : ¬ BPair.unit.oneValue (BPair.ofNat 4))
      (BPair.oneValue_trans (BPair.oneValue_symm (BPair.unit_mul _)) he)

/-- Two distinct C simple keys have Cartan cross product off
four, the two-key minor's unequal-membered read. -/
theorem cartC_pair (l i j : Nat) (hij : i ≠ j) :
    ¬ (cartC l i j * cartC l j i).oneValue (BPair.ofNat 4) := by
  cases Nat.lt_or_ge i j with
  | inl h => exact cartC_pair_lt l i j h
  | inr h =>
    rw [BPair.mul_comm]
    exact cartC_pair_lt l j i (Nat.lt_of_le_of_ne h (fun he => hij he.symm))

/-- The B and C Cartan entries are transposes. -/
theorem cartB_C_transpose (l i j : Nat) : cartB l i j = cartC l j i := by
  by_cases hji : j = i
  · rw [hji, cartBd, cartCd]
  · by_cases hnext : j = i + 1
    · rw [hnext]
      by_cases hedge : i + 2 = l
      · rw [cartBup2 l i hedge, cartCdn2 l i hedge]
      · rw [cartBup1 l i hedge, cartCdn1 l i hedge]
    · by_cases hprev : j + 1 = i
      · rw [← hprev, cartBdn, cartCup]
      · rw [cartBoff l i j hji hnext hprev,
          cartCoff l j i (fun h => hji h.symm) (fun h => hnext h.symm) (fun h => hprev h.symm)]

/-- B's distinct simple keys have Cartan cross product off four. -/
theorem cartB_pair (l i j : Nat) (hij : i ≠ j) :
    ¬ (cartB l i j * cartB l j i).oneValue (BPair.ofNat 4) := by
  rw [cartB_C_transpose, cartB_C_transpose, BPair.mul_comm]
  exact cartC_pair l i j hij

/-- D's distinct simple keys have Cartan cross product off four. -/
theorem cartD_pair (l i j : Nat) (hij : i ≠ j) :
    ¬ (cartD l i j * cartD l j i).oneValue (BPair.ofNat 4) := by
  have hoff : ∀ a b, a ≠ b → cartD l a b = BPair.unit ∨ cartD l a b = (BPair.ofNat 1).swap := by
    intro a b hab
    unfold cartD
    rw [ground.neBeqOf (fun h => hab h.symm)]
    cases h1 : (a + 1 == l) <;> cases h2 : (b + 1 == l) <;>
      cases h3 : (a + 3 == l) <;> cases h4 : (b + 3 == l) <;>
      cases h5 : (b + 1 == a || b == a + 1) <;> first | exact Or.inl rfl | exact Or.inr rfl
  cases hoff i j hij with
  | inl h =>
    rw [h]
    intro he
    exact (by decide +kernel : ¬ BPair.unit.oneValue (BPair.ofNat 4))
      (BPair.oneValue_trans (BPair.oneValue_symm (BPair.unit_mul _)) he)
  | inr h =>
    rw [h]
    cases hoff j i (fun he => hij he.symm) with
    | inl h' => rw [h']; decide +kernel
    | inr h' => rw [h']; decide +kernel

/-- The B and C coroot displays differ by doubling each entry
before the final one, on the even-gap domain of the half read. -/
theorem corootsB_C_scale : ∀ (D : List BPair),
    (∀ i, i + 1 < D.length →
      (ground.getAt BPair.unit D i + (ground.getAt BPair.unit D (i + 1)).swap).marginN % 2 = 0) →
    ∀ j, j < D.length →
      (ground.getAt BPair.unit (corootsC D) j).oneValue
        (BPair.ofNat (if j + 1 = D.length then 1 else 2)
          * ground.getAt BPair.unit (corootsB D) j)
  | [], _, j, hj => absurd hj (Nat.not_lt_zero j)
  | [a], _, 0, _ => BPair.oneValue_symm (BPair.ofNat_one_mul a)
  | [_], _, j + 1, hj => absurd (Nat.lt_of_succ_lt_succ hj) (Nat.not_lt_zero j)
  | a :: b :: D, heven, 0, _ => by
    rw [corootsC_cons, corootsB_cons]
    change (a + b.swap).oneValue
      (BPair.ofNat (if 1 = D.length + 2 then 1 else 2) * halfB (a + b.swap))
    rw [if_neg (Nat.ne_of_lt (Nat.succ_lt_succ (Nat.succ_pos D.length)))]
    exact BPair.oneValue_trans
      (BPair.oneValue_symm (halfB_read (a + b.swap) (heven 0 (Nat.succ_lt_succ (Nat.succ_pos _)))))
      (BPair.oneValue_symm (BPair.ofNat_two_mul _))
  | a :: b :: D, heven, j + 1, hj => by
    rw [corootsC_cons, corootsB_cons]
    change (ground.getAt BPair.unit (corootsC (b :: D)) j).oneValue
      (BPair.ofNat (if j + 1 + 1 = (b :: D).length + 1 then 1 else 2)
        * ground.getAt BPair.unit (corootsB (b :: D)) j)
    have ih := corootsB_C_scale (b :: D)
      (fun i hi => heven (i + 1) (Nat.succ_lt_succ hi)) j (Nat.lt_of_succ_lt_succ hj)
    by_cases h : j + 1 = (b :: D).length
    · rw [if_pos (congrArg Nat.succ h)]
      rw [if_pos h] at ih
      exact ih
    · rw [if_neg (fun he => h (Nat.succ.inj he))]
      rw [if_neg h] at ih
      exact ih

/-- The diagonal change from B's coroots to C's intertwines their
Cartan rows, with multiplier one only at the final key. -/
theorem cartB_C_scale (l i j : Nat) (hi : i < l) (hj : j < l) :
    (BPair.ofNat (if j + 1 = l then 1 else 2) * cartB l i j).oneValue
      (BPair.ofNat (if i + 1 = l then 1 else 2) * cartC l i j) := by
  by_cases hji : j = i
  · rw [hji, cartBd, cartCd]
    exact BPair.oneValue_refl _
  · by_cases hnext : j = i + 1
    · have hnot : ¬ i + 1 = l := Nat.ne_of_lt (by rw [← hnext]; exact hj)
      rw [hnext, cartCup, if_neg hnot]
      by_cases hedge : i + 2 = l
      · rw [cartBup2 l i hedge, if_pos hedge]
        decide +kernel
      · rw [cartBup1 l i hedge, if_neg hedge]
        exact BPair.oneValue_refl _
    · by_cases hprev : j + 1 = i
      · rw [← hprev, cartBdn, if_neg (Nat.ne_of_lt (by rw [hprev]; exact hi))]
        by_cases hedge : j + 2 = l
        · rw [cartCdn2 l j hedge, if_pos hedge]
          decide +kernel
        · rw [cartCdn1 l j hedge, if_neg hedge]
          exact BPair.oneValue_refl _
      · rw [cartBoff l i j hji hnext hprev, cartCoff l i j hji hprev hnext]
        exact BPair.oneValue_trans (BPair.mul_unit _) (BPair.oneValue_symm (BPair.mul_unit _))

private theorem corootsSuffix_congr (f : BPair → BPair)
    (hf : ∀ a b, a.oneValue b → (f a).oneValue (f b)) :
    ∀ D E : List BPair, D.length = E.length → poly.oneValue D E →
      poly.oneValue
        (List.zipWith (fun a b => f (a + b.swap)) D (D.drop 1) ++ [ground.getAt BPair.unit D (D.length - 1)])
        (List.zipWith (fun a b => f (a + b.swap)) E (E.drop 1) ++ [ground.getAt BPair.unit E (E.length - 1)])
  | [], [], _, _ => poly.oneValue_refl _
  | [], _ :: _, h, _ => Nat.noConfusion h
  | _ :: _, [], h, _ => Nat.noConfusion h
  | a :: D, b :: E, hw, h => by
    cases D with
    | nil =>
      cases E with
      | nil => exact ⟨h.1, trivial⟩
      | cons _ _ => exact Nat.noConfusion (Nat.succ.inj hw)
    | cons c D =>
      cases E with
      | nil => exact Nat.noConfusion (Nat.succ.inj hw)
      | cons d E => exact ⟨hf _ _ (BPair.add_congr h.1 (ground.swap_congr h.2.1)),
          corootsSuffix_congr f hf (c :: D) (d :: E) (Nat.succ.inj hw) h.2⟩

/-- B's coroot display reads one value across coordinate
representatives, including its signed half gaps. -/
theorem corootsB_congr (D E : List BPair) (hw : D.length = E.length) (h : poly.oneValue D E) :
    poly.oneValue (corootsB D) (corootsB E) :=
  corootsSuffix_congr halfB (fun _ _ h => BPair.oneValue_of_eq (halfB_congr h)) D E hw h

/-- C's coroot display reads one value across coordinate
representatives. -/
theorem corootsC_congr (D E : List BPair) (hw : D.length = E.length) (h : poly.oneValue D E) :
    poly.oneValue (corootsC D) (corootsC E) :=
  corootsSuffix_congr (fun x => x) (fun _ _ h => h) D E hw h

/-- D's coroot display reads one value across coordinate
representatives, at the half gaps and the fork's half sum. -/
theorem corootsD_congr : ∀ D E : List BPair, D.length = E.length → poly.oneValue D E →
    poly.oneValue (corootsD D) (corootsD E)
  | [], [], _, _ => poly.oneValue_refl _
  | [], _ :: _, h, _ => Nat.noConfusion h
  | _ :: _, [], h, _ => Nat.noConfusion h
  | a :: D, b :: E, hw, h => by
    cases D with
    | nil =>
      cases E with
      | nil =>
        exact ⟨BPair.oneValue_of_eq (halfB_congr (BPair.add_congr h.1 h.1)), trivial⟩
      | cons _ _ => exact Nat.noConfusion (Nat.succ.inj hw)
    | cons c D =>
      cases E with
      | nil => exact Nat.noConfusion (Nat.succ.inj hw)
      | cons d E =>
        cases D with
        | nil =>
          cases E with
          | nil => exact ⟨BPair.oneValue_of_eq (halfB_congr (BPair.add_congr h.1 (ground.swap_congr h.2.1))),
              BPair.oneValue_of_eq (halfB_congr (BPair.add_congr h.1 h.2.1)), trivial⟩
          | cons _ _ => exact Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hw))
        | cons e D =>
          cases E with
          | nil => exact Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hw))
          | cons f E =>
            rw [corootsD_cons, corootsD_cons]
            exact ⟨BPair.oneValue_of_eq (halfB_congr (BPair.add_congr h.1 (ground.swap_congr h.2.1))),
              corootsD_congr (c :: e :: D) (d :: f :: E) (Nat.succ.inj hw) h.2⟩

/-- The magnitudes of a signed coordinate image are the source
magnitudes read at its permutation. -/
theorem signedImage_margins (l : Nat) (D : List BPair) (p : List Nat) (n : Nat)
    (hp : 0 < ground.countOf p (places.perms l)) :
    (signedImage l D p n).map BPair.marginN
      = p.map (fun j => (ground.getAt BPair.unit D j).marginN) := by
  have hpl := (places.perm_member_reads hp).1
  refine ground.getAt_ext 0 _ _ (by rw [ground.length_map, signedImage_length, ground.length_map, hpl]) ?_
  intro i hi
  rw [ground.length_map, signedImage_length] at hi
  rw [ground.getAt_map BPair.unit 0 BPair.marginN _ i (by rw [signedImage_length]; exact hi),
    signedImage_margin l D p n i hi, ground.getAt_map 0 0 _ p i (by rw [hpl]; exact hi)]

/-- Signed permutations preserve every coordinate magnitude's
count, including the sum's unit. -/
theorem signedImage_margin_counts (l : Nat) (D : List BPair) (hD : D.length = l)
    (p : List Nat) (n : Nat) (hp : 0 < ground.countOf p (places.perms l)) (a : Nat) :
    ground.countOf a ((signedImage l D p n).map BPair.marginN) = ground.countOf a (D.map BPair.marginN) := by
  rw [signedImage_margins l D p n hp, ground.countOf_map_famFold]
  have h := ground.famFold_relist Nat.add 0 Nat.add_comm Nat.add_assoc
    (fun j => if a = (ground.getAt BPair.unit D j).marginN then 1 else 0)
    p (List.range l) (places.perm_counts_range l hp)
  rw [h, ← ground.countOf_map_famFold]
  have hm := ground.map_map (ground.getAt BPair.unit D) BPair.marginN (List.range l)
  rw [ground.range_map_getAt BPair.unit l D hD] at hm
  rw [← hm]

/-- Weak order of coordinate margins reads as weak order of
the mapped natural list at its own width. -/
private theorem margins_weak_order (U : List BPair) (l : Nat) (hU : U.length = l)
    (h : ∀ i, i + 1 < l → (ground.getAt BPair.unit U (i + 1)).marginN ≤ (ground.getAt BPair.unit U i).marginN) :
    ∀ i, i + 1 < (U.map BPair.marginN).length →
      ground.getAt 0 (U.map BPair.marginN) (i + 1) ≤ ground.getAt 0 (U.map BPair.marginN) i := by
  intro i hi
  rw [ground.length_map] at hi
  rw [ground.getAt_map BPair.unit 0 BPair.marginN U (i + 1) hi,
    ground.getAt_map BPair.unit 0 BPair.marginN U i (Nat.lt_of_succ_lt hi)]
  exact h i (by rw [← hU]; exact hi)

/-- Two coordinate displays in one signed orbit, each weakly
decreasing in magnitude, have the same magnitude list. -/
theorem signedImage_weak_margins (l : Nat) (D E : List BPair) (hD : D.length = l) (hE : E.length = l)
    (hd : ∀ i, i + 1 < l → (ground.getAt BPair.unit D (i + 1)).marginN ≤ (ground.getAt BPair.unit D i).marginN)
    (he : ∀ i, i + 1 < l → (ground.getAt BPair.unit E (i + 1)).marginN ≤ (ground.getAt BPair.unit E i).marginN)
    (p : List Nat) (n : Nat) (hp : 0 < ground.countOf p (places.perms l))
    (himage : poly.oneValue E (signedImage l D p n)) : E.map BPair.marginN = D.map BPair.marginN := by
  have hmap : E.map BPair.marginN = (signedImage l D p n).map BPair.marginN := by
    refine ground.getAt_ext 0 _ _ (by rw [ground.length_map, ground.length_map, hE, signedImage_length]) ?_
    intro i hi
    rw [ground.length_map] at hi
    rw [ground.getAt_map BPair.unit 0 BPair.marginN E i hi,
      ground.getAt_map BPair.unit 0 BPair.marginN _ i (by rw [signedImage_length, ← hE]; exact hi)]
    exact BPair.marginN_congr (poly.oneValue_getAt i himage)
  apply ground.descLeUnique _ _ (by rw [ground.length_map, ground.length_map, hE, hD])
    (margins_weak_order E l hE he) (margins_weak_order D l hD hd)
  intro a
  rw [hmap]
  exact signedImage_margin_counts l D hD p n hp a

/-- Two coordinate displays in one signed orbit, each strictly
decreasing in magnitude, have the same magnitude list. -/
theorem signedImage_ordered_margins (l : Nat) (D E : List BPair) (hD : D.length = l) (hE : E.length = l)
    (hd : ∀ i, i + 1 < l → (ground.getAt BPair.unit D (i + 1)).marginN < (ground.getAt BPair.unit D i).marginN)
    (he : ∀ i, i + 1 < l → (ground.getAt BPair.unit E (i + 1)).marginN < (ground.getAt BPair.unit E i).marginN)
    (p : List Nat) (n : Nat) (hp : 0 < ground.countOf p (places.perms l))
    (himage : poly.oneValue E (signedImage l D p n)) : E.map BPair.marginN = D.map BPair.marginN :=
  signedImage_weak_margins l D E hD hE (fun i hi => Nat.le_of_lt (hd i hi))
    (fun i hi => Nat.le_of_lt (he i hi)) p n hp himage

/-- Upper-side coordinate displays weakly decreasing in
magnitude identify one member of a signed orbit. -/
theorem signedImage_nonnegative_unique (l : Nat) (D E : List BPair) (hD : D.length = l) (hE : E.length = l)
    (hDp : ∀ i, i < l → BPair.unit ≤ ground.getAt BPair.unit D i)
    (hEp : ∀ i, i < l → BPair.unit ≤ ground.getAt BPair.unit E i)
    (hd : ∀ i, i + 1 < l → (ground.getAt BPair.unit D (i + 1)).marginN ≤ (ground.getAt BPair.unit D i).marginN)
    (he : ∀ i, i + 1 < l → (ground.getAt BPair.unit E (i + 1)).marginN ≤ (ground.getAt BPair.unit E i).marginN)
    (p : List Nat) (n : Nat) (hp : 0 < ground.countOf p (places.perms l))
    (himage : poly.oneValue E (signedImage l D p n)) : poly.oneValue E D := by
  have hm := signedImage_weak_margins l D E hD hE hd he p n hp himage
  refine poly.oneValue_of_entries E D (hE.trans hD.symm) (fun i hi => ?_)
  have hil : i < l := by rw [← hE]; exact hi
  apply BPair.oneValue_of_marginN (hEp i hil) (hDp i hil)
  have h := congrArg (fun U => ground.getAt 0 U i) hm
  rw [ground.getAt_map BPair.unit 0 BPair.marginN E i hi,
    ground.getAt_map BPair.unit 0 BPair.marginN D i (by rw [hD]; exact hil)] at h
  exact h

/-- Upper-side coordinate displays strictly decreasing in
magnitude identify one member of a signed orbit. -/
theorem signedImage_positive_unique (l : Nat) (D E : List BPair) (hD : D.length = l) (hE : E.length = l)
    (hDp : ∀ i, i < l → BPair.unit ≤ ground.getAt BPair.unit D i)
    (hEp : ∀ i, i < l → BPair.unit ≤ ground.getAt BPair.unit E i)
    (hd : ∀ i, i + 1 < l → (ground.getAt BPair.unit D (i + 1)).marginN < (ground.getAt BPair.unit D i).marginN)
    (he : ∀ i, i + 1 < l → (ground.getAt BPair.unit E (i + 1)).marginN < (ground.getAt BPair.unit E i).marginN)
    (p : List Nat) (n : Nat) (hp : 0 < ground.countOf p (places.perms l))
    (himage : poly.oneValue E (signedImage l D p n)) : poly.oneValue E D :=
  signedImage_nonnegative_unique l D E hD hE hDp hEp
    (fun i hi => Nat.le_of_lt (hd i hi)) (fun i hi => Nat.le_of_lt (he i hi)) p n hp himage

/-- The coordinate product of a signed image reads the original
product on the sign code's parity side. -/
theorem signedImage_product (l : Nat) (D : List BPair) (hD : D.length = l)
    (p : List Nat) (n : Nat) (hp : 0 < ground.countOf p (places.perms l)) :
    ground.famFold BPair.mul (BPair.ofNat 1) (fun x => x) (signedImage l D p n)
      = ground.signedAt (flipParity l n) (ground.famFold BPair.mul (BPair.ofNat 1) (fun x => x) D) := by
  have hsign : ∀ (keys : List Nat) (f : Nat → BPair),
      ground.famFold BPair.mul (BPair.ofNat 1)
        (fun i => ground.signedAt (baseDigit 2 i n == 1) (f i)) keys
      = ground.signedAt (ground.famFold Nat.add 0 (fun i => baseDigit 2 i n) keys % 2 == 1)
        (ground.famFold BPair.mul (BPair.ofNat 1) f keys) := by
    intro keys
    induction keys with
    | nil => intro f; rfl
    | cons i keys ih =>
      intro f
      change ground.signedAt (baseDigit 2 i n == 1) (f i) *
        ground.famFold BPair.mul (BPair.ofNat 1) _ keys = _
      rw [ih]
      change _ = ground.signedAt ((baseDigit 2 i n + ground.famFold Nat.add 0 _ keys) % 2 == 1)
        (f i * ground.famFold BPair.mul (BPair.ofNat 1) f keys)
      rw [parityMod_add, ground.modOfLt _ 2 (ground.baseDigit_lt 2 i n (by decide +kernel))]
      cases hi : (baseDigit 2 i n == 1) <;>
        cases ht : (ground.famFold Nat.add 0 (fun j => baseDigit 2 j n) keys % 2 == 1)
      · rfl
      · exact BPair.mul_swap _ _
      · exact BPair.swap_mul _ _
      · exact BPair.swap_mul_swap _ _
  rw [signedImage, ground.famFold_map]
  change ground.famFold BPair.mul (BPair.ofNat 1)
    (fun i => ground.signedAt (baseDigit 2 i n == 1) (ground.getAt BPair.unit D (ground.getAt 0 p i)))
    (List.range l) = _
  rw [hsign]
  have hprod : ground.famFold BPair.mul (BPair.ofNat 1)
      (fun i => ground.getAt BPair.unit D (ground.getAt 0 p i)) (List.range l)
      = ground.famFold BPair.mul (BPair.ofNat 1) (fun x => x) D := by
    rw [← ground.famFold_map BPair.mul (BPair.ofNat 1) (ground.getAt BPair.unit D) (ground.getAt 0 p),
      ground.range_map_getAt 0 l p (places.perm_member_reads hp).1]
    rw [ground.famFold_relist BPair.mul (BPair.ofNat 1) BPair.mul_comm BPair.mul_assoc
      (ground.getAt BPair.unit D) p (List.range l) (places.perm_counts_range l hp)]
    exact ground.famFold_getAt BPair.mul (BPair.ofNat 1) (fun x => x) BPair.unit D l hD
  rw [hprod]
  unfold flipParity
  rw [ground.foldlSum, Nat.zero_add]

/-- In the even-sign orbit, weakly ordered magnitudes and upper
coordinates before the last identify the display, including
repeated magnitudes and coordinates at the sum's unit. -/
theorem signedImage_even_weak_unique (k : Nat) (D E : List BPair)
    (hD : D.length = k + 1) (hE : E.length = k + 1)
    (hDp : ∀ i, i < k → BPair.unit ≤ ground.getAt BPair.unit D i)
    (hEp : ∀ i, i < k → BPair.unit ≤ ground.getAt BPair.unit E i)
    (hd : ∀ i, i + 1 < k + 1 → (ground.getAt BPair.unit D (i + 1)).marginN ≤ (ground.getAt BPair.unit D i).marginN)
    (he : ∀ i, i + 1 < k + 1 → (ground.getAt BPair.unit E (i + 1)).marginN ≤ (ground.getAt BPair.unit E i).marginN)
    (p : List Nat) (n : Nat) (hp : 0 < ground.countOf p (places.perms (k + 1)))
    (hpar : flipParity (k + 1) n = false)
    (himage : poly.oneValue E (signedImage (k + 1) D p n)) : poly.oneValue E D := by
  have hm := signedImage_weak_margins (k + 1) D E hD hE hd he p n hp himage
  have hmag : ∀ i, i < k + 1 →
      (ground.getAt BPair.unit E i).marginN = (ground.getAt BPair.unit D i).marginN := by
    intro i hi
    have h := congrArg (fun U => ground.getAt 0 U i) hm
    rw [ground.getAt_map BPair.unit 0 BPair.marginN E i (by rw [hE]; exact hi),
      ground.getAt_map BPair.unit 0 BPair.marginN D i (by rw [hD]; exact hi)] at h
    exact h
  have hfirst : ∀ i, i < k → (ground.getAt BPair.unit E i).oneValue (ground.getAt BPair.unit D i) :=
    fun i hi => BPair.oneValue_of_marginN (hEp i hi) (hDp i hi) (hmag i (Nat.lt_succ_of_lt hi))
  have hlast : (ground.getAt BPair.unit E k).oneValue (ground.getAt BPair.unit D k) := by
    cases Nat.eq_zero_or_pos (ground.getAt BPair.unit D k).marginN with
    | inl hz =>
      have hzero : ∀ x : BPair, x.marginN = 0 → x.oneValue BPair.unit := by
        intro x hx
        by_cases hs : x < BPair.unit
        · have hp := BPair.marginN_pos (ground.ltB_swap hs)
          rw [BPair.marginN_swap, hx] at hp
          exact False.elim (Nat.lt_irrefl 0 hp)
        · have h := BPair.ofNat_marginN (ground.leB_of_not_lt hs)
          rw [hx] at h
          exact h
      exact BPair.oneValue_trans (hzero _ ((hmag k (Nat.lt_succ_self k)).trans hz))
        (BPair.oneValue_symm (hzero _ hz))
    | inr hz =>
      have hdesc := margins_weak_order D (k + 1) hD hd
      have hpos : ∀ i, i < k → BPair.unit < ground.getAt BPair.unit D i := by
        intro i hi
        have hle := ground.descChain _ (ground.sortedAll _ hdesc) i (k - i)
        rw [ground.natAddSubCancel (Nat.le_of_lt hi)] at hle
        rw [ground.getAt_map BPair.unit 0 BPair.marginN D k (by rw [hD]; exact Nat.lt_succ_self k),
          ground.getAt_map BPair.unit 0 BPair.marginN D i (by rw [hD]; exact Nat.lt_succ_of_lt hi)] at hle
        exact BPair.lt_congr (BPair.oneValue_refl _) (BPair.oneValue_symm (BPair.ofNat_marginN (hDp i hi)))
          (ground.unitLtNat (Nat.lt_of_lt_of_le hz hle))
      let pref := ground.famFold BPair.mul (BPair.ofNat 1) (ground.getAt BPair.unit D) (List.range k)
      have hpref : BPair.unit < pref := by
        have hprod : ∀ keys : List Nat, (∀ i ∈ keys, BPair.unit < ground.getAt BPair.unit D i) →
            BPair.unit < ground.famFold BPair.mul (BPair.ofNat 1) (ground.getAt BPair.unit D) keys := by
          intro keys
          induction keys with
          | nil => intro _; exact ground.unitLtNat (Nat.succ_pos 0)
          | cons i keys ih =>
            intro h
            exact ground.unitLtMul (h i (List.Mem.head _)) (ih (fun j hj => h j (List.Mem.tail i hj)))
        exact hprod _ (fun i hi => hpos i (ground.ltOfMemRange hi))
      have hprod : (ground.famFold BPair.mul (BPair.ofNat 1) (fun x => x) E).oneValue
          (ground.famFold BPair.mul (BPair.ofNat 1) (fun x => x) D) := by
        have h := ground.famFold_congr_members_ov BPair.oneValue BPair.mul (BPair.ofNat 1)
          BPair.oneValue_refl (fun h1 h2 => BPair.mul_congr h1 h2)
          (ground.getAt BPair.unit E) (ground.getAt BPair.unit (signedImage (k + 1) D p n))
          (List.range (k + 1)) (fun i _ => poly.oneValue_getAt i himage)
        rw [ground.famFold_getAt _ _ (fun x => x) BPair.unit E _ hE,
          ground.famFold_getAt _ _ (fun x => x) BPair.unit _ _ (signedImage_length _ _ _ _),
          signedImage_product (k + 1) D hD p n hp, hpar] at h
        exact h
      have hsplit (U : List BPair) (hU : U.length = k + 1) :
          (ground.famFold BPair.mul (BPair.ofNat 1) (fun x => x) U).oneValue
            (ground.famFold BPair.mul (BPair.ofNat 1) (ground.getAt BPair.unit U) (List.range k)
              * ground.getAt BPair.unit U k) := by
        rw [← ground.famFold_getAt _ _ (fun x => x) BPair.unit U _ hU, ground.range_succ]
        exact BPair.oneValue_trans (ground.famFold_append_ov ground.bpairMulLaws _ _ _)
          (BPair.mul_congr (BPair.oneValue_refl _) (BPair.mul_ofNat_one _))
      have hpre : (ground.famFold BPair.mul (BPair.ofNat 1) (ground.getAt BPair.unit E) (List.range k)).oneValue pref :=
        ground.famFold_congr_members_ov BPair.oneValue BPair.mul (BPair.ofNat 1)
          BPair.oneValue_refl (fun h1 h2 => BPair.mul_congr h1 h2) _ _ _
          (fun i hi => hfirst i (ground.ltOfMem hi))
      exact ground.mulCancel (ground.offOfUnitLt hpref)
        (BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_symm hpre) (BPair.oneValue_refl _))
          (BPair.oneValue_trans (BPair.oneValue_symm (hsplit E hE))
            (BPair.oneValue_trans hprod (hsplit D hD))))
  refine poly.oneValue_of_entries E D (hE.trans hD.symm) ?_
  intro i hi
  rw [hE] at hi
  by_cases hik : i = k
  · rw [hik]; exact hlast
  · exact hfirst i (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) hik)

/-- In an even-sign orbit, strictly decreasing magnitudes and
positive coordinates before the final key identify the display.
The final coordinate may lie on either side or at equal members. -/
theorem signedImage_even_ordered_unique (k : Nat) (D E : List BPair)
    (hD : D.length = k + 1) (hE : E.length = k + 1)
    (hDp : ∀ i, i < k → BPair.unit < ground.getAt BPair.unit D i)
    (hEp : ∀ i, i < k → BPair.unit < ground.getAt BPair.unit E i)
    (hd : ∀ i, i + 1 < k + 1 → (ground.getAt BPair.unit D (i + 1)).marginN < (ground.getAt BPair.unit D i).marginN)
    (he : ∀ i, i + 1 < k + 1 → (ground.getAt BPair.unit E (i + 1)).marginN < (ground.getAt BPair.unit E i).marginN)
    (p : List Nat) (n : Nat) (hp : 0 < ground.countOf p (places.perms (k + 1)))
    (_hn : n < 2 ^ (k + 1)) (hpar : flipParity (k + 1) n = false)
    (himage : poly.oneValue E (signedImage (k + 1) D p n)) : poly.oneValue E D :=
  signedImage_even_weak_unique k D E hD hE
    (fun i hi => ground.leB_of_lt (hDp i hi)) (fun i hi => ground.leB_of_lt (hEp i hi))
    (fun i hi => Nat.le_of_lt (hd i hi)) (fun i hi => Nat.le_of_lt (he i hi)) p n hp hpar himage

/-- The dominant C seed is its displayed orbit's only
dominant coroot key, at canonical representatives. -/
theorem serWeylC_dominant_top (l : Nat) (hl : 0 < l) (v w : List BPair)
    (hv : v.length = l) (hw : w.length = l)
    (hpv : ∀ i, i < l → BPair.unit ≤ ground.getAt BPair.unit v i)
    (hpw : ∀ i, i < l → BPair.unit ≤ ground.getAt BPair.unit w i)
    (b : Bool) (hmem : (w, b) ∈ serWeylC l v) : poly.pnorm w = poly.pnorm v := by
  obtain ⟨p, hp, n, _, hkey⟩ := serWeylC_of_mem l v (w, b) hmem
  have hwkey : w = _ := congrArg Prod.fst hkey
  have hvp : 0 < v.length := by rw [hv]; exact hl
  have hwp : 0 < w.length := by rw [hw]; exact hl
  have hc : poly.oneValue (coordsC w) (signedImage l (coordsC v) p n) := by
    rw [hwkey]
    exact poly.oneValue_trans (coordsC_congr _ _ (poly.pnorm_length _) (poly.pnorm_oneValue _))
      (coordsC_corootsC _ (by rw [signedImage_length]; exact hl))
  have hvr := coordsC_dominant v (fun i hi => hpv i (by rw [← hv]; exact hi))
  have hwr := coordsC_dominant w (fun i hi => hpw i (by rw [← hw]; exact hi))
  have hcoords : poly.oneValue (coordsC w) (coordsC v) := by
    apply signedImage_nonnegative_unique l (coordsC v) (coordsC w)
      ((coordsC_length v).trans hv) ((coordsC_length w).trans hw)
      (fun i hi => hvr.1 i (by rw [hv]; exact hi))
      (fun i hi => hwr.1 i (by rw [hw]; exact hi)) ?_ ?_ p n
      (ground.countOf_pos_of_mem hp) hc
    · intro i hi
      exact BPair.marginN_le (hvr.1 (i + 1) (by rw [hv]; exact hi))
        (hvr.2 i (i + 1) (Nat.lt_succ_self i) (by rw [hv]; exact hi))
    · intro i hi
      exact BPair.marginN_le (hwr.1 (i + 1) (by rw [hw]; exact hi))
        (hwr.2 i (i + 1) (Nat.lt_succ_self i) (by rw [hw]; exact hi))
  apply poly.pnorm_congr w v (hw.trans hv.symm)
  exact poly.oneValue_trans (poly.oneValue_symm (corootsC_coordsC w hwp))
    (poly.oneValue_trans (corootsC_congr _ _ (by rw [coordsC_length, coordsC_length, hw, hv]) hcoords)
      (corootsC_coordsC v hvp))

/-- The strictly dominant C seed is its displayed orbit's only
strictly dominant coroot key, at canonical representatives. -/
theorem serWeylC_strict_top (l : Nat) (hl : 0 < l) (v w : List BPair)
    (hv : v.length = l) (hw : w.length = l)
    (hpv : ∀ i, i < l → BPair.unit < ground.getAt BPair.unit v i)
    (hpw : ∀ i, i < l → BPair.unit < ground.getAt BPair.unit w i)
    (b : Bool) (hmem : (w, b) ∈ serWeylC l v) : poly.pnorm w = poly.pnorm v :=
  serWeylC_dominant_top l hl v w hv hw
    (fun i hi => ground.leB_of_lt (hpv i hi)) (fun i hi => ground.leB_of_lt (hpw i hi)) b hmem

/-- The dominant B seed is its displayed orbit's only
dominant coroot key, at canonical representatives. -/
theorem serWeylB_dominant_top (l : Nat) (hl : 0 < l) (v w : List BPair)
    (hv : v.length = l) (hw : w.length = l)
    (hpv : ∀ i, i < l → BPair.unit ≤ ground.getAt BPair.unit v i)
    (hpw : ∀ i, i < l → BPair.unit ≤ ground.getAt BPair.unit w i)
    (b : Bool) (hmem : (w, b) ∈ serWeylB l v) : poly.pnorm w = poly.pnorm v := by
  obtain ⟨p, hp, n, _, hkey⟩ := serWeylB_of_mem l v (w, b) hmem
  have hwkey : w = _ := congrArg Prod.fst hkey
  have hvp : 0 < v.length := by rw [hv]; exact hl
  have hwp : 0 < w.length := by rw [hw]; exact hl
  have hpar : ∀ i j, i < l → j < l →
      (ground.getAt BPair.unit (coordsB v) i).marginN % 2 = (ground.getAt BPair.unit (coordsB v) j).marginN % 2 :=
    fun i j hi hj => coordsB_parity v i j (by rw [hv]; exact hi) (by rw [hv]; exact hj)
  have hc : poly.oneValue (coordsB w) (signedImage l (coordsB v) p n) := by
    rw [hwkey]
    exact poly.oneValue_trans (coordsB_congr _ _ (poly.pnorm_length _) (poly.pnorm_oneValue _))
      (coordsB_corootsB _ (by rw [signedImage_length]; exact hl)
        (fun i hi => signedImage_even_gaps l (coordsB v) p n (ground.countOf_pos_of_mem hp) hpar i
          (by rw [signedImage_length] at hi; exact hi)))
  have hvr := coordsB_dominant v (fun i hi => hpv i (by rw [← hv]; exact hi))
  have hwr := coordsB_dominant w (fun i hi => hpw i (by rw [← hw]; exact hi))
  have hcoords : poly.oneValue (coordsB w) (coordsB v) := by
    apply signedImage_nonnegative_unique l (coordsB v) (coordsB w)
      ((coordsB_length v).trans hv) ((coordsB_length w).trans hw)
      (fun i hi => hvr.1 i (by rw [hv]; exact hi))
      (fun i hi => hwr.1 i (by rw [hw]; exact hi)) ?_ ?_ p n
      (ground.countOf_pos_of_mem hp) hc
    · intro i hi
      exact BPair.marginN_le (hvr.1 (i + 1) (by rw [hv]; exact hi))
        (hvr.2 i (i + 1) (Nat.lt_succ_self i) (by rw [hv]; exact hi))
    · intro i hi
      exact BPair.marginN_le (hwr.1 (i + 1) (by rw [hw]; exact hi))
        (hwr.2 i (i + 1) (Nat.lt_succ_self i) (by rw [hw]; exact hi))
  apply poly.pnorm_congr w v (hw.trans hv.symm)
  exact poly.oneValue_trans (poly.oneValue_symm (corootsB_coordsB w hwp))
    (poly.oneValue_trans (corootsB_congr _ _ (by rw [coordsB_length, coordsB_length, hw, hv]) hcoords)
      (corootsB_coordsB v hvp))

/-- The strictly dominant B seed is its displayed orbit's only
strictly dominant coroot key, at canonical representatives. -/
theorem serWeylB_strict_top (l : Nat) (hl : 0 < l) (v w : List BPair)
    (hv : v.length = l) (hw : w.length = l)
    (hpv : ∀ i, i < l → BPair.unit < ground.getAt BPair.unit v i)
    (hpw : ∀ i, i < l → BPair.unit < ground.getAt BPair.unit w i)
    (b : Bool) (hmem : (w, b) ∈ serWeylB l v) : poly.pnorm w = poly.pnorm v :=
  serWeylB_dominant_top l hl v w hv hw
    (fun i hi => ground.leB_of_lt (hpv i hi)) (fun i hi => ground.leB_of_lt (hpw i hi)) b hmem

/-- The dominant D seed is its displayed even-sign orbit's
only dominant coroot key, including chamber walls. -/
theorem serWeylD_dominant_top (l : Nat) (hl : 2 ≤ l) (v w : List BPair)
    (hv : v.length = l) (hw : w.length = l)
    (hpv : ∀ i, i < l → BPair.unit ≤ ground.getAt BPair.unit v i)
    (hpw : ∀ i, i < l → BPair.unit ≤ ground.getAt BPair.unit w i)
    (b : Bool) (hmem : (w, b) ∈ serWeylD l v) : poly.pnorm w = poly.pnorm v := by
  obtain ⟨k, hk⟩ := Nat.le.dest hl
  rw [Nat.add_comm 2 k] at hk
  rw [← hk] at hv hw hpv hpw hmem
  have hv2 : 2 ≤ v.length := by rw [hv]; exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))
  have hw2 : 2 ≤ w.length := by rw [hw]; exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))
  obtain ⟨p, hp, n, _, hparity, hkey⟩ := serWeylD_of_mem (k + 2) v (w, b) hmem
  have hwkey : w = _ := congrArg Prod.fst hkey
  have hpar : ∀ i j, i < k + 2 → j < k + 2 →
      (ground.getAt BPair.unit (coordsD v) i).marginN % 2 = (ground.getAt BPair.unit (coordsD v) j).marginN % 2 :=
    fun i j hi hj => coordsD_parity v hv2 i j (by rw [hv]; exact hi) (by rw [hv]; exact hj)
  have hc : poly.oneValue (coordsD w) (signedImage (k + 2) (coordsD v) p n) := by
    rw [hwkey]
    exact poly.oneValue_trans (coordsD_congr _ _ (poly.pnorm_length _) (poly.pnorm_oneValue _))
      (coordsD_corootsD _ (by rw [signedImage_length]; exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k)))
        (fun i hi => signedImage_even_gaps (k + 2) (coordsD v) p n (ground.countOf_pos_of_mem hp) hpar i
          (by rw [signedImage_length] at hi; exact hi)))
  have hvr := coordsD_dominant v hv2 (fun i hi => hpv i (by rw [← hv]; exact hi))
  have hwr := coordsD_dominant w hw2 (fun i hi => hpw i (by rw [← hw]; exact hi))
  have hmargin (x y : BPair) (hxy : x ≤ y) (hxs : x.swap ≤ y) : x.marginN ≤ y.marginN := by
    by_cases hx : x < BPair.unit
    · have h := BPair.marginN_le (ground.leB_of_lt (ground.ltB_swap hx)) hxs
      rw [BPair.marginN_swap] at h
      exact h
    · exact BPair.marginN_le (ground.leB_of_not_lt hx) hxy
  have hcoords : poly.oneValue (coordsD w) (coordsD v) := by
    apply signedImage_even_weak_unique (k + 1) (coordsD v) (coordsD w)
      ((coordsD_length v hv2).trans hv) ((coordsD_length w hw2).trans hw)
      (fun i hi => hvr.1 i (by rw [hv]; exact Nat.succ_lt_succ hi))
      (fun i hi => hwr.1 i (by rw [hw]; exact Nat.succ_lt_succ hi)) ?_ ?_ p n
      (ground.countOf_pos_of_mem hp) hparity hc
    · intro i hi
      have h := hvr.2 i (i + 1) (Nat.lt_succ_self i) (by rw [hv]; exact hi)
      exact hmargin _ _ h.1 h.2
    · intro i hi
      have h := hwr.2 i (i + 1) (Nat.lt_succ_self i) (by rw [hw]; exact hi)
      exact hmargin _ _ h.1 h.2
  apply poly.pnorm_congr w v (hw.trans hv.symm)
  exact poly.oneValue_trans (poly.oneValue_symm (corootsD_coordsD w hw2))
    (poly.oneValue_trans (corootsD_congr _ _ (by rw [coordsD_length w hw2, coordsD_length v hv2, hw, hv]) hcoords)
      (corootsD_coordsD v hv2))

/-- The strictly dominant D seed is its displayed even-sign
orbit's only strictly dominant coroot key. -/
theorem serWeylD_strict_top (l : Nat) (hl : 2 ≤ l) (v w : List BPair)
    (hv : v.length = l) (hw : w.length = l)
    (hpv : ∀ i, i < l → BPair.unit < ground.getAt BPair.unit v i)
    (hpw : ∀ i, i < l → BPair.unit < ground.getAt BPair.unit w i)
    (b : Bool) (hmem : (w, b) ∈ serWeylD l v) : poly.pnorm w = poly.pnorm v :=
  serWeylD_dominant_top l hl v w hv hw (fun i hi => ground.leB_of_lt (hpv i hi))
    (fun i hi => ground.leB_of_lt (hpw i hi)) b hmem

private theorem coordsSuffix_neg (scale : BPair → BPair)
    (hs : ∀ a, scale a.swap = (scale a).swap) :
    ∀ v : List BPair, coordsSuffix scale (poly.neg v) = poly.neg (coordsSuffix scale v)
  | [] => rfl
  | [_] => rfl
  | a :: b :: v => by
    change coordsSuffix scale (a.swap :: poly.neg (b :: v)) = _
    rw [coordsSuffix_cons scale a.swap (poly.neg (b :: v)) (by rw [poly.length_neg]; exact Nat.succ_pos _),
      coordsSuffix_cons scale a (b :: v) (Nat.succ_pos _), coordsSuffix_neg scale hs (b :: v), poly.getAt_neg, hs]
    rfl

/-- B's coordinate display commutes with the memberwise swap. -/
theorem coordsB_neg (v : List BPair) : coordsB (poly.neg v) = poly.neg (coordsB v) :=
  coordsSuffix_neg (fun a => a + a) (fun _ => rfl) v

/-- C's coordinate display commutes with the memberwise swap. -/
theorem coordsC_neg (v : List BPair) : coordsC (poly.neg v) = poly.neg (coordsC v) :=
  coordsSuffix_neg (fun a => a) (fun _ => rfl) v

/-- D's coordinate display commutes with the memberwise swap. -/
theorem coordsD_neg : ∀ v : List BPair, coordsD (poly.neg v) = poly.neg (coordsD v)
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | a :: b :: c :: v => by
    change coordsD (a.swap :: poly.neg (b :: c :: v)) = _
    rw [coordsD_cons a.swap (poly.neg (b :: c :: v)) (by
        rw [poly.length_neg]; exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))),
      coordsD_cons a (b :: c :: v) (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))),
      coordsD_neg (b :: c :: v), poly.getAt_neg]
    rfl

/-- The code with every displayed bit occupied flips every
coordinate, at the width's parity. -/
theorem signedImage_neg (l : Nat) (D : List BPair) (hD : D.length = l) :
    ∃ n, n < 2 ^ l ∧ flipParity l n = (l % 2 == 1)
      ∧ signedImage l D (List.range l) n = poly.neg D := by
  obtain ⟨n, hn, hbit⟩ := ground.baseDigit_exists 2 (by decide) l (fun _ => 1) (by intros; decide)
  refine ⟨n, hn, ?_, ?_⟩
  · unfold flipParity
    rw [ground.foldlSum, Nat.zero_add,
      ground.famFold_congr_members Nat.add 0 (fun j => baseDigit 2 j n) (fun _ => 1)
        (List.range l) (fun j hj => hbit j (ground.ltOfMem hj)),
      ground.famFold_const, ground.length_range, Nat.mul_one]
  · refine ground.getAt_ext BPair.unit _ _ (by rw [signedImage_length, poly.length_neg, hD]) ?_
    intro i hi
    rw [signedImage_length] at hi
    rw [signedImage_getAt l D (List.range l) n i hi, hbit i hi,
      ground.getAt_range l i hi, poly.getAt_neg]
    rfl

/-- The B seed's partner lies in its displayed Weyl orbit. -/
theorem serWeylB_neg_seed (l : Nat) (hl : 0 < l) (v : List BPair) (hv : v.length = l) :
    poly.pnorm (poly.neg v) ∈ (serWeylB l v).map Prod.fst := by
  obtain ⟨n, hn, _, he⟩ := signedImage_neg l (coordsB v) ((coordsB_length v).trans hv)
  have hp : 0 < ground.countOf (List.range l) (places.perms l) := by
    rw [places.countRangePerms]; exact Nat.succ_pos 0
  have h := ground.mem_map_to Prod.fst (serWeylB_mem l v (List.range l) n hp hn)
  rw [he, ← coordsB_neg v, corootsB_coordsB_norm (poly.neg v)
    (by rw [poly.length_neg, hv]; exact hl)] at h
  exact h

/-- The C seed's partner lies in its displayed Weyl orbit. -/
theorem serWeylC_neg_seed (l : Nat) (hl : 0 < l) (v : List BPair) (hv : v.length = l) :
    poly.pnorm (poly.neg v) ∈ (serWeylC l v).map Prod.fst := by
  obtain ⟨n, hn, _, he⟩ := signedImage_neg l (coordsC v) ((coordsC_length v).trans hv)
  have hp : 0 < ground.countOf (List.range l) (places.perms l) := by
    rw [places.countRangePerms]; exact Nat.succ_pos 0
  have h := ground.mem_map_to Prod.fst (serWeylC_mem l v (List.range l) n hp hn)
  rw [he, ← coordsC_neg v, corootsC_coordsC_norm (poly.neg v)
    (by rw [poly.length_neg, hv]; exact hl)] at h
  exact h

/-- Exchanging D's two final coroots flips its final displayed
coordinate and fixes every earlier coordinate. -/
theorem coordsD_forkSwap : ∀ (v : List BPair) (k : Nat), v.length = k + 2 →
    coordsD (ground.adjSwap k v)
      = (coordsD v).set (k + 1) (ground.getAt BPair.unit (coordsD v) (k + 1)).swap
  | [], _, h => Nat.noConfusion h
  | [_], _, h => Nat.noConfusion (Nat.succ.inj h)
  | [a, b], k, h => by
    have hk : k = 0 := (Nat.succ.inj (Nat.succ.inj h)).symm
    rw [hk]
    change [b + a, a + b.swap] = [a + b, (b + a.swap).swap]
    rw [BPair.add_comm b a, ← BPair.swap_add, BPair.swap_swap, BPair.add_comm b.swap a]
  | _ :: _ :: _ :: _, 0, h => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj h))
  | a :: b :: c :: v, k + 1, h => by
    change coordsD (a :: ground.adjSwap k (b :: c :: v)) = _
    rw [coordsD_cons a (ground.adjSwap k (b :: c :: v)) (by
        rw [ground.length_adjSwap]; exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))),
      coordsD_cons a (b :: c :: v) (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))),
      coordsD_forkSwap (b :: c :: v) k (Nat.succ.inj h),
      ground.getAt_set_ne BPair.unit (coordsD (b :: c :: v)) (k + 1) 0 _ (fun he => Nat.noConfusion he)]
    rfl

/-- At even D width the seed's partner lies in its own orbit. -/
theorem serWeylD_neg_seed_even (l : Nat) (hl : 2 ≤ l) (heven : l % 2 = 0)
    (v : List BPair) (hv : v.length = l) :
    poly.pnorm (poly.neg v) ∈ (serWeylD l v).map Prod.fst := by
  have hv2 : 2 ≤ v.length := by rw [hv]; exact hl
  obtain ⟨n, hn, hpar, he⟩ := signedImage_neg l (coordsD v) ((coordsD_length v hv2).trans hv)
  rw [heven] at hpar
  have hp : 0 < ground.countOf (List.range l) (places.perms l) := by
    rw [places.countRangePerms]; exact Nat.succ_pos 0
  have h := ground.mem_map_to Prod.fst (serWeylD_mem l v (List.range l) n hp hn hpar)
  rw [he, ← coordsD_neg v, corootsD_coordsD_norm (poly.neg v) (by rw [poly.length_neg]; exact hv2)] at h
  exact h

/-- At odd D width the seed's partner lies in the orbit of the
seed with its final two coroots exchanged. -/
theorem serWeylD_neg_seed_odd (k : Nat) (hodd : (k + 2) % 2 = 1)
    (v : List BPair) (hv : v.length = k + 2) :
    poly.pnorm (poly.neg v) ∈ (serWeylD (k + 2) (ground.adjSwap k v)).map Prod.fst := by
  have hv2 : 2 ≤ v.length := by rw [hv]; exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))
  have ht : (ground.adjSwap k v).length = k + 2 := (ground.length_adjSwap k v).trans hv
  have ht2 : 2 ≤ (ground.adjSwap k v).length := by rw [ground.length_adjSwap]; exact hv2
  let D := coordsD v
  have hD : D.length = k + 2 := (coordsD_length v hv2).trans hv
  have hj : k + 1 < D.length := by rw [hD]; exact Nat.lt_succ_self _
  obtain ⟨n, hn, hpar, he⟩ := signedImage_neg (k + 2) (coordsD (ground.adjSwap k v))
    ((coordsD_length _ ht2).trans ht)
  rw [hodd] at hpar
  obtain ⟨m, hm, hpm, hem⟩ := signedImage_flip_set (k + 2) (k + 1) n
    (coordsD (ground.adjSwap k v)) (List.range (k + 2)) (Nat.lt_succ_self _) hn
  rw [hpar] at hpm
  have himage : signedImage (k + 2) (coordsD (ground.adjSwap k v)) (List.range (k + 2)) m = poly.neg D := by
    rw [hem, he, coordsD_forkSwap v k hv]
    change (poly.neg (D.set (k + 1) (ground.getAt BPair.unit D (k + 1)).swap)).set (k + 1)
      (ground.getAt BPair.unit (poly.neg (D.set (k + 1) (ground.getAt BPair.unit D (k + 1)).swap)) (k + 1)).swap = _
    rw [poly.getAt_neg, ground.getAt_set_self BPair.unit _ D (k + 1) hj, BPair.swap_swap,
      show poly.neg (D.set (k + 1) (ground.getAt BPair.unit D (k + 1)).swap)
        = (poly.neg D).set (k + 1) (ground.getAt BPair.unit D (k + 1))
        from ground.map_set BPair.swap (ground.getAt BPair.unit D (k + 1)).swap D (k + 1),
      ground.set_set, ← poly.getAt_neg D (k + 1),
      ground.set_self BPair.unit (poly.neg D) (k + 1) (by rw [poly.length_neg]; exact hj)]
  have hp : 0 < ground.countOf (List.range (k + 2)) (places.perms (k + 2)) := by
    rw [places.countRangePerms]; exact Nat.succ_pos 0
  have h := ground.mem_map_to Prod.fst (serWeylD_mem (k + 2) (ground.adjSwap k v) (List.range (k + 2)) m hp hm hpm)
  rw [himage] at h
  change poly.pnorm (corootsD (poly.neg (coordsD v))) ∈ _ at h
  rw [← coordsD_neg v, corootsD_coordsD_norm (poly.neg v) (by rw [poly.length_neg]; exact hv2)] at h
  exact h

/-- The D simple roots in orthonormal coordinates: successive
coordinate differences followed by the final coordinate sum. -/
private def rootRowsD : Nat → elim.Mat
  | 0 => [[BPair.ofNat 1, (BPair.ofNat 1).swap], [BPair.ofNat 1, BPair.ofNat 1]]
  | k + 1 => (BPair.ofNat 1 :: (BPair.ofNat 1).swap :: List.replicate (k + 1) BPair.unit)
      :: (rootRowsD k).map (BPair.unit :: ·)

private theorem rootRowsD_len : ∀ k, (rootRowsD k).length = k + 2
  | 0 => rfl
  | k + 1 => by
    change ((rootRowsD k).map (BPair.unit :: ·)).length + 1 = _
    rw [ground.length_map, rootRowsD_len k]

private theorem rootRowsD_width : ∀ k, elim.rowsLen (k + 2) (rootRowsD k)
  | 0 => ⟨rfl, rfl, trivial⟩
  | k + 1 => by
    refine ⟨?_, elim.rowsLen_map _ _ _ (fun r hr => ?_)⟩
    · change (List.replicate (k + 1) BPair.unit).length + 2 = _
      rw [ground.length_replicate]
    · change r.length + 1 = _
      rw [elim.rowsLen_of_mem (rootRowsD_width k) hr]

private theorem rootRowsD_indep : ∀ k, elim.indepRows (k + 2) (rootRowsD k)
  | 0 => by decide +kernel
  | k + 1 => by
    refine elim.indep_intro _ _ (rootRowsD_width (k + 1)) ?_
    intro cs hcs hnull
    cases cs with
    | nil => trivial
    | cons c cs =>
      have hcsl : cs.length = (rootRowsD k).length := by
        change cs.length + 1 = ((rootRowsD k).map (BPair.unit :: ·)).length + 1 at hcs
        rw [ground.length_map] at hcs
        exact Nat.succ.inj hcs
      have hhead : elim.colHead BPair.unit (rootRowsD (k + 1))
          = BPair.ofNat 1 :: List.replicate (rootRowsD k).length BPair.unit := by
        change BPair.ofNat 1 :: (((rootRowsD k).map (BPair.unit :: ·)).map _) = _
        rw [ground.map_map]
        change BPair.ofNat 1 :: ((rootRowsD k).map (fun _ => BPair.unit)) = _
        rw [ground.map_const]
      have htail : elim.dropCol (rootRowsD (k + 1))
          = ((BPair.ofNat 1).swap :: List.replicate (k + 1) BPair.unit) :: rootRowsD k := by
        change _ :: (((rootRowsD k).map (BPair.unit :: ·)).map (fun r => r.drop 1)) = _
        rw [ground.map_map]
        change _ :: ((rootRowsD k).map (fun r => r)) = _
        rw [ground.map_id]
        rfl
      rw [elim.combo_headSplit (k + 2) (c :: cs) _ hcs (rootRowsD_width (k + 1)), hhead, htail] at hnull
      have hc : c.oneValue BPair.unit := by
        refine BPair.oneValue_trans (BPair.oneValue_symm ?_) hnull.1
        change (c * BPair.ofNat 1 + elim.dotP cs (List.replicate (rootRowsD k).length BPair.unit)).oneValue c
        exact BPair.oneValue_trans
          (BPair.add_congr (BPair.mul_ofNat_one c) (elim.dotP_repl_unit cs _)) (BPair.add_unit c)
      have ht : poly.unitTail (elim.vecAdd
          (elim.vecScale c ((BPair.ofNat 1).swap :: List.replicate (k + 1) BPair.unit))
          (elim.combo (k + 2) cs (rootRowsD k))) := hnull.2
      refine ⟨hc, elim.indep_elim (rootRowsD_indep k) cs hcsl ?_⟩
      exact poly.unitTail_oneValue_right ht
        (elim.vecAdd_null_left _ _
          (by
            rw [elim.length_vecScale, elim.length_combo _ cs _ (rootRowsD_width k)]
            change (List.replicate (k + 1) BPair.unit).length + 1 = k + 2
            rw [ground.length_replicate])
          (elim.unitTail_vecScale_unit hc _))

/-- The D Cartan entry is unchanged by exchanging its two keys. -/
theorem cartD_symm (l i j : Nat) : cartD l i j = cartD l j i := by
  by_cases hij : i = j
  · rw [hij]
  · unfold cartD
    rw [ground.neBeqOf hij, ground.neBeqOf (fun h => hij h.symm)]
    by_cases hi : i + 1 = l
    · have hj : ¬ j + 1 = l := fun h => hij (Nat.succ.inj (hi.trans h.symm))
      rw [ground.eqBeqOf hi, ground.neBeqOf hj]
      rfl
    · by_cases hj : j + 1 = l
      · rw [ground.neBeqOf hi, ground.eqBeqOf hj]
        rfl
      · rw [ground.neBeqOf hi, ground.neBeqOf hj]
        rw [ground.beqSymm j (i + 1), ground.beqSymm i (j + 1), Bool.or_comm]
        rfl

private theorem rootRowsD_head (k j : Nat) (hj : j < k + 2) :
    cartD (k + 3) 0 (j + 1)
      = (ground.getAt BPair.unit (ground.getAt [] (rootRowsD k) j) 0).swap := by
  cases k with
  | zero =>
    cases j with
    | zero => rfl
    | succ j =>
      cases j with
      | zero => rfl
      | succ j => exact absurd hj (Nat.not_lt_of_ge (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))))
  | succ k =>
    cases j with
    | zero =>
      unfold cartD
      cases k <;> rfl
    | succ j =>
      change cartD (k + 1 + 3) 0 (j + 1 + 1) =
        (ground.getAt BPair.unit
          (ground.getAt [] ((rootRowsD k).map (BPair.unit :: ·)) j) 0).swap
      rw [ground.getAt_map [] [] (BPair.unit :: ·) _ j
        (by rw [rootRowsD_len]; exact Nat.lt_of_succ_lt_succ hj)]
      unfold cartD
      cases (j + 1 + 1 + 1 == k + 1 + 3) <;> rfl

private theorem rootRowsD_headDot (k : Nat) (r : List BPair) :
    (elim.dotP (BPair.ofNat 1 :: (BPair.ofNat 1).swap :: List.replicate (k + 1) BPair.unit)
      (BPair.unit :: r)).oneValue (ground.getAt BPair.unit r 0).swap := by
  cases r with
  | nil =>
    exact BPair.oneValue_trans
      (BPair.add_congr (BPair.mul_unit _) (BPair.oneValue_refl _)) (BPair.unit_add _)
  | cons a r =>
    change (BPair.ofNat 1 * BPair.unit + ((BPair.ofNat 1).swap * a
      + elim.dotP (List.replicate (k + 1) BPair.unit) r)).oneValue a.swap
    rw [BPair.swap_mul]
    exact BPair.oneValue_trans
      (BPair.add_congr (BPair.mul_unit _)
        (BPair.add_congr (ground.swap_congr (BPair.ofNat_one_mul a))
          (elim.dotP_null_tail_left _ _ (poly.unitTail_replicate _))))
      (BPair.oneValue_trans (BPair.unit_add _) (BPair.add_unit _))

private theorem cartD_step (l i j : Nat) : cartD (l + 1) (i + 1) (j + 1) = cartD l i j := by
  have hb (a b : Nat) : (a + 1 == b + 1) = (a == b) := by
    by_cases h : a = b
    · rw [ground.eqBeqOf h, ground.eqBeqOf (congrArg Nat.succ h)]
    · rw [ground.neBeqOf h, ground.neBeqOf (fun he => h (Nat.succ.inj he))]
  unfold cartD
  rw [hb j i, hb (i + 1) l, hb (j + 3) l, hb (j + 1) l, hb (i + 3) l,
    hb (j + 1) i, hb j (i + 1)]

private theorem rootRowsD_gram : ∀ k i j, i < k + 2 → j < k + 2 →
    (elim.dotP (ground.getAt [] (rootRowsD k) i)
      (ground.getAt [] (rootRowsD k) j)).oneValue (cartD (k + 2) i j)
  | 0, i, j, hi, hj => by
    cases i with
    | zero =>
      cases j with
      | zero => decide +kernel
      | succ j =>
        cases j with
        | zero => decide +kernel
        | succ j => exact absurd hj (Nat.not_lt_of_ge (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))))
    | succ i =>
      cases i with
      | zero =>
        cases j with
        | zero => decide +kernel
        | succ j =>
          cases j with
          | zero => decide +kernel
          | succ j => exact absurd hj (Nat.not_lt_of_ge (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))))
      | succ i => exact absurd hi (Nat.not_lt_of_ge (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))))
  | k + 1, 0, 0, _, _ => by
    rw [cartDd]
    change (BPair.ofNat 1 * BPair.ofNat 1 + ((BPair.ofNat 1).swap * (BPair.ofNat 1).swap
      + elim.dotP (List.replicate (k + 1) BPair.unit) (List.replicate (k + 1) BPair.unit))).oneValue _
    exact BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.add_congr (BPair.oneValue_refl _) (elim.dotP_repl_unit _ _))) (by decide +kernel)
  | k + 1, 0, j + 1, _, hj => by
    change (elim.dotP _ (ground.getAt [] ((rootRowsD k).map (BPair.unit :: ·)) j)).oneValue _
    rw [ground.getAt_map [] [] (BPair.unit :: ·) _ j (by rw [rootRowsD_len]; exact Nat.lt_of_succ_lt_succ hj),
      rootRowsD_head k j (Nat.lt_of_succ_lt_succ hj)]
    exact rootRowsD_headDot k _
  | k + 1, i + 1, 0, hi, _ => by
    rw [elim.dotP_comm, cartD_symm]
    change (elim.dotP _ (ground.getAt [] ((rootRowsD k).map (BPair.unit :: ·)) i)).oneValue _
    rw [ground.getAt_map [] [] (BPair.unit :: ·) _ i (by rw [rootRowsD_len]; exact Nat.lt_of_succ_lt_succ hi),
      rootRowsD_head k i (Nat.lt_of_succ_lt_succ hi)]
    exact rootRowsD_headDot k _
  | k + 1, i + 1, j + 1, hi, hj => by
    change (elim.dotP (ground.getAt [] ((rootRowsD k).map (BPair.unit :: ·)) i)
      (ground.getAt [] ((rootRowsD k).map (BPair.unit :: ·)) j)).oneValue _
    rw [ground.getAt_map [] [] (BPair.unit :: ·) _ i (by rw [rootRowsD_len]; exact Nat.lt_of_succ_lt_succ hi),
      ground.getAt_map [] [] (BPair.unit :: ·) _ j (by rw [rootRowsD_len]; exact Nat.lt_of_succ_lt_succ hj)]
    rw [cartD_step (k + 2) i j]
    change (BPair.unit * BPair.unit + elim.dotP _ _).oneValue (cartD (k + 2) i j)
    exact BPair.oneValue_trans (BPair.add_congr (BPair.mul_unit _) (rootRowsD_gram k i j
      (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj))) (BPair.unit_add _)
termination_by structural k => k

/-- Every leading minor of the D Cartan rows is off the sum's unit:
the rows are the Gram of the independent displayed simple roots. -/
theorem cartanD_lead (k m : Nat) (hm : m < k + 2) :
    ¬ (elim.leadMinor (tableD (k + 2)).cartan (m + 1)).oneValue BPair.unit := by
  have hlen : (tableD (k + 2)).cartan.length = k + 2 := ground.matOf_length _ _ _
  have hrl : (elim.gramM (rootRowsD k)).length = k + 2 :=
    (elim.sqAt_len (elim.gram_sqAt _)).trans (rootRowsD_len k)
  have he := elim.leadMinor_congr (elim.gramM (rootRowsD k)) (tableD (k + 2)).cartan
    (hrl.trans hlen.symm) (fun i hi j hj => by
      rw [hrl] at hi hj
      rw [elim.gramM_entry _ i j (by rw [rootRowsD_len]; exact hi) (by rw [rootRowsD_len]; exact hj),
        cartD_eq, ground.matOf_entry [] BPair.unit _ _ _ i j hi hj]
      exact rootRowsD_gram k i j hi hj) (m + 1) (by rw [hrl]; exact hm)
  intro hz
  exact elim.gram_leadMinor _ _ (rootRowsD_indep k) m (by rw [rootRowsD_len]; exact hm)
    (BPair.oneValue_trans he hz)

private theorem cartD_fork_cols (k i : Nat) (hi : i < k) :
    cartD (k + 2) i k = cartD (k + 2) i (k + 1) := by
  have hki : ¬ k = i := fun h => Nat.ne_of_lt hi h.symm
  have hkii : ¬ k + 1 = i := fun h => Nat.not_lt_of_ge (Nat.le_succ k) (by change k + 1 < k; rw [h]; exact hi)
  have hil : ¬ i + 1 = k + 2 := Nat.ne_of_lt (Nat.lt_succ_of_lt (Nat.succ_lt_succ hi))
  unfold cartD
  rw [ground.neBeqOf hki, ground.neBeqOf hkii, ground.neBeqOf hil,
    ground.neBeqOf (Nat.ne_of_lt (Nat.lt_succ_self (k + 1))), ground.eqBeqOf (rfl : k + 1 + 1 = k + 2)]
  by_cases he : i + 1 = k
  · rw [ground.eqBeqOf he.symm, ground.eqBeqOf (show i + 3 = k + 2 from congrArg (fun n => n + 2) he)]
    rfl
  · have hne : ¬ i + 3 = k + 2 := fun h => he (ground.addCancelR 2 (show i + 1 + 2 = k + 2 from h))
    rw [ground.neBeqOf (fun h => he h.symm), ground.neBeqOf hne]
    rfl

/-- Simultaneously exchanging D's final two simple keys preserves
its Cartan entries. -/
theorem cartD_forkSwap (k i j : Nat) (hi : i < k + 2) (hj : j < k + 2) :
    cartD (k + 2) (ground.swapIx k (k + 1) i) (ground.swapIx k (k + 1) j)
      = cartD (k + 2) i j := by
  have hsmall (a : Nat) (ha : a < k + 2) (h0 : a ≠ k) (h1 : a ≠ k + 1) : a < k :=
    Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ ha) h1)) h0
  by_cases hi0 : i = k
  · rw [hi0, ground.swapIx_fst]
    by_cases hj0 : j = k
    · rw [hj0, ground.swapIx_fst, cartDd, cartDd]
    · by_cases hj1 : j = k + 1
      · rw [hj1, ground.swapIx_snd (Nat.succ_ne_self k), cartD_symm _ (k + 1) k]
      · rw [ground.swapIx_off hj0 hj1, cartD_symm _ (k + 1) j, cartD_symm _ k j]
        exact (cartD_fork_cols k j (hsmall j hj hj0 hj1)).symm
  · by_cases hi1 : i = k + 1
    · rw [hi1, ground.swapIx_snd (Nat.succ_ne_self k)]
      by_cases hj0 : j = k
      · rw [hj0, ground.swapIx_fst, cartD_symm _ (k + 1) k]
      · by_cases hj1 : j = k + 1
        · rw [hj1, ground.swapIx_snd (Nat.succ_ne_self k), cartDd, cartDd]
        · rw [ground.swapIx_off hj0 hj1, cartD_symm _ (k + 1) j, cartD_symm _ k j]
          exact cartD_fork_cols k j (hsmall j hj hj0 hj1)
    · rw [ground.swapIx_off hi0 hi1]
      by_cases hj0 : j = k
      · rw [hj0, ground.swapIx_fst]
        exact (cartD_fork_cols k i (hsmall i hi hi0 hi1)).symm
      · by_cases hj1 : j = k + 1
        · rw [hj1, ground.swapIx_snd (Nat.succ_ne_self k)]
          exact cartD_fork_cols k i (hsmall i hi hi0 hi1)
        · rw [ground.swapIx_off hj0 hj1]

/-- The final-key exchange carries a D Cartan row to the exchanged
row, the simultaneous entry symmetry as a vector identity. -/
theorem cartanD_forkSwap (k i : Nat) (hi : i < k + 2) :
    ground.adjSwap k (ground.getAt [] (tableD (k + 2)).cartan i)
      = ground.getAt [] (tableD (k + 2)).cartan (ground.swapIx k (k + 1) i) := by
  have hlen : (tableD (k + 2)).cartan.length = k + 2 := ground.matOf_length _ _ _
  have hw : elim.rowsLen (k + 2) (tableD (k + 2)).cartan := elim.rowsLen_matOf _ _ _
  have his := ground.swapIx_lt (Nat.lt_succ_of_lt (Nat.lt_succ_self k)) (Nat.lt_succ_self (k + 1)) i hi
  refine ground.getAt_ext BPair.unit _ _ (by rw [ground.length_adjSwap,
    elim.rowsLen_getAt _ i hw (by rw [hlen]; exact hi),
    elim.rowsLen_getAt _ _ hw (by rw [hlen]; exact his)]) ?_
  intro j hj
  rw [ground.length_adjSwap, elim.rowsLen_getAt _ i hw (by rw [hlen]; exact hi)] at hj
  rw [ground.getAt_adjSwap BPair.unit k _ (by rw [elim.rowsLen_getAt _ i hw (by rw [hlen]; exact hi)]; exact Nat.lt_succ_self _),
    cartD_eq, ground.matOf_entry [] BPair.unit _ _ _ i _ hi
      (ground.swapIx_lt (Nat.lt_succ_of_lt (Nat.lt_succ_self k)) (Nat.lt_succ_self (k + 1)) j hj),
    ground.matOf_entry [] BPair.unit _ _ _ _ j his hj]
  have he := cartD_forkSwap k i (ground.swapIx k (k + 1) j) hi
    (ground.swapIx_lt (Nat.lt_succ_of_lt (Nat.lt_succ_self k)) (Nat.lt_succ_self (k + 1)) j hj)
  rw [ground.swapIx_invol] at he
  exact he.symm

/-- The prefixes of G2's six alternating simple reflections,
starting at the negative identity on a strictly dominant key. -/
def g2DualMat (j : Nat) : elim.Mat :=
  ground.getAt []
    [[poly.neg (([1, 0].map BPair.ofNat)), poly.neg (([0, 1].map BPair.ofNat))],
     [([1, 0].map BPair.ofNat), poly.neg (([1, 1].map BPair.ofNat))],
     [poly.neg (([2, 3].map BPair.ofNat)), ([1, 1].map BPair.ofNat)],
     [([2, 3].map BPair.ofNat), poly.neg (([1, 2].map BPair.ofNat))],
     [poly.neg (([1, 3].map BPair.ofNat)), ([1, 2].map BPair.ofNat)],
     [([1, 3].map BPair.ofNat), poly.neg (([0, 1].map BPair.ofNat))],
     [([1, 0].map BPair.ofNat), ([0, 1].map BPair.ofNat)]] j

/-- G2's twelve word actions: the first six alternating prefixes
and their memberwise partners. The seventh prefix is the identity,
which starts the partnered half of this cycle. -/
def weylMatG2 (j : Nat) : elim.Mat :=
  if j < 6 then g2DualMat j else elim.matSwap (g2DualMat (j - 6))

/-- G2's natural simple-fold coefficient matrix at a word
image: the transposed adjugate rows solve the gap from that image
to its seed (`con:sertables`' adjugate rows and dominance folds). -/
def weylFoldG2 (j : Nat) : elim.Mat :=
  elim.matMul (elim.transposeM (adjG2.map (fun r => r.map BPair.ofNat)))
    (elim.matAdd (elim.idMat 2) (elim.matSwap (weylMatG2 j)))

/-- Every G2 word gap is the displayed natural simple fold.
The coefficient matrices have the rank's shape and upper-side
entries, and their Cartan products rejoin the word to the identity. -/
theorem weylFoldG2_read : ∀ j, j < 12 →
    elim.sqAt (weylFoldG2 j) 2
      ∧ (∀ i, i < 2 → ∀ k, k < 2 → BPair.unit ≤ getAt BPair.unit (getAt [] (weylFoldG2 j) i) k)
      ∧ elim.matOneValue (elim.matAdd (weylMatG2 j)
        (elim.matMul (elim.transposeM tableG2.cartan) (weylFoldG2 j))) (elim.idMat 2) := by
  decide +kernel

/-- The two simple letters act on the twelve-cycle by its two
alternating edge matchings. -/
def weylStepG2 (i j : Nat) : Nat :=
  if i == j % 2 then (j + 1) % 12 else (j + 11) % 12

/-- The word actions have the two-key square shape. -/
theorem weylMatG2_shape : ∀ j, j < 12 →
    (weylMatG2 j).length = 2 ∧ elim.rowsLen 2 (weylMatG2 j) := by decide +kernel

/-- The reversed word's index in G2's displayed twelve-element
list, the inverse element at the reflection grading's transport. -/
def weylInvG2 (j : Nat) : Nat :=
  ground.getAt 0 [0, 1, 10, 3, 8, 5, 6, 7, 4, 9, 2, 11] j

/-- Word reversal permutes G2's displayed indices, keeps their
grading, and moves the word action across the fundamental Gram. -/
theorem weylInvG2_read : ∀ j, j < 12 →
    weylInvG2 j < 12 ∧ weylInvG2 (weylInvG2 j) = j
      ∧ weylInvG2 j % 2 = j % 2
      ∧ elim.matOneValue
        (elim.matMul (elim.transposeM (weylMatG2 j)) fundG2.gram)
        (elim.matMul fundG2.gram (weylMatG2 (weylInvG2 j))) := by
  decide +kernel

/-- A G2 word moves across the form as its reversed word, at
every pair of coroot keys (`con:sertables`' kept-form transport). -/
theorem weylMatG2_dot (j : Nat) (hj : j < 12)
    (x y : List BPair) (hx : x.length = 2) (hy : y.length = 2) :
    (dotB fundG2 (poly.pnorm (elim.matVec (weylMatG2 j) x)) y).oneValue
      (dotB fundG2 x (poly.pnorm (elim.matVec (weylMatG2 (weylInvG2 j)) y))) := by
  have hM := weylMatG2_shape j hj
  have hI := weylMatG2_shape (weylInvG2 j) (weylInvG2_read j hj).1
  have hG : elim.rowsLen 2 fundG2.gram := by decide +kernel
  refine BPair.oneValue_trans (dotB_congrL fundG2 _ _ y (poly.pnorm_oneValue _)) ?_
  refine BPair.oneValue_trans ?_ (BPair.oneValue_symm
    (dotB_congrR fundG2 x _ _ (poly.pnorm_oneValue _)))
  change (elim.dotP (elim.matVec (weylMatG2 j) x) (elim.matVec fundG2.gram y)).oneValue
    (elim.dotP x (elim.matVec fundG2.gram (elim.matVec (weylMatG2 (weylInvG2 j)) y)))
  refine BPair.oneValue_trans (elim.dotP_matVec_transpose 2 (weylMatG2 j) x
    (elim.matVec fundG2.gram y) hM.2 hx
    ((elim.matVec_length _ _).trans hM.1.symm)) ?_
  apply elim.dotP_oneValue_right
  exact poly.oneValue_trans
    (poly.oneValue_symm (elim.matVec_matMul _ fundG2.gram 2 hG y hy))
    (poly.oneValue_trans (elim.matVec_matOne _ _ y (weylInvG2_read j hj).2.2.2)
      (elim.matVec_matMul fundG2.gram _ 2 hI.2 y hy))

/-- Two distinct G2 word matrices have a row ordered entrywise
in one direction with a strict entry. Their actions therefore
separate at every strictly positive coroot seed. -/
theorem weylMatG2_separation : ∀ j, j < 12 → ∀ k, k < 12 → j = k ∨
    (∃ i, i < 2 ∧
      ((∀ q, q < 2 → getAt BPair.unit (getAt [] (weylMatG2 j) i) q ≤ getAt BPair.unit (getAt [] (weylMatG2 k) i) q)
        ∧ ∃ q, q < 2 ∧ getAt BPair.unit (getAt [] (weylMatG2 j) i) q < getAt BPair.unit (getAt [] (weylMatG2 k) i) q))
      ∨ (∃ i, i < 2 ∧
        (∀ q, q < 2 → getAt BPair.unit (getAt [] (weylMatG2 k) i) q ≤ getAt BPair.unit (getAt [] (weylMatG2 j) i) q)
        ∧ ∃ q, q < 2 ∧ getAt BPair.unit (getAt [] (weylMatG2 k) i) q < getAt BPair.unit (getAt [] (weylMatG2 j) i) q) := by
  decide +kernel

/-- Each G2 action's nonidentity column is detected by a
nonpositive row at a negative entry in that column. -/
theorem weylMatG2_chamber : ∀ j, j < 12 → ∀ k, k < 2 →
    (∀ i, i < 2 → (ground.getAt BPair.unit (ground.getAt [] (weylMatG2 j) i) k).oneValue
      (if k = i then BPair.ofNat 1 else BPair.unit)) ∨
    ∃ i, i < 2 ∧ (∀ q, q < 2 → ground.getAt BPair.unit (ground.getAt [] (weylMatG2 j) i) q ≤ BPair.unit)
      ∧ ground.getAt BPair.unit (ground.getAt [] (weylMatG2 j) i) k < BPair.unit := by decide +kernel

/-- Each simple letter keeps the cycle's index range. -/
theorem weylStepG2_lt : ∀ i, i < 2 → ∀ j, j < 12 → weylStepG2 i j < 12 := by decide +kernel

/-- Every letter reverses the cycle's reflection grade. -/
theorem weylStepG2_parity : ∀ i, i < 2 → ∀ j, j < 12 →
    (weylStepG2 i j % 2 == 1) = !(j % 2 == 1) := by decide +kernel

/-- A simple letter's matching is its own inverse. -/
theorem weylStepG2_invol : ∀ i, i < 2 → ∀ j, j < 12 →
    weylStepG2 i (weylStepG2 i j) = j := by decide +kernel

/-- The cycle's edge matchings are the actual simple reflection
matrices at the displayed G2 Cartan data. -/
theorem weylMatG2_step : ∀ i, i < 2 → ∀ j, j < 12 →
    elim.matOneValue (elim.matMul (reflM tableG2 i) (weylMatG2 j))
      (weylMatG2 (weylStepG2 i j)) := by decide +kernel

/-- The first seven cycle actions are the alternating prefixes,
including the identity reached at six letters. -/
theorem weylMatG2_prefix : ∀ j, j < 7 → weylMatG2 j = g2DualMat j := by decide +kernel

/-- On the first half-cycle the prescribed alternating letter
advances to the next prefix. -/
theorem weylStepG2_prefix : ∀ j, j < 6 → weylStepG2 (j % 2) j = j + 1 := by decide +kernel

/-- The displayed G2 orbit of a coroot key, with one grade per
word action and canonical balance representatives. -/
def weylG2 (v : List BPair) : List (List BPair × Bool) :=
  (List.range 12).map (fun j => (poly.pnorm (elim.matVec (weylMatG2 j) v), j % 2 == 1))

/-- Every G2 displayed key has two canonical coroot entries. -/
theorem weylG2_shape (v : List BPair) : wShapeRead tableG2 (weylG2 v) := by
  intro p hp
  obtain ⟨j, hj, he⟩ := ground.mem_map_of _ _ p hp
  rw [← he]
  refine ⟨?_, poly.pnorm_pnorm _⟩
  rw [poly.pnorm_length, elim.matVec_length, (weylMatG2_shape j (ground.ltOfMemRange hj)).1]
  rfl

/-- The G2 displayed family has twelve entries at every seed. -/
theorem weylG2_length (v : List BPair) : (weylG2 v).length = 12 := ground.length_mapRange _ _

/-- Every cycle index supplies its displayed key and grade. -/
theorem weylG2_mem (v : List BPair) (j : Nat) (hj : j < 12) :
    (poly.pnorm (elim.matVec (weylMatG2 j) v), j % 2 == 1) ∈ weylG2 v :=
  ground.mem_map_to _ (ground.memRange hj)

/-- The identity's cycle position supplies the even seed. -/
theorem weylG2_seed (v : List BPair) (hv : v.length = 2) :
    (poly.pnorm v, false) ∈ weylG2 v := by
  have h := weylG2_mem v 6 (by decide)
  have he : poly.pnorm (elim.matVec (weylMatG2 6) v) = poly.pnorm v :=
    poly.pnorm_congr _ _ ((elim.matVec_length _ v).trans hv.symm)
      (elim.matVec_idMat 2 v hv)
  rw [he] at h
  exact h

/-- Distinct G2 word indices have distinct canonical images at
every strictly dominant seed, by the ordered-row certificate. -/
theorem weylMatG2_inj (v : List BPair) (hv : v.length = 2)
    (hp : ∀ i, i < 2 → BPair.unit < ground.getAt BPair.unit v i)
    (j k : Nat) (hj : j < 12) (hk : k < 12)
    (he : poly.pnorm (elim.matVec (weylMatG2 j) v) = poly.pnorm (elim.matVec (weylMatG2 k) v)) : j = k := by
  have rows (a b : Nat) (ha : a < 12) (hb : b < 12)
      (heq : poly.pnorm (elim.matVec (weylMatG2 a) v) = poly.pnorm (elim.matVec (weylMatG2 b) v))
      (i : Nat) (hi : i < 2)
      (hle : ∀ q, q < 2 → getAt BPair.unit (getAt [] (weylMatG2 a) i) q ≤ getAt BPair.unit (getAt [] (weylMatG2 b) i) q)
      (q : Nat) (hq : q < 2)
      (hlt : getAt BPair.unit (getAt [] (weylMatG2 a) i) q < getAt BPair.unit (getAt [] (weylMatG2 b) i) q) : False := by
    have hA := weylMatG2_shape a ha
    have hB := weylMatG2_shape b hb
    have h := poly.oneValue_getAt i (poly.oneValue_trans (poly.oneValue_symm (poly.pnorm_oneValue _))
      (poly.oneValue_trans (poly.oneValue_of_eq heq) (poly.pnorm_oneValue _)))
    rw [elim.getAt_matVec _ _ i (by rw [hA.1]; exact hi),
      elim.getAt_matVec _ _ i (by rw [hB.1]; exact hi)] at h
    apply elim.dotP_ne_of_row_le _ _ v
      ((elim.rowsLen_getAt _ i hA.2 (by rw [hA.1]; exact hi)).trans hv.symm)
      ((elim.rowsLen_getAt _ i hB.2 (by rw [hB.1]; exact hi)).trans hv.symm)
      (fun z hz => hle z (by rw [← hv]; exact hz))
      (fun z hz => hp z (by rw [← hv]; exact hz)) q (by rw [hv]; exact hq) hlt
    exact BPair.oneValue_trans (BPair.oneValue_symm (elim.dotN_read _ _))
      (BPair.oneValue_trans h (elim.dotN_read _ _))
  cases weylMatG2_separation j hj k hk with
  | inl h => exact h
  | inr h =>
    cases h with
    | inl h =>
      obtain ⟨i, hi, hle, q, hq, hlt⟩ := h
      exact False.elim (rows j k hj hk he i hi hle q hq hlt)
    | inr h =>
      obtain ⟨i, hi, hle, q, hq, hlt⟩ := h
      exact False.elim (rows k j hk hj he.symm i hi hle q hq hlt)

/-- G2's displayed graded family has distinct coroot keys at
every strictly dominant seed, one image per word index. -/
theorem weylG2_regular (v : List BPair) (hv : v.length = 2)
    (hp : ∀ i, i < 2 → BPair.unit < ground.getAt BPair.unit v i) :
    ground.distinctList ((weylG2 v).map Prod.fst) := by
  change ground.distinctList (((List.range 12).map
    (fun j => (poly.pnorm (elim.matVec (weylMatG2 j) v), j % 2 == 1))).map Prod.fst)
  rw [ground.map_map]
  intro w hw
  obtain ⟨j, hj, he⟩ := ground.mem_map_of _ _ w hw
  rw [← he, ground.countOf_map_inj _ j (List.range 12)
    (fun k hk heq => weylMatG2_inj v hv hp k j (ground.ltOfMem hk) (ground.ltOfMemRange hj) heq)]
  exact Nat.le_of_eq (ground.countOf_range_one (ground.ltOfMemRange hj))

/-- The G2 displayed orbit of a dominant key has that key as its
only dominant image, including the chamber walls and the unit. -/
theorem weylG2_dominant_top (v w : List BPair) (hv : v.length = 2)
    (hpv : ∀ i, i < 2 → BPair.unit ≤ ground.getAt BPair.unit v i)
    (hpw : ∀ i, i < 2 → BPair.unit ≤ ground.getAt BPair.unit w i)
    (b : Bool) (hmem : (w, b) ∈ weylG2 v) : poly.pnorm w = poly.pnorm v := by
  obtain ⟨j, hj, he⟩ := ground.mem_map_of _ _ (w, b) hmem
  have hj' := ground.ltOfMemRange hj
  have hw : w = poly.pnorm (elim.matVec (weylMatG2 j) v) := (congrArg Prod.fst he).symm
  have hm := weylMatG2_shape j hj'
  have him : ∀ i, i < 2 → BPair.unit ≤ ground.getAt BPair.unit (elim.matVec (weylMatG2 j) v) i := by
    intro i hi
    have h := poly.oneValue_getAt i (poly.pnorm_oneValue (elim.matVec (weylMatG2 j) v))
    rw [← hw] at h
    exact ground.leB_congr_right h (hpw i hi)
  have hfixed := elim.matVec_nonnegative_fixed (weylMatG2 j) 2 (elim.sqAt_of hm.1 hm.2)
    (weylMatG2_chamber j hj') v hv hpv him
  rw [hw, poly.pnorm_pnorm]
  exact poly.pnorm_congr _ _ ((elim.matVec_length _ _).trans (hm.1.trans hv.symm)) hfixed

/-- Fundamental data at displayed adjugate rows: simple positions
are the one-key folds, and a root's reflected fold changes only its
reflecting coefficient. The simple root's partnered coefficient
has the same magnitude, so its permutation position is fixed. -/
def fundOfRows (t : Table) (rows : List (List Nat)) (scale : Nat) : FundData :=
  ⟨gramRows t rows, scale,
   (List.range t.rank).map (fun i => ground.posBy (fun a b => a == b) (ground.unitAt t.rank i) t.posFolds),
   (List.range t.rank).map (fun i => t.posFolds.map (fun c =>
     ground.posBy (fun a b => a == b)
       (c.set i (BPair.ofNat (ground.getAt 0 c i) + (gentable.corootAt t c i).swap).marginN) t.posFolds))⟩

/-- F4's fundamental form and reflection permutation data. -/
def fundF4 : FundData := fundOfRows tableF4 adjF4 1

/-- E6's fundamental form and reflection permutation data at its
three-fold clearing scale. -/
def fundE6 : FundData := fundOfRows tableE6 adjE6 3

/-- E7's fundamental form and reflection permutation data at its
two-fold clearing scale. -/
def fundE7 : FundData := fundOfRows tableE7 adjE7 2

/-- E8's fundamental form and reflection permutation data. -/
def fundE8 : FundData := fundOfRows tableE8 adjE8 1

/-! The fixed fundamental data satisfy the displayed shape, Gram,
reflection and positive-root permutation identities. -/

set_option maxHeartbeats 4000000 in
/-- F4's fundamental data have their stated shape. -/
theorem fundShape_F4 : fundShape tableF4 fundF4 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- F4's Gram reads the scaled length diagonal. -/
theorem gramRead_F4 : gramRead tableF4 fundF4 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- F4's simple positions read the one-key folds. -/
theorem simplePosRead_F4 : simplePosRead tableF4 fundF4 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- F4's simple matrices square to the identity. -/
theorem reflSquareRead_F4 : reflSquareRead tableF4 := by
  apply reflSquareRead_of_diagonal
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- F4's positive-root permutations are involutions. -/
theorem permSquareRead_F4 : permSquareRead tableF4 fundF4 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- F4's positive-root permutations read the actual reflections. -/
theorem permImageRead_F4 : permImageRead tableF4 fundF4 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- F4's positive roots pair positively with rho. -/
theorem rhoDotRead_F4 : rhoDotRead tableF4 fundF4 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- F4's simple reflections preserve the displayed Gram. -/
theorem reflFormRead_F4 : reflFormRead tableF4 fundF4 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- E6's fundamental data have their stated shape. -/
theorem fundShape_E6 : fundShape tableE6 fundE6 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- E6's Gram reads the scaled length diagonal. -/
theorem gramRead_E6 : gramRead tableE6 fundE6 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- E6's simple positions read the one-key folds. -/
theorem simplePosRead_E6 : simplePosRead tableE6 fundE6 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- E6's simple matrices square to the identity. -/
theorem reflSquareRead_E6 : reflSquareRead tableE6 := by
  apply reflSquareRead_of_diagonal
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- E6's positive-root permutations are involutions. -/
theorem permSquareRead_E6 : permSquareRead tableE6 fundE6 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- E6's positive-root permutations read the actual reflections. -/
theorem permImageRead_E6 : permImageRead tableE6 fundE6 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- E6's positive roots pair positively with rho. -/
theorem rhoDotRead_E6 : rhoDotRead tableE6 fundE6 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- E6's simple reflections preserve the displayed Gram. -/
theorem reflFormRead_E6 : reflFormRead tableE6 fundE6 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- E7's fundamental data have their stated shape. -/
theorem fundShape_E7 : fundShape tableE7 fundE7 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- E7's Gram reads the scaled length diagonal. -/
theorem gramRead_E7 : gramRead tableE7 fundE7 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- E7's simple positions read the one-key folds. -/
theorem simplePosRead_E7 : simplePosRead tableE7 fundE7 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- E7's simple matrices square to the identity. -/
theorem reflSquareRead_E7 : reflSquareRead tableE7 := by
  apply reflSquareRead_of_diagonal
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- E7's positive-root permutations are involutions. -/
theorem permSquareRead_E7 : permSquareRead tableE7 fundE7 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- E7's positive-root permutations read the actual reflections. -/
theorem permImageRead_E7 : permImageRead tableE7 fundE7 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- E7's positive roots pair positively with rho. -/
theorem rhoDotRead_E7 : rhoDotRead tableE7 fundE7 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- E7's simple reflections preserve the displayed Gram. -/
theorem reflFormRead_E7 : reflFormRead tableE7 fundE7 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- E8's fundamental data have their stated shape. -/
theorem fundShape_E8 : fundShape tableE8 fundE8 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- E8's Gram reads the scaled length diagonal. -/
theorem gramRead_E8 : gramRead tableE8 fundE8 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- E8's simple positions read the one-key folds. -/
theorem simplePosRead_E8 : simplePosRead tableE8 fundE8 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- E8's simple matrices square to the identity. -/
theorem reflSquareRead_E8 : reflSquareRead tableE8 := by
  apply reflSquareRead_of_diagonal
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- E8's positive-root permutations are involutions. -/
theorem permSquareRead_E8 : permSquareRead tableE8 fundE8 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- E8's positive-root permutations read the actual reflections. -/
theorem permImageRead_E8 : permImageRead tableE8 fundE8 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- E8's positive roots pair positively with rho. -/
theorem rhoDotRead_E8 : rhoDotRead tableE8 fundE8 := by decide +kernel

set_option maxHeartbeats 4000000 in
/-- E8's simple reflections preserve the displayed Gram. -/
theorem reflFormRead_E8 : reflFormRead tableE8 fundE8 := by decide +kernel


/-- G2's displayed fundamental Gram is symmetric. -/
theorem gramSymRead_G2 : gramSymRead fundG2 := by decide +kernel

/-- G2's transposed Cartan solve has the square frame, nonzero
leading minors and positive determinant required by natural fold
cofactors. The leading determinants are read by descent. -/
theorem cartanSolve_G2 : elim.sqAt tableG2.cartan tableG2.rank
    ∧ (∀ k, k < tableG2.rank →
      ¬ (elim.leadMinor (elim.transposeM tableG2.cartan) (k + 1)).oneValue BPair.unit)
    ∧ BPair.unit < elim.detD (elim.transposeM tableG2.cartan) := by
  have hs : elim.rowsLen (elim.transposeM tableG2.cartan).length (elim.transposeM tableG2.cartan) := by decide +kernel
  have hl : (elim.transposeM tableG2.cartan).length = tableG2.rank := by decide +kernel
  have hm : ∀ k, k < tableG2.rank →
      ¬ (elim.detD (((elim.transposeM tableG2.cartan).take (k + 1)).map (fun r => r.take (k + 1)))).oneValue BPair.unit := by
    decide +kernel
  refine ⟨by decide +kernel, ?_, by decide +kernel⟩
  intro k hk hz
  exact hm k hk (BPair.oneValue_trans (BPair.oneValue_symm
    (elim.leadMinor_detD _ hs (k + 1) (by rw [hl]; exact hk))) hz)

/-- F4's displayed fundamental Gram is symmetric. -/
theorem gramSymRead_F4 : gramSymRead fundF4 := by decide +kernel

/-- F4's transposed Cartan solve has the square frame, nonzero
leading minors and positive determinant required by natural fold
cofactors. The leading determinants are read by descent. -/
theorem cartanSolve_F4 : elim.sqAt tableF4.cartan tableF4.rank
    ∧ (∀ k, k < tableF4.rank →
      ¬ (elim.leadMinor (elim.transposeM tableF4.cartan) (k + 1)).oneValue BPair.unit)
    ∧ BPair.unit < elim.detD (elim.transposeM tableF4.cartan) := by
  have hs : elim.rowsLen (elim.transposeM tableF4.cartan).length (elim.transposeM tableF4.cartan) := by decide +kernel
  have hl : (elim.transposeM tableF4.cartan).length = tableF4.rank := by decide +kernel
  have hm : ∀ k, k < tableF4.rank →
      ¬ (elim.detD (((elim.transposeM tableF4.cartan).take (k + 1)).map (fun r => r.take (k + 1)))).oneValue BPair.unit := by
    decide +kernel
  refine ⟨by decide +kernel, ?_, by decide +kernel⟩
  intro k hk hz
  exact hm k hk (BPair.oneValue_trans (BPair.oneValue_symm
    (elim.leadMinor_detD _ hs (k + 1) (by rw [hl]; exact hk))) hz)

/-- E6's displayed fundamental Gram is symmetric. -/
theorem gramSymRead_E6 : gramSymRead fundE6 := by decide +kernel

/-- E6's transposed Cartan solve has the square frame, nonzero
leading minors and positive determinant required by natural fold
cofactors. The leading determinants are read by descent. -/
theorem cartanSolve_E6 : elim.sqAt tableE6.cartan tableE6.rank
    ∧ (∀ k, k < tableE6.rank →
      ¬ (elim.leadMinor (elim.transposeM tableE6.cartan) (k + 1)).oneValue BPair.unit)
    ∧ BPair.unit < elim.detD (elim.transposeM tableE6.cartan) := by
  have hs : elim.rowsLen (elim.transposeM tableE6.cartan).length (elim.transposeM tableE6.cartan) := by decide +kernel
  have hl : (elim.transposeM tableE6.cartan).length = tableE6.rank := by decide +kernel
  have hm : ∀ k, k < tableE6.rank →
      ¬ (elim.detD (((elim.transposeM tableE6.cartan).take (k + 1)).map (fun r => r.take (k + 1)))).oneValue BPair.unit := by
    decide +kernel
  refine ⟨by decide +kernel, ?_, by decide +kernel⟩
  intro k hk hz
  exact hm k hk (BPair.oneValue_trans (BPair.oneValue_symm
    (elim.leadMinor_detD _ hs (k + 1) (by rw [hl]; exact hk))) hz)

/-- E7's displayed fundamental Gram is symmetric. -/
theorem gramSymRead_E7 : gramSymRead fundE7 := by decide +kernel

/-- E7's transposed Cartan solve has the square frame, nonzero
leading minors and positive determinant required by natural fold
cofactors. The leading determinants are read by descent. -/
theorem cartanSolve_E7 : elim.sqAt tableE7.cartan tableE7.rank
    ∧ (∀ k, k < tableE7.rank →
      ¬ (elim.leadMinor (elim.transposeM tableE7.cartan) (k + 1)).oneValue BPair.unit)
    ∧ BPair.unit < elim.detD (elim.transposeM tableE7.cartan) := by
  have hs : elim.rowsLen (elim.transposeM tableE7.cartan).length (elim.transposeM tableE7.cartan) := by decide +kernel
  have hl : (elim.transposeM tableE7.cartan).length = tableE7.rank := by decide +kernel
  have hm : ∀ k, k < tableE7.rank →
      ¬ (elim.detD (((elim.transposeM tableE7.cartan).take (k + 1)).map (fun r => r.take (k + 1)))).oneValue BPair.unit := by
    decide +kernel
  refine ⟨by decide +kernel, ?_, by decide +kernel⟩
  intro k hk hz
  exact hm k hk (BPair.oneValue_trans (BPair.oneValue_symm
    (elim.leadMinor_detD _ hs (k + 1) (by rw [hl]; exact hk))) hz)

/-- E8's displayed fundamental Gram is symmetric. -/
theorem gramSymRead_E8 : gramSymRead fundE8 := by decide +kernel

/-- E8's transposed Cartan solve has the square frame, nonzero
leading minors and positive determinant required by natural fold
cofactors. The leading determinants are read by descent. -/
theorem cartanSolve_E8 : elim.sqAt tableE8.cartan tableE8.rank
    ∧ (∀ k, k < tableE8.rank →
      ¬ (elim.leadMinor (elim.transposeM tableE8.cartan) (k + 1)).oneValue BPair.unit)
    ∧ BPair.unit < elim.detD (elim.transposeM tableE8.cartan) := by
  have hs : elim.rowsLen (elim.transposeM tableE8.cartan).length (elim.transposeM tableE8.cartan) := by decide +kernel
  have hl : (elim.transposeM tableE8.cartan).length = tableE8.rank := by decide +kernel
  have hm : ∀ k, k < tableE8.rank →
      ¬ (elim.detD (((elim.transposeM tableE8.cartan).take (k + 1)).map (fun r => r.take (k + 1)))).oneValue BPair.unit := by
    decide +kernel
  refine ⟨by decide +kernel, ?_, by decide +kernel⟩
  intro k hk hz
  exact hm k hk (BPair.oneValue_trans (BPair.oneValue_symm
    (elim.leadMinor_detD _ hs (k + 1) (by rw [hl]; exact hk))) hz)


/-- G2's fundamental data have their stated shape. -/
theorem fundShape_G2 : fundShape tableG2 fundG2 := by decide +kernel

/-- G2's Gram reads the scaled length diagonal. -/
theorem gramRead_G2 : gramRead tableG2 fundG2 := by decide +kernel

/-- G2's simple positions read the one-key folds. -/
theorem simplePosRead_G2 : simplePosRead tableG2 fundG2 := by decide +kernel

/-- G2's simple matrices square to the identity. -/
theorem reflSquareRead_G2 : reflSquareRead tableG2 := by
  apply reflSquareRead_of_diagonal
  decide +kernel

/-- G2's positive-root permutations are involutions. -/
theorem permSquareRead_G2 : permSquareRead tableG2 fundG2 := by decide +kernel

/-- G2's positive-root permutations read the actual reflections. -/
theorem permImageRead_G2 : permImageRead tableG2 fundG2 := by decide +kernel

/-- G2's positive roots pair positively with rho. -/
theorem rhoDotRead_G2 : rhoDotRead tableG2 fundG2 := by decide +kernel

/-- G2's simple reflections preserve the displayed Gram. -/
theorem reflFormRead_G2 : reflFormRead tableG2 fundG2 := by decide +kernel


end sertables
