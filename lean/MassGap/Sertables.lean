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
module; the reflection permutation, the Weyl list and the
grading land with the alternant layer.  The defining tables enter
at their key encodings — the paired keys with `B`'s further null
key — the simple raisings and lowerings the displayed unit moves at
the form's twist (`B`'s short pair through the null key at the
cleared weights), each triple display one read (`tripleRead`, the
weighted transpose joined to the commutator displays at the coroot
diagonal), and the invariant count the stacked raisings' kernel
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
reflection join, the split certificates at `inertia`'s own reads
in the check module.
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

instance (t : Table) (s fam : List (List BPair)) :
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
          if n / 2 ^ k % 2 == 1 then mB 1 else pB 1)
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
          if n / 2 ^ k % 2 == 1 then mB 1 else pB 1))

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

instance (t : Table) (e : Nat) (rows : List (List Nat)) :
    Decidable (adjRead t e rows) :=
  inferInstanceAs (Decidable (_ = _))

/-- The θ-fold row: one adjugate row is the highest root's fold at
the fold key's multiple, the highest root the fundamental at that
key. -/
def thetaRowRead (t : Table) (e : Nat) (rows : List (List Nat))
    (k : Nat) : Prop :=
  (getAt [] rows k == t.thetaFold.map (fun c => e * c)) = true

instance (t : Table) (e : Nat) (rows : List (List Nat)) (k : Nat) :
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

/-- A member triple's display at one read: the pairing carries the
transpose (`Eᵀ W = W F`), the commutator reads the coroot diagonal
(`EF - FE = H`), and the diagonal returns the lowering
(`FH - HF = 2F`), the three entrywise one-value comparisons one
fold. -/
def tripleRead (W E F H : elim.Mat) : Prop :=
  ((if elim.matOneValue (elim.matMul (elim.transposeM E) W)
        (elim.matMul W F) then true else false)
    && (if elim.matOneValue
          (elim.matAdd (elim.matMul E F)
            (elim.matSwap (elim.matMul F E))) H
        then true else false)
    && (if elim.matOneValue
          (elim.matAdd (elim.matMul F H)
            (elim.matSwap (elim.matMul H F))) (elim.matAdd F F)
        then true else false)) = true

instance (W E F H : elim.Mat) : Decidable (tripleRead W E F H) :=
  inferInstanceAs (Decidable (_ = _))

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

instance (t : gentable.Table) (F : FundData) :
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

instance (t : gentable.Table) (G : elim.Mat) (s : Nat) :
    Decidable (gramReadG t G s) :=
  inferInstanceAs (Decidable (elim.matOneValue _ _))

/-- The Gram's defining read at the fundamental data, `gramReadG`
at the carried Gram and scale. -/
def gramRead (t : gentable.Table) (F : FundData) : Prop :=
  gramReadG t F.gram F.scale

instance (t : gentable.Table) (F : FundData) :
    Decidable (gramRead t F) :=
  inferInstanceAs (Decidable (elim.matOneValue _ _))

/-- A stated Gram's symmetry (`con:sertables`' form displays, the
symmetric pair read per content pair). -/
def gramSymReadG (G : elim.Mat) : Prop :=
  elim.matOneValue (elim.transposeM G) G

instance (G : elim.Mat) : Decidable (gramSymReadG G) :=
  inferInstanceAs (Decidable (elim.matOneValue _ _))

/-- The symmetry at the fundamental data, `gramSymReadG` at the
carried Gram. -/
def gramSymRead (F : FundData) : Prop :=
  gramSymReadG F.gram

instance (F : FundData) : Decidable (gramSymRead F) :=
  inferInstanceAs (Decidable (elim.matOneValue _ _))

/-- The simple positions' read: the positive list holds each simple
at its stated position, the one-key fold (`con:sertables`' positive
lists at their displayed folds). -/
def simplePosRead (t : gentable.Table) (F : FundData) : Prop :=
  ∀ i, i < t.rank →
    getAt [] t.posFolds (getAt 0 F.simplePos i)
      = (List.range t.rank).map (fun k => if k == i then 1 else 0)

instance (t : gentable.Table) (F : FundData) :
    Decidable (simplePosRead t F) :=
  inferInstanceAs (Decidable (∀ i, i < t.rank → _ = _))

/-- The involution read at the matrices: each reflection squares to
the identity, the table's own read (`con:sertables`: each letter an
involution, `s_i s_i μ = μ`). -/
def reflSquareRead (t : gentable.Table) : Prop :=
  ∀ i, i < t.rank →
    elim.matOneValue (elim.matMul (reflM t i) (reflM t i))
      (inertia.idMat t.rank)

instance (t : gentable.Table) : Decidable (reflSquareRead t) :=
  inferInstanceAs (Decidable (∀ i, i < t.rank →
    elim.matOneValue _ _))

/-- The involution read at the permutation data: each permutation of
the positive list is its own involution (`con:sertables`: each
letter an involution, read at the stated positions). -/
def permSquareRead (t : gentable.Table) (F : FundData) : Prop :=
  ∀ i, i < t.rank → ∀ j, j < t.posFolds.length →
    getAt 0 (getAt [] F.perms i)
      (getAt 0 (getAt [] F.perms i) j) = j

instance (t : gentable.Table) (F : FundData) :
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

instance (t : gentable.Table) (F : FundData) :
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

instance (t : gentable.Table) (F : FundData) :
    Decidable (permImageRead t F) :=
  inferInstanceAs (Decidable (∀ i, i < t.rank →
    (∀ j, j < t.posFolds.length → j ≠ _ → _ = _) ∧ _ = _))

/-- The `ρ`-dot read: every positive member's Gram pairing against
`ρ` is positive (`con:sertables`' regular reads, the `ρ`-fold's
members at positive root-fold dots). -/
def rhoDotRead (t : gentable.Table) (F : FundData) : Prop :=
  ∀ j, j < t.posFolds.length →
    BPair.unit < dotB F (posCorootV t j) (rhoV t)

instance (t : gentable.Table) (F : FundData) :
    Decidable (rhoDotRead t F) :=
  inferInstanceAs (Decidable (∀ j, j < t.posFolds.length →
    _ < _))

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

/-- The `B` coordinate display of a coroot vector: the doubled
suffix fold, the last key the last coroot read itself. -/
def coordsB (m : List BPair) : List BPair :=
  match m.reverse with
  | [] => []
  | a :: rest =>
    rest.foldl (fun acc x =>
      (x + x + ground.getAt BPair.unit acc 0) :: acc) [a]

/-- The `C` coordinate display: the plain suffix fold. -/
def coordsC (m : List BPair) : List BPair :=
  match m.reverse with
  | [] => []
  | a :: rest =>
    rest.foldl (fun acc x =>
      (x + ground.getAt BPair.unit acc 0) :: acc) [a]

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
    if n / 2 ^ q % 2 == 1 then x.swap else x)

/-- A sign vector's flip parity. -/
def flipParity (l n : Nat) : Bool :=
  ((List.range l).foldl (fun a q => a + n / 2 ^ q % 2) 0) % 2 == 1

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

instance (t : gentable.Table) (W : List (List BPair × Bool)) :
    Decidable (wShapeRead t W) :=
  inferInstanceAs (Decidable (∀ vp ∈ W, _ ∧ _ = _))

end sertables
