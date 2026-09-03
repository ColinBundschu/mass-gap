import MassGap.Ground
/-!
`con:places` — a shape is its column multiset, the occupancy family
over the lengths at the stated fundamental count (here the list's
own length): the row list is the derived display, `λ_i` the count of
columns of length at least `i`, the degree the box total.  The
shape's beta-set descends from `x_{d_f} = n_{d_f} + 1` by
`x_i = x_{i+1} + n_i + 1`, a set of `d_f` distinct positive
naturals; the unit shape's is the unit set `{1, …, d_f}`.  The
power's monomial tensors are the index lists; the content of a
monomial is the occupancy family over the letters, and the content
summand's basis is the monomial enumeration at a content.  A
permutation's inversion list counts the reversed place pairs, and
the swap grading is its parity (`parityOf`, a stated family's
count parity its side, `sideOf`), even and odd its two classes;
the graded sums of the column exhibit read the parity per
monomial.
The place permutations are the unit-content words (`perms`), at
the factorial count (`length_perms`, the arrangement count's
unit-content instance), the permuted display is `expo`, and a
permutation's cycles are the orbit walk at the place-count fuel
(`cycGo`, `cyclesOf`), packed by `cycles_pack` — the flattening
covers every place exactly once and each word is occupied,
bounded, closed under the assignment and its head's iterates
(`iterP`) — and carried across a relabeling by
`cyclesOf_transport`, whose relabeled wiring is again a member
(`transport_member`) and whose partner relabeling composes back to
the wiring (`transport_invol`), the enumeration itself distinct
(`perms_distinct`); a key's position in a stated listing is
`idxOf`, with its two roundtrips (`getAt_idxOf` the listing read
there, `idxOf_getAt` the distinct listing's entry naming its own
place, `idxOf_lt` the position's bound), and the relabeling's two
composition reads are the partner relabeled
(`invPerm_transport`) and the composite relabeled
(`expo_transport`); the
shape enumeration (`allShapes`) is complete at the width and
degree (`mem_allShapes`), sound (`allShapes_sound`), distinct
(`countOf_allShapes_le`), one member at the vacant degree
(`allShapes_zero`), the appended column's degree its snoc read
(`degree_snoc`).

The enumeration's coherence is the count equation
`countOf_monomialsAt` — the monomial list at a content holds
exactly the monomials of the content, once each, the count read at
the degree and the content — with `monomialsAt_distinct` its
corollary.  The inversion-list word clause is `word_count`, the
letter count the witness sum `L = c + 2w` at the returning count,
with the one-pair moves (`inversions_adjSwap_lt`/`_gt`) and the
grading flip (`parity_adjSwap`) beneath it, each read at the list
kit's own adjacent exchange `ground.adjSwap`; the transposition of
two places is the adjacent word's conjugation at the gap
(`swapPosG`), grading-odd at every gap (`parity_swapPosG`) with its
entry reads and `posOf`, the graded folds' pairing device.  The
descent is `sortWord` with its reads (`sortWord_reads`: the end
adjacent-sorted at `firstRev`'s unit read, the letter count the
inversion count, every letter interior), the sorted assignment is
one list (`sorted_eq_range`, the unit assignment at the
classification), the identity's words are even outright
(`word_identity`, `L = 2w` at the sorted assignment), and the swap
grading is additive over composition, two words concatenating
(`parity_comp` at `parityOf_add`).  The inverse permutation is
`invPerm`, the assignment flipped with its value at a letter the
witness place reading it: its counts the assignment's own
(`countOf_invPerm` over the count transport `countOf_comp`), the
composed pair the unit assignment (`invPerm_comp`), and its grading
the assignment's (`parity_invPerm`).  The beta-set's sorted display
enters as counts (`display`, `unitDisp` the unit shape's) with its
kit — the lengths, the entry read `(λ+u)_i = λ_i + (d-i)`, the
row list's weak descent (`rowList_le`) and its injectivity
(`rowList_inj`, the occupancies the consecutive gaps' own) — with
the shapes' composition by column union (`addS`, the occupancies'
sum) and its row read (`rowList_addS`, the rows adding key by key
at the one letter width) beside them — the arrangement count's
growth under a further box (`length_monomialsAt_le_bumpAt`, the
multinomial's ratio at or above one) their arithmetic read — and
the transposition
gains its map composition (`swapPair_map`) and the repeat's fix
(`swapPair_eq_of_getAt_eq`), the alternant identity tier's reads.
The expansion tier's
enumeration reads sit at the module's tail — the unit-content
enumeration's first-letter regrouping, the trailing unoccupied
key's drop, and the inversion count's head split at the tail's
member counts — `def:elim`'s determinant fold their consumer.
The enumeration kit beside them: the place pairs' double-fold read
(`pairsFold` at `pairsOf`), and the key box (`keyBox`,
the length-`d` keys at entries below the bound) with its counting
reads and the point collapses at an edit map's preimage
(`boxPick`, `boxPickZero`) — the alternant tier's convolution
their consumer.  The
single-key kit reads the reduced labels' rows: the repeated
family's split at a stated key (`replicate_split`) with the raise
there (`bumpAt_split`), one occupied key
over a vacant family (`sumNat_pointAt`, `rowList_pointAt` — the
rows that occupancy down to the key and vacant below), the scaled
family (`sumNat_scale`, `rowList_scale` — the rows are column
totals and the totals scale), and the deepest key's raise
(`rowList_full`, a full column moving every row by one).  The
count-family calculus the module reads — the totals with their
raise, lowering and reversal reads, the key range's counts and
splits, the family folds over the key range — is `ground`'s kit,
`def:ground`'s count carrier.
-/

namespace places
open ground

/-- A shape: the column multiset as the occupancy family over the
lengths `1..d_f`, total over the stated key list, the fundamental
count the list's length. -/
abbrev Shape := List Nat


/-- The row list, the derived display: `λ_i` the count of columns
of length at least `i`. -/
def rowList : Shape → List Nat
  | [] => []
  | n :: t => (n + sumNat t) :: rowList t

/-- The degree, the box total. -/
def degree (s : Shape) : Nat := sumNat (rowList s)

/-- The beta-set, descending from `x_{d_f} = n_{d_f} + 1` by
`x_i = x_{i+1} + n_i + 1`: `d_f` distinct positive naturals with
sorted display. -/
def betaSet : Shape → List Pos
  | [] => []
  | n :: t =>
    match betaSet t with
    | [] => [posOfSucc n]
    | x :: xs => (x + posOfSucc n) :: x :: xs

/-- The unit shape's beta-set, the unit set `{1, …, d_f}` at the
sorted display. -/
def unitSet (d : Nat) : List Pos := betaSet (List.replicate d 0)

/-- The beta-set's sorted display as counts, `(λ + u)_i = λ_i +
(d - i)`: the row list against the unit set's display, the rows'
read `x_i = λ_i + g + 1` at the join `i + g = d_f`
(`con:places`). -/
def display (s : Shape) : List Nat :=
  List.zipWith (fun l u => l + u) (rowList s)
    ((List.range s.length).map (fun i => s.length - i))

/-- The unit set's sorted display as counts, the unit shape's. -/
def unitDisp (d : Nat) : List Nat := display (List.replicate d 0)

/-- A permutation's inversion count: the reversed place pairs, one
count over the pairs. -/
def inversions : List Nat → Nat
  | [] => 0
  | a :: t => ground.countBelow a t + inversions t

/-- A count's parity, the successor flip: `true` at the odd
class. -/
def parityOf : Nat → Bool
  | 0 => false
  | n + 1 => !(parityOf n)

/-- A family's side, its count's parity (`thm:assembly`'s and
`cor:weyldim`'s subset folds: the `S`-term's side is `S`'s
count). -/
def sideOf {α : Type} (S : List α) : Bool := parityOf S.length

/-- The swap grading: `true` at the odd class. -/
def parity (m : List Nat) : Bool := parityOf (inversions m)

/-- The content of a monomial tensor at a stated letter count: the
occupancy family over the letters, the member count's own read
(`ground.countOf`). -/
def content (d : Nat) (m : List Nat) : List Nat :=
  (List.range d).map (fun i => ground.countOf i m)

private def monGo : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | fuel + 1, mu =>
    if sumNat mu = 0 then [[]]
    else
      (List.range mu.length).flatMap (fun i =>
        if 0 < getAt 0 mu i then
          (monGo fuel (dipAt i mu)).map (fun m => i :: m)
        else [])

/-- The content summand's basis: the monomial tensors at a stated
content, one index list per arrangement. -/
def monomialsAt (mu : List Nat) : List (List Nat) :=
  monGo (sumNat mu) mu

/-- The power's whole monomial basis at a letter count and a
degree. -/
def allMon (d k : Nat) : List (List Nat) :=
  ground.prodLists (List.replicate k (List.range d))

/-- A member's position in a stated list, the list's own count
beyond it. -/
def idxOf {α : Type} [BEq α] (m : α) : List α → Nat :=
  ground.posBy (fun a b => a == b) m

private def prodNat : List Nat → Nat
  | [] => 1
  | a :: t => a * prodNat t

/-- The arrangement count at a content, the multinomial read. -/
def countMon (mu : List Nat) : Nat :=
  factorial (sumNat mu) / prodNat (mu.map factorial)

/-- A monomial's position in its content's enumeration, the
arithmetic rank at the letters-ascending order (`monomialsAt`'s
own): the earlier-lettered arrangements counted per place. -/
def rankOf : List Nat → List Nat → Nat
  | [], _ => 0
  | a :: m, mu =>
    (List.range a).foldl (fun acc b =>
      if 0 < getAt 0 mu b then acc + countMon (dipAt b mu) else acc) 0
      + rankOf m (dipAt a mu)

/-- The contents at a letter count and a degree: the occupancy
families over the letters at the stated box total, one member per
family. -/
def allContents : Nat → Nat → List (List Nat)
  | 0, 0 => [[]]
  | 0, _ + 1 => []
  | d + 1, k => (List.range (k + 1)).flatMap (fun j =>
      (allContents d (k - j)).map (fun m => j :: m))

/-- The shapes at a fundamental count and a box total: the column
multisets over the lengths at the stated degree, one member per
family, the last length's occupancy appended per split. -/
def allShapes : Nat → Nat → List Shape
  | 0, 0 => [[]]
  | 0, _ + 1 => []
  | d + 1, k => (List.range (k + 1)).flatMap (fun j =>
      if j * (d + 1) ≤ k then
        (allShapes d (k - j * (d + 1))).map (fun s => s ++ [j])
      else [])

/-! The enumeration's coherence: the monomial list at a content
holds exactly the monomials of that content, once each — the count
equation `countOf_monomialsAt` at the degree and content reads,
`monomialsAt_distinct` its corollary. -/

private theorem foldRange_single (F : Nat → Nat) (a : Nat)
    (hoff : ∀ i, i ≠ a → F i = 0) (d : Nat) :
    ground.famFold Nat.add 0 F (List.range d)
      = if a < d then F a else 0 := by
  by_cases h : a < d
  · rw [if_pos h]
    exact ground.famFold_pick_of F a (List.range d)
      (ground.countOf_range_one h) (fun y _ hy => hoff y hy)
  · rw [if_neg h]
    exact ground.famFold_null_ov ground.natFoldLaws F (List.range d)
      (fun x hx => hoff x (fun he => h (he ▸ ground.ltOfMem hx)))

private theorem sumNat_indicator (a d : Nat) :
    sumNat ((List.range d).map (fun i => if i = a then 1 else 0))
      = if a < d then 1 else 0 :=
  (ground.sumMap (fun i => if i = a then 1 else 0)
      (List.range d)).trans
    ((ground.famFold_indicatorFlip a (List.range d)).trans
      (ground.countOf_range a d))

private theorem sumNat_content_le (d : Nat) :
    ∀ m : List Nat, sumNat (content d m) ≤ m.length
  | [] => by
    have hz : ∀ l : List Nat,
        sumNat (l.map (fun i =>
          ground.countOf i ([] : List Nat))) = 0 := by
      intro l
      induction l with
      | nil => rfl
      | cons a t ih =>
        show ground.countOf a [] + sumNat (t.map _) = 0
        rw [ih]
        rfl
    show sumNat ((List.range d).map (fun i =>
        ground.countOf i ([] : List Nat))) ≤ 0
    rw [hz (List.range d)]
    exact Nat.le_refl 0
  | a :: m => by
    show sumNat ((List.range d).map (fun i =>
        ground.countOf i (a :: m))) ≤ m.length + 1
    rw [ground.map_congr_all (fun i => ground.countOf i (a :: m))
        (fun i => (if i = a then 1 else 0) + ground.countOf i m)
        (fun i => ground.countOf_cons i a m) (List.range d),
      sumNat_map_add, sumNat_indicator a d]
    by_cases h : a < d
    · rw [if_pos h, Nat.add_comm 1 _]
      exact Nat.add_le_add (sumNat_content_le d m) (Nat.le_refl 1)
    · rw [if_neg h, Nat.zero_add]
      exact Nat.le_trans (sumNat_content_le d m) (Nat.le_succ m.length)

/-! The display kit: the row list's length and weak descent, the
display's length and entry reads — the sorted-display vocabulary
the alternant identity's statement tier reads. -/

/-- The row list's length is the shape's, the matched key lists. -/
theorem length_rowList : ∀ s : Shape, (rowList s).length = s.length
  | [] => rfl
  | _ :: t => by
    show (rowList t).length + 1 = t.length + 1
    rw [length_rowList t]

/-- The row list's head is the occupancy total, the first row
counting every column. -/
theorem rowList_head : ∀ s : Shape, 0 < s.length →
    ground.getAt 0 (rowList s) 0 = ground.sumNat s
  | [], h => absurd h (Nat.lt_irrefl 0)
  | _ :: _, _ => rfl


/-- The row list's consecutive gap is the shape's own occupancy. -/
theorem rowList_gap : ∀ (s : Shape) (j : Nat), j < s.length →
    ground.getAt 0 (rowList s) j
      = ground.getAt 0 s j + ground.getAt 0 (rowList s) (j + 1)
  | [], j, hj => absurd hj (Nat.not_lt_zero j)
  | n :: t, 0, _ => by
    show n + sumNat t = n + ground.getAt 0 (rowList t) 0
    match t with
    | [] => rfl
    | _ :: _ => rfl
  | _ :: t, j + 1, hj => by
    show ground.getAt 0 (rowList t) j
      = ground.getAt 0 t j + ground.getAt 0 (rowList t) (j + 1)
    exact rowList_gap t j (Nat.lt_of_succ_lt_succ hj)

/-- The row list reads the shape back: two shapes at one row list
are one shape, the occupancies the consecutive gaps' own. -/
theorem rowList_inj : ∀ s t : Shape, rowList s = rowList t → s = t
  | [], [], _ => rfl
  | [], b :: v, h =>
    nomatch (show ([] : List Nat) = (b + sumNat v) :: rowList v from h)
  | a :: u, [], h =>
    nomatch (show (a + sumNat u) :: rowList u = [] from h)
  | a :: u, b :: v, h => by
    have hh : a + sumNat u = b + sumNat v := (List.cons.inj h).1
    have hu : u = v := rowList_inj u v (List.cons.inj h).2
    rw [hu] at hh ⊢
    exact congrArg (fun n => n :: v) (addCancelR (sumNat v) hh)

/-- The display's length is the shape's. -/
theorem length_display (s : Shape) : (display s).length = s.length := by
  show (List.zipWith (fun l u => l + u) (rowList s)
      ((List.range s.length).map (fun i => s.length - i))).length
    = s.length
  rw [ground.length_zipWith _ _ _ s.length (length_rowList s)
      (ground.length_mapRange _ _)]


/-- The unit display's length is the letter count. -/
theorem length_unitDisp (d : Nat) : (unitDisp d).length = d := by
  show (display (List.replicate d 0)).length = d
  rw [length_display, ground.length_replicate 0]
/-- The display's entry read: the row against the unit display's
gap, `(λ + u)_i = λ_i + (d - i)`. -/
theorem getAt_display (s : Shape) (i : Nat) (hi : i < s.length) :
    ground.getAt 0 (display s) i
      = ground.getAt 0 (rowList s) i + (s.length - i) := by
  show ground.getAt 0 (List.zipWith (fun l u => l + u) (rowList s)
      ((List.range s.length).map (fun i => s.length - i))) i = _
  rw [ground.getAt_zipWith 0 0 0 _ _ _ i (by rw [length_rowList]; exact hi)
      (by rw [ground.length_mapRange]; exact hi),
    getAt_map_range 0 (fun i => s.length - i) s.length i, if_pos hi]

/-- The row list descends weakly: a deeper row at or below its
predecessor, the sorted rows' read. -/
theorem rowList_le : ∀ (s : Shape) (i : Nat), i + 1 < s.length →
    ground.getAt 0 (rowList s) (i + 1) ≤ ground.getAt 0 (rowList s) i
  | [], i, h => absurd h (Nat.not_lt_zero _)
  | _ :: t, i + 1, h => by
    show ground.getAt 0 (rowList t) (i + 1)
      ≤ ground.getAt 0 (rowList t) i
    exact rowList_le t i (Nat.lt_of_succ_lt_succ h)
  | n :: t, 0, h => by
    have ht : 0 < t.length := Nat.lt_of_succ_lt_succ h
    show ground.getAt 0 (rowList t) 0 ≤ n + sumNat t
    cases t with
    | nil => exact absurd ht (Nat.lt_irrefl 0)
    | cons m t' =>
      show m + sumNat t' ≤ n + (m + sumNat t')
      exact Nat.le_add_left _ n

/-- The display descends strictly: the weakly descending rows
against the unit display's strict steps. -/
theorem display_desc (lam : Shape) :
    ∀ i, i + 1 < lam.length →
      ground.getAt 0 (display lam) (i + 1)
        < ground.getAt 0 (display lam) i := by
  intro i hi1
  have hi : i < lam.length := Nat.lt_of_succ_lt hi1
  have h1 : (i + 1) + (lam.length - (i + 1)) = lam.length :=
    ground.natAddSubCancel (Nat.le_of_lt hi1)
  have h2 : i + (lam.length - i) = lam.length :=
    ground.natAddSubCancel (Nat.le_of_lt hi)
  have h3 : i + (lam.length - i)
      = i + (1 + (lam.length - (i + 1))) := by
    rw [h2, ← Nat.add_assoc i 1 (lam.length - (i + 1))]
    exact h1.symm
  have hLsub : lam.length - i = 1 + (lam.length - (i + 1)) :=
    ground.addCancelL i h3
  rw [getAt_display lam (i + 1) hi1, getAt_display lam i hi,
    hLsub]
  refine Nat.lt_of_lt_of_le
    (Nat.add_lt_add_left (show lam.length - (i + 1)
        < 1 + (lam.length - (i + 1)) by
      rw [Nat.add_comm 1 (lam.length - (i + 1))]
      exact Nat.lt_succ_self _)
      (ground.getAt 0 (rowList lam) (i + 1)))
    (Nat.add_le_add_right (rowList_le lam i hi1)
      (1 + (lam.length - (i + 1))))

/-- The display reads the shape back: two shapes at one display are
one shape. -/
theorem display_inj : ∀ s t : Shape, display s = display t → s = t := by
  intro s t h
  have hlen : s.length = t.length := by
    rw [← length_display s, ← length_display t, h]
  refine rowList_inj s t
    (ground.getAt_ext 0 (rowList s) (rowList t) ?_ ?_)
  · rw [length_rowList, length_rowList, hlen]
  · intro i hi
    have his : i < s.length := by
      rw [← length_rowList s]
      exact hi
    have hit : i < t.length := by
      rw [← hlen]
      exact his
    have hd : ground.getAt 0 (display s) i
        = ground.getAt 0 (display t) i := by rw [h]
    rw [getAt_display s i his, getAt_display t i hit, hlen] at hd
    exact ground.addCancelR (t.length - i) hd

/-- The shapes' composition by column union, the occupancies'
sum (`con:places`). -/
def addS (a b : Shape) : Shape := List.zipWith (fun x y => x + y) a b

private theorem sumNat_addS : ∀ (a b : Shape), b.length = a.length →
    sumNat (addS a b) = sumNat a + sumNat b
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | x :: u, y :: v, h => by
    show x + y + sumNat (addS u v) = x + sumNat u + (y + sumNat v)
    rw [sumNat_addS u v (Nat.succ.inj h),
      Nat.add_add_add_comm x y (sumNat u) (sumNat v)]

/-- The row lists adding over the column union (`con:places`): the
composed shape's rows the two rows' sum, key by key.  The one
letter width is load-bearing with its committed refusals: the
truncating fold off it withdraws an occupied tail on either
side. -/
theorem rowList_addS : ∀ (a b : Shape), b.length = a.length →
    rowList (addS a b)
      = List.zipWith (fun x y => x + y) (rowList a) (rowList b)
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | x :: u, y :: v, h => by
    show (x + y + sumNat (addS u v)) :: rowList (addS u v)
      = (x + sumNat u + (y + sumNat v))
        :: List.zipWith (fun x y => x + y) (rowList u) (rowList v)
    rw [rowList_addS u v (Nat.succ.inj h),
      sumNat_addS u v (Nat.succ.inj h),
      Nat.add_add_add_comm x y (sumNat u) (sumNat v)]

/-- A content family reads its alphabet's own length. -/
theorem content_length (d : Nat) (m : List Nat) :
    (content d m).length = d :=
  ground.length_mapRange _ d

private theorem getAt_content (d : Nat) (m : List Nat) (i : Nat) :
    ground.getAt 0 (content d m) i
      = if i < d then ground.countOf i m else 0 :=
  getAt_map_range 0 (fun i => ground.countOf i m) d i


private theorem countOf_monGo : ∀ (fuel : Nat) (mu m : List Nat),
    sumNat mu = fuel →
    ground.countOf m (monGo fuel mu)
      = if m.length = fuel ∧ content mu.length m = mu then 1 else 0
  | 0, mu, m, hsum => by
    match m with
    | [] =>
      have hc : content mu.length ([] : List Nat) = mu := by
        refine ground.getAt_ext 0 _ _ ?_ ?_
        · rw [content_length]
        · intro i hi
          rw [content_length] at hi
          rw [getAt_content, if_pos hi,
            getAt_zero_of_sum mu hsum i]
          rfl
      show (if ([] : List Nat) = ([] : List Nat) then 1 else 0)
          + ground.countOf ([] : List Nat) ([] : List (List Nat)) = _
      rw [if_pos rfl, if_pos ⟨rfl, hc⟩]
      rfl
    | a :: m' =>
      show (if a :: m' = ([] : List Nat) then 1 else 0)
          + ground.countOf (a :: m') ([] : List (List Nat)) = _
      rw [if_neg (fun hc : a :: m' = ([] : List Nat) => nomatch hc),
        if_neg (fun hc : (a :: m').length = 0 ∧ _ =>
          Nat.noConfusion hc.1)]
      rfl
  | k + 1, mu, m, hsum => by
    have hguard : ¬ sumNat mu = 0 := by
      rw [hsum]
      exact fun hb => Nat.noConfusion hb
    show ground.countOf m
        (if sumNat mu = 0 then [[]]
         else (List.range mu.length).flatMap (fun i =>
           if 0 < ground.getAt 0 mu i then
             (monGo k (dipAt i mu)).map (fun t => i :: t)
           else [])) = _
    rw [if_neg hguard, ground.countOf_flatMap]
    match m with
    | [] =>
      have hz : ∀ i, ground.countOf ([] : List Nat)
          (if 0 < ground.getAt 0 mu i then
            (monGo k (dipAt i mu)).map (fun t => i :: t)
           else []) = 0 := by
        intro i
        by_cases hi : 0 < ground.getAt 0 mu i
        · rw [if_pos hi, ground.countOf_nil_consMap]
        · rw [if_neg hi]
          rfl
      rw [ground.famFold_zero _ hz (List.range mu.length),
        if_neg (fun hc : ([] : List Nat).length = k + 1 ∧ _ =>
          Nat.noConfusion hc.1)]
    | a :: m' =>
      have hoff : ∀ i, i ≠ a → ground.countOf (a :: m')
          (if 0 < ground.getAt 0 mu i then
            (monGo k (dipAt i mu)).map (fun t => i :: t)
           else []) = 0 := by
        intro i hia
        by_cases hi : 0 < ground.getAt 0 mu i
        · rw [if_pos hi, ground.countOf_consMap,
            if_neg (fun he : a = i => hia he.symm)]
        · rw [if_neg hi]
          rfl
      rw [foldRange_single _ a hoff mu.length]
      by_cases ha : a < mu.length
      · rw [if_pos ha]
        by_cases hocc : 0 < ground.getAt 0 mu a
        · rw [if_pos hocc, ground.countOf_consMap, if_pos rfl,
            countOf_monGo k (dipAt a mu) m' (by
              have hs := sumNat_dipAt a mu hocc
              rw [hsum] at hs
              exact Nat.succ.inj hs)]
          by_cases hc1 : m'.length = k
              ∧ content (dipAt a mu).length m' = dipAt a mu
          · have hcd : content mu.length m' = dipAt a mu := by
              have h2 := hc1.2
              rw [(ground.length_dipAt a mu)] at h2
              exact h2
            have hcont : content mu.length (a :: m') = mu := by
              refine ground.getAt_ext 0 _ _ ?_ ?_
              · rw [content_length]
              · intro i hi
                rw [content_length] at hi
                rw [getAt_content, if_pos hi]
                by_cases hia : i = a
                · rw [hia, ground.countOf_head a m',
                    show ground.countOf a m'
                        = ground.getAt 0 (dipAt a mu) a from by
                      rw [hcd.symm, getAt_content, if_pos ha],
                    ground.getAt_dipAt a mu]
                  exact Nat.succ_pred_eq_of_pos hocc
                · rw [ground.countOf_head_ne hia m',
                    show ground.countOf i m'
                        = ground.getAt 0 (dipAt a mu) i from by
                      rw [hcd.symm, getAt_content, if_pos hi],
                    ground.getAt_dipAt_ne a mu i hia]
            rw [if_pos hc1, if_pos ⟨congrArg Nat.succ hc1.1, hcont⟩]
          · rw [if_neg hc1, if_neg (fun hc2 :
                (a :: m').length = k + 1
                  ∧ content mu.length (a :: m') = mu =>
              hc1 ⟨Nat.succ.inj hc2.1, by
                rw [(ground.length_dipAt a mu)]
                refine ground.getAt_ext 0 _ _ ?_ ?_
                · rw [content_length, (ground.length_dipAt a mu)]
                · intro i hi
                  rw [content_length] at hi
                  rw [getAt_content, if_pos hi]
                  by_cases hia : i = a
                  · rw [hia, ground.getAt_dipAt a mu,
                      show ground.getAt 0 mu a
                          = ground.countOf a m' + 1 from by
                        rw [hc2.2.symm, getAt_content, if_pos ha,
                          ground.countOf_head a m']]
                    rfl
                  · rw [ground.getAt_dipAt_ne a mu i hia,
                      show ground.getAt 0 mu i
                          = ground.countOf i (a :: m') from by
                        rw [hc2.2.symm, getAt_content, if_pos hi],
                      ground.countOf_head_ne hia m']⟩)]
        · rw [if_neg hocc,
            if_neg (fun hc2 : (a :: m').length = k + 1
                ∧ content mu.length (a :: m') = mu =>
              hocc (by
                rw [show ground.getAt 0 mu a
                    = ground.countOf a m' + 1 from by
                  rw [hc2.2.symm, getAt_content, if_pos ha,
                    ground.countOf_head a m']]
                exact Nat.succ_pos _))]
          rfl
      · rw [if_neg ha,
          if_neg (fun hc2 : (a :: m').length = k + 1
              ∧ content mu.length (a :: m') = mu =>
            have h1 : sumNat mu ≤ m'.length := by
              rw [hc2.2.symm]
              show sumNat ((List.range mu.length).map (fun i =>
                  ground.countOf i (a :: m')))
                ≤ m'.length
              rw [ground.map_congr_all
                  (fun i => ground.countOf i (a :: m'))
                  (fun i =>
                    (if i = a then 1 else 0) + ground.countOf i m')
                  (fun i => ground.countOf_cons i a m')
                  (List.range mu.length),
                sumNat_map_add, sumNat_indicator a mu.length,
                if_neg ha, Nat.zero_add]
              exact sumNat_content_le mu.length m'
            have h2 : m'.length + 1 = sumNat mu :=
              Eq.trans hc2.1 hsum.symm
            absurd (show m'.length + 1 ≤ m'.length from by
              rw [h2]; exact h1) (Nat.not_succ_le_self m'.length))]

/-- The enumeration's coherence: the monomial list at a content
holds exactly the monomials of the content, once each, the count
read at the degree and the content. -/
theorem countOf_monomialsAt (mu m : List Nat) :
    ground.countOf m (monomialsAt mu)
      = if m.length = sumNat mu ∧ content mu.length m = mu then 1
        else 0 :=
  countOf_monGo (sumNat mu) mu m rfl

/-- The enumeration is distinct, every monomial's count at most
one. -/
theorem monomialsAt_distinct (mu : List Nat) :
    ground.distinctList (monomialsAt mu) := by
  intro m _
  rw [countOf_monomialsAt]
  by_cases h : m.length = sumNat mu ∧ content mu.length m = mu
  · rw [if_pos h]
    exact Nat.le_refl 1
  · rw [if_neg h]
    exact Nat.le_succ 0

/-! The inversion-list word clause (`con:places`): composing with an
adjacent transposition moves the inversion list by exactly one pair
— the adjacent pair's read flips, the pairs meeting the two places
exchange theirs — so along a word the letter count is the witness
sum `L = c + 2w`, `c` the end's inversion count against the start's
and `w` the count of letters returning a pair (`word_count`): every
word for a permutation shares the list's parity, one class per
permutation. -/


private theorem countBelow_adjSwap (x : Nat) : ∀ (k : Nat)
    (m : List Nat),
    ground.countBelow x (adjSwap k m) = ground.countBelow x m
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, [_] => rfl
  | 0, a :: b :: t => by
    show ground.countBelow x (b :: a :: t)
      = ground.countBelow x (a :: b :: t)
    rw [ground.countBelow_cons x b (a :: t), ground.countBelow_cons x a t,
      ground.countBelow_cons x a (b :: t), ground.countBelow_cons x b t,
      ← Nat.add_assoc, ← Nat.add_assoc,
      Nat.add_comm (if b < x then 1 else 0) (if a < x then 1 else 0)]
  | k + 1, a :: t => by
    show ground.countBelow x (a :: adjSwap k t)
      = ground.countBelow x (a :: t)
    rw [ground.countBelow_cons, ground.countBelow_cons,
      countBelow_adjSwap x k t]

/-- The below-count at a strictly monotone letter map is the
count at the source letters. -/
private theorem countBelow_map (f : Nat → Nat) (a : Nat) :
    ∀ t : List Nat,
      (∀ b, 0 < ground.countOf b t → (b < a → f b < f a)) →
      (∀ b, 0 < ground.countOf b t → (f b < f a → b < a)) →
      ground.countBelow (f a) (t.map f) = ground.countBelow a t
  | [], _, _ => rfl
  | b :: t, hup, hdn => by
    show ground.countBelow (f a) (f b :: t.map f)
      = ground.countBelow a (b :: t)
    rw [ground.countBelow_cons, ground.countBelow_cons,
      countBelow_map f a t
      (fun c hc => hup c (Nat.lt_of_lt_of_le hc (Nat.le_add_left _ _)))
      (fun c hc => hdn c (Nat.lt_of_lt_of_le hc (Nat.le_add_left _ _)))]
    by_cases hba : b < a
    · rw [if_pos (hup b (by
          rw [ground.countOf_head]; exact Nat.succ_pos _) hba),
        if_pos hba]
    · rw [if_neg (fun hf => hba (hdn b (by
          rw [ground.countOf_head]; exact Nat.succ_pos _) hf)),
        if_neg hba]

/-- The inversion count at a strictly monotone letter map is the
source's own: every place pair's comparison is preserved, so the
grading reads across the map. -/
theorem inversions_map (f : Nat → Nat) :
    ∀ t : List Nat,
      (∀ a, 0 < ground.countOf a t → ∀ b, 0 < ground.countOf b t →
        (a < b → f a < f b) ∧ (f a < f b → a < b)) →
      inversions (t.map f) = inversions t
  | [], _ => rfl
  | a :: t, h => by
    show ground.countBelow (f a) (t.map f) + inversions (t.map f)
      = ground.countBelow a t + inversions t
    have hmem : ∀ c, 0 < ground.countOf c t →
        0 < ground.countOf c (a :: t) := fun c hc =>
      Nat.lt_of_lt_of_le hc (Nat.le_add_left _ _)
    have hah : 0 < ground.countOf a (a :: t) := by
      rw [ground.countOf_head]; exact Nat.succ_pos _
    rw [countBelow_map f a t
        (fun b hb hba => (h b (hmem b hb) a hah).1 hba)
        (fun b hb hfb => (h b (hmem b hb) a hah).2 hfb),
      inversions_map f t (fun c hc d hd =>
        h c (hmem c hc) d (hmem d hd))]

/-- The move at a strictly sorted adjacent pair: one pair enters
the inversion list, the further pairs exchanging theirs. -/
theorem inversions_adjSwap_lt : ∀ (k : Nat) (m : List Nat),
    k + 1 < m.length →
    ground.getAt 0 m k < ground.getAt 0 m (k + 1) →
    inversions (adjSwap k m) = inversions m + 1
  | 0, [], hk, _ => absurd hk (Nat.not_lt_zero _)
  | _ + 1, [], hk, _ => absurd hk (Nat.not_lt_zero _)
  | 0, [_], hk, _ => absurd hk (Nat.lt_irrefl 1)
  | 0, a :: b :: t, _, hab => by
    have hab' : a < b := hab
    show ground.countBelow b (a :: t)
        + (ground.countBelow a t + inversions t)
      = ground.countBelow a (b :: t)
        + (ground.countBelow b t + inversions t) + 1
    rw [ground.countBelow_cons, ground.countBelow_cons,
      if_pos hab', if_neg (Nat.lt_asymm hab'), Nat.zero_add,
      Nat.add_comm 1 (ground.countBelow b t),
      Nat.add_right_comm (ground.countBelow b t) 1
        (ground.countBelow a t + inversions t),
      Nat.add_left_comm (ground.countBelow b t) (ground.countBelow a t)
        (inversions t)]
  | k + 1, a :: t, hk, hab => by
    show ground.countBelow a (adjSwap k t) + inversions (adjSwap k t)
      = ground.countBelow a t + inversions t + 1
    rw [countBelow_adjSwap a k t,
      inversions_adjSwap_lt k t (Nat.lt_of_succ_lt_succ hk) hab,
      Nat.add_assoc]

/-- The move at a reversed adjacent pair: one pair returns, the
further pairs exchanging theirs. -/
theorem inversions_adjSwap_gt : ∀ (k : Nat) (m : List Nat),
    k + 1 < m.length →
    ground.getAt 0 m (k + 1) < ground.getAt 0 m k →
    inversions m = inversions (adjSwap k m) + 1
  | 0, [], hk, _ => absurd hk (Nat.not_lt_zero _)
  | _ + 1, [], hk, _ => absurd hk (Nat.not_lt_zero _)
  | 0, [_], hk, _ => absurd hk (Nat.lt_irrefl 1)
  | 0, a :: b :: t, _, hba => by
    have hba' : b < a := hba
    show ground.countBelow a (b :: t)
        + (ground.countBelow b t + inversions t)
      = ground.countBelow b (a :: t)
        + (ground.countBelow a t + inversions t) + 1
    rw [ground.countBelow_cons, ground.countBelow_cons,
      if_pos hba', if_neg (Nat.lt_asymm hba'), Nat.zero_add,
      Nat.add_comm 1 (ground.countBelow a t),
      Nat.add_right_comm (ground.countBelow a t) 1
        (ground.countBelow b t + inversions t),
      Nat.add_left_comm (ground.countBelow a t) (ground.countBelow b t)
        (inversions t)]
  | k + 1, a :: t, hk, hba => by
    show ground.countBelow a t + inversions t
      = ground.countBelow a (adjSwap k t) + inversions (adjSwap k t) + 1
    rw [countBelow_adjSwap a k t,
      inversions_adjSwap_gt k t (Nat.lt_of_succ_lt_succ hk) hba,
      Nat.add_assoc]

/-- The adjacent move at unequal entries flips the swap grading. -/
theorem parity_adjSwap (k : Nat) (m : List Nat)
    (hk : k + 1 < m.length)
    (hne : ground.getAt 0 m k ≠ ground.getAt 0 m (k + 1)) :
    parity (adjSwap k m) = !(parity m) := by
  match Nat.lt_or_ge (ground.getAt 0 m k)
      (ground.getAt 0 m (k + 1)) with
  | .inl hab =>
    show parityOf (inversions (adjSwap k m))
      = !(parityOf (inversions m))
    rw [inversions_adjSwap_lt k m hk hab]
    rfl
  | .inr hge =>
    have hba : ground.getAt 0 m (k + 1) < ground.getAt 0 m k :=
      Nat.lt_of_le_of_ne hge (fun e => hne e.symm)
    show parityOf (inversions (adjSwap k m))
      = !(parityOf (inversions m))
    rw [inversions_adjSwap_gt k m hk hba]
    show parityOf (inversions (adjSwap k m))
      = !(!(parityOf (inversions (adjSwap k m))))
    exact (Bool.not_not (parityOf (inversions (adjSwap k m)))).symm


/-- A word's action: the letters' adjacent transpositions applied
in order. -/
def applyWord : List Nat → List Nat → List Nat
  | [], m => m
  | k :: w, m => applyWord w (adjSwap k m)

/-- The count of letters returning a pair along a word, the
reversed-pair read at each letter's own site. -/
def returns : List Nat → List Nat → Nat
  | [], _ => 0
  | k :: w, m =>
    (if ground.getAt 0 m (k + 1) < ground.getAt 0 m k then 1 else 0)
      + returns w (adjSwap k m)

/-- The letter count is the witness sum `L = c + 2w`: along a word
at a distinct family with every letter interior, the letter count
joins the start's inversion count to the end's at twice the
returning count — so every word for a permutation shares the
inversion list's parity, one class per permutation. -/
theorem word_count : ∀ (w m : List Nat),
    (∀ x, ground.countOf x m ≤ 1) →
    (∀ k, 0 < ground.countOf k w → k + 1 < m.length) →
    w.length + inversions m
      = inversions (applyWord w m) + 2 * returns w m
  | [], m, _, _ => by
    show 0 + inversions m = inversions m + 2 * 0
    rw [Nat.zero_add]
    rfl
  | k :: w, m, hdist, hlet => by
    have hk : k + 1 < m.length := hlet k (by
      rw [ground.countOf_head]
      exact Nat.succ_pos _)
    have hne : ground.getAt 0 m k ≠ ground.getAt 0 m (k + 1) :=
      getAt_ne_of_distinct hdist (Nat.lt_succ_self k) hk
    have hdist' : ∀ x, ground.countOf x (adjSwap k m) ≤ 1 :=
      fun x => by
        rw [countOf_adjSwap x k m]
        exact hdist x
    have hlet' : ∀ k', 0 < ground.countOf k' w →
        k' + 1 < (adjSwap k m).length := fun k' hk' => by
      rw [length_adjSwap]
      exact hlet k' (Nat.lt_of_lt_of_le hk' (Nat.le_add_left _ _))
    show w.length + 1 + inversions m
      = inversions (applyWord w (adjSwap k m))
        + 2 * ((if ground.getAt 0 m (k + 1) < ground.getAt 0 m k
            then 1 else 0) + returns w (adjSwap k m))
    match Nat.lt_or_ge (ground.getAt 0 m k)
        (ground.getAt 0 m (k + 1)) with
    | .inl hab =>
      rw [if_neg (Nat.lt_asymm hab), Nat.zero_add,
        Nat.add_assoc w.length 1 (inversions m),
        Nat.add_comm 1 (inversions m),
        ← inversions_adjSwap_lt k m hk hab]
      exact word_count w (adjSwap k m) hdist' hlet'
    | .inr hge =>
      have hba : ground.getAt 0 m (k + 1) < ground.getAt 0 m k :=
        Nat.lt_of_le_of_ne hge (fun e => hne e.symm)
      rw [if_pos hba, inversions_adjSwap_gt k m hk hba,
        Nat.add_assoc w.length 1 (inversions (adjSwap k m) + 1),
        Nat.add_comm 1 (inversions (adjSwap k m) + 1),
        Nat.add_assoc (inversions (adjSwap k m)) 1 1,
        ← Nat.add_assoc w.length (inversions (adjSwap k m)) (1 + 1),
        word_count w (adjSwap k m) hdist' hlet',
        Nat.left_distrib 2 1 (returns w (adjSwap k m)),
        Nat.add_assoc (inversions (applyWord w (adjSwap k m)))
          (2 * returns w (adjSwap k m)) (1 + 1),
        Nat.add_comm (2 * returns w (adjSwap k m)) (1 + 1)]

theorem parityOf_add_two_mul :
    ∀ (a b : Nat), parityOf (a + 2 * b) = parityOf a
  | _, 0 => rfl
  | a, b + 1 => by
    have hs : a + 2 * (b + 1) = a + 2 * b + 2 := by
      rw [Nat.left_distrib 2 b 1, ← Nat.add_assoc]
    rw [hs,
      show parityOf (a + 2 * b + 2)
          = !(!(parityOf (a + 2 * b))) from rfl,
      Bool.not_not]
    exact parityOf_add_two_mul a b

/-- Every word for a permutation shares the inversion list's
parity, one class per permutation: the word clause's grading
read. -/
theorem word_parity (w m : List Nat)
    (hdist : ∀ x, ground.countOf x m ≤ 1)
    (hlet : ∀ k, 0 < ground.countOf k w → k + 1 < m.length) :
    parityOf (w.length + inversions m) = parity (applyWord w m) := by
  rw [word_count w m hdist hlet]
  exact parityOf_add_two_mul (inversions (applyWord w m))
    (returns w m)

/-! The transposition of two places: the adjacent word's
conjugation at the gap, one letter at the base and two per further
place between the pair, one letter beyond an even family — the swap
grading flips at every transposition, the word clause's read. -/

/-- The transposition of the places `p` and `p + g + 1`: the
adjacent word's conjugation at the gap. -/
def swapPosG (p : Nat) : Nat → List Nat → List Nat
  | 0, m => adjSwap p m
  | g + 1, m =>
    adjSwap (p + g + 1) (swapPosG p g (adjSwap (p + g + 1) m))

theorem length_swapPosG (p : Nat) : ∀ (g : Nat) (m : List Nat),
    (swapPosG p g m).length = m.length
  | 0, m => length_adjSwap p m
  | g + 1, m => by
    show (adjSwap (p + g + 1)
        (swapPosG p g (adjSwap (p + g + 1) m))).length = m.length
    rw [length_adjSwap, length_swapPosG p g, length_adjSwap]

theorem countOf_swapPosG (x p : Nat) : ∀ (g : Nat) (m : List Nat),
    ground.countOf x (swapPosG p g m) = ground.countOf x m
  | 0, m => countOf_adjSwap x p m
  | g + 1, m => by
    show ground.countOf x (adjSwap (p + g + 1)
        (swapPosG p g (adjSwap (p + g + 1) m))) = ground.countOf x m
    rw [countOf_adjSwap, countOf_swapPosG x p g, countOf_adjSwap]

/-- The transposition flips the swap grading: one letter at the
base with two per further place, an odd family at every gap. -/
theorem parity_swapPosG : ∀ (g p : Nat) (m : List Nat),
    p + g + 2 ≤ m.length → (∀ x, ground.countOf x m ≤ 1) →
    parity (swapPosG p g m) = !(parity m)
  | 0, p, m, hb, hdist =>
    parity_adjSwap p m hb
      (getAt_ne_of_distinct hdist (Nat.lt_succ_self p) hb)
  | g + 1, p, m, hb, hdist => by
    have hk1 : p + g + 1 + 1 < m.length := hb
    have hdist1 : ∀ x, ground.countOf x (adjSwap (p + g + 1) m) ≤ 1 :=
      fun x => by rw [countOf_adjSwap]; exact hdist x
    have hb1 : p + g + 2 ≤ (adjSwap (p + g + 1) m).length := by
      rw [length_adjSwap]
      exact Nat.le_trans (Nat.le_succ _) hb
    have hdist2 : ∀ x, ground.countOf x
        (swapPosG p g (adjSwap (p + g + 1) m)) ≤ 1 :=
      fun x => by rw [countOf_swapPosG]; exact hdist1 x
    have hk2 : p + g + 1 + 1
        < (swapPosG p g (adjSwap (p + g + 1) m)).length := by
      rw [length_swapPosG, length_adjSwap]
      exact hb
    show parity (adjSwap (p + g + 1)
        (swapPosG p g (adjSwap (p + g + 1) m))) = !(parity m)
    rw [parity_adjSwap (p + g + 1) _ hk2
        (getAt_ne_of_distinct hdist2 (Nat.lt_succ_self _) hk2),
      parity_swapPosG g p (adjSwap (p + g + 1) m) hb1 hdist1,
      parity_adjSwap (p + g + 1) m hk1
        (getAt_ne_of_distinct hdist (Nat.lt_succ_self _) hk1),
      Bool.not_not]

/-- The transposition is an involution. -/
theorem swapPosG_swapPosG (p : Nat) : ∀ (g : Nat) (m : List Nat),
    swapPosG p g (swapPosG p g m) = m
  | 0, m => adjSwap_adjSwap p m
  | g + 1, m => by
    show adjSwap (p + g + 1) (swapPosG p g (adjSwap (p + g + 1)
        (adjSwap (p + g + 1)
          (swapPosG p g (adjSwap (p + g + 1) m))))) = m
    rw [adjSwap_adjSwap (p + g + 1), swapPosG_swapPosG p g,
      adjSwap_adjSwap (p + g + 1)]

private theorem ne_add_succ (p g : Nat) : p ≠ p + g + 1 :=
  Nat.ne_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right p g)
    (Nat.lt_succ_self (p + g)))

/-- The transposition's entry read at its first place. -/
theorem getAt_swapPosG_fst : ∀ (g p : Nat) (m : List Nat),
    p + g + 2 ≤ m.length →
    ground.getAt 0 (swapPosG p g m) p
      = ground.getAt 0 m (p + g + 1)
  | 0, p, m, hb => getAt_adjSwap_fst 0 p m hb
  | g + 1, p, m, hb => by
    have hK : p + g + 1 + 1 < m.length := hb
    have hb1 : p + g + 2 ≤ (adjSwap (p + g + 1) m).length := by
      rw [length_adjSwap]
      exact Nat.le_trans (Nat.le_succ _) hb
    show ground.getAt 0 (adjSwap (p + g + 1)
        (swapPosG p g (adjSwap (p + g + 1) m))) p
      = ground.getAt 0 m (p + (g + 1) + 1)
    rw [getAt_adjSwap_ne 0 (p + g + 1) _ p (ne_add_succ p g)
        (ne_add_succ p (g + 1)),
      getAt_swapPosG_fst g p (adjSwap (p + g + 1) m) hb1,
      getAt_adjSwap_fst 0 (p + g + 1) m hK]
    rfl

/-- The transposition's entry read at its second place. -/
theorem getAt_swapPosG_snd : ∀ (g p : Nat) (m : List Nat),
    p + g + 2 ≤ m.length →
    ground.getAt 0 (swapPosG p g m) (p + g + 1)
      = ground.getAt 0 m p
  | 0, p, m, hb => getAt_adjSwap_snd 0 p m hb
  | g + 1, p, m, hb => by
    have hK : p + g + 1 + 1 < m.length := hb
    have hb1 : p + g + 2 ≤ (adjSwap (p + g + 1) m).length := by
      rw [length_adjSwap]
      exact Nat.le_trans (Nat.le_succ _) hb
    have hk2 : p + g + 1 + 1
        < (swapPosG p g (adjSwap (p + g + 1) m)).length := by
      rw [length_swapPosG, length_adjSwap]
      exact hb
    show ground.getAt 0 (adjSwap (p + g + 1)
        (swapPosG p g (adjSwap (p + g + 1) m))) (p + g + 1 + 1)
      = ground.getAt 0 m p
    rw [getAt_adjSwap_snd 0 (p + g + 1) _ hk2,
      getAt_swapPosG_snd g p (adjSwap (p + g + 1) m) hb1,
      getAt_adjSwap_ne 0 (p + g + 1) m p (ne_add_succ p g)
        (ne_add_succ p (g + 1))]

/-- The transposition's entry read off its two places. -/
theorem getAt_swapPosG_ne : ∀ (g p : Nat) (m : List Nat) (i : Nat),
    p + g + 2 ≤ m.length → i ≠ p → i ≠ p + g + 1 →
    ground.getAt 0 (swapPosG p g m) i = ground.getAt 0 m i
  | 0, p, m, i, _, hp, hp1 => getAt_adjSwap_ne 0 p m i hp hp1
  | g + 1, p, m, i, hb, hp, hp1 => by
    have hK : p + g + 1 + 1 < m.length := hb
    have hb1 : p + g + 2 ≤ (adjSwap (p + g + 1) m).length := by
      rw [length_adjSwap]
      exact Nat.le_trans (Nat.le_succ _) hb
    have hk2 : p + g + 1 + 1
        < (swapPosG p g (adjSwap (p + g + 1) m)).length := by
      rw [length_swapPosG, length_adjSwap]
      exact hb
    show ground.getAt 0 (adjSwap (p + g + 1)
        (swapPosG p g (adjSwap (p + g + 1) m))) i
      = ground.getAt 0 m i
    by_cases hiK : i = p + g + 1
    · rw [hiK, getAt_adjSwap_fst 0 (p + g + 1) _ hk2,
        getAt_swapPosG_ne g p (adjSwap (p + g + 1) m) (p + g + 1 + 1)
          hb1
          (fun e => ne_add_succ p (g + 1) e.symm)
          ((Nat.ne_of_lt (Nat.lt_succ_self (p + g + 1))).symm),
        getAt_adjSwap_snd 0 (p + g + 1) m hK]
    · rw [getAt_adjSwap_ne 0 (p + g + 1) _ i hiK hp1,
        getAt_swapPosG_ne g p (adjSwap (p + g + 1) m) i hb1 hp hiK,
        getAt_adjSwap_ne 0 (p + g + 1) m i hiK hp1]

/-- A member's first place, the occupancy's own read. -/
def posOf (x : Nat) : List Nat → Nat :=
  ground.posBy (fun a b => decide (a = b)) x

theorem posOf_lt (x : Nat) (m : List Nat) (h : 0 < ground.countOf x m) :
    posOf x m < m.length :=
  ground.posBy_lt_of_hit _ x m
    ⟨x, ground.mem_of_countOf_pos x m h, decide_eq_true rfl⟩

theorem getAt_posOf (x : Nat) (m : List Nat) (h : 0 < ground.countOf x m) :
    ground.getAt 0 m (posOf x m) = x :=
  (of_decide_eq_true (show decide (x = ground.getAt 0 m (posOf x m)) = true from
    ground.getAt_posBy 0 (fun a b : Nat => decide (a = b)) x m
      ⟨x, ground.mem_of_countOf_pos x m h, decide_eq_true rfl⟩)).symm

/-- The position at a head: the head itself at the key, past it
otherwise. -/
theorem posOf_cons (x a : Nat) (t : List Nat) :
    posOf x (a :: t) = if x = a then 0 else posOf x t + 1 := by
  by_cases h : x = a
  · rw [if_pos h]
    exact ground.posBy_cons_hit _ x a t (decide_eq_true h)
  · rw [if_neg h]
    exact ground.posBy_cons_miss _ x a t (decide_eq_false h)


/-! The permutation-membership reads: the enumeration at the unit
occupancy is the distinct families over the letters, the count
equation's instance, with the symmetric transposition `swapPair`
and the position reads the graded folds' pairing data. -/

/-- Two occupied members at distinct values read distinct
positions. -/
theorem posOf_inj {p : List Nat} {x y : Nat}
    (hx : 0 < ground.countOf x p) (hy : 0 < ground.countOf y p)
    (hne : ¬ x = y) :
    ¬ posOf x p = posOf y p := fun he =>
  hne (by
    rw [← getAt_posOf x p hx, ← getAt_posOf y p hy, he])

/-- The vacant occupancy family's row list is its own. -/
theorem rowList_replicate_zero : ∀ n : Nat,
    rowList (List.replicate n 0) = List.replicate n 0
  | 0 => rfl
  | n + 1 => by
    show (0 + sumNat (List.replicate n 0))
        :: rowList (List.replicate n 0) = 0 :: List.replicate n 0
    rw [sumNat_replicate_zero n, Nat.zero_add 0,
      rowList_replicate_zero n]

/-- The vacant shape's degree is the sum's unit. -/
theorem degree_replicate_zero (n : Nat) :
    degree (List.replicate n 0) = 0 := by
  show ground.sumNat (rowList (List.replicate n 0)) = 0
  rw [rowList_replicate_zero n, ground.sumNat_replicate_zero n]

/-! The single-key kit: one occupied key over a vacant family, the
scaled family, and the deepest key's raise — the reduced labels'
row lists read through them. -/

/-- The repeated family splits at a stated key. -/
theorem replicate_split {α : Type} (a : α) : ∀ g n : Nat,
    List.replicate (g + (n + 1)) a
      = List.replicate g a ++ a :: List.replicate n a
  | 0, n => by
    show List.replicate (0 + n + 1) a = a :: List.replicate n a
    rw [Nat.zero_add n]
    rfl
  | g + 1, n => by
    show List.replicate (g + 1 + n + 1) a
      = a :: (List.replicate g a ++ a :: List.replicate n a)
    rw [← replicate_split a g n, Nat.add_right_comm g 1 n]
    rfl

/-- A raise at the vacant prefix's own count reads the split
family's entry. -/
theorem bumpAt_split : ∀ (g e : Nat) (t : List Nat),
    ground.bumpAt g (List.replicate g 0 ++ e :: t)
      = List.replicate g 0 ++ (e + 1) :: t
  | 0, _, _ => rfl
  | g + 1, e, t => by
    show (0 : Nat) :: ground.bumpAt g (List.replicate g 0 ++ e :: t)
      = 0 :: (List.replicate g 0 ++ (e + 1) :: t)
    rw [bumpAt_split g e t]

/-- One occupied key over a vacant family carries its own
occupancy. -/
theorem sumNat_pointAt : ∀ (g n e : Nat),
    sumNat (List.replicate g 0 ++ e :: List.replicate n 0) = e
  | 0, n, e => by
    show e + sumNat (List.replicate n 0) = e
    rw [sumNat_replicate_zero n, Nat.add_zero e]
  | g + 1, n, e => by
    show 0 + sumNat (List.replicate g 0 ++ e :: List.replicate n 0) = e
    rw [Nat.zero_add, sumNat_pointAt g n e]

/-- One occupied key over a vacant family: the rows read that key's
occupancy down to it and are vacant below. -/
theorem rowList_pointAt : ∀ (g n e : Nat),
    rowList (List.replicate g 0 ++ e :: List.replicate n 0)
      = List.replicate (g + 1) e ++ List.replicate n 0
  | 0, n, e => by
    show (e + sumNat (List.replicate n 0)) :: rowList (List.replicate n 0)
      = e :: List.replicate n 0
    rw [sumNat_replicate_zero n, Nat.add_zero e, rowList_replicate_zero n]
  | g + 1, n, e => by
    show (0 + sumNat (List.replicate g 0 ++ e :: List.replicate n 0))
        :: rowList (List.replicate g 0 ++ e :: List.replicate n 0)
      = e :: (List.replicate (g + 1) e ++ List.replicate n 0)
    rw [Nat.zero_add, sumNat_pointAt g n e, rowList_pointAt g n e]

/-- The scaled family's total scales with it. -/
private theorem sumNat_scale (m : Nat) : ∀ l : List Nat,
    sumNat (l.map (fun n => n * m)) = sumNat l * m
  | [] => by
    show (0 : Nat) = 0 * m
    rw [Nat.zero_mul m]
  | n :: t => by
    show n * m + sumNat (t.map (fun n => n * m)) = (n + sumNat t) * m
    rw [sumNat_scale m t, ground.mulAddR n (sumNat t) m]

/-- The scaled shape's rows are the rows scaled: each row is a
column total, and the totals scale. -/
theorem rowList_scale (m : Nat) : ∀ s : Shape,
    rowList (s.map (fun n => n * m))
      = (rowList s).map (fun n => n * m)
  | [] => rfl
  | n :: t => by
    show (n * m + sumNat (t.map (fun n => n * m)))
        :: rowList (t.map (fun n => n * m))
      = (n + sumNat t) * m :: (rowList t).map (fun n => n * m)
    rw [sumNat_scale m t, ground.mulAddR n (sumNat t) m, rowList_scale m t]

/-- The deepest key's raise lifts every row by one: a full column
moves each column total by one. -/
theorem rowList_full : ∀ s : Shape,
    rowList (ground.bumpAt (s.length - 1) s)
      = (rowList s).map (fun x => x + 1)
  | [] => rfl
  | [a] => rfl
  | a :: b :: t => by
    have hlen : (b :: t).length - 1 + 1 = (a :: b :: t).length - 1 := rfl
    have hb : 0 < (b :: t).length := Nat.succ_pos t.length
    have hlt : (b :: t).length - 1 < (b :: t).length :=
      ground.subOneLt hb
    rw [← hlen]
    show (a + sumNat (ground.bumpAt ((b :: t).length - 1) (b :: t)))
        :: rowList (ground.bumpAt ((b :: t).length - 1) (b :: t))
      = (a + sumNat (b :: t) + 1)
        :: (rowList (b :: t)).map (fun x => x + 1)
    rw [sumNat_bumpAt ((b :: t).length - 1) (b :: t) hlt,
      rowList_full (b :: t), ← Nat.add_assoc a (sumNat (b :: t)) 1]

/-- A full column moves every display member by one successor
(`con:places`). -/
theorem display_full (s : Shape) :
    display (ground.bumpAt (s.length - 1) s)
      = (display s).map (fun x => x + 1) := by
  have hlenB : (ground.bumpAt (s.length - 1) s).length = s.length :=
    ground.length_bumpAt (s.length - 1) s
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [length_display, hlenB, ground.length_map, length_display]
  · intro i hi
    have hiB : i < (ground.bumpAt (s.length - 1) s).length := by
      rw [← length_display]
      exact hi
    have his : i < s.length := by
      rw [← hlenB]
      exact hiB
    have hir : i < (rowList s).length := by
      rw [length_rowList]
      exact his
    have hid : i < (display s).length := by
      rw [length_display]
      exact his
    rw [getAt_display _ i hiB, hlenB, rowList_full s,
      ground.getAt_map 0 0 (fun x => x + 1) (rowList s) i hir,
      ground.getAt_map 0 0 (fun x => x + 1) (display s) i hid,
      getAt_display s i his,
      Nat.add_assoc (ground.getAt 0 (rowList s) i) 1 (s.length - i),
      Nat.add_comm 1 (s.length - i),
      ← Nat.add_assoc (ground.getAt 0 (rowList s) i) (s.length - i) 1]

/-- The content's letter bound: at a list whose content over the
first `d` letters carries its whole length, every occurring letter
sits below `d` — no member escapes the stated alphabet. -/
theorem mem_lt_of_content (d : Nat) : ∀ m : List Nat,
    sumNat (content d m) = m.length →
    ∀ x, 0 < ground.countOf x m → x < d
  | [], _, x, hx => absurd hx (Nat.lt_irrefl 0)
  | a :: m, hsum, x, hx => by
    have hsplit : sumNat (content d (a :: m))
        = (if a < d then 1 else 0) + sumNat (content d m) := by
      show sumNat ((List.range d).map (fun i =>
          ground.countOf i (a :: m)))
        = (if a < d then 1 else 0) + sumNat (content d m)
      rw [ground.map_congr_all (fun i => ground.countOf i (a :: m))
          (fun i => (if i = a then 1 else 0) + ground.countOf i m)
          (fun i => ground.countOf_cons i a m) (List.range d),
        sumNat_map_add, sumNat_indicator a d]
      rfl
    have had : a < d := by
      by_cases had : a < d
      · exact had
      · rw [hsplit, if_neg had, Nat.zero_add] at hsum
        have hle := sumNat_content_le d m
        rw [hsum] at hle
        exact absurd hle (Nat.not_succ_le_self m.length)
    have hm : sumNat (content d m) = m.length := by
      rw [hsplit, if_pos had, Nat.add_comm] at hsum
      exact Nat.succ.inj hsum
    by_cases hxa : x = a
    · rw [hxa]
      exact had
    · rw [ground.countOf_head_ne hxa] at hx
      exact mem_lt_of_content d m hm x hx

/-- The permutation-membership reads at the unit occupancy: a
member of the enumeration at `1` on every letter reads its length,
its distinctness, its letters' bound, and every letter's
occupancy. -/
theorem perm_member_reads {d : Nat} {p : List Nat}
    (hp : 0 < ground.countOf p (monomialsAt (List.replicate d 1))) :
    p.length = d ∧ (∀ x, ground.countOf x p ≤ 1)
      ∧ (∀ x, 0 < ground.countOf x p → x < d)
      ∧ (∀ x, x < d → 0 < ground.countOf x p) := by
  rw [countOf_monomialsAt] at hp
  by_cases hc : p.length = sumNat (List.replicate d 1)
      ∧ content (List.replicate d 1).length p = List.replicate d 1
  · have hlen : p.length = d := by
      rw [hc.1, sumNat_replicate_one]
    have hcont : content d p = List.replicate d 1 := by
      have h2 := hc.2
      rw [ground.length_replicate 1 d] at h2
      exact h2
    have hsum : sumNat (content d p) = p.length := by
      rw [hcont, sumNat_replicate_one, hlen]
    have hone : ∀ x, x < d → ground.countOf x p = 1 := by
      intro x hxd
      have hread := getAt_content d p x
      rw [if_pos hxd, hcont, ground.getAt_replicate 0 1 d x hxd] at hread
      exact hread.symm
    refine ⟨hlen, ?_, mem_lt_of_content d p hsum, ?_⟩
    · intro x
      by_cases hxd : x < d
      · rw [hone x hxd]
        exact Nat.le_refl 1
      · match Nat.eq_zero_or_pos (ground.countOf x p) with
        | .inl hz =>
          rw [hz]
          exact Nat.le_succ 0
        | .inr hpos =>
          exact absurd (mem_lt_of_content d p hsum x hpos) hxd
    · intro x hxd
      rw [hone x hxd]
      exact Nat.succ_pos 0
  · rw [if_neg hc] at hp
    exact absurd hp (Nat.lt_irrefl 0)

/-- Membership transports across a count-preserving read: a family
at one length and every member count with a member of the
enumeration is a member. -/
theorem perm_member_of_counts {d : Nat} {p q : List Nat}
    (hp : 0 < ground.countOf p (monomialsAt (List.replicate d 1)))
    (hlen : q.length = p.length)
    (hc : ∀ x, ground.countOf x q = ground.countOf x p) :
    0 < ground.countOf q (monomialsAt (List.replicate d 1)) := by
  rw [countOf_monomialsAt] at hp
  by_cases hcnd : p.length = sumNat (List.replicate d 1)
      ∧ content (List.replicate d 1).length p = List.replicate d 1
  · have hcq : content (List.replicate d 1).length q
        = content (List.replicate d 1).length p := by
      show (List.range (List.replicate d 1).length).map
          (fun i => ground.countOf i q)
        = (List.range (List.replicate d 1).length).map
          (fun i => ground.countOf i p)
      exact ground.map_congr_all _ _ hc _
    rw [countOf_monomialsAt,
      if_pos ⟨hlen.trans hcnd.1, hcq.trans hcnd.2⟩]
    exact Nat.succ_pos 0
  · rw [if_neg hcnd] at hp
    exact absurd hp (Nat.lt_irrefl 0)

/-- The adjacent exchange keeps the place enumeration's membership:
the length and every letter count read through the move. -/
theorem perm_member_adjSwap {d : Nat} {p : List Nat}
    (hp : 0 < ground.countOf p (monomialsAt (List.replicate d 1)))
    (k : Nat) :
    0 < ground.countOf (ground.adjSwap k p)
      (monomialsAt (List.replicate d 1)) :=
  perm_member_of_counts hp (ground.length_adjSwap k p)
    (fun x => ground.countOf_adjSwap x k p)

/-- A place's entry names its place back, at a distinct family. -/
theorem posOf_getAt {m : List Nat}
    (hdist : ∀ z, ground.countOf z m ≤ 1) :
    ∀ t, t < m.length → posOf (ground.getAt 0 m t) m = t := by
  induction m with
  | nil => exact fun t h => absurd h (Nat.not_lt_zero t)
  | cons a m ih =>
    intro t ht
    match t with
    | 0 =>
      rw [posOf_cons]
      show (if a = a then 0 else posOf a m + 1) = 0
      rw [if_pos rfl]
    | t + 1 =>
      rw [posOf_cons]
      show (if ground.getAt 0 m t = a then 0
        else posOf (ground.getAt 0 m t) m + 1) = t + 1
      have hne : ground.getAt 0 m t ≠ a := fun he => by
        have h2 : 2 ≤ ground.countOf a (a :: m) := by
          rw [ground.countOf_head]
          have hpos : 0 < ground.countOf a m := by
            rw [← he]
            exact countOf_getAt_pos 0 m t (Nat.lt_of_succ_lt_succ ht)
          exact Nat.add_le_add hpos (Nat.le_refl 1)
        exact absurd (Nat.le_trans h2 (hdist a))
          (Nat.not_succ_le_self 1)
      rw [if_neg hne,
        ih (fun z => Nat.le_trans (Nat.le_add_left _ _) (hdist z))
          t (Nat.lt_of_succ_lt_succ ht)]

/-- The transposition at two places in either order, the gap's own
conjugation; at one place the family is kept. -/
def swapPair (i j : Nat) (m : List Nat) : List Nat :=
  if i < j then swapPosG i (j - i - 1) m
  else if j < i then swapPosG j (i - j - 1) m
  else m

/-- The transposition reads at either order. -/
theorem swapPair_comm (i j : Nat) (m : List Nat) :
    swapPair i j m = swapPair j i m := by
  show (if i < j then swapPosG i (j - i - 1) m
      else if j < i then swapPosG j (i - j - 1) m else m)
    = (if j < i then swapPosG j (i - j - 1) m
      else if i < j then swapPosG i (j - i - 1) m else m)
  by_cases hij : i < j
  · rw [if_pos hij, if_neg (Nat.lt_asymm hij), if_pos hij]
  · by_cases hji : j < i
    · rw [if_neg hij, if_pos hji, if_pos hji]
    · rw [if_neg hij, if_neg hji, if_neg hji, if_neg hij]

theorem length_swapPair (i j : Nat) (m : List Nat) :
    (swapPair i j m).length = m.length := by
  show (if i < j then swapPosG i (j - i - 1) m
      else if j < i then swapPosG j (i - j - 1) m else m).length
    = m.length
  by_cases hij : i < j
  · rw [if_pos hij]
    exact length_swapPosG i (j - i - 1) m
  · by_cases hji : j < i
    · rw [if_neg hij, if_pos hji]
      exact length_swapPosG j (i - j - 1) m
    · rw [if_neg hij, if_neg hji]

theorem countOf_swapPair (x i j : Nat) (m : List Nat) :
    ground.countOf x (swapPair i j m) = ground.countOf x m := by
  show ground.countOf x
      (if i < j then swapPosG i (j - i - 1) m
        else if j < i then swapPosG j (i - j - 1) m else m)
    = ground.countOf x m
  by_cases hij : i < j
  · rw [if_pos hij]
    exact countOf_swapPosG x i (j - i - 1) m
  · by_cases hji : j < i
    · rw [if_neg hij, if_pos hji]
      exact countOf_swapPosG x j (i - j - 1) m
    · rw [if_neg hij, if_neg hji]

/-- The transposition flips the swap grading at two distinct
interior places. -/
theorem parity_swapPair {i j : Nat} (m : List Nat) (hne : i ≠ j)
    (hi : i < m.length) (hj : j < m.length)
    (hdist : ∀ x, ground.countOf x m ≤ 1) :
    parity (swapPair i j m) = !(parity m) := by
  show parity
      (if i < j then swapPosG i (j - i - 1) m
        else if j < i then swapPosG j (i - j - 1) m else m)
    = !(parity m)
  by_cases hij : i < j
  · rw [if_pos hij]
    have h1 : i + (j - i - 1) + 1 + 1 ≤ m.length := by
      rw [ground.natGapEq hij]
      exact hj
    exact parity_swapPosG (j - i - 1) i m h1 hdist
  · by_cases hji : j < i
    · rw [if_neg hij, if_pos hji]
      have h1 : j + (i - j - 1) + 1 + 1 ≤ m.length := by
        rw [ground.natGapEq hji]
        exact hi
      exact parity_swapPosG (i - j - 1) j m h1 hdist
    · exact absurd (Nat.le_antisymm (Nat.le_of_not_lt hij)
        (Nat.le_of_not_lt hji)) (fun e => hne e.symm)

/-- The transposition's entry read at its first place. -/
theorem getAt_swapPair_fst {i j : Nat} (m : List Nat) (hne : i ≠ j)
    (hi : i < m.length) (hj : j < m.length) :
    ground.getAt 0 (swapPair i j m) i = ground.getAt 0 m j := by
  show ground.getAt 0
      (if i < j then swapPosG i (j - i - 1) m
        else if j < i then swapPosG j (i - j - 1) m else m) i
    = ground.getAt 0 m j
  by_cases hij : i < j
  · rw [if_pos hij]
    have h1 : i + (j - i - 1) + 1 + 1 ≤ m.length := by
      rw [ground.natGapEq hij]
      exact hj
    rw [getAt_swapPosG_fst (j - i - 1) i m h1, ground.natGapEq hij]
  · by_cases hji : j < i
    · rw [if_neg hij, if_pos hji]
      have h1 : j + (i - j - 1) + 1 + 1 ≤ m.length := by
        rw [ground.natGapEq hji]
        exact hi
      have hsnd := getAt_swapPosG_snd (i - j - 1) j m h1
      rw [show j + (i - j - 1) + 1 = i from ground.natGapEq hji] at hsnd
      rw [hsnd]
    · exact absurd (Nat.le_antisymm (Nat.le_of_not_lt hij)
        (Nat.le_of_not_lt hji)) (fun e => hne e.symm)

/-- The transposition's entry read at its second place. -/
theorem getAt_swapPair_snd {i j : Nat} (m : List Nat) (hne : i ≠ j)
    (hi : i < m.length) (hj : j < m.length) :
    ground.getAt 0 (swapPair i j m) j = ground.getAt 0 m i := by
  rw [swapPair_comm i j m]
  exact getAt_swapPair_fst m (fun e => hne e.symm) hj hi

/-- The transposition's entry read off its two places. -/
theorem getAt_swapPair_ne {i j t : Nat} (m : List Nat)
    (hi : i < m.length) (hj : j < m.length)
    (hti : t ≠ i) (htj : t ≠ j) :
    ground.getAt 0 (swapPair i j m) t = ground.getAt 0 m t := by
  show ground.getAt 0
      (if i < j then swapPosG i (j - i - 1) m
        else if j < i then swapPosG j (i - j - 1) m else m) t
    = ground.getAt 0 m t
  by_cases hij : i < j
  · rw [if_pos hij]
    have h1 : i + (j - i - 1) + 1 + 1 ≤ m.length := by
      rw [ground.natGapEq hij]
      exact hj
    exact getAt_swapPosG_ne (j - i - 1) i m t h1 hti
      (by rw [ground.natGapEq hij]; exact htj)
  · by_cases hji : j < i
    · rw [if_neg hij, if_pos hji]
      have h1 : j + (i - j - 1) + 1 + 1 ≤ m.length := by
        rw [ground.natGapEq hji]
        exact hi
      exact getAt_swapPosG_ne (i - j - 1) j m t h1 htj
        (by rw [ground.natGapEq hji]; exact hti)
    · rw [if_neg hij, if_neg hji]

/-- The transposition is an involution. -/
theorem swapPair_swapPair (i j : Nat) (m : List Nat) :
    swapPair i j (swapPair i j m) = m := by
  show (if i < j then swapPosG i (j - i - 1) (swapPair i j m)
      else if j < i then swapPosG j (i - j - 1) (swapPair i j m)
      else swapPair i j m)
    = m
  by_cases hij : i < j
  · rw [if_pos hij,
      show swapPair i j m = swapPosG i (j - i - 1) m from by
        show (if i < j then _ else _) = _
        rw [if_pos hij]]
    exact swapPosG_swapPosG i (j - i - 1) m
  · by_cases hji : j < i
    · rw [if_neg hij, if_pos hji,
        show swapPair i j m = swapPosG j (i - j - 1) m from by
          show (if i < j then _ else _) = _
          rw [if_neg hij, if_pos hji]]
      exact swapPosG_swapPosG j (i - j - 1) m
    · rw [if_neg hij, if_neg hji,
        show swapPair i j m = m from by
          show (if i < j then _ else _) = _
          rw [if_neg hij, if_neg hji]]


/-! The descent and the grading's additivity (`con:places`): the
words concatenate and reverse, the sorted assignment is one list at
the classification, and the swap grading is additive over
composition, two words concatenating — the general regroupings'
package. -/

/-- The words concatenate, the actions composing. -/
theorem applyWord_append : ∀ (u v m : List Nat),
    applyWord (u ++ v) m = applyWord v (applyWord u m)
  | [], _, _ => rfl
  | k :: u, v, m => applyWord_append u v (adjSwap k m)

/-- A word's action composes with an entry map. -/
theorem applyWord_map (f : Nat → Nat) : ∀ (w m : List Nat),
    applyWord w (m.map f) = (applyWord w m).map f
  | [], _ => rfl
  | k :: w, m => by
    show applyWord w (adjSwap k (m.map f)) = _
    rw [adjSwap_map f k m]
    exact applyWord_map f w (adjSwap k m)

private theorem swapPosG_map (f : Nat → Nat) (p : Nat) :
    ∀ (g : Nat) (m : List Nat),
      swapPosG p g (m.map f) = (swapPosG p g m).map f
  | 0, m => adjSwap_map f p m
  | g + 1, m => by
    show adjSwap (p + g + 1)
        (swapPosG p g (adjSwap (p + g + 1) (m.map f)))
      = (adjSwap (p + g + 1)
          (swapPosG p g (adjSwap (p + g + 1) m))).map f
    rw [adjSwap_map f (p + g + 1) m,
      swapPosG_map f p g (adjSwap (p + g + 1) m),
      adjSwap_map f (p + g + 1)]

/-- The transposition composes with an entry map. -/
theorem swapPair_map (f : Nat → Nat) (i j : Nat) (m : List Nat) :
    swapPair i j (m.map f) = (swapPair i j m).map f := by
  show (if i < j then swapPosG i (j - i - 1) (m.map f)
      else if j < i then swapPosG j (i - j - 1) (m.map f)
      else m.map f)
    = (if i < j then swapPosG i (j - i - 1) m
      else if j < i then swapPosG j (i - j - 1) m else m).map f
  by_cases hij : i < j
  · rw [if_pos hij, if_pos hij]
    exact swapPosG_map f i (j - i - 1) m
  · by_cases hji : j < i
    · rw [if_neg hij, if_pos hji, if_neg hij, if_pos hji]
      exact swapPosG_map f j (i - j - 1) m
    · rw [if_neg hij, if_neg hji, if_neg hij, if_neg hji]

/-- The transposition at two places reading one entry keeps the
family, the repeat's fix. -/
theorem swapPair_eq_of_getAt_eq {i j : Nat} (m : List Nat)
    (hne : i ≠ j) (hi : i < m.length) (hj : j < m.length)
    (heq : ground.getAt 0 m i = ground.getAt 0 m j) :
    swapPair i j m = m := by
  refine ground.getAt_ext 0 _ _ (length_swapPair i j m) ?_
  intro t ht
  rw [length_swapPair] at ht
  by_cases hti : t = i
  · rw [hti, getAt_swapPair_fst m hne hi hj, heq]
  · by_cases htj : t = j
    · rw [htj, getAt_swapPair_snd m hne hi hj, heq]
    · exact getAt_swapPair_ne m hi hj hti htj

/-- The reversed word undoes the action. -/
theorem applyWord_reverse : ∀ (w m : List Nat),
    applyWord w.reverse (applyWord w m) = m
  | [], m => rfl
  | k :: w, m => by
    rw [ground.reverse_cons, applyWord_append]
    show adjSwap k (applyWord w.reverse (applyWord w (adjSwap k m)))
      = m
    rw [applyWord_reverse w (adjSwap k m)]
    exact adjSwap_adjSwap k m


/-- The first reversed adjacent pair's place, an occupancy read. -/
def firstRev : List Nat → Option Nat
  | [] => none
  | [_] => none
  | a :: b :: t =>
    if b < a then some 0
    else (firstRev (b :: t)).map (fun k => k + 1)

/-- An occupied first-reversal read names its pair: the place sits
interior and its successor's entry reads below its own. -/
theorem firstRev_some : ∀ (m : List Nat) (k : Nat),
    firstRev m = some k →
    k + 1 < m.length ∧ ground.getAt 0 m (k + 1) < ground.getAt 0 m k
  | [], _, h => nomatch h
  | [_], _, h => nomatch h
  | a :: b :: t, k, h => by
    have h' : (if b < a then some 0
        else (firstRev (b :: t)).map (fun k => k + 1)) = some k := h
    by_cases hba : b < a
    · rw [if_pos hba] at h'
      rw [← Option.some.inj h']
      exact ⟨Nat.succ_lt_succ (Nat.succ_pos t.length), hba⟩
    · rw [if_neg hba] at h'
      cases hf : firstRev (b :: t) with
      | none =>
        rw [hf] at h'
        exact nomatch h'
      | some k' =>
        rw [hf] at h'
        obtain ⟨h1, h2⟩ := firstRev_some (b :: t) k' hf
        rw [← Option.some.inj h']
        exact ⟨Nat.succ_lt_succ h1, h2⟩

theorem firstRev_none : ∀ (m : List Nat),
    firstRev m = none → ∀ k, k + 1 < m.length →
    ¬ ground.getAt 0 m (k + 1) < ground.getAt 0 m k
  | [], _, k, hk => absurd hk (Nat.not_lt_zero _)
  | [_], _, k, hk =>
    absurd (Nat.lt_of_succ_lt_succ hk) (Nat.not_lt_zero k)
  | a :: b :: t, h, 0, _ => by
    have h' : (if b < a then some 0
        else (firstRev (b :: t)).map (fun k => k + 1)) = none := h
    by_cases hba : b < a
    · rw [if_pos hba] at h'
      exact nomatch h'
    · exact hba
  | a :: b :: t, h, k + 1, hk => by
    have h' : (if b < a then some 0
        else (firstRev (b :: t)).map (fun k => k + 1)) = none := h
    by_cases hba : b < a
    · rw [if_pos hba] at h'
      exact nomatch h'
    · rw [if_neg hba] at h'
      have hnone : firstRev (b :: t) = none := by
        cases hf : firstRev (b :: t) with
        | none => rfl
        | some k' =>
          rw [hf] at h'
          exact nomatch h'
      exact firstRev_none (b :: t) hnone k (Nat.lt_of_succ_lt_succ hk)

private theorem firstRev_tail_none {a b : Nat} {t : List Nat}
    (h : firstRev (a :: b :: t) = none) :
    firstRev (b :: t) = none := by
  have h' : (if b < a then some 0
      else (firstRev (b :: t)).map (fun k => k + 1)) = none := h
  by_cases hba : b < a
  · rw [if_pos hba] at h'
    exact nomatch h'
  · rw [if_neg hba] at h'
    cases hf : firstRev (b :: t) with
    | none => rfl
    | some k' =>
      rw [hf] at h'
      exact nomatch h'

/-- A list at a vacant first reversal ascends: an earlier entry
sits at or below every later one, the adjacent reads chained. -/
theorem le_of_firstRev_none (x : List Nat) (hs : firstRev x = none) :
    ∀ q p, p ≤ q → q < x.length →
    ground.getAt 0 x p ≤ ground.getAt 0 x q
  | 0, p, hpq, _ => by
    rw [Nat.le_antisymm hpq (Nat.zero_le p)]
    exact Nat.le_refl _
  | q + 1, p, hpq, hq =>
    match Nat.lt_or_ge p (q + 1) with
    | .inl hlt =>
      Nat.le_trans
        (le_of_firstRev_none x hs q p (Nat.le_of_lt_succ hlt)
          (Nat.lt_of_succ_lt hq))
        (Nat.le_of_not_lt (firstRev_none x hs q hq))
    | .inr hge => by
      rw [Nat.le_antisymm hpq hge]
      exact Nat.le_refl _

private theorem head_le_of_none (a : Nat) (t : List Nat)
    (h : firstRev (a :: t) = none) :
    ∀ j, j < t.length → a ≤ ground.getAt 0 t j :=
  fun j hj =>
    le_of_firstRev_none (a :: t) h (j + 1) 0 (Nat.zero_le _)
      (Nat.succ_lt_succ hj)

private theorem countBelow_zero : ∀ (a : Nat) (t : List Nat),
    (∀ j, j < t.length → a ≤ ground.getAt 0 t j) →
    ground.countBelow a t = 0
  | _, [], _ => rfl
  | a, b :: t, h => by
    rw [ground.countBelow_cons,
      if_neg (fun hba : b < a => Nat.lt_irrefl b
        (Nat.lt_of_lt_of_le hba (h 0 (Nat.succ_pos t.length)))),
      Nat.zero_add]
    exact countBelow_zero a t (fun j hj =>
      h (j + 1) (Nat.succ_lt_succ hj))

private theorem inversions_zero_of_none : ∀ m : List Nat,
    firstRev m = none → inversions m = 0
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: t, h => by
    show ground.countBelow a (b :: t) + inversions (b :: t) = 0
    rw [countBelow_zero a (b :: t)
        (head_le_of_none a (b :: t) h),
      inversions_zero_of_none (b :: t) (firstRev_tail_none h),
      Nat.zero_add]

private theorem firstRev_none_of_inv (m : List Nat)
    (h : inversions m = 0) : firstRev m = none := by
  cases hf : firstRev m with
  | none => rfl
  | some k =>
    obtain ⟨hk, hrev⟩ := firstRev_some m k hf
    have hstep := inversions_adjSwap_gt k m hk hrev
    rw [h] at hstep
    exact nomatch hstep

/-- The descent: one letter at the first reversed pair per step,
ending with every place pair sorted. -/
def sortWord : Nat → List Nat → List Nat
  | 0, _ => []
  | fuel + 1, m =>
    match firstRev m with
    | none => []
    | some k => k :: sortWord fuel (adjSwap k m)

private theorem sortWord_eq (fuel : Nat) (m : List Nat) :
    sortWord (fuel + 1) m
      = match firstRev m with
        | none => []
        | some k => k :: sortWord fuel (adjSwap k m) := rfl

/-- The descent's reads: the end is adjacent-sorted, the letter
count is the inversion count, and every letter is interior. -/
theorem sortWord_reads : ∀ (fuel : Nat) (m : List Nat),
    inversions m ≤ fuel →
    firstRev (applyWord (sortWord fuel m) m) = none
      ∧ (sortWord fuel m).length = inversions m
      ∧ (∀ x, 0 < ground.countOf x (sortWord fuel m) →
          x + 1 < m.length)
  | 0, m, h => by
    have h0 : inversions m = 0 := Nat.le_antisymm h (Nat.zero_le _)
    exact ⟨firstRev_none_of_inv m h0, h0.symm,
      fun x hx => absurd hx (Nat.lt_irrefl 0)⟩
  | fuel + 1, m, h => by
    cases hf : firstRev m with
    | none =>
      rw [sortWord_eq, hf]
      exact ⟨hf, (inversions_zero_of_none m hf).symm,
        fun x hx => absurd hx (Nat.lt_irrefl 0)⟩
    | some k =>
      obtain ⟨hk, hrev⟩ := firstRev_some m k hf
      have hstep := inversions_adjSwap_gt k m hk hrev
      have hfuel : inversions (adjSwap k m) ≤ fuel := by
        have hh := h
        rw [hstep] at hh
        exact Nat.le_of_succ_le_succ hh
      obtain ⟨hend, hlen, hlet⟩ :=
        sortWord_reads fuel (adjSwap k m) hfuel
      rw [sortWord_eq, hf]
      refine ⟨hend, ?_, ?_⟩
      · show (sortWord fuel (adjSwap k m)).length + 1 = inversions m
        rw [hlen, ← hstep]
      · intro x hx
        by_cases hxk : x = k
        · rw [hxk]
          exact hk
        · rw [ground.countOf_head_ne hxk] at hx
          have := hlet x hx
          rw [length_adjSwap] at this
          exact this


/-! The adjacent exchange as the transposition's instance, one
adjacent-sorted list per count family, and a count read's
transport along a word — `lem:strings`' sorting vocabulary at
the places calculus. -/

/-- The transposition at consecutive places is the list kit's own
adjacent exchange. -/
theorem swapPair_adjacent (k : Nat) (m : List Nat) :
    swapPair k (k + 1) m = ground.adjSwap k m := by
  have h1 : k + 1 - k = 1 :=
    ground.addCancelL k (by
      rw [ground.natAddSubCancel (Nat.le_succ k)])
  show (if k < k + 1 then swapPosG k (k + 1 - k - 1) m
    else if k + 1 < k then swapPosG (k + 1) (k - (k + 1) - 1) m
    else m) = ground.adjSwap k m
  rw [if_pos (Nat.lt_succ_self k), h1]
  exact rfl

/-- One adjacent-sorted list per count family. -/
theorem sorted_eq_of_counts : ∀ u v : List Nat,
    firstRev u = none → firstRev v = none →
    (∀ x, ground.countOf x u = ground.countOf x v) → u = v
  | [], [], _, _, _ => rfl
  | [], b :: s, _, _, hc => by
    have h0 := (hc b).symm
    rw [ground.countOf_head] at h0
    exact Nat.noConfusion h0
  | a :: t, [], _, _, hc => by
    have h0 := hc a
    rw [ground.countOf_head] at h0
    exact Nat.noConfusion h0
  | a :: t, b :: s, hu, hv, hc => by
    have hmemk : ∀ (c : Nat) (l : List Nat), firstRev (c :: l) = none →
        ∀ x, 0 < ground.countOf x (c :: l) → c ≤ x := by
      intro c l hn x hx
      match ground.getAt_of_mem 0 (ground.mem_of_countOf_pos x _ hx)
        with
      | ⟨j, hjl, hje⟩ =>
        match j with
        | 0 => exact Nat.le_of_eq hje
        | j + 1 =>
          rw [← hje]
          exact head_le_of_none c l hn j
            (Nat.lt_of_succ_lt_succ hjl)
    have hab : a = b := by
      refine Nat.le_antisymm ?_ ?_
      · refine hmemk a t hu b ?_
        rw [hc b, ground.countOf_head]
        exact Nat.succ_pos _
      · refine hmemk b s hv a ?_
        rw [← hc a, ground.countOf_head]
        exact Nat.succ_pos _
    have htail : ∀ x, ground.countOf x t = ground.countOf x s := by
      intro x
      refine ground.addCancelL (if x = b then 1 else 0) ?_
      have hx := hc x
      rw [ground.countOf_cons x a t, ground.countOf_cons x b s,
        hab] at hx
      exact hx
    have hut : firstRev t = none := by
      match t with
      | [] => rfl
      | c :: t' => exact firstRev_tail_none hu
    have hvt : firstRev s = none := by
      match s with
      | [] => rfl
      | c :: s' => exact firstRev_tail_none hv
    rw [hab, sorted_eq_of_counts t s hut hvt htail]

/-- A count read's transport along a word of interior letters. -/
theorem applyWord_inv (f : List Nat → Nat) (d : Nat)
    (hf : ∀ nu, nu.length = d → ∀ k, k + 1 < d →
      f (ground.adjSwap k nu) = f nu) :
    ∀ (w m : List Nat), m.length = d →
      (∀ x, 0 < ground.countOf x w → x + 1 < d) →
      f (applyWord w m) = f m
  | [], _, _, _ => rfl
  | k :: w, m, hm, hw => by
    show f (applyWord w (ground.adjSwap k m)) = f m
    rw [applyWord_inv f d hf w (ground.adjSwap k m)
        (by rw [ground.length_adjSwap]; exact hm)
        (fun x hx => hw x (by
          rw [ground.countOf_cons x k w]
          exact Nat.lt_of_lt_of_le hx (Nat.le_add_left _ _)))]
    exact hf m hm k (hw k (by
      rw [ground.countOf_head]
      exact Nat.succ_pos _))

/-! The monomial family's membership reads: a listed monomial's
own conditions, the content's positional entry, and the vacant
letter's absence from every member. -/

/-- A monomial listed at a content carries that content's degree
and reads it back. -/
theorem member_conditions {m mu : List Nat}
    (h : 0 < ground.countOf m (monomialsAt mu)) :
    m.length = sumNat mu ∧ content mu.length m = mu := by
  rw [countOf_monomialsAt mu m] at h
  by_cases hc : m.length = sumNat mu ∧ content mu.length m = mu
  · exact hc
  · rw [if_neg hc] at h
    exact absurd h (Nat.lt_irrefl 0)

/-- The content's entry at a letter below the alphabet is that
letter's count. -/
theorem getAt_contentAt (d : Nat) (m : List Nat) (x : Nat)
    (hx : x < d) :
    ground.getAt 0 (content d m) x = ground.countOf x m := by
  show ground.getAt 0
    ((List.range d).map (fun i => ground.countOf i m)) x = _
  rw [ground.getAt_map 0 0 (fun i => ground.countOf i m)
      (List.range d) x
      (by rw [length_range]; exact hx),
    getAt_range d x hx]

/-- An unoccupied letter of a content occurs in no member of that
content's monomial family. -/
theorem letter_zero (mu : List Nat) (j : Nat)
    (hz : ground.getAt 0 mu j = 0) :
    ∀ s, 0 < ground.countOf s (monomialsAt mu) →
      ground.countOf j s = 0 := by
  intro s hs
  match member_conditions hs with
  | ⟨hl, hc⟩ =>
    by_cases hj : j < mu.length
    · rw [← getAt_contentAt mu.length s j hj, hc, hz]
    · match Nat.eq_zero_or_pos (ground.countOf j s) with
      | .inl h0 => exact h0
      | .inr hpos =>
        exact absurd
          (mem_lt_of_content mu.length s (by rw [hc, hl]) j hpos)
          hj

theorem length_applyWord : ∀ (w m : List Nat),
    (applyWord w m).length = m.length
  | [], _ => rfl
  | k :: w, m => by
    show (applyWord w (adjSwap k m)).length = m.length
    rw [length_applyWord w (adjSwap k m), length_adjSwap]

theorem countOf_applyWord (x : Nat) : ∀ (w m : List Nat),
    ground.countOf x (applyWord w m) = ground.countOf x m
  | [], _ => rfl
  | k :: w, m => by
    show ground.countOf x (applyWord w (adjSwap k m)) = _
    rw [countOf_applyWord x w (adjSwap k m), countOf_adjSwap]

private theorem strict_chain (m : List Nat)
    (hnone : firstRev m = none)
    (hdist : ∀ x, ground.countOf x m ≤ 1) :
    ∀ (g i : Nat), i + g < m.length →
      ground.getAt 0 m i + g ≤ ground.getAt 0 m (i + g)
  | 0, i, _ => Nat.le_refl _
  | g + 1, i, h => by
    have hlt : ground.getAt 0 m (i + g)
        < ground.getAt 0 m (i + g + 1) :=
      Nat.lt_of_le_of_ne
        (Nat.le_of_not_lt (firstRev_none m hnone (i + g) h))
        (getAt_ne_of_distinct hdist (Nat.lt_succ_self (i + g)) h)
    have hch := strict_chain m hnone hdist g i
      (Nat.lt_of_succ_lt h)
    show ground.getAt 0 m i + g + 1 ≤ ground.getAt 0 m (i + g + 1)
    exact Nat.le_trans (Nat.succ_le_succ hch)
      (Nat.succ_le_of_lt hlt)

/-- The sorted assignment is one list: an adjacent-sorted distinct
family at interior letters and full length is the unit
assignment. -/
theorem sorted_eq_range (d : Nat) (m : List Nat)
    (hlen : m.length = d) (hdist : ∀ x, ground.countOf x m ≤ 1)
    (hval : ∀ x, 0 < ground.countOf x m → x < d)
    (hnone : firstRev m = none) : m = List.range d := by
  refine ground.getAt_ext 0 m (List.range d)
    (by rw [hlen, length_range]) ?_
  intro i hi
  have hid : i < d := by
    rw [← hlen]
    exact hi
  rw [getAt_range d i hid]
  have hd0 : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le i) hid
  have hds : d - 1 + 1 = d := Nat.succ_pred_eq_of_pos hd0
  have hdlt : d - 1 < m.length := by
    rw [hlen]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (d - 1))
      (Nat.le_of_eq hds)
  have hlow : i ≤ ground.getAt 0 m i := by
    have hc := strict_chain m hnone hdist i 0 (by
      rw [Nat.zero_add]
      exact hi)
    rw [Nat.zero_add] at hc
    exact Nat.le_trans (Nat.le_add_left i (ground.getAt 0 m 0)) hc
  have hd1 : i ≤ d - 1 :=
    Nat.le_of_lt_succ (show i < (d - 1) + 1 from by
      rw [hds]
      exact hid)
  have hsplit : i + (d - 1 - i) = d - 1 := ground.natAddSubCancel hd1
  have hup : ground.getAt 0 m i ≤ i := by
    have hc := strict_chain m hnone hdist (d - 1 - i) i (by
      rw [hsplit]
      exact hdlt)
    rw [hsplit] at hc
    have htop : ground.getAt 0 m (d - 1) ≤ d - 1 := by
      have hmem := hval (ground.getAt 0 m (d - 1))
        (countOf_getAt_pos 0 m (d - 1) hdlt)
      exact Nat.le_of_lt_succ
        (show ground.getAt 0 m (d - 1) < d - 1 + 1 from by
          rw [hds]
          exact hmem)
    have hcombined : ground.getAt 0 m i + (d - 1 - i)
        ≤ i + (d - 1 - i) := by
      rw [hsplit]
      exact Nat.le_trans hc htop
    exact ground.leCancelR (d - 1 - i) hcombined
  exact Nat.le_antisymm hup hlow


/-- The parity read is additive over the sum. -/
theorem parityOf_add : ∀ a b : Nat,
    parityOf (a + b) = xor (parityOf a) (parityOf b)
  | _, 0 => (xorFalse _).symm
  | a, b + 1 => by
    show Bool.not (parityOf (a + b))
      = xor (parityOf a) (Bool.not (parityOf b))
    rw [parityOf_add a b, xorNot]


/-- The swap grading is additive over composition, two words
concatenating: the composed assignment's parity is the two
parities' sum. -/
theorem parity_comp (d : Nat) (p q : List Nat)
    (hp : 0 < ground.countOf p (monomialsAt (List.replicate d 1)))
    (hq : 0 < ground.countOf q (monomialsAt (List.replicate d 1))) :
    parity (p.map (ground.getAt 0 q)) = xor (parity p) (parity q) := by
  obtain ⟨hplen, hpdist, hpval, _⟩ := perm_member_reads hp
  obtain ⟨hqlen, hqdist, _, _⟩ := perm_member_reads hq
  obtain ⟨hend, hlen, hlet⟩ :=
    sortWord_reads (inversions p) p (Nat.le_refl _)
  have hsorted : applyWord (sortWord (inversions p) p) p
      = List.range d := by
    refine sorted_eq_range d _ ?_ ?_ ?_ hend
    · rw [length_applyWord, hplen]
    · intro x
      rw [countOf_applyWord]
      exact hpdist x
    · intro x hx
      rw [countOf_applyWord] at hx
      exact hpval x hx
  have hpw : applyWord (sortWord (inversions p) p).reverse
      (List.range d) = p := by
    rw [← hsorted]
    exact applyWord_reverse _ p
  have hcomp : p.map (ground.getAt 0 q)
      = applyWord (sortWord (inversions p) p).reverse q :=
    calc p.map (ground.getAt 0 q)
        = (applyWord (sortWord (inversions p) p).reverse
            (List.range d)).map (ground.getAt 0 q) := by rw [hpw]
      _ = applyWord (sortWord (inversions p) p).reverse
            ((List.range d).map (ground.getAt 0 q)) :=
          (applyWord_map _ _ _).symm
      _ = applyWord (sortWord (inversions p) p).reverse q := by
          rw [range_map_getAt 0 d q hqlen]
  have hwp := word_parity (sortWord (inversions p) p).reverse q
    hqdist
    (fun k hk => by
      rw [hqlen]
      have hk' : 0 < ground.countOf k (sortWord (inversions p) p) := by
        rw [← countOf_reverse]
        exact hk
      have hb := hlet k hk'
      rw [hplen] at hb
      exact hb)
  rw [hcomp, ← hwp, ground.length_reverse, hlen]
  exact parityOf_add (inversions p) (inversions q)


/-! The inverse permutation (`con:places`): the assignment flipped,
its value at a letter the witness place reading it. -/


/-- The counts of a member's assignment are the reference's own,
the count equation's transport. -/
theorem countOf_comp (d : Nat) (x : Nat) {p r : List Nat}
    (hp : 0 < ground.countOf p (monomialsAt (List.replicate d 1)))
    (hr : r.length = d) :
    ground.countOf x (p.map (ground.getAt 0 r))
      = ground.countOf x r := by
  obtain ⟨hplen, hpdist, hpval, hpocc⟩ := perm_member_reads hp
  have hcounts : ∀ j, ground.countOf j p
      = ground.countOf j (List.range d) := by
    intro j
    rw [countOf_range j d]
    by_cases hj : j < d
    · rw [if_pos hj]
      exact Nat.le_antisymm (hpdist j) (hpocc j hj)
    · rw [if_neg hj]
      match Nat.eq_zero_or_pos (ground.countOf j p) with
      | .inl hz => exact hz
      | .inr hpos => exact absurd (hpval j hpos) hj
  rw [ground.countOf_map_famFold x (ground.getAt 0 r) p,
    ground.famFold_relist Nat.add 0 Nat.add_comm Nat.add_assoc
      (fun j => if x = ground.getAt 0 r j then 1 else 0)
      p (List.range d) hcounts,
    ← ground.countOf_map_famFold x (ground.getAt 0 r) (List.range d),
    range_map_getAt 0 d r hr]

private theorem posOf_absent (x : Nat) : ∀ m : List Nat,
    ground.countOf x m = 0 → posOf x m = m.length
  | [], _ => rfl
  | a :: t, h => by
    have hxa : x ≠ a := fun he => by
      rw [he, ground.countOf_head] at h
      exact nomatch h
    rw [posOf_cons]
    show (if x = a then 0 else posOf x t + 1) = t.length + 1
    rw [if_neg hxa, posOf_absent x t (by
      rw [← ground.countOf_head_ne hxa t]
      exact h)]

/-- The inverse permutation: the assignment flipped, its value at a
letter the witness place reading it. -/
def invPerm (d : Nat) (q : List Nat) : List Nat :=
  (List.range d).map (fun j => posOf j q)

/-- The place permutations at a count, the enumeration at the unit
occupancy. -/
def perms (d : Nat) : List (List Nat) :=
  monomialsAt (List.replicate d 1)

/-- A permutation's letter counts are the range's own: every letter
below the count once, every letter at or beyond it absent. -/
theorem perm_counts_range (k : Nat) {σ : List Nat}
    (hσ : 0 < ground.countOf σ (perms k)) (x : Nat) :
    ground.countOf x σ = ground.countOf x (List.range k) := by
  obtain ⟨hlen, hdist, hval, hocc⟩ := perm_member_reads hσ
  rw [ground.countOf_range x k]
  by_cases hx : x < k
  · rw [if_pos hx]
    exact Nat.le_antisymm (hdist x) (hocc x hx)
  · rw [if_neg hx]
    match Nat.eq_zero_or_pos (ground.countOf x σ) with
    | .inl h => exact h
    | .inr h => exact absurd (hval x h) hx

/-- The permuted display: the monomial's exponent list at a
permutation. -/
def expo (beta p : List Nat) : List Nat :=
  p.map (ground.getAt 0 beta)

/-- The permuted display of a member is a member: the composed
assignment's length and letter counts read through the two maps
(`con:places`' words at the grading's composition). -/
theorem expo_member (n : Nat) {q p : List Nat}
    (hq : 0 < ground.countOf q (perms n))
    (hp : 0 < ground.countOf p (perms n)) :
    0 < ground.countOf (expo q p) (perms n) := by
  have hplen := (perm_member_reads hp).1
  have hqlen := (perm_member_reads hq).1
  refine perm_member_of_counts hq ?_ (fun x => ?_)
  · show (p.map (ground.getAt 0 q)).length = _
    rw [ground.length_map, hplen, hqlen]
  · exact countOf_comp n x hp hqlen

/-- The permuted display's entry is the reference's at the
assignment's own key. -/
theorem getAt_expo (m p : List Nat) (q : Nat) (hq : q < p.length) :
    ground.getAt 0 (expo m p) q
      = ground.getAt 0 m (ground.getAt 0 p q) := by
  show ground.getAt 0 (p.map (ground.getAt 0 m)) q = _
  rw [ground.getAt_map 0 0 (ground.getAt 0 m) p q hq]

/-- The orbit walk: from a place the iterated images to the
start's return, the fuel bounding the steps — `cyclesOf`'s own
recursion, one cyclic word per orbit. -/
def cycGo (pi : List Nat) (start : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, i =>
    i :: (if ground.getAt 0 pi i == start then []
          else cycGo pi start fuel (ground.getAt 0 pi i))

/-- A permutation's cycles, the orbit words: from each least
unwalked place the iterated images to the start's return, one
cyclic word per orbit in place order, the walk's fuel the place
count. -/
def cyclesOf (pi : List Nat) : List (List Nat) :=
  ((List.range pi.length).foldl (fun st i =>
    if 0 < ground.countOf i st.2 then st
    else
      let c := cycGo pi i pi.length i
      (st.1 ++ [c], st.2 ++ c))
    (([], []) : List (List Nat) × List Nat)).1

theorem getAt_invPerm (d : Nat) (q : List Nat) {j : Nat}
    (hj : j < d) : ground.getAt 0 (invPerm d q) j = posOf j q := by
  show ground.getAt 0
    ((List.range d).map (fun j => posOf j q)) j = posOf j q
  rw [getAt_map_range 0 (fun j => posOf j q) d j, if_pos hj]

/-- The flipped assignment's length is the stated count. -/
theorem length_invPerm (d : Nat) (q : List Nat) :
    (invPerm d q).length = d :=
  ground.length_mapRange _ d

/-- The flipped assignment's counts are the assignment's own. -/
theorem countOf_invPerm (d : Nat) {q : List Nat} (x : Nat)
    (hq : 0 < ground.countOf q (monomialsAt (List.replicate d 1))) :
    ground.countOf x (invPerm d q) = ground.countOf x q := by
  obtain ⟨hqlen, hqdist, hqval, hqocc⟩ := perm_member_reads hq
  show ground.countOf x ((List.range d).map (fun j => posOf j q))
    = ground.countOf x q
  rw [ground.countOf_map_famFold x (fun j => posOf j q) (List.range d)]
  by_cases hx : x < d
  · rw [foldRange_single (fun j => if x = posOf j q then 1 else 0)
        (ground.getAt 0 q x)
        (fun j hj => by
          rw [if_neg (fun he : x = posOf j q => hj (by
            match Nat.eq_zero_or_pos (ground.countOf j q) with
            | .inl hz =>
              have habs := posOf_absent j q hz
              rw [habs, hqlen] at he
              exact absurd he (Nat.ne_of_lt hx)
            | .inr hpos =>
              rw [he]
              exact (getAt_posOf j q hpos).symm))]) d,
      if_pos (hqval (ground.getAt 0 q x)
        (countOf_getAt_pos 0 q x (by rw [hqlen]; exact hx))),
      if_pos ((posOf_getAt hqdist x (by
        rw [hqlen]; exact hx)).symm),
      Nat.le_antisymm (hqdist x) (hqocc x hx)]
  · have hz : ground.famFold Nat.add 0
        (fun j => if x = posOf j q then 1 else 0) (List.range d)
        = 0 := by
      rw [ground.famFold_congr_members Nat.add 0 _ (fun _ => 0)
        (List.range d) (fun j hj => by
          rw [countOf_range j d] at hj
          by_cases hjd : j < d
          · rw [if_neg (fun he : x = posOf j q => hx (by
              rw [he]
              have hjq : 0 < ground.countOf j q := hqocc j hjd
              have hpl := posOf_lt j q hjq
              rw [hqlen] at hpl
              exact hpl))]
          · rw [if_neg hjd] at hj
            exact absurd hj (Nat.lt_irrefl 0)),
        ground.famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl)
          (List.range d)]
    rw [hz]
    match Nat.eq_zero_or_pos (ground.countOf x q) with
    | .inl hz2 => exact hz2.symm
    | .inr hpos => exact absurd (hqval x hpos) hx

/-- The flipped assignment is a member. -/
theorem invPerm_member (d : Nat) {q : List Nat}
    (hq : 0 < ground.countOf q (monomialsAt (List.replicate d 1))) :
    0 < ground.countOf (invPerm d q)
      (monomialsAt (List.replicate d 1)) := by
  obtain ⟨hqlen, _, _, _⟩ := perm_member_reads hq
  exact perm_member_of_counts hq
    (by rw [length_invPerm, hqlen])
    (fun x => countOf_invPerm d x hq)

/-- The flip is an involution: the flipped assignment's flip reads
the assignment back, the witness of the witness the letter itself. -/
theorem invPerm_invPerm (d : Nat) {q : List Nat}
    (hq : 0 < ground.countOf q
      (monomialsAt (List.replicate d 1))) :
    invPerm d (invPerm d q) = q := by
  obtain ⟨hqlen, hqdist, hqval, _⟩ := perm_member_reads hq
  obtain ⟨_, hidist, _, _⟩ :=
    perm_member_reads (invPerm_member d hq)
  refine ground.getAt_ext 0 _ _ (by rw [length_invPerm, hqlen]) ?_
  intro i hi
  rw [length_invPerm] at hi
  rw [getAt_invPerm d (invPerm d q) hi]
  have hti : ground.getAt 0 q i < d :=
    hqval _ (countOf_getAt_pos 0 q i (by rw [hqlen]; exact hi))
  have hkey : ground.getAt 0 (invPerm d q)
      (ground.getAt 0 q i) = i := by
    rw [getAt_invPerm d q hti,
      posOf_getAt hqdist i (by rw [hqlen]; exact hi)]
  have hmain := posOf_getAt hidist (ground.getAt 0 q i)
    (by rw [length_invPerm]; exact hti)
  rw [hkey] at hmain
  exact hmain


theorem firstRev_none_of_sorted : ∀ m : List Nat,
    (∀ k, k + 1 < m.length →
      ¬ ground.getAt 0 m (k + 1) < ground.getAt 0 m k) →
    firstRev m = none
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: t, h => by
    show (if b < a then some 0
        else (firstRev (b :: t)).map (fun k => k + 1)) = none
    have hba : ¬ b < a := h 0 (Nat.succ_lt_succ (Nat.succ_pos t.length))
    rw [if_neg hba,
      firstRev_none_of_sorted (b :: t) (fun k hk =>
        h (k + 1) (Nat.succ_lt_succ hk))]
    rfl

theorem inversions_range (d : Nat) :
    inversions (List.range d) = 0 :=
  inversions_zero_of_none (List.range d)
    (firstRev_none_of_sorted (List.range d) (fun k hk => by
      have hk1 : k + 1 < d := by
        rw [← length_range d]
        exact hk
      rw [getAt_range d (k + 1) hk1,
        getAt_range d k (Nat.lt_of_succ_lt hk1)]
      exact fun hlt => Nat.lt_irrefl k
        (Nat.lt_of_succ_lt_succ (Nat.lt_succ_of_lt hlt))))


/-- The unit assignment's grading is even: its inversion family is
vacant, the parity read false. -/
theorem parity_range (d : Nat) :
    parity (List.range d) = false := by
  show parityOf (inversions (List.range d)) = false
  rw [inversions_range]
  rfl

/-- The adjacent exchange of the unit assignment is odd. -/
theorem parity_adjSwap_range (d k : Nat) (hk : k + 1 < d) :
    parity (ground.adjSwap k (List.range d)) = true := by
  have hlen : k + 1 < (List.range d).length := by
    rw [ground.length_range]
    exact hk
  have hne : ground.getAt 0 (List.range d) k
      ≠ ground.getAt 0 (List.range d) (k + 1) := by
    rw [ground.getAt_range d k (Nat.lt_of_succ_lt hk),
      ground.getAt_range d (k + 1) hk]
    exact Nat.ne_of_lt (Nat.lt_succ_self k)
  rw [parity_adjSwap k (List.range d) hlen hne, parity_range d]
  rfl

/-- The identity's words are at the paired letters alone, the
letter count twice the returning count, even outright. -/
theorem word_identity (d : Nat) (w : List Nat)
    (hlet : ∀ k, 0 < ground.countOf k w →
      k + 1 < (List.range d).length)
    (hend : applyWord w (List.range d) = List.range d) :
    w.length = 2 * returns w (List.range d) := by
  have hw := word_count w (List.range d)
    (fun x => by
      rw [countOf_range x d]
      by_cases hx : x < d
      · rw [if_pos hx]
        exact Nat.le_refl 1
      · rw [if_neg hx]
        exact Nat.le_succ 0)
    hlet
  rw [hend, inversions_range d, Nat.zero_add] at hw
  exact hw

private theorem xor_eq_false {a b : Bool} (h : xor a b = false) :
    a = b := by
  cases a with
  | true =>
    cases b with
    | true => rfl
    | false => exact absurd h (fun hh => Bool.noConfusion hh)
  | false =>
    cases b with
    | true => exact absurd h (fun hh => Bool.noConfusion hh)
    | false => rfl

/-- A member's entry sits below the width. -/
theorem perm_lt (m : Nat) {ρ : List Nat}
    (hr : 0 < ground.countOf ρ (perms m)) (i : Nat)
    (hi : i < m) : ground.getAt 0 ρ i < m := by
  obtain ⟨hlen, _, hval, _⟩ := perm_member_reads hr
  exact hval _ (ground.countOf_getAt_pos 0 ρ i (by
    rw [hlen]
    exact hi))

/-- The partner assignment's entry sits below the width. -/
theorem perm_inv_lt (m : Nat) {ρ : List Nat}
    (hr : 0 < ground.countOf ρ (perms m)) (i : Nat)
    (hi : i < m) :
    ground.getAt 0 (invPerm m ρ) i < m := by
  obtain ⟨hlen, _, _, hocc⟩ := perm_member_reads hr
  rw [getAt_invPerm m ρ hi, ← hlen]
  exact posOf_lt i ρ (hocc i hi)

/-- The assignment reads its partner's entry back. -/
theorem perm_right (m : Nat) {ρ : List Nat}
    (hr : 0 < ground.countOf ρ (perms m)) (i : Nat)
    (hi : i < m) :
    ground.getAt 0 ρ (ground.getAt 0 (invPerm m ρ) i) = i := by
  obtain ⟨_, _, _, hocc⟩ := perm_member_reads hr
  rw [getAt_invPerm m ρ hi]
  exact getAt_posOf i ρ (hocc i hi)

/-- The partner reads the assignment's entry back. -/
theorem perm_left (m : Nat) {ρ : List Nat}
    (hr : 0 < ground.countOf ρ (perms m)) (i : Nat)
    (hi : i < m) :
    ground.getAt 0 (invPerm m ρ) (ground.getAt 0 ρ i) = i := by
  obtain ⟨hlen, hdist, _, _⟩ := perm_member_reads hr
  rw [getAt_invPerm m ρ (perm_lt m hr i hi)]
  exact posOf_getAt hdist i (by
    rw [hlen]
    exact hi)

/-- The composed pair reads the unit assignment: the flipped
assignment against the assignment is the sorted display. -/
theorem invPerm_comp (d : Nat) {q : List Nat}
    (hq : 0 < ground.countOf q (monomialsAt (List.replicate d 1))) :
    (invPerm d q).map (ground.getAt 0 q) = List.range d := by
  obtain ⟨hqlen, hqdist, hqval, hqocc⟩ := perm_member_reads hq
  show ((List.range d).map (fun j => posOf j q)).map
      (ground.getAt 0 q) = List.range d
  rw [ground.map_map (fun j => posOf j q) (ground.getAt 0 q)
      (List.range d),
    ground.map_congr_members
      (fun x => ground.getAt 0 q (posOf x q)) (fun x => x)
      (List.range d) (fun j hj => by
        rw [countOf_range j d] at hj
        by_cases hjd : j < d
        · exact getAt_posOf j q (hqocc j hjd)
        · rw [if_neg hjd] at hj
          exact absurd hj (Nat.lt_irrefl 0)),
    ground.map_id]

/-- The flipped assignment shares the grading: composing the two
reads the unit assignment, whose parity is even. -/
theorem parity_invPerm (d : Nat) {q : List Nat}
    (hq : 0 < ground.countOf q (monomialsAt (List.replicate d 1))) :
    parity (invPerm d q) = parity q := by
  have hpc := parity_comp d (invPerm d q) q (invPerm_member d hq) hq
  rw [invPerm_comp d hq] at hpc
  have hfalse : parity (List.range d) = false := by
    show parityOf (inversions (List.range d)) = false
    rw [inversions_range d]
    rfl
  rw [hfalse] at hpc
  exact xor_eq_false hpc.symm

/-! The orbit walk's kit: the iterated assignment with its splits
and bound, the positional injectivity, and the pigeonhole at the
key range — a distinct family within the alphabet is no longer
than the alphabet. -/

/-- The assignment's iterate at a count: `def:ground`'s composed
walk, the place after the stated number of steps. -/
def iterP (pi : List Nat) : Nat → Nat → Nat
  | 0, j => j
  | t + 1, j => ground.getAt 0 pi (iterP pi t j)

/-- The iterate splits at its first step. -/
theorem iterP_succ (pi : List Nat) :
    ∀ (t j : Nat),
      iterP pi (t + 1) j = iterP pi t (ground.getAt 0 pi j)
  | 0, _ => rfl
  | t + 1, j => congrArg (ground.getAt 0 pi) (iterP_succ pi t j)

/-- The iterate splits at any seam. -/
theorem iterP_add (pi : List Nat) :
    ∀ (a b j : Nat), iterP pi (a + b) j = iterP pi a (iterP pi b j)
  | 0, b, j => by rw [Nat.zero_add]; rfl
  | a + 1, b, j => by
    rw [Nat.succ_add]
    exact congrArg (ground.getAt 0 pi) (iterP_add pi a b j)

/-- The iterates stay within the key range. -/
theorem iterP_lt (k : Nat) {π : List Nat}
    (hπ : 0 < ground.countOf π (perms k)) :
    ∀ (t j : Nat), j < k → iterP π t j < k := by
  obtain ⟨hlen, _, hval, _⟩ := perm_member_reads hπ
  intro t
  induction t with
  | zero => exact fun j hj => hj
  | succ t ih =>
    intro j hj
    exact hval _ (ground.countOf_getAt_pos 0 π (iterP π t j)
      (by rw [hlen]; exact ih j hj))

/-- The assignment is positionally injective: one value sits at one
place. -/
theorem perm_inj (k : Nat) {π : List Nat}
    (hπ : 0 < ground.countOf π (perms k)) :
    ∀ a b, a < k → b < k →
      ground.getAt 0 π a = ground.getAt 0 π b → a = b := by
  obtain ⟨hlen, hdist, _, _⟩ := perm_member_reads hπ
  intro a b ha hb he
  have h1 := posOf_getAt hdist a (by rw [hlen]; exact ha)
  have h2 := posOf_getAt hdist b (by rw [hlen]; exact hb)
  rw [← h1, he, h2]

/-- The cycle fold read at the walk: `cyclesOf` is the fold
over the key range taking each unwalked place's orbit. -/
private theorem cyclesOf_read (pi : List Nat) :
    cyclesOf pi
      = ((List.range pi.length).foldl (fun st i =>
          if 0 < ground.countOf i st.2 then st
          else
            (st.1 ++ [cycGo pi i pi.length i],
             st.2 ++ cycGo pi i pi.length i))
          (([], []) : List (List Nat) × List Nat)).1 := rfl

/-- The walk's pack: against a distinct emitted trace chained from
the start and a fuel covering the range, the walk's members sit in
the range, close under the assignment up to the start's return,
are fresh off the trace, distinct, iterates of the entry, hold the
entry, and reach the start's preimage — the budget forcing the
return before the fuel runs out (the pigeonhole at the range). -/
private theorem cycM_pack (k : Nat) {π : List Nat}
    (hπ : 0 < ground.countOf π (perms k)) (i : Nat) :
    ∀ (fuel : Nat) (j : Nat) (seen : List Nat), j < k →
      (∀ x, ground.countOf x seen ≤ 1) →
      (∀ x, 0 < ground.countOf x seen → x < k) →
      ground.countOf j seen = 0 →
      ground.getAt 0 (seen ++ [j]) 0 = i →
      (∀ t, t + 1 < (seen ++ [j]).length →
        ground.getAt 0 (seen ++ [j]) (t + 1)
          = ground.getAt 0 π (ground.getAt 0 (seen ++ [j]) t)) →
      k ≤ fuel + seen.length →
      (∀ p, 0 < ground.countOf p (cycGo π i fuel j) → p < k)
        ∧ (∀ p, 0 < ground.countOf p (cycGo π i fuel j) →
            ground.getAt 0 π p = i
              ∨ 0 < ground.countOf (ground.getAt 0 π p)
                  (cycGo π i fuel j))
        ∧ (∀ p, 0 < ground.countOf p (cycGo π i fuel j) →
            ground.countOf p seen = 0)
        ∧ (∀ p, ground.countOf p (cycGo π i fuel j) ≤ 1)
        ∧ (∀ p, 0 < ground.countOf p (cycGo π i fuel j) →
            ∃ t, p = iterP π t j)
        ∧ 0 < ground.countOf j (cycGo π i fuel j)
        ∧ (∃ p, 0 < ground.countOf p (cycGo π i fuel j)
            ∧ ground.getAt 0 π p = i) := by
  obtain ⟨hπlen, hπdist, hπval, hπocc⟩ := perm_member_reads hπ
  intro fuel
  induction fuel with
  | zero =>
    intro j seen hj hsd hsk hjf _ _ hbud
    exfalso
    have hlen := ground.length_le_of_distinct (seen ++ [j]) k
      (ground.snoc_distinct hsd hjf) (ground.snoc_lt hsk hj)
    rw [ground.length_append] at hlen
    have hbud' : k ≤ seen.length := by
      rw [Nat.zero_add] at hbud
      exact hbud
    have habs : seen.length + 1 ≤ seen.length :=
      Nat.le_trans hlen hbud'
    exact absurd habs (Nat.not_succ_le_self seen.length)
  | succ fuel ih =>
    intro j seen hj hsd hsk hjf hhead hchain hbud
    by_cases hg : ground.getAt 0 π j = i
    · have hstep : cycGo π i (fuel + 1) j = [j] := by
        show j :: (if ground.getAt 0 π j == i then []
          else cycGo π i fuel (ground.getAt 0 π j)) = [j]
        rw [ground.eqBeqOf hg, if_pos rfl]
      rw [hstep]
      have hone : ∀ p : Nat,
          ground.countOf p [j] = if p = j then 1 else 0 :=
        fun p => (ground.countOf_cons p j ([] : List Nat)).trans
          (Nat.add_zero _)
      have hmem : ∀ p : Nat, 0 < ground.countOf p [j] → p = j := by
        intro p hp
        by_cases hpj : p = j
        · exact hpj
        · rw [hone p, if_neg hpj] at hp
          exact absurd hp (Nat.lt_irrefl 0)
      have hjj : 0 < ground.countOf j [j] := by
        rw [hone j, if_pos rfl]
        exact Nat.succ_pos 0
      refine ⟨?_, ?_, ?_, ?_, ?_, hjj, ⟨j, hjj, hg⟩⟩
      · intro p hp
        rw [hmem p hp]
        exact hj
      · intro p hp
        rw [hmem p hp]
        exact Or.inl hg
      · intro p hp
        rw [hmem p hp]
        exact hjf
      · intro p
        rw [hone p]
        by_cases hpj : p = j
        · rw [if_pos hpj]
          exact Nat.le_refl 1
        · rw [if_neg hpj]
          exact Nat.le_succ 0
      · intro p hp
        exact ⟨0, hmem p hp⟩
    · have hbeq : (ground.getAt 0 π j == i) = false := by
        cases hbe : (ground.getAt 0 π j == i) with
        | false => rfl
        | true => exact absurd (ground.beqEqOf hbe) hg
      have hstep : cycGo π i (fuel + 1) j
          = j :: cycGo π i fuel (ground.getAt 0 π j) := by
        show j :: (if ground.getAt 0 π j == i then []
          else cycGo π i fuel (ground.getAt 0 π j)) = _
        rw [hbeq,
          if_neg (fun h : false = true => Bool.noConfusion h)]
      have hj' : ground.getAt 0 π j < k :=
        hπval _ (ground.countOf_getAt_pos 0 π j (by rw [hπlen]; exact hj))
      have hlen_tr : (seen ++ [j]).length = seen.length + 1 := by
        rw [ground.length_append]
        rfl
      have hfresh : ground.countOf (ground.getAt 0 π j)
          (seen ++ [j]) = 0 := by
        match Nat.eq_zero_or_pos (ground.countOf (ground.getAt 0 π j)
            (seen ++ [j])) with
        | .inl h => exact h
        | .inr hpos =>
          exfalso
          match ground.getAt_of_mem 0
              (ground.mem_of_countOf_pos _ _ hpos) with
          | ⟨t, ht, hte⟩ =>
            match t with
            | 0 =>
              rw [hhead] at hte
              exact hg hte.symm
            | s + 1 =>
              have hchs := hchain s ht
              have hpp : ground.getAt 0 π
                  (ground.getAt 0 (seen ++ [j]) s)
                  = ground.getAt 0 π j := by
                rw [← hchs, hte]
              have hs_lt : s < (seen ++ [j]).length :=
                Nat.lt_of_succ_lt ht
              have htrs_lt : ground.getAt 0 (seen ++ [j]) s < k :=
                ground.snoc_lt hsk hj _
                  (ground.countOf_getAt_pos 0 (seen ++ [j]) s hs_lt)
              have hsj : ground.getAt 0 (seen ++ [j]) s = j :=
                perm_inj k hπ _ j htrs_lt hj hpp
              have hs_seen : s < seen.length := by
                rw [hlen_tr] at ht
                exact Nat.lt_of_succ_lt_succ ht
              have hjs : 0 < ground.countOf j seen := by
                rw [← hsj, ground.getAt_append 0 seen [j] s,
                  if_pos hs_seen]
                exact ground.countOf_getAt_pos 0 seen s hs_seen
              rw [hjf] at hjs
              exact absurd hjs (Nat.lt_irrefl 0)
      have hhead' : ground.getAt 0
          ((seen ++ [j]) ++ [ground.getAt 0 π j]) 0 = i := by
        rw [ground.getAt_append 0 (seen ++ [j]) _ 0,
          if_pos (by rw [hlen_tr]; exact Nat.succ_pos _)]
        exact hhead
      have hchain' : ∀ t,
          t + 1 < ((seen ++ [j]) ++ [ground.getAt 0 π j]).length →
          ground.getAt 0 ((seen ++ [j]) ++ [ground.getAt 0 π j]) (t + 1)
            = ground.getAt 0 π (ground.getAt 0
                ((seen ++ [j]) ++ [ground.getAt 0 π j]) t) := by
        intro t ht
        have hlen2 : ((seen ++ [j]) ++ [ground.getAt 0 π j]).length
            = (seen ++ [j]).length + 1 := by
          rw [ground.length_append]
          rfl
        by_cases hts : t + 1 < (seen ++ [j]).length
        · rw [ground.getAt_append 0 (seen ++ [j]) _ (t + 1),
            if_pos hts, ground.getAt_append 0 (seen ++ [j]) _ t,
            if_pos (Nat.lt_of_succ_lt hts)]
          exact hchain t hts
        · have hte : t + 1 = (seen ++ [j]).length := by
            rw [hlen2] at ht
            exact Nat.le_antisymm (Nat.le_of_lt_succ ht)
              (Nat.le_of_not_lt hts)
          have htl : t < (seen ++ [j]).length := by
            rw [← hte]
            exact Nat.lt_succ_self t
          have hts2 : t = seen.length := by
            rw [hlen_tr] at hte
            exact Nat.succ.inj hte
          have hgj : ground.getAt 0 (seen ++ [j]) t = j := by
            rw [ground.getAt_append 0 seen [j] t, hts2,
              if_neg (Nat.lt_irrefl _), Nat.sub_self]
            rfl
          rw [ground.getAt_append 0 (seen ++ [j]) _ (t + 1),
            if_neg (by rw [hte]; exact Nat.lt_irrefl _), hte,
            Nat.sub_self,
            ground.getAt_append 0 (seen ++ [j]) _ t, if_pos htl, hgj]
          rfl
      have hbud' : k ≤ fuel + (seen ++ [j]).length := by
        rw [hlen_tr, Nat.add_comm seen.length 1, ← Nat.add_assoc]
        exact hbud
      obtain ⟨ia, ib, ic, id2, ie, ig, ihh⟩ := ih (ground.getAt 0 π j)
        (seen ++ [j]) hj' (ground.snoc_distinct hsd hjf)
        (ground.snoc_lt hsk hj) hfresh hhead' hchain' hbud'
      rw [hstep]
      have hsplit : ∀ p, 0 < ground.countOf p
          (j :: cycGo π i fuel (ground.getAt 0 π j)) →
          p = j ∨ 0 < ground.countOf p
            (cycGo π i fuel (ground.getAt 0 π j)) := by
        intro p hp
        by_cases hpj : p = j
        · exact Or.inl hpj
        · rw [ground.countOf_head_ne hpj] at hp
          exact Or.inr hp
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro p hp
        match hsplit p hp with
        | .inl hpj =>
          rw [hpj]
          exact hj
        | .inr hpc => exact ia p hpc
      · intro p hp
        match hsplit p hp with
        | .inl hpj =>
          refine Or.inr ?_
          rw [hpj]
          exact ground.countOf_cons_pos ig
        | .inr hpc =>
          match ib p hpc with
          | .inl hpi => exact Or.inl hpi
          | .inr hpn => exact Or.inr (ground.countOf_cons_pos hpn)
      · intro p hp
        match hsplit p hp with
        | .inl hpj =>
          rw [hpj]
          exact hjf
        | .inr hpc =>
          have hz := ic p hpc
          rw [ground.countOf_snoc] at hz
          exact Nat.eq_zero_of_add_eq_zero_right hz
      · intro p
        by_cases hpj : p = j
        · rw [hpj, ground.countOf_head]
          match Nat.eq_zero_or_pos (ground.countOf j
              (cycGo π i fuel (ground.getAt 0 π j))) with
          | .inl hz =>
            rw [hz]
            exact Nat.le_refl 1
          | .inr hpos =>
            have hz := ic j hpos
            rw [ground.countOf_snoc, if_pos rfl] at hz
            exact Nat.noConfusion hz
        · rw [ground.countOf_head_ne hpj]
          exact id2 p
      · intro p hp
        match hsplit p hp with
        | .inl hpj => exact ⟨0, hpj⟩
        | .inr hpc =>
          match ie p hpc with
          | ⟨t, hpt⟩ =>
            refine ⟨t + 1, ?_⟩
            rw [iterP_succ]
            exact hpt
      · rw [ground.countOf_head]
        exact Nat.succ_pos _
      · match ihh with
        | ⟨p, hpc, hpi⟩ => exact ⟨p, ground.countOf_cons_pos hpc, hpi⟩

/-- The return: from any place the iterates come back — the walk
reaches the start's preimage, whose image closes the orbit. -/
private theorem iter_return (k : Nat) {π : List Nat}
    (hπ : 0 < ground.countOf π (perms k)) (j : Nat)
    (hj : j < k) : ∃ r, iterP π (r + 1) j = j := by
  obtain ⟨_, _, _, _, he, _, hp, hpc, hpi⟩ := cycM_pack k hπ j k j []
    hj (fun _ => Nat.le_succ 0)
    (fun x hx => absurd hx (Nat.lt_irrefl 0)) rfl rfl
    (fun t ht => absurd (Nat.lt_of_succ_lt_succ ht) (Nat.not_lt_zero t))
    (Nat.le_refl k)
  match he hp hpc with
  | ⟨t, hpt⟩ =>
    refine ⟨t, ?_⟩
    show ground.getAt 0 π (iterP π t j) = j
    rw [← hpt]
    exact hpi

/-- The orbit relation is symmetric: a place reading as an iterate
reads its source back, the return closing the gap. -/
private theorem iter_back (k : Nat) {π : List Nat}
    (hπ : 0 < ground.countOf π (perms k)) :
    ∀ (t j p : Nat), j < k → p = iterP π t j →
      ∃ s, j = iterP π s p := by
  obtain ⟨hπlen, _, hπval, _⟩ := perm_member_reads hπ
  intro t
  induction t with
  | zero =>
    intro j p _ hp
    exact ⟨0, hp.symm⟩
  | succ t ihb =>
    intro j p hj hp
    have hj' : ground.getAt 0 π j < k :=
      hπval _ (ground.countOf_getAt_pos 0 π j (by rw [hπlen]; exact hj))
    have hp' : p = iterP π t (ground.getAt 0 π j) := by
      rw [← iterP_succ]
      exact hp
    match ihb (ground.getAt 0 π j) p hj' hp' with
    | ⟨s, hs⟩ =>
      match iter_return k hπ j hj with
      | ⟨r, hr⟩ =>
        refine ⟨r + s, ?_⟩
        rw [iterP_add π r s p, ← hs, ← iterP_succ π r j]
        exact hr.symm

/-- The cycle fold's invariant: the visited list counts as the
cycles' flattening, is distinct, bounded and closed under the
assignment, and every collected cycle is occupied, bounded, closed,
and its members the head's iterates. -/
private def cycInv (k : Nat) (π : List Nat)
    (st : List (List Nat) × List Nat) : Prop :=
  (∀ q, ground.countOf q st.2
      = ground.countOf q (st.1.flatMap (fun c => c)))
    ∧ (∀ q, ground.countOf q st.2 ≤ 1)
    ∧ (∀ q, 0 < ground.countOf q st.2 → q < k)
    ∧ (∀ q, 0 < ground.countOf q st.2 →
        0 < ground.countOf (ground.getAt 0 π q) st.2)
    ∧ (∀ c, 0 < ground.countOf c st.1 →
        0 < c.length
          ∧ (∀ p, 0 < ground.countOf p c → p < k)
          ∧ (∀ p, 0 < ground.countOf p c →
              0 < ground.countOf (ground.getAt 0 π p) c)
          ∧ (∀ p, 0 < ground.countOf p c →
              ∃ t, p = iterP π t (ground.getAt 0 c 0)))

/-- The visited list is closed under the iterates. -/
private theorem visited_iter (k : Nat) (π : List Nat)
    {st : List (List Nat) × List Nat} (hinv : cycInv k π st) :
    ∀ (s q : Nat), 0 < ground.countOf q st.2 →
      0 < ground.countOf (iterP π s q) st.2 := by
  intro s
  induction s with
  | zero => exact fun q hq => hq
  | succ s ihs =>
    intro q hq
    exact hinv.2.2.2.1 _ (ihs q hq)

/-- The fold's step keeps the invariant and grows the visited list
onto the processed key: a walked key adds its whole orbit — fresh
off the visited list, the return reading any met place back to the
start against the guard. -/
private theorem cycStep_pack (k : Nat) {π : List Nat}
    (hπ : 0 < ground.countOf π (perms k))
    (st : List (List Nat) × List Nat) (x : Nat) (hxk : x < k)
    (hinv : cycInv k π st) :
    cycInv k π (if 0 < ground.countOf x st.2 then st
        else (st.1 ++ [cycGo π x k x], st.2 ++ cycGo π x k x))
      ∧ (∀ q, 0 < ground.countOf q st.2 →
          0 < ground.countOf q
            (if 0 < ground.countOf x st.2 then st
              else (st.1 ++ [cycGo π x k x],
                st.2 ++ cycGo π x k x)).2)
      ∧ 0 < ground.countOf x
          (if 0 < ground.countOf x st.2 then st
            else (st.1 ++ [cycGo π x k x], st.2 ++ cycGo π x k x)).2 := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := hinv
  by_cases hx : 0 < ground.countOf x st.2
  · rw [if_pos hx]
    exact ⟨⟨i1, i2, i3, i4, i5⟩, fun q hq => hq, hx⟩
  · rw [if_neg hx]
    have hxf : ground.countOf x st.2 = 0 :=
      match Nat.eq_zero_or_pos (ground.countOf x st.2) with
      | .inl h => h
      | .inr h => absurd h hx
    obtain ⟨wa, wb, _, wd, we, wg, _⟩ := cycM_pack k hπ x k x []
      hxk (fun _ => Nat.le_succ 0)
      (fun z hz => absurd hz (Nat.lt_irrefl 0)) rfl rfl
      (fun t ht => absurd (Nat.lt_of_succ_lt_succ ht)
        (Nat.not_lt_zero t))
      (Nat.le_refl k)
    have hhead : ground.getAt 0 (cycGo π x k x) 0 = x := by
      match k, hxk with
      | k' + 1, _ => rfl
    have hdisj : ∀ p, 0 < ground.countOf p (cycGo π x k x) →
        ground.countOf p st.2 = 0 := by
      intro p hp
      match Nat.eq_zero_or_pos (ground.countOf p st.2) with
      | .inl h => exact h
      | .inr hpos =>
        exfalso
        match we p hp with
        | ⟨t, hpt⟩ =>
          match iter_back k hπ t x p hxk hpt with
          | ⟨s, hxs⟩ =>
            refine hx ?_
            rw [hxs]
            exact visited_iter k π ⟨i1, i2, i3, i4, i5⟩ s p hpos
    have hclosure : ∀ p, 0 < ground.countOf p (cycGo π x k x) →
        0 < ground.countOf (ground.getAt 0 π p) (cycGo π x k x) := by
      intro p hp
      match wb p hp with
      | .inl hpi =>
        rw [hpi]
        exact wg
      | .inr hpn => exact hpn
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro q
      show ground.countOf q (st.2 ++ cycGo π x k x) = _
      rw [ground.countOf_append,
        ground.flatMap_append (fun c => c) st.1 [cycGo π x k x],
        ground.countOf_append, i1 q]
      refine congrArg (Nat.add _) ?_
      show ground.countOf q (cycGo π x k x)
        = ground.countOf q (cycGo π x k x ++ [])
      rw [ground.countOf_append]
      exact (Nat.add_zero _).symm
    · intro q
      show ground.countOf q (st.2 ++ cycGo π x k x) ≤ 1
      rw [ground.countOf_append]
      match Nat.eq_zero_or_pos (ground.countOf q (cycGo π x k x)) with
      | .inl hz =>
        rw [hz, Nat.add_zero]
        exact i2 q
      | .inr hp =>
        rw [hdisj q hp, Nat.zero_add]
        exact wd q
    · intro q hq
      match ground.countOf_append_split q st.2 (cycGo π x k x) hq with
      | .inl h => exact i3 q h
      | .inr h => exact wa q h
    · intro q hq
      match ground.countOf_append_split q st.2 (cycGo π x k x) hq with
      | .inl h => exact ground.countOf_append_left _ _ (i4 q h)
      | .inr h => exact ground.countOf_append_right _ _ (hclosure q h)
    · intro c hc
      have hc' : 0 < ground.countOf c st.1
          ∨ 0 < ground.countOf c [cycGo π x k x] :=
        ground.countOf_append_split c st.1 [cycGo π x k x] hc
      match hc' with
      | .inl h => exact i5 c h
      | .inr h =>
        have hcx : c = cycGo π x k x := by
          by_cases hce : c = cycGo π x k x
          · exact hce
          · have hz : ground.countOf c [cycGo π x k x] = 0 :=
              ground.countOf_head_ne hce []
            rw [hz] at h
            exact absurd h (Nat.lt_irrefl 0)
        rw [hcx]
        refine ⟨ground.length_pos_of_countOf wg, wa, hclosure, ?_⟩
        rw [hhead]
        exact we
    · intro q hq
      exact ground.countOf_append_left _ _ hq
    · exact ground.countOf_append_right _ st.2 wg

/-- The cycle fold's pack over any key list within the range: the
invariant rides the fold, the visited list only grows, and every
processed key lands in it. -/
private theorem cyclesFold_pack (k : Nat) {π : List Nat}
    (hπ : 0 < ground.countOf π (perms k)) :
    ∀ (l : List Nat) (st : List (List Nat) × List Nat),
      (∀ x, 0 < ground.countOf x l → x < k) →
      cycInv k π st →
      cycInv k π (l.foldl (fun st i =>
          if 0 < ground.countOf i st.2 then st
          else (st.1 ++ [cycGo π i k i], st.2 ++ cycGo π i k i)) st)
        ∧ (∀ q, 0 < ground.countOf q st.2 →
            0 < ground.countOf q (l.foldl (fun st i =>
              if 0 < ground.countOf i st.2 then st
              else (st.1 ++ [cycGo π i k i],
                st.2 ++ cycGo π i k i)) st).2)
        ∧ (∀ q, 0 < ground.countOf q l →
            0 < ground.countOf q (l.foldl (fun st i =>
              if 0 < ground.countOf i st.2 then st
              else (st.1 ++ [cycGo π i k i],
                st.2 ++ cycGo π i k i)) st).2)
  | [], st, _, hinv =>
    ⟨hinv, fun _ hq => hq, fun q hq => absurd hq (Nat.lt_irrefl 0)⟩
  | x :: l, st, hlk, hinv => by
    have hxk : x < k := hlk x (by
      rw [ground.countOf_head]
      exact Nat.succ_pos _)
    obtain ⟨sinv, sgrow, sx⟩ := cycStep_pack k hπ st x hxk hinv
    obtain ⟨finv, fgrow, fcov⟩ := cyclesFold_pack k hπ l
      (if 0 < ground.countOf x st.2 then st
        else (st.1 ++ [cycGo π x k x], st.2 ++ cycGo π x k x))
      (fun z hz => hlk z (ground.countOf_cons_pos hz)) sinv
    refine ⟨finv, ?_, ?_⟩
    · intro q hq
      exact fgrow q (sgrow q hq)
    · intro q hq
      by_cases hqx : q = x
      · rw [hqx]
        exact fgrow x sx
      · rw [ground.countOf_head_ne hqx] at hq
        exact fcov q hq

/-- The cycles' pack: `cyclesOf` at an enumeration member
covers every place exactly once — the flattening distinct and the
range covered — and each cycle is occupied, bounded, closed under
the assignment, and its members the head's iterates. -/
theorem cycles_pack (k : Nat) {π : List Nat}
    (hπ : 0 < ground.countOf π (perms k)) :
    (∀ q, ground.countOf q
        ((cyclesOf π).flatMap (fun c => c)) ≤ 1)
      ∧ (∀ q, q < k →
          0 < ground.countOf q
            ((cyclesOf π).flatMap (fun c => c)))
      ∧ (∀ c, 0 < ground.countOf c (cyclesOf π) →
          0 < c.length
            ∧ (∀ p, 0 < ground.countOf p c → p < k)
            ∧ (∀ p, 0 < ground.countOf p c →
                0 < ground.countOf (ground.getAt 0 π p) c)
            ∧ (∀ p, 0 < ground.countOf p c →
                ∃ t, p = iterP π t (ground.getAt 0 c 0))) := by
  obtain ⟨hπlen, _, _, _⟩ := perm_member_reads hπ
  have hread := cyclesOf_read π
  rw [hπlen] at hread
  obtain ⟨⟨f1, f2, _, _, f5⟩, _, fcov⟩ := cyclesFold_pack k hπ
    (List.range k) (([], []) : List (List Nat) × List Nat)
    (fun x hx => ground.ltOfMem hx)
    ⟨fun _ => rfl, fun _ => Nat.le_succ 0,
      fun _ hq => absurd hq (Nat.lt_irrefl 0),
      fun _ hq => absurd hq (Nat.lt_irrefl 0),
      fun _ hc => absurd hc (Nat.lt_irrefl 0)⟩
  refine ⟨?_, ?_, ?_⟩
  · intro q
    rw [hread, ← f1 q]
    exact f2 q
  · intro q hq
    rw [hread, ← f1 q]
    exact fcov q (ground.countOf_range_pos hq)
  · intro c hc
    rw [hread] at hc
    exact f5 c hc

/-! The relabeling transport (`con:places`' composition sentence:
a permutation composed between a second permutation and its
inverse permutation walks the composed orbits at the images, the
cycle count one value across the composition; consumed by
`rem:kernel`'s gauge-mode clause): the wiring relabeled through a
place permutation is again a wiring, the partner relabeling
composes back to the wiring, and the cycle count is the wiring's
own — one orbit word per orbit either side. -/

/-- The place enumeration is distinct: the permutations are the
unit-content monomials, whose enumeration lists each once. -/
theorem perms_distinct : ∀ k : Nat, ground.distinctList (perms k) :=
  fun k => monomialsAt_distinct (List.replicate k 1)

/-- A cell's occupied key occupies the cells' flattening. -/
private theorem flat_pos {q : Nat} :
    ∀ (D : List (List Nat)) (i : Nat), i < D.length →
      0 < ground.countOf q (ground.getAt ([] : List Nat) D i) →
      0 < ground.countOf q (D.flatMap (fun c => c))
  | [], i, hi, _ => absurd hi (Nat.not_lt_zero i)
  | a :: t, 0, _, h => by
    have ha : 0 < ground.countOf q a := h
    show 0 < ground.countOf q (a ++ t.flatMap (fun c => c))
    rw [ground.countOf_append]
    exact Nat.lt_of_lt_of_le ha (Nat.le_add_right _ _)
  | a :: t, i + 1, hi, h => by
    have ht : 0 < ground.countOf q (t.flatMap (fun c => c)) :=
      flat_pos t i (Nat.lt_of_succ_lt_succ hi) h
    show 0 < ground.countOf q (a ++ t.flatMap (fun c => c))
    rw [ground.countOf_append]
    exact Nat.lt_of_lt_of_le ht (Nat.le_add_left _ _)

/-- An occupied key of the flattening names its cell. -/
private theorem flat_index {q : Nat} :
    ∀ D : List (List Nat),
      0 < ground.countOf q (D.flatMap (fun c => c)) →
      ∃ i, i < D.length
        ∧ 0 < ground.countOf q (ground.getAt ([] : List Nat) D i)
  | [], h => absurd h (Nat.lt_irrefl 0)
  | a :: t, h => by
    have h' : 0 < ground.countOf q (a ++ t.flatMap (fun c => c)) :=
      h
    match ground.countOf_append_split q a _ h' with
    | .inl hl => exact ⟨0, Nat.succ_pos _, hl⟩
    | .inr hrt =>
      match flat_index t hrt with
      | ⟨i, hi, hq⟩ => exact ⟨i + 1, Nat.succ_lt_succ hi, hq⟩

/-- Two cells sharing a key put the key twice in the flattening. -/
private theorem two_cells {q : Nat} :
    ∀ (D : List (List Nat)) (s s' : Nat), s < s' → s' < D.length →
      0 < ground.countOf q (ground.getAt ([] : List Nat) D s) →
      0 < ground.countOf q (ground.getAt ([] : List Nat) D s') →
      2 ≤ ground.countOf q (D.flatMap (fun c => c))
  | [], _, s', _, hs', _, _ => absurd hs' (Nat.not_lt_zero s')
  | _ :: _, 0, 0, hlt, _, _, _ => absurd hlt (Nat.lt_irrefl 0)
  | a :: t, 0, s' + 1, _, hs', hq, hq' => by
    have ha : 0 < ground.countOf q a := hq
    have ht : 0 < ground.countOf q (t.flatMap (fun c => c)) :=
      flat_pos t s' (Nat.lt_of_succ_lt_succ hs') hq'
    show 2 ≤ ground.countOf q (a ++ t.flatMap (fun c => c))
    rw [ground.countOf_append]
    exact Nat.add_le_add ha ht
  | _ :: _, s + 1, 0, hlt, _, _, _ =>
    absurd hlt (Nat.not_lt_zero (s + 1))
  | a :: t, s + 1, s' + 1, hlt, hs', hq, hq' => by
    have h2 : 2 ≤ ground.countOf q (t.flatMap (fun c => c)) :=
      two_cells t s s' (Nat.lt_of_succ_lt_succ hlt)
        (Nat.lt_of_succ_lt_succ hs') hq hq'
    show 2 ≤ ground.countOf q (a ++ t.flatMap (fun c => c))
    rw [ground.countOf_append]
    exact Nat.le_trans h2 (Nat.le_add_left _ _)

/-- The hit fold keeps a read the accumulator already holds. -/
private theorem hitFold_keep (P : Nat → Prop) [DecidablePred P] :
    ∀ (l : List Nat) (acc : Nat), P acc →
      P (l.foldl (fun a i => if P i then i else a) acc)
  | [], _, h => h
  | i :: t, acc, h => by
    show P (t.foldl (fun a j => if P j then j else a)
      (if P i then i else acc))
    by_cases hi : P i
    · rw [if_pos hi]
      exact hitFold_keep P t i hi
    · rw [if_neg hi]
      exact hitFold_keep P t acc h

/-- The hit fold reads a key the family holds at the read. -/
private theorem hitFold_hit (P : Nat → Prop) [DecidablePred P] :
    ∀ (l : List Nat) (acc i : Nat), 0 < ground.countOf i l → P i →
      P (l.foldl (fun a j => if P j then j else a) acc)
  | [], _, i, hi, _ => absurd hi (Nat.lt_irrefl 0)
  | b :: t, acc, i, hi, hpi => by
    show P (t.foldl (fun a j => if P j then j else a)
      (if P b then b else acc))
    by_cases hib : i = b
    · have hpb : P b := by rw [← hib]; exact hpi
      rw [if_pos hpb]
      exact hitFold_keep P t b hpb
    · rw [ground.countOf_head_ne hib] at hi
      exact hitFold_hit P t _ i hi hpi

/-- A key occupying a cell read names a key of the cell list: past
the list the read is the vacant cell. -/
private theorem cellIndex_lt {q : Nat} (D : List (List Nat))
    (i : Nat)
    (h : 0 < ground.countOf q (ground.getAt ([] : List Nat) D i)) :
    i < D.length := by
  by_cases hi : i < D.length
  · exact hi
  · rw [ground.getAt_over ([] : List Nat) D i
      (Nat.le_of_not_lt hi)] at h
    exact absurd h (Nat.lt_irrefl 0)

/-- A key family injective on the first list's keys and landing in
the second's is a pigeonhole: the first list is no longer than the
second. -/
private theorem length_le_of_index {C D : List (List Nat)}
    (g : Nat → Nat)
    (hlt : ∀ s, s < C.length → g s < D.length)
    (hinj : ∀ s s', s < C.length → s' < C.length →
      g s = g s' → s = s') :
    C.length ≤ D.length := by
  have hLd : ∀ z, ground.countOf z
      ((List.range C.length).map g) ≤ 1 := by
    intro z
    match Nat.eq_zero_or_pos
        (ground.countOf z ((List.range C.length).map g)) with
    | .inl hz =>
      rw [hz]
      exact Nat.zero_le 1
    | .inr hpos =>
      match ground.mem_map_of g (List.range C.length) z
          (ground.mem_of_countOf_pos z _ hpos) with
      | ⟨y, hy, hgy⟩ =>
        have hyl : y < C.length :=
          ground.ltOfMem (ground.countOf_pos_of_mem hy)
        rw [ground.countOf_map_iff g (List.range C.length) z y
          (fun v hv => ⟨fun he => hinj y v hyl (ground.ltOfMem hv)
              (by rw [hgy]; exact he),
            fun he => by rw [← he, hgy]⟩)]
        exact ground.distinctList_all
          (ground.distinctList_range C.length) y
  have hLlt : ∀ z, 0 < ground.countOf z
      ((List.range C.length).map g) → z < D.length := by
    intro z hz
    match ground.mem_map_of g (List.range C.length) z
        (ground.mem_of_countOf_pos z _ hz) with
    | ⟨y, hy, hgy⟩ =>
      rw [← hgy]
      exact hlt y (ground.ltOfMem (ground.countOf_pos_of_mem hy))
  have hfin := ground.length_le_of_distinct
    ((List.range C.length).map g) D.length hLd hLlt
  rw [ground.length_map, ground.length_range] at hfin
  exact hfin

/-- A cell closed under the assignment holds every iterate of its
members. -/
private theorem cyc_iter {π c : List Nat}
    (hcl : ∀ x, 0 < ground.countOf x c →
      0 < ground.countOf (ground.getAt 0 π x) c) :
    ∀ (t x : Nat), 0 < ground.countOf x c →
      0 < ground.countOf (iterP π t x) c := by
  intro t
  induction t with
  | zero => exact fun _ hx => hx
  | succ t ih =>
    intro x hx
    exact hcl _ (ih x hx)

/-- The relabeled wiring's entry: the wiring read at the partner
relabeling's key, relabeled. -/
private theorem getAt_relab (n : Nat) (comp r : List Nat) (i : Nat)
    (hi : i < n) :
    ground.getAt 0 ((invPerm n r).map (fun j =>
        ground.getAt 0 r (ground.getAt 0 comp j))) i
      = ground.getAt 0 r (ground.getAt 0 comp
          (ground.getAt 0 (invPerm n r) i)) :=
  ground.getAt_map 0 0 (fun j =>
      ground.getAt 0 r (ground.getAt 0 comp j)) (invPerm n r) i
    (by rw [length_invPerm]; exact hi)

/-- The iterates transport along the relabeling: the relabeled
wiring's iterate at a relabeled place is the wiring's iterate
relabeled. -/
private theorem iterP_transport (n : Nat) {comp r p : List Nat}
    (hc : 0 < ground.countOf comp (perms n))
    (hr : 0 < ground.countOf r (perms n))
    (hpe : ∀ i, i < n → ground.getAt 0 p i
      = ground.getAt 0 r (ground.getAt 0 comp
          (ground.getAt 0 (invPerm n r) i))) :
    ∀ (t x : Nat), x < n →
      iterP p t (ground.getAt 0 r x)
        = ground.getAt 0 r (iterP comp t x) := by
  obtain ⟨hrlen, hrdist, hrval, _⟩ := perm_member_reads hr
  intro t
  induction t with
  | zero => exact fun _ _ => rfl
  | succ t ih =>
    intro x hx
    have hz : iterP comp t x < n := iterP_lt n hc t x hx
    have hzlen : iterP comp t x < r.length := by
      rw [hrlen]
      exact hz
    have hry : ground.getAt 0 r (iterP comp t x) < n :=
      hrval _ (ground.countOf_getAt_pos 0 r _ hzlen)
    show ground.getAt 0 p (iterP p t (ground.getAt 0 r x))
      = ground.getAt 0 r
          (ground.getAt 0 comp (iterP comp t x))
    rw [ih x hx, hpe _ hry, getAt_invPerm n r hry,
      posOf_getAt hrdist (iterP comp t x) hzlen]

/-- The relabeled wiring is an enumeration member: the relabeling
is the permuted display of the permuted display. -/
theorem transport_member (n : Nat) {comp r : List Nat}
    (hc : 0 < ground.countOf comp (perms n))
    (hr : 0 < ground.countOf r (perms n)) :
    0 < ground.countOf ((invPerm n r).map (fun j =>
      ground.getAt 0 r (ground.getAt 0 comp j))) (perms n) := by
  have hmap : (invPerm n r).map (fun j =>
      ground.getAt 0 r (ground.getAt 0 comp j))
      = expo r (expo comp (invPerm n r)) := by
    show _ = ((invPerm n r).map (ground.getAt 0 comp)).map
      (ground.getAt 0 r)
    rw [ground.map_map (ground.getAt 0 comp) (ground.getAt 0 r)
      (invPerm n r)]
  rw [hmap]
  exact expo_member n hr (expo_member n hc (invPerm_member n hr))

/-- The partner relabeling's entry reads the wiring back. -/
private theorem relab_back (n : Nat) {comp r p : List Nat}
    (hc : 0 < ground.countOf comp (perms n))
    (hr : 0 < ground.countOf r (perms n))
    (hpe : ∀ i, i < n → ground.getAt 0 p i
      = ground.getAt 0 r (ground.getAt 0 comp
          (ground.getAt 0 (invPerm n r) i)))
    (i : Nat) (hi : i < n) :
    ground.getAt 0 (invPerm n r) (ground.getAt 0 p
        (ground.getAt 0 (invPerm n (invPerm n r)) i))
      = ground.getAt 0 comp i := by
  obtain ⟨hrlen, hrdist, hrval, _⟩ := perm_member_reads hr
  obtain ⟨hclen, _, hcval, _⟩ := perm_member_reads hc
  have hilen : i < r.length := by
    rw [hrlen]
    exact hi
  have hy : ground.getAt 0 r i < n :=
    hrval _ (ground.countOf_getAt_pos 0 r i hilen)
  have hci : ground.getAt 0 comp i < n :=
    hcval _ (ground.countOf_getAt_pos 0 comp i (by
      rw [hclen]
      exact hi))
  have hcilen : ground.getAt 0 comp i < r.length := by
    rw [hrlen]
    exact hci
  have hz : ground.getAt 0 r (ground.getAt 0 comp i) < n :=
    hrval _ (ground.countOf_getAt_pos 0 r _ hcilen)
  rw [invPerm_invPerm n hr, hpe _ hy, getAt_invPerm n r hy,
    posOf_getAt hrdist i hilen, getAt_invPerm n r hz,
    posOf_getAt hrdist (ground.getAt 0 comp i) hcilen]

/-- The partner relabeling composes to the wiring: relabeling the
relabeled wiring through the flipped assignment reads the wiring
back. -/
theorem transport_invol (n : Nat) {comp r : List Nat}
    (hc : 0 < ground.countOf comp (perms n))
    (hr : 0 < ground.countOf r (perms n)) :
    (invPerm n (invPerm n r)).map (fun j =>
      ground.getAt 0 (invPerm n r)
        (ground.getAt 0 ((invPerm n r).map (fun i =>
          ground.getAt 0 r (ground.getAt 0 comp i))) j))
    = comp := by
  obtain ⟨hclen, _, _, _⟩ := perm_member_reads hc
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [ground.length_map, length_invPerm, hclen]
  · intro i hi
    rw [ground.length_map, length_invPerm] at hi
    rw [ground.getAt_map 0 0 _ (invPerm n (invPerm n r)) i
      (by rw [length_invPerm]; exact hi)]
    exact relab_back n hc hr (getAt_relab n comp r) i hi

/-- The half comparison: the wiring's cycle count is at or below
the relabeled wiring's, each cycle's relabeled head naming its own
cell of the relabeled wiring's cycles. -/
private theorem cycles_le (n : Nat) {comp r p : List Nat}
    (hc : 0 < ground.countOf comp (perms n))
    (hr : 0 < ground.countOf r (perms n))
    (hp : 0 < ground.countOf p (perms n))
    (hpe : ∀ i, i < n → ground.getAt 0 p i
      = ground.getAt 0 r (ground.getAt 0 comp
          (ground.getAt 0 (invPerm n r) i))) :
    (cyclesOf comp).length ≤ (cyclesOf p).length := by
  obtain ⟨hrlen, _, hrval, _⟩ := perm_member_reads hr
  obtain ⟨hCflat, _, hCcell⟩ := cycles_pack n hc
  obtain ⟨_, hDcov, hDcell⟩ := cycles_pack n hp
  have hcellMem : ∀ s, s < (cyclesOf comp).length →
      0 < ground.countOf
        (ground.getAt ([] : List Nat) (cyclesOf comp) s)
        (cyclesOf comp) := fun s hs =>
    ground.countOf_getAt_pos ([] : List Nat) (cyclesOf comp) s hs
  have hheadMem : ∀ s, s < (cyclesOf comp).length →
      0 < ground.countOf (ground.getAt 0
          (ground.getAt ([] : List Nat) (cyclesOf comp) s) 0)
        (ground.getAt ([] : List Nat) (cyclesOf comp) s) :=
    fun s hs => ground.countOf_getAt_pos 0 _ 0
      (hCcell _ (hcellMem s hs)).1
  have hheadLt : ∀ s, s < (cyclesOf comp).length →
      ground.getAt 0
        (ground.getAt ([] : List Nat) (cyclesOf comp) s) 0 < n :=
    fun s hs => (hCcell _ (hcellMem s hs)).2.1 _ (hheadMem s hs)
  have hcellEq : ∀ (x s s' : Nat), s < (cyclesOf comp).length →
      s' < (cyclesOf comp).length →
      0 < ground.countOf x
        (ground.getAt ([] : List Nat) (cyclesOf comp) s) →
      0 < ground.countOf x
        (ground.getAt ([] : List Nat) (cyclesOf comp) s') →
      s = s' := by
    intro x s s' hs hs' h1 h2
    match Nat.lt_or_ge s s' with
    | .inl hlt =>
      exact absurd (Nat.le_trans
        (two_cells (cyclesOf comp) s s' hlt hs' h1 h2)
        (hCflat x)) (Nat.not_succ_le_self 1)
    | .inr hge =>
      match Nat.lt_or_ge s' s with
      | .inl hlt =>
        exact absurd (Nat.le_trans
          (two_cells (cyclesOf comp) s' s hlt hs h2 h1)
          (hCflat x)) (Nat.not_succ_le_self 1)
      | .inr hge2 => exact Nat.le_antisymm hge2 hge
  have hcross : ∀ (s s' k : Nat), s < (cyclesOf comp).length →
      s' < (cyclesOf comp).length →
      ground.getAt 0 r (ground.getAt 0
          (ground.getAt ([] : List Nat) (cyclesOf comp) s') 0)
        = iterP p k (ground.getAt 0 r (ground.getAt 0
            (ground.getAt ([] : List Nat) (cyclesOf comp) s) 0)) →
      s = s' := by
    intro s s' k hs hs' hk
    rw [iterP_transport n hc hr hpe k _ (hheadLt s hs)] at hk
    have h1 : ground.getAt 0
        (ground.getAt ([] : List Nat) (cyclesOf comp) s') 0
        = iterP comp k (ground.getAt 0
            (ground.getAt ([] : List Nat) (cyclesOf comp) s) 0) :=
      perm_inj n hr _ _ (hheadLt s' hs')
        (iterP_lt n hc k _ (hheadLt s hs)) hk
    refine hcellEq _ s s' hs hs' ?_ (hheadMem s' hs')
    rw [h1]
    exact cyc_iter (hCcell _ (hcellMem s hs)).2.2.1 k _
      (hheadMem s hs)
  have hA : ∀ s, s < (cyclesOf comp).length →
      0 < ground.countOf (ground.getAt 0 r (ground.getAt 0
          (ground.getAt ([] : List Nat) (cyclesOf comp) s) 0))
        (ground.getAt ([] : List Nat) (cyclesOf p)
          ((List.range (cyclesOf p).length).foldl (fun a i =>
            if 0 < ground.countOf (ground.getAt 0 r (ground.getAt 0
                (ground.getAt ([] : List Nat) (cyclesOf comp) s) 0))
                (ground.getAt ([] : List Nat) (cyclesOf p) i)
              then i else a) (cyclesOf p).length)) := by
    intro s hs
    have hq : ground.getAt 0 r (ground.getAt 0
        (ground.getAt ([] : List Nat) (cyclesOf comp) s) 0) < n :=
      hrval _ (ground.countOf_getAt_pos 0 r _ (by
        rw [hrlen]
        exact hheadLt s hs))
    match flat_index (cyclesOf p) (hDcov _ hq) with
    | ⟨i, hi, hqi⟩ =>
      exact hitFold_hit (fun i => 0 < ground.countOf
          (ground.getAt 0 r (ground.getAt 0
            (ground.getAt ([] : List Nat) (cyclesOf comp) s) 0))
          (ground.getAt ([] : List Nat) (cyclesOf p) i))
        (List.range (cyclesOf p).length) (cyclesOf p).length i
        (ground.countOf_range_pos hi) hqi
  refine length_le_of_index (fun s =>
    (List.range (cyclesOf p).length).foldl (fun a i =>
      if 0 < ground.countOf (ground.getAt 0 r (ground.getAt 0
          (ground.getAt ([] : List Nat) (cyclesOf comp) s) 0))
          (ground.getAt ([] : List Nat) (cyclesOf p) i)
        then i else a) (cyclesOf p).length) ?_ ?_
  · intro s hs
    exact cellIndex_lt (cyclesOf p) _ (hA s hs)
  · intro s s' hs hs' heq
    have h1 := hA s hs
    have h2 := hA s' hs'
    rw [← heq] at h2
    obtain ⟨_, _, _, hiter⟩ := hDcell _
      (ground.countOf_getAt_pos ([] : List Nat) (cyclesOf p) _
        (cellIndex_lt (cyclesOf p) _ h1))
    obtain ⟨a, ha⟩ := hiter _ h1
    obtain ⟨b, hb⟩ := hiter _ h2
    match Nat.le_total a b with
    | .inl hab =>
      match Nat.le.dest hab with
      | ⟨k, hk⟩ =>
        refine hcross s s' k hs hs' ?_
        rw [hb, ← hk, Nat.add_comm a k, iterP_add p k a, ← ha]
    | .inr hba =>
      match Nat.le.dest hba with
      | ⟨k, hk⟩ =>
        refine (hcross s' s k hs' hs ?_).symm
        rw [ha, ← hk, Nat.add_comm b k, iterP_add p k b, ← hb]

/-- The cycle count at a relabeled wiring is the wiring's own: the
orbit words transport along the relabeling, one word per orbit
either side. -/
theorem cyclesOf_transport (n : Nat) {comp r : List Nat}
    (hc : 0 < ground.countOf comp (perms n))
    (hr : 0 < ground.countOf r (perms n)) :
    (cyclesOf ((invPerm n r).map (fun j =>
      ground.getAt 0 r (ground.getAt 0 comp j)))).length
    = (cyclesOf comp).length := by
  have hm := transport_member n hc hr
  refine Nat.le_antisymm ?_ (cycles_le n hc hr hm
    (getAt_relab n comp r))
  exact cycles_le n hm (invPerm_member n hr) hc
    (fun i hi => (relab_back n hc hr (getAt_relab n comp r)
      i hi).symm)

/-! The key's position at the wiring carrier (`con:places`'
enumeration, one word per permutation): the position read with
its two roundtrips, and the relabeling's composition reads — the
partner relabeled and the composite relabeled. -/

/-- The position at a head key is the leading place, past a
refused head the tail's own beyond it. -/
private theorem idxOf_cons (b x : List Nat) (t : List (List Nat)) :
    idxOf x (b :: t) = if x = b then 0 else idxOf x t + 1 := by
  by_cases hxb : x = b
  · rw [hxb]
    show (if (b == b) = true then 0 else idxOf b t + 1) = _
    rw [ground.listEqBeq b, if_pos (rfl : b = b)]
    rfl
  · show (if (x == b) = true then 0 else idxOf x t + 1) = _
    rw [ground.listBeqRefuse (fun _ _ hh => ground.beqEqOf hh)
      hxb, if_neg hxb]
    rfl

/-- An occupied key's position sits inside the list. -/
theorem idxOf_lt : ∀ (l : List (List Nat)) (x : List Nat),
    0 < ground.countOf x l → idxOf x l < l.length
  | [], _, h => absurd h (Nat.lt_irrefl 0)
  | b :: t, x, h => by
    rw [idxOf_cons b x t]
    by_cases hxb : x = b
    · rw [if_pos hxb]
      exact Nat.succ_pos _
    · rw [if_neg hxb]
      refine Nat.succ_lt_succ (idxOf_lt t x ?_)
      rw [← ground.countOf_head_ne hxb t]
      exact h

/-- The list read at an occupied key's position is that key. -/
theorem getAt_idxOf : ∀ (l : List (List Nat)) (x : List Nat),
    0 < ground.countOf x l → ground.getAt [] l (idxOf x l) = x
  | [], _, h => absurd h (Nat.lt_irrefl 0)
  | b :: t, x, h => by
    rw [idxOf_cons b x t]
    by_cases hxb : x = b
    · rw [if_pos hxb]
      exact hxb.symm
    · rw [if_neg hxb]
      show ground.getAt [] t (idxOf x t) = x
      refine getAt_idxOf t x ?_
      rw [← ground.countOf_head_ne hxb t]
      exact h

/-- A distinct list's entry names its own place back. -/
theorem idxOf_getAt : ∀ (l : List (List Nat)) (i : Nat),
    ground.distinctList l → i < l.length →
    idxOf (ground.getAt [] l i) l = i
  | [], _, _, hi => absurd hi (Nat.not_lt_zero _)
  | b :: t, 0, _, _ => by
    show idxOf b (b :: t) = 0
    rw [idxOf_cons b b t, if_pos rfl]
  | b :: t, i + 1, hd, hi => by
    have hit : i < t.length := Nat.lt_of_succ_lt_succ hi
    have hmem : 0 < ground.countOf (ground.getAt [] t i) t :=
      ground.countOf_getAt_pos ([] : List Nat) t i hit
    have hne : ground.getAt ([] : List Nat) t i ≠ b := by
      intro he
      have hb : 0 < ground.countOf b t := by
        rw [← he]
        exact hmem
      have h2 : ground.countOf b (b :: t) ≤ 1 :=
        hd b (List.Mem.head t)
      rw [ground.countOf_head b t] at h2
      exact absurd (Nat.le_trans (Nat.succ_le_succ hb) h2)
        (Nat.not_succ_le_self 1)
    have hdt : ground.distinctList t := by
      intro x hx
      refine Nat.le_trans ?_ (hd x (List.Mem.tail b hx))
      rw [ground.countOf_cons x b t]
      exact Nat.le_add_left _ _
    show idxOf (ground.getAt ([] : List Nat) t i) (b :: t) = i + 1
    rw [idxOf_cons b _ t, if_neg hne, idxOf_getAt t i hdt hit]

/-- The relabeled wiring's partner is the partner relabeled: the
flipped assignment travels along the relabeling. -/
theorem invPerm_transport (k : Nat) (b ρ : List Nat)
    (hb : 0 < ground.countOf b (perms k))
    (hr : 0 < ground.countOf ρ (perms k)) :
    invPerm k ((invPerm k ρ).map (fun j =>
      ground.getAt 0 ρ (ground.getAt 0 b j)))
    = (invPerm k ρ).map (fun j =>
        ground.getAt 0 ρ (ground.getAt 0 (invPerm k b) j)) := by
  obtain ⟨hrlen, hrdist, hrval, hrocc⟩ := perm_member_reads hr
  obtain ⟨hblen, _, _, hbocc⟩ := perm_member_reads hb
  obtain ⟨_, hcdist, _, _⟩ :=
    perm_member_reads (transport_member k hb hr)
  have hCl : ((invPerm k ρ).map (fun j =>
      ground.getAt 0 ρ (ground.getAt 0 b j))).length = k := by
    rw [ground.length_map, length_invPerm]
  refine ground.getAt_ext 0 _ _
    (by rw [length_invPerm, ground.length_map, length_invPerm]) ?_
  intro i hi
  rw [length_invPerm] at hi
  have hul : posOf i ρ < k := by
    rw [← hrlen]
    exact posOf_lt i ρ (hrocc i hi)
  have hvl : posOf (posOf i ρ) b < k := by
    rw [← hblen]
    exact posOf_lt _ b (hbocc _ hul)
  have hvr : posOf (posOf i ρ) b < ρ.length := by
    rw [hrlen]
    exact hvl
  have hwk : ground.getAt 0 ρ (posOf (posOf i ρ) b) < k :=
    hrval _ (ground.countOf_getAt_pos 0 ρ _ hvr)
  have hCw : ground.getAt 0 ((invPerm k ρ).map (fun j =>
      ground.getAt 0 ρ (ground.getAt 0 b j)))
      (ground.getAt 0 ρ (posOf (posOf i ρ) b)) = i := by
    rw [getAt_relab k b ρ _ hwk, getAt_invPerm k ρ hwk,
      posOf_getAt hrdist _ hvr,
      getAt_posOf (posOf i ρ) b (hbocc _ hul),
      getAt_posOf i ρ (hrocc i hi)]
  have hkey := posOf_getAt hcdist
    (ground.getAt 0 ρ (posOf (posOf i ρ) b)) (by rw [hCl]; exact hwk)
  rw [hCw] at hkey
  rw [getAt_invPerm k ((invPerm k ρ).map (fun j =>
      ground.getAt 0 ρ (ground.getAt 0 b j))) hi,
    ground.getAt_map 0 0 _ (invPerm k ρ) i
      (by rw [length_invPerm]; exact hi),
    getAt_invPerm k ρ hi, getAt_invPerm k b hul]
  exact hkey

/-- The relabeled wirings' composite is the composite relabeled:
the relabeling carries the assignment fold. -/
theorem expo_transport (k : Nat) (a c ρ : List Nat)
    (hc : 0 < ground.countOf c (perms k))
    (hr : 0 < ground.countOf ρ (perms k)) :
    expo ((invPerm k ρ).map (fun j =>
        ground.getAt 0 ρ (ground.getAt 0 a j)))
      ((invPerm k ρ).map (fun j =>
        ground.getAt 0 ρ (ground.getAt 0 c j)))
    = (invPerm k ρ).map (fun j =>
        ground.getAt 0 ρ (ground.getAt 0 (expo a c) j)) := by
  obtain ⟨hrlen, hrdist, hrval, hrocc⟩ := perm_member_reads hr
  obtain ⟨hclen, _, hcval, _⟩ := perm_member_reads hc
  have hCl : ((invPerm k ρ).map (fun j =>
      ground.getAt 0 ρ (ground.getAt 0 c j))).length = k := by
    rw [ground.length_map, length_invPerm]
  have hAl : ((invPerm k ρ).map (fun j =>
      ground.getAt 0 ρ (ground.getAt 0 (expo a c) j))).length = k := by
    rw [ground.length_map, length_invPerm]
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · show (((invPerm k ρ).map (fun j =>
        ground.getAt 0 ρ (ground.getAt 0 c j))).map
      (ground.getAt 0 ((invPerm k ρ).map (fun j =>
        ground.getAt 0 ρ (ground.getAt 0 a j))))).length = _
    rw [ground.length_map, hCl, hAl]
  · intro i hi
    rw [show (expo ((invPerm k ρ).map (fun j =>
        ground.getAt 0 ρ (ground.getAt 0 a j)))
      ((invPerm k ρ).map (fun j =>
        ground.getAt 0 ρ (ground.getAt 0 c j)))).length
        = k from by
      show (((invPerm k ρ).map (fun j =>
          ground.getAt 0 ρ (ground.getAt 0 c j))).map
        (ground.getAt 0 ((invPerm k ρ).map (fun j =>
          ground.getAt 0 ρ (ground.getAt 0 a j))))).length = k
      rw [ground.length_map, hCl]] at hi
    have hul : posOf i ρ < k := by
      rw [← hrlen]
      exact posOf_lt i ρ (hrocc i hi)
    have hzc : posOf i ρ < c.length := by
      rw [hclen]
      exact hul
    have hzk : ground.getAt 0 c (posOf i ρ) < k :=
      hcval _ (ground.countOf_getAt_pos 0 c _ hzc)
    have hzr : ground.getAt 0 c (posOf i ρ) < ρ.length := by
      rw [hrlen]
      exact hzk
    have hwk : ground.getAt 0 ρ (ground.getAt 0 c (posOf i ρ)) < k :=
      hrval _ (ground.countOf_getAt_pos 0 ρ _ hzr)
    rw [getAt_expo _ _ i (by rw [hCl]; exact hi),
      getAt_relab k c ρ i hi, getAt_invPerm k ρ hi,
      getAt_relab k a ρ _ hwk, getAt_invPerm k ρ hwk,
      posOf_getAt hrdist _ hzr,
      getAt_relab k (expo a c) ρ i hi, getAt_invPerm k ρ hi,
      getAt_expo a c (posOf i ρ) hzc]

/-! The expansion tier's enumeration reads (`def:elim`'s
determinant fold consumes them): the unit-content enumeration
regroups by its first letter over the dropped key's enumerations,
a trailing unoccupied key drops from the enumeration outright, and
the inversion count splits at the head against the tail's member
counts. -/

private theorem flatMap_fold {α β : Type} (f : α → List β) :
    ∀ l : List α, l.flatMap f = ground.famFold List.append [] f l
  | [] => rfl
  | a :: t => congrArg (List.append (f a)) (flatMap_fold f t)

private theorem dipAt_replicate_one : ∀ (i e : Nat), i < e + 1 →
    dipAt i (List.replicate (e + 1) 1)
      = List.replicate i 1 ++ 0 :: List.replicate (e - i) 1
  | 0, _, _ => rfl
  | i + 1, 0, h => absurd (Nat.lt_of_succ_lt_succ h)
      (Nat.not_lt_zero i)
  | i + 1, e + 1, h => by
    show 1 :: dipAt i (List.replicate (e + 1) 1)
      = 1 :: (List.replicate i 1
          ++ 0 :: List.replicate (e + 1 - (i + 1)) 1)
    have hsub : e + 1 - (i + 1) = e - i := Nat.succ_sub_succ e i
    rw [dipAt_replicate_one i e (Nat.lt_of_succ_lt_succ h), hsub]

/-- The unit-content enumeration regroups by its first letter: one
branch per letter at the dropped key's enumeration, the letter
consed onto the tail's arrangements. -/
theorem monomialsAt_ones_expand (e : Nat) :
    monomialsAt (List.replicate (e + 1) 1)
      = (List.range (e + 1)).flatMap (fun j =>
          (monomialsAt (List.replicate j 1
              ++ 0 :: List.replicate (e - j) 1)).map
            (fun t => j :: t)) := by
  show monGo (sumNat (List.replicate (e + 1) 1))
      (List.replicate (e + 1) 1) = _
  rw [show sumNat (List.replicate (e + 1) 1) = e + 1 from
    sumNat_replicate_one (e + 1)]
  show (if sumNat (List.replicate (e + 1) 1) = 0 then [[]]
    else (List.range (List.replicate (e + 1) 1).length).flatMap
      (fun i =>
        if 0 < ground.getAt 0 (List.replicate (e + 1) 1) i then
          (monGo e (dipAt i (List.replicate (e + 1) 1))).map
            (fun m => i :: m)
        else [])) = _
  rw [if_neg (fun hz : sumNat (List.replicate (e + 1) 1) = 0 =>
      nomatch ((sumNat_replicate_one (e + 1)).symm.trans hz)),
    show (List.replicate (e + 1) 1).length = e + 1 from
      ground.length_replicate 1 (e + 1),
    flatMap_fold, flatMap_fold]
  refine ground.famFold_congr_members List.append [] _ _
    (List.range (e + 1)) (fun i hi => ?_)
  have hie : i < e + 1 := by
    rw [countOf_range i (e + 1)] at hi
    by_cases h : i < e + 1
    · exact h
    · rw [if_neg h] at hi
      exact absurd hi (Nat.lt_irrefl 0)
  rw [if_pos (by
      rw [ground.getAt_replicate 0 1 (e + 1) i hie]
      exact Nat.succ_pos 0),
    dipAt_replicate_one i e hie]
  show (monGo e (List.replicate i 1
      ++ 0 :: List.replicate (e - i) 1)).map (fun m => i :: m)
    = (monGo (sumNat (List.replicate i 1
        ++ 0 :: List.replicate (e - i) 1))
      (List.replicate i 1 ++ 0 :: List.replicate (e - i) 1)).map
      (fun t => i :: t)
  rw [ground.sumNat_replicate_strike i e (Nat.le_of_lt_succ hie)]

private theorem dipAt_append_lt {v : List Nat} :
    ∀ (i : Nat) (mu : List Nat), i < mu.length →
      dipAt i (mu ++ v) = dipAt i mu ++ v
  | _, [], h => absurd h (Nat.not_lt_zero _)
  | 0, a :: t, _ => rfl
  | i + 1, a :: t, h => by
    show a :: dipAt i (t ++ v) = a :: (dipAt i t ++ v)
    rw [dipAt_append_lt i t (Nat.lt_of_succ_lt_succ h)]

private theorem monGo_zero_tail : ∀ (fuel : Nat) (mu : List Nat),
    monGo fuel (mu ++ [0]) = monGo fuel mu
  | 0, _ => rfl
  | fuel + 1, mu => by
    have hs : sumNat (mu ++ [0]) = sumNat mu :=
      (sumNat_append mu [0]).trans rfl
    show (if sumNat (mu ++ [0]) = 0 then [[]]
      else (List.range (mu ++ [0]).length).flatMap (fun i =>
        if 0 < ground.getAt 0 (mu ++ [0]) i then
          (monGo fuel (dipAt i (mu ++ [0]))).map (fun m => i :: m)
        else [])) = _
    rw [hs]
    by_cases hz : sumNat mu = 0
    · rw [if_pos hz]
      show _ = (if sumNat mu = 0 then [[]] else _)
      rw [if_pos hz]
    · rw [if_neg hz]
      show _ = (if sumNat mu = 0 then [[]]
        else (List.range mu.length).flatMap (fun i =>
          if 0 < ground.getAt 0 mu i then
            (monGo fuel (dipAt i mu)).map (fun m => i :: m)
          else []))
      have hlen1 : (mu ++ [0]).length = mu.length + 1 :=
        (ground.length_append mu [0]).trans rfl
      rw [if_neg hz, hlen1,
        range_succ mu.length, flatMap_fold, flatMap_fold,
        ground.famFold_append List.append []
          (fun x y z => ground.append_assoc x y z) (fun _ => rfl)]
      show List.append _ _ = _
      rw [show ground.famFold List.append []
          (fun i => if 0 < ground.getAt 0 (mu ++ [0]) i then
            (monGo fuel (dipAt i (mu ++ [0]))).map (fun m => i :: m)
          else []) [mu.length] = ([] : List (List Nat)) from by
        show List.append (if 0 < ground.getAt 0 (mu ++ [0]) mu.length
            then _ else []) [] = []
        rw [if_neg (by
          rw [ground.getAt_append 0 mu [0] mu.length,
            if_neg (Nat.lt_irrefl mu.length), Nat.sub_self]
          exact Nat.lt_irrefl 0)]
        rfl]
      rw [show ∀ l : List (List Nat), List.append l [] = l
        from fun l => ground.append_nil l]
      refine ground.famFold_congr_members List.append [] _ _
        (List.range mu.length) (fun i hi => ?_)
      have him : i < mu.length := by
        rw [countOf_range i mu.length] at hi
        by_cases h : i < mu.length
        · exact h
        · rw [if_neg h] at hi
          exact absurd hi (Nat.lt_irrefl 0)
      rw [show ground.getAt 0 (mu ++ [0]) i = ground.getAt 0 mu i
          from by
        rw [ground.getAt_append 0 mu [0] i, if_pos him],
        dipAt_append_lt i mu him,
        monGo_zero_tail fuel (dipAt i mu)]

/-- A trailing unoccupied key drops from the enumeration: the
monomial lists agree outright. -/
theorem monomialsAt_zero_tail (mu : List Nat) :
    monomialsAt (mu ++ [0]) = monomialsAt mu := by
  show monGo (sumNat (mu ++ [0])) (mu ++ [0])
    = monGo (sumNat mu) mu
  rw [(sumNat_append mu [0]).trans rfl]
  exact monGo_zero_tail (sumNat mu) mu

/-- The inversion count at a head splits: at a tail holding every
value below the head once, the head contributes its own value. -/
theorem inversions_cons_of_counts (a : Nat) (t : List Nat)
    (hlow : ∀ x, x < a → 0 < ground.countOf x t)
    (hcap : ∀ x, x < a → ground.countOf x t ≤ 1) :
    inversions (a :: t) = a + inversions t := by
  show ground.countBelow a t + inversions t = a + inversions t
  rw [ground.countBelow_sum a t,
    ground.famFold_congr_members Nat.add 0 _ (fun _ => (1 : Nat))
      (List.range a)
      (fun x hx => by
        have hxa : x < a := by
          rw [countOf_range x a] at hx
          by_cases h : x < a
          · exact h
          · rw [if_neg h] at hx
            exact absurd hx (Nat.lt_irrefl 0)
        exact Nat.le_antisymm (hcap x hxa) (hlow x hxa)),
    ground.famFold_length (List.range a), length_range a]

/-! The enumeration's rank tier (`con:places`): `rankOf`'s defining
clause — the arithmetic rank is the monomial's position in the
letters-ascending enumeration, the earlier-lettered arrangements
counted per place — with the arrangement count `countMon` the
enumeration's own length.  The block identity
`length · (Π factorial) = factorial(total)` reads the division
exactly, the cofactor derived on the kernel's fuel-structural
`Nat.div.go` at Ground (`ground.divMulSelf`). -/

private theorem factorial_pos : ∀ n : Nat, 0 < factorial n
  | 0 => Nat.lt_succ_self 0
  | n + 1 => by
    show 0 < (n + 1) * factorial n
    rw [Nat.succ_mul]
    exact Nat.lt_of_lt_of_le (factorial_pos n)
      (Nat.le_add_left (factorial n) (n * factorial n))

private theorem prodNat_factorial_pos : ∀ mu : List Nat,
    0 < prodNat (mu.map factorial)
  | [] => Nat.lt_succ_self 0
  | n :: t => by
    show 0 < factorial n * prodNat (t.map factorial)
    have h1 := factorial_pos n
    have h2 := prodNat_factorial_pos t
    match hm : factorial n, hp : prodNat (t.map factorial) with
    | 0, _ => exact absurd (hm ▸ h1) (Nat.lt_irrefl 0)
    | _, 0 => exact absurd (hp ▸ h2) (Nat.lt_irrefl 0)
    | x + 1, y + 1 =>
      rw [Nat.succ_mul, Nat.add_succ]
      exact Nat.succ_pos _

private theorem prodNat_factorial_sum_zero : ∀ mu : List Nat,
    sumNat mu = 0 → prodNat (mu.map factorial) = 1
  | [], _ => rfl
  | n :: t, h => by
    have h' : n + sumNat t = 0 := h
    show factorial n * prodNat (t.map factorial) = 1
    rw [Nat.eq_zero_of_add_eq_zero_right h',
      prodNat_factorial_sum_zero t (Nat.eq_zero_of_add_eq_zero_left h')]
    rfl

private theorem prodNat_dipAt : ∀ (mu : List Nat) (a : Nat),
    0 < ground.getAt 0 mu a →
    prodNat ((dipAt a mu).map factorial) * ground.getAt 0 mu a
      = prodNat (mu.map factorial)
  | [], 0, h => absurd h (Nat.lt_irrefl 0)
  | [], _ + 1, h => absurd h (Nat.lt_irrefl 0)
  | n :: t, 0, h => by
    show factorial (n - 1) * prodNat (t.map factorial) * n
      = factorial n * prodNat (t.map factorial)
    rw [ground.mulAssoc (factorial (n - 1))
        (prodNat (t.map factorial)) n,
      Nat.mul_comm (prodNat (t.map factorial)) n,
      ← ground.mulAssoc (factorial (n - 1)) n
        (prodNat (t.map factorial)),
      Nat.mul_comm (factorial (n - 1)) n]
    have hn : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos h
    have : n * factorial (n - 1) = factorial n := by
      rw [← hn]
      rfl
    rw [this]
  | n :: t, a + 1, h => by
    show factorial n * prodNat ((dipAt a t).map factorial)
        * ground.getAt 0 t a
      = factorial n * prodNat (t.map factorial)
    rw [ground.mulAssoc (factorial n)
      (prodNat ((dipAt a t).map factorial))
      (ground.getAt 0 t a), prodNat_dipAt t a h]


/-- A letter's own word reads the unit content at its key. -/
theorem content_unitAt (d i : Nat) : content d [i] = unitAt d i := by
  show (List.range d).map (fun k => ground.countOf k [i])
    = (List.range d).map (fun j => if j = i then 1 else 0)
  exact ground.map_congr_all _ _
    (fun k => by
      rw [ground.countOf_cons k i ([] : List Nat)]
      show (if k = i then 1 else 0) + 0 = if k = i then 1 else 0
      rw [Nat.add_zero])
    (List.range d)

/-- The content splits over the join, one componentwise sum per
letter. -/
theorem content_append (d : Nat) (a b : List Nat) :
    content d (a ++ b)
      = List.zipWith (fun x y => x + y) (content d a)
        (content d b) := by
  show (List.range d).map (fun i => ground.countOf i (a ++ b))
    = List.zipWith (fun x y => x + y)
      ((List.range d).map (fun i => ground.countOf i a))
      ((List.range d).map (fun i => ground.countOf i b))
  rw [ground.zipWith_map_map (fun x y => x + y)
    (fun i => ground.countOf i a) (fun i => ground.countOf i b)
    (List.range d)]
  exact ground.map_congr_all _ _
    (fun i => ground.countOf_append i a b) (List.range d)

/-- The unit content's enumeration is its own letter, once. -/
theorem monomialsAt_unitAt (d i : Nat) (hi : i < d) :
    monomialsAt (unitAt d i) = [[i]] := by
  refine ground.single_of_counts [i] (monomialsAt (unitAt d i)) (fun m => ?_)
  rw [countOf_monomialsAt (unitAt d i) m, length_unitAt d i,
    sumNat_unitAt d i hi]
  by_cases hm : m = [i]
  · rw [if_pos hm, if_pos (show m.length = 1 ∧ content d m = unitAt d i
      from by rw [hm]; exact ⟨rfl, content_unitAt d i⟩)]
  · rw [if_neg hm, if_neg ?_]
    intro hc
    refine hm ?_
    match m, hc with
    | [], hc => exact Nat.noConfusion hc.1
    | [a], hc =>
      have hg : ground.getAt 0 (content d [a]) i
          = ground.getAt 0 (unitAt d i) i := by rw [hc.2]
      rw [content_unitAt d a, getAt_unitAt d a i, getAt_unitAt d i i,
        if_pos hi, if_pos hi, if_pos rfl] at hg
      by_cases hai : i = a
      · rw [hai]
      · rw [if_neg hai] at hg
        exact Nat.noConfusion hg
    | a :: b :: t, hc => exact Nat.noConfusion (Nat.succ.inj hc.1)

/-- The one-box shape's degree is the one. -/
theorem degree_unitAt (n : Nat) : degree (unitAt (n + 1) 0) = 1 := by
  show sumNat (rowList (unitAt (n + 1) 0)) = 1
  rw [unitAt_zero n]
  show sumNat ((1 + sumNat (List.replicate n 0))
    :: rowList (List.replicate n 0)) = 1
  rw [sumNat_replicate_zero n, rowList_replicate_zero n]
  show 1 + 0 + sumNat (List.replicate n 0) = 1
  rw [sumNat_replicate_zero n]


/-- The guarded family below a letter counts the keys under it. -/
private theorem belowAll (b c : Nat) : ∀ m : Nat, m ≤ b →
    ground.famFold Nat.add 0 (fun a => if a < b then c else 0)
      (List.range m) = c * m
  | 0, _ => rfl
  | m + 1, h => by
    rw [ground.range_succ m,
      ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add
        (fun a => if a < b then c else 0) (List.range m) [m],
      belowAll b c m (Nat.le_of_succ_le h)]
    show Nat.add (c * m)
      (Nat.add (if m < b then c else 0) 0) = c * (m + 1)
    rw [if_pos (show m < b from h)]
    rfl

/-- The guarded family below a letter folds to the letter's own
key, the further keys refused. -/
theorem belowRun (b c : Nat) : ∀ g : Nat,
    ground.famFold Nat.add 0 (fun a => if a < b then c else 0)
      (List.range (b + g)) = c * b
  | 0 => belowAll b c b (Nat.le_refl b)
  | g + 1 => by
    show ground.famFold Nat.add 0 (fun a => if a < b then c else 0)
      (List.range (b + g + 1)) = c * b
    rw [ground.range_succ (b + g),
      ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add
        (fun a => if a < b then c else 0) (List.range (b + g))
        [b + g],
      belowRun b c g]
    show Nat.add (c * b)
      (Nat.add (if b + g < b then c else 0) 0) = c * b
    rw [if_neg (fun hlt => Nat.lt_irrefl (b + g)
      (Nat.lt_of_lt_of_le hlt (Nat.le_add_right b g)))]
    rfl


/-- The dot's exchange: the two lists' fold at the entry products
commuted. -/
theorem dotNat_comm : ∀ X Y : List Nat, dotNat X Y = dotNat Y X
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: X, b :: Y => by
    show a * b + dotNat X Y = b * a + dotNat Y X
    rw [Nat.mul_comm a b, dotNat_comm X Y]

/-- The dot distributes over the componentwise sum. -/
theorem dotNat_zipAdd (u a c : List Nat)
    (ha : a.length = u.length) (hc : c.length = u.length) :
    dotNat u (List.zipWith (fun x y => x + y) a c)
      = dotNat u a + dotNat u c := by
  have hzl : (List.zipWith (fun x y => x + y) a c).length
      = u.length := by
    exact ground.length_zipWith (fun x y => x + y) a c u.length
      ha hc
  rw [dotNat_index u (List.zipWith (fun x y => x + y) a c) hzl,
    dotNat_index u a ha, dotNat_index u c hc,
    ← ground.famFold_add_split
      (fun i => ground.getAt 0 u i * ground.getAt 0 a i)
      (fun i => ground.getAt 0 u i * ground.getAt 0 c i)
      (List.range u.length)]
  refine ground.famFold_congr_members Nat.add 0 _ _
    (List.range u.length) (fun i hi => ?_)
  have hiu : i < u.length := ltOfMem hi
  rw [ground.getAt_zipWith 0 0 0 (fun x y => x + y) a c i
      (by rw [ha]; exact hiu) (by rw [hc]; exact hiu),
    Nat.left_distrib]

/-- The place pairs at a width, each earlier place against each
later one, the later place peeling. -/
def pairsOf : Nat → List (Nat × Nat)
  | 0 => []
  | d + 1 => pairsOf d ++ (List.range d).map (fun j => (j, d))

/-- A pair's places read the width and the order. -/
theorem pairs_mem : ∀ (d : Nat) (pr : Nat × Nat),
    0 < ground.countOf pr (pairsOf d) → pr.1 < pr.2 ∧ pr.2 < d
  | 0, _, h => absurd h (Nat.lt_irrefl 0)
  | d + 1, pr, h => by
    rw [show pairsOf (d + 1)
        = pairsOf d ++ (List.range d).map (fun j => (j, d)) from rfl,
      ground.countOf_append] at h
    match Nat.eq_zero_or_pos (ground.countOf pr (pairsOf d)) with
    | .inr hl =>
      match pairs_mem d pr hl with
      | ⟨h1, h2⟩ => exact ⟨h1, Nat.lt_succ_of_lt h2⟩
    | .inl hz =>
      rw [hz, Nat.zero_add] at h
      match ground.mem_map_of (fun j => (j, d)) (List.range d)
          pr (ground.mem_of_countOf_pos pr _ h) with
      | ⟨j, hj, hje⟩ =>
        rw [← hje]
        exact ⟨ltOfMemRange hj,
          Nat.lt_succ_self d⟩

/-- Each pair enters once. -/
theorem pairs_distinct : ∀ (d : Nat) (pr : Nat × Nat),
    ground.countOf pr (pairsOf d) ≤ 1
  | 0, _ => Nat.le_of_lt (Nat.lt_succ_self 0)
  | d + 1, pr => by
    rw [show pairsOf (d + 1)
        = pairsOf d ++ (List.range d).map (fun j => (j, d)) from rfl,
      ground.countOf_append]
    match Nat.eq_zero_or_pos (ground.countOf pr (pairsOf d)) with
    | .inl hz =>
      rw [hz, Nat.zero_add]
      have hmap : ∀ (l : List Nat), (∀ x, ground.countOf x l ≤ 1) →
          ground.countOf pr (l.map (fun j => (j, d))) ≤ 1 := by
        intro l
        induction l with
        | nil => intro _; exact Nat.le_of_lt (Nat.lt_succ_self 0)
        | cons a t ih =>
          intro hdst
          show ground.countOf pr
            ((a, d) :: t.map (fun j => (j, d))) ≤ 1
          rw [ground.countOf_cons]
          by_cases hpa : pr = (a, d)
          · rw [if_pos hpa]
            have hz2 : ground.countOf pr (t.map (fun j => (j, d)))
                = 0 := by
              match Nat.eq_zero_or_pos
                  (ground.countOf pr (t.map (fun j => (j, d)))) with
              | .inl h0 => exact h0
              | .inr hp =>
                match ground.mem_map_of (fun j => (j, d)) t pr
                    (ground.mem_of_countOf_pos pr _ hp) with
                | ⟨j, hj, hje⟩ =>
                  exfalso
                  have hja : j = a := by
                    have := congrArg Prod.fst (hje.trans hpa)
                    exact this
                  have h1 := hdst a
                  rw [ground.countOf_head] at h1
                  have h2 : 0 < ground.countOf a t := by
                    rw [← hja]
                    exact ground.countOf_pos_of_mem hj
                  exact absurd (Nat.lt_of_lt_of_le
                    (Nat.succ_lt_succ h2) h1) (Nat.lt_irrefl 1)
            rw [hz2]
            exact Nat.le_refl 1
          · rw [if_neg hpa, Nat.zero_add]
            exact ih (fun x => Nat.le_trans
              (show ground.countOf x t ≤ ground.countOf x (a :: t) from
                Nat.le_add_left _ _) (hdst x))
      exact hmap (List.range d) (fun x => by
        rw [countOf_range x d]
        cases Nat.lt_or_ge x d with
        | inl h => rw [if_pos h]; exact Nat.le_refl 1
        | inr h =>
          rw [if_neg (fun hc => absurd (Nat.lt_of_lt_of_le hc h)
            (Nat.lt_irrefl x))]
          exact Nat.zero_le 1)
    | .inr hl =>
      have h2 : ground.countOf pr ((List.range d).map
          (fun j => (j, d))) = 0 := by
        match Nat.eq_zero_or_pos (ground.countOf pr
            ((List.range d).map (fun j => (j, d)))) with
        | .inl h0 => exact h0
        | .inr hp =>
          exfalso
          match ground.mem_map_of (fun j => (j, d)) (List.range d) pr
              (ground.mem_of_countOf_pos pr _ hp) with
          | ⟨j, hj, hje⟩ =>
            have hd2 := (pairs_mem d pr hl).2
            rw [← hje] at hd2
            exact absurd hd2 (Nat.lt_irrefl d)
      rw [h2, Nat.add_zero]
      exact pairs_distinct d pr

/-- Every ordered place pair below the width joins the family. -/
theorem pairs_complete :
    ∀ (d : Nat) {j k : Nat}, j < k → k < d →
    0 < ground.countOf (j, k) (pairsOf d)
  | 0, _, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | d + 1, j, k, hjk, hk => by
    rw [show pairsOf (d + 1)
        = pairsOf d ++ (List.range d).map (fun i => (i, d)) from rfl,
      ground.countOf_append]
    match Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hk) with
    | .inl he =>
      refine Nat.lt_of_lt_of_le ?_ (Nat.le_add_left _ _)
      have hm : ((j, k) : Nat × Nat)
          ∈ (List.range d).map (fun i => (i, d)) := by
        rw [he]
        exact ground.mem_map_to (fun i => (i, d))
          (memRange (he ▸ hjk))
      exact ground.countOf_pos_of_mem hm
    | .inr hlt =>
      exact Nat.lt_of_lt_of_le (pairs_complete d hjk hlt)
        (Nat.le_add_right _ _)

/-- The successor width's pairs recount as the first place's own
against the shifted pairs. -/
theorem countOf_pairs_split (D : Nat) :
    ∀ x : Nat × Nat, ground.countOf x (pairsOf (D + 1))
      = ground.countOf x
        ((List.range D).map (fun k => ((0, k + 1) : Nat × Nat))
          ++ (pairsOf D).map
            (fun r => ((r.1 + 1, r.2 + 1) : Nat × Nat)))
  | (j, k) => by
    rw [ground.countOf_append]
    match j, k with
    | j, 0 =>
      rw [show ground.countOf ((j, 0) : Nat × Nat)
          (pairsOf (D + 1)) = 0 from
        match Nat.eq_zero_or_pos (ground.countOf
            ((j, 0) : Nat × Nat) (pairsOf (D + 1))) with
        | .inl h0 => h0
        | .inr hp => absurd (pairs_mem (D + 1) (j, 0) hp).1
            (Nat.not_lt_zero j),
        ground.countOf_map_none _ ((j, 0) : Nat × Nat)
          (List.range D) (fun y _ he =>
            Nat.noConfusion (congrArg Prod.snd he)),
        ground.countOf_map_none _ ((j, 0) : Nat × Nat)
          (pairsOf D) (fun r _ he =>
            Nat.noConfusion (congrArg Prod.snd he))]
    | 0, k + 1 =>
      by_cases hk : k < D
      · rw [Nat.le_antisymm
            (pairs_distinct (D + 1) ((0, k + 1) : Nat × Nat))
            (pairs_complete (D + 1) (Nat.succ_pos k)
              (Nat.succ_lt_succ hk)),
          ground.countOf_map_inj
            (fun k => ((0, k + 1) : Nat × Nat)) k (List.range D)
            (fun y _ he => Nat.succ.inj (congrArg Prod.snd he)),
          countOf_range k D, if_pos hk,
          ground.countOf_map_none _ ((0, k + 1) : Nat × Nat)
            (pairsOf D) (fun r _ he =>
              Nat.noConfusion (congrArg Prod.fst he))]
      · rw [show ground.countOf ((0, k + 1) : Nat × Nat)
            (pairsOf (D + 1)) = 0 from
          match Nat.eq_zero_or_pos (ground.countOf
              ((0, k + 1) : Nat × Nat) (pairsOf (D + 1))) with
          | .inl h0 => h0
          | .inr hp => absurd (Nat.lt_of_succ_lt_succ
              (pairs_mem (D + 1) (0, k + 1) hp).2) hk,
          ground.countOf_map_none _ ((0, k + 1) : Nat × Nat)
            (List.range D) (fun y hy he => hk (by
              rw [← Nat.succ.inj (congrArg Prod.snd he)]
              exact ltOfMem hy)),
          ground.countOf_map_none _ ((0, k + 1) : Nat × Nat)
            (pairsOf D) (fun r _ he =>
              Nat.noConfusion (congrArg Prod.fst he))]
    | j + 1, k + 1 =>
      by_cases hjk : j < k ∧ k < D
      · rw [Nat.le_antisymm
            (pairs_distinct (D + 1) ((j + 1, k + 1) : Nat × Nat))
            (pairs_complete (D + 1) (Nat.succ_lt_succ hjk.1)
              (Nat.succ_lt_succ hjk.2)),
          ground.countOf_map_none _ ((j + 1, k + 1) : Nat × Nat)
            (List.range D) (fun y _ he =>
              Nat.noConfusion (congrArg Prod.fst he)),
          ground.countOf_map_inj
            (fun r => ((r.1 + 1, r.2 + 1) : Nat × Nat))
            ((j, k) : Nat × Nat) (pairsOf D)
            (fun x _ he => by
              have h1 := Nat.succ.inj (congrArg Prod.fst he)
              have h2 := Nat.succ.inj (congrArg Prod.snd he)
              show ((x.1, x.2) : Nat × Nat) = (j, k)
              rw [h1, h2]),
          Nat.le_antisymm
            (pairs_distinct D ((j, k) : Nat × Nat))
            (pairs_complete D hjk.1 hjk.2)]
      · rw [show ground.countOf ((j + 1, k + 1) : Nat × Nat)
            (pairsOf (D + 1)) = 0 from
          match Nat.eq_zero_or_pos (ground.countOf
              ((j + 1, k + 1) : Nat × Nat) (pairsOf (D + 1))) with
          | .inl h0 => h0
          | .inr hp => absurd
              ⟨Nat.lt_of_succ_lt_succ
                  (pairs_mem (D + 1) (j + 1, k + 1) hp).1,
                Nat.lt_of_succ_lt_succ
                  (pairs_mem (D + 1) (j + 1, k + 1) hp).2⟩ hjk,
          ground.countOf_map_none _ ((j + 1, k + 1) : Nat × Nat)
            (List.range D) (fun y _ he =>
              Nat.noConfusion (congrArg Prod.fst he)),
          ground.countOf_map_none _ ((j + 1, k + 1) : Nat × Nat)
            (pairsOf D) (fun r hr he => hjk (by
              have h1 := Nat.succ.inj (congrArg Prod.fst he)
              have h2 := Nat.succ.inj (congrArg Prod.snd he)
              rw [← h1, ← h2]
              exact ⟨(pairs_mem D r hr).1, (pairs_mem D r hr).2⟩))]

/-- A list's inversion count reads over the place pairs: one
reversed-order test per pair. -/
theorem inversions_pairs : ∀ t : List Nat,
    inversions t
    = ground.famFold Nat.add 0
      (fun r => if ground.getAt 0 t r.2 < ground.getAt 0 t r.1
        then (1 : Nat) else 0)
      (pairsOf t.length)
  | [] => rfl
  | a :: t => by
    show ground.countBelow a t + inversions t
      = ground.famFold Nat.add 0
        (fun r => if ground.getAt 0 (a :: t) r.2
            < ground.getAt 0 (a :: t) r.1
          then (1 : Nat) else 0)
        (pairsOf (t.length + 1))
    rw [ground.famFold_relist Nat.add 0 Nat.add_comm Nat.add_assoc
        _ (pairsOf (t.length + 1))
        ((List.range t.length).map
            (fun k => ((0, k + 1) : Nat × Nat))
          ++ (pairsOf t.length).map
            (fun r => ((r.1 + 1, r.2 + 1) : Nat × Nat)))
        (countOf_pairs_split t.length),
      ground.famFold_append Nat.add 0
        (fun x y z => Nat.add_assoc x y z)
        (fun x => Nat.zero_add x) _ _ _,
      ground.famFold_map Nat.add 0 _
        (fun k => ((0, k + 1) : Nat × Nat)) (List.range t.length),
      ground.famFold_map Nat.add 0 _
        (fun r => ((r.1 + 1, r.2 + 1) : Nat × Nat))
        (pairsOf t.length),
      inversions_pairs t, ground.countBelow_index a t]
    rfl


private theorem fold_mul_right (F : Nat → Nat) (c : Nat) :
    ∀ l : List Nat,
      ground.famFold Nat.add 0 F l * c
        = ground.famFold Nat.add 0 (fun x => F x * c) l
  | [] => Nat.zero_mul c
  | a :: t => by
    show (F a + ground.famFold Nat.add 0 F t) * c = _
    rw [ground.mulAddR (F a) (ground.famFold Nat.add 0 F t) c,
      fold_mul_right F c t]
    rfl

private theorem fold_mul_left (F : Nat → Nat) (c : Nat) :
    ∀ l : List Nat,
      ground.famFold Nat.add 0 (fun x => c * F x) l
        = c * ground.famFold Nat.add 0 F l
  | [] => (Nat.mul_zero c).symm
  | a :: t => by
    show c * F a + ground.famFold Nat.add 0 (fun x => c * F x) t
      = c * (F a + ground.famFold Nat.add 0 F t)
    rw [fold_mul_left F c t, Nat.mul_add]

private theorem len_monGo : ∀ (fuel : Nat) (mu : List Nat),
    sumNat mu = fuel →
    (monGo fuel mu).length * prodNat (mu.map factorial)
      = factorial fuel
  | 0, mu, h => by
    show (1 : Nat) * prodNat (mu.map factorial) = 1
    rw [Nat.one_mul, prodNat_factorial_sum_zero mu h]
  | fuel + 1, mu, h => by
    show (if sumNat mu = 0 then [[]]
        else (List.range mu.length).flatMap (fun i =>
          if 0 < ground.getAt 0 mu i then
            (monGo fuel (dipAt i mu)).map (fun m => i :: m)
          else [])).length * prodNat (mu.map factorial)
      = factorial (fuel + 1)
    rw [if_neg (fun hc : sumNat mu = 0 =>
      Nat.noConfusion (h.symm.trans hc)),
      ground.length_flatMap, fold_mul_right,
      ground.famFold_congr_all Nat.add 0 _
        (fun b => factorial fuel * ground.getAt 0 mu b)
        (fun b => by
          by_cases hb : 0 < ground.getAt 0 mu b
          · rw [if_pos hb]
            show ((monGo fuel (dipAt b mu)).map
                (fun m => b :: m)).length
                * prodNat (mu.map factorial) = _
            rw [ground.length_map, ← prodNat_dipAt mu b hb,
              ← ground.mulAssoc ((monGo fuel (dipAt b mu)).length)
                (prodNat ((dipAt b mu).map factorial))
                (ground.getAt 0 mu b),
              len_monGo fuel (dipAt b mu)
                (Nat.succ.inj ((sumNat_dipAt b mu hb).trans h))]
          · rw [if_neg hb]
            show (0 : Nat) * prodNat (mu.map factorial)
              = factorial fuel * ground.getAt 0 mu b
            have hz : ground.getAt 0 mu b = 0 := by
              match hg : ground.getAt 0 mu b with
              | 0 => rfl
              | g + 1 => exact absurd (hg ▸ Nat.succ_pos g) hb
            rw [hz, Nat.zero_mul, Nat.mul_zero])
        (List.range mu.length),
      fold_mul_left (fun i => ground.getAt 0 mu i) (factorial fuel)
        (List.range mu.length),
      sumIndex mu, h]
    show factorial fuel * (fuel + 1) = (fuel + 1) * factorial fuel
    exact Nat.mul_comm (factorial fuel) (fuel + 1)

/-- The arrangement count is the enumeration's length, the
multinomial's division read exactly at the block identity. -/
theorem countMon_read (mu : List Nat) :
    countMon mu = (monomialsAt mu).length := by
  show factorial (sumNat mu) / prodNat (mu.map factorial)
    = (monGo (sumNat mu) mu).length
  rw [← len_monGo (sumNat mu) mu rfl]
  exact divMulSelf ((monGo (sumNat mu) mu).length)
    (prodNat (mu.map factorial)) (prodNat_factorial_pos mu)

/-- The unit factors' product is one. -/
private theorem prodNat_replicate_one : ∀ k : Nat,
    prodNat (List.replicate k 1) = 1
  | 0 => rfl
  | k + 1 => by
    show 1 * prodNat (List.replicate k 1) = 1
    rw [prodNat_replicate_one k, Nat.mul_one]

/-- The place permutations' count is the factorial, the
arrangement count at the unit content. -/
theorem length_perms (k : Nat) :
    (perms k).length = factorial k := by
  show (monomialsAt (List.replicate k 1)).length = factorial k
  rw [← countMon_read]
  show factorial (sumNat (List.replicate k 1))
    / prodNat ((List.replicate k 1).map factorial)
    = factorial k
  rw [sumNat_replicate_one k,
    ground.map_replicate factorial 1 k,
    show factorial 1 = 1 from rfl,
    prodNat_replicate_one k]
  have h := ground.divMulSelf (factorial k) 1 (Nat.lt_succ_self 0)
  rw [Nat.mul_one] at h
  exact h

/-- The enumeration at an unoccupied content is the one nullary
arrangement. -/
theorem monomialsAt_sum_zero (mu : List Nat) (h : sumNat mu = 0) :
    monomialsAt mu = [[]] := by
  show monGo (sumNat mu) mu = [[]]
  rw [h]
  rfl

/-- The arrangement count grows with a further box: at a key inside
the letter list the raised content enumerates at least as many
arrangements as its source, the multinomial's own ratio
`(N + 1) / (mu_j + 1)` at or above one. -/
theorem length_monomialsAt_le_bumpAt (j : Nat) (mu : List Nat)
    (hj : j < mu.length) :
    (monomialsAt mu).length
      ≤ (monomialsAt (ground.bumpAt j mu)).length := by
  have hs : sumNat (ground.bumpAt j mu) = sumNat mu + 1 :=
    sumNat_bumpAt j mu hj
  have hg : ground.getAt 0 (ground.bumpAt j mu) j
      = ground.getAt 0 mu j + 1 :=
    ground.getAt_bumpAt_self j mu hj
  have hP : prodNat (mu.map factorial) * (ground.getAt 0 mu j + 1)
      = prodNat ((ground.bumpAt j mu).map factorial) := by
    have h := prodNat_dipAt (ground.bumpAt j mu) j
      (by rw [hg]; exact Nat.succ_pos _)
    rw [ground.dipAt_bumpAt_self j mu, hg] at h
    exact h
  have h1 : (monomialsAt mu).length * prodNat (mu.map factorial)
      = factorial (sumNat mu) := len_monGo (sumNat mu) mu rfl
  have h2 : (monomialsAt (ground.bumpAt j mu)).length
        * prodNat ((ground.bumpAt j mu).map factorial)
      = (sumNat mu + 1) * factorial (sumNat mu) := by
    show (monGo (sumNat (ground.bumpAt j mu))
        (ground.bumpAt j mu)).length
        * prodNat ((ground.bumpAt j mu).map factorial)
      = (sumNat mu + 1) * factorial (sumNat mu)
    rw [hs]
    exact len_monGo (sumNat mu + 1) (ground.bumpAt j mu) hs
  have hkey : (monomialsAt (ground.bumpAt j mu)).length
        * (ground.getAt 0 mu j + 1)
      = (sumNat mu + 1) * (monomialsAt mu).length := by
    refine Nat.eq_of_mul_eq_mul_right (m := prodNat (mu.map factorial))
      (prodNat_factorial_pos mu) ?_
    rw [ground.mulAssoc ((monomialsAt (ground.bumpAt j mu)).length)
        (ground.getAt 0 mu j + 1) (prodNat (mu.map factorial)),
      Nat.mul_comm (ground.getAt 0 mu j + 1)
        (prodNat (mu.map factorial)), hP, h2,
      ground.mulAssoc (sumNat mu + 1) ((monomialsAt mu).length)
        (prodNat (mu.map factorial)), h1]
  refine Nat.le_of_mul_le_mul_right
    (c := ground.getAt 0 mu j + 1) ?_ (Nat.succ_pos _)
  rw [hkey, Nat.mul_comm (sumNat mu + 1) ((monomialsAt mu).length)]
  exact Nat.mul_le_mul_left _
    (Nat.succ_le_succ (getAt_le_sumNat mu j))

/-- The rank block at a letter: the withdrawn content's enumeration
re-headed, the enumeration's own per-letter block. -/
private def rankBlk (mu : List Nat) (fuel i : Nat) :
    List (List Nat) :=
  if 0 < ground.getAt 0 mu i then
    (monGo fuel (dipAt i mu)).map (fun m => i :: m)
  else []

/-- The enumeration is occupied at every content, the factorial's
positivity read through the block identity. -/
theorem monomialsAt_occupied (mu : List Nat) :
    0 < (monomialsAt mu).length := by
  match hl : (monomialsAt mu).length with
  | n + 1 => exact Nat.succ_pos n
  | 0 =>
    have h := len_monGo (sumNat mu) mu rfl
    rw [show (monomialsAt mu).length
        = (monGo (sumNat mu) mu).length from rfl] at hl
    rw [hl, Nat.zero_mul] at h
    exact absurd (h ▸ factorial_pos (sumNat mu))
      (Nat.lt_irrefl 0)

private theorem range_prefix : ∀ (n a : Nat), a ≤ n →
    ∃ t, List.range n = List.range a ++ t
  | 0, 0, _ => ⟨[], rfl⟩
  | n + 1, a, h => by
    by_cases ha : a = n + 1
    · cases ha
      exact ⟨[], (ground.append_nil (List.range (n + 1))).symm⟩
    · match range_prefix n a
        (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne h ha)) with
      | ⟨t, ht⟩ =>
        refine ⟨t ++ [n], ?_⟩
        rw [range_succ n, ht, ground.append_assoc]

/-- `rankOf`'s positional read, the tex's defining clause: at a
member of the content's enumeration the arithmetic rank sits below
the length and reads the member back, the prefix blocks' lengths
the arrangement counts at the withdrawn letters. -/
theorem rankOf_read : ∀ (m mu : List Nat),
    m.length = sumNat mu → content mu.length m = mu →
    rankOf m mu < (monomialsAt mu).length
      ∧ ground.getAt [] (monomialsAt mu) (rankOf m mu) = m
  | [], mu, hlen, _ => by
    have hsum : sumNat mu = 0 := hlen.symm
    show rankOf [] mu < (monGo (sumNat mu) mu).length
      ∧ ground.getAt [] (monGo (sumNat mu) mu) (rankOf [] mu) = []
    rw [hsum]
    exact ⟨Nat.lt_succ_self 0, rfl⟩
  | a :: m', mu, hlen, hcont => by
    have hsc : sumNat (content mu.length (a :: m'))
        = (a :: m').length := by rw [hcont, ← hlen]
    have hcpos : 0 < ground.countOf a (a :: m') := by
      rw [ground.countOf_cons, if_pos rfl, Nat.add_comm]
      exact Nat.succ_pos _
    have had : a < mu.length :=
      mem_lt_of_content mu.length (a :: m') hsc a hcpos
    have hocc : 0 < ground.getAt 0 mu a := by
      rw [← hcont, getAt_content, if_pos had]
      exact hcpos
    have hlen' : m'.length = sumNat (dipAt a mu) := by
      have h1 : sumNat (dipAt a mu) + 1 = sumNat mu :=
        sumNat_dipAt a mu hocc
      have h2 : m'.length + 1 = sumNat mu := hlen
      exact Nat.succ.inj (h2.trans h1.symm)
    have hcont' : content (dipAt a mu).length m' = dipAt a mu := by
      rw [(ground.length_dipAt a mu)]
      refine ground.getAt_ext 0 _ _ ?_ ?_
      · rw [content_length, (ground.length_dipAt a mu)]
      · intro i hi
        rw [content_length] at hi
        rw [getAt_content, if_pos hi]
        by_cases hia : i = a
        · rw [hia, ground.getAt_dipAt a mu, ← hcont, getAt_content,
            if_pos had]
          rw [ground.countOf_cons, if_pos rfl,
            Nat.add_comm 1 (ground.countOf a m')]
          rfl
        · rw [ground.getAt_dipAt_ne a mu i hia, ← hcont, getAt_content,
            if_pos hi]
          rw [ground.countOf_cons, if_neg hia, Nat.zero_add]
    match rankOf_read m' (dipAt a mu) hlen' hcont' with
    | ⟨ihlt, ihget⟩ =>
      have hk : sumNat mu = m'.length + 1 := hlen.symm
      have hfuel : sumNat (dipAt a mu) = m'.length := hlen'.symm
      have hmono : monomialsAt mu
          = (List.range mu.length).flatMap (rankBlk mu m'.length) := by
        show monGo (sumNat mu) mu = _
        rw [hk]
        show (if sumNat mu = 0 then [[]] else _) = _
        rw [if_neg (fun hc : sumNat mu = 0 =>
          Nat.noConfusion (hk.symm.trans hc))]
        rfl
      have hpref : (List.range a).foldl (fun acc b =>
          if 0 < ground.getAt 0 mu b then
            acc + countMon (dipAt b mu)
          else acc) 0
          = ((List.range a).flatMap (rankBlk mu m'.length)).length := by
        rw [ground.length_flatMap (rankBlk mu m'.length) (List.range a),
          ground.foldl_congr _ (fun acc b => acc
            + (if 0 < ground.getAt 0 mu b then
                countMon (dipAt b mu) else 0))
            (fun acc b => by
              by_cases hb : 0 < ground.getAt 0 mu b
              · rw [if_pos hb, if_pos hb]
              · rw [if_neg hb, if_neg hb]
                rfl)
            (List.range a) 0,
          ground.foldlSum, Nat.zero_add]
        refine ground.famFold_congr_all Nat.add 0 _ _ ?_
          (List.range a)
        intro b
        by_cases hb : 0 < ground.getAt 0 mu b
        · show (if 0 < ground.getAt 0 mu b then
              countMon (dipAt b mu) else 0)
            = (rankBlk mu m'.length b).length
          rw [if_pos hb]
          show countMon (dipAt b mu)
            = (if 0 < ground.getAt 0 mu b then
                (monGo m'.length (dipAt b mu)).map (fun m => b :: m)
              else []).length
          rw [if_pos hb, ground.length_map,
            countMon_read (dipAt b mu)]
          show (monGo (sumNat (dipAt b mu)) (dipAt b mu)).length
            = (monGo m'.length (dipAt b mu)).length
          rw [Nat.succ.inj ((sumNat_dipAt b mu hb).trans hk)]
        · show (if 0 < ground.getAt 0 mu b then
              countMon (dipAt b mu) else 0)
            = (rankBlk mu m'.length b).length
          rw [if_neg hb]
          show (0 : Nat)
            = (if 0 < ground.getAt 0 mu b then
                (monGo m'.length (dipAt b mu)).map (fun m => b :: m)
              else []).length
          rw [if_neg hb]
          rfl
      match range_prefix mu.length (a + 1) had with
      | ⟨tail, htail⟩ =>
        have hsplit : monomialsAt mu
            = (List.range a).flatMap (rankBlk mu m'.length)
              ++ (rankBlk mu m'.length a
                  ++ tail.flatMap (rankBlk mu m'.length)) := by
          rw [hmono, htail, range_succ a, ground.append_assoc,
            ground.flatMap_append, ground.flatMap_append,
            show List.flatMap (rankBlk mu m'.length) [a]
                = rankBlk mu m'.length a
              from ground.append_nil (rankBlk mu m'.length a)]
        have hblka : rankBlk mu m'.length a
            = (monomialsAt (dipAt a mu)).map
                (fun m => a :: m) := by
          show (if 0 < ground.getAt 0 mu a then
              (monGo m'.length (dipAt a mu)).map (fun m => a :: m)
            else []) = _
          rw [if_pos hocc]
          show (monGo m'.length (dipAt a mu)).map _
            = (monGo (sumNat (dipAt a mu)) (dipAt a mu)).map _
          rw [hfuel]
        have hrank : rankOf (a :: m') mu
            = ((List.range a).flatMap (rankBlk mu m'.length)).length
              + rankOf m' (dipAt a mu) := by
          show (List.range a).foldl (fun acc b =>
              if 0 < ground.getAt 0 mu b then
                acc + countMon (dipAt b mu)
              else acc) 0 + rankOf m' (dipAt a mu) = _
          rw [hpref]
        have hlt' : rankOf m' (dipAt a mu)
            < (rankBlk mu m'.length a).length := by
          rw [hblka, ground.length_map]
          exact ihlt
        constructor
        · rw [hrank, hsplit, ground.length_append,
            ground.length_append]
          exact Nat.add_lt_add_left
            (Nat.lt_of_lt_of_le hlt'
              (Nat.le_add_right (rankBlk mu m'.length a).length
                (tail.flatMap (rankBlk mu m'.length)).length))
            ((List.range a).flatMap (rankBlk mu m'.length)).length
        · rw [hrank, hsplit,
            ground.getAt_append []
              ((List.range a).flatMap (rankBlk mu m'.length))
              (rankBlk mu m'.length a
                ++ tail.flatMap (rankBlk mu m'.length)) _,
            if_neg (Nat.not_lt.mpr (Nat.le_add_right _ _)),
            addSubSelfL,
            ground.getAt_append [] (rankBlk mu m'.length a)
              (tail.flatMap (rankBlk mu m'.length)) _,
            if_pos hlt', hblka,
            ground.getAt_map [] [] (fun m => a :: m)
              (monomialsAt (dipAt a mu)) _ ihlt, ihget]

/-- `rankOf`'s inverse read at a listed place: the rank of the
enumeration's own entry is that entry's place, the positional read
injective on the distinct family. -/
theorem rankOf_getAt (mu : List Nat) (k : Nat)
    (hk : k < (monomialsAt mu).length) :
    rankOf (ground.getAt [] (monomialsAt mu) k) mu = k := by
  have hm := member_conditions
    (ground.countOf_getAt_pos [] (monomialsAt mu) k hk)
  have hr := rankOf_read (ground.getAt [] (monomialsAt mu) k) mu
    hm.1 hm.2
  exact ground.getAt_inj_distinct ([] : List Nat) (monomialsAt mu)
    (monomialsAt_distinct mu) _ k hr.1 hk hr.2


/-- The pair fold as the free double range fold, one inner range
per top key: the guard-free companion of `pairsFold`, each shape
consumed at its own sites. -/
theorem pairsFold_free (F : Nat × Nat → Nat) : ∀ L : Nat,
    ground.famFold Nat.add 0 F (pairsOf L)
      = ground.famFold Nat.add 0
          (fun d => ground.famFold Nat.add 0 (fun j => F (j, d))
            (List.range d)) (List.range L)
  | 0 => rfl
  | L + 1 => by
    rw [show pairsOf (L + 1)
        = pairsOf L ++ (List.range L).map (fun j => (j, L)) from rfl,
      ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add F
        (pairsOf L) ((List.range L).map (fun j => (j, L))),
      ground.famFold_map Nat.add 0 F (fun j => (j, L)) (List.range L),
      pairsFold_free F L, ground.range_succ L,
      ground.famFold_snoc (fun d => ground.famFold Nat.add 0
        (fun j => F (j, d)) (List.range d)) (List.range L) L]
    rfl

/-- The place pairs' fold as the double fold over the letters at
the order guard. -/
theorem pairsFold (F : Nat × Nat → Nat) : ∀ d : Nat,
    ground.famFold Nat.add 0 F (pairsOf d)
      = ground.famFold Nat.add 0
        (fun a => ground.famFold Nat.add 0
          (fun b => if a < b then F (a, b) else 0)
          (List.range d))
        (List.range d)
  | 0 => rfl
  | d + 1 => by
    have hsplit : ∀ a : Nat, ground.famFold Nat.add 0
        (fun b => if a < b then F (a, b) else 0)
        (List.range (d + 1))
        = ground.famFold Nat.add 0
          (fun b => if a < b then F (a, b) else 0)
          (List.range d)
          + (if a < d then F (a, d) else 0) := by
      intro a
      rw [ground.range_succ d,
        ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add
          _ (List.range d) [d]]
      show _ + ((if a < d then F (a, d) else 0) + 0) = _
      rw [Nat.add_zero]
    have hzero : ground.famFold Nat.add 0
        (fun b => if d < b then F (d, b) else 0)
        (List.range d) = 0 :=
      (ground.famFold_congr_members Nat.add 0 _ (fun _ => 0)
        (List.range d) (fun b hb =>
          if_neg (fun hc => Nat.lt_irrefl d
            (Nat.lt_trans hc (ltOfMem hb))))).trans
        (ground.famFold_zero _ (fun _ => rfl) _)
    rw [show pairsOf (d + 1)
        = pairsOf d ++ (List.range d).map (fun j => (j, d))
        from rfl,
      ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add
        F _ _,
      ground.famFold_map Nat.add 0 F (fun j => (j, d))
        (List.range d),
      pairsFold F d,
      ground.famFold_congr_all Nat.add 0 _ _ hsplit
        (List.range (d + 1)),
      ground.range_succ d,
      ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add
        _ (List.range d) [d],
      show ground.famFold Nat.add 0
          (fun a => ground.famFold Nat.add 0
            (fun b => if a < b then F (a, b) else 0)
            (List.range d)
            + (if a < d then F (a, d) else 0)) [d]
        = (ground.famFold Nat.add 0
            (fun b => if d < b then F (d, b) else 0)
            (List.range d)
            + (if d < d then F (d, d) else 0)) + 0 from rfl,
      hzero, if_neg (Nat.lt_irrefl d)]
    have hfin : ground.famFold Nat.add 0
        (fun a => ground.famFold Nat.add 0
          (fun b => if a < b then F (a, b) else 0)
          (List.range d))
        (List.range d)
        + ground.famFold Nat.add 0 (fun j => F (j, d))
          (List.range d)
        = ground.famFold Nat.add 0
          (fun a => ground.famFold Nat.add 0
            (fun b => if a < b then F (a, b) else 0)
            (List.range d)
            + (if a < d then F (a, d) else 0))
          (List.range d) := by
      rw [ground.famFold_congr_members Nat.add 0
          (fun j => F (j, d))
          (fun a => if a < d then F (a, d) else 0)
          (List.range d)
          (fun a ha => (if_pos (ltOfMem ha)).symm),
        ← ground.famFold_add_split
          (fun a => ground.famFold Nat.add 0
            (fun b => if a < b then F (a, b) else 0)
            (List.range d))
          (fun a => if a < d then F (a, d) else 0)
          (List.range d)]
    exact hfin

/-- The key box: the length-`d` keys at entries below the bound,
the per-key box at the constant bound (`ground.boxAll`), the
vacant alphabet its own two lines. -/
def keyBox (d B : Nat) : List (List Nat) :=
  match B with
  | 0 =>
    match d with
    | 0 => [[]]
    | _ + 1 => []
  | B' + 1 => ground.boxAll (List.replicate d B')



theorem keyBox_len :
    ∀ (d B : Nat) (w : List Nat),
      0 < ground.countOf w (keyBox d B) → w.length = d
  | 0, 0, [], _ => rfl
  | 0, 0, _ :: _, h =>
    absurd (show (0 : Nat) < 0 from h) (Nat.lt_irrefl 0)
  | d + 1, 0, w, h =>
    absurd (show (0 : Nat) < 0 from h) (Nat.lt_irrefl 0)
  | d, B' + 1, w, h => by
    have h' : 0 < ground.countOf w
        (ground.boxAll (List.replicate d B')) := h
    rw [ground.boxAll_countOf] at h'
    by_cases hcond : w.length = (List.replicate d B').length
        ∧ (∀ i, i < (List.replicate d B').length →
            ground.getAt 0 w i ≤ ground.getAt 0 (List.replicate d B') i)
    · exact hcond.1.trans (ground.length_replicate B' d)
    · rw [if_neg hcond] at h'
      exact absurd h' (Nat.lt_irrefl 0)


theorem keyBox_count :
    ∀ (d B : Nat) (w : List Nat), w.length = d →
      (∀ i, i < d → ground.getAt 0 w i < B) →
      ground.countOf w (keyBox d B) = 1
  | 0, 0, [], _, _ => rfl
  | 0, 0, _ :: _, h, _ => Nat.noConfusion h
  | d + 1, 0, _, _, hent =>
    absurd (hent 0 (Nat.succ_pos d)) (Nat.not_lt_zero _)
  | d, B' + 1, w, hlen, hent => by
    show ground.countOf w (ground.boxAll (List.replicate d B')) = 1
    rw [ground.boxAll_countOf]
    refine if_pos ⟨hlen.trans (ground.length_replicate B' d).symm, ?_⟩
    intro i hi
    have hid : i < d := by
      rw [ground.length_replicate] at hi
      exact hi
    rw [ground.getAt_replicate 0 B' d i hid]
    exact Nat.le_of_lt_succ (hent i hid)


theorem keyBox_ent :
    ∀ (d B : Nat) (w : List Nat),
      0 < ground.countOf w (keyBox d B) →
      ∀ t, t < d → ground.getAt 0 w t < B
  | 0, _, _, _, t, ht => absurd ht (Nat.not_lt_zero t)
  | d + 1, 0, w, h, _, _ =>
    absurd (show (0 : Nat) < 0 from h) (Nat.lt_irrefl 0)
  | d + 1, B' + 1, w, h, t, ht => by
    have h' : 0 < ground.countOf w
        (ground.boxAll (List.replicate (d + 1) B')) := h
    rw [ground.boxAll_countOf] at h'
    by_cases hcond : w.length = (List.replicate (d + 1) B').length
        ∧ (∀ i, i < (List.replicate (d + 1) B').length →
            ground.getAt 0 w i
              ≤ ground.getAt 0 (List.replicate (d + 1) B') i)
    · have hti : t < (List.replicate (d + 1) B').length := by
        rw [ground.length_replicate]
        exact ht
      have hle := hcond.2 t hti
      rw [ground.getAt_replicate 0 B' (d + 1) t
        (by rw [ground.length_replicate] at hti; exact hti)] at hle
      exact Nat.lt_of_le_of_lt hle (Nat.lt_succ_self B')
    · rw [if_neg hcond] at h'
      exact absurd h' (Nat.lt_irrefl 0)


/-- The point collapse over the key box: a guarded read at an
edit map's preimage picks the one box key. -/
theorem boxPick {d B : Nat} (G : List Nat → Nat)
    (E : List Nat → List Nat) (K w₀ : List Nat)
    (hlen : w₀.length = d)
    (hent : ∀ t, t < d → ground.getAt 0 w₀ t < B)
    (hfwd : ∀ w, 0 < ground.countOf w (keyBox d B) →
      K = E w → w = w₀)
    (hbwd : E w₀ = K) :
    ground.famFold Nat.add 0
      (fun w => if K = E w then G w else 0) (keyBox d B)
    = G w₀ := by
  refine (ground.famFold_congr_members Nat.add 0 _
    (fun w => if w = w₀ then G w else 0) (keyBox d B)
    (fun w hw => ?_)).trans
    (ground.famFold_pick G w₀ (keyBox d B)
      (keyBox_count d B w₀ hlen hent))
  by_cases hE : K = E w
  · rw [if_pos hE, if_pos (hfwd w hw hE)]
  · rw [if_neg hE,
      if_neg (fun hww : w = w₀ => hE (by rw [hww, hbwd]))]

theorem boxPickZero {d B : Nat} (G : List Nat → Nat)
    (E : List Nat → List Nat) (K : List Nat)
    (hnone : ∀ w, 0 < ground.countOf w (keyBox d B) →
      ¬ K = E w) :
    ground.famFold Nat.add 0
      (fun w => if K = E w then G w else 0) (keyBox d B)
    = 0 := by
  refine (ground.famFold_congr_members Nat.add 0 _
    (fun _ => (0 : Nat)) (keyBox d B)
    (fun w hw => ?_)).trans (ground.famFold_zero
      (fun _ => (0 : Nat)) (fun _ => rfl) (keyBox d B))
  rw [if_neg (hnone w hw)]


/-- The content enumeration is complete: a family of the stated
letter count is a member of the enumeration at its own box
total. -/
theorem mem_allContents : ∀ (d : Nat) (c : List Nat),
    c.length = d → c ∈ allContents d (c.foldl (fun a b => a + b) 0)
  | 0, [], _ => List.Mem.head _
  | 0, _ :: _, h => Nat.noConfusion h
  | _ + 1, [], h => Nat.noConfusion h
  | d + 1, a :: t, hl => by
    have hsum : (a :: t).foldl (fun x b => x + b) 0
        = a + t.foldl (fun x b => x + b) 0 := by
      show t.foldl (fun x b => x + b) (0 + a)
        = a + t.foldl (fun x b => x + b) 0
      rw [ground.foldlSum (fun b => b) t (0 + a),
        ground.foldlSum (fun b => b) t 0, Nat.zero_add, Nat.zero_add]
    rw [hsum]
    show a :: t ∈ (List.range
        (a + t.foldl (fun x b => x + b) 0 + 1)).flatMap
      (fun j => (allContents d
        (a + t.foldl (fun x b => x + b) 0 - j)).map (fun m => j :: m))
    refine ground.mem_flatMap_to _ (a := a) ?_ ?_
    · exact ground.memRange
        (Nat.lt_succ_of_le (Nat.le_add_right a _))
    · show a :: t ∈ (allContents d
        (a + t.foldl (fun x b => x + b) 0 - a)).map (fun m => a :: m)
      rw [ground.addSubSelfL a (t.foldl (fun x b => x + b) 0)]
      exact ground.mem_map_to (fun m => a :: m)
        (mem_allContents d t (Nat.succ.inj hl))

/-- The content enumeration's members carry the stated letter count
and box total. -/
theorem allContents_reads : ∀ (d k : Nat) (mu : List Nat),
    0 < ground.countOf mu (allContents d k) →
    mu.length = d ∧ sumNat mu = k
  | 0, 0, mu, h => by
    by_cases hm : mu = []
    · rw [hm]
      exact ⟨rfl, rfl⟩
    · have h0 : ground.countOf mu (allContents 0 0) = 0 :=
        ground.countOf_head_ne hm []
      rw [h0] at h
      exact absurd h (Nat.lt_irrefl 0)
  | 0, _ + 1, _, h => absurd h (Nat.lt_irrefl 0)
  | d + 1, k, mu, h => by
    have hm : mu ∈ (List.range (k + 1)).flatMap (fun j =>
        (allContents d (k - j)).map (fun m => j :: m)) :=
      ground.mem_of_countOf_pos mu _ h
    match ground.mem_flatMap_of _ (List.range (k + 1)) mu hm with
    | ⟨jj, hjm, hmm⟩ =>
      match ground.mem_map_of _ (allContents d (k - jj)) mu
          hmm with
      | ⟨m, hmem, hcons⟩ =>
        have hjk : jj ≤ k := Nat.le_of_lt_succ
          (ground.ltOfMemRange hjm)
        have hIH := allContents_reads d (k - jj) m
          (ground.countOf_pos_of_mem hmem)
        refine ⟨?_, ?_⟩
        · rw [← hcons]
          show m.length + 1 = d + 1
          rw [hIH.1]
        · rw [← hcons]
          show jj + sumNat m = k
          rw [hIH.2, Nat.add_comm]
          exact ground.subAdd hjk

/-- The shape at a stated row list, the occupancies the
consecutive gaps: the head's gap at its successor with the last
row its own column count. -/
def shapeOf : List Nat → Shape
  | [] => []
  | [a] => [a]
  | a :: b :: t => (a - b) :: shapeOf (b :: t)

/-- The shape inverse keeps the length. -/
theorem length_shapeOf : ∀ mu : List Nat,
    (shapeOf mu).length = mu.length
  | [] => rfl
  | [_] => rfl
  | _ :: b :: t => congrArg Nat.succ (length_shapeOf (b :: t))

private theorem sumNat_shapeOf : ∀ (mu : List Nat) (a : Nat),
    (∀ k, k + 1 < (a :: mu).length →
      ground.getAt 0 (a :: mu) (k + 1)
        ≤ ground.getAt 0 (a :: mu) k) →
    sumNat (shapeOf (a :: mu)) = a
  | [], a, _ => rfl
  | b :: t, a, hdom => by
    show (a - b) + sumNat (shapeOf (b :: t)) = a
    rw [sumNat_shapeOf t b
      (fun k hk => hdom (k + 1) (Nat.succ_lt_succ hk))]
    have hba : b ≤ a :=
      hdom 0 (Nat.succ_lt_succ (Nat.succ_pos t.length))
    match Nat.le.dest hba with
    | ⟨c, hc⟩ =>
      rw [← hc, addSubSelfL b c]
      exact Nat.add_comm c b

/-- The shape inverse reads back at a dominant list: the row list
of the gap shape is the list itself. -/
theorem rowList_shapeOf : ∀ mu : List Nat,
    (∀ k, k + 1 < mu.length →
      ground.getAt 0 mu (k + 1) ≤ ground.getAt 0 mu k) →
    rowList (shapeOf mu) = mu
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: t, hdom => by
    show ((a - b) + sumNat (shapeOf (b :: t)))
        :: rowList (shapeOf (b :: t)) = a :: b :: t
    rw [sumNat_shapeOf t b
        (fun k hk => hdom (k + 1) (Nat.succ_lt_succ hk)),
      rowList_shapeOf (b :: t)
        (fun k hk => hdom (k + 1) (Nat.succ_lt_succ hk))]
    have hba : b ≤ a :=
      hdom 0 (Nat.succ_lt_succ (Nat.succ_pos t.length))
    match Nat.le.dest hba with
    | ⟨c, hc⟩ =>
      rw [← hc, addSubSelfL b c, Nat.add_comm c b]

/-- The shape inverse closes the round trip: the gap shape of a
shape's own row list is the shape. -/
theorem shapeOf_rowList (x : Shape) : shapeOf (rowList x) = x :=
  rowList_inj _ _ (rowList_shapeOf (rowList x)
    (fun k hk => rowList_le x k (by rw [← length_rowList x]; exact hk)))

/-- The row list's last entry is the shape's own last occupancy,
the off-list read vacant. -/
theorem rowList_last (x : Shape) (r : Nat) (hlen : x.length = r + 1) :
    ground.getAt 0 (rowList x) r = ground.getAt 0 x r := by
  have hg := rowList_gap x r (by rw [hlen]; exact Nat.lt_succ_self r)
  rw [ground.getAt_over 0 (rowList x) (r + 1)
      (by rw [length_rowList, hlen]; exact Nat.le_refl _),
    Nat.add_zero] at hg
  exact hg

/-! The shape enumeration's reads: a last occupancy adds its
columns' boxes, every shape of the stated width sits in the
enumeration at its own degree, a member has the stated width and
degree, and each shape is listed at most once. -/

/-- A last occupancy adds its columns' boxes: the degree of a shape
with a last length appended grows by the appended count at the new
length. -/
theorem degree_snoc : ∀ (s : Shape) (j : Nat),
    degree (s ++ [j]) = degree s + j * (s.length + 1)
  | [], j => by
    show j + 0 + 0 = 0 + j * (0 + 1)
    rw [Nat.add_zero, Nat.add_zero, Nat.zero_add, Nat.mul_one]
  | a :: t, j => by
    show a + sumNat (t ++ [j]) + degree (t ++ [j])
      = a + sumNat t + degree t + j * (t.length + 1 + 1)
    rw [sumNat_append t [j], degree_snoc t j]
    show a + (sumNat t + (j + 0)) + (degree t + j * (t.length + 1))
      = a + sumNat t + degree t + j * (t.length + 1 + 1)
    rw [Nat.add_zero, Nat.mul_succ j (t.length + 1),
      ← Nat.add_assoc a (sumNat t) j,
      Nat.add_assoc (a + sumNat t) j (degree t + j * (t.length + 1)),
      Nat.add_comm j (degree t + j * (t.length + 1)),
      ← Nat.add_assoc (a + sumNat t) (degree t + j * (t.length + 1)) j,
      ← Nat.add_assoc (a + sumNat t) (degree t) (j * (t.length + 1)),
      Nat.add_assoc (a + sumNat t + degree t) (j * (t.length + 1)) j]

/-- One raised occupancy adds its column's boxes to the degree. -/
theorem degree_bumpAt : ∀ (i : Nat) (s : Shape), i < s.length →
    degree (ground.bumpAt i s) = degree s + (i + 1)
  | _, [], h => absurd h (Nat.not_lt_zero _)
  | 0, n :: t, _ => by
    show n + 1 + sumNat t + degree t = n + sumNat t + degree t + 1
    rw [Nat.add_right_comm n 1 (sumNat t),
      Nat.add_right_comm (n + sumNat t) 1 (degree t)]
  | i + 1, n :: t, h => by
    show n + sumNat (ground.bumpAt i t) + degree (ground.bumpAt i t)
        = n + sumNat t + degree t + (i + 1 + 1)
    rw [sumNat_bumpAt i t (Nat.lt_of_succ_lt_succ h),
      degree_bumpAt i t (Nat.lt_of_succ_lt_succ h),
      ← Nat.add_assoc n (sumNat t) 1,
      Nat.add_right_comm (n + sumNat t) 1 (degree t + (i + 1)),
      ← Nat.add_assoc (n + sumNat t) (degree t) (i + 1),
      Nat.add_assoc (n + sumNat t + degree t) (i + 1) 1]

/-- The degree joins its reversal's at the width's successor
against the occupancy total, the position weights pairing to one
count per column. -/
theorem degree_reverse_add : ∀ w : Shape,
    degree w + degree w.reverse = (w.length + 1) * sumNat w
  | [] => rfl
  | n :: t => by
    rw [ground.reverse_cons n t]
    show n + sumNat t + degree t + degree (t.reverse ++ [n])
        = (t.length + 1 + 1) * (n + sumNat t)
    rw [degree_snoc t.reverse n, ground.length_reverse t]
    rw [show n + sumNat t + degree t
          + (degree t.reverse + n * (t.length + 1))
        = n + sumNat t + n * (t.length + 1)
          + (degree t + degree t.reverse) from by
      rw [Nat.add_assoc (n + sumNat t) (degree t)
          (degree t.reverse + n * (t.length + 1)),
        Nat.add_comm (degree t.reverse) (n * (t.length + 1)),
        ← Nat.add_assoc (degree t) (n * (t.length + 1))
          (degree t.reverse),
        Nat.add_comm (degree t) (n * (t.length + 1)),
        Nat.add_assoc (n * (t.length + 1)) (degree t)
          (degree t.reverse),
        ← Nat.add_assoc (n + sumNat t) (n * (t.length + 1))
          (degree t + degree t.reverse)]]
    rw [degree_reverse_add t]
    rw [Nat.mul_add (t.length + 1 + 1) n (sumNat t)]
    rw [show (t.length + 1 + 1) * n = n + n * (t.length + 1) from by
      rw [Nat.mul_comm (t.length + 1 + 1) n, Nat.mul_succ,
        Nat.add_comm (n * (t.length + 1)) n]]
    rw [show (t.length + 1 + 1) * sumNat t
        = sumNat t + (t.length + 1) * sumNat t from by
      rw [Nat.succ_mul (t.length + 1) (sumNat t),
        Nat.add_comm ((t.length + 1) * sumNat t) (sumNat t)]]
    rw [Nat.add_assoc (n + sumNat t) (n * (t.length + 1))
        ((t.length + 1) * sumNat t),
      Nat.add_add_add_comm n (sumNat t) (n * (t.length + 1))
        ((t.length + 1) * sumNat t)]

/-- The shape enumeration is complete: a shape of the stated width
is a member of the enumeration at its own degree. -/
theorem mem_allShapes : ∀ (d : Nat) (s : Shape),
    s.length = d → s ∈ allShapes d (degree s)
  | 0, [], _ => List.Mem.head _
  | 0, _ :: _, h => Nat.noConfusion h
  | d + 1, s, hl =>
    match ground.snoc_split d s hl with
    | ⟨s', j, hs, hl'⟩ => by
      rw [hs, degree_snoc s' j, hl']
      have hjle : j ≤ j * (d + 1) := by
        rw [Nat.mul_succ j d]
        exact Nat.le_add_left j (j * d)
      have hlt : j * (d + 1) ≤ degree s' + j * (d + 1) :=
        Nat.le_add_left _ _
      show s' ++ [j] ∈ (List.range (degree s' + j * (d + 1) + 1)).flatMap
        (fun j' => if j' * (d + 1) ≤ degree s' + j * (d + 1) then
          (allShapes d (degree s' + j * (d + 1) - j' * (d + 1))).map
            (fun x => x ++ [j'])
        else [])
      refine ground.mem_flatMap_to _ (a := j) ?_ ?_
      · exact ground.memRange
          (Nat.lt_succ_of_le (Nat.le_trans hjle hlt))
      · rw [if_pos hlt, Nat.add_comm (degree s') (j * (d + 1)),
          ground.addSubSelfL (j * (d + 1)) (degree s')]
        exact ground.mem_map_to (fun x => x ++ [j])
          (mem_allShapes d s' hl')

/-- The shape enumeration is sound: a member has the stated width
and the stated degree. -/
theorem allShapes_sound : ∀ (d k : Nat) (s : Shape),
    s ∈ allShapes d k → s.length = d ∧ degree s = k
  | 0, 0, s, h => by
    have h' : s ∈ [([] : Shape)] := h
    cases h' with
    | head => exact ⟨rfl, rfl⟩
    | tail _ h2 => exact nomatch h2
  | 0, _ + 1, _, h => nomatch h
  | d + 1, k, s, h => by
    match ground.mem_flatMap_of _ _ s h with
    | ⟨j, hj, hs⟩ =>
      by_cases hjk : j * (d + 1) ≤ k
      · rw [if_pos hjk] at hs
        match ground.mem_map_of _ _ s hs with
        | ⟨x, hx, hxs⟩ =>
          obtain ⟨hxl, hxd⟩ := allShapes_sound d (k - j * (d + 1)) x hx
          rw [← hxs, ground.length_append, degree_snoc x j, hxl, hxd]
          refine ⟨rfl, ?_⟩
          exact ground.subAdd hjk
      · rw [if_neg hjk] at hs
        exact nomatch hs

/-- Each shape is listed at most once in the enumeration: the
last occupancy picks its branch and the prefixes' enumeration
lists the prefix at most once. -/
theorem countOf_allShapes_le : ∀ (d k : Nat) (s : Shape),
    ground.countOf s (allShapes d k) ≤ 1
  | 0, 0, s => by
    show ground.countOf s ([] :: []) ≤ 1
    rw [ground.countOf_cons]
    by_cases hs : s = []
    · rw [if_pos hs]
      exact Nat.le_refl 1
    · rw [if_neg hs]
      exact Nat.zero_le 1
  | 0, _ + 1, _ => Nat.zero_le 1
  | d + 1, k, s => by
    show ground.countOf s ((List.range (k + 1)).flatMap
      (fun j => if j * (d + 1) ≤ k then
        (allShapes d (k - j * (d + 1))).map (fun x => x ++ [j])
      else [])) ≤ 1
    rw [ground.countOf_flatMap]
    match hs : s.length with
    | 0 =>
      have hnil : s = [] := by
        match s, hs with
        | [], _ => rfl
        | _ :: _, h => exact Nat.noConfusion h
      refine Nat.le_trans (Nat.le_of_eq ?_) (Nat.zero_le 1)
      refine ground.famFold_zero _ ?_ (List.range (k + 1))
      intro j
      by_cases hjk : j * (d + 1) ≤ k
      · rw [if_pos hjk, hnil]
        exact ground.countOf_nil_snocMap j _
      · rw [if_neg hjk]
        rfl
    | n + 1 =>
      match ground.snoc_split n s hs with
      | ⟨s', j, hsj, hl'⟩ =>
        refine ground.famFold_le_one_at _ j (List.range (k + 1)) ?_ ?_ ?_
        · intro i _ hij
          by_cases hik : i * (d + 1) ≤ k
          · rw [if_pos hik, hsj]
            exact ground.countOf_snocMap_ne s' j i hij _
          · rw [if_neg hik]
            rfl
        · by_cases hjk : j * (d + 1) ≤ k
          · rw [if_pos hjk, hsj,
              ground.countOf_map_inj (fun x => x ++ [j]) s' _
                (fun x _ hx => ground.snoc_inj x s' j hx)]
            exact countOf_allShapes_le d (k - j * (d + 1)) s'
          · rw [if_neg hjk]
            exact Nat.zero_le 1
        · rw [countOf_range j (k + 1)]
          by_cases hjk : j < k + 1
          · rw [if_pos hjk]
            exact Nat.le_refl 1
          · rw [if_neg hjk]
            exact Nat.zero_le 1


/-- The vacant degree's enumeration is the all-vacant shape alone. -/
theorem allShapes_zero : ∀ d : Nat,
    allShapes d 0 = [List.replicate d 0]
  | 0 => rfl
  | d + 1 => by
    show ((if 0 * (d + 1) ≤ 0 then
        (allShapes d (0 - 0 * (d + 1))).map (fun s => s ++ [0])
      else []) ++ [])
      = [List.replicate (d + 1) 0]
    rw [if_pos (Nat.le_of_eq (Nat.zero_mul (d + 1))),
      Nat.zero_mul (d + 1)]
    show (allShapes d 0).map (fun s => s ++ [0]) ++ []
      = [List.replicate (d + 1) 0]
    rw [allShapes_zero d]
    show [List.replicate d 0 ++ [0]] ++ []
      = [List.replicate (d + 1) 0]
    rw [ground.replicate_snoc 0 d]
    rfl

/-- The unit assignment sits once in the place enumeration. -/
theorem countRangePerms (d : Nat) :
    ground.countOf (List.range d) (perms d) = 1 := by
  have h1 : (List.range d).length = sumNat (List.replicate d 1) := by
    rw [length_range, sumNat_replicate_one d]
  have h2 : content (List.replicate d (1 : Nat)).length (List.range d)
      = List.replicate d 1 := by
    rw [ground.length_replicate 1 d]
    show (List.range d).map
        (fun i => ground.countOf i (List.range d))
      = List.replicate d 1
    rw [ground.map_congr_members _ (fun _ => (1 : Nat))
        (List.range d) (fun i hi => by
          by_cases hid : i < d
          · rw [countOf_range i d, if_pos hid]
          · rw [countOf_range i d, if_neg hid] at hi
            exact absurd hi (Nat.lt_irrefl 0)),
      ground.map_const (1 : Nat), length_range]
  show ground.countOf (List.range d)
    (monomialsAt (List.replicate d 1)) = 1
  rw [countOf_monomialsAt, if_pos ⟨h1, h2⟩]

/-- A list at the count with every letter at most once and every
letter below the count occupied is a member of the permutations:
the content at the count reads the all-ones family, the
enumeration's own count. -/
theorem perm_of_counts (d : Nat) (l : List Nat) (hlen : l.length = d)
    (hdist : ∀ x, ground.countOf x l ≤ 1)
    (hcov : ∀ x, x < d → 0 < ground.countOf x l) :
    0 < ground.countOf l (perms d) := by
  show 0 < ground.countOf l (monomialsAt (List.replicate d 1))
  rw [countOf_monomialsAt]
  have hc : l.length = sumNat (List.replicate d 1)
      ∧ content (List.replicate d 1).length l = List.replicate d 1 := by
    refine ⟨by rw [sumNat_replicate_one]; exact hlen, ?_⟩
    rw [ground.length_replicate 1 d]
    refine ground.getAt_ext 0 _ _
      (by rw [content_length, ground.length_replicate]) ?_
    intro x hx
    rw [content_length] at hx
    rw [getAt_contentAt d l x hx, ground.getAt_replicate 0 1 d x hx]
    exact Nat.le_antisymm (hdist x) (hcov x hx)
  rw [if_pos hc]
  exact Nat.succ_pos 0

/-- Membership from the entry reads: a family at the place count,
its entries below that count and its keys read injectively, is an
enumeration member — the entries are distinct and cover the
alphabet, so every letter's count is the range's own. -/
theorem perm_of_reads (n : Nat) (l : List Nat) (hlen : l.length = n)
    (hbnd : ∀ i, i < n → ground.getAt 0 l i < n)
    (hinj : ∀ i j, i < n → j < n →
      ground.getAt 0 l i = ground.getAt 0 l j → i = j) :
    0 < ground.countOf l (perms n) := by
  have hdist : ∀ x, ground.countOf x l ≤ 1 :=
    ground.distinctList_all (ground.distinct_of_getAt_inj 0 l
      (fun p q hp hq he =>
        hinj p q (Nat.lt_of_lt_of_le hp (Nat.le_of_eq hlen))
          (Nat.lt_of_lt_of_le hq (Nat.le_of_eq hlen)) he))
  have hval : ∀ x, 0 < ground.countOf x l → x < n := by
    intro x hx
    match ground.getAt_of_mem 0 (ground.mem_of_countOf_pos x l hx) with
    | ⟨k, hk, he⟩ =>
      rw [← he]
      exact hbnd k (Nat.lt_of_lt_of_le hk (Nat.le_of_eq hlen))
  have hocc : ∀ x, x < n → 0 < ground.countOf x l := by
    intro x hx
    match Nat.eq_zero_or_pos (ground.countOf x l) with
    | .inr hp => exact hp
    | .inl hz =>
      have hd2 : ∀ y, ground.countOf y (x :: l) ≤ 1 := by
        intro y
        rw [ground.countOf_cons]
        by_cases hyx : y = x
        · rw [if_pos hyx, hyx, hz]
          exact Nat.le_refl 1
        · rw [if_neg hyx, Nat.zero_add]
          exact hdist y
      have hl2 : ∀ y, 0 < ground.countOf y (x :: l) → y < n := by
        intro y hy
        by_cases hyx : y = x
        · rw [hyx]
          exact hx
        · refine hval y ?_
          rw [ground.countOf_cons, if_neg hyx, Nat.zero_add] at hy
          exact hy
      have hle := ground.length_le_of_distinct (x :: l) n hd2 hl2
      rw [show (x :: l).length = l.length + 1 from rfl, hlen] at hle
      exact absurd hle (Nat.not_succ_le_self n)
  have hpr : 0 < ground.countOf (List.range n)
      (monomialsAt (List.replicate n 1)) := by
    show 0 < ground.countOf (List.range n) (perms n)
    rw [countRangePerms n]
    exact Nat.succ_pos 0
  refine perm_member_of_counts hpr ?_ ?_
  · rw [ground.length_range n]
    exact hlen
  · intro x
    rw [ground.countOf_range x n]
    by_cases hx : x < n
    · rw [if_pos hx]
      exact Nat.le_antisymm (hdist x) (hocc x hx)
    · rw [if_neg hx]
      match Nat.eq_zero_or_pos (ground.countOf x l) with
      | .inl hz => exact hz
      | .inr hp => exact absurd (hval x hp) hx

/-- An adjacent exchange of the unit assignment sits in the place
enumeration once. -/
theorem countOf_adjSwap_perms (d k : Nat) :
    ground.countOf (ground.adjSwap k (List.range d)) (perms d) = 1 := by
  refine Nat.le_antisymm
    (monomialsAt_distinct (List.replicate d 1) _
      (ground.mem_of_countOf_pos _ _ ?_)) ?_
  all_goals
    refine perm_member_adjSwap ?_ k
    show 0 < ground.countOf (List.range d) (perms d)
    rw [countRangePerms d]
    exact Nat.succ_pos 0

/-! The tie tier at strictly descending displays: the unit-content
gap read and the raise's rigidity. -/

/-- The unit gap at a letter: a tie whose gap is the letter's unit
content is exactly a raise of the second display at that letter. -/
theorem tieGap_unit (d : Nat) (y z : List Nat)
    (hy : y.length = d) (hz : z.length = d) (i : Nat)
    (hi : i < d) :
    ground.tieGap y z = some (unitAt d i)
      ↔ y = ground.bumpAt i z := by
  have hul : (unitAt d i).length = d := length_unitAt d i
  have hug : ∀ k, ground.getAt 0 (unitAt d i) k
      = if k < d then (if k = i then 1 else 0) else 0 :=
    fun k => getAt_unitAt d i k
  constructor
  · intro hg
    obtain ⟨_, _, hent⟩ := ground.tieGap_reads y z _ hg
    refine ground.getAt_ext 0 y (ground.bumpAt i z)
      (by rw [ground.length_bumpAt, hy, hz]) (fun k hk => ?_)
    have hkd : k < d := by rw [← hy]; exact hk
    have he := hent k hk
    rw [hug k, if_pos hkd] at he
    by_cases hki : k = i
    · rw [hki] at he ⊢
      rw [if_pos rfl, Nat.add_comm] at he
      rw [ground.getAt_bumpAt_self i z (by rw [hz]; exact hi), ← he]
    · rw [if_neg hki, Nat.zero_add] at he
      rw [ground.getAt_bumpAt_ne i z k hki, ← he]
  · intro hb
    refine ground.tieGap_make y z _ (by rw [hul, hy])
      (by rw [hz, hy]) (fun k hk => ?_)
    have hkd : k < d := by rw [← hy]; exact hk
    rw [hug k, if_pos hkd, hb]
    by_cases hki : k = i
    · rw [hki, if_pos rfl,
        ground.getAt_bumpAt_self i z (by rw [hz]; exact hi),
        Nat.add_comm]
    · rw [if_neg hki, Nat.zero_add,
        ground.getAt_bumpAt_ne i z k hki]

/-- The tie's rigidity: at two strictly descending families of one
width, a permuted first family raised at one letter reading the
second forces the identity permutation, the raise then the source's
own. -/
theorem tie_rigid (d : Nat) (x y : List Nat)
    (hx : x.length = d) (hy : y.length = d)
    (hdx : ∀ i, i + 1 < d →
      ground.getAt 0 x (i + 1) < ground.getAt 0 x i)
    (hdy : ∀ i, i + 1 < d →
      ground.getAt 0 y (i + 1) < ground.getAt 0 y i)
    (p : List Nat)
    (hp : 0 < ground.countOf p (perms d))
    (i : Nat) (hi : i < d)
    (h : y = ground.bumpAt i (expo x p)) :
    p = List.range d ∧ y = ground.bumpAt i x := by
  obtain ⟨hplen, _, hpval, _⟩ := perm_member_reads hp
  have hel : (expo x p).length = d := by
    show (p.map (ground.getAt 0 x)).length = d
    rw [ground.length_map, hplen]
  have hie : i < (expo x p).length := by rw [hel]; exact hi
  have hix : i < x.length := by rw [hx]; exact hi
  have hdxl : ∀ k, k + 1 < x.length →
      ground.getAt 0 x (k + 1) < ground.getAt 0 x k :=
    fun k hk => hdx k (by rw [← hx]; exact hk)
  have hdyl : ∀ k, k + 1 < y.length →
      ground.getAt 0 y (k + 1) < ground.getAt 0 y k :=
    fun k hk => hdy k (by rw [← hy]; exact hk)
  have hcnt : ∀ w, ground.countOf w (expo x p)
      = ground.countOf w x :=
    fun w => countOf_comp d w hp hx
  have htop : ground.countOf
        (ground.getAt 0 (expo x p) i + 1) y
      = ground.countOf (ground.getAt 0 (expo x p) i + 1) x
        + 1 := by
    rw [h, ground.countOf_bumpAt_top i (expo x p) hie,
      hcnt (ground.getAt 0 (expo x p) i + 1)]
  have hzero : ground.countOf
      (ground.getAt 0 (expo x p) i + 1) x = 0 := by
    have hle := ground.countOf_desc_le y hdyl
      (ground.getAt 0 (expo x p) i + 1)
    rw [htop] at hle
    exact Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hle)
  have hvx : 0 < ground.countOf
      (ground.getAt 0 (expo x p) i) x := by
    rw [← hcnt]
    exact countOf_getAt_pos 0 (expo x p) i hie
  obtain ⟨i0, hi0, hgi0⟩ := ground.getAt_of_mem (0 : Nat)
    (ground.mem_of_countOf_pos _ x hvx)
  have hzero0 : ground.countOf (ground.getAt 0 x i0 + 1) x = 0 := by
    rw [hgi0]
    exact hzero
  have hdx' : ∀ k, k + 1 < (ground.bumpAt i0 x).length →
      ground.getAt 0 (ground.bumpAt i0 x) (k + 1)
        < ground.getAt 0 (ground.bumpAt i0 x) k := by
    intro k hk
    rw [ground.length_bumpAt] at hk
    by_cases hk1 : k + 1 = i0
    · have hkne : ¬ k = i0 := fun he =>
        absurd (hk1.trans he.symm) (Nat.ne_of_gt (Nat.lt_succ_self k))
      rw [hk1, ground.getAt_bumpAt_self i0 x hi0,
        ground.getAt_bumpAt_ne i0 x k hkne]
      have hlt : ground.getAt 0 x i0 < ground.getAt 0 x k := by
        rw [← hk1]
        exact hdxl k hk
      refine Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hlt) (fun he => ?_)
      have hpos : 0 < ground.countOf (ground.getAt 0 x i0 + 1) x := by
        rw [he]
        exact countOf_getAt_pos 0 x k (Nat.lt_of_succ_lt hk)
      rw [hzero0] at hpos
      exact Nat.lt_irrefl 0 hpos
    · by_cases hk0 : k = i0
      · rw [hk0, ground.getAt_bumpAt_self i0 x hi0,
          ground.getAt_bumpAt_ne i0 x (i0 + 1)
            (fun he => Nat.ne_of_gt (Nat.lt_succ_self i0) he)]
        rw [hk0] at hk
        exact Nat.lt_succ_of_lt (hdxl i0 hk)
      · rw [ground.getAt_bumpAt_ne i0 x (k + 1) hk1,
          ground.getAt_bumpAt_ne i0 x k hk0]
        exact hdxl k hk
  have hcx : ∀ w, ground.countOf w (ground.bumpAt i0 x)
      = ground.countOf w y := by
    intro w
    by_cases hw0 : w = ground.getAt 0 x i0
    · have h1 : ground.countOf w (ground.bumpAt i0 x) + 1
          = ground.countOf w x := by
        rw [hw0]
        exact ground.countOf_bumpAt_at i0 x hi0
      have h2 : ground.countOf w y + 1 = ground.countOf w x := by
        rw [h, hw0, hgi0,
          ground.countOf_bumpAt_at i (expo x p) hie,
          hcnt (ground.getAt 0 (expo x p) i)]
      exact ground.addCancelR 1 (h1.trans h2.symm)
    · by_cases hw1 : w = ground.getAt 0 x i0 + 1
      · rw [hw1, ground.countOf_bumpAt_top i0 x hi0, hgi0, htop]
      · rw [ground.countOf_bumpAt_ne i0 x w hw0 hw1, h,
          ground.countOf_bumpAt_ne i (expo x p) w
            (fun he => hw0 (he.trans hgi0.symm))
            (fun he => hw1 (he.trans (congrArg (fun z => z + 1)
              hgi0.symm))),
          hcnt w]
  have hxy : ground.bumpAt i0 x = y :=
    ground.descUnique (ground.bumpAt i0 x) y
      (by rw [ground.length_bumpAt, hx, hy]) hdx' hdyl hcx
  have hii0 : i = i0 := by
    by_cases hc : i = i0
    · exact hc
    · have h1 : ground.getAt 0 y i
          = ground.getAt 0 (expo x p) i + 1 := by
        rw [h, ground.getAt_bumpAt_self i (expo x p) hie]
      have h2 : ground.getAt 0 y i = ground.getAt 0 x i := by
        rw [← hxy, ground.getAt_bumpAt_ne i0 x i hc]
      have h3 : 0 < ground.countOf
          (ground.getAt 0 (expo x p) i + 1) x := by
        rw [h1.symm.trans h2]
        exact countOf_getAt_pos 0 x i hix
      rw [hzero] at h3
      exact absurd h3 (Nat.lt_irrefl 0)
  have hex : expo x p = x := by
    have hb : ground.bumpAt i (expo x p)
        = ground.bumpAt i x := by
      rw [← h, ← hxy, hii0]
    rw [← ground.dipAt_bumpAt_self i (expo x p), hb,
      ground.dipAt_bumpAt_self i x]
  refine ⟨?_, by rw [← hxy, hii0]⟩
  refine ground.getAt_ext 0 p (List.range d)
    (by rw [hplen, length_range]) (fun k hk => ?_)
  have hkd : k < d := by rw [← hplen]; exact hk
  rw [getAt_range d k hkd]
  have hpk : ground.getAt 0 p k < d := hpval _ (countOf_getAt_pos 0 p k hk)
  have hme : ground.getAt 0 x (ground.getAt 0 p k)
      = ground.getAt 0 x k := by
    rw [← ground.getAt_map 0 0 (ground.getAt 0 x) p k hk]
    show ground.getAt 0 (expo x p) k = ground.getAt 0 x k
    rw [hex]
  exact desc_inj hdxl (ground.getAt 0 p k) k
    (by rw [hx]; exact hpk) (by rw [hx]; exact hkd) hme


/-- A letter-pair move's entries are capped at the double. -/
theorem moveCap (d : Nat) (m : List Nat) (i j : Nat)
    (h2 : ground.getAt 0 m i = 2) (h0 : ground.getAt 0 m j = 0)
    (h1 : ∀ k, k < d → ¬ k = i → ¬ k = j → ground.getAt 0 m k = 1)
    (t : Nat) (ht : t < d) : ground.getAt 0 m t ≤ 2 := by
  by_cases hti : t = i
  · exact Nat.le_of_eq (by rw [hti, h2])
  · by_cases htj : t = j
    · rw [htj, h0]
      exact Nat.zero_le 2
    · rw [h1 t ht hti htj]
      exact Nat.le_succ 1

/-- A letter-pair move's doubled place is its raised place. -/
theorem movePlaceTwo (d : Nat) (m : List Nat) (i j : Nat)
    (h0 : ground.getAt 0 m j = 0)
    (h1 : ∀ k, k < d → ¬ k = i → ¬ k = j → ground.getAt 0 m k = 1)
    (t : Nat) (ht : t < d) (hv : ground.getAt 0 m t = 2) : t = i := by
  by_cases hti : t = i
  · exact hti
  · by_cases htj : t = j
    · rw [htj, h0] at hv
      exact absurd hv (by decide +kernel)
    · rw [h1 t ht hti htj] at hv
      exact absurd hv (by decide +kernel)

/-- A letter-pair move's vacant place is its lowered place. -/
theorem movePlaceZero (d : Nat) (m : List Nat) (i j : Nat)
    (h2 : ground.getAt 0 m i = 2)
    (h1 : ∀ k, k < d → ¬ k = i → ¬ k = j → ground.getAt 0 m k = 1)
    (t : Nat) (ht : t < d) (hv : ground.getAt 0 m t = 0) : t = j := by
  by_cases htj : t = j
  · exact htj
  · by_cases hti : t = i
    · rw [hti, h2] at hv
      exact absurd hv (by decide +kernel)
    · rw [h1 t ht hti htj] at hv
      exact absurd hv (by decide +kernel)

/-- The squeeze at a reversed place pair: a capped raise against a
strict rise pins the raise at the double, the lowering at the fold's
unit and the rise at one. -/
private theorem squeezeGap (a b u v : Nat) (hle : a ≤ 2) (huv : u < v)
    (hlt : b + v < a + u) : a = 2 ∧ b = 0 ∧ v = u + 1 := by
  obtain ⟨e, he⟩ := Nat.le.dest huv
  rw [← he] at hlt
  have hrw : b + (u + 1 + e) = b + 1 + e + u := by
    rw [Nat.add_assoc u 1 e, Nat.add_comm u (1 + e),
      ← Nat.add_assoc b (1 + e) u, ← Nat.add_assoc b 1 e]
  rw [hrw] at hlt
  have hcore : b + 1 + e < a := Nat.lt_of_add_lt_add_right hlt
  have hb1 : b + e + 1 ≤ 1 := by
    rw [Nat.add_right_comm b e 1]
    exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hcore hle)
  obtain ⟨hb0, he0⟩ :=
    ground.addZeroN (Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hb1))
  refine ⟨?_, hb0, ?_⟩
  · rw [hb0, he0] at hcore
    exact Nat.le_antisymm hle hcore
  · rw [← he, he0]

/-- The all-ones tie forces the identity permutation and the raised
display: the permuted display's reversal would break the target's
descent. -/
theorem tieOnes (d : Nat) (s c : Shape) (hs : s.length = d)
    (p : List Nat) (hp : 0 < ground.countOf p (perms d))
    (m : List Nat)
    (htie : ground.tieGap (display c) (expo (display s) p) = some m)
    (hme : ∀ k, k < d → ground.getAt 0 m k = 1) :
    p = List.range d ∧ display c = (display s).map (fun x => x + 1) := by
  obtain ⟨hplen, hpdist, hpval, _⟩ := perm_member_reads hp
  have hthl : (display s).length = d := by
    rw [length_display, hs]
  obtain ⟨_, hzl, hent⟩ := ground.tieGap_reads _ _ _ htie
  have hcdl : (display c).length = d := by
    rw [← hzl]
    show (p.map (ground.getAt 0 (display s))).length = d
    rw [ground.length_map, hplen]
  have hcl : c.length = d := by
    rw [← length_display c]
    exact hcdl
  have hw : ∀ t, t < d →
      ground.getAt 0 (expo (display s) p) t
        = ground.getAt 0 (display s) (ground.getAt 0 p t) := by
    intro t ht
    exact getAt_expo (display s) p t (by rw [hplen]; exact ht)
  have hcv : ∀ t, t < d → ground.getAt 0 (display c) t
      = ground.getAt 0 (display s) (ground.getAt 0 p t) + 1 := by
    intro t ht
    have he := hent t (by rw [hcdl]; exact ht)
    rw [hme t ht, hw t ht] at he
    rw [← he, Nat.add_comm]
  have hdesc : ∀ i, i + 1 < (display s).length →
      ground.getAt 0 (display s) (i + 1)
        < ground.getAt 0 (display s) i := by
    intro i hi
    rw [length_display] at hi
    exact display_desc s i hi
  have hnone : firstRev p = none := by
    cases hf : firstRev p with
    | none => rfl
    | some k =>
      obtain ⟨hk1, hk2⟩ := firstRev_some p k hf
      rw [hplen] at hk1
      have hpk : ground.getAt 0 p k < d :=
        hpval _ (ground.countOf_getAt_pos 0 p k
          (by rw [hplen]; exact Nat.lt_of_succ_lt hk1))
      have hlt : ground.getAt 0 (display s) (ground.getAt 0 p k)
          < ground.getAt 0 (display s) (ground.getAt 0 p (k + 1)) :=
        ground.desc_lt hdesc
          (ground.getAt 0 p k) (ground.getAt 0 p (k + 1)) hk2
          (by rw [hthl]; exact hpk)
      have hdc := display_desc c k (by rw [hcl]; exact hk1)
      rw [hcv k (Nat.lt_of_succ_lt hk1), hcv (k + 1) hk1] at hdc
      exact absurd (Nat.lt_of_succ_lt_succ hdc) (Nat.not_lt_of_gt hlt)
  have hpr : p = List.range d :=
    sorted_eq_range d p hplen hpdist hpval hnone
  refine ⟨hpr, ground.getAt_ext 0 _ _ ?_ ?_⟩
  · rw [hcdl, ground.length_map, hthl]
  · intro t ht
    rw [hcdl] at ht
    rw [hcv t ht, hpr, ground.getAt_range d t ht,
      ground.getAt_map 0 0 (fun x => x + 1) (display s) t
        (by rw [hthl]; exact ht)]

/-- A letter-pair-move tie off the identity forces the adjacent
exchange at a unit gap of the source display, the target the raised
display: the squeeze at the first reversal pins the raised and
lowered places, and the exchanged permutation reads the all-ones
tie. -/
theorem tieMove (d : Nat) (s c : Shape) (hs : s.length = d)
    (p : List Nat) (hp : 0 < ground.countOf p (perms d))
    (hne : ¬ p = List.range d) (m : List Nat)
    (htie : ground.tieGap (display c) (expo (display s) p) = some m)
    (i j : Nat)
    (h2 : ground.getAt 0 m i = 2) (h0 : ground.getAt 0 m j = 0)
    (h1 : ∀ k, k < d → ¬ k = i → ¬ k = j → ground.getAt 0 m k = 1) :
    ∃ k, k + 1 < d
      ∧ ground.getAt 0 (display s) k
          = ground.getAt 0 (display s) (k + 1) + 1
      ∧ p = ground.adjSwap k (List.range d)
      ∧ display c = (display s).map (fun x => x + 1) := by
  obtain ⟨hplen, hpdist, hpval, _⟩ := perm_member_reads hp
  have hthl : (display s).length = d := by
    rw [length_display, hs]
  obtain ⟨_, hzl0, _⟩ := ground.tieGap_reads _ _ _ htie
  have hcdl : (display c).length = d := by
    rw [← hzl0]
    show (p.map (ground.getAt 0 (display s))).length = d
    rw [ground.length_map, hplen]
  have hcl : c.length = d := by
    rw [← length_display c]
    exact hcdl
  have hdesc : ∀ t, t + 1 < (display s).length →
      ground.getAt 0 (display s) (t + 1)
        < ground.getAt 0 (display s) t := by
    intro t ht
    rw [length_display] at ht
    exact display_desc s t ht
  obtain ⟨_, _, hent⟩ := ground.tieGap_reads _ _ _ htie
  have hcv : ∀ t, t < d → ground.getAt 0 (display c) t
      = ground.getAt 0 m t
        + ground.getAt 0 (display s) (ground.getAt 0 p t) := by
    intro t ht
    have he := hent t (by rw [hcdl]; exact ht)
    rw [getAt_expo (display s) p t (by rw [hplen]; exact ht)] at he
    exact he.symm
  cases hf : firstRev p with
  | none =>
    exact absurd (sorted_eq_range d p hplen hpdist hpval hf) hne
  | some k =>
    obtain ⟨hk1, hk2⟩ := firstRev_some p k hf
    rw [hplen] at hk1
    have hk0 : k < d := Nat.lt_of_succ_lt hk1
    have hpk : ground.getAt 0 p k < d :=
      hpval _ (ground.countOf_getAt_pos 0 p k (by rw [hplen]; exact hk0))
    have hwlt : ground.getAt 0 (display s) (ground.getAt 0 p k)
        < ground.getAt 0 (display s) (ground.getAt 0 p (k + 1)) :=
      ground.desc_lt hdesc (ground.getAt 0 p k) (ground.getAt 0 p (k + 1))
        hk2 (by rw [hthl]; exact hpk)
    have hdc := display_desc c k (by rw [hcl]; exact hk1)
    rw [hcv (k + 1) hk1, hcv k hk0] at hdc
    obtain ⟨hmk2, hmk10, hvu⟩ := squeezeGap (ground.getAt 0 m k)
      (ground.getAt 0 m (k + 1))
      (ground.getAt 0 (display s) (ground.getAt 0 p k))
      (ground.getAt 0 (display s) (ground.getAt 0 p (k + 1)))
      (moveCap d m i j h2 h0 h1 k hk0) hwlt hdc
    have hki : k = i := movePlaceTwo d m i j h0 h1 k hk0 hmk2
    have hkj : k + 1 = j := movePlaceZero d m i j h2 h1 (k + 1) hk1 hmk10
    have hqlen : (ground.adjSwap k p).length = d := by
      rw [ground.length_adjSwap, hplen]
    have hqm : 0 < ground.countOf (ground.adjSwap k p) (perms d) :=
      perm_member_adjSwap hp k
    have hqtie : ground.tieGap (display c)
        (expo (display s) (ground.adjSwap k p))
          = some (List.replicate d 1) := by
      refine ground.tieGap_make _ _ _ ?_ ?_ ?_
      · rw [ground.length_replicate, hcdl]
      · show ((ground.adjSwap k p).map
          (ground.getAt 0 (display s))).length
          = (display c).length
        rw [ground.length_map, hqlen, hcdl]
      · intro t ht
        rw [hcdl] at ht
        rw [ground.getAt_replicate 0 1 d t ht,
          getAt_expo (display s)
            (ground.adjSwap k p) t (by rw [hqlen]; exact ht),
          hcv t ht]
        by_cases htk : t = k
        · rw [htk, ground.getAt_adjSwap_fst 0 k p (by rw [hplen]; exact hk1),
            hmk2, hvu, Nat.add_comm (ground.getAt 0
              (display s) (ground.getAt 0 p k)) 1,
            ← Nat.add_assoc 1 1 _]
        · by_cases htk1 : t = k + 1
          · rw [htk1, ground.getAt_adjSwap_snd 0 k p
              (by rw [hplen]; exact hk1), hmk10, hvu, Nat.zero_add,
              Nat.add_comm (ground.getAt 0
                (display s) (ground.getAt 0 p k)) 1]
          · rw [ground.getAt_adjSwap_ne 0 k p t htk htk1,
              h1 t ht (fun he => htk (he.trans hki.symm))
                (fun he => htk1 (he.trans hkj.symm))]
    obtain ⟨hqr, hdisp⟩ := tieOnes d s c hs (ground.adjSwap k p) hqm
      (List.replicate d 1) hqtie
      (fun t ht => ground.getAt_replicate 0 1 d t ht)
    refine ⟨k, hk1, ?_, ?_, hdisp⟩
    · have e1 : ground.getAt 0 p (k + 1) = k := by
        rw [← ground.getAt_adjSwap_fst 0 k p (by rw [hplen]; exact hk1),
          hqr, ground.getAt_range d k hk0]
      have e2 : ground.getAt 0 p k = k + 1 := by
        rw [← ground.getAt_adjSwap_snd 0 k p (by rw [hplen]; exact hk1),
          hqr, ground.getAt_range d (k + 1) hk1]
      have hvu' : ground.getAt 0 (display s)
            (ground.getAt 0 p (k + 1))
          = ground.getAt 0 (display s) (ground.getAt 0 p k) + 1 := hvu
      rw [e1, e2] at hvu'
      exact hvu'
    · rw [← hqr, ground.adjSwap_adjSwap]
end places
