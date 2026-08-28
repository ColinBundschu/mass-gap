import MassGap.Blockcount
import MassGap.Steinberg
import MassGap.Strings
/-!
`lem:pieri` — one box fuses up the shapes: `N^c_{μf} = 1` at every
dominant `c = μ + e_i` with the row's members exactly those targets,
`f` the one-box shape.  The row is a computation on the column
multiset — a new column of length one, or an occupied column grown
by one — and the identity with `def:blockcount`'s kernel-dimension
count is the stated decidable read `read`, its instances the check
module's pins; the general theorem `readAll` closes the row read at
any target of the positive width, the tex's derivation
`cor:steinberg` at the one-box factor — whose block is the
fundamental one, its span the unit contents, so the ties read the
target's display as a raise of the source's at one letter.  The
complement tier mirrors it at the complement's one-column shape:
`rowD` the one-box withdrawals of the full-column raise, `readD`
the decidable row read, and `readAllD` the general theorem — the
factor's span contents are the full column's withdrawn letters at
one count each (`strings.countCongr` transporting each to the top
line's count, the sorted representative's dominance cap refusing a
repeated letter), and the ties read the target's display as the
source's raised at every letter but one, the identity permutation
forced through the flip's transport.
-/

namespace pieri
open ground places

/-- The one-box shape at a stated fundamental count: one column of
length one. -/
def oneBox (d : Nat) : Shape := unitAt d 0

/-- The row's targets, the one-box additions: a new column of length
one, and each occupied length below the fundamental count grown by
one, the occupancy at its key moved to the successor key
(`units.moveDn` on the column multiset). -/
def row (s : Shape) : List Shape :=
  (match s with
   | [] => []
   | a :: t => [(a + 1) :: t])
  ++ (List.range (s.length - 1)).flatMap (fun j =>
      if 0 < ground.getAt 0 s j then [units.moveDn j s] else [])

/-- `lem:pieri`'s row read at the definitional count: the fusion
count at the one-box shape is the row's occupancy at the target,
one exactly at the one-box additions. -/
def read (s c : Shape) : Prop :=
  blockcount.fusionCount s (oneBox s.length) c = ground.countOf c (row s)

instance (s c : Shape) : Decidable (read s c) :=
  inferInstanceAs (Decidable (_ = _))


/-! The general theorem's tier (`readAll`): `cor:steinberg` at the
one-box factor.  The one-box block is the fundamental one — its
span the unit contents, one member per letter — so a tie
`ν_σ + σ(s + u) = c + u` carries a unit content as its gap, that
is `display c` is `display (s)`'s permuted display raised at one
letter.  The raise is rigid: the raised value's successor is vacant
in a strictly descending display, so the raised list is itself
strictly descending with the source's value counts, `descUnique`
identifies it with `display c`, and the positional read off the
distinct values forces the identity permutation.  The one surviving
contributor is even, the odd sum vacant, and the row bridge reads
the indicator back as the row's occupancy at the target. -/

/-- The one-box shape's width is the stated fundamental count: its
column multiset is the unit content at the first letter. -/
theorem length_oneBox (d : Nat) : (oneBox d).length = d :=
  length_unitAt d 0

/-- The one-box block's content occupancies: its span's contents
are the unit contents, one per letter. -/
private theorem occ_oneBox (d : Nat) (hd : 0 < d) (m : List Nat) :
    blockcount.occupancyAt (blockcount.blockSpan (oneBox d)) m
      = ground.countOf m ((List.range d).map (unitAt d)) := by
  rw [blockcount.occupancyAt_eq_occ m (blockcount.blockSpan (oneBox d)),
    blockcount.occ_eq_countOf m (blockcount.blockSpan (oneBox d)),
    show blockcount.blockSpan (oneBox d)
        = (List.range d).map (fun i =>
            ⟨unitAt d i, [BPair.ofNat 1]⟩)
      from blockcount.blockSpan_fund d hd,
    ground.map_map _ blockcount.HVec.content (List.range d)]

private theorem countOf_unitList (d i : Nat) (hi : i < d) :
    ground.countOf (unitAt d i) ((List.range d).map (unitAt d)) = 1 := by
  rw [ground.countOf_fold (unitAt d i) ((List.range d).map (unitAt d)),
    ground.famFold_map Nat.add 0
      (fun z => if unitAt d i = z then 1 else 0) (unitAt d) (List.range d),
    ground.famFold_congr_members Nat.add 0
      (fun j => if unitAt d i = unitAt d j then 1 else 0)
      (fun j => if i = j then 1 else 0) (List.range d)
      (fun j _ => by
        by_cases hij : i = j
        · rw [if_pos hij, if_pos (congrArg (unitAt d) hij)]
        · rw [if_neg hij, if_neg (unitAt_ne d i j hi hij)]),
    ← ground.countOf_fold i (List.range d), countOf_range i d,
    if_pos hi]

private theorem unit_of_pos (d : Nat) (m : List Nat)
    (h : 0 < ground.countOf m ((List.range d).map (unitAt d))) :
    ∃ i, i < d ∧ unitAt d i = m := by
  obtain ⟨a, ha, hae⟩ := ground.mem_map_of (unitAt d) (List.range d) m
    (ground.mem_of_countOf_pos m _ h)
  refine ⟨a, ?_, hae⟩
  have hc := ground.countOf_pos_of_mem ha
  rw [countOf_range a d] at hc
  by_cases had : a < d
  · exact had
  · rw [if_neg had] at hc
    exact absurd hc (Nat.lt_irrefl 0)

private theorem bumpAt_inj (r : List Nat) (i i' : Nat)
    (hi : i < r.length) (hne : ¬ i = i') :
    ¬ ground.bumpAt i r = ground.bumpAt i' r := by
  intro he
  have h1 : ground.getAt 0 (ground.bumpAt i r) i
      = ground.getAt 0 (ground.bumpAt i' r) i := by rw [he]
  rw [ground.getAt_bumpAt_self i r hi,
    ground.getAt_bumpAt_ne i' r i hne] at h1
  exact absurd h1 (Nat.ne_of_gt (Nat.lt_succ_self _))

/-- The raise reads the same at the display and at the row list:
the unit display rides along untouched. -/
private theorem display_bump (s c : Shape) (hca : c.length = s.length)
    (i : Nat) :
    display c = ground.bumpAt i (display s)
      ↔ rowList c = ground.bumpAt i (rowList s) := by
  have hds : ground.bumpAt i (display s)
      = List.zipWith (fun a b => a + b) (ground.bumpAt i (rowList s))
        (unitDisp s.length) := by
    rw [weylchar.display_zip s,
      (ground.bumpAt_zipWith_left i (rowList s)
        (unitDisp s.length)).symm]
  have hdc : display c
      = List.zipWith (fun a b => a + b) (rowList c)
        (unitDisp s.length) := by
    rw [weylchar.display_zip c, hca]
  constructor
  · intro he
    rw [hdc, hds] at he
    refine ground.getAt_ext 0 (rowList c) (ground.bumpAt i (rowList s))
      (by rw [length_rowList, ground.length_bumpAt, length_rowList, hca])
      (fun k hk => ?_)
    have hkc : k < (rowList c).length := hk
    have hks : k < (ground.bumpAt i (rowList s)).length := by
      rw [ground.length_bumpAt, length_rowList, ← hca, ← length_rowList]
      exact hk
    have hku : k < (unitDisp s.length).length := by
      rw [length_unitDisp, ← hca, ← length_rowList]
      exact hk
    have h1 : ground.getAt 0
          (List.zipWith (fun a b => a + b) (rowList c)
            (unitDisp s.length)) k
        = ground.getAt 0
          (List.zipWith (fun a b => a + b)
            (ground.bumpAt i (rowList s)) (unitDisp s.length)) k := by
      rw [he]
    rw [ground.getAt_zipWith 0 0 0 (fun a b => a + b) (rowList c)
        (unitDisp s.length) k hkc hku,
      ground.getAt_zipWith 0 0 0 (fun a b => a + b)
        (ground.bumpAt i (rowList s)) (unitDisp s.length) k hks hku] at h1
    exact ground.addCancelR _ h1
  · intro he
    rw [hdc, hds, he]

/-- The raise at a successor key reads the source's occupancy
there. -/
private theorem occ_of_bump (s c : Shape) (j : Nat)
    (hj : j + 1 < s.length) (hca : c.length = s.length)
    (hb : rowList c = ground.bumpAt (j + 1) (rowList s)) :
    ground.getAt 0 c j + 1 = ground.getAt 0 s j := by
  have hjs : j < s.length := Nat.lt_of_succ_lt hj
  have hjr : j + 1 < (rowList s).length := by
    rw [length_rowList]; exact hj
  have h1 : ground.getAt 0 (rowList c) j
      = ground.getAt 0 (rowList s) j := by
    rw [hb, ground.getAt_bumpAt_ne (j + 1) (rowList s) j
      (Nat.ne_of_lt (Nat.lt_succ_self j))]
  have h2 : ground.getAt 0 (rowList c) (j + 1)
      = ground.getAt 0 (rowList s) (j + 1) + 1 := by
    rw [hb, ground.getAt_bumpAt_self (j + 1) (rowList s) hjr]
  have h3 := rowList_gap c j (by rw [hca]; exact hjs)
  rw [h1, h2, rowList_gap s j hjs] at h3
  have h4 : ground.getAt 0 c j + 1
        + ground.getAt 0 (rowList s) (j + 1)
      = ground.getAt 0 s j + ground.getAt 0 (rowList s) (j + 1) := by
    rw [Nat.add_right_comm (ground.getAt 0 c j) 1
        (ground.getAt 0 (rowList s) (j + 1)),
      Nat.add_assoc (ground.getAt 0 c j)
        (ground.getAt 0 (rowList s) (j + 1)) 1]
    exact h3.symm
  exact ground.addCancelR _ h4

/-- The row splits at its two arms: the new column's singleton
against the grown columns' guarded family, the target's occupancy
adding over the join. -/
theorem row_split (a : Nat) (t : Shape) (c : Shape) :
    ground.countOf c (row (a :: t))
      = ground.countOf c [(a + 1) :: t]
        + ground.famFold Nat.add 0
            (fun j => ground.countOf c
              (if 0 < ground.getAt 0 (a :: t) j then
                [units.moveDn j (a :: t)] else []))
            (List.range t.length) := by
  show ground.countOf c ([(a + 1) :: t]
      ++ (List.range ((a :: t).length - 1)).flatMap
        (fun j => if 0 < ground.getAt 0 (a :: t) j then
          [units.moveDn j (a :: t)] else [])) = _
  rw [ground.countOf_append, ground.countOf_flatMap]
  rfl

/-- The row's occupancy at a shape of positive width: the head's
raise against the grown columns' guarded fold, `row_split` at the
stated width. -/
theorem countOf_row : ∀ (s : Shape), 0 < s.length → ∀ (c : Shape),
    ground.countOf c (row s)
      = (if c = ground.bumpAt 0 s then 1 else 0)
        + ground.famFold Nat.add 0
            (fun j => ground.countOf c
              (if 0 < ground.getAt 0 s j then
                [units.moveDn j s] else []))
            (List.range (s.length - 1))
  | a :: t, _, c => by
    rw [row_split a t c, ground.countOf_cons]
    show (if c = (a + 1) :: t then 1 else 0) + 0 + _ = _
    rw [Nat.add_zero]
    rfl

/-- Every row member's row list raises the source's at one
letter. -/
private theorem row_bump (s c : Shape) (hd : 0 < s.length)
    (hpos : 0 < ground.countOf c (row s)) :
    ∃ i, i < s.length ∧ rowList c = ground.bumpAt i (rowList s) := by
  match s, hd, hpos with
  | a :: t, _, hpos =>
    rw [row_split a t c] at hpos
    match Nat.eq_zero_or_pos (ground.countOf c [(a + 1) :: t]) with
    | .inr hh =>
      exact ⟨0, Nat.succ_pos t.length, by
        rw [ground.countOf_single hh]
        exact units.rowList_grow a t⟩
    | .inl hz =>
      rw [hz, Nat.zero_add] at hpos
      obtain ⟨j, hj, hfj⟩ := ground.famFold_pos_witness _
        (List.range t.length) hpos
      have hjt : j < t.length := by
        rw [countOf_range j t.length] at hj
        by_cases hc : j < t.length
        · exact hc
        · rw [if_neg hc] at hj
          exact absurd hj (Nat.lt_irrefl 0)
      by_cases hg : 0 < ground.getAt 0 (a :: t) j
      · rw [if_pos hg] at hfj
        refine ⟨j + 1, Nat.succ_lt_succ hjt, ?_⟩
        rw [ground.countOf_single hfj]
        exact units.rowList_moveDn j (a :: t) (Nat.succ_lt_succ hjt) hg
      · rw [if_neg hg] at hfj
        exact absurd hfj (Nat.lt_irrefl 0)

/-- The raise at a letter names exactly one row member. -/
private theorem bump_row (s c : Shape) (hd : 0 < s.length)
    (hca : c.length = s.length) (i : Nat) (hi : i < s.length)
    (hb : rowList c = ground.bumpAt i (rowList s)) :
    ground.countOf c (row s) = 1 := by
  match s, hd, hca, i, hi, hb with
  | a :: t, _, hca, i, hi, hb =>
    have hrl : (rowList (a :: t)).length = t.length + 1 :=
      length_rowList (a :: t)
    have hlt : ∀ j, 0 < ground.countOf j (List.range t.length) →
        j < t.length := fun _ hj => ground.ltOfMem hj
    have hmv : ∀ j, j < t.length → 0 < ground.getAt 0 (a :: t) j →
        rowList (units.moveDn j (a :: t))
          = ground.bumpAt (j + 1) (rowList (a :: t)) :=
      fun j hj hg => units.rowList_moveDn j (a :: t) (Nat.succ_lt_succ hj) hg
    rw [row_split a t c]
    match i, hi, hb with
    | 0, _, hb =>
      have hce : c = (a + 1) :: t :=
        rowList_inj c ((a + 1) :: t) (by rw [hb, units.rowList_grow a t])
      have hstep : ∀ j, 0 < ground.countOf j (List.range t.length) →
          ground.countOf c
            (if 0 < ground.getAt 0 (a :: t) j then
              [units.moveDn j (a :: t)] else []) = 0 := by
        intro j hj
        by_cases hg : 0 < ground.getAt 0 (a :: t) j
        · have hne : ¬ c = units.moveDn j (a :: t) := by
            intro hcm
            refine bumpAt_inj (rowList (a :: t)) 0 (j + 1)
              (by rw [hrl]; exact Nat.succ_pos _)
              (fun h0 => Nat.noConfusion h0) ?_
            rw [← hb, hcm]
            exact hmv j (hlt j hj) hg
          rw [if_pos hg]
          exact ground.countOf_head_ne hne ([] : List Shape)
        · rw [if_neg hg]
          rfl
      have hhz : ground.countOf c [(a + 1) :: t] = 1 := by
        rw [hce, ground.countOf_head]
        rfl
      rw [hhz,
        ground.famFold_congr_members Nat.add 0 _ (fun _ => (0 : Nat))
          (List.range t.length) hstep,
        ground.famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl)
          (List.range t.length), Nat.add_zero]
    | j0 + 1, hi, hb =>
      have hj0 : j0 < t.length := Nat.lt_of_succ_lt_succ hi
      have hocc : 0 < ground.getAt 0 (a :: t) j0 := by
        rw [← occ_of_bump (a :: t) c j0 hi hca hb]
        exact Nat.succ_pos _
      have hcm : c = units.moveDn j0 (a :: t) :=
        rowList_inj c (units.moveDn j0 (a :: t))
          (by rw [hb, hmv j0 hj0 hocc])
      have hnh : ¬ c = (a + 1) :: t := by
        intro hce
        refine bumpAt_inj (rowList (a :: t)) 0 (j0 + 1)
          (by rw [hrl]; exact Nat.succ_pos _)
          (fun h0 => Nat.noConfusion h0) ?_
        rw [← units.rowList_grow a t, ← hce]
        exact hb
      have hstep : ∀ j, 0 < ground.countOf j (List.range t.length) →
          ground.countOf c
            (if 0 < ground.getAt 0 (a :: t) j then
              [units.moveDn j (a :: t)] else [])
            = if j0 = j then 1 else 0 := by
        intro j hj
        by_cases hj0j : j0 = j
        · rw [← hj0j, if_pos hocc, if_pos rfl, hcm, ground.countOf_head]
          rfl
        · by_cases hg : 0 < ground.getAt 0 (a :: t) j
          · have hne : ¬ c = units.moveDn j (a :: t) := by
              intro hcm2
              refine bumpAt_inj (rowList (a :: t)) (j0 + 1) (j + 1)
                (by rw [hrl]; exact Nat.succ_lt_succ hj0)
                (fun he => hj0j (Nat.succ.inj he)) ?_
              rw [← hb, hcm2]
              exact hmv j (hlt j hj) hg
            rw [if_neg hj0j, if_pos hg]
            exact ground.countOf_head_ne hne ([] : List Shape)
          · rw [if_neg hj0j, if_neg hg]
            rfl
      have hhz : ground.countOf c [(a + 1) :: t] = 0 :=
        ground.countOf_head_ne hnh ([] : List Shape)
      rw [hhz, Nat.zero_add,
        ground.famFold_congr_members Nat.add 0 _
          (fun j => if j0 = j then 1 else 0) (List.range t.length) hstep,
        ← ground.countOf_fold j0 (List.range t.length),
        countOf_range j0 t.length, if_pos hj0]

/-- The gap's absence at every letter reads the vacant row
occupancy. -/
private theorem row_zero (s c : Shape) (hd : 0 < s.length)
    (hca : c.length = s.length)
    (hno : ∀ i, i < s.length →
      ¬ ground.tieGap (display c) (display s) = some (unitAt s.length i)) :
    ground.countOf c (row s) = 0 := by
  match hc : ground.countOf c (row s) with
  | 0 => rfl
  | n + 1 =>
    obtain ⟨i, hi, hbi⟩ := row_bump s c hd (by rw [hc]; exact Nat.succ_pos n)
    exact absurd
      ((tieGap_unit s.length (display c) (display s)
          (by rw [length_display, hca]) (length_display s) i hi).mpr
        ((display_bump s c hca i).mpr hbi))
      (hno i hi)

/-- The gap at a letter reads the row's unit occupancy. -/
private theorem row_one (s c : Shape) (hd : 0 < s.length)
    (hca : c.length = s.length) (i : Nat) (hi : i < s.length)
    (hg : ground.tieGap (display c) (display s) = some (unitAt s.length i)) :
    ground.countOf c (row s) = 1 :=
  bump_row s c hd hca i hi
    ((display_bump s c hca i).mp
      ((tieGap_unit s.length (display c) (display s)
        (by rw [length_display, hca]) (length_display s) i hi).mp hg))

/-- The one-box factor's tie value at the source's own display: the
gap's occupancy is the row's occupancy at the target. -/
private theorem gapValue_row (s c : Shape) (hd : 0 < s.length)
    (hca : c.length = s.length) :
    weylchar.multAtGap
        (blockcount.occupancyAt (blockcount.blockSpan (oneBox s.length)))
        (display c) (display s)
      = ground.countOf c (row s) := by
  show (match ground.tieGap (display c) (display s) with
    | some nu => blockcount.occupancyAt
        (blockcount.blockSpan (oneBox s.length)) nu
    | none => 0) = ground.countOf c (row s)
  cases hg : ground.tieGap (display c) (display s) with
  | none =>
    have hno : ∀ i, i < s.length →
        ¬ ground.tieGap (display c) (display s)
          = some (unitAt s.length i) := by
      intro i _ he
      rw [hg] at he
      exact nomatch he
    show (0 : Nat) = ground.countOf c (row s)
    rw [row_zero s c hd hca hno]
  | some m =>
    show blockcount.occupancyAt
      (blockcount.blockSpan (oneBox s.length)) m = ground.countOf c (row s)
    rw [occ_oneBox s.length hd m]
    by_cases hu : 0 < ground.countOf m
        ((List.range s.length).map (unitAt s.length))
    · obtain ⟨i, hi, him⟩ := unit_of_pos s.length m hu
      rw [← him, countOf_unitList s.length i hi,
        row_one s c hd hca i hi (hg.trans (congrArg some him.symm))]
    · have hz : ground.countOf m
          ((List.range s.length).map (unitAt s.length)) = 0 := by
        match hcm : ground.countOf m
            ((List.range s.length).map (unitAt s.length)) with
        | 0 => rfl
        | n + 1 => exact absurd (by rw [hcm]; exact Nat.succ_pos n) hu
      have hno : ∀ i, i < s.length →
          ¬ ground.tieGap (display c) (display s)
            = some (unitAt s.length i) := by
        intro i hi he
        have hme : m = unitAt s.length i :=
          Option.some.inj (hg.symm.trans he)
        refine hu ?_
        rw [hme, countOf_unitList s.length i hi]
        exact Nat.succ_pos 0
      rw [hz, row_zero s c hd hca hno]

/-- `cor:steinberg`'s two graded sums at the one-box factor: the
identity permutation the one contributor, the even sum the row's
occupancy at the target and the odd sum vacant. -/
private theorem gradedSums_oneBox (s c : Shape)
    (hd : 0 < s.length) (hca : c.length = s.length) :
    steinberg.gradedSums (oneBox s.length) s c
      = (ground.countOf c (row s), 0) := by
  have hoff : ∀ p ∈ places.perms s.length,
      ¬ p = List.range s.length → ∀ acc : Nat × Nat,
      (match ground.tieGap (display c) (places.expo (display s) p) with
        | none => acc
        | some m =>
          if parity p then
            (acc.1, acc.2 + blockcount.occupancyAt
              (blockcount.blockSpan (oneBox s.length)) m)
          else
            (acc.1 + blockcount.occupancyAt
              (blockcount.blockSpan (oneBox s.length)) m, acc.2))
        = acc := by
    intro p hpm hne acc
    have hp : 0 < ground.countOf p (places.perms s.length) :=
      ground.countOf_pos_of_mem hpm
    cases hg : ground.tieGap (display c) (places.expo (display s) p) with
    | none => rfl
    | some m =>
      have hzm : blockcount.occupancyAt
          (blockcount.blockSpan (oneBox s.length)) m = 0 := by
        rw [occ_oneBox s.length hd m]
        match hcm : ground.countOf m
            ((List.range s.length).map (unitAt s.length)) with
        | 0 => rfl
        | n + 1 =>
          obtain ⟨i, hi, him⟩ := unit_of_pos s.length m
            (by rw [hcm]; exact Nat.succ_pos n)
          have hpl : (places.expo (display s) p).length = s.length := by
            show (p.map (ground.getAt 0 (display s))).length = s.length
            rw [ground.length_map]
            exact (perm_member_reads hp).1
          have hbu : display c
              = ground.bumpAt i (places.expo (display s) p) :=
            (tieGap_unit s.length (display c)
              (places.expo (display s) p)
              (by rw [length_display, hca]) hpl i hi).mp
              (hg.trans (congrArg some him.symm))
          exact absurd
            (tie_rigid s.length (display s) (display c)
              (length_display s) (by rw [length_display, hca])
              (fun k hk => display_desc s k hk)
              (fun k hk => display_desc c k (by rw [hca]; exact hk))
              p hp i hi hbu).1
            hne
      show (if parity p then
          (acc.1, acc.2 + blockcount.occupancyAt
            (blockcount.blockSpan (oneBox s.length)) m)
        else
          (acc.1 + blockcount.occupancyAt
            (blockcount.blockSpan (oneBox s.length)) m, acc.2)) = acc
      rw [hzm]
      cases parity p with
      | true =>
        show ((acc.1, acc.2 + 0) : Nat × Nat) = acc
        rw [Nat.add_zero]
      | false =>
        show ((acc.1 + 0, acc.2) : Nat × Nat) = acc
        rw [Nat.add_zero]
  have hat : ∀ acc : Nat × Nat,
      (match ground.tieGap (display c)
          (places.expo (display s) (List.range s.length)) with
        | none => acc
        | some m =>
          if parity (List.range s.length) then
            (acc.1, acc.2 + blockcount.occupancyAt
              (blockcount.blockSpan (oneBox s.length)) m)
          else
            (acc.1 + blockcount.occupancyAt
              (blockcount.blockSpan (oneBox s.length)) m, acc.2))
        = (acc.1 + ground.countOf c (row s), acc.2) := by
    intro acc
    rw [show places.expo (display s) (List.range s.length) = display s
        from range_map_getAt 0 s.length (display s) (length_display s),
      parity_range s.length]
    have hv := gapValue_row s c hd hca
    cases hg : ground.tieGap (display c) (display s) with
    | none =>
      have hz : ground.countOf c (row s) = 0 := by
        rw [← hv]
        show (match ground.tieGap (display c) (display s) with
          | some nu => blockcount.occupancyAt
              (blockcount.blockSpan (oneBox s.length)) nu
          | none => 0) = 0
        rw [hg]
      show acc = (acc.1 + ground.countOf c (row s), acc.2)
      rw [hz, Nat.add_zero]
    | some m =>
      have hvm : blockcount.occupancyAt
          (blockcount.blockSpan (oneBox s.length)) m
          = ground.countOf c (row s) := by
        rw [← hv]
        show blockcount.occupancyAt
            (blockcount.blockSpan (oneBox s.length)) m
          = match ground.tieGap (display c) (display s) with
            | some nu => blockcount.occupancyAt
                (blockcount.blockSpan (oneBox s.length)) nu
            | none => 0
        rw [hg]
      show ((acc.1 + blockcount.occupancyAt
        (blockcount.blockSpan (oneBox s.length)) m, acc.2) : Nat × Nat)
        = (acc.1 + ground.countOf c (row s), acc.2)
      rw [hvm]
  show steinberg.sumsWith
      (blockcount.occupancyAt (blockcount.blockSpan (oneBox s.length)))
      (oneBox s.length).length s c = (ground.countOf c (row s), 0)
  rw [length_oneBox s.length]
  show (places.perms s.length).foldl
      (fun acc p =>
        match ground.tieGap (display c) (places.expo (display s) p) with
        | none => acc
        | some m =>
          if parity p then
            (acc.1, acc.2 + blockcount.occupancyAt
              (blockcount.blockSpan (oneBox s.length)) m)
          else
            (acc.1 + blockcount.occupancyAt
              (blockcount.blockSpan (oneBox s.length)) m, acc.2))
      (0, 0) = (ground.countOf c (row s), 0)
  rw [ground.foldl_pick _ (List.range s.length)
      (fun acc => (acc.1 + ground.countOf c (row s), acc.2)) hat
      (places.perms s.length) hoff
      (places.countRangePerms s.length) (0, 0)]
  show ((0 + ground.countOf c (row s), 0) : Nat × Nat)
    = (ground.countOf c (row s), 0)
  rw [Nat.zero_add]

/-- `lem:pieri`'s row read at any target of the positive width: the
one-box fusion count is the row's occupancy at the target, one
exactly at the one-box additions — `cor:steinberg` at the one-box
factor, whose block is the fundamental one. -/
theorem readAll (s c : Shape) (hd : 0 < s.length)
    (hca : c.length = s.length) : read s c := by
  have h := steinberg.readAll (oneBox s.length) s c
    (by rw [length_oneBox]) (by rw [length_oneBox]; exact hca)
  have h2 : blockcount.fusionCount (oneBox s.length) s c
      + (steinberg.gradedSums (oneBox s.length) s c).2
    = (steinberg.gradedSums (oneBox s.length) s c).1 := h
  rw [gradedSums_oneBox s c hd hca] at h2
  have h3 : blockcount.fusionCount (oneBox s.length) s c + 0
      = ground.countOf c (row s) := h2
  rw [Nat.add_zero] at h3
  show blockcount.fusionCount s (oneBox s.length) c
    = ground.countOf c (row s)
  rw [blockcount.fusionCount_comm s (oneBox s.length) c
    (length_oneBox s.length)]
  exact h3

/-! The complement-factor tier: `lem:pieri`'s clause at the
complement's one-column shape.  The factor's block contents are the
full column's withdrawn letters at one count each — a count read
transported across the letters' exchanges through the shared sorted
representative to the top line's count (`strings.countCongr`;
`lowerspan.topRead_def`), a content holding a letter twice vacant at
the dominance cap (`lowerspan.supportRead_def` at the sorted
representative) — and the tie analysis reads the target's display as
the source's raised at every letter but one, the identity
permutation forced. -/

/-- The complement's one-column shape at a stated fundamental
count: one column of length `d - 1`, `lem:dualread`(ii)'s
complement at the one-box shape. -/
def complBox (d : Nat) : Shape := unitAt d (d - 2)

/-- The complement's one-column shape keeps the stated width. -/
theorem length_complBox (d : Nat) : (complBox d).length = d :=
  length_unitAt d (d - 2)

/-- The complement row's targets: the one-box withdrawals of the
full-column raise, every row raised by one except one. -/
def rowD (s : Shape) : List Shape :=
  units.removals (ground.bumpAt (s.length - 1) s)

/-- `lem:pieri`'s complement row read at the definitional count:
the fusion count at the complement's one-column shape is the row's
occupancy at the target, one exactly at the full column's withdrawn
letters. -/
def readD (s c : Shape) : Prop :=
  blockcount.fusionCount s (complBox s.length) c
    = ground.countOf c (rowD s)

instance (s c : Shape) : Decidable (readD s c) :=
  inferInstanceAs (Decidable (_ = _))

/-- The complement factor's content at a withdrawn letter: one at
every place off the letter. -/
def coUnit (d i : Nat) : List Nat :=
  (List.range d).map (fun k => if k = i then 0 else 1)

/-- The complement factor's content carries the stated width. -/
theorem length_coUnit (d i : Nat) : (coUnit d i).length = d :=
  ground.length_mapRange _ d

/-- The complement factor's content at a place inside the width:
the fold's unit at the withdrawn letter, one at every further
place. -/
theorem getAt_coUnit (d i k : Nat) (hk : k < d) :
    ground.getAt 0 (coUnit d i) k = if k = i then 0 else 1 := by
  show ground.getAt 0 ((List.range d).map (fun k => if k = i then 0 else 1)) k = _
  rw [ground.getAt_map 0 0 (fun k => if k = i then 0 else 1)
      (List.range d) k (by rw [ground.length_range]; exact hk),
    ground.getAt_range d k hk]

private theorem coUnit_ne (d i j : Nat) (hi : i < d) (hij : ¬ i = j) :
    ¬ coUnit d i = coUnit d j := by
  intro he
  have h1 : ground.getAt 0 (coUnit d i) i
      = ground.getAt 0 (coUnit d j) i := by rw [he]
  rw [getAt_coUnit d i i hi, getAt_coUnit d j i hi, if_pos rfl,
    if_neg hij] at h1
  exact Nat.noConfusion h1

theorem countOf_coUnitList (d i : Nat) (hi : i < d) :
    ground.countOf (coUnit d i) ((List.range d).map (coUnit d)) = 1 := by
  rw [ground.countOf_fold (coUnit d i) ((List.range d).map (coUnit d)),
    ground.famFold_map Nat.add 0
      (fun z => if coUnit d i = z then 1 else 0) (coUnit d) (List.range d),
    ground.famFold_congr_members Nat.add 0
      (fun j => if coUnit d i = coUnit d j then 1 else 0)
      (fun j => if i = j then 1 else 0) (List.range d)
      (fun j _ => by
        by_cases hij : i = j
        · rw [if_pos hij, if_pos (congrArg (coUnit d) hij)]
        · rw [if_neg hij, if_neg (coUnit_ne d i j hi hij)]),
    ← ground.countOf_fold i (List.range d), countOf_range i d,
    if_pos hi]

/-- An occupied member of the withdrawn-letter family names its
letter. -/
theorem coUnit_of_pos (d : Nat) (m : List Nat)
    (h : 0 < ground.countOf m ((List.range d).map (coUnit d))) :
    ∃ i, i < d ∧ coUnit d i = m := by
  obtain ⟨a, ha, hae⟩ := ground.mem_map_of (coUnit d) (List.range d) m
    (ground.mem_of_countOf_pos m _ h)
  refine ⟨a, ?_, hae⟩
  have hc := ground.countOf_pos_of_mem ha
  rw [countOf_range a d] at hc
  by_cases had : a < d
  · exact had
  · rw [if_neg had] at hc
    exact absurd hc (Nat.lt_irrefl 0)

private theorem swapPair_self (j : Nat) (m : List Nat) :
    swapPair j j m = m := by
  show (if j < j then _ else if j < j then _ else m) = m
  rw [if_neg (Nat.lt_irrefl j), if_neg (Nat.lt_irrefl j)]

private theorem coUnit_swap (d i j : Nat) (hi : i < d) (hj : j < d) :
    swapPair i j (coUnit d j) = coUnit d i := by
  by_cases hij : i = j
  · rw [hij, swapPair_self]
  · refine ground.getAt_ext 0 _ _
      (by rw [length_swapPair, length_coUnit, length_coUnit]) ?_
    intro k hk
    rw [length_swapPair, length_coUnit] at hk
    by_cases hki : k = i
    · rw [hki, getAt_swapPair_fst (coUnit d j) hij
          (by rw [length_coUnit]; exact hi)
          (by rw [length_coUnit]; exact hj),
        getAt_coUnit d j j hj, getAt_coUnit d i i hi, if_pos rfl,
        if_pos rfl]
    · by_cases hkj : k = j
      · rw [hkj, getAt_swapPair_snd (coUnit d j) hij
            (by rw [length_coUnit]; exact hi)
            (by rw [length_coUnit]; exact hj),
          getAt_coUnit d j i hi, getAt_coUnit d i j hj,
          if_neg (fun h : i = j => hij h),
          if_neg (fun h : j = i => hij h.symm)]
      · rw [getAt_swapPair_ne (coUnit d j)
            (by rw [length_coUnit]; exact hi)
            (by rw [length_coUnit]; exact hj) hki hkj,
          getAt_coUnit d j k hk, getAt_coUnit d i k hk,
          if_neg hkj, if_neg hki]

private theorem coUnit_succ (d i : Nat) :
    coUnit (d + 1) (i + 1) = 1 :: coUnit d i := by
  show (List.range (d + 1)).map (fun k => if k = i + 1 then 0 else 1)
    = 1 :: coUnit d i
  rw [ground.range_cons d]
  show (if (0 : Nat) = i + 1 then 0 else 1)
      :: ((List.range d).map (fun j => j + 1)).map
        (fun k => if k = i + 1 then 0 else 1)
    = 1 :: coUnit d i
  rw [if_neg (fun h : (0 : Nat) = i + 1 => Nat.noConfusion h),
    ground.map_map (fun j => j + 1)
      (fun k => if k = i + 1 then 0 else 1) (List.range d),
    ground.map_congr_members
      (fun j => if j + 1 = i + 1 then 0 else 1)
      (fun j => if j = i then 0 else 1) (List.range d)
      (fun j _ => by
        by_cases hji : j = i
        · rw [if_pos hji, if_pos (congrArg Nat.succ hji)]
        · rw [if_neg (fun h : j + 1 = i + 1 => hji (Nat.succ.inj h)),
            if_neg hji])]
  rfl

private theorem rowList_complBoxK : ∀ k : Nat,
    rowList (unitAt (k + 2) k) = coUnit (k + 2) (k + 1)
  | 0 => by decide +kernel
  | k + 1 => by
    show rowList (unitAt ((k + 2) + 1) (k + 1))
      = coUnit ((k + 2) + 1) ((k + 1) + 1)
    rw [ground.unitAt_succ (k + 2) k, coUnit_succ (k + 2) (k + 1)]
    show (0 + sumNat (unitAt (k + 2) k)) :: rowList (unitAt (k + 2) k)
      = 1 :: coUnit (k + 2) (k + 1)
    rw [Nat.zero_add,
      ground.sumNat_unitAt (k + 2) k
        (Nat.lt_of_succ_lt (Nat.lt_succ_self (k + 1))),
      rowList_complBoxK k]

private theorem countOf_coUnit01 : ∀ k : Nat,
    ground.countOf 0 (coUnit (k + 2) (k + 1)) = 1
      ∧ ground.countOf 1 (coUnit (k + 2) (k + 1)) + 1 = k + 2
  | 0 => by decide +kernel
  | k + 1 => by
    show ground.countOf 0 (coUnit ((k + 2) + 1) ((k + 1) + 1)) = 1
      ∧ ground.countOf 1 (coUnit ((k + 2) + 1) ((k + 1) + 1)) + 1
        = (k + 2) + 1
    rw [coUnit_succ (k + 2) (k + 1)]
    refine ⟨?_, ?_⟩
    · rw [ground.countOf_head_ne
        (fun h : (0 : Nat) = 1 => Nat.noConfusion h)
        (coUnit (k + 2) (k + 1))]
      exact (countOf_coUnit01 k).1
    · rw [ground.countOf_head]
      exact congrArg Nat.succ (countOf_coUnit01 k).2

/-- The ascending chain at a reversal-free family. -/
private theorem sum_count1 : ∀ l : List Nat,
    (∀ j, j < l.length → ground.getAt 0 l j ≤ 1) →
    ground.sumNat l = ground.countOf 1 l
  | [], _ => rfl
  | a :: t, hb => by
    have hht : ∀ j, j < t.length → ground.getAt 0 t j ≤ 1 :=
      fun j hj => hb (j + 1) (Nat.succ_lt_succ hj)
    have hha : a ≤ 1 := hb 0 (Nat.succ_pos t.length)
    match a, hha with
    | 0, _ =>
      rw [ground.countOf_head_ne
        (fun h : (1 : Nat) = 0 => Nat.noConfusion h) t]
      show (0 : Nat) + ground.sumNat t = ground.countOf 1 t
      rw [Nat.zero_add, sum_count1 t hht]
    | 1, _ =>
      rw [ground.countOf_head]
      show (1 : Nat) + ground.sumNat t = ground.countOf 1 t + 1
      rw [sum_count1 t hht, Nat.add_comm]
    | n + 2, hha =>
      exact absurd (Nat.lt_of_succ_lt_succ hha) (Nat.not_lt_zero n)

private theorem count01 : ∀ l : List Nat,
    (∀ j, j < l.length → ground.getAt 0 l j ≤ 1) →
    ground.countOf 0 l + ground.countOf 1 l = l.length
  | [], _ => rfl
  | a :: t, hb => by
    have hht : ∀ j, j < t.length → ground.getAt 0 t j ≤ 1 :=
      fun j hj => hb (j + 1) (Nat.succ_lt_succ hj)
    have hha : a ≤ 1 := hb 0 (Nat.succ_pos t.length)
    match a, hha with
    | 0, _ =>
      rw [ground.countOf_head,
        ground.countOf_head_ne
          (fun h : (1 : Nat) = 0 => Nat.noConfusion h) t,
        Nat.add_right_comm, count01 t hht]
      rfl
    | 1, _ =>
      rw [ground.countOf_head,
        ground.countOf_head_ne
          (fun h : (0 : Nat) = 1 => Nat.noConfusion h) t,
        ← Nat.add_assoc, count01 t hht]
      rfl
    | n + 2, hha =>
      exact absurd (Nat.lt_of_succ_lt_succ hha) (Nat.not_lt_zero n)

/-- The complement block's content occupancies: the span's contents
are the full column's withdrawn letters, one per letter — the count
transported across the letters' exchanges to the top line's count,
and a content off the withdrawn letters vacant at the sorted
representative's dominance cap. -/
theorem occ_complBox (d : Nat) (hd : 2 ≤ d) (m : List Nat) :
    blockcount.occupancyAt (blockcount.blockSpan (complBox d)) m
      = ground.countOf m ((List.range d).map (coUnit d)) := by
  match d, hd with
  | k + 2, _ =>
  rw [← blockcount.span_countOf (complBox (k + 2)) m]
  by_cases hpos : 0 < ground.countOf m
      ((List.range (k + 2)).map (coUnit (k + 2)))
  · obtain ⟨i, hi, him⟩ := coUnit_of_pos (k + 2) m hpos
    rw [← him, countOf_coUnitList (k + 2) i hi,
      strings.countCongr (complBox (k + 2)) (coUnit (k + 2) i)
        (rowList (complBox (k + 2)))
        (by rw [length_coUnit, length_complBox])
        (by rw [length_rowList, length_complBox])
        (fun v => by
          rw [show rowList (complBox (k + 2)) = coUnit (k + 2) (k + 1)
              from rowList_complBoxK k,
            ← coUnit_swap (k + 2) i (k + 1) hi (Nat.lt_succ_self (k + 1)),
            countOf_swapPair v i (k + 1) (coUnit (k + 2) (k + 1))])]
    exact lowerspan.topRead_def (complBox (k + 2))
  · have hz : ground.countOf m
        ((List.range (k + 2)).map (coUnit (k + 2))) = 0 := by
      match hcz : ground.countOf m
          ((List.range (k + 2)).map (coUnit (k + 2))) with
      | 0 => rfl
      | n + 1 =>
        exact absurd (by rw [hcz]; exact Nat.succ_pos n) hpos
    rw [hz]
    match hocc : ground.countOf m
        ((blockcount.blockSpan (complBox (k + 2))).map
          blockcount.HVec.content) with
    | 0 => rfl
    | n + 1 =>
    exfalso
    have hcm : 0 < ground.countOf m
        ((blockcount.blockSpan (complBox (k + 2))).map
          blockcount.HVec.content) := by
      rw [hocc]
      exact Nat.succ_pos n
    obtain ⟨v, hv, hvm⟩ := ground.mem_map_of blockcount.HVec.content
      (blockcount.blockSpan (complBox (k + 2))) m
      (ground.mem_of_countOf_pos m _ hcm)
    have hlm : m.length = k + 2 := by
      rw [← hvm]
      have hw := blockcount.blockSpan_width (complBox (k + 2)) v hv
      rw [length_complBox] at hw
      exact hw
    -- the sorted representative and its reverse
    have hsort : firstRev
        (applyWord (sortWord (inversions m) m) m) = none :=
      (sortWord_reads (inversions m) m (Nat.le_refl _)).1
    have hlms : (applyWord (sortWord (inversions m) m) m).length
        = k + 2 := by
      rw [length_applyWord, hlm]
    have hcntm : ∀ w, ground.countOf w
          (applyWord (sortWord (inversions m) m) m)
        = ground.countOf w m :=
      fun w => countOf_applyWord w (sortWord (inversions m) m) m
    have hcms : ground.countOf
          (applyWord (sortWord (inversions m) m) m)
          ((blockcount.blockSpan (complBox (k + 2))).map
            blockcount.HVec.content)
        = ground.countOf m
          ((blockcount.blockSpan (complBox (k + 2))).map
            blockcount.HVec.content) :=
      strings.countCongr (complBox (k + 2)) _ m
        (by rw [hlms, length_complBox])
        (by rw [hlm, length_complBox]) hcntm
    have hcnt_r : ∀ w, ground.countOf w
          (applyWord (sortWord (inversions m) m) m).reverse
        = ground.countOf w m :=
      fun w => (ground.countOf_reverse w _).trans (hcntm w)
    have hlmr : (applyWord (sortWord (inversions m) m) m).reverse.length
        = k + 2 := by
      rw [ground.length_reverse, hlms]
    have hcmr : ground.countOf
          (applyWord (sortWord (inversions m) m) m).reverse
          ((blockcount.blockSpan (complBox (k + 2))).map
            blockcount.HVec.content)
        = ground.countOf m
          ((blockcount.blockSpan (complBox (k + 2))).map
            blockcount.HVec.content) :=
      strings.countCongr (complBox (k + 2)) _ m
        (by rw [hlmr, length_complBox])
        (by rw [hlm, length_complBox]) hcnt_r
    have hmemr : (applyWord (sortWord (inversions m) m) m).reverse
        ∈ ((blockcount.blockSpan (complBox (k + 2))).map
          blockcount.HVec.content) :=
      ground.mem_of_countOf_pos _ _ (by rw [hcmr, hocc]; exact Nat.succ_pos n)
    have hdom : weylchar.domBy
        (applyWord (sortWord (inversions m) m) m).reverse
        (rowList (complBox (k + 2))) :=
      lowerspan.supportRead_def (complBox (k + 2)) _ hmemr
    rw [show rowList (complBox (k + 2)) = coUnit (k + 2) (k + 1)
        from rowList_complBoxK k] at hdom
    -- the last entry's cap, and every entry of m with it
    have hpre1 := weylchar.domGo_prefix 0 _ _ hdom 1
    rw [ground.prefixAt_one, ground.prefixAt_one,
      getAt_coUnit (k + 2) (k + 1) 0 (Nat.succ_pos (k + 1)),
      if_neg (fun h : (0 : Nat) = k + 1 => Nat.noConfusion h),
      Nat.zero_add] at hpre1
    have hlast : ground.getAt 0
        (applyWord (sortWord (inversions m) m) m) (k + 1) ≤ 1 := by
      rw [← ground.getAt_reverse (0 : Nat)
        (applyWord (sortWord (inversions m) m) m) 0 (k + 1)
        (by rw [hlms, Nat.zero_add])]
      exact hpre1
    have hmax : ∀ w, 0 < ground.countOf w m → w ≤ 1 := by
      intro w hw
      have hw2 : 0 < ground.countOf w
          (applyWord (sortWord (inversions m) m) m) := by
        rw [hcntm w]
        exact hw
      obtain ⟨q, hq, hgq⟩ := ground.getAt_of_mem 0
        (ground.mem_of_countOf_pos w _ hw2)
      have hql : q ≤ k + 1 := by
        rw [hlms] at hq
        exact Nat.le_of_lt_succ hq
      rw [← hgq]
      exact Nat.le_trans
        (places.le_of_firstRev_none
          (applyWord (sortWord (inversions m) m) m) hsort
          (k + 1) q hql (by rw [hlms]; exact Nat.lt_succ_self (k + 1)))
        hlast
    have hmaxAt : ∀ j, j < m.length → ground.getAt 0 m j ≤ 1 :=
      fun j hj => hmax (ground.getAt 0 m j)
        (ground.countOf_getAt_pos 0 m j hj)
    -- the totals across the dominance walk
    have hsum := weylchar.domGo_sum 0 _ _ hdom
    have hps : ∀ l : List Nat,
        ground.prefixAt l.length l = ground.sumNat l :=
      fun l => ground.prefixAt_full l l.length (Nat.le_refl _)
    rw [hps, hps, Nat.zero_add] at hsum
    have hmaxAtR : ∀ j,
        j < (applyWord (sortWord (inversions m) m) m).reverse.length →
        ground.getAt 0
          (applyWord (sortWord (inversions m) m) m).reverse j ≤ 1 :=
      fun j hj => hmax _ (by
        rw [← hcnt_r (ground.getAt 0
          (applyWord (sortWord (inversions m) m) m).reverse j)]
        exact ground.countOf_getAt_pos 0 _ j hj)
    have hmaxCo : ∀ j, j < (coUnit (k + 2) (k + 1)).length →
        ground.getAt 0 (coUnit (k + 2) (k + 1)) j ≤ 1 := by
      intro j hj
      rw [length_coUnit] at hj
      rw [getAt_coUnit (k + 2) (k + 1) j hj]
      by_cases hjk : j = k + 1
      · rw [if_pos hjk]
        exact Nat.zero_le 1
      · rw [if_neg hjk]
        exact Nat.le_refl 1
    rw [sum_count1 _ hmaxAtR, sum_count1 _ hmaxCo, hcnt_r 1] at hsum
    have hc1co : ground.countOf 1 (coUnit (k + 2) (k + 1)) = k + 1 :=
      Nat.succ.inj (countOf_coUnit01 k).2
    rw [hc1co] at hsum
    -- the zero count
    have hcnt01 := count01 m hmaxAt
    rw [hsum, hlm] at hcnt01
    have hc0 : ground.countOf 0 m = 1 := by
      have h1 : ground.countOf 0 m + (k + 1) = 1 + (k + 1) := by
        rw [Nat.add_comm 1 (k + 1)]
        exact hcnt01
      exact ground.addCancelR (k + 1) h1
    -- m is a withdrawn letter's content
    have hposOf : posOf 0 m < m.length :=
      posOf_lt 0 m (by rw [hc0]; exact Nat.succ_pos 0)
    have hg0 : ground.getAt 0 m (posOf 0 m) = 0 :=
      getAt_posOf 0 m (by rw [hc0]; exact Nat.succ_pos 0)
    have hmco : m = coUnit (k + 2) (posOf 0 m) := by
      refine ground.getAt_ext 0 m (coUnit (k + 2) (posOf 0 m))
        (by rw [hlm, length_coUnit]) ?_
      intro j hj
      rw [hlm] at hj
      rw [getAt_coUnit (k + 2) (posOf 0 m) j hj]
      by_cases hji : j = posOf 0 m
      · rw [if_pos hji, hji, hg0]
      · rw [if_neg hji]
        match hgj : ground.getAt 0 m j with
        | 0 =>
          exact absurd
            (by
              have h := ground.countOf_two_pos 0 m j (posOf 0 m)
                (by rw [hlm]; exact hj) hposOf hji
                (by rw [hgj, hg0])
              rw [hgj] at h
              exact h)
            (by rw [hc0]; exact fun h => absurd h (Nat.not_le_of_lt (Nat.lt_succ_self 1)))
        | 1 => rfl
        | w + 2 =>
          exact absurd
            (by rw [← hgj]
                exact hmaxAt j (by rw [hlm]; exact hj))
            (fun h => absurd (Nat.le_of_succ_le_succ h)
              (Nat.not_lt_zero w))
    rw [hmco, countOf_coUnitList (k + 2) (posOf 0 m)
      (by rw [← hlm]; exact hposOf)] at hz
    exact Nat.noConfusion hz

/-- The all-but-one raise: every entry raised by one except the
withdrawn letter's. -/
private def raiseOff (i : Nat) (r : List Nat) : List Nat :=
  ground.dipAt i (r.map (fun x => x + 1))

private theorem length_raiseOff (i : Nat) (r : List Nat) :
    (raiseOff i r).length = r.length := by
  show (ground.dipAt i (r.map (fun x => x + 1))).length = r.length
  rw [ground.length_dipAt, ground.length_map]

private theorem getAt_raiseOff_self (i : Nat) (r : List Nat)
    (hi : i < r.length) :
    ground.getAt 0 (raiseOff i r) i = ground.getAt 0 r i := by
  show ground.getAt 0 (ground.dipAt i (r.map (fun x => x + 1))) i
    = ground.getAt 0 r i
  rw [ground.getAt_dipAt i (r.map (fun x => x + 1)),
    ground.getAt_map 0 0 (fun x => x + 1) r i hi]
  rfl

private theorem getAt_raiseOff_ne (i : Nat) (r : List Nat) (k : Nat)
    (hk : k < r.length) (hki : ¬ k = i) :
    ground.getAt 0 (raiseOff i r) k = ground.getAt 0 r k + 1 := by
  show ground.getAt 0 (ground.dipAt i (r.map (fun x => x + 1))) k
    = ground.getAt 0 r k + 1
  rw [ground.getAt_dipAt_ne i (r.map (fun x => x + 1)) k hki,
    ground.getAt_map 0 0 (fun x => x + 1) r k hk]

/-- The tie at a withdrawn letter's content: the first display is
the second's all-but-one raise. -/
private theorem tieGap_coUnit (d : Nat) (y z : List Nat)
    (hy : y.length = d) (hz : z.length = d) (i : Nat) (hi : i < d) :
    ground.tieGap y z = some (coUnit d i) ↔ y = raiseOff i z := by
  have hcg : ∀ k, ground.getAt 0 (coUnit d i) k
      = if k < d then (if k = i then 0 else 1) else 0 := fun k =>
    ground.getAt_map_range 0 (fun k => if k = i then 0 else 1) d k
  constructor
  · intro hg
    obtain ⟨_, _, hent⟩ := ground.tieGap_reads y z _ hg
    refine ground.getAt_ext 0 y (raiseOff i z)
      (by rw [length_raiseOff, hy, hz]) (fun k hk => ?_)
    have hkd : k < d := by rw [← hy]; exact hk
    have hkz : k < z.length := by rw [hz]; exact hkd
    have he := hent k hk
    rw [hcg k, if_pos hkd] at he
    by_cases hki : k = i
    · rw [hki] at he ⊢
      rw [if_pos rfl, Nat.zero_add] at he
      rw [getAt_raiseOff_self i z (by rw [hz]; exact hi), ← he]
    · rw [if_neg hki, Nat.add_comm] at he
      rw [getAt_raiseOff_ne i z k hkz hki, ← he]
  · intro hb
    refine ground.tieGap_make y z _ (by rw [length_coUnit, hy])
      (by rw [hz, hy]) (fun k hk => ?_)
    have hkd : k < d := by rw [← hy]; exact hk
    have hkz : k < z.length := by rw [hz]; exact hkd
    rw [hcg k, if_pos hkd, hb]
    by_cases hki : k = i
    · rw [hki, if_pos rfl, Nat.zero_add,
        getAt_raiseOff_self i z (by rw [hz]; exact hi)]
    · rw [if_neg hki, getAt_raiseOff_ne i z k hkz hki, Nat.add_comm]

private theorem map1_zip : ∀ (u v : List Nat),
    (List.zipWith (fun a b => a + b) u v).map (fun x => x + 1)
      = List.zipWith (fun a b => a + b) (u.map (fun x => x + 1)) v
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: u, b :: v => by
    show (a + b + 1) :: (List.zipWith (fun a b => a + b) u v).map
        (fun x => x + 1)
      = (a + 1 + b) :: List.zipWith (fun a b => a + b)
        (u.map (fun x => x + 1)) v
    rw [map1_zip u v, Nat.add_right_comm]

private theorem raiseOff_zip (s : Shape) (i : Nat)
    (hi : i < s.length) :
    raiseOff i (display s)
      = List.zipWith (fun a b => a + b) (raiseOff i (rowList s))
        (unitDisp s.length) := by
  show ground.dipAt i ((display s).map (fun x => x + 1)) = _
  rw [weylchar.display_zip s,
    map1_zip (rowList s) (unitDisp s.length),
    ← ground.dipAt_zipWith_left i ((rowList s).map (fun x => x + 1))
      (unitDisp s.length)
      (by rw [ground.getAt_map 0 0 (fun x => x + 1) (rowList s) i
            (by rw [length_rowList]; exact hi)]
          exact Nat.succ_pos _)]
  rfl

/-- The all-but-one raise reads the same at the display and at the
row list: the unit display rides along untouched. -/
private theorem display_dip (s c : Shape) (hca : c.length = s.length)
    (i : Nat) (hi : i < s.length) :
    display c = raiseOff i (display s)
      ↔ rowList c = raiseOff i (rowList s) := by
  have hds : raiseOff i (display s)
      = List.zipWith (fun a b => a + b) (raiseOff i (rowList s))
        (unitDisp s.length) := raiseOff_zip s i hi
  have hdc : display c
      = List.zipWith (fun a b => a + b) (rowList c)
        (unitDisp s.length) := by
    rw [weylchar.display_zip c, hca]
  constructor
  · intro he
    rw [hdc, hds] at he
    refine ground.getAt_ext 0 (rowList c) (raiseOff i (rowList s))
      (by rw [length_rowList, length_raiseOff, length_rowList, hca])
      (fun k hk => ?_)
    have hkc : k < (rowList c).length := hk
    have hks : k < (raiseOff i (rowList s)).length := by
      rw [length_raiseOff, length_rowList, ← hca, ← length_rowList]
      exact hk
    have hku : k < (unitDisp s.length).length := by
      rw [length_unitDisp, ← hca, ← length_rowList]
      exact hk
    have h1 : ground.getAt 0
          (List.zipWith (fun a b => a + b) (rowList c)
            (unitDisp s.length)) k
        = ground.getAt 0
          (List.zipWith (fun a b => a + b)
            (raiseOff i (rowList s)) (unitDisp s.length)) k := by
      rw [he]
    rw [ground.getAt_zipWith 0 0 0 (fun a b => a + b) (rowList c)
        (unitDisp s.length) k hkc hku,
      ground.getAt_zipWith 0 0 0 (fun a b => a + b)
        (raiseOff i (rowList s)) (unitDisp s.length) k hks hku] at h1
    exact ground.addCancelR _ h1
  · intro he
    rw [hdc, hds, he]

/-- The full-column raise maps every row up by one. -/
private theorem rowList_bumpLast : ∀ s : Shape, 0 < s.length →
    rowList (ground.bumpAt (s.length - 1) s)
      = (rowList s).map (fun x => x + 1)
  | [a], _ => rfl
  | a :: b :: t, _ => by
    show rowList (a :: ground.bumpAt ((b :: t).length - 1) (b :: t))
      = ((a + sumNat (b :: t)) :: rowList (b :: t)).map
        (fun x => x + 1)
    show (a + sumNat (ground.bumpAt ((b :: t).length - 1) (b :: t)))
        :: rowList (ground.bumpAt ((b :: t).length - 1) (b :: t))
      = (a + sumNat (b :: t) + 1)
        :: (rowList (b :: t)).map (fun x => x + 1)
    rw [rowList_bumpLast (b :: t) (Nat.succ_pos t.length),
      ground.sumNat_bumpAt ((b :: t).length - 1) (b :: t)
        (Nat.lt_succ_self t.length),
      ← Nat.add_assoc]

/-- The withdrawals' counting split at the two arms. -/
private theorem removals_member (w c : Shape) (hd : 0 < w.length)
    (hpos : 0 < ground.countOf c (units.removals w)) :
    ∃ i, i < w.length
      ∧ rowList c = ground.dipAt i (rowList w) := by
  match w, hd, hpos with
  | a :: t, _, hpos =>
    rw [units.removals_split a t c] at hpos
    match Nat.eq_zero_or_pos (ground.countOf c
        (if 0 < a then [(a - 1) :: t] else [])) with
    | .inr hh =>
      refine ⟨0, Nat.succ_pos t.length, ?_⟩
      by_cases hg : 0 < a
      · rw [if_pos hg] at hh
        rw [ground.countOf_single hh]
        have hgrow : rowList (a :: t)
            = ground.bumpAt 0 (rowList ((a - 1) :: t)) := by
          have h1 := units.rowList_grow (a - 1) t
          rw [show a - 1 + 1 = a from ground.subAdd hg] at h1
          exact h1
        rw [hgrow, ground.dipAt_bumpAt_self]
      · rw [if_neg hg] at hh
        exact absurd hh (Nat.lt_irrefl 0)
    | .inl hz =>
      rw [hz, Nat.zero_add] at hpos
      obtain ⟨j, hj, hfj⟩ := ground.famFold_pos_witness _
        (List.range t.length) hpos
      have hjt : j < t.length := ground.ltOfMem hj
      by_cases hg : 0 < ground.getAt 0 (a :: t) (j + 1)
      · rw [if_pos hg] at hfj
        refine ⟨j + 1, Nat.succ_lt_succ hjt, ?_⟩
        rw [ground.countOf_single hfj]
        exact units.rowList_moveUp j (a :: t)
          (Nat.succ_lt_succ hjt) hg
      · rw [if_neg hg] at hfj
        exact absurd hfj (Nat.lt_irrefl 0)

/-- A row-list dip at an interior row reads the source's occupancy
at the row's own key. -/
private theorem occ_of_dip (s c : Shape) (i : Nat)
    (hi : i + 1 < s.length) (hca : c.length = s.length)
    (hb : rowList c = raiseOff i (rowList s)) :
    ground.getAt 0 c i + 1 = ground.getAt 0 s i := by
  have his : i < s.length := Nat.lt_of_succ_lt hi
  have hirs : i < (rowList s).length := by
    rw [length_rowList]; exact his
  have hi1rs : i + 1 < (rowList s).length := by
    rw [length_rowList]; exact hi
  have h1 : ground.getAt 0 (rowList c) i
      = ground.getAt 0 (rowList s) i := by
    rw [hb, getAt_raiseOff_self i (rowList s) hirs]
  have h2 : ground.getAt 0 (rowList c) (i + 1)
      = ground.getAt 0 (rowList s) (i + 1) + 1 := by
    rw [hb, getAt_raiseOff_ne i (rowList s) (i + 1) hi1rs
      (Nat.ne_of_gt (Nat.lt_succ_self i))]
  have h3 := rowList_gap c i (by rw [hca]; exact his)
  rw [h1, h2, rowList_gap s i his] at h3
  have h4 : ground.getAt 0 c i + 1
        + ground.getAt 0 (rowList s) (i + 1)
      = ground.getAt 0 s i + ground.getAt 0 (rowList s) (i + 1) := by
    rw [Nat.add_right_comm (ground.getAt 0 c i) 1
        (ground.getAt 0 (rowList s) (i + 1)),
      Nat.add_assoc (ground.getAt 0 c i)
        (ground.getAt 0 (rowList s) (i + 1)) 1]
    exact h3.symm
  exact ground.addCancelR _ h4

private theorem rowD_dip (s c : Shape) (hd : 0 < s.length)
    (hpos : 0 < ground.countOf c (rowD s)) :
    ∃ i, i < s.length ∧ rowList c = raiseOff i (rowList s) := by
  obtain ⟨i, hi, hrc⟩ := removals_member
    (ground.bumpAt (s.length - 1) s) c
    (by rw [ground.length_bumpAt]; exact hd) hpos
  rw [ground.length_bumpAt] at hi
  refine ⟨i, hi, ?_⟩
  rw [hrc, rowList_bumpLast s hd]
  rfl

private theorem dipAt_inj (r : List Nat) (i i' : Nat)
    (hri : 0 < ground.getAt 0 r i) (hne : ¬ i = i') :
    ¬ ground.dipAt i r = ground.dipAt i' r := by
  intro he
  have h1 : ground.getAt 0 (ground.dipAt i r) i
      = ground.getAt 0 (ground.dipAt i' r) i := by rw [he]
  rw [ground.getAt_dipAt i r,
    ground.getAt_dipAt_ne i' r i hne] at h1
  have h2 : ground.getAt 0 r i - 1 + 1
      = ground.getAt 0 r i + 1 := by rw [h1]
  rw [ground.subAdd hri] at h2
  exact absurd h2 (Nat.ne_of_lt (Nat.lt_succ_self _))

/-- The dip at a row names exactly one withdrawal, at the stated
occupancies. -/
private theorem dip_removals (w c : Shape)
    (hca : c.length = w.length) (i : Nat) (hi : i < w.length)
    (hrow : ∀ k, k < w.length → 0 < ground.getAt 0 (rowList w) k)
    (hb : rowList c = ground.dipAt i (rowList w))
    (harm0 : i = 0 → 0 < ground.getAt 0 w 0)
    (harmj : ∀ j, i = j + 1 → 0 < ground.getAt 0 w (j + 1)) :
    ground.countOf c (units.removals w) = 1 := by
  match w, hca, hi, hrow, hb, harm0, harmj with
  | a :: t, hca, hi, hrow, hb, harm0, harmj =>
    have hrl : (rowList (a :: t)).length = t.length + 1 :=
      length_rowList (a :: t)
    have hmv : ∀ j, j < t.length → 0 < ground.getAt 0 (a :: t) (j + 1) →
        rowList (units.moveUp j (a :: t))
          = ground.dipAt (j + 1) (rowList (a :: t)) :=
      fun j hj hg => units.rowList_moveUp j (a :: t)
        (Nat.succ_lt_succ hj) hg
    rw [units.removals_split a t c]
    match i, hi, hb, harm0, harmj with
    | 0, _, hb, harm0, _ =>
      have ha : 0 < a := harm0 rfl
      have hgrow : ground.dipAt 0 (rowList (a :: t))
          = rowList ((a - 1) :: t) := by
        have h1 := units.rowList_grow (a - 1) t
        rw [show a - 1 + 1 = a from ground.subAdd ha] at h1
        rw [h1, ground.dipAt_bumpAt_self]
      have hce : c = (a - 1) :: t :=
        rowList_inj c ((a - 1) :: t) (by rw [hb, hgrow])
      have hstep : ∀ j, 0 < ground.countOf j (List.range t.length) →
          ground.countOf c
            (if 0 < ground.getAt 0 (a :: t) (j + 1) then
              [units.moveUp j (a :: t)] else []) = 0 := by
        intro j hj
        by_cases hg : 0 < ground.getAt 0 (a :: t) (j + 1)
        · have hne : ¬ c = units.moveUp j (a :: t) := by
            intro hcm
            refine dipAt_inj (rowList (a :: t)) 0 (j + 1)
              (hrow 0 (Nat.succ_pos t.length))
              (fun h0 => Nat.noConfusion h0) ?_
            rw [← hb, hcm]
            exact hmv j (ground.ltOfMem hj) hg
          rw [if_pos hg]
          exact ground.countOf_head_ne hne ([] : List Shape)
        · rw [if_neg hg]
          rfl
      have hhz : ground.countOf c
          (if 0 < a then [(a - 1) :: t] else []) = 1 := by
        rw [if_pos ha, hce, ground.countOf_head]
        rfl
      rw [hhz,
        ground.famFold_congr_members Nat.add 0 _ (fun _ => (0 : Nat))
          (List.range t.length) hstep,
        ground.famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl)
          (List.range t.length), Nat.add_zero]
    | j0 + 1, hi, hb, _, harmj =>
      have hj0 : j0 < t.length := Nat.lt_of_succ_lt_succ hi
      have hocc : 0 < ground.getAt 0 (a :: t) (j0 + 1) := harmj j0 rfl
      have hcm : c = units.moveUp j0 (a :: t) :=
        rowList_inj c (units.moveUp j0 (a :: t))
          (by rw [hb, hmv j0 hj0 hocc])
      have hnh : ground.countOf c
          (if 0 < a then [(a - 1) :: t] else []) = 0 := by
        by_cases ha : 0 < a
        · have hne : ¬ c = (a - 1) :: t := by
            intro hce
            refine dipAt_inj (rowList (a :: t)) (j0 + 1) 0
              (hrow (j0 + 1) (Nat.succ_lt_succ hj0))
              (fun h0 => Nat.noConfusion h0) ?_
            have hgrow : ground.dipAt 0 (rowList (a :: t))
                = rowList ((a - 1) :: t) := by
              have h1 := units.rowList_grow (a - 1) t
              rw [show a - 1 + 1 = a from ground.subAdd ha] at h1
              rw [h1, ground.dipAt_bumpAt_self]
            rw [← hb, hce, ← hgrow]
          rw [if_pos ha]
          exact ground.countOf_head_ne hne ([] : List Shape)
        · rw [if_neg ha]
          rfl
      have hstep : ∀ j, 0 < ground.countOf j (List.range t.length) →
          ground.countOf c
            (if 0 < ground.getAt 0 (a :: t) (j + 1) then
              [units.moveUp j (a :: t)] else [])
            = if j0 = j then 1 else 0 := by
        intro j hj
        by_cases hj0j : j0 = j
        · rw [← hj0j, if_pos hocc, if_pos rfl, hcm,
            ground.countOf_head]
          rfl
        · by_cases hg : 0 < ground.getAt 0 (a :: t) (j + 1)
          · have hne : ¬ c = units.moveUp j (a :: t) := by
              intro hcm2
              refine dipAt_inj (rowList (a :: t)) (j0 + 1) (j + 1)
                (hrow (j0 + 1) (Nat.succ_lt_succ hj0))
                (fun he => hj0j (Nat.succ.inj he)) ?_
              rw [← hb, hcm2]
              exact hmv j (ground.ltOfMem hj) hg
            rw [if_neg hj0j, if_pos hg]
            exact ground.countOf_head_ne hne ([] : List Shape)
          · rw [if_neg hj0j, if_neg hg]
            rfl
      rw [hnh, Nat.zero_add,
        ground.famFold_congr_members Nat.add 0 _
          (fun j => if j0 = j then 1 else 0) (List.range t.length)
          hstep,
        ← ground.countOf_fold j0 (List.range t.length),
        countOf_range j0 t.length, if_pos hj0]

private theorem dip_rowD (s c : Shape) (hca : c.length = s.length)
    (i : Nat) (hi : i < s.length)
    (hb : rowList c = raiseOff i (rowList s)) :
    ground.countOf c (rowD s) = 1 := by
  have hd : 0 < s.length := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  have hrow : ∀ k, k < (ground.bumpAt (s.length - 1) s).length →
      0 < ground.getAt 0
        (rowList (ground.bumpAt (s.length - 1) s)) k := by
    intro k hk
    rw [ground.length_bumpAt] at hk
    rw [rowList_bumpLast s hd,
      ground.getAt_map 0 0 (fun x => x + 1) (rowList s) k
        (by rw [length_rowList]; exact hk)]
    exact Nat.succ_pos _
  have hb' : rowList c
      = ground.dipAt i (rowList (ground.bumpAt (s.length - 1) s)) := by
    rw [rowList_bumpLast s hd]
    exact hb
  refine dip_removals (ground.bumpAt (s.length - 1) s) c
    (by rw [ground.length_bumpAt]; exact hca)
    i (by rw [ground.length_bumpAt]; exact hi) hrow hb' ?_ ?_
  · intro h0
    match s, hca, hi, hb, hd with
    | [a], _, _, _, _ =>
      show 0 < ground.getAt 0 (ground.bumpAt 0 [a]) 0
      rw [ground.getAt_bumpAt_self ((0 : Nat)) [a] (Nat.succ_pos 0)]
      exact Nat.succ_pos a
    | a :: b :: t2, hca, hi, hb, _ =>
      show 0 < ground.getAt 0
        (ground.bumpAt (t2.length + 1) (a :: b :: t2)) 0
      rw [ground.getAt_bumpAt_ne (t2.length + 1)
        (a :: b :: t2) 0 (fun h => Nat.noConfusion h)]
      have hocc := occ_of_dip (a :: b :: t2) c 0
        (Nat.succ_lt_succ (Nat.succ_pos t2.length)) hca
        (by rw [← h0]; exact hb)
      rw [← hocc]
      exact Nat.succ_pos _
  · intro j hj
    match s, hca, hi, hb, hd with
    | [a], _, hi, _, _ =>
      rw [hj] at hi
      exact absurd (Nat.lt_of_succ_lt_succ hi) (Nat.not_lt_zero j)
    | a :: b :: t2, hca, hi, hb, _ =>
      by_cases hlast : j + 1 = t2.length + 1
      · show 0 < ground.getAt 0
          (ground.bumpAt (t2.length + 1) (a :: b :: t2)) (j + 1)
        rw [hlast, ground.getAt_bumpAt_self (t2.length + 1)
          (a :: b :: t2) (Nat.lt_succ_self _)]
        exact Nat.succ_pos _
      · show 0 < ground.getAt 0
          (ground.bumpAt (t2.length + 1) (a :: b :: t2)) (j + 1)
        rw [ground.getAt_bumpAt_ne (t2.length + 1)
          (a :: b :: t2) (j + 1) hlast]
        have hj2 : (j + 1) + 1 < (a :: b :: t2).length := by
          have hjlt : j + 1 < t2.length + 1 + 1 := by
            rw [← hj]
            exact hi
          have hjle : j + 1 < t2.length + 1 :=
            Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hjlt) hlast
          exact Nat.succ_lt_succ hjle
        have hocc := occ_of_dip (a :: b :: t2) c (j + 1) hj2 hca
          (by rw [← hj]; exact hb)
        rw [← hocc]
        exact Nat.succ_pos _

private theorem rowD_zero (s c : Shape) (hd : 0 < s.length)
    (hca : c.length = s.length)
    (hno : ∀ i, i < s.length →
      ¬ ground.tieGap (display c) (display s)
        = some (coUnit s.length i)) :
    ground.countOf c (rowD s) = 0 := by
  match hc : ground.countOf c (rowD s) with
  | 0 => rfl
  | n + 1 =>
    obtain ⟨i, hi, hbi⟩ := rowD_dip s c hd
      (by rw [hc]; exact Nat.succ_pos n)
    exact absurd
      ((tieGap_coUnit s.length (display c) (display s)
          (by rw [length_display, hca]) (length_display s) i hi).mpr
        ((display_dip s c hca i hi).mpr hbi))
      (hno i hi)

private theorem rowD_one (s c : Shape) (hca : c.length = s.length)
    (i : Nat) (hi : i < s.length)
    (hg : ground.tieGap (display c) (display s)
      = some (coUnit s.length i)) :
    ground.countOf c (rowD s) = 1 :=
  dip_rowD s c hca i hi
    ((display_dip s c hca i hi).mp
      ((tieGap_coUnit s.length (display c) (display s)
        (by rw [length_display, hca]) (length_display s) i hi).mp hg))

/-- The complement factor's tie value at the source's own display:
the gap's occupancy is the complement row's occupancy at the
target. -/
private theorem gapValue_rowD (s c : Shape) (hd2 : 2 ≤ s.length)
    (hca : c.length = s.length) :
    weylchar.multAtGap
        (blockcount.occupancyAt
          (blockcount.blockSpan (complBox s.length)))
        (display c) (display s)
      = ground.countOf c (rowD s) := by
  have hd : 0 < s.length := Nat.lt_of_lt_of_le (Nat.succ_pos 1) hd2
  show (match ground.tieGap (display c) (display s) with
    | some nu => blockcount.occupancyAt
        (blockcount.blockSpan (complBox s.length)) nu
    | none => 0) = ground.countOf c (rowD s)
  cases hg : ground.tieGap (display c) (display s) with
  | none =>
    have hno : ∀ i, i < s.length →
        ¬ ground.tieGap (display c) (display s)
          = some (coUnit s.length i) := by
      intro i _ he
      rw [hg] at he
      exact nomatch he
    show (0 : Nat) = ground.countOf c (rowD s)
    rw [rowD_zero s c hd hca hno]
  | some m =>
    show blockcount.occupancyAt
        (blockcount.blockSpan (complBox s.length)) m
      = ground.countOf c (rowD s)
    rw [occ_complBox s.length hd2 m]
    by_cases hu : 0 < ground.countOf m
        ((List.range s.length).map (coUnit s.length))
    · obtain ⟨i, hi, him⟩ := coUnit_of_pos s.length m hu
      rw [← him, countOf_coUnitList s.length i hi,
        rowD_one s c hca i hi (hg.trans (congrArg some him.symm))]
    · have hz : ground.countOf m
          ((List.range s.length).map (coUnit s.length)) = 0 := by
        match hcm : ground.countOf m
            ((List.range s.length).map (coUnit s.length)) with
        | 0 => rfl
        | n + 1 => exact absurd (by rw [hcm]; exact Nat.succ_pos n) hu
      have hno : ∀ i, i < s.length →
          ¬ ground.tieGap (display c) (display s)
            = some (coUnit s.length i) := by
        intro i hi he
        have hme : m = coUnit s.length i :=
          Option.some.inj (hg.symm.trans he)
        refine hu ?_
        rw [hme, countOf_coUnitList s.length i hi]
        exact Nat.succ_pos 0
      rw [hz, rowD_zero s c hd hca hno]

private theorem desc_map1 (v : List Nat)
    (hdv : ∀ k, k + 1 < v.length →
      ground.getAt 0 v (k + 1) < ground.getAt 0 v k) :
    ∀ k, k + 1 < (v.map (fun x => x + 1)).length →
      ground.getAt 0 (v.map (fun x => x + 1)) (k + 1)
        < ground.getAt 0 (v.map (fun x => x + 1)) k := by
  intro k hk
  rw [ground.length_map] at hk
  rw [ground.getAt_map 0 0 (fun x => x + 1) v (k + 1) hk,
    ground.getAt_map 0 0 (fun x => x + 1) v k (Nat.lt_of_succ_lt hk)]
  exact Nat.succ_lt_succ (hdv k hk)

private theorem expo_map1 (v p : List Nat) (d : Nat)
    (hv : v.length = d)
    (hp : 0 < ground.countOf p (places.perms d)) :
    places.expo (v.map (fun x => x + 1)) p
      = (places.expo v p).map (fun x => x + 1) := by
  obtain ⟨_, _, hpval, _⟩ := perm_member_reads hp
  show p.map (ground.getAt 0 (v.map (fun x => x + 1)))
    = (p.map (ground.getAt 0 v)).map (fun x => x + 1)
  rw [ground.map_map (ground.getAt 0 v) (fun x => x + 1) p]
  exact ground.map_congr_members _ _ p (fun y hy => by
    rw [ground.getAt_map 0 0 (fun x => x + 1) v y
      (by rw [hv]; exact hpval y hy)])

private theorem expo_inv (X p : List Nat) (d : Nat)
    (hX : X.length = d)
    (hp : 0 < ground.countOf p (places.perms d)) :
    places.expo (places.expo X p) (invPerm d p) = X := by
  obtain ⟨hplen, _, _, _⟩ := perm_member_reads hp
  obtain ⟨_, _, hival, _⟩ := perm_member_reads (invPerm_member d hp)
  show (invPerm d p).map (ground.getAt 0 (places.expo X p)) = X
  rw [ground.map_congr_members
      (ground.getAt 0 (places.expo X p))
      (fun y => ground.getAt 0 X (ground.getAt 0 p y))
      (invPerm d p)
      (fun y hy => places.getAt_expo X p y
        (by rw [hplen]; exact hival y hy)),
    ← ground.map_map (ground.getAt 0 p) (ground.getAt 0 X)
      (invPerm d p),
    invPerm_comp d hp, range_map_getAt 0 d X hX]

private theorem posOf_getAt_perm (d : Nat) {p : List Nat}
    (hp : 0 < ground.countOf p (places.perms d))
    (i : Nat) (hi : i < d) :
    posOf (ground.getAt 0 p i) p = i := by
  obtain ⟨hplen, hpdist, _, _⟩ := perm_member_reads hp
  have hocc : 0 < ground.countOf (ground.getAt 0 p i) p :=
    ground.countOf_getAt_pos 0 p i (by rw [hplen]; exact hi)
  have hga := getAt_posOf (ground.getAt 0 p i) p hocc
  by_cases he : posOf (ground.getAt 0 p i) p = i
  · exact he
  · exact absurd
      (Nat.le_trans
        (by
          have h := ground.countOf_two_pos 0 p
            (posOf (ground.getAt 0 p i) p) i
            (posOf_lt _ p hocc) (by rw [hplen]; exact hi) he hga
          rw [hga] at h
          exact h)
        (hpdist (ground.getAt 0 p i)))
      (Nat.lt_irrefl 1)

private theorem posOf_range (d j : Nat) (hj : j < d) :
    posOf j (List.range d) = j := by
  have h := posOf_getAt_perm d
    (by rw [places.countRangePerms d]; exact Nat.succ_pos 0) j hj
  rw [ground.getAt_range d j hj] at h
  exact h

private theorem invPerm_range (d : Nat) :
    invPerm d (List.range d) = List.range d := by
  show (List.range d).map (fun j => posOf j (List.range d))
    = List.range d
  rw [ground.map_congr_members (fun j => posOf j (List.range d))
      (ground.getAt 0 (List.range d)) (List.range d)
      (fun j hj => by
        have hjd : j < d := by
          have hc := hj
          rw [countOf_range j d] at hc
          by_cases hcd : j < d
          · exact hcd
          · rw [if_neg hcd] at hc
            exact absurd hc (Nat.lt_irrefl 0)
        rw [posOf_range d j hjd, ground.getAt_range d j hjd]),
    range_map_getAt 0 d (List.range d) (ground.length_range d)]

private theorem expo_bump_inv (v p : List Nat) (d i : Nat)
    (hv : v.length = d) (hi : i < d)
    (hp : 0 < ground.countOf p (places.perms d)) :
    places.expo (ground.bumpAt i v) (invPerm d p)
      = ground.bumpAt (ground.getAt 0 p i)
          (places.expo v (invPerm d p)) := by
  obtain ⟨hplen, _, hpval, hpocc⟩ := perm_member_reads hp
  obtain ⟨hqlen, _, hqval, _⟩ := perm_member_reads (invPerm_member d hp)
  have hqm : ∀ k, k < d →
      ground.getAt 0 (invPerm d p) k = posOf k p := fun k hk => by
    show ground.getAt 0
      ((List.range d).map (fun j => posOf j p)) k = posOf k p
    rw [ground.getAt_map_range 0 (fun j => posOf j p) d k, if_pos hk]
  have hi' : ground.getAt 0 p i < d :=
    hpval _ (ground.countOf_getAt_pos 0 p i (by rw [hplen]; exact hi))
  refine ground.getAt_ext 0 _ _ ?_ (fun k hk => ?_)
  · show ((invPerm d p).map
        (ground.getAt 0 (ground.bumpAt i v))).length
      = (ground.bumpAt (ground.getAt 0 p i)
          ((invPerm d p).map (ground.getAt 0 v))).length
    rw [ground.length_map, ground.length_bumpAt, ground.length_map]
  · have hkd : k < d := by
      show k < d
      have hk2 : k < ((invPerm d p).map
          (ground.getAt 0 (ground.bumpAt i v))).length := hk
      rw [ground.length_map, hqlen] at hk2
      exact hk2
    have hkq : k < (invPerm d p).length := by rw [hqlen]; exact hkd
    rw [places.getAt_expo (ground.bumpAt i v) (invPerm d p) k hkq]
    show ground.getAt 0 (ground.bumpAt i v)
        (ground.getAt 0 (invPerm d p) k)
      = ground.getAt 0 (ground.bumpAt (ground.getAt 0 p i)
          ((invPerm d p).map (ground.getAt 0 v))) k
    by_cases hki : k = ground.getAt 0 p i
    · rw [hki, ground.getAt_bumpAt_self (ground.getAt 0 p i)
          ((invPerm d p).map (ground.getAt 0 v))
          (by rw [ground.length_map, hqlen]; exact hi'),
        hqm (ground.getAt 0 p i) hi', posOf_getAt_perm d hp i hi,
        ground.getAt_bumpAt_self i v (by rw [hv]; exact hi)]
      rw [show ground.getAt 0
          ((invPerm d p).map (ground.getAt 0 v))
          (ground.getAt 0 p i)
        = ground.getAt 0 v i from by
        rw [ground.getAt_map 0 0 (ground.getAt 0 v) (invPerm d p)
            (ground.getAt 0 p i) (by rw [hqlen]; exact hi'),
          hqm (ground.getAt 0 p i) hi',
          posOf_getAt_perm d hp i hi]]
    · have hne : ¬ ground.getAt 0 (invPerm d p) k = i := by
        rw [hqm k hkd]
        intro hpk
        have hocc : 0 < ground.countOf k p := hpocc k hkd
        have h2 := getAt_posOf k p hocc
        rw [hpk] at h2
        exact hki h2.symm
      rw [ground.getAt_bumpAt_ne i v (ground.getAt 0 (invPerm d p) k)
          hne,
        ground.getAt_bumpAt_ne (ground.getAt 0 p i)
          ((invPerm d p).map (ground.getAt 0 v)) k hki,
        ground.getAt_map 0 0 (ground.getAt 0 v) (invPerm d p) k hkq]

/-- `cor:steinberg`'s two graded sums at the complement factor: the
identity permutation the one contributor, the even sum the
complement row's occupancy at the target and the odd sum vacant. -/
private theorem gradedSums_complBox (s c : Shape)
    (hd2 : 2 ≤ s.length) (hca : c.length = s.length) :
    steinberg.gradedSums (complBox s.length) s c
      = (ground.countOf c (rowD s), 0) := by
  have hoff : ∀ p ∈ places.perms s.length,
      ¬ p = List.range s.length → ∀ acc : Nat × Nat,
      (match ground.tieGap (display c) (places.expo (display s) p) with
        | none => acc
        | some m =>
          if parity p then
            (acc.1, acc.2 + blockcount.occupancyAt
              (blockcount.blockSpan (complBox s.length)) m)
          else
            (acc.1 + blockcount.occupancyAt
              (blockcount.blockSpan (complBox s.length)) m, acc.2))
        = acc := by
    intro p hpm hne acc
    have hp : 0 < ground.countOf p (places.perms s.length) :=
      ground.countOf_pos_of_mem hpm
    obtain ⟨hplen, _, hpval, _⟩ := perm_member_reads hp
    cases hg : ground.tieGap (display c)
        (places.expo (display s) p) with
    | none => rfl
    | some m =>
      have hzm : blockcount.occupancyAt
          (blockcount.blockSpan (complBox s.length)) m = 0 := by
        rw [occ_complBox s.length hd2 m]
        match hcm : ground.countOf m
            ((List.range s.length).map (coUnit s.length)) with
        | 0 => rfl
        | n + 1 =>
          obtain ⟨i, hi, him⟩ := coUnit_of_pos s.length m
            (by rw [hcm]; exact Nat.succ_pos n)
          have hpl : (places.expo (display s) p).length = s.length := by
            show (p.map (ground.getAt 0 (display s))).length = s.length
            rw [ground.length_map]
            exact hplen
          have hbu : display c
              = raiseOff i (places.expo (display s) p) :=
            (tieGap_coUnit s.length (display c)
              (places.expo (display s) p)
              (by rw [length_display, hca]) hpl i hi).mp
              (hg.trans (congrArg some him.symm))
          have hexpo : places.expo
                ((display s).map (fun x => x + 1)) p
              = (places.expo (display s) p).map (fun x => x + 1) :=
            expo_map1 (display s) p s.length (length_display s) hp
          have hocc : 0 < ground.getAt 0
              (places.expo ((display s).map (fun x => x + 1)) p) i := by
            rw [places.getAt_expo _ p i (by rw [hplen]; exact hi),
              ground.getAt_map 0 0 (fun x => x + 1) (display s)
                (ground.getAt 0 p i)
                (by rw [length_display]
                    exact hpval _ (ground.countOf_getAt_pos 0 p i
                      (by rw [hplen]; exact hi)))]
            exact Nat.succ_pos _
          have hbu2 : places.expo
              ((display s).map (fun x => x + 1)) p
              = ground.bumpAt i (display c) := by
            rw [hbu]
            show places.expo ((display s).map (fun x => x + 1)) p
              = ground.bumpAt i (ground.dipAt i
                ((places.expo (display s) p).map (fun x => x + 1)))
            rw [← hexpo, ground.bumpAt_dipAt_self i _ hocc]
          have happ : (display s).map (fun x => x + 1)
              = places.expo (ground.bumpAt i (display c))
                (invPerm s.length p) := by
            rw [← hbu2]
            exact (expo_inv ((display s).map (fun x => x + 1)) p
              s.length
              (by rw [ground.length_map, length_display]) hp).symm
          have hi' : ground.getAt 0 p i < s.length :=
            hpval _ (ground.countOf_getAt_pos 0 p i
              (by rw [hplen]; exact hi))
          have htr := places.tie_rigid s.length (display c)
            ((display s).map (fun x => x + 1))
            (by rw [length_display, hca])
            (by rw [ground.length_map, length_display])
            (fun k hk => display_desc c k (by rw [hca]; exact hk))
            (fun k hk => desc_map1 (display s)
              (fun k2 hk2 => display_desc s k2
                (by rw [length_display s] at hk2; exact hk2)) k
              (by rw [ground.length_map, length_display]; exact hk))
            (invPerm s.length p) (invPerm_member s.length hp)
            (ground.getAt 0 p i) hi'
            (happ.trans
              (expo_bump_inv (display c) p s.length i
                (by rw [length_display, hca]) hi hp))
          have hpr : p = List.range s.length := by
            have h1 := (invPerm_invPerm s.length hp).symm
            rw [htr.1, invPerm_range s.length] at h1
            exact h1
          exact absurd hpr hne
      show (if parity p then
          (acc.1, acc.2 + blockcount.occupancyAt
            (blockcount.blockSpan (complBox s.length)) m)
        else
          (acc.1 + blockcount.occupancyAt
            (blockcount.blockSpan (complBox s.length)) m, acc.2)) = acc
      rw [hzm]
      cases parity p with
      | true =>
        show ((acc.1, acc.2 + 0) : Nat × Nat) = acc
        rw [Nat.add_zero]
      | false =>
        show ((acc.1 + 0, acc.2) : Nat × Nat) = acc
        rw [Nat.add_zero]
  have hat : ∀ acc : Nat × Nat,
      (match ground.tieGap (display c)
          (places.expo (display s) (List.range s.length)) with
        | none => acc
        | some m =>
          if parity (List.range s.length) then
            (acc.1, acc.2 + blockcount.occupancyAt
              (blockcount.blockSpan (complBox s.length)) m)
          else
            (acc.1 + blockcount.occupancyAt
              (blockcount.blockSpan (complBox s.length)) m, acc.2))
        = (acc.1 + ground.countOf c (rowD s), acc.2) := by
    intro acc
    rw [show places.expo (display s) (List.range s.length) = display s
        from range_map_getAt 0 s.length (display s) (length_display s),
      parity_range s.length]
    have hv := gapValue_rowD s c hd2 hca
    cases hg : ground.tieGap (display c) (display s) with
    | none =>
      have hz : ground.countOf c (rowD s) = 0 := by
        rw [← hv]
        show (match ground.tieGap (display c) (display s) with
          | some nu => blockcount.occupancyAt
              (blockcount.blockSpan (complBox s.length)) nu
          | none => 0) = 0
        rw [hg]
      show acc = (acc.1 + ground.countOf c (rowD s), acc.2)
      rw [hz, Nat.add_zero]
    | some m =>
      have hvm : blockcount.occupancyAt
          (blockcount.blockSpan (complBox s.length)) m
          = ground.countOf c (rowD s) := by
        rw [← hv]
        show blockcount.occupancyAt
            (blockcount.blockSpan (complBox s.length)) m
          = match ground.tieGap (display c) (display s) with
            | some nu => blockcount.occupancyAt
                (blockcount.blockSpan (complBox s.length)) nu
            | none => 0
        rw [hg]
      show ((acc.1 + blockcount.occupancyAt
        (blockcount.blockSpan (complBox s.length)) m, acc.2)
          : Nat × Nat)
        = (acc.1 + ground.countOf c (rowD s), acc.2)
      rw [hvm]
  show steinberg.sumsWith
      (blockcount.occupancyAt
        (blockcount.blockSpan (complBox s.length)))
      (complBox s.length).length s c
    = (ground.countOf c (rowD s), 0)
  rw [length_complBox s.length]
  show (places.perms s.length).foldl
      (fun acc p =>
        match ground.tieGap (display c)
            (places.expo (display s) p) with
        | none => acc
        | some m =>
          if parity p then
            (acc.1, acc.2 + blockcount.occupancyAt
              (blockcount.blockSpan (complBox s.length)) m)
          else
            (acc.1 + blockcount.occupancyAt
              (blockcount.blockSpan (complBox s.length)) m, acc.2))
      (0, 0) = (ground.countOf c (rowD s), 0)
  rw [ground.foldl_pick _ (List.range s.length)
      (fun acc => (acc.1 + ground.countOf c (rowD s), acc.2)) hat
      (places.perms s.length) hoff
      (places.countRangePerms s.length) (0, 0)]
  show ((0 + ground.countOf c (rowD s), 0) : Nat × Nat)
    = (ground.countOf c (rowD s), 0)
  rw [Nat.zero_add]

/-- `lem:pieri`'s complement row read at any target of the stated
width: the fusion count at the complement's one-column shape is the
row's occupancy at the target, one exactly at the full column's
withdrawn letters — `cor:steinberg` at the complement factor, whose
block's contents are the withdrawn letters at one count each. -/
theorem readAllD (s c : Shape) (hd : 2 ≤ s.length)
    (hca : c.length = s.length) : readD s c := by
  have h := steinberg.readAll (complBox s.length) s c
    (by rw [length_complBox]) (by rw [length_complBox]; exact hca)
  have h2 : blockcount.fusionCount (complBox s.length) s c
      + (steinberg.gradedSums (complBox s.length) s c).2
    = (steinberg.gradedSums (complBox s.length) s c).1 := h
  rw [gradedSums_complBox s c hd hca] at h2
  have h3 : blockcount.fusionCount (complBox s.length) s c + 0
      = ground.countOf c (rowD s) := h2
  rw [Nat.add_zero] at h3
  show blockcount.fusionCount s (complBox s.length) c
    = ground.countOf c (rowD s)
  rw [blockcount.fusionCount_comm s (complBox s.length) c
    (length_complBox s.length)]
  exact h3

end pieri
