import MassGap.Pairpencil
import MassGap.Greenprod
/-!
`con:depthchain` — the depth chain of a window.  The `X`-sector's
carrier is the window index at the unit label class's alphabet, the
fusion data's labels read at the unit's class (`xData`).  A window's
members enter with their fibers' positions in the window list
(`pos`, one position list per index member, the unit's line the
member `0`); two positions are joined where some plaquette term's
entry at them sits off the sum's unit (`joinedAt`,
`thm:pairpencil`'s magnetic member at `def:algebra`'s changed-edge
read) and two members where some position pair is (`joined`), the
fusion graph, symmetric at symmetric terms (`joined_symm`); the
reach at a step count from the sector's base is the base, then at
each step the members joined to a reached member (`reach`,
`reachB`), a member's depth the least step count reaching it
(`depthOf` at `ground.firstAt`, the walk's budget the member count,
within which every reached member's depth sits: the reach grows by
a member per count until a count adds no member, and the walk is
closed there, `depth_lt` at the pigeonhole over the index); a
shell is the members at one depth (`shell`), the shells' list the
occupied shells from the base's depth up, closing at the first
vacant depth (`shells`), every occupied depth listed since a member
first reached at a count is joined to one first reached at the
count before (`mem_shells`), the position shells the members'
positions shell by shell (`posShells`), and the depth order lists
them (`depthOrder`).  A joined step moves the reach by one count
(`reach_step`), so the depth moves by at most one across a joined
pair (`depth_step`).

The slab data along a position-shell list are the shells' own
blocks (`slabDiag`, each shell's selection) and the bonds between
consecutive shells (`slabOff`), at `lem:greenprod`'s slab shape
(`slabs_shape`); the off-band read (`offBandB`) puts every entry
between two shells beyond neighbors at the sum's unit, and at it
the matrix along the joined key list is the assembled block
tridiagonal (`chain_assemble`, the shells' blocks and bonds at
`greenprod.assemble`).  A matrix whose entries between two
members' positions sit at the sum's unit wherever the members are
not joined (`crossB`) reads off-band along the depth chain's
position shells at the joined step's depth move
(`posShells_offBand`), so the depth chain is the assembled slab data
(`depth_assemble`); the magnetic member, the terms' sum, reads so
at the terms' own joins (`msum_cross`), and the gram with the
electric member's form at the fibers' orthogonal sum
(`memberDiag_cross`).
-/

namespace depthchain
open ground elim

/-- The positions' bound at every member key: a listed member's
positions sit below the order, and a key beyond the list reads the
vacant position list. -/
private theorem pos_lt (pos : List (List Nat)) (o : Nat)
    (hpos : ∀ s ∈ pos, ∀ i ∈ s, i < o) :
    ∀ a, ∀ i, i ∈ getAt [] pos a → i < o := fun a i hi => by
  cases Nat.lt_or_ge a pos.length with
  | inl h => exact hpos _ (mem_getAt [] pos a h) i hi
  | inr h =>
    rw [getAt_over [] pos a h] at hi
    exact nomatch hi

/-- The `X`-sector's alphabet: the fusion data with the labels below
a cutoff read at the unit's class alone, the adjoint's fusion
keeping every link's label class (`lem:chargedcell`(i)). -/
def xData {L : Type} (F : fusion.Data L) : fusion.Data L :=
  { F with below := fun C =>
      (F.below C).filter (fun l => F.cls l == F.cls F.unit) }

/-- Two positions are joined where some term's entry at them sits
off the sum's unit. -/
def joinedAt (terms : List Mat) (i j : Nat) : Bool :=
  terms.any (fun T =>
    !decide ((getAt BPair.unit (getAt [] T i) j).oneValue BPair.unit))

/-- Two members are joined where some pair of their positions is. -/
def joined (terms : List Mat) (pos : List (List Nat)) (a b : Nat) : Bool :=
  (getAt [] pos a).any (fun i => (getAt [] pos b).any (fun j =>
    joinedAt terms i j))

/-- The reach at a step count from the base among the members below
the count: the base, then at each step the members joined to a
reached member. -/
def reach (terms : List Mat) (pos : List (List Nat)) (n : Nat)
    (base : List Nat) : Nat → List Nat
  | 0 => base
  | k + 1 => (List.range n).filter (fun a =>
      containsB (reach terms pos n base k) a
        || (reach terms pos n base k).any (fun b => joined terms pos a b))

/-- A member's reach read at a step count. -/
def reachB (terms : List Mat) (pos : List (List Nat)) (n : Nat)
    (base : List Nat) (k a : Nat) : Bool :=
  containsB (reach terms pos n base k) a

/-- The depth: the least step count reaching the member, the walk's
budget the member count. -/
def depthOf (terms : List Mat) (pos : List (List Nat)) (n : Nat)
    (base : List Nat) (a : Nat) : Nat :=
  firstAt (fun k => reachB terms pos n base k a = true) 0 n

/-- The shell at a depth: the members below the count at that
depth. -/
def shell (terms : List Mat) (pos : List (List Nat)) (n : Nat)
    (base : List Nat) (d : Nat) : List Nat :=
  (List.range n).filter (fun a => depthOf terms pos n base a == d)

/-- The shells from a depth up, at a stated count: each depth's
shell joined while occupied, the list closing at the first vacant
depth. -/
def shellsGo (terms : List Mat) (pos : List (List Nat)) (n : Nat)
    (base : List Nat) : Nat → Nat → List (List Nat)
  | _, 0 => []
  | d, fuel + 1 =>
    match shell terms pos n base d with
    | [] => []
    | a :: s => (a :: s) :: shellsGo terms pos n base (d + 1) fuel

/-- The shells' list: the occupied shells from the base's depth up,
within the member count. -/
def shells (terms : List Mat) (pos : List (List Nat)) (n : Nat)
    (base : List Nat) : List (List Nat) :=
  shellsGo terms pos n base 0 n

/-- The position shells: each shell's members' positions. -/
def posShells (terms : List Mat) (pos : List (List Nat)) (n : Nat)
    (base : List Nat) : List (List Nat) :=
  (shells terms pos n base).map (fun s => s.flatMap (fun a => getAt [] pos a))

/-- The depth order: the sector's positions listed shell by shell. -/
def depthOrder (terms : List Mat) (pos : List (List Nat)) (n : Nat)
    (base : List Nat) : List Nat :=
  (posShells terms pos n base).flatMap (fun s => s)

/-- The diagonal blocks along a shell list, each shell's own
selection of the matrix. -/
def slabDiag (M : Mat) (sh : List (List Nat)) : List Mat :=
  sh.map (fun s => selM s s M)

/-- The bonds along a shell list, the selections at consecutive
shells. -/
def slabOff (M : Mat) : List (List Nat) → List Mat
  | [] => []
  | [_] => []
  | s :: s' :: t => selM s s' M :: slabOff M (s' :: t)

/-- The off-band read: every entry between a shell and the shells
beyond its neighbor sits at the sum's unit. -/
def offBandB (M : Mat) : List (List Nat) → Bool
  | [] => true
  | [_] => true
  | s :: s' :: t =>
    s.all (fun i => (t.flatMap (fun s => s)).all (fun j =>
        decide ((getAt BPair.unit (getAt [] M i) j).oneValue BPair.unit)))
      && offBandB M (s' :: t)

/-- The cross read: at every two distinct members not joined, the
matrix's entries between their positions sit at the sum's unit. -/
def crossB (terms : List Mat) (pos : List (List Nat)) (M : Mat) : Bool :=
  (List.range pos.length).all (fun a => (List.range pos.length).all (fun b =>
    (a == b) || joined terms pos a b
      || (getAt [] pos a).all (fun i => (getAt [] pos b).all (fun j =>
        decide ((getAt BPair.unit (getAt [] M i) j).oneValue BPair.unit)))))

/-- A member joined to a reached member is reached at the next
count. -/
private theorem reach_step (terms : List Mat) (pos : List (List Nat)) (n : Nat)
    (base : List Nat) (k a b : Nat) (ha : a < n)
    (hj : joined terms pos a b = true)
    (hr : reachB terms pos n base k b = true) :
    reachB terms pos n base (k + 1) a = true := by
  have hbm : b ∈ reach terms pos n base k :=
    mem_of_countOf_pos b _ (of_decide_eq_true hr)
  have h2 : (reach terms pos n base k).any (fun b => joined terms pos a b)
      = true := any_of_mem _ hbm hj
  show containsB ((List.range n).filter (fun a =>
      containsB (reach terms pos n base k) a
        || (reach terms pos n base k).any (fun b => joined terms pos a b))) a
    = true
  refine decide_eq_true (countOf_pos_of_mem (mem_filter_to _ (memRange ha) ?_))
  rw [h2]
  exact Bool.or_true _

/-- The depth moves by at most one across a joined step: a member
joined to another sits at most one depth beyond it, the budget's end
its cap where the walk misses. -/
theorem depth_step (terms : List Mat) (pos : List (List Nat)) (n : Nat)
    (base : List Nat) (a b : Nat) (ha : a < n)
    (hj : joined terms pos a b = true) :
    depthOf terms pos n base a ≤ depthOf terms pos n base b + 1 := by
  cases Nat.lt_or_ge (depthOf terms pos n base b) n with
  | inl hlt =>
    have hPb : reachB terms pos n base (depthOf terms pos n base b) b = true :=
      firstAt_stop (fun k => reachB terms pos n base k b = true) n 0
        (by rw [Nat.zero_add]; exact hlt)
    have hPa := reach_step terms pos n base _ a b ha hj hPb
    cases Nat.lt_or_ge (depthOf terms pos n base b + 1)
        (depthOf terms pos n base a) with
    | inl h =>
      exact absurd hPa
        (firstAt_below (fun k => reachB terms pos n base k a = true) n 0 _
          (Nat.zero_le _) h)
    | inr h => exact h
  | inr hge =>
    exact Nat.le_trans
      (Nat.le_trans (firstAt_le (fun k => reachB terms pos n base k a = true) n 0)
        (by rw [Nat.zero_add]; exact hge))
      (Nat.le_succ _)

/-- At symmetric square terms the position join reads one value at
the exchanged keys, both keys within the order. -/
private theorem joinedAt_symm (terms : List Mat) (o : Nat)
    (hT : ∀ T, T ∈ terms → sqAt T o ∧ matOneValue (transposeM T) T)
    (i j : Nat) (hi : i < o) (hj : j < o) :
    joinedAt terms i j = joinedAt terms j i := by
  have key : ∀ T, T ∈ terms →
      (!decide ((getAt BPair.unit (getAt [] T i) j).oneValue BPair.unit))
        = !decide ((getAt BPair.unit (getAt [] T j) i).oneValue BPair.unit) := by
    intro T hTm
    have hS := symEntry o T (rowsLen_of_sqAt (hT T hTm).1)
      (sqAt_len (hT T hTm).1) (hT T hTm).2 i j hi hj
    cases hd : decide ((getAt BPair.unit (getAt [] T j) i).oneValue BPair.unit) with
    | true =>
      rw [decide_eq_true (BPair.oneValue_trans (BPair.oneValue_symm hS)
        (of_decide_eq_true hd))]
    | false =>
      cases hd' : decide ((getAt BPair.unit (getAt [] T i) j).oneValue
          BPair.unit) with
      | true =>
        exact absurd (decide_eq_true (BPair.oneValue_trans hS
          (of_decide_eq_true hd'))) (by rw [hd]; exact Bool.noConfusion)
      | false => rfl
  cases h1 : joinedAt terms i j with
  | true =>
    obtain ⟨T, hTm, hTv⟩ := mem_of_any _ _ h1
    rw [key T hTm] at hTv
    exact (any_of_mem _ hTm hTv).symm
  | false =>
    cases h2 : joinedAt terms j i with
    | true =>
      obtain ⟨T, hTm, hTv⟩ := mem_of_any _ _ h2
      rw [← key T hTm] at hTv
      exact absurd (any_of_mem (fun T => !decide
        ((getAt BPair.unit (getAt [] T i) j).oneValue BPair.unit)) hTm hTv)
        (by show ¬ joinedAt terms i j = true; rw [h1]; exact Bool.noConfusion)
    | false => rfl

/-- The member join reads one value at the exchanged members, at
symmetric square terms and positions within the order. -/
theorem joined_symm (terms : List Mat) (pos : List (List Nat)) (o : Nat)
    (hT : ∀ T, T ∈ terms → sqAt T o ∧ matOneValue (transposeM T) T)
    (hpos : ∀ s ∈ pos, ∀ i ∈ s, i < o) (a b : Nat) :
    joined terms pos a b = joined terms pos b a := by
  have key : ∀ i j, i ∈ getAt [] pos a → j ∈ getAt [] pos b →
      joinedAt terms i j = joinedAt terms j i :=
    fun i j hi hj => joinedAt_symm terms o hT i j (pos_lt pos o hpos a i hi)
      (pos_lt pos o hpos b j hj)
  cases h1 : joined terms pos a b with
  | true =>
    obtain ⟨i, hi, hiv⟩ := mem_of_any _ _ h1
    obtain ⟨j, hj, hjv⟩ := mem_of_any _ _ hiv
    rw [key i j hi hj] at hjv
    exact (any_of_mem _ hj (any_of_mem _ hi hjv)).symm
  | false =>
    cases h2 : joined terms pos b a with
    | true =>
      obtain ⟨j, hj, hjv⟩ := mem_of_any _ _ h2
      obtain ⟨i, hi, hiv⟩ := mem_of_any _ _ hjv
      rw [← key i j hi hj] at hiv
      exact absurd (any_of_mem (fun i => (getAt [] pos b).any (fun j =>
        joinedAt terms i j)) hi (any_of_mem _ hj hiv))
        (by show ¬ joined terms pos a b = true; rw [h1]; exact Bool.noConfusion)
    | false => rfl

/-- A shell's members sit at its depth, below the count. -/
private theorem mem_shell (terms : List Mat) (pos : List (List Nat))
    (n : Nat) (base : List Nat) (d a : Nat)
    (h : a ∈ shell terms pos n base d) :
    a < n ∧ depthOf terms pos n base a = d := by
  obtain ⟨hr, hd⟩ := mem_filter_of _ _ a h
  exact ⟨ltOfMemRange hr, beqEqOf hd⟩

/-- A member below the count sits in its depth's shell. -/
private theorem shell_of_depth (terms : List Mat) (pos : List (List Nat))
    (n : Nat) (base : List Nat) (a : Nat) (ha : a < n) :
    a ∈ shell terms pos n base (depthOf terms pos n base a) :=
  mem_filter_to _ (memRange ha) (eqBeqOf rfl)

/-- The shells' walk from a depth lists each member's shell at the
depth's successors: a member of the `p`-th listed shell sits at
depth `d + p`, below the count. -/
private theorem shellsGo_depth (terms : List Mat) (pos : List (List Nat))
    (n : Nat) (base : List Nat) :
    ∀ (fuel d p a : Nat),
      a ∈ getAt [] (shellsGo terms pos n base d fuel) p →
      a < n ∧ depthOf terms pos n base a = d + p
  | 0, _, _, _, h => nomatch h
  | fuel + 1, d, p, a, h => by
    revert h
    show a ∈ getAt [] (match shell terms pos n base d with
      | [] => []
      | a :: s => (a :: s) :: shellsGo terms pos n base (d + 1) fuel) p →
        a < n ∧ depthOf terms pos n base a = d + p
    cases hs : shell terms pos n base d with
    | nil => exact fun h => nomatch h
    | cons x s =>
      match p with
      | 0 =>
        intro h
        have h' : a ∈ shell terms pos n base d := by rw [hs]; exact h
        exact mem_shell terms pos n base d a h'
      | p + 1 =>
        intro h
        obtain ⟨h1, h2⟩ := shellsGo_depth terms pos n base fuel (d + 1) p a h
        exact ⟨h1, by rw [h2, Nat.add_right_comm, Nat.add_assoc]⟩

/-- The shells' walk lists occupied shells alone. -/
private theorem shellsGo_pos (terms : List Mat) (pos : List (List Nat))
    (n : Nat) (base : List Nat) :
    ∀ (fuel d : Nat) (s : List Nat), s ∈ shellsGo terms pos n base d fuel →
      0 < s.length
  | 0, _, _, h => nomatch h
  | fuel + 1, d, s, h => by
    revert h
    show s ∈ (match shell terms pos n base d with
      | [] => []
      | a :: s => (a :: s) :: shellsGo terms pos n base (d + 1) fuel) →
        0 < s.length
    cases shell terms pos n base d with
    | nil => exact fun h => nomatch h
    | cons x t =>
      intro h
      cases h with
      | head => exact Nat.succ_pos _
      | tail _ h' => exact shellsGo_pos terms pos n base fuel (d + 1) s h'

/-- The shells' walk lists every occupied shell at its own position
where the shells below it are occupied. -/
private theorem shellsGo_get (terms : List Mat) (pos : List (List Nat))
    (n : Nat) (base : List Nat) :
    ∀ (fuel d p : Nat), p < fuel →
      (∀ e, e ≤ p → 0 < (shell terms pos n base (d + e)).length) →
      getAt [] (shellsGo terms pos n base d fuel) p
        = shell terms pos n base (d + p)
  | 0, _, p, hp, _ => absurd hp (Nat.not_lt_zero p)
  | fuel + 1, d, p, hp, hocc => by
    show getAt [] (match shell terms pos n base d with
      | [] => []
      | a :: s => (a :: s) :: shellsGo terms pos n base (d + 1) fuel) p
      = shell terms pos n base (d + p)
    cases hs : shell terms pos n base d with
    | nil =>
      have h0 := hocc 0 (Nat.zero_le p)
      rw [Nat.add_zero, hs] at h0
      exact absurd h0 (Nat.lt_irrefl 0)
    | cons x s =>
      match p, hp, hocc with
      | 0, _, _ => exact hs.symm
      | p + 1, hp, hocc =>
        show getAt [] (shellsGo terms pos n base (d + 1) fuel) p
          = shell terms pos n base (d + (p + 1))
        rw [shellsGo_get terms pos n base fuel (d + 1) p
          (Nat.lt_of_succ_lt_succ hp)
          (fun e he => by
            rw [Nat.add_right_comm]
            exact hocc (e + 1) (Nat.succ_le_succ he)),
          Nat.add_right_comm, Nat.add_assoc]

/-! The walk closes within the member count: the reach at a positive
count is a distinct list of members below the count, it grows by a
member per count while a count adds a member, and once a count adds
no member every further reach is the closed one, so every reached
member's depth sits below the count (`depth_lt`); and a member first
reached at a count is joined to a member first reached at the count
before, so the occupied depths are consecutive from the base's
(`shell_contiguous`) and every reached member sits in a listed shell
(`mem_shells`). -/

/-- The reach at a positive count is a filter of the range: its
members sit below the count, each once. -/
private theorem reach_range (terms : List Mat) (pos : List (List Nat))
    (n : Nat) (base : List Nat) (k a : Nat) :
    countOf a (reach terms pos n base (k + 1)) ≤ 1
      ∧ (a ∈ reach terms pos n base (k + 1) → a < n) := by
  refine ⟨?_, fun h => ltOfMemRange (mem_filter_of _ _ a h).1⟩
  show countOf a ((List.range n).filter _) ≤ 1
  rw [countOf_filter, countOf_range]
  cases (containsB (reach terms pos n base k) a
      || (reach terms pos n base k).any (fun b => joined terms pos a b)) with
  | true =>
    cases Nat.decLt a n with
    | isTrue h => rw [if_pos rfl, if_pos h]; exact Nat.le_refl 1
    | isFalse h => rw [if_pos rfl, if_neg h]; exact Nat.zero_le 1
  | false => rw [if_neg Bool.noConfusion]; exact Nat.zero_le 1

/-- A reached member below the count stays reached at the next
count. -/
private theorem reach_mono (terms : List Mat) (pos : List (List Nat))
    (n : Nat) (base : List Nat) (k a : Nat) (ha : a < n)
    (h : a ∈ reach terms pos n base k) :
    a ∈ reach terms pos n base (k + 1) := by
  refine mem_filter_to _ (memRange ha) ?_
  show (containsB (reach terms pos n base k) a
    || (reach terms pos n base k).any (fun b => joined terms pos a b)) = true
  have hc : containsB (reach terms pos n base k) a = true :=
    decide_eq_true (countOf_pos_of_mem h)
  rw [hc]
  rfl

/-- A member reached at a count, off the count before, is joined to
a member reached at the count before. -/
private theorem reach_new (terms : List Mat) (pos : List (List Nat))
    (n : Nat) (base : List Nat) (k a : Nat)
    (h : a ∈ reach terms pos n base (k + 1))
    (hno : ¬ a ∈ reach terms pos n base k) :
    ∃ b, b ∈ reach terms pos n base k ∧ joined terms pos a b = true := by
  have hp := (mem_filter_of _ _ a h).2
  cases hc : containsB (reach terms pos n base k) a with
  | true =>
    exact absurd (mem_of_countOf_pos a _ (of_decide_eq_true hc)) hno
  | false =>
    rw [hc, Bool.false_or] at hp
    exact mem_of_any _ _ hp

/-- Two reaches at one member set read one further reach: the next
count's filter reads its predicate at the members alone. -/
private theorem reach_congr (terms : List Mat) (pos : List (List Nat))
    (n : Nat) (base : List Nat) (k k' : Nat)
    (h : ∀ a, a ∈ reach terms pos n base k ↔ a ∈ reach terms pos n base k') :
    reach terms pos n base (k + 1) = reach terms pos n base (k' + 1) := by
  show (List.range n).filter _ = (List.range n).filter _
  refine filter_congr _ _ (fun a => ?_) _
  have hc : containsB (reach terms pos n base k) a
      = containsB (reach terms pos n base k') a := by
    cases hx : containsB (reach terms pos n base k') a with
    | true =>
      exact decide_eq_true (countOf_pos_of_mem
        ((h a).mpr (mem_of_countOf_pos a _ (of_decide_eq_true hx))))
    | false =>
      cases hy : containsB (reach terms pos n base k) a with
      | true =>
        exact absurd (decide_eq_true (countOf_pos_of_mem
          ((h a).mp (mem_of_countOf_pos a _ (of_decide_eq_true hy)))))
          (by show ¬ containsB (reach terms pos n base k') a = true
              rw [hx]; exact Bool.noConfusion)
      | false => rfl
  have hany : (reach terms pos n base k).any (fun b => joined terms pos a b)
      = (reach terms pos n base k').any (fun b => joined terms pos a b) := by
    cases hx : (reach terms pos n base k').any (fun b => joined terms pos a b) with
    | true =>
      obtain ⟨b, hb, hbv⟩ := mem_of_any _ _ hx
      exact any_of_mem _ ((h b).mpr hb) hbv
    | false =>
      cases hy : (reach terms pos n base k).any (fun b => joined terms pos a b) with
      | true =>
        obtain ⟨b, hb, hbv⟩ := mem_of_any _ _ hy
        exact absurd (any_of_mem _ ((h b).mp hb) hbv)
          (by show ¬ (reach terms pos n base k').any (fun b => joined terms pos a b) = true
              rw [hx]; exact Bool.noConfusion)
      | false => rfl
  rw [hc, hany]

/-- The closed read at a count: the next count adds no member. -/
private def closedB (terms : List Mat) (pos : List (List Nat)) (n : Nat)
    (base : List Nat) (k : Nat) : Bool :=
  (reach terms pos n base (k + 1)).all (fun a =>
    containsB (reach terms pos n base k) a)

/-- A closed count stays closed: every further reach is the count's
own, the members below the count. -/
private theorem reach_closed (terms : List Mat) (pos : List (List Nat))
    (n : Nat) (base : List Nat) (k : Nat)
    (hbase : ∀ a, a ∈ base → a < n)
    (h : closedB terms pos n base k = true) :
    ∀ j, reach terms pos n base (k + 1 + j) = reach terms pos n base (k + 1)
  | 0 => rfl
  | j + 1 => by
    have hIH := reach_closed terms pos n base k hbase h j
    have hlt : ∀ a, a ∈ reach terms pos n base k → a < n := by
      intro a ha
      cases k with
      | zero => exact hbase a ha
      | succ k' => exact (reach_range terms pos n base k' a).2 ha
    show reach terms pos n base (k + 1 + j + 1) = reach terms pos n base (k + 1)
    rw [reach_congr terms pos n base (k + 1 + j) k (fun a => by
      rw [hIH]
      exact ⟨fun ha => mem_of_countOf_pos a _
          (of_decide_eq_true (all_of_mem _ _ h a ha)),
        fun ha => reach_mono terms pos n base k a (hlt a ha) ha⟩)]

/-- A list whose every-read fails holds a member failing the read. -/
private theorem exists_of_all_false {α : Type} (f : α → Bool) :
    ∀ l : List α, l.all f = false → ∃ x, x ∈ l ∧ f x = false
  | [], h => Bool.noConfusion h
  | z :: t, h => by
    cases hz : f z with
    | false => exact ⟨z, List.Mem.head _, hz⟩
    | true =>
      have ht : t.all f = false := by
        have h' : (f z && t.all f) = false := h
        rw [hz, Bool.true_and] at h'
        exact h'
      obtain ⟨x, hx, hxv⟩ := exists_of_all_false f t ht
      exact ⟨x, List.Mem.tail _ hx, hxv⟩

/-- At an open count the reach grows by at least one member. -/
private theorem reach_grow (terms : List Mat) (pos : List (List Nat))
    (n : Nat) (base : List Nat) (k : Nat)
    (hbase : ∀ a, a ∈ base → a < n) (hdist : distinctList base)
    (h : closedB terms pos n base k = false) :
    (reach terms pos n base k).length + 1
      ≤ (reach terms pos n base (k + 1)).length := by
  have hlt : ∀ a, a ∈ reach terms pos n base k → a < n := by
    intro a ha
    cases k with
    | zero => exact hbase a ha
    | succ k' => exact (reach_range terms pos n base k' a).2 ha
  have hdk : ∀ a, countOf a (reach terms pos n base k) ≤ 1 := by
    intro a
    cases k with
    | zero => exact distinctList_all hdist a
    | succ k' => exact (reach_range terms pos n base k' a).1
  -- a member of the next count off the count's reach
  have hex : ∃ x, x ∈ reach terms pos n base (k + 1)
      ∧ ¬ x ∈ reach terms pos n base k := by
    cases hall : (reach terms pos n base (k + 1)).all (fun a =>
        containsB (reach terms pos n base k) a) with
    | true => exact Bool.noConfusion (h.symm.trans hall)
    | false =>
      obtain ⟨x, hx, hxv⟩ := exists_of_all_false _ _ hall
      exact ⟨x, hx, fun hm =>
        Bool.noConfusion (hxv.symm.trans (decide_eq_true (countOf_pos_of_mem hm)))⟩
  obtain ⟨x, hx, hxno⟩ := hex
  have hxc : countOf x (reach terms pos n base k) = 0 := by
    cases Nat.eq_zero_or_pos (countOf x (reach terms pos n base k)) with
    | inl h0 => exact h0
    | inr hp => exact absurd (mem_of_countOf_pos x _ hp) hxno
  show (x :: reach terms pos n base k).length
    ≤ (reach terms pos n base (k + 1)).length
  refine length_le_of_distinct_mem (x :: reach terms pos n base k)
    (reach terms pos n base (k + 1)) ?_ ?_ ?_
  · intro y
    rw [countOf_cons]
    cases Nat.decEq y x with
    | isTrue hyx =>
      rw [if_pos hyx, hyx, hxc]
      exact Nat.le_refl 1
    | isFalse hyx =>
      rw [if_neg hyx, Nat.zero_add]
      exact hdk y
  · intro y hy
    cases hy with
    | head => exact hx
    | tail _ hy' => exact reach_mono terms pos n base k y (hlt y hy') hy'
  · intro y _
    exact (reach_range terms pos n base k y).1

/-- The reach at a count holds at most the member count. -/
private theorem reach_len (terms : List Mat) (pos : List (List Nat))
    (n : Nat) (base : List Nat) (k : Nat)
    (hbase : ∀ a, a ∈ base → a < n) (hdist : distinctList base) :
    (reach terms pos n base k).length ≤ n := by
  cases k with
  | zero =>
    exact length_le_of_distinct base n (distinctList_all hdist)
      (fun a ha => hbase a (mem_of_countOf_pos a _ ha))
  | succ k' =>
    exact length_le_of_distinct _ n
      (fun a => (reach_range terms pos n base k' a).1)
      (fun a ha => (reach_range terms pos n base k' a).2
        (mem_of_countOf_pos a _ ha))

/-- While every count below a stated one is open, the reach at that
count holds one member beyond the count, at an occupied base. -/
private theorem reach_open_len (terms : List Mat) (pos : List (List Nat))
    (n : Nat) (base : List Nat)
    (hbase : ∀ a, a ∈ base → a < n) (hdist : distinctList base)
    (hocc : 0 < base.length) :
    ∀ K, (∀ c, c < K → closedB terms pos n base c = false) →
      K + 1 ≤ (reach terms pos n base K).length
  | 0, _ => hocc
  | K + 1, hopen => by
    have hIH := reach_open_len terms pos n base hbase hdist hocc K
      (fun c hc => hopen c (Nat.lt_succ_of_lt hc))
    exact Nat.le_trans (Nat.succ_le_succ hIH)
      (reach_grow terms pos n base K hbase hdist (hopen K (Nat.lt_succ_self K)))

/-- The first closed count below the member count. -/
private def closedAt (terms : List Mat) (pos : List (List Nat)) (n : Nat)
    (base : List Nat) : Nat :=
  firstAt (fun k => closedB terms pos n base k = true) 0 n

/-- Every reached member is reached at the first closed count, which
sits below the member count. -/
private theorem reach_at_closed (terms : List Mat) (pos : List (List Nat))
    (n : Nat) (base : List Nat)
    (hbase : ∀ a, a ∈ base → a < n) (hdist : distinctList base)
    (hocc : 0 < base.length) :
    closedAt terms pos n base < n
      ∧ ∀ m a, a ∈ reach terms pos n base m →
        a ∈ reach terms pos n base (closedAt terms pos n base) := by
  have hlt : closedAt terms pos n base < n := by
    cases Nat.lt_or_ge (closedAt terms pos n base) n with
    | inl h => exact h
    | inr hge =>
      have hopen : ∀ c, c < n → closedB terms pos n base c = false := by
        intro c hc
        cases hcl : closedB terms pos n base c with
        | true =>
          exact absurd hcl (firstAt_below (fun k => closedB terms pos n base k = true)
            n 0 c (Nat.zero_le c) (Nat.lt_of_lt_of_le hc hge))
        | false => rfl
      have h1 := reach_open_len terms pos n base hbase hdist hocc n hopen
      have h2 := reach_len terms pos n base n hbase hdist
      exact absurd (Nat.le_trans h1 h2) (Nat.not_succ_le_self n)
  refine ⟨hlt, fun m a ha => ?_⟩
  have hcl : closedB terms pos n base (closedAt terms pos n base) = true :=
    firstAt_stop (fun k => closedB terms pos n base k = true) n 0
      (by rw [Nat.zero_add]; exact hlt)
  have hltm : ∀ a, a ∈ reach terms pos n base m → a < n := by
    intro a ha
    cases m with
    | zero => exact hbase a ha
    | succ m' => exact (reach_range terms pos n base m' a).2 ha
  cases Nat.lt_or_ge m (closedAt terms pos n base + 1) with
  | inl hm =>
    -- reached before the closed count: the reach grows to it
    have hup : ∀ j, a ∈ reach terms pos n base (m + j) := by
      intro j
      induction j with
      | zero => exact ha
      | succ j ih =>
        exact reach_mono terms pos n base (m + j) a (hltm a ha) ih
    have := hup (closedAt terms pos n base - m)
    rw [natAddSubCancel (Nat.le_of_lt_succ hm)] at this
    exact this
  | inr hm =>
    have hm' := natAddSubCancel hm
    have hcls := reach_closed terms pos n base _ hbase hcl
      (m - (closedAt terms pos n base + 1))
    rw [hm'] at hcls
    rw [hcls] at ha
    exact mem_of_countOf_pos a _ (of_decide_eq_true (all_of_mem _ _ hcl a ha))

/-- Every reached member's depth sits below the member count, at an
occupied distinct base within the count: the walk closes within the
count. -/
theorem depth_lt (terms : List Mat) (pos : List (List Nat)) (n : Nat)
    (base : List Nat)
    (hbase : ∀ a, a ∈ base → a < n) (hdist : distinctList base)
    (hocc : 0 < base.length) (m a : Nat)
    (ha : reachB terms pos n base m a = true) :
    depthOf terms pos n base a < n := by
  obtain ⟨hlt, hall⟩ := reach_at_closed terms pos n base hbase hdist hocc
  have hc : reachB terms pos n base (closedAt terms pos n base) a = true :=
    decide_eq_true (countOf_pos_of_mem
      (hall m a (mem_of_countOf_pos a _ (of_decide_eq_true ha))))
  cases Nat.lt_or_ge (closedAt terms pos n base) (depthOf terms pos n base a) with
  | inl h =>
    exact absurd hc (firstAt_below (fun k => reachB terms pos n base k a = true)
      n 0 _ (Nat.zero_le _) h)
  | inr h => exact Nat.lt_of_le_of_lt h hlt

/-- A member at a depth beyond the base's is joined to a member at
the depth before: the occupied depths are consecutive. -/
theorem shell_contiguous (terms : List Mat) (pos : List (List Nat))
    (n : Nat) (base : List Nat) (hbase : ∀ a, a ∈ base → a < n)
    (d a : Nat) (hdn : d + 1 < n) (ha : a ∈ shell terms pos n base (d + 1)) :
    0 < (shell terms pos n base d).length := by
  obtain ⟨han, hda⟩ := mem_shell terms pos n base (d + 1) a ha
  have hr : a ∈ reach terms pos n base (d + 1) := by
    have hs : reachB terms pos n base (depthOf terms pos n base a) a = true :=
      firstAt_stop (fun k => reachB terms pos n base k a = true) n 0
        (by rw [Nat.zero_add]; show depthOf terms pos n base a < n
            rw [hda]; exact hdn)
    rw [hda] at hs
    exact mem_of_countOf_pos a _ (of_decide_eq_true hs)
  have hno : ¬ a ∈ reach terms pos n base d := by
    intro hm
    have hb : reachB terms pos n base d a = true :=
      decide_eq_true (countOf_pos_of_mem hm)
    exact absurd hb (firstAt_below (fun k => reachB terms pos n base k a = true)
      n 0 d (Nat.zero_le d) (by show d < depthOf terms pos n base a
                                rw [hda]; exact Nat.lt_succ_self d))
  obtain ⟨b, hb, hjb⟩ := reach_new terms pos n base d a hr hno
  have hbn : b < n := by
    cases d with
    | zero => exact hbase b hb
    | succ d' => exact (reach_range terms pos n base d' b).2 hb
  have hdb_le : depthOf terms pos n base b ≤ d := by
    cases Nat.lt_or_ge d (depthOf terms pos n base b) with
    | inl h =>
      exact absurd (decide_eq_true (countOf_pos_of_mem hb))
        (firstAt_below (fun k => reachB terms pos n base k b = true) n 0 d
          (Nat.zero_le d) h)
    | inr h => exact h
  have hdb : depthOf terms pos n base b = d := by
    cases Nat.lt_or_ge (depthOf terms pos n base b) d with
    | inl hlt =>
      have hbr : reachB terms pos n base (depthOf terms pos n base b) b = true :=
        firstAt_stop (fun k => reachB terms pos n base k b = true) n 0
          (by rw [Nat.zero_add]
              exact Nat.lt_trans hlt (Nat.lt_trans (Nat.lt_succ_self d) hdn))
      have hup : ∀ j, b ∈ reach terms pos n base (depthOf terms pos n base b + j) := by
        intro j
        induction j with
        | zero => exact mem_of_countOf_pos b _ (of_decide_eq_true hbr)
        | succ j ih => exact reach_mono terms pos n base _ b hbn ih
      have h1d : 1 ≤ d := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt)
      have hbd := hup (d - 1 - depthOf terms pos n base b)
      rw [natAddSubCancel (Nat.le_sub_one_of_lt hlt)] at hbd
      have hstep := reach_step terms pos n base (d - 1) a b han hjb
        (decide_eq_true (countOf_pos_of_mem hbd))
      rw [subAdd h1d] at hstep
      exact absurd (mem_of_countOf_pos a _ (of_decide_eq_true hstep)) hno
    | inr h => exact Nat.le_antisymm hdb_le h
  have hbs : b ∈ shell terms pos n base d := by
    rw [← hdb]
    exact shell_of_depth terms pos n base b hbn
  exact Nat.lt_of_lt_of_le (countOf_pos_of_mem hbs) (countOf_le_length b _)

/-- Every shell below a member's depth is occupied, at a depth below
the count: the contiguity descended from the member's own shell. -/
private theorem shells_below (terms : List Mat) (pos : List (List Nat))
    (n : Nat) (base : List Nat) (hbase : ∀ a, a ∈ base → a < n) :
    ∀ (D a : Nat), a < n → depthOf terms pos n base a = D → D < n →
      ∀ e, e ≤ D → 0 < (shell terms pos n base e).length
  | 0, a, ha, hD, _, e, he => by
    have hsh : shell terms pos n base e
        = shell terms pos n base (depthOf terms pos n base a) := by
      rw [Nat.eq_zero_of_le_zero he, hD]
    rw [hsh]
    exact Nat.lt_of_lt_of_le
      (countOf_pos_of_mem (shell_of_depth terms pos n base a ha))
      (countOf_le_length a _)
  | D + 1, a, ha, hD, hDn, e, he => by
    have haD : a ∈ shell terms pos n base (D + 1) := by
      rw [← hD]; exact shell_of_depth terms pos n base a ha
    have hprev := shell_contiguous terms pos n base hbase D a hDn haD
    obtain ⟨b, hb⟩ : ∃ b, b ∈ shell terms pos n base D := by
      cases hs : shell terms pos n base D with
      | nil => rw [hs] at hprev; exact absurd hprev (Nat.lt_irrefl 0)
      | cons b _ => exact ⟨b, List.Mem.head _⟩
    obtain ⟨hbn, hdb⟩ := mem_shell terms pos n base D b hb
    cases Nat.lt_or_ge e (D + 1) with
    | inl hlt =>
      exact shells_below terms pos n base hbase D b hbn hdb
        (Nat.lt_of_succ_lt hDn) e (Nat.le_of_lt_succ hlt)
    | inr hge =>
      have hsh : shell terms pos n base e
          = shell terms pos n base (depthOf terms pos n base a) := by
        rw [Nat.le_antisymm he hge, hD]
      rw [hsh]
      exact Nat.lt_of_lt_of_le
        (countOf_pos_of_mem (shell_of_depth terms pos n base a ha))
        (countOf_le_length a _)

/-- Every reached member below the count sits in a listed shell, its
own depth's: the occupied depths are consecutive from the base's and
every depth sits below the count. -/
theorem mem_shells (terms : List Mat) (pos : List (List Nat)) (n : Nat)
    (base : List Nat)
    (hbase : ∀ a, a ∈ base → a < n) (hdist : distinctList base)
    (hocc : 0 < base.length) (m a : Nat) (ha : a < n)
    (hr : reachB terms pos n base m a = true) :
    a ∈ getAt [] (shells terms pos n base) (depthOf terms pos n base a) := by
  have hlt := depth_lt terms pos n base hbase hdist hocc m a hr
  show a ∈ getAt [] (shellsGo terms pos n base 0 n) (depthOf terms pos n base a)
  rw [shellsGo_get terms pos n base n 0 _ hlt (fun e he => by
    rw [Nat.zero_add]
    exact shells_below terms pos n base hbase _ a ha rfl hlt e he), Nat.zero_add]
  exact shell_of_depth terms pos n base a ha

/-! The slab data along a shell list and their assembly. -/

/-- The slab data along a shell list of occupied shells are at
`lem:greenprod`'s slab shape, the orders the shells' counts. -/
theorem slabs_shape (M : Mat) : ∀ sh : List (List Nat), 0 < sh.length →
    (∀ s, s ∈ sh → 0 < s.length) →
    greenprod.slabShape (slabDiag M sh) (slabOff M sh) (sh.map List.length)
  | [], h, _ => absurd h (Nat.lt_irrefl 0)
  | [s], _, hp =>
    ⟨hp s (List.Mem.head _), sqAt_of (length_selM s s M) (rowsLen_selM s M s)⟩
  | s :: s' :: t, _, hp =>
    ⟨hp s (List.Mem.head _),
     sqAt_of (length_selM s s M) (rowsLen_selM s M s),
     rectAt_of (length_selM s s' M) (rowsLen_selM s' M s),
     slabs_shape M (s' :: t) (Nat.succ_pos _)
       (fun x hx => hp x (List.Mem.tail _ hx))⟩

/-- A mapped list of unit reads reads one value with the unit list
at its count. -/
private theorem units_oneValue (f : Nat → BPair) : ∀ l : List Nat,
    (∀ x, x ∈ l → (f x).oneValue BPair.unit) →
    poly.oneValue (l.map f) (List.replicate l.length BPair.unit)
  | [], _ => trivial
  | x :: t, h =>
    ⟨h x (List.Mem.head _),
     units_oneValue f t (fun y hy => h y (List.Mem.tail _ hy))⟩

/-- The coupling block against the joined tail reads the padded
bond: the neighbor shell's block with the further shells' entries at
the sum's unit. -/
private theorem coupling_pad (M : Mat) (s s' : List Nat)
    (t : List (List Nat))
    (hoff : (s.all (fun i => (t.flatMap (fun s => s)).all (fun j =>
      decide ((getAt BPair.unit (getAt [] M i) j).oneValue
        BPair.unit)))) = true) :
    matOneValue (selM s (s' ++ t.flatMap (fun s => s)) M)
      (greenprod.offPad (s'.length + (t.flatMap (fun s => s)).length)
        (selM s s' M)) := by
  refine matOne_getAt _ _ ?_ ?_
  · rw [length_selM, greenprod.offPad_len, length_selM]
  · intro p hp
    rw [length_selM] at hp
    have hkey : getAt 0 s p ∈ s := mem_getAt 0 s p hp
    have hrow : ∀ (J : List Nat), getAt [] (selM s J M) p
        = J.map (fun j => getAt BPair.unit (getAt [] M (getAt 0 s p)) j) :=
      fun J => ground.getAt_map 0 [] _ s p hp
    rw [greenprod.offPad_getAt _ _ p (by rw [length_selM]; exact hp),
      hrow, hrow]
    show poly.oneValue
      ((s' ++ t.flatMap (fun s => s)).map
        (fun j => getAt BPair.unit (getAt [] M (getAt 0 s p)) j))
      ((s'.map (fun j => getAt BPair.unit (getAt [] M (getAt 0 s p)) j))
        ++ List.replicate ((s'.length + (t.flatMap (fun s => s)).length)
          - (s'.map (fun j => getAt BPair.unit (getAt [] M (getAt 0 s p)) j)).length)
          BPair.unit)
    rw [map_append, length_map, addSubSelfL]
    refine poly.oneValue_append _ _ _ _ rfl (poly.oneValue_refl _) ?_
    refine units_oneValue _ _ (fun j hj => ?_)
    exact of_decide_eq_true
      (all_of_mem _ _ (all_of_mem _ _ hoff _ hkey) j hj)

/-- The matrix along a shell list's joined keys is the assembled
block tridiagonal of its slab data, at a symmetric square matrix
whose entries between shells beyond neighbors sit at the sum's
unit: the shells' blocks the diagonal slabs and the consecutive
shells' selections the bonds (`lem:greenprod`'s split at
`greenprod.assemble`).  The shells occupied and their keys within
the order are the walk's own frame. -/
theorem chain_assemble (M : Mat) (o : Nat) (hM : sqAt M o)
    (hsym : matOneValue (transposeM M) M) :
    ∀ sh : List (List Nat), (∀ s, s ∈ sh → 0 < s.length) →
      (∀ s, s ∈ sh → ∀ i, i ∈ s → i < o) → offBandB M sh = true →
      matOneValue (selM (sh.flatMap (fun s => s)) (sh.flatMap (fun s => s)) M)
        (greenprod.assemble (slabDiag M sh) (slabOff M sh))
  | [], _, _, _ => trivial
  | [s], _, _, _ => by
    show matOneValue (selM (s ++ []) (s ++ []) M) (selM s s M)
    rw [append_nil]
    exact matOne_refl _
  | s :: s' :: t, hp, ho, hoff => by
    have hoffs := ground.andSplitB hoff
    have hpt : ∀ x, x ∈ s' :: t → 0 < x.length :=
      fun x hx => hp x (List.Mem.tail _ hx)
    have hot : ∀ x, x ∈ s' :: t → ∀ i, i ∈ x → i < o :=
      fun x hx => ho x (List.Mem.tail _ hx)
    have hIH := chain_assemble M o hM hsym (s' :: t) hpt hot hoffs.2
    have hshape := slabs_shape M (s' :: t) (Nat.succ_pos _) hpt
    have hlen : ((s' :: t).flatMap (fun s => s)).length
        = sumNat ((s' :: t).map List.length) := by
      rw [length_flatMap]
      show famFold Nat.add 0 (fun x => x.length) (s' :: t)
        = famFold Nat.add 0 (fun x => x) ((s' :: t).map List.length)
      rw [famFold_map]
    have hsqR : sqAt (greenprod.assemble (slabDiag M (s' :: t))
        (slabOff M (s' :: t))) ((s' :: t).flatMap (fun s => s)).length := by
      rw [hlen]
      exact greenprod.assemble_sq _ _ _ hshape
    have hs0 : 0 < s.length := hp s (List.Mem.head _)
    have hoffT : (s' :: t).flatMap (fun s => s) = s' ++ t.flatMap (fun s => s) :=
      rfl
    have hle : s'.length ≤ ((s' :: t).flatMap (fun s => s)).length := by
      rw [hoffT, length_append]
      exact Nat.le_add_right _ _
    have hcons := greenprod.assemble_cons (selM s s M) (selM s s' M)
      (slabDiag M (s' :: t)) (slabOff M (s' :: t)) s.length s'.length
      ((s' :: t).flatMap (fun s => s)).length (length_selM s s M) hs0
      (length_selM s s' M) (rowsLen_selM s' M s) hle (sqAt_len hsqR)
      (greenprod.sqAt_headD _ _ hsqR)
    have hidx : (s.all (fun i => Nat.blt i o)) = true :=
      all_of_mem_intro _ s (fun i hi => ltBlt (ho s (List.Mem.head _) i hi))
    have hcpl : (((s' :: t).flatMap (fun s => s)).all (fun j => Nat.blt j o))
        = true :=
      all_of_mem_intro _ _ (fun j hj => by
        obtain ⟨u, hu, hju⟩ := mem_flatMap_of _ _ j hj
        exact ltBlt (hot u hu j hju))
    have hsplit := inertia.selM_blockJoin M s ((s' :: t).flatMap (fun s => s)) o
      hM hsym hs0 hidx hcpl
    have hpad : matOneValue (selM s ((s' :: t).flatMap (fun s => s)) M)
        (greenprod.offPad ((s' :: t).flatMap (fun s => s)).length
          (selM s s' M)) := by
      rw [hoffT, length_append]
      exact coupling_pad M s s' t hoffs.1
    have hjoin := inertia.blockJoin_congr (selM s s M) (selM s s M)
      (selM s ((s' :: t).flatMap (fun s => s)) M)
      (greenprod.offPad ((s' :: t).flatMap (fun s => s)).length (selM s s' M))
      (selM ((s' :: t).flatMap (fun s => s)) ((s' :: t).flatMap (fun s => s)) M)
      (greenprod.assemble (slabDiag M (s' :: t)) (slabOff M (s' :: t)))
      (rowsLen_selM s M s) (rowsLen_selM s M s)
      (length_selM _ _ _) ((greenprod.offPad_len _ _).trans (length_selM _ _ _))
      (rowsLen_selM _ M s)
      (greenprod.offPad_rows _ _ _ (rowsLen_selM s' M s) hle)
      (matOne_refl _) hpad hIH
    show matOneValue
      (selM (s ++ (s' :: t).flatMap (fun s => s))
        (s ++ (s' :: t).flatMap (fun s => s)) M)
      (greenprod.assemble (selM s s M :: slabDiag M (s' :: t))
        (selM s s' M :: slabOff M (s' :: t)))
    rw [hcons]
    exact matOne_trans hsplit hjoin

/-- A position of a position shell is a position of one of the
shell's members. -/
private theorem mem_posShell (pos : List (List Nat)) (s : List Nat) (i : Nat)
    (h : i ∈ s.flatMap (fun a => getAt [] pos a)) :
    ∃ a, a ∈ s ∧ i ∈ getAt [] pos a :=
  mem_flatMap_of _ s i h

/-- The depth chain's position shells read off-band at a matrix
whose cross entries sit at the sum's unit off the joins: a position
of a member two or more depths beyond another's would join the two
members, against the joined step's depth move. -/
private theorem posShells_offBand (terms : List Mat) (pos : List (List Nat))
    (n : Nat) (base : List Nat) (o : Nat)
    (hT : ∀ T, T ∈ terms → sqAt T o ∧ matOneValue (transposeM T) T)
    (hpos : ∀ s ∈ pos, ∀ i ∈ s, i < o) (hn : n = pos.length)
    (M : Mat) (hcross : crossB terms pos M = true) :
    ∀ (fuel d : Nat), offBandB M ((shellsGo terms pos n base d fuel).map
      (fun s => s.flatMap (fun a => getAt [] pos a))) = true
  | 0, _ => rfl
  | fuel + 1, d => by
    show offBandB M ((match shell terms pos n base d with
      | [] => []
      | a :: s => (a :: s) :: shellsGo terms pos n base (d + 1) fuel).map
        (fun s : List Nat => s.flatMap (fun a => getAt [] pos a))) = true
    cases hs : shell terms pos n base d with
    | nil => rfl
    | cons x s =>
      cases hg : shellsGo terms pos n base (d + 1) fuel with
      | nil => rfl
      | cons s' t =>
        show (((x :: s).flatMap (fun a => getAt [] pos a)).all (fun i =>
            ((t.map (fun s : List Nat => s.flatMap (fun a => getAt [] pos a))).flatMap
              (fun s : List Nat => s)).all (fun j =>
            decide ((getAt BPair.unit (getAt [] M i) j).oneValue BPair.unit)))
          && offBandB M ((s' :: t).map
            (fun s : List Nat => s.flatMap (fun a => getAt [] pos a)))) = true
        have hrest : offBandB M ((s' :: t).map
            (fun s => s.flatMap (fun a => getAt [] pos a))) = true := by
          rw [← hg]
          exact posShells_offBand terms pos n base o hT hpos hn M hcross fuel (d + 1)
        rw [hrest, Bool.and_true]
        refine all_of_mem_intro _ _ (fun i hi => all_of_mem_intro _ _ (fun j hj => ?_))
        obtain ⟨a, ha, hia⟩ := mem_posShell pos (x :: s) i hi
        have ha' : a ∈ shell terms pos n base d := by rw [hs]; exact ha
        obtain ⟨han, hda⟩ := mem_shell terms pos n base d a ha'
        obtain ⟨u, hu, hju⟩ := mem_flatMap_of _ _ j hj
        obtain ⟨sb, hsb, hu'⟩ := mem_map_of _ _ u hu
        obtain ⟨b, hb, hjb⟩ := mem_posShell pos sb j (by rw [hu']; exact hju)
        obtain ⟨p, hp, hsp⟩ := ground.getAt_of_mem [] hsb
        have hbt : b ∈ getAt [] (shellsGo terms pos n base (d + 1) fuel) (p + 1) := by
          rw [hg]; show b ∈ getAt [] t p; rw [hsp]; exact hb
        obtain ⟨hbn, hdb⟩ := shellsGo_depth terms pos n base fuel (d + 1) (p + 1) b hbt
        have hnj : joined terms pos a b = false := by
          cases hjoin : joined terms pos a b with
          | false => rfl
          | true =>
            have hjb' : joined terms pos b a = true := by
              rw [← joined_symm terms pos o hT hpos a b]; exact hjoin
            have hstep := depth_step terms pos n base b a hbn hjb'
            rw [hdb, hda] at hstep
            exact absurd hstep
              (Nat.not_le_of_gt (Nat.lt_add_of_pos_right (Nat.succ_pos p)))
        have hne : (a == b) = false := by
          cases hab : (a == b) with
          | false => rfl
          | true =>
            have := beqEqOf hab
            rw [this, hdb] at hda
            exact absurd hda (Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self d)
              (Nat.le_add_right (d + 1) (p + 1))))
        have hab := all_of_mem _ _ (all_of_mem _ _ hcross a
          (memRange (by rw [← hn]; exact han))) b
          (memRange (by rw [← hn]; exact hbn))
        rw [hne, hnj, Bool.false_or, Bool.false_or] at hab
        exact all_of_mem _ _ (all_of_mem _ _ hab i hia) j hjb

/-- The depth chain: at a symmetric square matrix whose cross
entries sit at the sum's unit off the members' joins, the matrix
along the depth order is the assembled block tridiagonal of the
position shells' slab data — the sector's pencil at the shells,
block tridiagonal over the depth with the shells its slabs. -/
theorem depth_assemble (terms : List Mat) (pos : List (List Nat))
    (n : Nat) (base : List Nat) (o : Nat)
    (hT : ∀ T, T ∈ terms → sqAt T o ∧ matOneValue (transposeM T) T)
    (hpos : ∀ s ∈ pos, ∀ i ∈ s, i < o)
    (hocc : ∀ a, a < pos.length → 0 < (getAt [] pos a).length)
    (hn : n = pos.length)
    (M : Mat) (hM : sqAt M o) (hsym : matOneValue (transposeM M) M)
    (hcross : crossB terms pos M = true) :
    matOneValue (selM (depthOrder terms pos n base)
        (depthOrder terms pos n base) M)
      (greenprod.assemble (slabDiag M (posShells terms pos n base))
        (slabOff M (posShells terms pos n base))) :=
  chain_assemble M o hM hsym (posShells terms pos n base)
    (fun s hs => by
      obtain ⟨sm, hsm, hsm'⟩ := mem_map_of _ _ s hs
      obtain ⟨a, ha⟩ : ∃ a, a ∈ sm := by
        have hp := shellsGo_pos terms pos n base n 0 sm hsm
        cases hsm2 : sm with
        | nil => rw [hsm2] at hp; exact absurd hp (Nat.lt_irrefl 0)
        | cons a _ => exact ⟨a, List.Mem.head _⟩
      obtain ⟨q, hq, hsq⟩ := ground.getAt_of_mem [] hsm
      have han := (shellsGo_depth terms pos n base n 0 q a
        (by show a ∈ getAt [] (shells terms pos n base) q
            rw [hsq]; exact ha)).1
      have hpa := hocc a (by rw [← hn]; exact han)
      obtain ⟨i, hi⟩ : ∃ i, i ∈ getAt [] pos a := by
        cases hpe : getAt [] pos a with
        | nil => rw [hpe] at hpa; exact absurd hpa (Nat.lt_irrefl 0)
        | cons i _ => exact ⟨i, List.Mem.head _⟩
      rw [← hsm']
      exact Nat.lt_of_lt_of_le
        (countOf_pos_of_mem (mem_flatMap_to _ ha hi)) (countOf_le_length i _))
    (fun s hs i hi => by
      obtain ⟨sm, _, hsm'⟩ := mem_map_of _ _ s hs
      rw [← hsm'] at hi
      obtain ⟨a, _, hia⟩ := mem_posShell pos sm i hi
      exact pos_lt pos o hpos a i hia)
    (posShells_offBand terms pos n base o hT hpos hn M hcross n 0)

/-- The terms' sum reads its cross entries at the sum's unit off the
joins: at two members not joined every term's entry between their
positions sits at the sum's unit, and the sum folds them. -/
theorem msum_cross (terms : List Mat) (pos : List (List Nat)) (o : Nat)
    (hT : ∀ T, T ∈ terms → sqAt T o)
    (hpos : ∀ s ∈ pos, ∀ i ∈ s, i < o) :
    crossB terms pos (msum o (getAt [] terms) (List.range terms.length)) = true := by
  refine all_of_mem_intro _ _ (fun a _ => all_of_mem_intro _ _ (fun b _ => ?_))
  cases hab : (a == b) with
  | true => rfl
  | false =>
  cases hj : joined terms pos a b with
  | true => rfl
  | false =>
    show (false || false || _) = true
    rw [Bool.false_or, Bool.false_or]
    refine all_of_mem_intro _ _ (fun i hi => all_of_mem_intro _ _ (fun j hjp => ?_))
    refine decide_eq_true ?_
    have hshape : ∀ k, k ∈ List.range terms.length →
        rowsLen o (getAt [] terms k) ∧ (getAt [] terms k).length = o := by
      intro k hk
      have hm := mem_getAt [] terms k (ltOfMemRange hk)
      exact ⟨rowsLen_of_sqAt (hT _ hm), sqAt_len (hT _ hm)⟩
    rw [entry_msum o (getAt [] terms) i j (pos_lt pos o hpos a i hi)
      (pos_lt pos o hpos b j hjp) _ hshape]
    refine foldB_null _ _ (fun k hk => ?_)
    have hkm := mem_getAt [] terms k (ltOfMemRange (mem_of_countOf_pos k _ hk))
    -- the term's entry: off the join at every term
    cases hd : decide ((getAt BPair.unit (getAt [] (getAt [] terms k) i) j).oneValue
        BPair.unit) with
    | true => exact of_decide_eq_true hd
    | false =>
      have hat : joinedAt terms i j = true :=
        any_of_mem _ hkm (by rw [hd]; rfl)
      exact absurd (any_of_mem (fun i => (getAt [] pos b).any (fun j =>
        joinedAt terms i j)) hi (any_of_mem _ hjp hat))
        (by show ¬ joined terms pos a b = true; rw [hj]; exact Bool.noConfusion)

/-- A matrix whose entries between distinct members' positions sit
at the sum's unit, the fibers' orthogonal sum, reads its cross
entries there off the joins outright. -/
theorem memberDiag_cross (terms : List Mat) (pos : List (List Nat)) (M : Mat)
    (hdiag : ((List.range pos.length).all (fun a =>
      (List.range pos.length).all (fun b =>
        (a == b) || (getAt [] pos a).all (fun i => (getAt [] pos b).all (fun j =>
          decide ((getAt BPair.unit (getAt [] M i) j).oneValue
            BPair.unit)))))) = true) :
    crossB terms pos M = true := by
  refine all_of_mem_intro _ _ (fun a ha => all_of_mem_intro _ _ (fun b hb => ?_))
  have hab := all_of_mem _ _ (all_of_mem _ _ hdiag a ha) b hb
  cases heq : (a == b) with
  | true => rfl
  | false =>
    rw [heq, Bool.false_or] at hab
    show (false || joined terms pos a b || _) = true
    rw [Bool.false_or, hab, Bool.or_true]

end depthchain
