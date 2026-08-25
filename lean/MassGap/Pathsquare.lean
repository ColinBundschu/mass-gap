import MassGap.Pieri
/-!
`lem:pathsquare` — the path count's square sum.  The path count
`pathCount` of a shape is the count of its descents to the unit
shape by one box removed at a time (`removals`, the covered shapes:
a column of length one dropped, or an occupied column shortened by
one), the recursion `pathGo` at the degree's own fuel, one at the
unit shape and the fold over the removals below, with the fuel's
stability and the recursion's two reads `pathCount_vac` and
`pathCount_step` its public reads.  The covers read the removals
backwards: `lem:pieri`'s row at a source is the list of shapes
covering it, and the mirror `row_removals` reads the row's
occupancy at a target as the target's removals' occupancy at the
source — the new column against the shortened head, each grown
column against its own raised key, the mismatched widths vacant on
both sides; a removal descends the degree by one at the source's
width (`degree_removals`).  The square sum `squareSum` is the
theorem: at `k ≤ d` over the shapes of `k` boxes at `d` letters,
`Σ pathCount² = k!` — on the free space of the shapes the cover
operator `U` and the removal operator `D` are transposes for the
shape pairing, the path count the level vector `U^k 1`'s
coefficient, `DU = UD + id` at the shapes of fewer than `d` rows
(two distinct shapes of one size share a cover exactly where they
share a removal, and a shape's covers exceed its removals by one),
and the telescope `D U^{j+1} 1 = (j+1) U^j 1` at every `j < d`
closes the pairing at the factorial.
-/

namespace pathsquare
open ground places
open units (removals removals_split)

/-- The path recursion at the degree's own fuel: one at the unit
shape, the fold over the removals below. -/
private def pathGo : Nat → Shape → Nat
  | 0, _ => 1
  | fuel + 1, s =>
    if degree s == 0 then 1
    else (removals s).foldl (fun acc t => acc + pathGo fuel t) 0

/-- The shape lattice's path count. -/
def pathCount (s : Shape) : Nat := pathGo (degree s) s


/-- A row member keeps the source's width: a target of a different
width reads the row at nought. -/
private theorem row_count_ne (t s : Shape)
    (h : ¬ s.length = t.length) :
    ground.countOf s (pieri.row t) = 0 := by
  match t with
  | [] => rfl
  | a :: t' =>
    have hne1 : ¬ s = (a + 1) :: t' := fun he =>
      h ((congrArg List.length he).trans rfl)
    rw [pieri.row_split a t' s,
      ground.countOf_head_ne hne1 ([] : List Shape)]
    show 0 + ground.famFold Nat.add 0
      (fun j => ground.countOf s
        (if 0 < ground.getAt 0 (a :: t') j then
          [units.moveDn j (a :: t')] else []))
      (List.range t'.length) = 0
    rw [Nat.zero_add]
    refine ground.famFold_zero _ ?_ (List.range t'.length)
    intro j
    by_cases hg : 0 < ground.getAt 0 (a :: t') j
    · rw [if_pos hg]
      have hne2 : ¬ s = units.moveDn j (a :: t') := fun he =>
        h (by rw [he, units.length_moveDn j (a :: t')])
      rw [ground.countOf_head_ne hne2 ([] : List Shape)]
      rfl
    · rw [if_neg hg]
      rfl

/-- A removal keeps the source's width: a source of a different
width reads the removals at nought. -/
private theorem removals_count_ne (t s : Shape)
    (h : ¬ t.length = s.length) :
    ground.countOf t (removals s) = 0 := by
  match s with
  | [] => rfl
  | b :: s' =>
    have hh : ground.countOf t
        (if 0 < b then [(b - 1) :: s'] else []) = 0 := by
      by_cases hb : 0 < b
      · rw [if_pos hb]
        have hne : ¬ t = (b - 1) :: s' := fun he =>
          h ((congrArg List.length he).trans rfl)
        rw [ground.countOf_head_ne hne ([] : List Shape)]
        rfl
      · rw [if_neg hb]
        rfl
    rw [removals_split b s' t, hh]
    rw [Nat.zero_add]
    refine ground.famFold_zero _ ?_ (List.range s'.length)
    intro j
    by_cases hg : 0 < ground.getAt 0 (b :: s') (j + 1)
    · rw [if_pos hg]
      have hne : ¬ t = units.moveUp j (b :: s') := fun he =>
        h (by rw [he, units.length_moveUp j (b :: s')])
      rw [ground.countOf_head_ne hne ([] : List Shape)]
      rfl
    · rw [if_neg hg]
      rfl

/-- The mirror: the row's occupancy at a target is the target's
removals' occupancy at the source — the new column against the
shortened head, each grown column against its own raised key, and
the mismatched widths vacant on both sides. -/
theorem row_removals (t s : Shape) :
    ground.countOf s (pieri.row t) = ground.countOf t (removals s) := by
  by_cases hlen : t.length = s.length
  · match t, s, hlen with
      | [], [], _ => rfl
      | [], _ :: _, hlen => exact Nat.noConfusion hlen
      | _ :: _, [], hlen => exact Nat.noConfusion hlen
      | a :: t', b :: s', hlen =>
        have hts : t'.length = s'.length := Nat.succ.inj hlen
        have hhead : ground.countOf (b :: s') [(a + 1) :: t']
            = ground.countOf (a :: t')
              (if 0 < b then [(b - 1) :: s'] else []) := by
          by_cases hb : 0 < b
          · rw [if_pos hb]
            by_cases he : (b :: s') = (a + 1) :: t'
            · have h2 : (a :: t') = (b - 1) :: s' := by
                rw [(List.cons.inj he).1, (List.cons.inj he).2]
                rfl
              rw [← he, ← h2, ground.countOf_head, ground.countOf_head]
              rfl
            · have hne : ¬ (a :: t') = (b - 1) :: s' := by
                intro h2
                refine he ?_
                rw [← (List.cons.inj h2).2, (List.cons.inj h2).1,
                  ground.subAdd hb]
              rw [ground.countOf_head_ne he ([] : List Shape),
                ground.countOf_head_ne hne ([] : List Shape)]
              rfl
          · rw [if_neg hb]
            have hne : ¬ (b :: s') = (a + 1) :: t' := by
              intro he
              refine hb ?_
              rw [(List.cons.inj he).1]
              exact Nat.succ_pos a
            rw [ground.countOf_head_ne hne ([] : List Shape)]
            rfl
        have hfold : ground.famFold Nat.add 0
            (fun j => ground.countOf (b :: s')
              (if 0 < ground.getAt 0 (a :: t') j then
                [units.moveDn j (a :: t')] else []))
            (List.range t'.length)
          = ground.famFold Nat.add 0
            (fun j => ground.countOf (a :: t')
              (if 0 < ground.getAt 0 (b :: s') (j + 1) then
                [units.moveUp j (b :: s')] else []))
            (List.range s'.length) := by
          rw [hts]
          refine ground.famFold_congr_members Nat.add 0 _ _
            (List.range s'.length) ?_
          intro j hj
          have hjs : j < s'.length := by
            rw [countOf_range j s'.length] at hj
            by_cases hc : j < s'.length
            · exact hc
            · rw [if_neg hc] at hj
              exact absurd hj (Nat.lt_irrefl 0)
          have hjS : j + 1 < (b :: s').length := Nat.succ_lt_succ hjs
          have hjT : j + 1 < (a :: t').length := by
            show j + 1 < t'.length + 1
            rw [hts]
            exact Nat.succ_lt_succ hjs
          by_cases hgS : 0 < ground.getAt 0 (b :: s') (j + 1)
          · rw [if_pos hgS]
            by_cases hgT : 0 < ground.getAt 0 (a :: t') j
            · rw [if_pos hgT]
              by_cases hdn : (b :: s') = units.moveDn j (a :: t')
              · have hup : (a :: t') = units.moveUp j (b :: s') := by
                  rw [hdn, units.moveUp_moveDn j (a :: t') hjT hgT]
                rw [← hdn, ← hup, ground.countOf_head, ground.countOf_head]
                rfl
              · have hne : ¬ (a :: t') = units.moveUp j (b :: s') := by
                  intro hu
                  refine hdn ?_
                  rw [hu, units.moveDn_moveUp j (b :: s') hjS hgS]
                rw [ground.countOf_head_ne hdn ([] : List Shape),
                  ground.countOf_head_ne hne ([] : List Shape)]
                rfl
            · rw [if_neg hgT]
              have hne : ¬ (a :: t') = units.moveUp j (b :: s') := by
                intro hu
                refine hgT ?_
                rw [hu, units.getAt_moveUp_self j (b :: s') (Nat.lt_of_succ_lt hjS)]
                exact Nat.succ_pos _
              rw [ground.countOf_head_ne hne ([] : List Shape)]
              rfl
          · rw [if_neg hgS]
            have hne : ¬ (b :: s') = units.moveDn j (a :: t') := by
              intro hd
              refine hgS ?_
              rw [hd, units.getAt_moveDn_next j (a :: t') hjT]
              exact Nat.succ_pos _
            by_cases hgT : 0 < ground.getAt 0 (a :: t') j
            · rw [if_pos hgT, ground.countOf_head_ne hne ([] : List Shape)]
              rfl
            · rw [if_neg hgT]
              rfl
        show ground.countOf (b :: s') (pieri.row (a :: t'))
          = ground.countOf (a :: t') (removals (b :: s'))
        rw [pieri.row_split a t' (b :: s'), removals_split b s' (a :: t'),
          hhead, hfold]
  · rw [row_count_ne t s (fun he => hlen he.symm),
      removals_count_ne t s hlen]

/-- A removal descends the degree by one and keeps the width: the
shortened head lowers the first row, a raised key lowers its
successor row, and the row list reads the raise back. -/
theorem degree_removals (s t : Shape)
    (h : 0 < ground.countOf t (removals s)) :
    places.degree t + 1 = places.degree s ∧ t.length = s.length := by
  match s, h with
  | [], h => exact absurd h (Nat.lt_irrefl 0)
  | b :: s', h =>
    rw [removals_split b s' t] at h
    match ground.posOr h with
    | .inl hh =>
      have hb : 0 < b := by
        by_cases hbc : 0 < b
        · exact hbc
        · rw [if_neg hbc] at hh
          exact absurd hh (Nat.lt_irrefl 0)
      rw [if_pos hb] at hh
      have hte : t = (b - 1) :: s' := ground.countOf_single hh
      have hb1 : b - 1 + 1 = b := ground.subAdd hb
      have hgrow : rowList (b :: s')
          = ground.bumpAt 0 (rowList ((b - 1) :: s')) := by
        have h0 := units.rowList_grow (b - 1) s'
        rw [hb1] at h0
        exact h0
      have hlen0 : 0 < (rowList ((b - 1) :: s')).length := by
        rw [length_rowList]
        exact Nat.succ_pos _
      refine ⟨?_, by rw [hte]; rfl⟩
      show sumNat (rowList t) + 1 = sumNat (rowList (b :: s'))
      rw [hte, hgrow,
        ground.sumNat_bumpAt 0 (rowList ((b - 1) :: s')) hlen0]
    | .inr hp =>
      obtain ⟨j, hj, hfj⟩ := ground.famFold_pos_witness _
        (List.range s'.length) hp
      have hjs : j < s'.length := by
        rw [countOf_range j s'.length] at hj
        by_cases hc : j < s'.length
        · exact hc
        · rw [if_neg hc] at hj
          exact absurd hj (Nat.lt_irrefl 0)
      have hjS : j + 1 < (b :: s').length := Nat.succ_lt_succ hjs
      have hg : 0 < ground.getAt 0 (b :: s') (j + 1) := by
        by_cases hgc : 0 < ground.getAt 0 (b :: s') (j + 1)
        · exact hgc
        · rw [if_neg hgc] at hfj
          exact absurd hfj (Nat.lt_irrefl 0)
      rw [if_pos hg] at hfj
      have hte : t = units.moveUp j (b :: s') :=
        ground.countOf_single hfj
      have hlent : t.length = (b :: s').length := by
        rw [hte]
        exact units.length_moveUp j (b :: s')
      have hjT : j + 1 < t.length := by
        rw [hlent]
        exact hjS
      have hocc : 0 < ground.getAt 0 t j := by
        rw [hte, units.getAt_moveUp_self j (b :: s') (Nat.lt_of_succ_lt hjS)]
        exact Nat.succ_pos _
      have hdn : units.moveDn j t = b :: s' := by
        rw [hte]
        exact units.moveDn_moveUp j (b :: s') hjS hg
      have hrow : rowList (b :: s')
          = ground.bumpAt (j + 1) (rowList t) := by
        rw [← hdn]
        exact units.rowList_moveDn j t hjT hocc
      have hjR : j + 1 < (rowList t).length := by
        rw [length_rowList]
        exact hjT
      refine ⟨?_, hlent⟩
      show sumNat (rowList t) + 1 = sumNat (rowList (b :: s'))
      rw [hrow, ground.sumNat_bumpAt (j + 1) (rowList t) hjR]

/-- The recursion's step equation. -/
private theorem pathGo_succ (k : Nat) (s : Shape) :
    pathGo (k + 1) s
      = if places.degree s == 0 then 1
        else (removals s).foldl (fun acc t => acc + pathGo k t) 0 := rfl

/-- The recursion's fuel is stable beyond the degree: at a fuel at
or beyond the degree the recursion reads the path count. -/
private theorem pathGo_fuel : ∀ (k : Nat) (s : Shape),
    places.degree s ≤ k → pathGo k s = pathCount s := by
  intro k
  induction k with
  | zero =>
    intro s hs
    have h0 : places.degree s = 0 := Nat.eq_zero_of_le_zero hs
    show pathGo 0 s = pathGo (places.degree s) s
    rw [h0]
  | succ k ih =>
    intro s hs
    show pathGo (k + 1) s = pathGo (places.degree s) s
    match hd : places.degree s with
    | 0 =>
      rw [pathGo_succ k s, hd]
      rfl
    | q + 1 =>
      have hq : q + 1 ≤ k + 1 := by
        have hs' := hs
        rw [hd] at hs'
        exact hs'
      rw [pathGo_succ k s, pathGo_succ q s, hd]
      show (removals s).foldl (fun acc t => acc + pathGo k t) 0
        = (removals s).foldl (fun acc t => acc + pathGo q t) 0
      rw [ground.foldlSum (pathGo k) (removals s) 0,
        ground.foldlSum (pathGo q) (removals s) 0]
      refine congrArg (fun x => 0 + x) ?_
      refine ground.famFold_congr_members Nat.add 0 _ _ (removals s) ?_
      intro t ht
      obtain ⟨hdt, _⟩ := degree_removals s t ht
      have hdt' : places.degree t = q := by
        rw [hd] at hdt
        exact Nat.succ.inj hdt
      rw [ih t (by rw [hdt']; exact Nat.le_of_succ_le_succ hq)]
      show pathGo (places.degree t) t = pathGo q t
      rw [hdt']

/-- The unit shape's path count is one, the recursion's seed at the
vacant degree. -/
theorem pathCount_vac (s : Shape) (h : places.degree s = 0) :
    pathCount s = 1 := by
  show pathGo (places.degree s) s = 1
  rw [h]
  rfl

/-- The recursion at an occupied degree: the path count is the fold
of the removals' path counts, one step down the lattice. -/
theorem pathCount_step (s : Shape) (k : Nat)
    (h : places.degree s = k + 1) :
    pathCount s = ground.famFold Nat.add 0 pathCount (removals s) := by
  show pathGo (places.degree s) s = _
  rw [h, pathGo_succ k s, h]
  show (removals s).foldl (fun acc t => acc + pathGo k t) 0 = _
  rw [ground.foldlSum (pathGo k) (removals s) 0, Nat.zero_add]
  refine ground.famFold_congr_members Nat.add 0 _ _ (removals s) ?_
  intro t ht
  obtain ⟨hdt, _⟩ := degree_removals s t ht
  exact pathGo_fuel k t
    (by rw [h] at hdt; exact Nat.le_of_eq (Nat.succ.inj hdt))

/-! The square-sum tier (`squareSum`): the cover operator `U` and
the removal operator `D` on coefficient functions are transposes
for the shape pairing, `DU = UD + id` at the shapes of fewer than
`d` rows, and the telescope closes the pairing at the factorial.
Beneath the commutator sits the moves' interchange kit: the head
move (the new column) and the adjacent moves pass each other, and
each move's key reads are the guards' own. -/

/-- A cover ascends the degree by one and keeps the width, the
mirror of the removals' descent. -/
private theorem row_degree (t s : Shape)
    (h : 0 < ground.countOf s (pieri.row t)) :
    places.degree s = places.degree t + 1 ∧ s.length = t.length := by
  rw [row_removals t s] at h
  obtain ⟨hd, hl⟩ := degree_removals s t h
  exact ⟨hd.symm, hl.symm⟩

/-- The cover operator on coefficient functions: the value at a
shape folds the function over the shapes it covers. -/
private def upF (f : Shape → Nat) (s : Shape) : Nat :=
  ground.famFold Nat.add 0 f (removals s)

/-- The removal operator on coefficient functions: the value at a
shape folds the function over the shapes covering it. -/
private def dnF (f : Shape → Nat) (t : Shape) : Nat :=
  ground.famFold Nat.add 0 f (pieri.row t)

/-- The shape pairing at a degree: the fold of the pointwise
products over the shapes of the stated boxes and letters. -/
private def pairAt (d m : Nat) (f g : Shape → Nat) : Nat :=
  ground.famFold Nat.add 0 (fun s => f s * g s) (places.allShapes d m)

/-- A value splits at a key's guard: the picked arm against the
withheld one. -/
private theorem ifSplit (c : Prop) [Decidable c] (x : Nat) :
    x = (if c then x else 0) + (if c then 0 else x) := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc, Nat.add_zero]
  · rw [if_neg hc, if_neg hc, Nat.zero_add]


/-- The range fold peels its first key: the head's value against
the shifted family. -/
private theorem foldRange_cons (F : Nat → Nat) :
    ∀ n : Nat, ground.famFold Nat.add 0 F (List.range (n + 1))
      = F 0 + ground.famFold Nat.add 0 (fun j => F (j + 1)) (List.range n)
  | 0 => rfl
  | n + 1 => by
    rw [ground.range_succ (n + 1),
      ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add F
        (List.range (n + 1)) [n + 1],
      foldRange_cons F n,
      ground.range_succ n,
      ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add
        (fun j => F (j + 1)) (List.range n) [n]]
    show F 0 + ground.famFold Nat.add 0 (fun j => F (j + 1)) (List.range n)
        + (F (n + 1) + 0)
      = F 0 + (ground.famFold Nat.add 0 (fun j => F (j + 1)) (List.range n)
        + (F (n + 1) + 0))
    rw [Nat.add_assoc]



/-- The last key of a shape with fewer boxes than letters is
vacant: an occupied last column would carry at least the width in
boxes. -/
private theorem getAt_last_zero (t : Shape) (n : Nat)
    (hl : t.length = n + 1) (hm : places.degree t < n + 1) :
    ground.getAt 0 t n = 0 := by
  obtain ⟨t0, x, hte, hl0⟩ := ground.snoc_split n t hl
  have hd : places.degree t = places.degree t0 + x * (t0.length + 1) := by
    rw [hte]
    exact places.degree_snoc t0 x
  have hx : x = 0 := by
    match x, hd with
    | 0, _ => rfl
    | y + 1, hd =>
      have h1 : (y + 1) * (t0.length + 1)
          = y * (t0.length + 1) + (t0.length + 1) :=
        Nat.succ_mul y (t0.length + 1)
      have h2 : t0.length + 1 ≤ places.degree t := by
        rw [hd, h1]
        exact Nat.le_trans
          (Nat.le_add_left (t0.length + 1) (y * (t0.length + 1)))
          (Nat.le_add_left _ (places.degree t0))
      rw [hl0] at h2
      exact absurd (Nat.lt_of_lt_of_le hm h2) (Nat.lt_irrefl _)
  rw [hte, hx]
  have hg := ground.getAt_append_add 0 t0 [0] 0
  rw [Nat.add_zero, hl0] at hg
  exact hg

/-- The occupied keys count once more from the head at a vacant
last key: the row's guard family against the removals'. -/
private theorem guard_count (t : Shape) (n : Nat)
    (hz : ground.getAt 0 t n = 0) :
    ground.famFold Nat.add 0
        (fun j => if 0 < ground.getAt 0 t j then 1 else 0)
        (List.range n)
      = (if 0 < ground.getAt 0 t 0 then 1 else 0)
        + ground.famFold Nat.add 0
            (fun j => if 0 < ground.getAt 0 t (j + 1) then 1 else 0)
            (List.range n) := by
  have hsnoc : ground.famFold Nat.add 0
      (fun j => if 0 < ground.getAt 0 t j then 1 else 0)
      (List.range (n + 1))
      = ground.famFold Nat.add 0
        (fun j => if 0 < ground.getAt 0 t j then 1 else 0)
        (List.range n) := by
    rw [ground.range_succ n,
      ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add
        (fun j => if 0 < ground.getAt 0 t j then 1 else 0)
        (List.range n) [n]]
    show ground.famFold Nat.add 0
        (fun j => if 0 < ground.getAt 0 t j then 1 else 0)
        (List.range n)
        + ((if 0 < ground.getAt 0 t n then 1 else 0) + 0)
      = ground.famFold Nat.add 0
        (fun j => if 0 < ground.getAt 0 t j then 1 else 0)
        (List.range n)
    rw [hz, if_neg (Nat.lt_irrefl 0)]
    rfl
  have hcons := foldRange_cons
    (fun j => if 0 < ground.getAt 0 t j then 1 else 0) n
  rw [hsnoc] at hcons
  exact hcons

/-- A guarded singleton's fold: the guard against the member's
weight. -/
private theorem famFold_guard (c : Prop) [Decidable c]
    (F : Shape → Nat) (v : Shape) :
    ground.famFold Nat.add 0 F (if c then [v] else [])
      = if c then F v else 0 := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]
    show F v + 0 = F v
    rw [Nat.add_zero]
  · rw [if_neg hc, if_neg hc]
    rfl


/-- The row's fold at any weight: the head's raise against the
lowered keys' guarded family. -/
private theorem row_fold (F : Shape → Nat) (a : Nat) (tt : List Nat) :
    ground.famFold Nat.add 0 F (pieri.row (a :: tt))
      = F (ground.bumpAt 0 (a :: tt))
        + ground.famFold Nat.add 0
            (fun j => if 0 < ground.getAt 0 (a :: tt) j
              then F (units.moveDn j (a :: tt)) else 0)
            (List.range tt.length) := by
  show ground.famFold Nat.add 0 F
      ([ground.bumpAt 0 (a :: tt)] ++ (List.range tt.length).flatMap
        (fun j => if 0 < ground.getAt 0 (a :: tt) j
          then [units.moveDn j (a :: tt)] else []))
    = _
  rw [ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add F
      [ground.bumpAt 0 (a :: tt)]
      ((List.range tt.length).flatMap
        (fun j => if 0 < ground.getAt 0 (a :: tt) j
          then [units.moveDn j (a :: tt)] else [])),
    ground.famFold_flatMap F
      (fun j => if 0 < ground.getAt 0 (a :: tt) j
        then [units.moveDn j (a :: tt)] else [])
      (List.range tt.length)]
  show F (ground.bumpAt 0 (a :: tt)) + 0
      + ground.famFold Nat.add 0
        (fun j => ground.famFold Nat.add 0 F
          (if 0 < ground.getAt 0 (a :: tt) j
            then [units.moveDn j (a :: tt)] else []))
        (List.range tt.length)
    = _
  rw [Nat.add_zero,
    ground.famFold_congr_all Nat.add 0
      (fun j => ground.famFold Nat.add 0 F
        (if 0 < ground.getAt 0 (a :: tt) j
          then [units.moveDn j (a :: tt)] else []))
      (fun j => if 0 < ground.getAt 0 (a :: tt) j
        then F (units.moveDn j (a :: tt)) else 0)
      (fun j => famFold_guard _ F _) (List.range tt.length)]

/-- The removals' fold at any weight: the head's guarded lowering
against the raised keys' guarded family. -/
private theorem removals_fold (F : Shape → Nat) (b : Nat)
    (ss : List Nat) :
    ground.famFold Nat.add 0 F (removals (b :: ss))
      = (if 0 < b then F (ground.dipAt 0 (b :: ss)) else 0)
        + ground.famFold Nat.add 0
            (fun j => if 0 < ground.getAt 0 (b :: ss) (j + 1)
              then F (units.moveUp j (b :: ss)) else 0)
            (List.range ss.length) := by
  show ground.famFold Nat.add 0 F
      ((if 0 < b then [ground.dipAt 0 (b :: ss)] else [])
        ++ (List.range ss.length).flatMap
          (fun j => if 0 < ground.getAt 0 (b :: ss) (j + 1)
            then [units.moveUp j (b :: ss)] else []))
    = _
  rw [ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add F
      (if 0 < b then [ground.dipAt 0 (b :: ss)] else [])
      ((List.range ss.length).flatMap
        (fun j => if 0 < ground.getAt 0 (b :: ss) (j + 1)
          then [units.moveUp j (b :: ss)] else [])),
    famFold_guard (0 < b) F (ground.dipAt 0 (b :: ss)),
    ground.famFold_flatMap F
      (fun j => if 0 < ground.getAt 0 (b :: ss) (j + 1)
        then [units.moveUp j (b :: ss)] else [])
      (List.range ss.length),
    ground.famFold_congr_all Nat.add 0
      (fun j => ground.famFold Nat.add 0 F
        (if 0 < ground.getAt 0 (b :: ss) (j + 1)
          then [units.moveUp j (b :: ss)] else []))
      (fun j => if 0 < ground.getAt 0 (b :: ss) (j + 1)
        then F (units.moveUp j (b :: ss)) else 0)
      (fun j => famFold_guard _ F _) (List.range ss.length)]
  rfl

/-- The removals' occupancy in indicator form: the head's guarded
lowering against the raised keys' guarded family. -/
private theorem removals_count (s x : Shape) (hs : 0 < s.length) :
    ground.countOf x (removals s)
      = (if 0 < ground.getAt 0 s 0
          then (if x = ground.dipAt 0 s then 1 else 0) else 0)
        + ground.famFold Nat.add 0
            (fun j => if 0 < ground.getAt 0 s (j + 1)
              then (if x = units.moveUp j s then 1 else 0) else 0)
            (List.range (s.length - 1)) := by
  match s, hs with
  | [], hs => exact absurd hs (Nat.lt_irrefl 0)
  | b :: s', _ =>
    rw [ground.countOf_fold x (removals (b :: s')),
      removals_fold (fun r => if x = r then 1 else 0) b s']
    rfl

/-- The row's occupancy in indicator form: the head's raise against
the lowered keys' guarded family. -/
private theorem row_count (s x : Shape) (hs : 0 < s.length) :
    ground.countOf x (pieri.row s)
      = (if x = ground.bumpAt 0 s then 1 else 0)
        + ground.famFold Nat.add 0
            (fun j => if 0 < ground.getAt 0 s j
              then (if x = units.moveDn j s then 1 else 0) else 0)
            (List.range (s.length - 1)) := by
  match s, hs with
  | [], hs => exact absurd hs (Nat.lt_irrefl 0)
  | a :: t, _ =>
    rw [ground.countOf_fold x (pieri.row (a :: t)),
      row_fold (fun c => if x = c then 1 else 0) a t]
    rfl

/-- The five-summand shuffle beneath the commutator's ledger. -/
private theorem addShuffle (w p q r s v : Nat) :
    (w + p) + (q + ((r + s) + v)) = w + ((r + q) + (p + (s + v))) := by
  rw [Nat.add_assoc w p (q + ((r + s) + v)),
    Nat.add_assoc r s v,
    ← Nat.add_assoc q r (s + v), Nat.add_comm q r,
    Nat.add_assoc r q (s + v),
    ← Nat.add_assoc p r (q + (s + v)), Nat.add_comm p r,
    Nat.add_assoc r p (q + (s + v)),
    ← Nat.add_assoc p q (s + v), Nat.add_comm p q,
    Nat.add_assoc q p (s + v),
    Nat.add_assoc r q (p + (s + v))]

/-- The mixed head arm: lowering the head of a grown column reads
growing a column of the lowered head, guard for guard. -/
private theorem arm_dipAt0 (a : Nat) (tt : List Nat) (t' : Shape) :
    ground.famFold Nat.add 0
        (fun j => if 0 < ground.getAt 0 (a :: tt) j
          then (if 0 < ground.getAt 0 (units.moveDn j (a :: tt)) 0
            then (if t' = ground.dipAt 0 (units.moveDn j (a :: tt)) then 1 else 0)
            else 0)
          else 0)
        (List.range tt.length)
      = ground.famFold Nat.add 0
        (fun j => if 0 < a
          then (if 0 < ground.getAt 0 (ground.dipAt 0 (a :: tt)) j
            then (if t' = units.moveDn j (ground.dipAt 0 (a :: tt)) then 1 else 0)
            else 0)
          else 0)
        (List.range tt.length) := by
  refine ground.famFold_congr_all Nat.add 0 _ _ ?_ (List.range tt.length)
  intro j
  rw [units.dipAt0_moveDn j (a :: tt)]
  match j with
  | 0 =>
    rw [units.getAt_moveDn_self 0 (a :: tt), ground.getAt_dipAt 0 (a :: tt)]
    rfl
  | jj + 1 =>
    rw [units.getAt_moveDn_ne (jj + 1) (a :: tt) 0
        (fun he => Nat.noConfusion he) (fun he => Nat.noConfusion he),
      ground.getAt_dipAt_ne 0 (a :: tt) (jj + 1)
        (fun hc => Nat.noConfusion hc),
      ground.if_swap (0 < ground.getAt 0 (a :: tt) (jj + 1))
        (0 < ground.getAt 0 (a :: tt) 0)
        (if t' = units.moveDn (jj + 1) (ground.dipAt 0 (a :: tt)) then 1 else 0)]
    rfl

/-- The diagonal ledger: each occupied key's raise-then-lower reads
the source, once more from the head than the lower-then-raise reads
at a vacant last key. -/
private theorem diag_count (a : Nat) (tt : List Nat) (t' : Shape)
    (hz : ground.getAt 0 (a :: tt) tt.length = 0) :
    ground.famFold Nat.add 0
        (fun j => if 0 < ground.getAt 0 (a :: tt) j
          then (if t' = a :: tt then 1 else 0) else 0)
        (List.range tt.length)
      = (if 0 < a then (if t' = a :: tt then 1 else 0) else 0)
        + ground.famFold Nat.add 0
            (fun j => if 0 < ground.getAt 0 (a :: tt) (j + 1)
              then (if t' = a :: tt then 1 else 0) else 0)
            (List.range tt.length) := by
  by_cases he : t' = a :: tt
  · rw [if_pos he]
    exact guard_count (a :: tt) tt.length hz
  · rw [if_neg he,
      ground.famFold_zero
        (fun j => if 0 < ground.getAt 0 (a :: tt) j then 0 else 0)
        (fun _ => ite_self 0) (List.range tt.length),
      ground.famFold_zero
        (fun j => if 0 < ground.getAt 0 (a :: tt) (j + 1) then 0 else 0)
        (fun _ => ite_self 0) (List.range tt.length),
      ite_self (c := 0 < a) 0]

/-- The crossed arms at distinct keys: raise at one key then lower
at another reads the moves in either order, guard for guard. -/
private theorem cross_arm (u : List Nat) (t' : Shape) (j j' : Nat)
    (hne : ¬ j' = j) :
    (if 0 < ground.getAt 0 u j
      then (if 0 < ground.getAt 0 (units.moveDn j u) (j' + 1)
        then (if t' = units.moveUp j' (units.moveDn j u) then 1 else 0)
        else 0)
      else 0)
      = (if 0 < ground.getAt 0 u (j' + 1)
        then (if 0 < ground.getAt 0 (units.moveUp j' u) j
          then (if t' = units.moveDn j (units.moveUp j' u) then 1 else 0)
          else 0)
        else 0) := by
  rw [units.moveUp_moveDn_comm j' j u hne]
  by_cases hjj : j = j' + 1
  · rw [hjj, units.getAt_moveDn_self (j' + 1) u, units.getAt_moveUp_next j' u]
  · rw [units.getAt_moveDn_ne j u (j' + 1)
        (fun he => hjj he.symm) (fun he => hne (Nat.succ.inj he)),
      units.getAt_moveUp_ne j' u j (fun he => hne he.symm) hjj,
      ground.if_swap (0 < ground.getAt 0 u j)
        (0 < ground.getAt 0 u (j' + 1))
        (if t' = units.moveDn j (units.moveUp j' u) then 1 else 0)]

/-- The crossed arms' double fold swaps its keys: the raises'
removals read the removals' raises off the diagonal. -/
private theorem off_swap (a : Nat) (tt : List Nat) (t' : Shape) :
    ground.famFold Nat.add 0
        (fun j => ground.famFold Nat.add 0
          (fun j' => if j' = j then 0
            else (if 0 < ground.getAt 0 (a :: tt) j
              then (if 0 < ground.getAt 0 (units.moveDn j (a :: tt)) (j' + 1)
                then (if t' = units.moveUp j' (units.moveDn j (a :: tt))
                  then 1 else 0)
                else 0)
              else 0))
          (List.range tt.length))
        (List.range tt.length)
      = ground.famFold Nat.add 0
        (fun j => ground.famFold Nat.add 0
          (fun j' => if j' = j then 0
            else (if 0 < ground.getAt 0 (a :: tt) (j + 1)
              then (if 0 < ground.getAt 0 (units.moveUp j (a :: tt)) j'
                then (if t' = units.moveDn j' (units.moveUp j (a :: tt))
                  then 1 else 0)
                else 0)
              else 0))
          (List.range tt.length))
        (List.range tt.length) := by
  have hpoint : ∀ w u : Nat,
      (if w = u then 0
        else (if 0 < ground.getAt 0 (a :: tt) u
          then (if 0 < ground.getAt 0 (units.moveDn u (a :: tt)) (w + 1)
            then (if t' = units.moveUp w (units.moveDn u (a :: tt))
              then 1 else 0)
            else 0)
          else 0))
      = (if u = w then 0
        else (if 0 < ground.getAt 0 (a :: tt) (w + 1)
          then (if 0 < ground.getAt 0 (units.moveUp w (a :: tt)) u
            then (if t' = units.moveDn u (units.moveUp w (a :: tt))
              then 1 else 0)
            else 0)
          else 0)) := by
    intro w u
    by_cases hwu : w = u
    · rw [if_pos hwu, if_pos hwu.symm]
    · rw [if_neg hwu]
      rw [if_neg (show ¬ u = w from fun he => hwu he.symm)]
      exact cross_arm (a :: tt) t' u w hwu
  exact (ground.famFold_swap
      (fun j j' => if j' = j then 0
        else (if 0 < ground.getAt 0 (a :: tt) j
          then (if 0 < ground.getAt 0 (units.moveDn j (a :: tt)) (j' + 1)
            then (if t' = units.moveUp j' (units.moveDn j (a :: tt))
              then 1 else 0)
            else 0)
          else 0))
      (List.range tt.length) (List.range tt.length)).trans
    (ground.famFold_congr_all Nat.add 0
      (fun w => ground.famFold Nat.add 0
        (fun u => if w = u then 0
          else (if 0 < ground.getAt 0 (a :: tt) u
            then (if 0 < ground.getAt 0 (units.moveDn u (a :: tt)) (w + 1)
              then (if t' = units.moveUp w (units.moveDn u (a :: tt))
                then 1 else 0)
              else 0)
            else 0))
        (List.range tt.length))
      (fun w => ground.famFold Nat.add 0
        (fun u => if u = w then 0
          else (if 0 < ground.getAt 0 (a :: tt) (w + 1)
            then (if 0 < ground.getAt 0 (units.moveUp w (a :: tt)) u
              then (if t' = units.moveDn u (units.moveUp w (a :: tt))
                then 1 else 0)
              else 0)
            else 0))
        (List.range tt.length))
      (fun w => ground.famFold_congr_all Nat.add 0 _ _
        (fun u => hpoint w u) (List.range tt.length))
      (List.range tt.length))

/-- Two sums agree arm for arm. -/
private theorem addCongr {A B C D : Nat} (h1 : A = B) (h2 : C = D) :
    A + C = B + D := by
  rw [h1, h2]

/-- The covers' removals, fully split: the head's raise-then-lower
reads the source outright; the raise-then-adjacent-lower arms, the
adjacent-raise-then-head-lower arms, the diagonal raise-then-lower
arms at the source, and the crossed arms off the diagonal. -/
private theorem cover_left (a : Nat) (tt : List Nat) (t' : Shape) :
    ground.famFold Nat.add 0
        (fun s => ground.countOf t' (removals s)) (pieri.row (a :: tt))
      = ((if t' = a :: tt then 1 else 0)
          + ground.famFold Nat.add 0
              (fun j => if 0 < ground.getAt 0 (a :: tt) (j + 1)
                then (if t' = ground.bumpAt 0 (units.moveUp j (a :: tt)) then 1 else 0)
                else 0)
              (List.range tt.length))
        + (ground.famFold Nat.add 0
            (fun j => if 0 < ground.getAt 0 (a :: tt) j
              then (if 0 < ground.getAt 0 (units.moveDn j (a :: tt)) 0
                then (if t' = ground.dipAt 0 (units.moveDn j (a :: tt)) then 1 else 0)
                else 0)
              else 0)
            (List.range tt.length)
          + (ground.famFold Nat.add 0
              (fun j => if 0 < ground.getAt 0 (a :: tt) j
                then (if t' = a :: tt then 1 else 0) else 0)
              (List.range tt.length)
            + ground.famFold Nat.add 0
                (fun j => ground.famFold Nat.add 0
                  (fun j' => if j' = j then 0
                    else (if 0 < ground.getAt 0 (a :: tt) j
                      then (if 0 < ground.getAt 0
                          (units.moveDn j (a :: tt)) (j' + 1)
                        then (if t' = units.moveUp j'
                            (units.moveDn j (a :: tt))
                          then 1 else 0)
                        else 0)
                      else 0))
                  (List.range tt.length))
                (List.range tt.length))) := by
  have hHU : ground.countOf t' (removals (ground.bumpAt 0 (a :: tt)))
      = (if t' = a :: tt then 1 else 0)
        + ground.famFold Nat.add 0
            (fun j => if 0 < ground.getAt 0 (a :: tt) (j + 1)
              then (if t' = ground.bumpAt 0 (units.moveUp j (a :: tt)) then 1 else 0)
              else 0)
            (List.range tt.length) := by
    rw [removals_count (ground.bumpAt 0 (a :: tt)) t'
        (by rw [ground.length_bumpAt 0 (a :: tt)]; exact Nat.succ_pos tt.length),
      if_pos (show 0 < ground.getAt 0 (ground.bumpAt 0 (a :: tt)) 0
        from Nat.succ_pos a),
      ground.dipAt_bumpAt_self 0 (a :: tt)]
    refine addCongr rfl ?_
    exact ground.famFold_congr_all Nat.add 0
      (fun j => if 0 < ground.getAt 0 (ground.bumpAt 0 (a :: tt)) (j + 1)
        then (if t' = units.moveUp j (ground.bumpAt 0 (a :: tt)) then 1 else 0)
        else 0)
      (fun j => if 0 < ground.getAt 0 (a :: tt) (j + 1)
        then (if t' = ground.bumpAt 0 (units.moveUp j (a :: tt)) then 1 else 0)
        else 0)
      (fun j => by
        rw [ground.getAt_bumpAt_ne 0 (a :: tt) (j + 1)
          (fun hc => Nat.noConfusion hc),
        ← units.bumpAt0_moveUp j (a :: tt)])
      (List.range tt.length)
  have hB : ∀ j, 0 < ground.countOf j (List.range tt.length) →
      (if 0 < ground.getAt 0 (a :: tt) j
        then ground.countOf t' (removals (units.moveDn j (a :: tt)))
        else 0)
      = (if 0 < ground.getAt 0 (a :: tt) j
          then (if 0 < ground.getAt 0 (units.moveDn j (a :: tt)) 0
            then (if t' = ground.dipAt 0 (units.moveDn j (a :: tt)) then 1 else 0)
            else 0)
          else 0)
        + ((if 0 < ground.getAt 0 (a :: tt) j
            then (if t' = a :: tt then 1 else 0) else 0)
          + ground.famFold Nat.add 0
              (fun j' => if j' = j then 0
                else (if 0 < ground.getAt 0 (a :: tt) j
                  then (if 0 < ground.getAt 0
                      (units.moveDn j (a :: tt)) (j' + 1)
                    then (if t' = units.moveUp j'
                        (units.moveDn j (a :: tt))
                      then 1 else 0)
                    else 0)
                  else 0))
              (List.range tt.length)) := by
    intro j hjc
    have hjlt : j < tt.length := by
      rw [countOf_range j tt.length] at hjc
      by_cases hc : j < tt.length
      · exact hc
      · rw [if_neg hc] at hjc
        exact absurd hjc (Nat.lt_irrefl 0)
    by_cases hg : 0 < ground.getAt 0 (a :: tt) j
    · rw [if_pos hg, if_pos hg, if_pos hg,
        removals_count (units.moveDn j (a :: tt)) t'
          (by rw [units.length_moveDn j (a :: tt)]
              exact Nat.succ_pos tt.length),
        show (units.moveDn j (a :: tt)).length - 1 = tt.length from
          congrArg (fun w => w - 1) (units.length_moveDn j (a :: tt))]
      refine addCongr rfl ?_
      have h1 : ground.countOf j (List.range tt.length) = 1 := by
        rw [countOf_range j tt.length, if_pos hjlt]
      have hXj : (if 0 < ground.getAt 0 (units.moveDn j (a :: tt)) (j + 1)
          then (if t' = units.moveUp j (units.moveDn j (a :: tt))
            then 1 else 0)
          else 0) = (if t' = a :: tt then 1 else 0) := by
        rw [units.getAt_moveDn_next j (a :: tt) (Nat.succ_lt_succ hjlt),
          if_pos (Nat.succ_pos (ground.getAt 0 (a :: tt) (j + 1))),
          units.moveUp_moveDn j (a :: tt) (Nat.succ_lt_succ hjlt) hg]
      have hoffB : ground.famFold Nat.add 0
          (fun j' => if j' = j then 0
            else (if 0 < ground.getAt 0
                (units.moveDn j (a :: tt)) (j' + 1)
              then (if t' = units.moveUp j' (units.moveDn j (a :: tt))
                then 1 else 0)
              else 0))
          (List.range tt.length)
          = ground.famFold Nat.add 0
            (fun j' => if j' = j then 0
              else (if 0 < ground.getAt 0 (a :: tt) j
                then (if 0 < ground.getAt 0
                    (units.moveDn j (a :: tt)) (j' + 1)
                  then (if t' = units.moveUp j'
                      (units.moveDn j (a :: tt))
                    then 1 else 0)
                  else 0)
                else 0))
            (List.range tt.length) := by
        refine ground.famFold_congr_all Nat.add 0 _ _ ?_
          (List.range tt.length)
        intro j'
        by_cases hjj : j' = j
        · rw [if_pos hjj, if_pos hjj]
        · rw [if_neg hjj, if_neg hjj, if_pos hg]
      exact (ground.famFold_congr_all Nat.add 0
          (fun j' => if 0 < ground.getAt 0
              (units.moveDn j (a :: tt)) (j' + 1)
            then (if t' = units.moveUp j' (units.moveDn j (a :: tt))
              then 1 else 0)
            else 0)
          (fun j' => (if j' = j
              then (if 0 < ground.getAt 0
                  (units.moveDn j (a :: tt)) (j' + 1)
                then (if t' = units.moveUp j' (units.moveDn j (a :: tt))
                  then 1 else 0)
                else 0)
              else 0)
            + (if j' = j then 0
              else (if 0 < ground.getAt 0
                  (units.moveDn j (a :: tt)) (j' + 1)
                then (if t' = units.moveUp j' (units.moveDn j (a :: tt))
                  then 1 else 0)
                else 0)))
          (fun j' => ifSplit (j' = j) _) (List.range tt.length)).trans
        ((ground.famFold_add_split
          (fun j' => if j' = j
            then (if 0 < ground.getAt 0
                (units.moveDn j (a :: tt)) (j' + 1)
              then (if t' = units.moveUp j' (units.moveDn j (a :: tt))
                then 1 else 0)
              else 0)
            else 0)
          (fun j' => if j' = j then 0
            else (if 0 < ground.getAt 0
                (units.moveDn j (a :: tt)) (j' + 1)
              then (if t' = units.moveUp j' (units.moveDn j (a :: tt))
                then 1 else 0)
              else 0))
          (List.range tt.length)).trans
          (addCongr ((ground.famFold_pick
            (fun j' => if 0 < ground.getAt 0
                (units.moveDn j (a :: tt)) (j' + 1)
              then (if t' = units.moveUp j' (units.moveDn j (a :: tt))
                then 1 else 0)
              else 0)
            j (List.range tt.length) h1).trans hXj) hoffB))
    · rw [if_neg hg, if_neg hg, if_neg hg,
        ground.famFold_zero
          (fun j' => if j' = j then 0
            else (if 0 < ground.getAt 0 (a :: tt) j
              then (if 0 < ground.getAt 0
                  (units.moveDn j (a :: tt)) (j' + 1)
                then (if t' = units.moveUp j'
                    (units.moveDn j (a :: tt))
                  then 1 else 0)
                else 0)
              else 0))
          (fun j' => by
            by_cases hjj : j' = j
            · rw [if_pos hjj]
            · rw [if_neg hjj, if_neg hg])
          (List.range tt.length)]
  refine (row_fold (fun s => ground.countOf t' (removals s)) a tt).trans ?_
  show ground.countOf t' (removals (ground.bumpAt 0 (a :: tt)))
      + ground.famFold Nat.add 0
        (fun j => if 0 < ground.getAt 0 (a :: tt) j
          then ground.countOf t' (removals (units.moveDn j (a :: tt)))
          else 0)
        (List.range tt.length)
    = _
  rw [hHU,
    ground.famFold_congr_members Nat.add 0 _ _ (List.range tt.length) hB]
  refine addCongr rfl ?_
  exact (ground.famFold_add_split
      (fun j => if 0 < ground.getAt 0 (a :: tt) j
        then (if 0 < ground.getAt 0 (units.moveDn j (a :: tt)) 0
          then (if t' = ground.dipAt 0 (units.moveDn j (a :: tt)) then 1 else 0)
          else 0)
        else 0)
      (fun j => (if 0 < ground.getAt 0 (a :: tt) j
          then (if t' = a :: tt then 1 else 0) else 0)
        + ground.famFold Nat.add 0
            (fun j' => if j' = j then 0
              else (if 0 < ground.getAt 0 (a :: tt) j
                then (if 0 < ground.getAt 0
                    (units.moveDn j (a :: tt)) (j' + 1)
                  then (if t' = units.moveUp j'
                      (units.moveDn j (a :: tt))
                    then 1 else 0)
                  else 0)
                else 0))
            (List.range tt.length))
      (List.range tt.length)).trans
    (addCongr rfl (ground.famFold_add_split
      (fun j => if 0 < ground.getAt 0 (a :: tt) j
        then (if t' = a :: tt then 1 else 0) else 0)
      (fun j => ground.famFold Nat.add 0
        (fun j' => if j' = j then 0
          else (if 0 < ground.getAt 0 (a :: tt) j
            then (if 0 < ground.getAt 0
                (units.moveDn j (a :: tt)) (j' + 1)
              then (if t' = units.moveUp j' (units.moveDn j (a :: tt))
                then 1 else 0)
              else 0)
            else 0))
        (List.range tt.length))
      (List.range tt.length)))

/-- The removals' covers, fully split: the head's lower-then-raise
reads the source under the head's own guard; the lower-then-adjacent
arms, the adjacent-lower-then-head arms, the diagonal arms at the
source, and the crossed arms off the diagonal. -/
private theorem cover_right (a : Nat) (tt : List Nat) (t' : Shape) :
    ground.famFold Nat.add 0
        (fun r => ground.countOf t' (pieri.row r)) (removals (a :: tt))
      = ((if 0 < a then (if t' = a :: tt then 1 else 0) else 0)
          + ground.famFold Nat.add 0
              (fun j => if 0 < a
                then (if 0 < ground.getAt 0 (ground.dipAt 0 (a :: tt)) j
                  then (if t' = units.moveDn j (ground.dipAt 0 (a :: tt))
                    then 1 else 0)
                  else 0)
                else 0)
              (List.range tt.length))
        + (ground.famFold Nat.add 0
            (fun j => if 0 < ground.getAt 0 (a :: tt) (j + 1)
              then (if t' = ground.bumpAt 0 (units.moveUp j (a :: tt)) then 1 else 0)
              else 0)
            (List.range tt.length)
          + (ground.famFold Nat.add 0
              (fun j => if 0 < ground.getAt 0 (a :: tt) (j + 1)
                then (if t' = a :: tt then 1 else 0) else 0)
              (List.range tt.length)
            + ground.famFold Nat.add 0
                (fun j => ground.famFold Nat.add 0
                  (fun j' => if j' = j then 0
                    else (if 0 < ground.getAt 0 (a :: tt) (j + 1)
                      then (if 0 < ground.getAt 0
                          (units.moveUp j (a :: tt)) j'
                        then (if t' = units.moveDn j'
                            (units.moveUp j (a :: tt))
                          then 1 else 0)
                        else 0)
                      else 0))
                  (List.range tt.length))
                (List.range tt.length))) := by
  have hD : (if 0 < a
        then ground.countOf t' (pieri.row (ground.dipAt 0 (a :: tt))) else 0)
      = (if 0 < a then (if t' = a :: tt then 1 else 0) else 0)
        + ground.famFold Nat.add 0
            (fun j => if 0 < a
              then (if 0 < ground.getAt 0 (ground.dipAt 0 (a :: tt)) j
                then (if t' = units.moveDn j (ground.dipAt 0 (a :: tt))
                  then 1 else 0)
                else 0)
              else 0)
            (List.range tt.length) := by
    by_cases ha : 0 < a
    · rw [if_pos ha, if_pos ha,
        row_count (ground.dipAt 0 (a :: tt)) t'
          (by rw [ground.length_dipAt 0 (a :: tt)]
              exact Nat.succ_pos tt.length),
        ground.bumpAt_dipAt_self 0 (a :: tt)
          (show 0 < ground.getAt 0 (a :: tt) 0 from ha)]
      refine addCongr rfl ?_
      exact ground.famFold_congr_all Nat.add 0
        (fun j => if 0 < ground.getAt 0 (ground.dipAt 0 (a :: tt)) j
          then (if t' = units.moveDn j (ground.dipAt 0 (a :: tt)) then 1 else 0)
          else 0)
        (fun j => if 0 < a
          then (if 0 < ground.getAt 0 (ground.dipAt 0 (a :: tt)) j
            then (if t' = units.moveDn j (ground.dipAt 0 (a :: tt)) then 1 else 0)
            else 0)
          else 0)
        (fun j => (if_pos ha).symm) (List.range tt.length)
    · rw [if_neg ha, if_neg ha,
        ground.famFold_zero
          (fun j => if 0 < a
            then (if 0 < ground.getAt 0 (ground.dipAt 0 (a :: tt)) j
              then (if t' = units.moveDn j (ground.dipAt 0 (a :: tt))
                then 1 else 0)
              else 0)
            else 0)
          (fun _ => if_neg ha) (List.range tt.length)]
  have hE : ∀ j, 0 < ground.countOf j (List.range tt.length) →
      (if 0 < ground.getAt 0 (a :: tt) (j + 1)
        then ground.countOf t' (pieri.row (units.moveUp j (a :: tt)))
        else 0)
      = (if 0 < ground.getAt 0 (a :: tt) (j + 1)
          then (if t' = ground.bumpAt 0 (units.moveUp j (a :: tt)) then 1 else 0)
          else 0)
        + ((if 0 < ground.getAt 0 (a :: tt) (j + 1)
            then (if t' = a :: tt then 1 else 0) else 0)
          + ground.famFold Nat.add 0
              (fun j' => if j' = j then 0
                else (if 0 < ground.getAt 0 (a :: tt) (j + 1)
                  then (if 0 < ground.getAt 0
                      (units.moveUp j (a :: tt)) j'
                    then (if t' = units.moveDn j'
                        (units.moveUp j (a :: tt))
                      then 1 else 0)
                    else 0)
                  else 0))
              (List.range tt.length)) := by
    intro j hjc
    have hjlt : j < tt.length := by
      rw [countOf_range j tt.length] at hjc
      by_cases hc : j < tt.length
      · exact hc
      · rw [if_neg hc] at hjc
        exact absurd hjc (Nat.lt_irrefl 0)
    by_cases hg : 0 < ground.getAt 0 (a :: tt) (j + 1)
    · rw [if_pos hg, if_pos hg, if_pos hg,
        row_count (units.moveUp j (a :: tt)) t'
          (by rw [units.length_moveUp j (a :: tt)]
              exact Nat.succ_pos tt.length),
        show (units.moveUp j (a :: tt)).length - 1 = tt.length from
          congrArg (fun w => w - 1) (units.length_moveUp j (a :: tt))]
      refine addCongr rfl ?_
      have h1 : ground.countOf j (List.range tt.length) = 1 := by
        rw [countOf_range j tt.length, if_pos hjlt]
      have hYj : (if 0 < ground.getAt 0 (units.moveUp j (a :: tt)) j
          then (if t' = units.moveDn j (units.moveUp j (a :: tt))
            then 1 else 0)
          else 0) = (if t' = a :: tt then 1 else 0) := by
        rw [units.getAt_moveUp_self j (a :: tt)
            (Nat.lt_of_lt_of_le hjlt (Nat.le_succ tt.length)),
          if_pos (Nat.succ_pos (ground.getAt 0 (a :: tt) j)),
          units.moveDn_moveUp j (a :: tt) (Nat.succ_lt_succ hjlt) hg]
      have hoffE : ground.famFold Nat.add 0
          (fun j' => if j' = j then 0
            else (if 0 < ground.getAt 0 (units.moveUp j (a :: tt)) j'
              then (if t' = units.moveDn j' (units.moveUp j (a :: tt))
                then 1 else 0)
              else 0))
          (List.range tt.length)
          = ground.famFold Nat.add 0
            (fun j' => if j' = j then 0
              else (if 0 < ground.getAt 0 (a :: tt) (j + 1)
                then (if 0 < ground.getAt 0
                    (units.moveUp j (a :: tt)) j'
                  then (if t' = units.moveDn j'
                      (units.moveUp j (a :: tt))
                    then 1 else 0)
                  else 0)
                else 0))
            (List.range tt.length) := by
        refine ground.famFold_congr_all Nat.add 0 _ _ ?_
          (List.range tt.length)
        intro j'
        by_cases hjj : j' = j
        · rw [if_pos hjj, if_pos hjj]
        · rw [if_neg hjj, if_neg hjj, if_pos hg]
      exact (ground.famFold_congr_all Nat.add 0
          (fun j' => if 0 < ground.getAt 0 (units.moveUp j (a :: tt)) j'
            then (if t' = units.moveDn j' (units.moveUp j (a :: tt))
              then 1 else 0)
            else 0)
          (fun j' => (if j' = j
              then (if 0 < ground.getAt 0 (units.moveUp j (a :: tt)) j'
                then (if t' = units.moveDn j' (units.moveUp j (a :: tt))
                  then 1 else 0)
                else 0)
              else 0)
            + (if j' = j then 0
              else (if 0 < ground.getAt 0 (units.moveUp j (a :: tt)) j'
                then (if t' = units.moveDn j' (units.moveUp j (a :: tt))
                  then 1 else 0)
                else 0)))
          (fun j' => ifSplit (j' = j) _) (List.range tt.length)).trans
        ((ground.famFold_add_split
          (fun j' => if j' = j
            then (if 0 < ground.getAt 0 (units.moveUp j (a :: tt)) j'
              then (if t' = units.moveDn j' (units.moveUp j (a :: tt))
                then 1 else 0)
              else 0)
            else 0)
          (fun j' => if j' = j then 0
            else (if 0 < ground.getAt 0 (units.moveUp j (a :: tt)) j'
              then (if t' = units.moveDn j' (units.moveUp j (a :: tt))
                then 1 else 0)
              else 0))
          (List.range tt.length)).trans
          (addCongr ((ground.famFold_pick
            (fun j' => if 0 < ground.getAt 0 (units.moveUp j (a :: tt)) j'
              then (if t' = units.moveDn j' (units.moveUp j (a :: tt))
                then 1 else 0)
              else 0)
            j (List.range tt.length) h1).trans hYj) hoffE))
    · rw [if_neg hg, if_neg hg, if_neg hg,
        ground.famFold_zero
          (fun j' => if j' = j then 0
            else (if 0 < ground.getAt 0 (a :: tt) (j + 1)
              then (if 0 < ground.getAt 0
                  (units.moveUp j (a :: tt)) j'
                then (if t' = units.moveDn j'
                    (units.moveUp j (a :: tt))
                  then 1 else 0)
                else 0)
              else 0))
          (fun j' => by
            by_cases hjj : j' = j
            · rw [if_pos hjj]
            · rw [if_neg hjj, if_neg hg])
          (List.range tt.length)]
  refine (removals_fold
    (fun r => ground.countOf t' (pieri.row r)) a tt).trans ?_
  show (if 0 < a
        then ground.countOf t' (pieri.row (ground.dipAt 0 (a :: tt))) else 0)
      + ground.famFold Nat.add 0
        (fun j => if 0 < ground.getAt 0 (a :: tt) (j + 1)
          then ground.countOf t' (pieri.row (units.moveUp j (a :: tt)))
          else 0)
        (List.range tt.length)
    = _
  rw [hD,
    ground.famFold_congr_members Nat.add 0 _ _ (List.range tt.length) hE]
  refine addCongr rfl ?_
  exact (ground.famFold_add_split
      (fun j => if 0 < ground.getAt 0 (a :: tt) (j + 1)
        then (if t' = ground.bumpAt 0 (units.moveUp j (a :: tt)) then 1 else 0)
        else 0)
      (fun j => (if 0 < ground.getAt 0 (a :: tt) (j + 1)
          then (if t' = a :: tt then 1 else 0) else 0)
        + ground.famFold Nat.add 0
            (fun j' => if j' = j then 0
              else (if 0 < ground.getAt 0 (a :: tt) (j + 1)
                then (if 0 < ground.getAt 0
                    (units.moveUp j (a :: tt)) j'
                  then (if t' = units.moveDn j'
                      (units.moveUp j (a :: tt))
                    then 1 else 0)
                  else 0)
                else 0))
            (List.range tt.length))
      (List.range tt.length)).trans
    (addCongr rfl (ground.famFold_add_split
      (fun j => if 0 < ground.getAt 0 (a :: tt) (j + 1)
        then (if t' = a :: tt then 1 else 0) else 0)
      (fun j => ground.famFold Nat.add 0
        (fun j' => if j' = j then 0
          else (if 0 < ground.getAt 0 (a :: tt) (j + 1)
            then (if 0 < ground.getAt 0 (units.moveUp j (a :: tt)) j'
              then (if t' = units.moveDn j' (units.moveUp j (a :: tt))
                then 1 else 0)
              else 0)
            else 0))
        (List.range tt.length))
      (List.range tt.length)))

/-- The commutator at the lists: over a source of a vacant last
key, the covers' removals read the removals' covers with one
further match at the source itself. -/
private theorem cover_core (a : Nat) (tt : List Nat) (t' : Shape)
    (hz : ground.getAt 0 (a :: tt) tt.length = 0) :
    ground.famFold Nat.add 0
        (fun s => ground.countOf t' (removals s)) (pieri.row (a :: tt))
      = (if t' = a :: tt then 1 else 0)
        + ground.famFold Nat.add 0
            (fun r => ground.countOf t' (pieri.row r))
            (removals (a :: tt)) := by
  rw [cover_left a tt t', arm_dipAt0 a tt t', diag_count a tt t' hz,
    off_swap a tt t', cover_right a tt t']
  exact addShuffle _ _ _ _ _ _

/-- Two shapes of one size share a cover exactly where they share a
removal, and a shape's covers exceed its removals by one at fewer
boxes than letters: `DU = UD + id` read at one matrix entry. -/
private theorem cover_count (d m : Nat) (t t' : Shape)
    (ht : t ∈ places.allShapes d m) (hm : m < d) :
    ground.famFold Nat.add 0
        (fun s => ground.countOf s (pieri.row t')) (pieri.row t)
      = (if t' = t then 1 else 0)
        + ground.famFold Nat.add 0
            (fun r => ground.countOf r (removals t')) (removals t) := by
  obtain ⟨htl, htd⟩ := places.allShapes_sound d m t ht
  rw [ground.famFold_congr_all Nat.add 0
      (fun s => ground.countOf s (pieri.row t'))
      (fun s => ground.countOf t' (removals s))
      (fun s => row_removals t' s) (pieri.row t),
    ground.famFold_congr_all Nat.add 0
      (fun r => ground.countOf r (removals t'))
      (fun r => ground.countOf t' (pieri.row r))
      (fun r => (row_removals r t').symm) (removals t)]
  match t, htl, htd with
  | [], htl, _ =>
    rw [← htl] at hm
    exact absurd hm (Nat.not_lt_zero m)
  | a :: tt, htl, htd =>
    have hmt : places.degree (a :: tt) < tt.length + 1 := by
      rw [htd]
      rw [← htl] at hm
      exact hm
    exact cover_core a tt t'
      (getAt_last_zero (a :: tt) tt.length rfl hmt)

/-- The cover and removal operators are transposes for the shape
pairing: both double folds collect onto the shapes' enumeration at
the lower degree, where the mirror trades each cover read for its
removal read. -/
private theorem adjoint (d m : Nat) (f g : Shape → Nat) :
    pairAt d (m + 1) (upF f) g = pairAt d m f (dnF g) := by
  show ground.famFold Nat.add 0 (fun s => upF f s * g s)
      (places.allShapes d (m + 1))
    = ground.famFold Nat.add 0 (fun t => f t * dnF g t)
      (places.allShapes d m)
  have hA : ∀ s, 0 < ground.countOf s (places.allShapes d (m + 1)) →
      upF f s * g s
        = ground.famFold Nat.add 0
            (fun t => ground.countOf t (removals s) * (f t * g s))
            (places.allShapes d m) := by
    intro s hs
    obtain ⟨hsl, hsd⟩ := places.allShapes_sound d (m + 1) s
      (ground.mem_of_countOf_pos s (places.allShapes d (m + 1)) hs)
    have hbasis : ∀ x, 0 < ground.countOf x (removals s) →
        ground.countOf x (places.allShapes d m) = 1 := by
      intro x hx
      obtain ⟨hdx, hlx⟩ := degree_removals s x hx
      have hdm : places.degree x = m := by
        rw [hsd] at hdx
        exact Nat.succ.inj hdx
      have hmem : x ∈ places.allShapes d m := by
        have h0 := places.mem_allShapes d x (hlx.trans hsl)
        rw [hdm] at h0
        exact h0
      exact Nat.le_antisymm (places.countOf_allShapes_le d m x)
        (ground.countOf_pos_of_mem hmem)
    show ground.famFold Nat.add 0 f (removals s) * g s = _
    exact ((ground.famFold_mulR (g s) f (removals s)).symm).trans
      (ground.famFold_countCollect (fun t => f t * g s) (removals s)
        (places.allShapes d m) hbasis)
  have hC : ∀ t, 0 < ground.countOf t (places.allShapes d m) →
      ground.famFold Nat.add 0
        (fun s => ground.countOf t (removals s) * (f t * g s))
        (places.allShapes d (m + 1))
      = f t * dnF g t := by
    intro t htc
    obtain ⟨htl, htd⟩ := places.allShapes_sound d m t
      (ground.mem_of_countOf_pos t (places.allShapes d m) htc)
    have hbasis : ∀ x, 0 < ground.countOf x (pieri.row t) →
        ground.countOf x (places.allShapes d (m + 1)) = 1 := by
      intro x hx
      obtain ⟨hdx, hlx⟩ := row_degree t x hx
      have hmem : x ∈ places.allShapes d (m + 1) := by
        have h0 := places.mem_allShapes d x (hlx.trans htl)
        rw [hdx, htd] at h0
        exact h0
      exact Nat.le_antisymm (places.countOf_allShapes_le d (m + 1) x)
        (ground.countOf_pos_of_mem hmem)
    have hrr : ground.famFold Nat.add 0
        (fun s => ground.countOf t (removals s) * (f t * g s))
        (places.allShapes d (m + 1))
        = ground.famFold Nat.add 0
          (fun s => ground.countOf s (pieri.row t) * (f t * g s))
          (places.allShapes d (m + 1)) :=
      ground.famFold_congr_all Nat.add 0 _ _
        (fun s => by rw [row_removals t s]) (places.allShapes d (m + 1))
    rw [hrr]
    exact ((ground.famFold_countCollect (fun s => f t * g s)
        (pieri.row t) (places.allShapes d (m + 1)) hbasis).symm).trans
      (ground.famFold_mul (f t) g (pieri.row t)).symm
  rw [ground.famFold_congr_members Nat.add 0 _ _
      (places.allShapes d (m + 1)) hA]
  exact (ground.famFold_swap
      (fun s t => ground.countOf t (removals s) * (f t * g s))
      (places.allShapes d (m + 1)) (places.allShapes d m)).trans
    (ground.famFold_congr_members Nat.add 0
      (fun t => ground.famFold Nat.add 0
        (fun s => ground.countOf t (removals s) * (f t * g s))
        (places.allShapes d (m + 1)))
      (fun t => f t * dnF g t)
      (places.allShapes d m) hC)

/-- The commutator: `DU = UD + id` at the shapes of fewer boxes
than letters — both double folds collect onto the shapes' own
degree, where the cover count reads the removal count with one
further match at the shape itself. -/
private theorem duud (d m : Nat) (hm : m < d) (f : Shape → Nat) :
    ∀ t, t ∈ places.allShapes d m →
      dnF (upF f) t = f t + upF (dnF f) t := by
  intro t ht
  obtain ⟨htl, htd⟩ := places.allShapes_sound d m t ht
  have hR : upF (dnF f) t
      = ground.famFold Nat.add 0
          (fun x => ground.famFold Nat.add 0
            (fun r => ground.countOf r (removals x)) (removals t) * f x)
          (places.allShapes d m) := by
    have h2 : ∀ r, 0 < ground.countOf r (removals t) →
        dnF f r = ground.famFold Nat.add 0
          (fun x => ground.countOf r (removals x) * f x)
          (places.allShapes d m) := by
      intro r hr
      obtain ⟨hdr, hlr⟩ := degree_removals t r hr
      have hbasis : ∀ x, 0 < ground.countOf x (pieri.row r) →
          ground.countOf x (places.allShapes d m) = 1 := by
        intro x hx
        obtain ⟨hdx, hlx⟩ := row_degree r x hx
        have hmem : x ∈ places.allShapes d m := by
          have h0 := places.mem_allShapes d x (hlx.trans (hlr.trans htl))
          rw [hdx, hdr, htd] at h0
          exact h0
        exact Nat.le_antisymm (places.countOf_allShapes_le d m x)
          (ground.countOf_pos_of_mem hmem)
      show ground.famFold Nat.add 0 f (pieri.row r) = _
      refine (ground.famFold_countCollect f (pieri.row r)
        (places.allShapes d m) hbasis).trans ?_
      refine ground.famFold_congr_all Nat.add 0 _ _ ?_
        (places.allShapes d m)
      intro x
      rw [row_removals r x]
    show ground.famFold Nat.add 0 (dnF f) (removals t) = _
    rw [ground.famFold_congr_members Nat.add 0 _ _ (removals t) h2]
    exact (ground.famFold_swap
        (fun r x => ground.countOf r (removals x) * f x)
        (removals t) (places.allShapes d m)).trans
      (ground.famFold_congr_all Nat.add 0
        (fun x => ground.famFold Nat.add 0
          (fun r => ground.countOf r (removals x) * f x) (removals t))
        (fun x => ground.famFold Nat.add 0
          (fun r => ground.countOf r (removals x)) (removals t) * f x)
        (fun x => ground.famFold_mulR (f x)
          (fun r => ground.countOf r (removals x)) (removals t))
        (places.allShapes d m))
  have hL : dnF (upF f) t
      = f t + ground.famFold Nat.add 0
          (fun x => ground.famFold Nat.add 0
            (fun r => ground.countOf r (removals x)) (removals t) * f x)
          (places.allShapes d m) := by
    have h1 : ∀ s, 0 < ground.countOf s (pieri.row t) →
        upF f s = ground.famFold Nat.add 0
          (fun x => ground.countOf x (removals s) * f x)
          (places.allShapes d m) := by
      intro s hs
      obtain ⟨hds, hls⟩ := row_degree t s hs
      have hbasis : ∀ x, 0 < ground.countOf x (removals s) →
          ground.countOf x (places.allShapes d m) = 1 := by
        intro x hx
        obtain ⟨hdx, hlx⟩ := degree_removals s x hx
        have hdm : places.degree x = m := by
          rw [hds, htd] at hdx
          exact Nat.succ.inj hdx
        have hmem : x ∈ places.allShapes d m := by
          have h0 := places.mem_allShapes d x (hlx.trans (hls.trans htl))
          rw [hdm] at h0
          exact h0
        exact Nat.le_antisymm (places.countOf_allShapes_le d m x)
          (ground.countOf_pos_of_mem hmem)
      exact ground.famFold_countCollect f (removals s)
        (places.allShapes d m) hbasis
    have h3 : ∀ x, 0 < ground.countOf x (places.allShapes d m) →
        ground.famFold Nat.add 0
          (fun s => ground.countOf x (removals s) * f x) (pieri.row t)
        = (if x = t then f x else 0)
          + ground.famFold Nat.add 0
              (fun r => ground.countOf r (removals x)) (removals t)
            * f x := by
      intro x _
      have hcc : ground.famFold Nat.add 0
          (fun s => ground.countOf x (removals s) * f x) (pieri.row t)
          = ground.famFold Nat.add 0
            (fun s => ground.countOf s (pieri.row x) * f x)
            (pieri.row t) :=
        ground.famFold_congr_all Nat.add 0 _ _
          (fun s => by rw [row_removals x s]) (pieri.row t)
      rw [hcc, ground.famFold_mulR (f x)
          (fun s => ground.countOf s (pieri.row x)) (pieri.row t),
        cover_count d m t x ht hm, ground.mulAddR]
      refine addCongr ?_ rfl
      by_cases hxt : x = t
      · rw [if_pos hxt, if_pos hxt, Nat.one_mul]
      · rw [if_neg hxt, if_neg hxt, Nat.zero_mul]
    show ground.famFold Nat.add 0 (upF f) (pieri.row t) = _
    rw [ground.famFold_congr_members Nat.add 0 _ _ (pieri.row t) h1]
    refine (ground.famFold_swap
        (fun s x => ground.countOf x (removals s) * f x)
        (pieri.row t) (places.allShapes d m)).trans ?_
    refine (ground.famFold_congr_members Nat.add 0
        (fun x => ground.famFold Nat.add 0
          (fun s => ground.countOf x (removals s) * f x) (pieri.row t))
        (fun x => (if x = t then f x else 0)
          + ground.famFold Nat.add 0
              (fun r => ground.countOf r (removals x)) (removals t)
            * f x)
        (places.allShapes d m) h3).trans ?_
    refine (ground.famFold_add_split
        (fun x => if x = t then f x else 0)
        (fun x => ground.famFold Nat.add 0
          (fun r => ground.countOf r (removals x)) (removals t) * f x)
        (places.allShapes d m)).trans ?_
    refine addCongr ?_ rfl
    have h1t : ground.countOf t (places.allShapes d m) = 1 :=
      Nat.le_antisymm (places.countOf_allShapes_le d m t)
        (ground.countOf_pos_of_mem ht)
    exact ground.famFold_pick f t (places.allShapes d m) h1t
  rw [hL, hR]

/-- The telescope: `D U^{j+1} 1 = (j+1) U^j 1` at every `j < d` —
each cover's path count steps down through its removals, the
commutator peels one copy of the source, and the induction reads
the removals' folds one degree below. -/
private theorem telescope (d : Nat) :
    ∀ j, j < d → ∀ t, t ∈ places.allShapes d j →
      dnF pathCount t = (j + 1) * pathCount t := by
  intro j
  induction j with
  | zero =>
    intro hj t ht
    obtain ⟨htl, htd⟩ := places.allShapes_sound d 0 t ht
    have h1 : ∀ s, 0 < ground.countOf s (pieri.row t) →
        pathCount s = upF pathCount s := by
      intro s hs
      obtain ⟨hds, _⟩ := row_degree t s hs
      rw [htd] at hds
      exact pathCount_step s 0 hds
    have h0 : upF (dnF pathCount) t = 0 := by
      have hvac : ∀ r, 0 < ground.countOf r (removals t) →
          dnF pathCount r = 0 := by
        intro r hr
        obtain ⟨hdr, _⟩ := degree_removals t r hr
        rw [htd] at hdr
        exact Nat.noConfusion hdr
      show ground.famFold Nat.add 0 (dnF pathCount) (removals t) = 0
      rw [ground.famFold_congr_members Nat.add 0 (dnF pathCount)
          (fun _ => 0) (removals t) hvac,
        ground.famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl)
          (removals t)]
    show ground.famFold Nat.add 0 pathCount (pieri.row t)
      = (0 + 1) * pathCount t
    rw [ground.famFold_congr_members Nat.add 0 pathCount
        (upF pathCount) (pieri.row t) h1,
      show ground.famFold Nat.add 0 (upF pathCount) (pieri.row t)
          = pathCount t + upF (dnF pathCount) t
        from duud d 0 hj pathCount t ht,
      h0, Nat.add_zero]
    show pathCount t = 1 * pathCount t
    rw [Nat.one_mul]
  | succ q ih =>
    intro hj t ht
    obtain ⟨htl, htd⟩ := places.allShapes_sound d (q + 1) t ht
    have h1 : ∀ s, 0 < ground.countOf s (pieri.row t) →
        pathCount s = upF pathCount s := by
      intro s hs
      obtain ⟨hds, _⟩ := row_degree t s hs
      rw [htd] at hds
      exact pathCount_step s (q + 1) hds
    have h2 : upF (dnF pathCount) t = (q + 1) * upF pathCount t := by
      have hall : ∀ r, 0 < ground.countOf r (removals t) →
          dnF pathCount r = (q + 1) * pathCount r := by
        intro r hr
        obtain ⟨hdr, hlr⟩ := degree_removals t r hr
        have hdq : places.degree r = q := by
          rw [htd] at hdr
          exact Nat.succ.inj hdr
        have hrm : r ∈ places.allShapes d q := by
          have h0 := places.mem_allShapes d r (hlr.trans htl)
          rw [hdq] at h0
          exact h0
        exact ih (Nat.lt_of_succ_lt hj) r hrm
      show ground.famFold Nat.add 0 (dnF pathCount) (removals t) = _
      rw [ground.famFold_congr_members Nat.add 0 (dnF pathCount)
          (fun r => (q + 1) * pathCount r) (removals t) hall]
      exact (ground.famFold_mul (q + 1) pathCount (removals t)).symm
    have h3 : upF pathCount t = pathCount t :=
      (pathCount_step t q htd).symm
    show ground.famFold Nat.add 0 pathCount (pieri.row t)
      = (q + 1 + 1) * pathCount t
    rw [ground.famFold_congr_members Nat.add 0 pathCount
        (upF pathCount) (pieri.row t) h1,
      show ground.famFold Nat.add 0 (upF pathCount) (pieri.row t)
          = pathCount t + upF (dnF pathCount) t
        from duud d (q + 1) hj pathCount t ht,
      h2, h3, Nat.succ_mul (q + 1) (pathCount t),
      Nat.add_comm (pathCount t) ((q + 1) * pathCount t)]

/-- The path count's square sum: at `k ≤ d` the fold of the squared
path counts over the shapes of `k` boxes at `d` letters is the
factorial — the cover and removal operators transposes for the
shape pairing, `DU = UD + id` at the shapes of fewer than `d` rows,
and the telescope `D U^{j+1} 1 = (j+1) U^j 1` at every `j < d`. -/
theorem squareSum (d k : Nat) (hk : k ≤ d) :
    ground.famFold Nat.add 0 (fun s => pathCount s * pathCount s)
        (places.allShapes d k)
      = ground.factorial k := by
  revert hk
  induction k with
  | zero =>
    intro _
    rw [places.allShapes_zero d]
    have hmem : List.replicate d 0 ∈ places.allShapes d 0 := by
      rw [places.allShapes_zero d]
      exact List.Mem.head []
    have h0 : places.degree (List.replicate d 0) = 0 :=
      (places.allShapes_sound d 0 (List.replicate d 0) hmem).2
    show pathCount (List.replicate d 0) * pathCount (List.replicate d 0)
        + 0
      = ground.factorial 0
    rw [pathCount_vac (List.replicate d 0) h0]
    rfl
  | succ q ih =>
    intro hk
    have hstep : ∀ s, 0 < ground.countOf s (places.allShapes d (q + 1)) →
        pathCount s * pathCount s = upF pathCount s * pathCount s := by
      intro s hs
      obtain ⟨_, hsd⟩ := places.allShapes_sound d (q + 1) s
        (ground.mem_of_countOf_pos s (places.allShapes d (q + 1)) hs)
      exact congrArg (fun w => w * pathCount s) (pathCount_step s q hsd)
    have htel : ∀ t, 0 < ground.countOf t (places.allShapes d q) →
        pathCount t * dnF pathCount t
          = (q + 1) * (pathCount t * pathCount t) := by
      intro t htc
      rw [telescope d q hk t
          (ground.mem_of_countOf_pos t (places.allShapes d q) htc),
        Nat.mul_comm (pathCount t) ((q + 1) * pathCount t),
        ground.mulAssoc (q + 1) (pathCount t) (pathCount t)]
    rw [ground.famFold_congr_members Nat.add 0
        (fun s => pathCount s * pathCount s)
        (fun s => upF pathCount s * pathCount s)
        (places.allShapes d (q + 1)) hstep,
      show ground.famFold Nat.add 0
          (fun s => upF pathCount s * pathCount s)
          (places.allShapes d (q + 1))
        = ground.famFold Nat.add 0
          (fun t => pathCount t * dnF pathCount t)
          (places.allShapes d q)
        from adjoint d q pathCount pathCount]
    refine (ground.famFold_congr_members Nat.add 0
        (fun t => pathCount t * dnF pathCount t)
        (fun t => (q + 1) * (pathCount t * pathCount t))
        (places.allShapes d q) htel).trans ?_
    refine ((ground.famFold_mul (q + 1)
        (fun t => pathCount t * pathCount t)
        (places.allShapes d q)).symm).trans ?_
    rw [ih (Nat.le_of_succ_le hk)]
    rfl

end pathsquare
