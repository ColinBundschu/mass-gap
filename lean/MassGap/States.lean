import MassGap.Places
import MassGap.Genericlift
/-!
`con:states` — the permutation presentation's states.  A factor is
a variable with its dagger read, one of the four letters
(`Factor`, the pair of the variable's and the dagger's reads), and
a factor list fixes the presentation's site (`FList`).  A generator
`Φ_π` is indexed by a wiring at the places — `π(i) = j` records
that the row index of factor `i` is contracted against the column
index of factor `j` — the wiring total with every place's value
once (`permAt`); its trace structure is the wiring's cycles
(`places.cyclesOf`, `con:places`' orbit words).  States are the generators' combinations at
polynomial-pair coefficients in the residue (`Comb` at
`lem:genericlift`'s pairs), the trace-polynomial reduction of the
walled Brauer category: the group enters only as the loop value
`d_f` of the calculus, `prop:wg`'s pairing the reads' own
carrier and `rem:kernel`'s word index the combinations' gauge-free
key.  The presentation's product concatenates the sites and blocks
the wirings — the first's wiring against the second's shifted by
the first's site length (`mulComb` at `shiftW`), the coefficients
at the pairs' product — and a state's coefficient at a wiring is
the literal key's fold over the combination (`coeffAtW`, the
generator basis's read).  An action's linear extension over a state
is the per-generator images at the coefficients' products
(`extComb`, the insertion reads' shared carrier).
-/

namespace states
open ground places

/-- A factor: the variable's read with the dagger's, one of the
four letters. -/
abbrev Factor := Bool × Bool

/-- A factor list, the presentation's site. -/
abbrev FList := List Factor

/-- A wiring at the places: the assignment total with every place's
value once. -/
def permAt (π : List Nat) (m : Nat) : Prop :=
  π.length = m
  ∧ ((List.range m).all (fun j => ground.countOf j π == 1)) = true

instance (π : List Nat) (m : Nat) : Decidable (permAt π m) :=
  inferInstanceAs (Decidable (_ ∧ _ = _))

/-- A state: a formal combination of the generators at
polynomial-pair coefficients in the residue, keyed by the
wirings. -/
abbrev Comb := List (List Nat × poly.PPair)

/-- The wiring shifted by an offset, the concatenated site's second
block. -/
def shiftW (n : Nat) (π : List Nat) : List Nat :=
  π.map (fun j => j + n)

/-- The presentation's product: the sites concatenate and the wirings
block, the first's wiring against the second's shifted, the
coefficients at the pairs' product. -/
def mulComb (a b : Comb) : Comb :=
  a.flatMap (fun ea => b.map (fun eb =>
    (ea.1 ++ shiftW ea.1.length eb.1,
     poly.pMul ea.2 eb.2)))

/-- A state's coefficient at a wiring, the literal key's fold — the
generator basis's read (`rem:kernel`'s word coefficient is the class
sum). -/
def coeffAtW (c : Comb) (π : List Nat) : poly.PPair :=
  c.foldl (fun acc e =>
    if e.1 == π then poly.pAdd acc e.2 else acc)
    poly.pZero

/-- An action's linear extension over a state, the per-generator
images at the coefficients' products. -/
def extComb (act : List Nat → Comb) (c : Comb) : Comb :=
  c.flatMap (fun e => (act e.1).map (fun t =>
    (t.1, poly.pMul e.2 t.2)))

/-- A state's key list, one wiring joined per refusal. -/
def suppOf (c : Comb) : List (List Nat) :=
  c.foldl (fun acc e =>
    if acc.any (fun v => v == e.1) then acc else acc ++ [e.1]) []

/-- A state collected at its key list: one entry per occupied
wiring, the key's fold at its reduced representative — the
combination the occupancy family over the wirings (`rem:kernel`'s
projection at the generator keys), every fold over the state
reading the collected form at the key folds' own values, the
representative `lem:genericlift`'s certified reduction. -/
def collect (c : Comb) : Comb :=
  (suppOf c).map (fun w => (w, genericlift.pReduce (coeffAtW c w)))


/-- A wiring's occupied values sit below its width: the width's
values fill the places one each, so every place reads one of them
and an occupied value is its own place's read. -/
theorem permAt_entries {π : List Nat} {m : Nat} (h : permAt π m) :
    ∀ x, 0 < ground.countOf x π → x < m := by
  obtain ⟨hlen, hall⟩ := h
  have hone : ∀ j, j < m → ground.countOf j π = 1 := by
    intro j hj
    exact ground.beqEqOf (ground.all_range_read m hall j hj)
  have hposlt : ∀ j, j < m → places.posOf j π < m := by
    intro j hj
    have hp := places.posOf_lt j π
      (by rw [hone j hj]; exact Nat.succ_pos 0)
    rw [hlen] at hp
    exact hp
  have hPread : ∀ k, k < m →
      ground.getAt 0 ((List.range m).map
        (fun j => places.posOf j π)) k = places.posOf k π := by
    intro k hk
    rw [ground.getAt_map 0 0 (fun j => places.posOf j π)
        (List.range m) k (by rw [ground.length_range]; exact hk),
      ground.getAt_range m k hk]
  have hPlen : ((List.range m).map
      (fun j => places.posOf j π)).length = m := by
    rw [ground.length_map, ground.length_range]
  have hPdist : ∀ x, ground.countOf x ((List.range m).map
      (fun j => places.posOf j π)) ≤ 1 := by
    refine fun x => ground.distinctList_all
      (ground.distinct_of_getAt_inj 0 _ ?_) x
    intro p q hp hq he
    rw [hPlen] at hp hq
    rw [hPread p hp, hPread q hq] at he
    have hgp := places.getAt_posOf p π
      (by rw [hone p hp]; exact Nat.succ_pos 0)
    have hgq := places.getAt_posOf q π
      (by rw [hone q hq]; exact Nat.succ_pos 0)
    rw [← hgp, ← hgq, he]
  have hsat : ∀ i, i < m → 0 < ground.countOf i
      ((List.range m).map (fun j => places.posOf j π)) := by
    intro i hi
    match Nat.eq_zero_or_pos (ground.countOf i
        ((List.range m).map (fun j => places.posOf j π))) with
    | .inr hpos => exact hpos
    | .inl hz =>
      exfalso
      have hcov : ∀ x ∈ (List.range m).map
          (fun j => places.posOf j π),
          x ∈ ground.eraseFirst i (List.range m) := by
        intro x hx
        have hxc := ground.countOf_pos_of_mem hx
        obtain ⟨k, hk, hgk⟩ := ground.getAt_of_mem 0 hx
        rw [hPlen] at hk
        rw [hPread k hk] at hgk
        have hxlt : x < m := by
          rw [← hgk]
          exact hposlt k hk
        have hxne : x ≠ i := by
          intro hxi
          rw [hxi] at hxc
          rw [hz] at hxc
          exact absurd hxc (Nat.lt_irrefl 0)
        refine ground.mem_of_countOf_pos x _ ?_
        rw [ground.countOf_eraseFirst_ne (List.range m) i x hxne,
          ground.countOf_range x m, if_pos hxlt]
        exact Nat.succ_pos 0
      have hiR : 0 < ground.countOf i (List.range m) := by
        rw [ground.countOf_range i m, if_pos hi]
        exact Nat.succ_pos 0
      have hDd : ground.distinctList
          (ground.eraseFirst i (List.range m)) := by
        intro y _
        by_cases hyi : y = i
        · have hself := ground.countOf_eraseFirst_self
            (List.range m) i hiR
          have hR := ground.countOf_range i m
          rw [if_pos hi] at hR
          rw [hR] at hself
          rw [hyi, ← Nat.succ.inj hself]
          exact Nat.le_succ 0
        · rw [ground.countOf_eraseFirst_ne (List.range m) i y hyi,
            ground.countOf_range y m]
          by_cases hym : y < m
          · rw [if_pos hym]
            exact Nat.le_refl 1
          · rw [if_neg hym]
            exact Nat.le_of_lt (Nat.succ_pos 0)
      have hle := ground.length_le_of_distinct_mem
        ((List.range m).map (fun j => places.posOf j π))
        (ground.eraseFirst i (List.range m)) hPdist hcov hDd
      rw [hPlen] at hle
      have hlen2 := ground.length_eraseFirst i (List.range m) hiR
      rw [ground.length_range] at hlen2
      exact absurd (Nat.le_trans (Nat.le_of_eq hlen2) hle)
        (Nat.not_succ_le_self _)
  intro x hx
  have hplt : places.posOf x π < m := by
    have hp := places.posOf_lt x π hx
    rw [hlen] at hp
    exact hp
  obtain ⟨k, hk, hgk⟩ := ground.getAt_of_mem 0
    (ground.mem_of_countOf_pos (places.posOf x π) _
      (hsat (places.posOf x π) hplt))
  rw [hPlen] at hk
  rw [hPread k hk] at hgk
  have hgx := places.getAt_posOf x π hx
  rw [← hgk] at hgx
  rw [places.getAt_posOf k π
    (by rw [hone k hk]; exact Nat.succ_pos 0)] at hgx
  rw [← hgx]
  exact hk


/-- A wiring at the width is an enumeration member, its counts the
unit assignment's own. -/
theorem permAt_member {π : List Nat} {m : Nat} (h : permAt π m) :
    0 < ground.countOf π (places.perms m) := by
  have hone : ∀ j, j < m → ground.countOf j π = 1 := fun j hj =>
    ground.beqEqOf (ground.all_range_read m h.2 j hj)
  have hrng : 0 < ground.countOf (List.range m)
      (places.monomialsAt (List.replicate m 1)) := by
    show 0 < ground.countOf (List.range m) (places.perms m)
    rw [places.countRangePerms m]
    exact Nat.succ_pos 0
  show 0 < ground.countOf π
    (places.monomialsAt (List.replicate m 1))
  refine places.perm_member_of_counts hrng ?_ ?_
  · rw [ground.length_range]
    exact h.1
  · intro x
    rw [ground.countOf_range x m]
    by_cases hx : x < m
    · rw [if_pos hx]
      exact hone x hx
    · rw [if_neg hx]
      match Nat.eq_zero_or_pos (ground.countOf x π) with
      | .inl hz => exact hz
      | .inr hpos => exact absurd (permAt_entries h x hpos) hx

/-- An enumeration member is a wiring at the width, the counts the
member reads' own. -/
theorem member_permAt {π : List Nat} {m : Nat}
    (h : 0 < ground.countOf π (places.perms m)) : permAt π m := by
  obtain ⟨hlen, hdist, _, hocc⟩ := places.perm_member_reads h
  refine ⟨hlen, ground.all_range_intro m ?_⟩
  intro j hj
  exact ground.eqBeqOf (Nat.le_antisymm (hdist j) (hocc j hj))

/-- A value below the shift is absent from the shifted wiring. -/
private theorem countOf_shift_low (la y : Nat) (hy : y < la) :
    ∀ πb : List Nat, ground.countOf y (shiftW la πb) = 0
  | [] => rfl
  | v :: t => by
    show ground.countOf y ((v + la) :: shiftW la t) = 0
    rw [ground.countOf_head_ne
      (Nat.ne_of_lt (Nat.lt_of_lt_of_le hy (Nat.le_add_left la v))),
      countOf_shift_low la y hy t]

/-- The shifted wiring's count at a shifted value is the value's
own. -/
private theorem countOf_shift (la v : Nat) (πb : List Nat) :
    ground.countOf (v + la) (shiftW la πb)
      = ground.countOf v πb := by
  show ground.countOf (v + la) (πb.map (fun j => j + la))
    = ground.countOf v πb
  refine ground.countOf_map_iff (fun j => j + la) πb (v + la) v ?_
  intro w _
  constructor
  · intro he
    exact ground.addCancelR la he
  · intro he
    rw [he]

/-- Two wirings concatenate at the shifted second block, the join
a wiring at the summed width. -/
theorem permAt_concat {πa πb : List Nat} {la lb : Nat}
    (ha : permAt πa la) (hb : permAt πb lb) :
    permAt (πa ++ shiftW la πb) (la + lb) := by
  have honea : ∀ j, j < la → ground.countOf j πa = 1 := fun j hj =>
    ground.beqEqOf (ground.all_range_read la ha.2 j hj)
  have honeb : ∀ j, j < lb → ground.countOf j πb = 1 := fun j hj =>
    ground.beqEqOf (ground.all_range_read lb hb.2 j hj)
  refine ⟨?_, ground.all_range_intro (la + lb) ?_⟩
  · rw [ground.length_append, ha.1]
    show la + (πb.map (fun j => j + la)).length = la + lb
    rw [ground.length_map, hb.1]
  · intro j hj
    refine ground.eqBeqOf ?_
    rw [ground.countOf_append]
    match Nat.lt_or_ge j la with
    | .inl hlt =>
      rw [honea j hlt, countOf_shift_low la j hlt πb]
    | .inr hge =>
      obtain ⟨d, hd⟩ := Nat.le.dest hge
      have hdlb : d < lb := by
        match Nat.lt_or_ge d lb with
        | .inl h1 => exact h1
        | .inr h2 =>
          have hle : la + lb ≤ la + d := Nat.add_le_add_left h2 la
          rw [hd] at hle
          exact absurd (Nat.lt_of_lt_of_le hj hle)
            (Nat.lt_irrefl j)
      have hza : ground.countOf j πa = 0 := by
        match Nat.eq_zero_or_pos (ground.countOf j πa) with
        | .inl hz => exact hz
        | .inr hpos =>
          exact absurd
            (Nat.lt_of_lt_of_le (permAt_entries ha j hpos) hge)
            (Nat.lt_irrefl j)
      have hj2 : j = d + la := by
        rw [Nat.add_comm]
        exact hd.symm
      rw [hza, hj2, countOf_shift la d πb, honeb d hdlb]


/-- The block swap's relabeling at a three-block site: the head
kept in place, the second block read across the third and the
third read back — the concatenated site's two orders one state at
the word index. -/
def swapW (n a b : Nat) : List Nat :=
  List.range n
    ++ (shiftW (n + a) (List.range b) ++ shiftW n (List.range a))

/-- The shifted wiring's place count is the wiring's own. -/
theorem length_shiftW (m : Nat) (π : List Nat) :
    (shiftW m π).length = π.length := by
  show (π.map (fun j => j + m)).length = π.length
  rw [ground.length_map]

/-- The block swap's place count is the site's own. -/
theorem length_swapW (n a b : Nat) :
    (swapW n a b).length = n + (b + a) := by
  show ((List.range n)
    ++ (shiftW (n + a) (List.range b)
      ++ shiftW n (List.range a))).length = n + (b + a)
  rw [ground.length_append, ground.length_range, ground.length_append,
    length_shiftW, length_shiftW, ground.length_range,
    ground.length_range]

/-- The head block's entries are their own keys. -/
theorem getAt_swapW_low (n a b i : Nat) (h : i < n) :
    ground.getAt 0 (swapW n a b) i = i := by
  show ground.getAt 0 ((List.range n)
    ++ (shiftW (n + a) (List.range b)
      ++ shiftW n (List.range a))) i = i
  rw [ground.getAt_append 0 (List.range n) _ i, ground.length_range,
    if_pos h, ground.getAt_range n i h]

/-- The second block's entries read across the third. -/
theorem getAt_swapW_mid (n a b r : Nat) (h : r < b) :
    ground.getAt 0 (swapW n a b) (n + r) = n + (a + r) := by
  show ground.getAt 0 ((List.range n)
    ++ (shiftW (n + a) (List.range b)
      ++ shiftW n (List.range a))) (n + r) = n + (a + r)
  have hk := ground.getAt_append_add 0 (List.range n)
    (shiftW (n + a) (List.range b) ++ shiftW n (List.range a)) r
  rw [ground.length_range] at hk
  rw [hk, ground.getAt_append 0 (shiftW (n + a) (List.range b)) _ r,
    length_shiftW, ground.length_range, if_pos h]
  show ground.getAt 0 ((List.range b).map (fun j => j + (n + a))) r
    = n + (a + r)
  rw [ground.getAt_map 0 0 (fun j => j + (n + a)) (List.range b) r
      (by rw [ground.length_range]; exact h),
    ground.getAt_range b r h, Nat.add_comm r (n + a),
    Nat.add_assoc n a r]

/-- The third block's entries read back. -/
theorem getAt_swapW_high (n a b s : Nat) (h : s < a) :
    ground.getAt 0 (swapW n a b) (n + (b + s)) = n + s := by
  show ground.getAt 0 ((List.range n)
    ++ (shiftW (n + a) (List.range b)
      ++ shiftW n (List.range a))) (n + (b + s)) = n + s
  have hk := ground.getAt_append_add 0 (List.range n)
    (shiftW (n + a) (List.range b) ++ shiftW n (List.range a)) (b + s)
  rw [ground.length_range] at hk
  have hk2 := ground.getAt_append_add 0 (shiftW (n + a) (List.range b))
    (shiftW n (List.range a)) s
  rw [length_shiftW, ground.length_range] at hk2
  rw [hk, hk2]
  show ground.getAt 0 ((List.range a).map (fun j => j + n)) s = n + s
  rw [ground.getAt_map 0 0 (fun j => j + n) (List.range a) s
      (by rw [ground.length_range]; exact h),
    ground.getAt_range a s h, Nat.add_comm s n]

/-- The block swap is a wiring at the concatenated site's count. -/
theorem permAt_swapW (n a b : Nat) :
    permAt (swapW n a b) (n + (a + b)) := by
  refine ⟨?_, ground.all_range_intro (n + (a + b)) ?_⟩
  · rw [length_swapW, Nat.add_comm b a]
  · intro j hj
    refine ground.eqBeqOf ?_
    show ground.countOf j ((List.range n)
      ++ (shiftW (n + a) (List.range b)
        ++ shiftW n (List.range a))) = 1
    rw [ground.countOf_append, ground.countOf_append,
      ground.countOf_range j n]
    match Nat.lt_or_ge j n with
    | .inl hjn =>
      rw [if_pos hjn,
        countOf_shift_low (n + a) j
          (Nat.lt_of_lt_of_le hjn (Nat.le_add_right n a))
          (List.range b),
        countOf_shift_low n j hjn (List.range a)]
    | .inr hge =>
      obtain ⟨d, hd⟩ := Nat.le.dest hge
      have hjd : j = d + n := by
        rw [Nat.add_comm]
        exact hd.symm
      rw [if_neg (fun hc => absurd (Nat.lt_of_lt_of_le hc hge)
        (Nat.lt_irrefl j))]
      match Nat.lt_or_ge j (n + a) with
      | .inl hja =>
        have h0 : d + n < n + a := by
          rw [← hjd]
          exact hja
        have hda : d < a := Nat.lt_of_add_lt_add_right
          (show d + n < a + n from by
            rw [Nat.add_comm a n]
            exact h0)
        rw [countOf_shift_low (n + a) j hja (List.range b), hjd,
          countOf_shift n d (List.range a),
          ground.countOf_range d a, if_pos hda]
      | .inr hge2 =>
        obtain ⟨e, he⟩ := Nat.le.dest hge2
        have hje : j = e + (n + a) := by
          rw [Nat.add_comm]
          exact he.symm
        have h1 : e + (n + a) < n + (a + b) := by
          rw [← hje]
          exact hj
        have h2 : e + (n + a) < b + (n + a) := by
          rw [Nat.add_comm b (n + a), Nat.add_assoc n a b]
          exact h1
        have heb : e < b := Nat.lt_of_add_lt_add_right h2
        rw [hje, countOf_shift (n + a) e (List.range b),
          ground.countOf_range e b, if_pos heb]
        rw [show e + (n + a) = (e + a) + n from by
            rw [Nat.add_assoc e a n, Nat.add_comm a n,
              ← Nat.add_assoc],
          countOf_shift n (e + a) (List.range a),
          ground.countOf_range (e + a) a,
          if_neg (fun hc => absurd (Nat.lt_of_le_of_lt
            (Nat.le_add_left a e) hc) (Nat.lt_irrefl a))]

end states
