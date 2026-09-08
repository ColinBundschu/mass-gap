import MassGap.Places
import MassGap.Genericlift
/-!
`con:states` — the permutation presentation's states.  A factor is
a variable with its dagger read (`Factor`, the pair of the
variable's key and the dagger's read, a variable a link's matrix
at the coefficient carrier), and a factor list fixes the
presentation's site (`FList`).  A generator
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
(`extComb`, the insertion reads' shared carrier).  The wiring
surgery the generator insertions read: a word's dagger read
(`daggerW`), fresh positions padded at the tail (`padW`), a chain of
positions placed at a factor's row or after its column
(`chainAtRow`, `chainAtCol`), the last position contracted through
with a self-wired position a loop at the count (`contractLast`), and
two letters at the last two positions contracted by the Fierz
display, the transposition member at the letters' columns exchanged
and the identity member outright (`fierzT`, `fierzI`).  The unit at
a word's factors, the word's evaluation loops at the count's
cofactor each, joins a state to the site with the word and its
dagger read (`padState`, `invDfP`).  The evaluation contraction
(`con:states`' clause): the contractible pairs (`evalPairs`), one
contraction at the first pair with the further positions moved down
(`evalStep`, `delPos`), the contractions at every factor to closure
with the loops counted (`contractAll`), the residual read at the
site's positions along the relabeling (`relabelTo`, `residualKey`),
and a state's normal form, the entries at their residual keys with
the loops at the coefficients (`normalOf`, `keysOf`, `atKey`,
`siteOf`).
-/

namespace states
open ground places

/-- A factor: the variable's key with the dagger's read. -/
abbrev Factor := Nat × Bool

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

/-- A factor list's dagger read: the reversed list at the dagger reads
flipped, the word `P̄` of a word `P`. -/
def daggerW (P : FList) : FList := (P.reverse).map (fun f => (f.1, !f.2))

/-- The wiring with `t` fresh positions appended at the tail, each
wired to itself until placed. -/
def padW (t : Nat) (π : List Nat) : List Nat :=
  π ++ (List.range t).map (fun s => π.length + s)

/-- A chain of positions `c` placed between `π(k)` and `k` in order:
the first's row against `π(k)`'s column, each further's row against
the prior's column, and `k`'s row against the last's column. -/
def chainAtRow (k : Nat) (c : List Nat) (π : List Nat) : List Nat :=
  match c with
  | [] => π
  | c0 :: cs =>
    let π1 := π.set c0 (getAt 0 π k)
    let π2 := (List.range cs.length).foldl (fun acc s =>
      acc.set (getAt 0 cs s) (getAt 0 (c0 :: cs) s)) π1
    π2.set k (getAt 0 (c0 :: cs) cs.length)

/-- A chain placed after `k`: the first's row against `k`'s column,
each further's row against the prior's column, and the factor whose
row met `k`'s column now meets the last's. -/
def chainAtCol (k : Nat) (c : List Nat) (π : List Nat) : List Nat :=
  match c with
  | [] => π
  | c0 :: cs =>
    let x := places.posOf k π
    let π1 := π.set c0 k
    let π2 := (List.range cs.length).foldl (fun acc s =>
      acc.set (getAt 0 cs s) (getAt 0 (c0 :: cs) s)) π1
    π2.set x (getAt 0 (c0 :: cs) cs.length)

/-- The last position contracted through: the factor whose row met
its column now meets the column its row met; a position wired to
itself is a loop, the count read. -/
def contractLast (π : List Nat) : List Nat × Nat :=
  match π.length with
  | 0 => ([], 0)
  | n + 1 =>
    let L := n
    let out := getAt 0 π L
    let x := places.posOf L π
    if x == L then (π.take n, 1) else ((π.set x out).take n, 0)

/-- Two letters at the last two positions contracted by the Fierz
display: the transposition member exchanges the letters' columns
before contracting both, the identity member contracts them
outright; each returns the wiring with its loop count. -/
def fierzT (π : List Nat) : List Nat × Nat :=
  match π.length with
  | 0 => ([], 0)
  | 1 => ([], 0)
  | n + 2 =>
    let a := getAt 0 π n
    let b := getAt 0 π (n + 1)
    let π' := (π.set n b).set (n + 1) a
    let r1 := contractLast π'
    let r2 := contractLast r1.1
    (r2.1, r1.2 + r2.2)

def fierzI (π : List Nat) : List Nat × Nat :=
  let r1 := contractLast π
  let r2 := contractLast r1.1
  (r2.1, r1.2 + r2.2)

/-- One evaluation contraction: an undaggered and a daggered factor
of one link wired at the product withdraw, the wiring spliced
across the pair, the positions beyond them moved down. -/
def delPos (p : Nat) (π : List Nat) : List Nat :=
  (π.eraseIdx p).map (fun v => if p < v then v - 1 else v)

/-- The count's cofactor `[1 : d_f]`, the loop value's own. -/
def invDfP : poly.PPair := ([⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩])

/-- The unit at a word's factors: a state on the site joined to the
word and its dagger read, each word factor wired in a two-cycle with
its own dagger copy, the loops at the count's cofactor each. -/
def padState (F P : FList) (c : Comb) : Comb :=
  let n := F.length
  let m := P.length
  let loops := (List.range m).map (fun s => n + m + m - 1 - s)
    ++ (List.range m).map (fun s => n + m - 1 - s)
  c.map (fun e => (e.1 ++ loops,
    (List.range m).foldl (fun acc _ => poly.pMul acc invDfP) e.2))

/-- The contractible pairs: an undaggered and a daggered factor of
one link wired at the product, read at the wiring's edges, one
candidate per position (its row against the column it meets). -/
def evalPairs (F : FList) (π : List Nat) : List (Nat × Nat) :=
  (List.range F.length).flatMap (fun a =>
    let b := getAt 0 π a
    let fa := getAt (0, false) F a
    let fb := getAt (0, false) F b
    if fa.1 == fb.1 && fa.2 != fb.2 then
      (if fa.2 == false then [(a, b)] else [(b, a)])
    else [])

/-- One evaluation contraction at the first contractible pair: the
factor whose row met the second's column now meets the column the
first's row met, a pair closing on itself a loop at the count, the
two positions withdrawn with the further positions moved down. -/
def evalStep (F : FList) (π : List Nat) : FList × List Nat × Nat :=
  match evalPairs F π with
  | [] => (F, π, 0)
  | (u, v) :: _ =>
    let fs := if getAt 0 π v == u then (u, v) else (v, u)
    let x := places.posOf fs.2 π
    let loop := if x == fs.1 then 1 else 0
    let π1 := π.set x (getAt 0 π fs.1)
    let hi := if u < v then v else u
    let lo := if u < v then u else v
    ((F.eraseIdx hi).eraseIdx lo, delPos lo (delPos hi π1), loop)

def evalAllGo : Nat → FList → List Nat → Nat → FList × List Nat × Nat
  | 0, F, π, k => (F, π, k)
  | fuel + 1, F, π, k =>
    let r := evalStep F π
    if r.2.1.length == π.length then (F, π, k)
    else evalAllGo fuel r.1 r.2.1 (k + r.2.2)

/-- The evaluation contractions at every factor iterated to closure,
the loops counted. -/
def contractAll (F : FList) (π : List Nat) : FList × List Nat × Nat :=
  evalAllGo F.length F π 0

/-- A factor list's positions read at a further list's, each factor
at the first unmatched position of its own reads. -/
def relabelGo (F : FList) : List Nat → FList → List Nat → List Nat
  | _, [], acc => acc
  | used, f :: G, acc =>
    let p := ((List.range F.length).filter (fun q =>
      getAt (0, false) F q == f && countOf q used == 0)).headD F.length
    relabelGo F (p :: used) G (acc ++ [p])

def relabelTo (F G : FList) : List Nat := relabelGo F [] G []

/-- A residual wiring read at the site's positions: the residual's
factors relabeled to the site's first unmatched positions, the
key their sorted list and the wiring in the key's rank coordinates. -/
def residualKey (F G : FList) (π : List Nat) : List Nat × List Nat :=
  let r := relabelTo F G
  let key := (List.range F.length).filter (fun p => 0 < ground.countOf p r)
  (key, (List.range G.length).map (fun q =>
    let g := places.posOf (getAt 0 key q) r
    places.posOf (getAt 0 r (getAt 0 π g)) key))

/-- A state's entries at their residual keys after every evaluation
contraction, the loops at the coefficient. -/
def normalOf (F : FList) (c : Comb) : List (List Nat × (List Nat × poly.PPair)) :=
  c.map (fun e =>
    let r := contractAll F e.1
    let k := residualKey F r.1 r.2.1
    (k.1, (k.2, poly.pMul e.2 ((List.range r.2.2).foldl (fun acc _ =>
      poly.pMul acc ([⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩])) poly.pOne))))

/-- The residual keys occupied by a state. -/
def keysOf (l : List (List Nat × (List Nat × poly.PPair))) : List (List Nat) :=
  l.foldl (fun acc e => if acc.any (fun k => k == e.1) then acc else acc ++ [e.1]) []

/-- The sub-state at one residual key. -/
def atKey (l : List (List Nat × (List Nat × poly.PPair))) (k : List Nat) : Comb :=
  (l.filter (fun e => e.1 == k)).map (fun e => e.2)

/-- The site's factors at a residual key. -/
def siteOf (F : FList) (k : List Nat) : FList := k.map (fun p => getAt (0, false) F p)

end states
