import MassGap.Blockcount
import MassGap.Pieri
import MassGap.Dualread
/-!
`lem:adjchar` — the adjoint character: `f ⊗ f̄ = θ ⊕ 1`, and the
adjoint's contents are the letter-pair moves, one place raised and
one lowered, each ordered pair of distinct places once, with the
unit-monomial content at multiplicity `r`.  The content list is the
occupancy read `multRead`, one pass over the content: the all-ones
family reads the residue's count, a family at one place doubled and
one unread with the rest ones reads one, every other family the
fold's unit.  An occupied
read's entries are capped at two with the boxes at the fundamental
count (`multRead_flat`), and its two arms are entrywise
(`multRead_cases`): the unit-monomial content at the residue's
count, or a letter-pair move at one — the raised place at two, the
lowered at the fold's unit, every further place at one.
The reduced shape's own reads are `length_theta` and
`rowList_theta`, the column totals `(2, 1^{d_f - 2}, 0)` — the
Casimir tiers' carrier.  The identity with `def:blockcount`'s
carrier is the general theorem `occupancy`: at every content of the
width the adjoint block's occupancy is the formula's read.  Its
proof transcribes the lemma's own sentences — `f̄` is the one-column
shape at the complement gap and `f̄ ⊗ f` exhausts by the one-box
row (`lem:pieri`), the dominant additions `θ` and the full column
at one block each (`countOf_row_complBox`); the product's contents
are the factors' contents' sums, the one-box block reading each
letter once and `f̄`'s block each withdrawn letter once
(`occ_fused`); `lem:blockcount`(ii)'s content refinement reads the
product's occupancies as the two blocks' at their counts
(`occ_split`); and the full-column line is occupied at the
unit-monomial content alone (`dualread.occ_line`), so `θ`'s
occupancies are the product's with the line's withdrawn.  The
character display `χ_θ + 1 = |tr U|²` and the block splitting land
with the label index's calculus (`prop:repring`'s layer).
-/

namespace adjchar
open ground places

/-- The adjoint's reduced shape `(2, 1^{d_f - 2})` as its column
multiset: one column of length one and one at the fundamental
count's predecessor, the two joining at `d_f = 2`. -/
def theta (d : Nat) : Shape :=
  ground.bumpAt 0 (ground.bumpAt (d - 2) (List.replicate d 0))

/-- The adjoint's degree is the fundamental count, its two
columns' boxes at the one-box and the deep column
(`lem:adjchar`'s shape). -/
theorem degree_theta (d : Nat) (hd : 2 ≤ d) :
    places.degree (theta d) = d := by
  match Nat.le.dest hd with
  | ⟨e, he⟩ =>
    have hde : d = e + 2 := by rw [← he, Nat.add_comm]
    subst hde
    have h1 : places.degree
        (ground.bumpAt e (List.replicate (e + 2) 0)) = e + 1 := by
      rw [places.degree_bumpAt e (List.replicate (e + 2) 0)
          (by rw [ground.length_replicate]
              exact Nat.lt_add_of_pos_right Nat.zero_lt_two)]
      show ground.sumNat (places.rowList (List.replicate (e + 2) 0))
        + (e + 1) = e + 1
      rw [places.rowList_replicate_zero (e + 2),
        ground.sumNat_replicate_zero (e + 2), Nat.zero_add]
    show places.degree (ground.bumpAt 0
      (ground.bumpAt (e + 2 - 2) (List.replicate (e + 2) 0))) = e + 2
    rw [places.degree_bumpAt 0
        (ground.bumpAt (e + 2 - 2) (List.replicate (e + 2) 0))
        (by rw [ground.length_bumpAt, ground.length_replicate]
            exact Nat.succ_pos (e + 1))]
    show places.degree
      (ground.bumpAt e (List.replicate (e + 2) 0)) + (0 + 1) = e + 2
    rw [h1]

/-- The adjoint's shape has the fundamental count's length. -/
theorem length_theta (d : Nat) : (theta d).length = d := by
  show (ground.bumpAt 0
      (ground.bumpAt (d - 2) (List.replicate d 0))).length = d
  rw [ground.length_bumpAt, ground.length_bumpAt,
    ground.length_replicate]

/-- The raised vacancy family's total is one box. -/
private theorem sumNat_bumpRep (g : Nat) :
    ground.sumNat (ground.bumpAt g (List.replicate (g + 2) 0)) = 1 := by
  rw [ground.sumNat_bumpAt g (List.replicate (g + 2) 0)
      (by rw [ground.length_replicate]
          exact Nat.lt_succ_of_le (Nat.le_succ g)),
    ground.sumNat_replicate_zero (g + 2)]

/-- The raised vacancy family's row list is the unit rows over the
trailing vacancy. -/
private theorem rowList_bumpRep : ∀ g : Nat,
    places.rowList (ground.bumpAt g (List.replicate (g + 2) 0))
      = List.replicate (g + 1) 1 ++ [0]
  | 0 => rfl
  | g + 1 => by
    show (0 + ground.sumNat (ground.bumpAt g (List.replicate (g + 2) 0)))
        :: places.rowList (ground.bumpAt g (List.replicate (g + 2) 0))
      = 1 :: (List.replicate (g + 1) 1 ++ [0])
    rw [sumNat_bumpRep g, rowList_bumpRep g, Nat.zero_add 1]

/-- `θ`'s row list, the reduced shape `(2, 1^{d_f - 2})` read as
column totals: the doubled head over the unit rows with the
trailing vacancy. -/
theorem rowList_theta : ∀ g : Nat,
    places.rowList (theta (g + 2)) = 2 :: (List.replicate g 1 ++ [0])
  | 0 => rfl
  | g + 1 => by
    show (1 + ground.sumNat (ground.bumpAt g (List.replicate (g + 2) 0)))
        :: places.rowList (ground.bumpAt g (List.replicate (g + 2) 0))
      = 2 :: (List.replicate (g + 1) 1 ++ [0])
    rw [sumNat_bumpRep g, rowList_bumpRep g]

/-- The content list read entrywise, one pass over the content at
the fundamental count: the two flags record a vacancy and a double
seen, a letter at one keeps them, and a second vacancy, a second
double, a letter beyond two or a width off the count reads off the
list. -/
private def multScan :
    Bool → Bool → Nat → List Nat → Option (Bool × Bool)
  | z, w, 0, [] => some (z, w)
  | _, _, _ + 1, [] => none
  | _, _, 0, _ :: _ => none
  | z, w, r + 1, e :: t =>
    if e = 1 then multScan z w r t
    else if e = 0 then (if z then none else multScan true w r t)
    else if e = 2 then (if w then none else multScan z true r t)
    else none

/-- The adjoint's content read: the unit-monomial content at the
residue's count `d_f - 1`, a letter-pair move at one, every other
family the fold's unit, the scan's two occupied states at their
values. -/
def multRead (d : Nat) (m : List Nat) : Nat :=
  if multScan false false d m = some (false, false) then d - 1
  else if multScan false false d m = some (true, true) then 1
  else 0

private theorem scan_cons (z w : Bool) (r e : Nat) (t : List Nat) :
    multScan z w (r + 1) (e :: t)
      = (if e = 1 then multScan z w r t
        else if e = 0 then (if z then none else multScan true w r t)
        else if e = 2 then (if w then none else multScan z true r t)
        else none) := rfl

/-- The all-ones family's reads: every entry at most two, the sum
the length, and every entry below the length the fold's unit. -/
private theorem ones_read : ∀ (l : List Nat),
    ground.countOf 1 l = l.length →
    (∀ i, ground.getAt 0 l i ≤ 2) ∧ sumNat l = l.length
      ∧ (∀ k, k < l.length → ground.getAt 0 l k = 1)
  | [], _ =>
    ⟨fun _ => Nat.zero_le 2, rfl,
      fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | b :: t, h => by
    have h' : (if (1 : Nat) = b then 1 else 0)
        + ground.countOf 1 t = t.length + 1 :=
      (ground.countOf_cons 1 b t).symm.trans h
    by_cases hb1 : (1 : Nat) = b
    · rw [if_pos hb1] at h'
      have hct : ground.countOf 1 t = t.length := by
        refine ground.addCancelR 1 ?_
        rw [Nat.add_comm (ground.countOf 1 t) 1]
        exact h'
      obtain ⟨hent, hsum, hone⟩ := ones_read t hct
      refine ⟨?_, ?_, ?_⟩
      · intro i
        match i with
        | 0 =>
          show b ≤ 2
          rw [← hb1]
          exact Nat.le_succ 1
        | i + 1 => exact hent i
      · show b + sumNat t = t.length + 1
        rw [← hb1, hsum, Nat.add_comm 1 t.length]
      · intro k hk
        match k with
        | 0 => exact hb1.symm
        | k + 1 => exact hone k (Nat.lt_of_succ_lt_succ hk)
    · rw [if_neg hb1, Nat.zero_add] at h'
      have hle := ground.countOf_le_length 1 t
      rw [h'] at hle
      exact absurd hle (Nat.not_succ_le_self t.length)

/-- The head indicators of the three low values total at most
one. -/
private theorem ind3 (b : Nat) :
    (if (0 : Nat) = b then 1 else 0)
      + (if (1 : Nat) = b then 1 else 0)
      + (if (2 : Nat) = b then 1 else 0) ≤ 1 := by
  match b with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | b + 3 =>
    rw [if_neg (fun hh => Nat.noConfusion hh),
      if_neg (fun hh => Nat.noConfusion (Nat.succ.inj hh)),
      if_neg (fun hh =>
        Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hh)))]
    exact Nat.zero_le 1

/-- Three distinct values' counts total at most the length. -/
private theorem three_le : ∀ (l : List Nat),
    ground.countOf 0 l + ground.countOf 1 l + ground.countOf 2 l
      ≤ l.length
  | [] => Nat.le_refl 0
  | b :: t => by
    rw [ground.countOf_cons, ground.countOf_cons,
      ground.countOf_cons]
    show (if (0 : Nat) = b then 1 else 0) + ground.countOf 0 t
        + ((if (1 : Nat) = b then 1 else 0) + ground.countOf 1 t)
        + ((if (2 : Nat) = b then 1 else 0) + ground.countOf 2 t)
      ≤ t.length + 1
    rw [Nat.add_add_add_comm (if (0 : Nat) = b then 1 else 0)
      (ground.countOf 0 t) (if (1 : Nat) = b then 1 else 0)
      (ground.countOf 1 t),
      Nat.add_add_add_comm ((if (0 : Nat) = b then 1 else 0)
        + (if (1 : Nat) = b then 1 else 0))
      (ground.countOf 0 t + ground.countOf 1 t)
      (if (2 : Nat) = b then 1 else 0) (ground.countOf 2 t)]
    refine Nat.le_trans (Nat.add_le_add_right (ind3 b) _) ?_
    refine Nat.le_trans (Nat.add_le_add_left (three_le t) 1) ?_
    rw [Nat.add_comm 1 t.length]
    exact Nat.le_refl _

/-- A family whose three low counts fill its length reads every
entry at most two and its sum at the middle count joined to the
top count's double. -/
private theorem three_read : ∀ (l : List Nat),
    ground.countOf 0 l + ground.countOf 1 l + ground.countOf 2 l
      = l.length →
    (∀ i, ground.getAt 0 l i ≤ 2)
      ∧ sumNat l
        = ground.countOf 1 l + 2 * ground.countOf 2 l
  | [], _ => ⟨fun _ => Nat.zero_le 2, rfl⟩
  | b :: t, h => by
    have h' : ((if (0 : Nat) = b then 1 else 0)
          + (if (1 : Nat) = b then 1 else 0)
          + (if (2 : Nat) = b then 1 else 0))
        + (ground.countOf 0 t + ground.countOf 1 t
          + ground.countOf 2 t)
        = t.length + 1 := by
      rw [← Nat.add_add_add_comm ((if (0 : Nat) = b then 1 else 0)
          + (if (1 : Nat) = b then 1 else 0))
        (ground.countOf 0 t + ground.countOf 1 t)
        (if (2 : Nat) = b then 1 else 0) (ground.countOf 2 t),
        ← Nat.add_add_add_comm (if (0 : Nat) = b then 1 else 0)
        (ground.countOf 0 t) (if (1 : Nat) = b then 1 else 0)
        (ground.countOf 1 t),
        ← ground.countOf_cons, ← ground.countOf_cons,
        ← ground.countOf_cons]
      exact h
    match b with
    | 0 =>
      have h1 : 1 + (ground.countOf 0 t + ground.countOf 1 t
          + ground.countOf 2 t) = t.length + 1 := h'
      have hS : ground.countOf 0 t + ground.countOf 1 t
          + ground.countOf 2 t = t.length := by
        refine ground.addCancelR 1 ?_
        rw [Nat.add_comm _ 1]
        exact h1
      obtain ⟨hent, hsum⟩ := three_read t hS
      refine ⟨?_, ?_⟩
      · intro i
        match i with
        | 0 => exact Nat.zero_le 2
        | i + 1 => exact hent i
      · show 0 + sumNat t
          = (0 + ground.countOf 1 t) + 2 * (0 + ground.countOf 2 t)
        rw [Nat.zero_add, Nat.zero_add, Nat.zero_add, hsum]
    | 1 =>
      have h1 : 1 + (ground.countOf 0 t + ground.countOf 1 t
          + ground.countOf 2 t) = t.length + 1 := h'
      have hS : ground.countOf 0 t + ground.countOf 1 t
          + ground.countOf 2 t = t.length := by
        refine ground.addCancelR 1 ?_
        rw [Nat.add_comm _ 1]
        exact h1
      obtain ⟨hent, hsum⟩ := three_read t hS
      refine ⟨?_, ?_⟩
      · intro i
        match i with
        | 0 => exact Nat.le_succ 1
        | i + 1 => exact hent i
      · show 1 + sumNat t
          = (1 + ground.countOf 1 t) + 2 * (0 + ground.countOf 2 t)
        rw [Nat.zero_add, hsum,
          Nat.add_assoc 1 (ground.countOf 1 t)
            (2 * ground.countOf 2 t)]
    | 2 =>
      have h1 : 1 + (ground.countOf 0 t + ground.countOf 1 t
          + ground.countOf 2 t) = t.length + 1 := h'
      have hS : ground.countOf 0 t + ground.countOf 1 t
          + ground.countOf 2 t = t.length := by
        refine ground.addCancelR 1 ?_
        rw [Nat.add_comm _ 1]
        exact h1
      obtain ⟨hent, hsum⟩ := three_read t hS
      refine ⟨?_, ?_⟩
      · intro i
        match i with
        | 0 => exact Nat.le_refl 2
        | i + 1 => exact hent i
      · show 2 + sumNat t
          = (0 + ground.countOf 1 t) + 2 * (1 + ground.countOf 2 t)
        rw [Nat.zero_add, hsum, Nat.add_comm 1 (ground.countOf 2 t),
          Nat.mul_succ 2 (ground.countOf 2 t),
          ← Nat.add_assoc (ground.countOf 1 t)
            (2 * ground.countOf 2 t) 2,
          Nat.add_comm
            (ground.countOf 1 t + 2 * ground.countOf 2 t) 2]
    | b + 3 =>
      have h0 : 0 + (ground.countOf 0 t + ground.countOf 1 t
          + ground.countOf 2 t) = t.length + 1 := h'
      rw [Nat.zero_add] at h0
      have hle := three_le t
      rw [h0] at hle
      exact absurd hle (Nat.not_succ_le_self t.length)

/-- An occupied scan reads its counts: the width at the count, the
vacancies and the doubles each at most one joined to the flags, and
the three low counts filling the width. -/
private theorem scan_some : ∀ (t : List Nat) (z w : Bool) (r : Nat)
    (z' w' : Bool), multScan z w r t = some (z', w') →
    r = t.length
      ∧ ground.countOf 0 t + (if z then 1 else 0) = (if z' then 1 else 0)
      ∧ ground.countOf 2 t + (if w then 1 else 0) = (if w' then 1 else 0)
      ∧ ground.countOf 0 t + ground.countOf 1 t + ground.countOf 2 t
          = t.length
  | [], z, w, 0, z', w', h => by
    have h' : (z, w) = (z', w') := Option.some.inj h
    have hz : z = z' := congrArg Prod.fst h'
    have hw : w = w' := congrArg Prod.snd h'
    rw [← hz, ← hw]
    exact ⟨rfl, Nat.zero_add _, Nat.zero_add _, rfl⟩
  | [], _, _, _ + 1, _, _, h => nomatch h
  | _ :: _, _, _, 0, _, _, h => nomatch h
  | e :: t, z, w, r + 1, z', w', h => by
    rw [scan_cons] at h
    match e, h with
    | 1, h =>
      rw [if_pos rfl] at h
      obtain ⟨hr, h0, h2, hs⟩ := scan_some t z w r z' w' h
      refine ⟨?_, ?_, ?_, ?_⟩
      · show r + 1 = t.length + 1
        rw [hr]
      · rw [ground.countOf_cons 0 1 t, if_neg (fun he => Nat.noConfusion he),
          Nat.zero_add]
        exact h0
      · rw [ground.countOf_cons 2 1 t,
          if_neg (fun he => Nat.noConfusion (Nat.succ.inj he)),
          Nat.zero_add]
        exact h2
      · rw [ground.countOf_cons 0 1 t, ground.countOf_cons 1 1 t,
          ground.countOf_cons 2 1 t, if_neg (fun he => Nat.noConfusion he),
          if_pos rfl, if_neg (fun he => Nat.noConfusion (Nat.succ.inj he)),
          Nat.zero_add, Nat.zero_add]
        show ground.countOf 0 t + (1 + ground.countOf 1 t)
          + ground.countOf 2 t = t.length + 1
        rw [Nat.add_comm 1 (ground.countOf 1 t),
          ← Nat.add_assoc (ground.countOf 0 t) (ground.countOf 1 t) 1,
          Nat.add_right_comm (ground.countOf 0 t + ground.countOf 1 t) 1
            (ground.countOf 2 t), hs]
    | 0, h =>
      rw [if_neg (fun he => Nat.noConfusion he), if_pos rfl] at h
      match z, h with
      | true, h =>
        rw [if_pos rfl] at h
        exact nomatch h
      | false, h =>
        rw [if_neg (fun he => Bool.noConfusion he)] at h
        obtain ⟨hr, h0, h2, hs⟩ := scan_some t true w r z' w' h
        refine ⟨?_, ?_, ?_, ?_⟩
        · show r + 1 = t.length + 1
          rw [hr]
        · rw [ground.countOf_cons 0 0 t, if_pos rfl]
          show 1 + ground.countOf 0 t + 0 = _
          rw [Nat.add_zero, Nat.add_comm 1 (ground.countOf 0 t)]
          exact h0
        · rw [ground.countOf_cons 2 0 t,
            if_neg (fun he => Nat.noConfusion he), Nat.zero_add]
          exact h2
        · rw [ground.countOf_cons 0 0 t, ground.countOf_cons 1 0 t,
            ground.countOf_cons 2 0 t, if_pos rfl,
            if_neg (fun he => Nat.noConfusion he),
            if_neg (fun he => Nat.noConfusion he),
            Nat.zero_add, Nat.zero_add]
          show 1 + ground.countOf 0 t + ground.countOf 1 t
            + ground.countOf 2 t = t.length + 1
          rw [Nat.add_comm 1 (ground.countOf 0 t),
            Nat.add_right_comm (ground.countOf 0 t) 1 (ground.countOf 1 t),
            Nat.add_right_comm (ground.countOf 0 t + ground.countOf 1 t) 1
              (ground.countOf 2 t), hs]
    | 2, h =>
      rw [if_neg (fun he => Nat.noConfusion (Nat.succ.inj he)),
        if_neg (fun he => Nat.noConfusion he), if_pos rfl] at h
      match w, h with
      | true, h =>
        rw [if_pos rfl] at h
        exact nomatch h
      | false, h =>
        rw [if_neg (fun he => Bool.noConfusion he)] at h
        obtain ⟨hr, h0, h2, hs⟩ := scan_some t z true r z' w' h
        refine ⟨?_, ?_, ?_, ?_⟩
        · show r + 1 = t.length + 1
          rw [hr]
        · rw [ground.countOf_cons 0 2 t,
            if_neg (fun he => Nat.noConfusion he), Nat.zero_add]
          exact h0
        · rw [ground.countOf_cons 2 2 t, if_pos rfl]
          show 1 + ground.countOf 2 t + 0 = _
          rw [Nat.add_zero, Nat.add_comm 1 (ground.countOf 2 t)]
          exact h2
        · rw [ground.countOf_cons 0 2 t, ground.countOf_cons 1 2 t,
            ground.countOf_cons 2 2 t,
            if_neg (fun he => Nat.noConfusion he),
            if_neg (fun he => Nat.noConfusion (Nat.succ.inj he)),
            if_pos rfl, Nat.zero_add, Nat.zero_add]
          show ground.countOf 0 t + ground.countOf 1 t
            + (1 + ground.countOf 2 t) = t.length + 1
          rw [Nat.add_comm 1 (ground.countOf 2 t),
            ← Nat.add_assoc (ground.countOf 0 t + ground.countOf 1 t)
              (ground.countOf 2 t) 1, hs]
    | _ + 3, h =>
      rw [if_neg (fun he => Nat.noConfusion (Nat.succ.inj he)),
        if_neg (fun he => Nat.noConfusion he),
        if_neg (fun he => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj he)))]
        at h
      exact nomatch h

/-- The counts read an occupied scan: at the width, with the
vacancies and the doubles each at most one joined to the flags and
the three low counts filling the width, the scan is occupied. -/
private theorem scan_of : ∀ (t : List Nat) (z w : Bool) (r : Nat),
    r = t.length →
    ground.countOf 0 t + (if z then 1 else 0) ≤ 1 →
    ground.countOf 2 t + (if w then 1 else 0) ≤ 1 →
    ground.countOf 0 t + ground.countOf 1 t + ground.countOf 2 t
      = t.length →
    ∃ z' w', multScan z w r t = some (z', w')
  | [], z, w, 0, _, _, _, _ => ⟨z, w, rfl⟩
  | [], _, _, _ + 1, hr, _, _, _ => Nat.noConfusion hr
  | _ :: _, _, _, 0, hr, _, _, _ => Nat.noConfusion hr
  | e :: t, z, w, r + 1, hr, h0, h2, hs => by
    have hr' : r = t.length := Nat.succ.inj hr
    have hs' : ((if (0 : Nat) = e then 1 else 0) + ground.countOf 0 t)
        + ((if (1 : Nat) = e then 1 else 0) + ground.countOf 1 t)
        + ((if (2 : Nat) = e then 1 else 0) + ground.countOf 2 t)
        = t.length + 1 := by
      rw [← ground.countOf_cons, ← ground.countOf_cons,
        ← ground.countOf_cons]
      exact hs
    rw [ground.countOf_cons 0 e t] at h0
    rw [ground.countOf_cons 2 e t] at h2
    rw [scan_cons]
    match e, h0, h2, hs' with
    | 1, h0, h2, hs' =>
      rw [if_pos rfl]
      rw [if_neg (fun he => Nat.noConfusion he), Nat.zero_add] at h0
      rw [if_neg (fun he => Nat.noConfusion (Nat.succ.inj he)), Nat.zero_add]
        at h2
      rw [if_neg (fun he => Nat.noConfusion he), if_pos rfl,
        if_neg (fun he => Nat.noConfusion (Nat.succ.inj he)),
        Nat.zero_add, Nat.zero_add, Nat.add_comm 1 (ground.countOf 1 t),
        ← Nat.add_assoc (ground.countOf 0 t) (ground.countOf 1 t) 1,
        Nat.add_right_comm (ground.countOf 0 t + ground.countOf 1 t) 1
          (ground.countOf 2 t)] at hs'
      exact scan_of t z w r hr' h0 h2 (ground.addCancelR 1 hs')
    | 0, h0, h2, hs' =>
      rw [if_neg (fun he => Nat.noConfusion he), if_pos rfl]
      rw [if_pos rfl] at h0
      rw [if_neg (fun he => Nat.noConfusion he), Nat.zero_add] at h2
      rw [if_pos rfl, if_neg (fun he => Nat.noConfusion he),
        if_neg (fun he => Nat.noConfusion he), Nat.zero_add, Nat.zero_add,
        Nat.add_comm 1 (ground.countOf 0 t),
        Nat.add_right_comm (ground.countOf 0 t) 1 (ground.countOf 1 t),
        Nat.add_right_comm (ground.countOf 0 t + ground.countOf 1 t) 1
          (ground.countOf 2 t)] at hs'
      match z, h0 with
      | true, h0 =>
        exact absurd (Nat.le_trans (Nat.succ_le_succ
          (Nat.le_add_right 1 (ground.countOf 0 t))) h0) (by decide +kernel)
      | false, h0 =>
        rw [if_neg (fun he => Bool.noConfusion he)]
        refine scan_of t true w r hr' ?_ h2 (ground.addCancelR 1 hs')
        show ground.countOf 0 t + 1 ≤ 1
        rw [Nat.add_comm]
        exact h0
    | 2, h0, h2, hs' =>
      rw [if_neg (fun he => Nat.noConfusion (Nat.succ.inj he)),
        if_neg (fun he => Nat.noConfusion he), if_pos rfl]
      rw [if_neg (fun he => Nat.noConfusion he), Nat.zero_add] at h0
      rw [if_pos rfl] at h2
      rw [if_neg (fun he => Nat.noConfusion he),
        if_neg (fun he => Nat.noConfusion (Nat.succ.inj he)), if_pos rfl,
        Nat.zero_add, Nat.zero_add, Nat.add_comm 1 (ground.countOf 2 t),
        ← Nat.add_assoc (ground.countOf 0 t + ground.countOf 1 t)
          (ground.countOf 2 t) 1] at hs'
      match w, h2 with
      | true, h2 =>
        exact absurd (Nat.le_trans (Nat.succ_le_succ
          (Nat.le_add_right 1 (ground.countOf 2 t))) h2) (by decide +kernel)
      | false, h2 =>
        rw [if_neg (fun he => Bool.noConfusion he)]
        refine scan_of t z true r hr' h0 ?_ (ground.addCancelR 1 hs')
        show ground.countOf 2 t + 1 ≤ 1
        rw [Nat.add_comm]
        exact h2
    | _ + 3, _, _, hs' =>
      rw [if_neg (fun he => Nat.noConfusion he),
        if_neg (fun he => Nat.noConfusion (Nat.succ.inj he)),
        if_neg (fun he => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj he))),
        Nat.zero_add, Nat.zero_add, Nat.zero_add] at hs'
      have hle := three_le t
      rw [hs'] at hle
      exact absurd hle (Nat.not_succ_le_self t.length)

/-- The unit-monomial content reads the residue's count. -/
theorem multRead_ones (d : Nat) :
    multRead d (List.replicate d 1) = d - 1 := by
  have hc0 : ground.countOf 0 (List.replicate d 1) = 0 :=
    ground.countOf_replicate_ne 0 1 (fun he => Nat.noConfusion he) d
  have hc2 : ground.countOf 2 (List.replicate d 1) = 0 :=
    ground.countOf_replicate_ne 2 1
      (fun he => Nat.noConfusion (Nat.succ.inj he)) d
  obtain ⟨z', w', h⟩ := scan_of (List.replicate d 1) false false d
    (ground.length_replicate 1 d).symm
    (by rw [hc0]; exact Nat.zero_le 1) (by rw [hc2]; exact Nat.zero_le 1)
    (by rw [hc0, hc2, ground.countOf_replicate 1 d, ground.length_replicate,
      Nat.zero_add, Nat.add_zero])
  obtain ⟨_, h0, h2, _⟩ := scan_some _ false false d z' w' h
  rw [hc0] at h0
  rw [hc2] at h2
  have hz : z' = false := by
    match z', h0 with
    | false, _ => rfl
    | true, h0 => exact absurd h0 (by decide +kernel)
  have hw : w' = false := by
    match w', h2 with
    | false, _ => rfl
    | true, h2 => exact absurd h2 (by decide +kernel)
  rw [hz, hw] at h
  show (if multScan false false d (List.replicate d 1) = some (false, false)
      then d - 1
      else if multScan false false d (List.replicate d 1) = some (true, true)
        then 1 else 0) = d - 1
  rw [if_pos h]

/-- The content read's letter-pair arm at the explicit counts: the
single vacancy against the single double over the unit places. -/
theorem multRead_move (d : Nat) (m : List Nat) (hl : m.length = d)
    (hc0 : ground.countOf 0 m = 1) (hc2 : ground.countOf 2 m = 1)
    (hc1 : ground.countOf 1 m + 2 = d) : multRead d m = 1 := by
  obtain ⟨z', w', h⟩ := scan_of m false false d hl.symm
    (by rw [hc0]; exact Nat.le_refl 1) (by rw [hc2]; exact Nat.le_refl 1)
    (by rw [hc0, hc2, hl, ← hc1]
        exact (Nat.add_right_comm 1 (ground.countOf 1 m) 1).trans
          (Nat.add_comm (1 + 1) (ground.countOf 1 m)))
  obtain ⟨_, h0, h2, _⟩ := scan_some _ false false d z' w' h
  rw [hc0] at h0
  rw [hc2] at h2
  have hz : z' = true := by
    match z', h0 with
    | true, _ => rfl
    | false, h0 => exact absurd h0 (by decide +kernel)
  have hw : w' = true := by
    match w', h2 with
    | true, _ => rfl
    | false, h2 => exact absurd h2 (by decide +kernel)
  rw [hz, hw] at h
  have hne : ¬ multScan false false d m = some (false, false) := by
    rw [h]
    decide +kernel
  show (if multScan false false d m = some (false, false) then d - 1
      else if multScan false false d m = some (true, true) then 1 else 0)
    = 1
  rw [if_neg hne, if_pos h]

/-- A content read off the fold's unit is capped entrywise at two
with the boxes at the fundamental count. -/
theorem multRead_flat (d : Nat) (m : List Nat)
    (hpos : 0 < multRead d m) :
    (∀ i, ground.getAt 0 m i ≤ 2) ∧ ground.sumNat m = d := by
  by_cases hA : multScan false false d m = some (false, false)
  · obtain ⟨hl, h0, h2, hs⟩ := scan_some m false false d false false hA
    have h0' : ground.countOf 0 m + 0 = 0 := h0
    have h2' : ground.countOf 2 m + 0 = 0 := h2
    rw [Nat.add_zero] at h0' h2'
    rw [h0', h2', Nat.zero_add, Nat.add_zero] at hs
    obtain ⟨hent, hsum, _⟩ := ones_read m hs
    exact ⟨hent, hsum.trans hl.symm⟩
  · by_cases hB : multScan false false d m = some (true, true)
    · obtain ⟨hl, h0, h2, hs⟩ := scan_some m false false d true true hB
      have h0' : ground.countOf 0 m + 0 = 1 := h0
      have h2' : ground.countOf 2 m + 0 = 1 := h2
      rw [Nat.add_zero] at h0' h2'
      obtain ⟨hent, hsum⟩ := three_read m hs
      refine ⟨hent, ?_⟩
      rw [hsum, h2', Nat.mul_one, hl, ← hs, h0', h2']
      exact ((Nat.add_right_comm 1 (ground.countOf 1 m) 1).trans
        (Nat.add_comm (1 + 1) (ground.countOf 1 m))).symm
    · have h0 : multRead d m = 0 := by
        show (if multScan false false d m = some (false, false) then d - 1
            else if multScan false false d m = some (true, true) then 1
            else 0) = 0
        rw [if_neg hA, if_neg hB]
      rw [h0] at hpos
      exact absurd hpos (Nat.lt_irrefl 0)

/-- A value at or below two off both the vacancy and the double is
the fold's unit. -/
private theorem le_two_read :
    ∀ v : Nat, v ≤ 2 → ¬ v = 0 → ¬ v = 2 → v = 1
  | 0, _, h0, _ => absurd rfl h0
  | 1, _, _, _ => rfl
  | 2, _, _, h2 => absurd rfl h2
  | v + 3, hle, _, _ =>
    absurd (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hle))
      (Nat.not_succ_le_zero v)

/-- The content read's two occupied arms, entrywise: the
unit-monomial content at the residue's count, or a letter-pair move
at one, the raised place at two, the lowered at the fold's unit,
every further place at one. -/
theorem multRead_cases (d : Nat) (m : List Nat)
    (hpos : 0 < multRead d m) :
    (m.length = d ∧ (∀ k, k < d → ground.getAt 0 m k = 1)
      ∧ multRead d m = d - 1)
    ∨ (m.length = d
      ∧ (∃ i, i < d ∧ ∃ j, j < d ∧ ¬ i = j
          ∧ ground.getAt 0 m i = 2 ∧ ground.getAt 0 m j = 0
          ∧ (∀ k, k < d → ¬ k = i → ¬ k = j
              → ground.getAt 0 m k = 1))
      ∧ multRead d m = 1) := by
  by_cases hA : multScan false false d m = some (false, false)
  · obtain ⟨hl, h0, h2, hs⟩ := scan_some m false false d false false hA
    have h0' : ground.countOf 0 m + 0 = 0 := h0
    have h2' : ground.countOf 2 m + 0 = 0 := h2
    rw [Nat.add_zero] at h0' h2'
    rw [h0', h2', Nat.zero_add, Nat.add_zero] at hs
    obtain ⟨_, _, hone⟩ := ones_read m hs
    refine Or.inl ⟨hl.symm, ?_, ?_⟩
    · intro k hk
      refine hone k ?_
      rw [← hl]
      exact hk
    · show (if multScan false false d m = some (false, false) then d - 1
          else if multScan false false d m = some (true, true) then 1
          else 0) = d - 1
      rw [if_pos hA]
  · by_cases hB : multScan false false d m = some (true, true)
    · obtain ⟨hl, h0, h2, _⟩ := scan_some m false false d true true hB
      have hld : m.length = d := hl.symm
      have hc0d : ground.countOf 0 m + 0 = 1 := h0
      have hc2d : ground.countOf 2 m + 0 = 1 := h2
      rw [Nat.add_zero] at hc0d hc2d
      have hcap : ∀ i, ground.getAt 0 m i ≤ 2 :=
        (multRead_flat d m hpos).1
      have hm2 : (2 : Nat) ∈ m :=
        ground.mem_of_countOf_pos 2 m
          (by rw [hc2d]; exact Nat.succ_pos 0)
      have hm0 : (0 : Nat) ∈ m :=
        ground.mem_of_countOf_pos 0 m
          (by rw [hc0d]; exact Nat.succ_pos 0)
      obtain ⟨i, hi, hiv⟩ := ground.getAt_of_mem 0 hm2
      obtain ⟨j, hj, hjv⟩ := ground.getAt_of_mem 0 hm0
      have hid : i < d := by
        rw [← hld]
        exact hi
      have hjd : j < d := by
        rw [← hld]
        exact hj
      have hij : ¬ i = j := by
        intro he
        rw [he, hjv] at hiv
        exact absurd hiv (by decide +kernel)
      refine Or.inr ⟨hld, ⟨i, hid, j, hjd, hij, hiv, hjv, ?_⟩, ?_⟩
      · intro k hk hki hkj
        have hkm : k < m.length := by
          rw [hld]
          exact hk
        refine le_two_read _ (hcap k) ?_ ?_
        · intro hz
          have hp2 := ground.countOf_two_pos 0 m k j hkm hj hkj
            (by rw [hz, hjv])
          rw [hz, hc0d] at hp2
          exact absurd hp2 (Nat.not_succ_le_self 1)
        · intro hz
          have hp2 := ground.countOf_two_pos 0 m k i hkm hi hki
            (by rw [hz, hiv])
          rw [hz, hc2d] at hp2
          exact absurd hp2 (Nat.not_succ_le_self 1)
      · show (if multScan false false d m = some (false, false) then d - 1
            else if multScan false false d m = some (true, true) then 1
            else 0) = 1
        rw [if_neg hA, if_pos hB]
    · have h0 : multRead d m = 0 := by
        show (if multScan false false d m = some (false, false) then d - 1
            else if multScan false false d m = some (true, true) then 1
            else 0) = 0
        rw [if_neg hA, if_neg hB]
      rw [h0] at hpos
      exact absurd hpos (Nat.lt_irrefl 0)

/-! `lem:adjchar`'s block tier.  `f̄` is the one-column shape at the
complement gap (`pieri.complBox`), `r` rows of one box, and
`f̄ ⊗ f` exhausts by the one-box row: the dominant one-box
additions of `(1^r)` are `θ` and the full column, one block each
with every further label vacant.  The product's contents are the
factors' contents' sums — the one-box block reads each letter once
and `f̄`'s block each withdrawn letter once — so the product reads
the unit-monomial content at `d_f` and each letter-pair move once.
The content refinement of `lem:blockcount`(ii) reads the product's
occupancies as the two blocks' at their counts, and the full-column
line is occupied at the unit-monomial content alone, so `θ`'s
occupancies are the product's with the line's withdrawn. -/

/-- The adjoint's shape is the complement's one-column shape raised
at the first column, `lem:dualread`(ii)'s complement against the
one-box factor. -/
private theorem theta_bump (d : Nat) (hd : 2 ≤ d) :
    theta d = ground.bumpAt 0 (pieri.complBox d) := by
  show ground.bumpAt 0 (ground.bumpAt (d - 2) (List.replicate d 0))
    = ground.bumpAt 0 (ground.unitAt d (d - 2))
  rw [ground.unitAt_bumpRep d (d - 2)
    (Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_two hd)
      Nat.zero_lt_two)]

/-- The complement's one-column shape at its column list: the
vacant columns below the occupied gap, the top column vacant. -/
private theorem complBox_form (k : Nat) :
    pieri.complBox (k + 2) = List.replicate k 0 ++ [1, 0] := by
  show ground.unitAt (k + 2) k = _
  rw [ground.unitAt_replicate (k + 2) k
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_succ (k + 1))),
    ground.addSubSelfL k 2]
  rfl

/-- The occupied gap's move sends the complement's one-column shape
to the full column. -/
private theorem moveDn_complBox : ∀ k : Nat,
    units.moveDn k (List.replicate k 0 ++ [1, 0])
      = List.replicate (k + 1) 0 ++ [1]
  | 0 => rfl
  | k + 1 => by
    show (0 : Nat) :: units.moveDn k (List.replicate k 0 ++ [1, 0])
      = 0 :: (List.replicate (k + 1) 0 ++ [1])
    rw [moveDn_complBox k]

/-- The complement's row is the adjoint's shape against the full
column, one block each with every further label vacant. -/
theorem countOf_row_complBox (k : Nat) (c : Shape) :
    ground.countOf c (pieri.row (pieri.complBox (k + 2)))
      = (if c = theta (k + 2) then 1 else 0)
        + (if c = dualread.fulls (k + 2) 1 then 1 else 0) := by
  have hlen : (pieri.complBox (k + 2)).length = k + 2 :=
    pieri.length_complBox (k + 2)
  rw [pieri.countOf_row (pieri.complBox (k + 2))
      (by rw [hlen]; exact Nat.succ_pos (k + 1)) c,
    ← theta_bump (k + 2) (Nat.le_add_left 2 k), hlen]
  show (if c = theta (k + 2) then 1 else 0)
      + ground.famFold Nat.add 0
        (fun j => ground.countOf c
          (if 0 < ground.getAt 0 (pieri.complBox (k + 2)) j then
            [units.moveDn j (pieri.complBox (k + 2))] else []))
        (List.range (k + 1)) = _
  rw [ground.famFold_congr_members Nat.add 0 _
      (fun j => if j = k then
        (if c = dualread.fulls (k + 2) 1 then 1 else 0) else 0)
      (List.range (k + 1))
      (fun j hj => by
        have hjk : j < k + 1 :=
          ground.ltOfMemRange
            (ground.mem_of_countOf_pos j _ hj)
        have hg : ground.getAt 0 (pieri.complBox (k + 2)) j
            = if j = k then 1 else 0 := by
          show ground.getAt 0 (ground.unitAt (k + 2) k) j = _
          rw [ground.getAt_unitAt,
            if_pos (Nat.lt_succ_of_lt hjk)]
        rw [hg]
        by_cases hje : j = k
        · rw [if_pos hje, if_pos hje, if_pos (Nat.succ_pos 0), hje,
            complBox_form k, moveDn_complBox k,
            ground.countOf_cons]
          show (if c = dualread.fulls (k + 2) 1 then 1 else 0) + 0
            = (if c = dualread.fulls (k + 2) 1 then 1 else 0)
          rw [Nat.add_zero]
        · rw [if_neg hje, if_neg hje, if_neg (Nat.lt_irrefl 0)]
          rfl),
    ground.famFold_pick
      (fun _ => if c = dualread.fulls (k + 2) 1 then 1 else 0) k
      (List.range (k + 1))
      (ground.countOf_range_one (Nat.lt_succ_self k))]


/-- The complement's fusion count against the one-box factor: one
at the adjoint's shape, one at the full column, every further
label vacant. -/
private theorem fusionCount_complBox (k : Nat) (c : Shape)
    (hc : c.length = k + 2) :
    blockcount.fusionCount (pieri.complBox (k + 2))
        (pieri.oneBox (k + 2)) c
      = (if c = theta (k + 2) then 1 else 0)
        + (if c = dualread.fulls (k + 2) 1 then 1 else 0) := by
  have h : blockcount.fusionCount (pieri.complBox (k + 2))
      (pieri.oneBox (pieri.complBox (k + 2)).length) c
      = ground.countOf c (pieri.row (pieri.complBox (k + 2))) :=
    pieri.readAll (pieri.complBox (k + 2)) c
      (by rw [pieri.length_complBox]; exact Nat.succ_pos (k + 1))
      (by rw [pieri.length_complBox]; exact hc)
  rw [pieri.length_complBox] at h
  rw [h, countOf_row_complBox k c]

/-- The adjoint's row list parts from the unit-monomial content at
its doubled head. -/
private theorem rowList_theta_ne (k : Nat) :
    ¬ places.rowList (theta (k + 2)) = List.replicate (k + 2) 1 := by
  intro he
  rw [rowList_theta k] at he
  have h0 : (2 : Nat) = 1 := congrArg (fun l => ground.getAt 0 l 0) he
  exact absurd h0 (by decide +kernel)

/-- The adjoint's shape parts from the full column. -/
private theorem theta_ne_fulls (k : Nat) :
    ¬ theta (k + 2) = dualread.fulls (k + 2) 1 := by
  intro he
  refine rowList_theta_ne k ?_
  rw [he, dualread.rowList_fulls]

/-- The fused carrier `f̄ ⊗ f` at the width `k + 2`. -/
private def fusedK (k : Nat) : List blockcount.HVec :=
  blockcount.fusedAt (blockcount.blockSpan (pieri.complBox (k + 2)))
    (blockcount.blockSpan (pieri.oneBox (k + 2)))

/-- `lem:blockcount`(ii)'s content refinement at the fused carrier:
the product's occupancies are the two blocks' at their counts, and
the row's counts are one apiece. -/
private theorem occ_split (k : Nat) (m : List Nat) :
    blockcount.occ m (fusedK k)
      = blockcount.occ m (blockcount.blockSpan (theta (k + 2)))
        + blockcount.occ m
            (blockcount.blockSpan (dualread.fulls (k + 2) 1)) := by
  have hba : (pieri.oneBox (k + 2)).length
      = (pieri.complBox (k + 2)).length := by
    rw [pieri.length_oneBox, pieri.length_complBox]
  obtain ⟨hsz, hwid, hcl, hiP⟩ :=
    blockcount.fusedSpan_pack (pieri.complBox (k + 2))
      (pieri.oneBox (k + 2)) hba
  have hrl := blockcount.exhaust_rowList_shapeOf
    (pieri.complBox (k + 2)).length (fusedK k) hsz hwid hcl
  have hwnu : ∀ nu ∈ (blockcount.exhaust (pieri.complBox (k + 2)).length
        (fusedK k)).map blockcount.HVec.content, nu.length = k + 2 := by
    intro nu hnu
    rw [blockcount.exhaust_width (pieri.complBox (k + 2)).length
        (fusedK k) hsz hwid hcl nu hnu,
      pieri.length_complBox]
  have hcnt : ∀ c : Shape, c.length = k + 2 →
      blockcount.countAt (fusedK k) (places.rowList c)
        = (if c = theta (k + 2) then 1 else 0)
          + (if c = dualread.fulls (k + 2) 1 then 1 else 0) := by
    intro c hc
    show blockcount.countAt
      (blockcount.fusedAt (blockcount.blockSpan (pieri.complBox (k + 2)))
        (blockcount.blockSpan (pieri.oneBox (k + 2)))) (places.rowList c) = _
    rw [← blockcount.fusionCount_countAt (pieri.complBox (k + 2))
      (pieri.oneBox (k + 2)) c hba]
    exact fusionCount_complBox k c hc
  have hkey : ∀ c : Shape, c.length = k + 2 →
      blockcount.countAt (fusedK k) (places.rowList c) = 1 →
      ground.countOf (places.rowList c)
        (ground.dedupL ((blockcount.exhaust (pieri.complBox (k + 2)).length
        (fusedK k)).map blockcount.HVec.content)) = 1 := by
    intro c _ hone
    refine Nat.le_antisymm (ground.countOf_dedupL_le _ _) ?_
    refine ground.countOf_pos_of_mem (ground.mem_dedupL ?_)
    refine ground.mem_of_countOf_pos _ _ ?_
    rw [← blockcount.occ_eq_countOf,
      ← blockcount.countAt_exhaust (pieri.complBox (k + 2)).length
        (fusedK k) hsz hwid hcl,
      hone]
    exact Nat.succ_pos 0
  have hcTh : ground.countOf (places.rowList (theta (k + 2)))
      (ground.dedupL ((blockcount.exhaust (pieri.complBox (k + 2)).length
        (fusedK k)).map blockcount.HVec.content)) = 1 :=
    hkey (theta (k + 2)) (length_theta (k + 2)) (by
      rw [hcnt (theta (k + 2)) (length_theta (k + 2)), if_pos rfl,
        if_neg (theta_ne_fulls k)])
  have hcFu : ground.countOf (List.replicate (k + 2) 1)
      (ground.dedupL ((blockcount.exhaust (pieri.complBox (k + 2)).length
        (fusedK k)).map blockcount.HVec.content)) = 1 := by
    have h := hkey (dualread.fulls (k + 2) 1)
      (dualread.length_fulls (k + 2) 1) (by
      rw [hcnt (dualread.fulls (k + 2) 1) (dualread.length_fulls (k + 2) 1),
        if_neg (fun he => theta_ne_fulls k he.symm), if_pos rfl])
    rw [dualread.rowList_fulls (k + 2) 1] at h
    exact h
  have hcong : ground.famFold Nat.add 0
      (fun nu => blockcount.countAt (fusedK k) nu
        * blockcount.occ m
            (blockcount.blockSpan (places.shapeOf nu)))
      (ground.dedupL ((blockcount.exhaust (pieri.complBox (k + 2)).length
        (fusedK k)).map blockcount.HVec.content))
      = ground.famFold Nat.add 0
        (fun nu =>
          (if nu = places.rowList (theta (k + 2)) then
            blockcount.occ m (blockcount.blockSpan (theta (k + 2)))
            else 0)
          + (if nu = List.replicate (k + 2) 1 then
            blockcount.occ m
              (blockcount.blockSpan (dualread.fulls (k + 2) 1))
            else 0))
        (ground.dedupL ((blockcount.exhaust (pieri.complBox (k + 2)).length
        (fusedK k)).map blockcount.HVec.content)) := by
    refine ground.famFold_congr_members Nat.add 0 _ _ _ ?_
    intro nu hnu
    have hnuE : nu ∈ (blockcount.exhaust (pieri.complBox (k + 2)).length
        (fusedK k)).map blockcount.HVec.content :=
      ground.mem_of_dedupL (ground.mem_of_countOf_pos nu _ hnu)
    have hrlnu : places.rowList (places.shapeOf nu) = nu :=
      hrl nu hnuE
    have hcs := hcnt (places.shapeOf nu)
      (by rw [places.length_shapeOf]; exact hwnu nu hnuE)
    rw [hrlnu] at hcs
    by_cases hth : places.shapeOf nu = theta (k + 2)
    · have hnth : nu = places.rowList (theta (k + 2)) := by
        rw [← hrlnu, hth]
      rw [hcs, hth, if_pos rfl, if_neg (theta_ne_fulls k),
        Nat.add_zero, Nat.one_mul, if_pos hnth,
        if_neg (fun he : nu = List.replicate (k + 2) 1 =>
          rowList_theta_ne k (hnth.symm.trans he))]
      exact (Nat.add_zero _).symm
    · by_cases hfu : places.shapeOf nu = dualread.fulls (k + 2) 1
      · have hnfu : nu = List.replicate (k + 2) 1 := by
          rw [← hrlnu, hfu, dualread.rowList_fulls]
        rw [hcs, hfu, if_neg (fun he => theta_ne_fulls k he.symm),
          if_pos rfl, Nat.zero_add, Nat.one_mul,
          if_neg (fun he : nu = places.rowList (theta (k + 2)) =>
            rowList_theta_ne k (he.symm.trans hnfu)),
          if_pos hnfu, Nat.zero_add]
      · rw [hcs, if_neg hth, if_neg hfu, Nat.add_zero, Nat.zero_mul,
          if_neg (fun he : nu = places.rowList (theta (k + 2)) =>
            hth (by rw [he, places.shapeOf_rowList])),
          if_neg (fun he : nu = List.replicate (k + 2) 1 =>
            hfu (by
              rw [he, ← dualread.rowList_fulls (k + 2) 1,
                places.shapeOf_rowList]))]
  have hpick1 : ground.famFold Nat.add 0
      (fun nu => if nu = places.rowList (theta (k + 2)) then
        blockcount.occ m (blockcount.blockSpan (theta (k + 2)))
        else 0)
      (ground.dedupL ((blockcount.exhaust (pieri.complBox (k + 2)).length
        (fusedK k)).map blockcount.HVec.content))
      = blockcount.occ m (blockcount.blockSpan (theta (k + 2))) :=
    ground.famFold_pick
      (fun _ => blockcount.occ m
        (blockcount.blockSpan (theta (k + 2))))
      (places.rowList (theta (k + 2)))
      (ground.dedupL ((blockcount.exhaust (pieri.complBox (k + 2)).length
        (fusedK k)).map blockcount.HVec.content)) hcTh
  have hpick2 : ground.famFold Nat.add 0
      (fun nu => if nu = List.replicate (k + 2) 1 then
        blockcount.occ m
          (blockcount.blockSpan (dualread.fulls (k + 2) 1))
        else 0)
      (ground.dedupL ((blockcount.exhaust (pieri.complBox (k + 2)).length
        (fusedK k)).map blockcount.HVec.content))
      = blockcount.occ m
        (blockcount.blockSpan (dualread.fulls (k + 2) 1)) :=
    ground.famFold_pick
      (fun _ => blockcount.occ m
        (blockcount.blockSpan (dualread.fulls (k + 2) 1)))
      (List.replicate (k + 2) 1)
      (ground.dedupL ((blockcount.exhaust (pieri.complBox (k + 2)).length
        (fusedK k)).map blockcount.HVec.content)) hcFu
  rw [← blockcount.dimAt_occ (fusedK k) hiP m,
    blockcount.gradedDim_countAt (pieri.complBox (k + 2)).length
      (fusedK k) hsz hwid hcl m,
    hcong, ground.famFold_add_split, hpick1, hpick2]


/-- The move at one letter twice reads the unit-monomial content
back. -/
private theorem moveAt_diag (d i : Nat) (hi : i < d) :
    blockcount.moveAt i i (List.replicate d 1) = List.replicate d 1 :=
  ground.bumpAt_dipAt_self i (List.replicate d 1)
    (by rw [ground.getAt_replicate 0 1 d i hi]; exact Nat.succ_pos 0)

/-- The withdrawn letter's content joined to the raised letter's is
the letter-pair move at the unit-monomial content, the raised letter
against the withdrawn (`con:places`' contents' sum at `con:units`'
move). -/
private theorem coUnit_add_unitAt (d i j : Nat) :
    List.zipWith (fun a b => a + b) (pieri.coUnit d i) (ground.unitAt d j)
      = blockcount.moveAt j i (List.replicate d 1) := by
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [ground.length_zipWith (fun a b => a + b) (pieri.coUnit d i)
        (ground.unitAt d j) d (pieri.length_coUnit d i)
        (ground.length_unitAt d j),
      blockcount.length_moveAt, ground.length_replicate]
  · intro t ht
    rw [ground.length_zipWith _ _ _ d (pieri.length_coUnit d i)
      (ground.length_unitAt d j)] at ht
    rw [ground.getAt_zipWith 0 0 0 (fun a b => a + b) (pieri.coUnit d i)
        (ground.unitAt d j) t
        (by rw [pieri.length_coUnit]; exact ht)
        (by rw [ground.length_unitAt]; exact ht),
      pieri.getAt_coUnit d i t ht, ground.getAt_unitAt, if_pos ht]
    by_cases hti : t = i
    · by_cases htj : t = j
      · have hR : ground.getAt 0
            (blockcount.moveAt j i (List.replicate d 1)) t = 1 := by
          rw [← htj, ← hti, moveAt_diag d t ht,
            ground.getAt_replicate 0 1 d t ht]
        rw [if_pos hti, if_pos htj]
        exact hR.symm
      · have hR : ground.getAt 0
            (blockcount.moveAt j i (List.replicate d 1)) t = 0 := by
          have hi : i < d := by
            rw [← hti]
            exact ht
          have h := blockcount.getAt_moveAt_snd j i (List.replicate d 1)
            (fun he => htj (hti.trans he.symm))
            (by rw [ground.getAt_replicate 0 1 d i hi]; exact Nat.succ_pos 0)
          rw [ground.getAt_replicate 0 1 d i hi] at h
          rw [hti]
          exact Nat.succ.inj h
        rw [if_pos hti, if_neg htj]
        exact hR.symm
    · by_cases htj : t = j
      · have hR : ground.getAt 0
            (blockcount.moveAt j i (List.replicate d 1)) t = 2 := by
          have hj : j < d := by
            rw [← htj]
            exact ht
          rw [htj, blockcount.getAt_moveAt_fst j i _
              (fun he => hti (htj.trans he))
              (by rw [ground.length_replicate]; exact hj),
            ground.getAt_replicate 0 1 d j hj]
        rw [if_neg hti, if_pos htj]
        exact hR.symm
      · have hR : ground.getAt 0
            (blockcount.moveAt j i (List.replicate d 1)) t = 1 := by
          rw [blockcount.getAt_moveAt_ne j i _ t htj hti,
            ground.getAt_replicate 0 1 d t ht]
        rw [if_neg hti, if_neg htj]
        exact hR.symm

/-- The letter-pair move at distinct letters: the raised place at
two, the lowered at the fold's unit, every further place at one. -/
private theorem moveAt_reads (d a b : Nat) (ha : a < d) (hb : b < d)
    (hab : ¬ a = b) :
    ground.getAt 0 (blockcount.moveAt a b (List.replicate d 1)) a = 2
      ∧ ground.getAt 0 (blockcount.moveAt a b (List.replicate d 1)) b = 0
      ∧ ∀ t, t < d → ¬ t = a → ¬ t = b →
          ground.getAt 0 (blockcount.moveAt a b (List.replicate d 1)) t
            = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [blockcount.getAt_moveAt_fst a b _ hab
        (by rw [ground.length_replicate]; exact ha),
      ground.getAt_replicate 0 1 d a ha]
  · have h := blockcount.getAt_moveAt_snd a b (List.replicate d 1) hab
      (by rw [ground.getAt_replicate 0 1 d b hb]; exact Nat.succ_pos 0)
    rw [ground.getAt_replicate 0 1 d b hb] at h
    exact Nat.succ.inj h
  · intro t ht hta htb
    rw [blockcount.getAt_moveAt_ne a b _ t hta htb,
      ground.getAt_replicate 0 1 d t ht]

/-- The move's counts: one vacancy, one double, the units at the
residue's predecessor. -/
private theorem moveAt_counts (d a b : Nat) (ha : a < d) (hb : b < d)
    (hab : ¬ a = b) :
    ground.countOf 0 (blockcount.moveAt a b (List.replicate d 1)) = 1
      ∧ ground.countOf 2 (blockcount.moveAt a b (List.replicate d 1)) = 1
      ∧ ground.countOf 1 (blockcount.moveAt a b (List.replicate d 1)) + 2
          = d := by
  obtain ⟨h2, h0, h1⟩ := moveAt_reads d a b ha hb hab
  have hlen : (blockcount.moveAt a b (List.replicate d 1)).length = d := by
    rw [blockcount.length_moveAt, ground.length_replicate]
  obtain ⟨c0, c2, c1⟩ := ground.countOf_pattern2
    (blockcount.moveAt a b (List.replicate d 1)) a b
    (by rw [hlen]; exact ha) (by rw [hlen]; exact hb) hab h2 h0
    (fun t ht => h1 t (by rw [← hlen]; exact ht))
  rw [hlen] at c1
  exact ⟨c0, c2, c1⟩

/-- A content at the move's reads is the move. -/
private theorem move_of_reads (d : Nat) (m : List Nat) (hm : m.length = d)
    (a b : Nat) (ha : a < d) (hb : b < d) (hab : ¬ a = b)
    (h2 : ground.getAt 0 m a = 2) (h0 : ground.getAt 0 m b = 0)
    (hoth : ∀ t, t < d → ¬ t = a → ¬ t = b → ground.getAt 0 m t = 1) :
    m = blockcount.moveAt a b (List.replicate d 1) := by
  obtain ⟨r2, r0, r1⟩ := moveAt_reads d a b ha hb hab
  refine ground.getAt_ext 0 m _
    (by rw [hm, blockcount.length_moveAt, ground.length_replicate]) ?_
  intro t ht
  have htd : t < d := by
    rw [hm] at ht
    exact ht
  by_cases hta : t = a
  · rw [hta, h2, r2]
  · by_cases htb : t = b
    · rw [htb, h0, r0]
    · rw [hoth t htd hta htb, r1 t htd hta htb]

/-- The product's occupancy as the two factors' letters' fold: the
one-box block reads each letter once and the complement's block
each withdrawn letter once, so the product's contents are the
letter pairs' sums. -/
private theorem occ_fused_fold (k : Nat) (m : List Nat) :
    blockcount.occ m (fusedK k)
      = ground.famFold Nat.add 0
          (fun i => ground.famFold Nat.add 0
            (fun j => if m = blockcount.moveAt j i (List.replicate (k + 2) 1)
              then 1 else 0)
            (List.range (k + 2)))
          (List.range (k + 2)) := by
  have hB : blockcount.blockSpan (pieri.oneBox (k + 2))
      = (List.range (k + 2)).map (fun i =>
          (⟨ground.unitAt (k + 2) i, [BPair.ofNat 1]⟩ : blockcount.HVec)) :=
    blockcount.blockSpan_fund (k + 2) (Nat.succ_pos (k + 1))
  have hinner : ∀ v : blockcount.HVec,
      ground.countOf m (((blockcount.blockSpan (pieri.oneBox (k + 2))).map
        (blockcount.tensorH v)).map blockcount.HVec.content)
      = ground.famFold Nat.add 0
        (fun j => if m = List.zipWith (fun a b => a + b) v.content
            (ground.unitAt (k + 2) j) then 1 else 0)
        (List.range (k + 2)) := by
    intro v
    rw [ground.countOf_fold m, ground.famFold_map, ground.famFold_map,
      hB, ground.famFold_map]
    rfl
  have hcov : ∀ x, 0 < ground.countOf x
      ((blockcount.blockSpan (pieri.complBox (k + 2))).map
        blockcount.HVec.content) →
      ground.countOf x ((List.range (k + 2)).map
        (pieri.coUnit (k + 2))) = 1 := by
    intro x hx
    rw [blockcount.span_countOf (pieri.complBox (k + 2)) x,
      pieri.occ_complBox (k + 2)
        (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))) x] at hx
    obtain ⟨i, hi, hix⟩ := pieri.coUnit_of_pos (k + 2) x hx
    rw [← hix]
    exact pieri.countOf_coUnitList (k + 2) i hi
  rw [blockcount.occ_eq_countOf m,
    show fusedK k
      = (blockcount.blockSpan (pieri.complBox (k + 2))).flatMap (fun v =>
        (blockcount.blockSpan (pieri.oneBox (k + 2))).map
          (blockcount.tensorH v)) from rfl,
    ground.map_flatMap, ground.countOf_flatMap,
    ground.famFold_congr_all Nat.add 0 _ _ hinner
      (blockcount.blockSpan (pieri.complBox (k + 2))),
    ← ground.famFold_map Nat.add 0
      (fun c => ground.famFold Nat.add 0
        (fun j => if m = List.zipWith (fun a b => a + b) c
          (ground.unitAt (k + 2) j) then 1 else 0) (List.range (k + 2)))
      blockcount.HVec.content (blockcount.blockSpan (pieri.complBox (k + 2))),
    ground.famFold_countCollect _ _
      ((List.range (k + 2)).map (pieri.coUnit (k + 2))) hcov,
    ground.famFold_congr_members Nat.add 0 _
      (fun c => ground.famFold Nat.add 0
        (fun j => if m = List.zipWith (fun a b => a + b) c
          (ground.unitAt (k + 2) j) then 1 else 0) (List.range (k + 2)))
      ((List.range (k + 2)).map (pieri.coUnit (k + 2)))
      (fun c hc => by
        obtain ⟨i, hi, hic⟩ := pieri.coUnit_of_pos (k + 2) c hc
        rw [blockcount.span_countOf (pieri.complBox (k + 2)) c,
          pieri.occ_complBox (k + 2)
            (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))) c,
          ← hic, pieri.countOf_coUnitList (k + 2) i hi, Nat.one_mul]),
    ground.famFold_map]
  refine ground.famFold_congr_all Nat.add 0 _ _ (fun i => ?_)
    (List.range (k + 2))
  refine ground.famFold_congr_all Nat.add 0 _ _ (fun j => ?_)
    (List.range (k + 2))
  show (if m = List.zipWith (fun a b => a + b) (pieri.coUnit (k + 2) i)
      (ground.unitAt (k + 2) j) then 1 else 0) = _
  rw [coUnit_add_unitAt]


/-- The product's occupancy at a content of the width: the adjoint's
read joined to the full-column line's, the unit-monomial content at
the fundamental count and each letter-pair move at one. -/
private theorem occ_fused (k : Nat) (m : List Nat)
    (hm : m.length = k + 2) :
    blockcount.occ m (fusedK k)
      = multRead (k + 2) m
        + (if m = List.replicate (k + 2) 1 then 1 else 0) := by
  rw [occ_fused_fold k m]
  by_cases hmr : m = List.replicate (k + 2) 1
  · rw [if_pos hmr, hmr, multRead_ones (k + 2)]
    refine ground.famFold_rangeOne _ (k + 2) ?_
    intro i hi
    have hpick := ground.famFold_pick_of
      (fun j => if List.replicate (k + 2) 1
        = blockcount.moveAt j i (List.replicate (k + 2) 1) then 1 else 0)
      i (List.range (k + 2)) (ground.countOf_range_one hi)
      (fun j hj hji => by
        refine if_neg ?_
        intro he
        obtain ⟨c0, _, _⟩ := moveAt_counts (k + 2) j i (ground.ltOfMem hj)
          hi hji
        rw [← he, ground.countOf_replicate_ne 0 1
          (fun hh => Nat.noConfusion hh) (k + 2)] at c0
        exact Nat.noConfusion c0)
    rw [hpick, moveAt_diag (k + 2) i hi, if_pos rfl]
  · rw [if_neg hmr, Nat.add_zero]
    by_cases hpos : 0 < multRead (k + 2) m
    · match multRead_cases (k + 2) m hpos with
      | .inl ⟨_, hone, _⟩ =>
        exact absurd (ground.getAt_ext 0 m (List.replicate (k + 2) 1)
          (by rw [hm, ground.length_replicate])
          (fun t ht => by
            have htd : t < k + 2 := by
              rw [hm] at ht
              exact ht
            rw [hone t htd,
              ground.getAt_replicate 0 1 (k + 2) t htd])) hmr
      | .inr ⟨_, ⟨p, hp, q, hq, hpq, h2, h0, hoth⟩, hmv⟩ =>
        have hme : m = blockcount.moveAt p q (List.replicate (k + 2) 1) :=
          move_of_reads (k + 2) m hm p q hp hq hpq h2 h0 hoth
        have hdiag : ∀ i, i < k + 2 →
            ¬ m = blockcount.moveAt i i (List.replicate (k + 2) 1) := by
          intro i hi he
          rw [moveAt_diag (k + 2) i hi] at he
          exact hmr he
        rw [hmv]
        have hq' : ground.famFold Nat.add 0
            (fun j => if m = blockcount.moveAt j q (List.replicate (k + 2) 1)
              then 1 else 0) (List.range (k + 2)) = 1 := by
          rw [ground.famFold_pick_of _ p (List.range (k + 2))
              (ground.countOf_range_one hp)
              (fun j hj hjp => by
                have hjd : j < k + 2 := ground.ltOfMem hj
                refine if_neg ?_
                intro he
                by_cases hjq : j = q
                · rw [hjq] at he
                  exact hdiag q hq he
                · obtain ⟨r2, _, _⟩ := moveAt_reads (k + 2) j q hjd hq hjq
                  rw [← he, hoth j hjd hjp hjq] at r2
                  exact Nat.noConfusion (Nat.succ.inj r2)),
            if_pos hme]
        rw [ground.famFold_pick_of _ q (List.range (k + 2))
            (ground.countOf_range_one hq)
            (fun i hi hiq => by
              have hid : i < k + 2 := ground.ltOfMem hi
              refine ground.famFold_rangeZero _ (k + 2) ?_
              intro j hj
              refine if_neg ?_
              intro he
              by_cases hij : i = j
              · rw [← hij] at he
                exact hdiag i hid he
              · obtain ⟨_, r0, _⟩ := moveAt_reads (k + 2) j i hj hid
                  (fun hh => hij hh.symm)
                by_cases hip : i = p
                · rw [← he, hip, h2] at r0
                  exact Nat.noConfusion r0
                · rw [← he, hoth i hid hip hiq] at r0
                  exact Nat.noConfusion r0),
          hq']
    · have hz : multRead (k + 2) m = 0 := by
        match Nat.eq_zero_or_pos (multRead (k + 2) m) with
        | .inl h => exact h
        | .inr h => exact absurd h hpos
      rw [hz]
      refine ground.famFold_rangeZero _ (k + 2) ?_
      intro i hi
      refine ground.famFold_rangeZero _ (k + 2) ?_
      intro j hj
      refine if_neg ?_
      intro he
      by_cases hij : i = j
      · rw [← hij] at he
        exact hmr (he.trans (moveAt_diag (k + 2) i hi))
      · obtain ⟨c0, c2, c1⟩ :=
          moveAt_counts (k + 2) j i hj hi (fun hh => hij hh.symm)
        rw [← he] at c0 c2 c1
        rw [multRead_move (k + 2) m hm c0 c2 c1] at hz
        exact Nat.noConfusion hz

/-- `lem:adjchar`'s content list against the adjoint block: at every
content of the width the block's occupancy is the formula's read,
the product's occupancies with the full-column line's withdrawn. -/
theorem occupancy (d : Nat) (hd : 2 ≤ d) (m : List Nat)
    (hm : m.length = d) :
    blockcount.occupancyAt (blockcount.blockSpan (theta d)) m
      = multRead d m := by
  match d, hd with
  | k + 2, _ =>
    rw [blockcount.occupancyAt_eq_occ]
    refine ground.addCancelR
      (if m = List.replicate (k + 2) 1 then 1 else 0) ?_
    rw [← occ_fused k m hm, occ_split k m, dualread.occ_line (k + 2) 1 m]


end adjchar
