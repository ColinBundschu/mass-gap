import MassGap.Blockcount
/-!
`lem:tops` — the tops at the units carrier.  Clause (i),
`max_top`: a pool member whose raising-moved contents are
unoccupied reads every raising image at the unit tail — the
settled read at the vacant group, the image homogeneous at a
content off every occupied summand (`vacant_settled`, the group's
row count at the occupancy with `elim.spanRel_nil_unit` the
vacant span's read).  Clause (iii) is the landed exhibit tier,
`blockcount.exhibit_top` and `blockcount.exhibit_top_all`, cited
at its consumers.  Clause (ii), the top
content's dominance, is `dominant` at the crossed exchange's
pairing read, the tex's matrix-units sentence.  The
exhaustion tier (`lem:blockcount`(i)) is the arriving consumer,
the maximal-content top its selection.
-/

namespace tops
open ground places blockcount

/-- A settled action image at a vacant content reads the unit
tail: the group is unoccupied, so the settled read's span is the
vacant one. -/
theorem vacant_settled (pool : List HVec) (w : HVec) (i j : Nat)
    (hset : settledAt pool (act i j w))
    (hocc : occ (moveAt i j w.content) pool = 0) :
    poly.unitTail (act i j w).coords := by
  have hg : groupAt pool (act i j w).content = [] := by
    refine ground.nil_of_length_zero _ ?_
    rw [length_groupAt]
    exact hocc
  match hset with
  | Or.inl hu => exact unitTail_of_allU _ hu
  | Or.inr hs =>
    rw [hg] at hs
    exact elim.spanRel_nil_unit _ _ hs

/-- `lem:tops`(i) at the units carrier: a settled member whose
every raising-moved content is unoccupied is a top, each raising
image at the unit tail. -/
theorem max_top (d : Nat) (pool : List HVec) (w : HVec)
    (hset : ∀ j, j < d → ∀ i, i < j →
      settledAt pool (act i j w))
    (hocc : ∀ j, j < d → ∀ i, i < j →
      occ (moveAt i j w.content) pool = 0) :
    ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j w).coords :=
  fun j hj i hij =>
    vacant_settled pool w i j (hset j hj i hij) (hocc j hj i hij)

/-! `lem:tops`(ii)'s tier at the units carrier: the crossed
exchange (`con:units`' table read at the two moved contents), the
transpose walk to the lowered image's self-pairing, and the
positive pairing's side read — `lem:tops`(ii)'s own matrix-units
sentence, `lem:strings`' residual walk the further consumer. -/

/-- The action at a vacant source letter reads the unit tail. -/
theorem act_null (i j : Nat) (w : HVec)
    (hz : ground.getAt 0 w.content j = 0) :
    poly.unitTail (act i j w).coords :=
  units.matVec_null_unocc (moveAt i j w.content) w.content i j hz
    w.coords


/-- The round trip's width at an occupied letter, the content's
own enumeration. -/
theorem len_act2 (i j : Nat) (w : HVec)
    (hocc : 0 < ground.getAt 0 w.content i) :
    (act i j (act j i w)).coords.length
      = (places.monomialsAt w.content).length := by
  have hc : (act i j (act j i w)).content = w.content :=
    moveAt_round_at i j w.content hocc
  have hsz : (act i j (act j i w)).coords.length
      = (places.monomialsAt
          (act i j (act j i w)).content).length :=
    act_sized i j (act j i w)
  rw [hc] at hsz
  exact hsz


theorem raise_exch (i j : Nat) (hij : ¬ i = j) (y : HVec)
    (hocc : 0 < ground.getAt 0 y.content i)
    (hcj : 0 < ground.getAt 0 y.content j)
    (hiy : i < y.content.length) (hjy : j < y.content.length)
    (hszy : sized y) :
    poly.oneValue
      (elim.vecAdd (act i j (act j i y)).coords
        (elim.vecScale (BPair.ofNat (ground.getAt 0 y.content j))
          y.coords))
      (elim.vecAdd
        (elim.matVec (units.matUnitAt y.content
            (moveAt i j y.content) j i) (act i j y).coords)
        (elim.vecScale (BPair.ofNat (ground.getAt 0 y.content i))
          y.coords)) := by
  have hji : ¬ j = i := fun he => hij he.symm
  have hmuA : moveAt i j (moveAt j i y.content) = y.content :=
    moveAt_round_at i j y.content hocc
  have hmuB : moveAt j i (moveAt i j y.content) = y.content :=
    moveAt_round_at j i y.content hcj
  have hiA : i < (moveAt j i y.content).length := by
    rw [length_moveAt]
    exact hiy
  have hjB : j < (moveAt i j y.content).length := by
    rw [length_moveAt]
    exact hjy
  have hUp := blockcount.out_gen (moveAt j i y.content) i j hiA hij
  have hDn' := blockcount.out_gen (moveAt i j y.content) j i hjB hji
  rw [hmuA] at hUp
  rw [hmuB] at hDn'
  have hkey := units.matVec_gpair_read y.content
    (moveAt j i y.content) (moveAt i j y.content) i j
    (blockcount.out_gen y.content j i hjy hji) hUp
    (blockcount.out_gen y.content i j hiy hij) hDn' y.coords hszy
  show poly.oneValue
    (elim.vecAdd
      (elim.matVec (units.matUnitAt
          (moveAt i j (moveAt j i y.content))
          (moveAt j i y.content) i j)
        (elim.matVec (units.matUnitAt (moveAt j i y.content)
          y.content j i) y.coords))
      (elim.vecScale (BPair.ofNat (ground.getAt 0 y.content j))
        y.coords))
    (elim.vecAdd
      (elim.matVec (units.matUnitAt y.content
          (moveAt i j y.content) j i)
        (elim.matVec (units.matUnitAt (moveAt i j y.content)
          y.content i j) y.coords))
      (elim.vecScale (BPair.ofNat (ground.getAt 0 y.content i))
        y.coords))
  rw [hmuA]
  exact hkey


/-- The crossed exchange at a vacant raised letter: the exchange's
first composite reads the unit and the display collapses to the
two scales. -/
theorem raise_exch_low (i j : Nat) (hij : ¬ i = j)
    (y : HVec) (hz : ground.getAt 0 y.content i = 0)
    (hcj : 0 < ground.getAt 0 y.content j)
    (hiy : i < y.content.length) (hjy : j < y.content.length)
    (hszy : sized y) :
    poly.oneValue
      (elim.vecScale (BPair.ofNat (ground.getAt 0 y.content j))
        y.coords)
      (elim.vecAdd
        (elim.matVec (units.matUnitAt y.content
            (moveAt i j y.content) j i) (act i j y).coords)
        (elim.vecScale (BPair.ofNat (ground.getAt 0 y.content i))
          y.coords)) := by
  have hji : ¬ j = i := fun he => hij he.symm
  have hmuB : moveAt j i (moveAt i j y.content) = y.content :=
    moveAt_round_at j i y.content hcj
  have hjB : j < (moveAt i j y.content).length := by
    rw [length_moveAt]
    exact hjy
  have hDn' := blockcount.out_gen (moveAt i j y.content) j i hjB hji
  rw [hmuB] at hDn'
  have hDn : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt y.content) →
      0 < ground.countOf m (units.unitAct j i s) →
      m.length = sumNat ([] : List Nat)
        ∧ content ([] : List Nat).length m = ([] : List Nat) := by
    intro s m hs hm
    rw [units.unitAct_nil_of_zero j i s
      (letter_zero y.content i hz s hs)] at hm
    exact absurd hm (Nat.lt_irrefl 0)
  have hUp : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt ([] : List Nat)) →
      0 < ground.countOf m (units.unitAct i j s) →
      m.length = sumNat y.content
        ∧ content y.content.length m = y.content := by
    intro s m hs hm
    rw [units.unitAct_nil_of_zero i j s
      (letter_zero ([] : List Nat) j rfl s hs)] at hm
    exact absurd hm (Nat.lt_irrefl 0)
  have hkey := units.matVec_gpair_read y.content ([] : List Nat)
    (moveAt i j y.content) i j hDn hUp
    (blockcount.out_gen y.content i j hiy hij) hDn' y.coords hszy
  have hnullA : poly.unitTail
      (elim.matVec (units.matUnitAt y.content ([] : List Nat) i j)
        (elim.matVec (units.matUnitAt ([] : List Nat) y.content j i)
          y.coords)) :=
    elim.matVec_null _ _
      (units.matVec_null_unocc ([] : List Nat) y.content j i hz
        y.coords)
  refine poly.oneValue_trans
    (poly.oneValue_symm (elim.vecAdd_null_left _ _ ?_ hnullA)) hkey
  rw [units.matVec_matUnitAt_length,
    elim.length_vecScale, hszy]


/-- A count's multiple keeps the side at or above. -/
theorem side_ofNat_mul (p : BPair) (hp : p.snd ≤ p.fst) :
    ∀ n : Nat, (BPair.ofNat n * p).snd ≤ (BPair.ofNat n * p).fst
  | 0 => by
    show (BPair.unit * p).snd ≤ (BPair.unit * p).fst
    exact side_congr (BPair.oneValue_symm (BPair.unit_mul p))
      (Or.inl rfl)
  | n + 1 => by
    have hchain : (BPair.ofNat (n + 1) * p).oneValue
        (BPair.ofNat n * p + BPair.ofNat 1 * p) := by
      refine BPair.oneValue_trans
        (BPair.mul_congr_left (BPair.ofNat_add n 1)) ?_
      rw [BPair.right_distrib]
      exact BPair.oneValue_refl _
    refine side_congr (BPair.oneValue_symm hchain) ?_
    exact elim.side_add (side_ofNat_mul p hp n)
      (side_congr
        (BPair.oneValue_symm
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq
              (BPair.mul_comm (BPair.ofNat 1) p))
            (BPair.mul_ofNat_one p)))
        hp)


/-- The lowered image's self-pairing walks across the transpose
to the round trip's pairing at the member. -/
theorem selfpair_adj (i j : Nat) (hij : ¬ i = j) (y : HVec)
    (hocc : 0 < ground.getAt 0 y.content i)
    (hiy : i < y.content.length) (hjy : j < y.content.length)
    (hszy : sized y) :
    (elim.dotP (act j i y).coords (act j i y).coords).oneValue
      (elim.dotP y.coords (act i j (act j i y)).coords) := by
  have hji : ¬ j = i := fun he => hij he.symm
  have hmu : moveAt i j (moveAt j i y.content) = y.content :=
    moveAt_round_at i j y.content hocc
  have hiA : i < (moveAt j i y.content).length := by
    rw [length_moveAt]
    exact hiy
  have hout' := blockcount.out_gen (moveAt j i y.content) i j hiA hij
  rw [hmu] at hout'
  have htrans := units.matUnit_transpose_read
    (moveAt j i y.content) y.content j i
    (blockcount.out_gen y.content j i hjy hji) hout'
  have heq : (act i j (act j i y)).coords
      = elim.matVec (units.matUnitAt y.content
          (moveAt j i y.content) i j) (act j i y).coords := by
    show elim.matVec (units.matUnitAt
        (moveAt i j (moveAt j i y.content))
        (moveAt j i y.content) i j) (act j i y).coords = _
    rw [hmu]
  rw [heq]
  refine BPair.oneValue_trans
    (elim.dotP_matVec_transpose
      (places.monomialsAt y.content).length
      (units.matUnitAt (moveAt j i y.content) y.content j i)
      y.coords (act j i y).coords
      (units.rowsLen_matUnitAt _ _ j i) hszy
      (elim.matVec_length _ _)) ?_
  exact elim.dotP_oneValue_right y.coords _ _
    (elim.matVec_matOne _ _ _ htrans)


/-- `lem:tops`(ii)'s crossed-exchange display at the positive
pairing: the lowered image's self-pairing joins the second
letter's multiple of the member's own to the first's, the
exchange at the raising's unit. -/
theorem top_scalar (i j : Nat) (hij : ¬ i = j) (y : HVec)
    (hi : i < y.content.length) (hj : j < y.content.length)
    (hsz : sized y) (htop : poly.unitTail (act i j y).coords)
    (hcj : 0 < ground.getAt 0 y.content j) :
    ((elim.dotP (act j i y).coords (act j i y).coords)
      + BPair.ofNat (ground.getAt 0 y.content j)
          * elim.dotP y.coords y.coords).oneValue
      (BPair.ofNat (ground.getAt 0 y.content i)
        * elim.dotP y.coords y.coords) := by
  have hnullR : poly.unitTail (elim.matVec
      (units.matUnitAt y.content (moveAt i j y.content) j i)
      (act i j y).coords) := elim.matVec_null _ _ htop
  have hlenR : (elim.matVec (units.matUnitAt y.content
        (moveAt i j y.content) j i) (act i j y).coords).length
      = (elim.vecScale (BPair.ofNat (ground.getAt 0 y.content i))
        y.coords).length := by
    rw [units.matVec_matUnitAt_length,
      elim.length_vecScale, hsz]
  by_cases hocc : 0 < ground.getAt 0 y.content i
  · have hvec : poly.oneValue
        (elim.vecAdd (act i j (act j i y)).coords
          (elim.vecScale (BPair.ofNat (ground.getAt 0 y.content j))
            y.coords))
        (elim.vecScale (BPair.ofNat (ground.getAt 0 y.content i))
          y.coords) :=
      poly.oneValue_trans (raise_exch i j hij y hocc hcj hi hj hsz)
        (elim.vecAdd_null_left _ _ hlenR hnullR)
    refine BPair.oneValue_trans
      (BPair.add_congr (selfpair_adj i j hij y hocc hi hj hsz)
        (BPair.oneValue_symm
          (elim.dotP_vecScale_right y.coords y.coords _))) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_symm (elim.dotP_vecAdd y.coords _ _ ?_ ?_)) ?_
    · rw [len_act2 i j y hocc, hsz]
    · rw [elim.length_vecScale]
    · refine BPair.oneValue_trans
        (elim.dotP_oneValue_right y.coords _ _ hvec) ?_
      exact elim.dotP_vecScale_right y.coords y.coords _
  · have hz : ground.getAt 0 y.content i = 0 :=
      match Nat.eq_zero_or_pos (ground.getAt 0 y.content i) with
      | .inl h0 => h0
      | .inr hp => absurd hp hocc
    have hvec2 : poly.oneValue
        (elim.vecScale (BPair.ofNat (ground.getAt 0 y.content j))
          y.coords)
        (elim.vecScale (BPair.ofNat (ground.getAt 0 y.content i))
          y.coords) :=
      poly.oneValue_trans
        (raise_exch_low i j hij y hz hcj hi hj hsz)
        (elim.vecAdd_null_left _ _ hlenR hnullR)
    refine BPair.oneValue_trans
      (BPair.add_congr
        (elim.dotP_null_tail_right _ _ (act_null j i y hz))
        (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans (BPair.unit_add _) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_symm
        (elim.dotP_vecScale_right y.coords y.coords _)) ?_
    refine BPair.oneValue_trans
      (elim.dotP_oneValue_right y.coords _ _ hvec2) ?_
    exact elim.dotP_vecScale_right y.coords y.coords _


/-- `lem:tops`(ii)'s pairing read: the positive pairing forces
the second letter's count at or below the first at a member off
the sum's unit. -/
theorem top_gap (i j : Nat) (hij : ¬ i = j) (y : HVec)
    (hi : i < y.content.length) (hj : j < y.content.length)
    (hsz : sized y) (htop : poly.unitTail (act i j y).coords)
    (hoff : ¬ poly.unitTail y.coords) :
    ground.getAt 0 y.content j ≤ ground.getAt 0 y.content i := by
  match Nat.lt_or_ge (ground.getAt 0 y.content i)
      (ground.getAt 0 y.content j) with
  | .inr hge => exact hge
  | .inl hlt =>
    have hcj : 0 < ground.getAt 0 y.content j :=
      Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
    have hsc := top_scalar i j hij y hi hj hsz htop hcj
    match Nat.le.dest hlt with
    | ⟨g, hg⟩ =>
      have hsum : ground.getAt 0 y.content i + (1 + g)
          = ground.getAt 0 y.content j := by
        rw [← Nat.add_assoc]
        exact hg
      have hofn : (BPair.ofNat (ground.getAt 0 y.content j)).oneValue
          (BPair.ofNat (ground.getAt 0 y.content i)
            + BPair.ofNat (1 + g)) := by
        rw [← hsum]
        exact BPair.ofNat_add (ground.getAt 0 y.content i) (1 + g)
      have hB : (BPair.ofNat (ground.getAt 0 y.content j)
            * elim.dotP y.coords y.coords).oneValue
          (BPair.ofNat (ground.getAt 0 y.content i)
              * elim.dotP y.coords y.coords
            + BPair.ofNat (1 + g) * elim.dotP y.coords y.coords) :=
        BPair.oneValue_trans (BPair.mul_congr_left hofn)
          (BPair.oneValue_of_eq (BPair.right_distrib _ _ _))
      have hX : ((elim.dotP (act j i y).coords (act j i y).coords
            + BPair.ofNat (1 + g) * elim.dotP y.coords y.coords)
          + BPair.ofNat (ground.getAt 0 y.content i)
              * elim.dotP y.coords y.coords).oneValue
          (BPair.unit
            + BPair.ofNat (ground.getAt 0 y.content i)
                * elim.dotP y.coords y.coords) := by
        refine BPair.oneValue_trans (BPair.oneValue_of_eq ?_)
          (BPair.oneValue_trans
            (BPair.oneValue_trans
              (BPair.add_congr (BPair.oneValue_refl _)
                (BPair.oneValue_symm hB)) hsc)
            (BPair.oneValue_symm (BPair.unit_add _)))
        rw [BPair.add_assoc, BPair.add_comm
            (BPair.ofNat (1 + g) * elim.dotP y.coords y.coords)
            (BPair.ofNat (ground.getAt 0 y.content i)
              * elim.dotP y.coords y.coords),
          ← BPair.add_assoc]
      have hnull := (elim.side_split
        (elim.dotP_self_side (act j i y).coords)
        (side_ofNat_mul (elim.dotP y.coords y.coords)
          (elim.dotP_self_side y.coords) (1 + g))
        (ground.BPair.add_cancel hX)).2
      exact absurd
        (elim.dotP_self_null y.coords
          (ground.mul_cancel_unit
            (BPair.ofNat_off_unit (1 + g)
              (Nat.le_add_right 1 g)) hnull))
        hoff


/-- `lem:tops`(ii) at the units carrier: a top's content is
dominant, each later letter at or below its predecessor —
`top_gap`'s read at the adjacent pair. -/
theorem dominant (d : Nat) (w : HVec) (hsz : sized w)
    (hwid : w.content.length = d)
    (hoff : ¬ poly.unitTail w.coords)
    (htop : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j w).coords) :
    ∀ k, k + 1 < d →
      ground.getAt 0 w.content (k + 1)
        ≤ ground.getAt 0 w.content k :=
  fun k hk1 =>
    top_gap k (k + 1) (fun he => Nat.succ_ne_self k he.symm) w
      (by rw [hwid]; exact Nat.lt_of_succ_lt hk1)
      (by rw [hwid]; exact hk1)
      hsz (htop (k + 1) hk1 k (Nat.lt_succ_self k)) hoff

end tops
