import MassGap.Lowerspan
/-!
`lem:blockirr` — the clauses at the span calculus's stated data:
`irred` (i), `endo_scalar` (ii), `hom_content` (iii), with clause
(iv) a named landing site below.

Clause (i), `irred` — the stated list's irreducibility read
at the span's own data: a pool `v :: tail` with `lem:lowerspan`'s
three span reads (sized, the width, and the words' provenance —
every word an occupied adjacent lowering image of an earlier
member) and a stated list `L` of span members closed under the
letter-pair actions splits into two disjuncts at the top
content's trichotomy.  The head's line is derived, not bound:
each provenance step drops the height fold by exactly one
(`lowerspan.ht_moveDn` at the width's own length with the
lowering's occupancy guard), so no word sits at the head's
content (`ht_strict`) and the top-content group is the head's
one-member list (`group_head`).  A member of `L` at the head's content off the
sum's unit puts the head inside `L`'s own group span — the line
exchange, the head's group solved through that member and the
roles swapped at the cleared combination — and the provenance
walk carries the reads down the pool: `blockcount.act_transport`
at the closure hypothesis transports the earlier member's span
read to the word's own group, the positional bridge
`moveAt (j+1) j = units.moveDn j` identifying the lowering with
the letter-pair action.  Otherwise
every member of `L` at the head's content reads the unit, and the
transpose walk closes the second disjunct: the pairing against a
lowering image moves through `elim.dotP_matVec_transpose` and
`units.matUnit_transpose_read` to the exchanged letters' action on
the `L` member, whose settled read the walk's earlier step kills
term by term, so a member of `L` is perpendicular to every pool
member carrying its own content — the walk's guard, and the only
pairings its own span read consumes, forcing its self-pairing to
the sum's
unit and its coordinates to the unit tail at the pairing's
definiteness (`elim.dotP_self_null`).

Clause (ii), `endo_scalar` — a matrix family on the span, one
matrix per occupied content against the monomial coordinates,
with the moved reads at every letter pair and the top's value
settled, reads the cleared line
`⟨v,v⟩·(T w) ≐ ⟨T v, v⟩·w` at every member: the base is the
head group's residual read (`group_head` at the derived head
line), the step the moved read across each provenance lowering
(`elim.matVec_vecScale_free`, `elim.matVec_congr`), and the walk
along the provenance carries the display from the head to every
member.  Clause (iii), `hom_content` — a
family from one span into another at settled values and some
value off the sum's unit reads the top contents equal: the
target head sits off the sum's unit derived (`head_off`: at a
unit head every word of the target pool reads the unit tail and
so does every value settled there, against the value off it),
clause (i) at the value list inside the target
(`elim.spanRel_matVec` the span's matrix transport) settles the
target's members in the value list's span, and the height pincer
(`ht_strict` at both pools) closes the content comparison.

Clause (iv), one dimension per shape, `dim_eq`: two pools at the
span calculus's stated data whose heads read one content read one
count.  The pool is its head's word images (`pool_words`, the
provenance walked at the positional bridge `lowerH_act`), each
content group a word list at the realization's own congruence
(`blockcount.groupAt_map_congr`), and the count runs
content group by content group: a group's words at the partner
top read images inside the partner's group at the moved content
(`word_span`, the head at its listed row with
`blockcount.act_transport` at the settled letters), independent
at the words' pairings — the Gram transports across the two tops
at the cross-multiplied scale (`blockcount.wordGram` termwise
through the pairing's bilinearity, `rowGram`/`comboGram`), a null
combination crossing to the first group whose independence reads
the coefficients back (`image_indep`, the head's self-pairing off
the unit at `elim.indep_row_off`) — so the groups' counts sit at
or below each other's (`occ_le` at `elim.span_count_le`), and the
occupied contents' counts sum to the dimensions at the partition
over a distinct covering index (`countOf_partition`), the
orthogonal grading's read.  The sized and width binders are
`con:places`' member definition — a homogeneous member is its
coordinate family over its own content's monomials, the power at
the declared letter count — the carrier's well-formedness data at
the tree's uniform convention; that `indepAll`'s per-group row
widths and the provenance's chain re-derive them is a property of
those reads' shape conjuncts (a certificate states its orders),
never statement data.  The top binders are the tex's own frame
(the clause's two tops), re-derivable at the stated data since a
raising image's group sits above the head where the height fold
refuses every word.  The shared content, independence, closure
and provenance binders carry their committed refusals.
-/

namespace blockirr
open ground places blockcount

/-! The positional and span kit the two walks consume: the entry
at a key is a member and a member sits at a key, the unit family's
tail read, a row family's pairing read, a settled vector's span at
the content enumeration, a member's own row inside its group, and
the adjacent lowering's two identifications. -/

/-- A row family whose every row pairs to the sum's unit maps to
the unit tail, the combination's null pairing read rowwise. -/
private theorem unitTail_rowmap : ∀ (M : elim.Mat) (u : List BPair),
    (∀ k, k < M.length →
      (elim.dotP (ground.getAt ([] : List BPair) M k) u).oneValue
        BPair.unit) →
    poly.unitTail (M.map (fun r => elim.dotP r u))
  | [], _, _ => trivial
  | _ :: t, u, h =>
    ⟨h 0 (Nat.succ_pos t.length),
     unitTail_rowmap t u (fun k hk => h (k + 1) (Nat.succ_lt_succ hk))⟩

/-- A member's coordinates are a listed row of its own content
group. -/
private theorem group_index (mu : List Nat) (y : HVec)
    (hc : y.content = mu) :
    ∀ pool : List HVec, y ∈ pool →
      ∃ k, k < (groupAt pool mu).length
        ∧ ground.getAt ([] : List BPair) (groupAt pool mu) k
          = y.coords := by
  intro pool
  induction pool with
  | nil => exact fun h => nomatch h
  | cons z t ih =>
    intro h
    cases h with
    | head =>
      have hb : (y.content == mu) = true := by
        rw [hc]
        exact ground.listEqBeq mu
      have hg : groupAt (y :: t) mu
          = match y.content == mu with
            | true => y.coords :: groupAt t mu
            | false => groupAt t mu := groupAt_cons y t mu
      rw [hb] at hg
      have hg2 : groupAt (y :: t) mu = y.coords :: groupAt t mu := hg
      refine ⟨0, ?_, ?_⟩
      · rw [hg2]
        exact Nat.succ_pos _
      · rw [hg2]
        rfl
    | tail _ hm =>
      match ih hm with
      | ⟨k, hk, he⟩ =>
        have hg : groupAt (z :: t) mu
            = match z.content == mu with
              | true => z.coords :: groupAt t mu
              | false => groupAt t mu := groupAt_cons z t mu
        cases hb : z.content == mu with
        | true =>
          rw [hb] at hg
          have hg2 : groupAt (z :: t) mu = z.coords :: groupAt t mu := hg
          refine ⟨k + 1, ?_, ?_⟩
          · rw [hg2]
            exact Nat.succ_lt_succ hk
          · rw [hg2]
            exact he
        | false =>
          rw [hb] at hg
          have hg2 : groupAt (z :: t) mu = groupAt t mu := hg
          refine ⟨k, ?_, ?_⟩
          · rw [hg2]
            exact hk
          · rw [hg2]
            exact he

/-! The head's line, derived at the provenance: every word's
content reads the height fold strictly below the head's, so the
head alone carries the top content and the line read is the
one-member list's own (`lem:lowerspan`'s descent at
`lowerspan.ht`, the width supplying the moved letter's bound and
the lowering guard its occupancy). -/

/-- The height descent along the pool: every position's content
reads the fold at or below the head's, one step per provenance
lowering. -/
private theorem htGo (d : Nat) (v : HVec) (tail : List HVec)
    (hwid : ∀ w ∈ v :: tail, w.content.length = d)
    (hprov : ∀ k, k < tail.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tail) i)
          = some (getAt (⟨[], []⟩ : HVec) tail k)) :
    ∀ m p : Nat, p ≤ m → p < (v :: tail).length →
      lowerspan.ht (getAt (⟨[], []⟩ : HVec) (v :: tail) p).content
        ≤ lowerspan.ht v.content
  | 0, 0, _, _ => Nat.le_refl _
  | 0, _ + 1, hp, _ => absurd hp (Nat.not_succ_le_zero _)
  | _ + 1, 0, _, _ => Nat.le_refl _
  | m + 1, k + 1, hp, hlt => by
    have hk : k < tail.length := Nat.lt_of_succ_lt_succ hlt
    match hprov k hk with
    | ⟨i, hik, j, hjd, hlow⟩ =>
      have hip : i < (v :: tail).length :=
        Nat.lt_trans (Nat.lt_of_le_of_lt hik hk)
          (Nat.lt_succ_self tail.length)
      have hih := htGo d v tail hwid hprov m i
        (Nat.le_trans hik (Nat.le_of_succ_le_succ hp)) hip
      have hum := ground.mem_getAt (⟨[], []⟩ : HVec) (v :: tail) i hip
      have hr := lowerH_reads hlow
      have hjc : j + 1
          < (getAt (⟨[], []⟩ : HVec) (v :: tail) i).content.length := by
        rw [hwid _ hum]
        exact hjd
      have hstep := lowerspan.ht_moveDn j
        (getAt (⟨[], []⟩ : HVec) (v :: tail) i).content hjc hr.1
      show lowerspan.ht (getAt (⟨[], []⟩ : HVec) tail k).content
        ≤ lowerspan.ht v.content
      rw [hr.2]
      refine Nat.le_trans ?_ hih
      rw [← hstep]
      exact Nat.le_succ _

/-- Every provenance word sits strictly below the head at the
height fold, one drop per lowering step. -/
theorem ht_strict (d : Nat) (v : HVec) (tail : List HVec)
    (hwid : ∀ w ∈ v :: tail, w.content.length = d)
    (hprov : ∀ k, k < tail.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tail) i)
          = some (getAt (⟨[], []⟩ : HVec) tail k)) :
    ∀ w ∈ tail, lowerspan.ht w.content < lowerspan.ht v.content := by
  intro w hm
  match ground.getAt_of_mem (⟨[], []⟩ : HVec) hm with
  | ⟨k, hk, he⟩ =>
    match hprov k hk with
    | ⟨i, hik, j, hjd, hlow⟩ =>
      have hip : i < (v :: tail).length :=
        Nat.lt_trans (Nat.lt_of_le_of_lt hik hk)
          (Nat.lt_succ_self tail.length)
      have hih := htGo d v tail hwid hprov i i (Nat.le_refl i) hip
      have hum := ground.mem_getAt (⟨[], []⟩ : HVec) (v :: tail) i hip
      have hr := lowerH_reads hlow
      have hjc : j + 1 < (getAt (⟨[], []⟩ : HVec)
          (v :: tail) i).content.length := by
        rw [hwid _ hum]
        exact hjd
      have hstep := lowerspan.ht_moveDn j
        (getAt (⟨[], []⟩ : HVec) (v :: tail) i).content hjc hr.1
      have hwc : w.content
          = units.moveDn j
            (getAt (⟨[], []⟩ : HVec) (v :: tail) i).content := by
        rw [← he]
        exact hr.2
      rw [hwc]
      refine Nat.lt_of_lt_of_le ?_ hih
      rw [← hstep]
      exact Nat.lt_succ_self _

/-- The top-content group is the head's one-member list: the
provenance's height descent puts every word strictly below, so no
word carries the head's content (`lem:lowerspan`'s top line). -/
theorem group_head (d : Nat) (v : HVec) (tail : List HVec)
    (hwid : ∀ w ∈ v :: tail, w.content.length = d)
    (hprov : ∀ k, k < tail.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tail) i)
          = some (getAt (⟨[], []⟩ : HVec) tail k)) :
    groupAt (v :: tail) v.content = [v.coords] := by
  have hg : groupAt (v :: tail) v.content
      = match v.content == v.content with
        | true => v.coords :: groupAt tail v.content
        | false => groupAt tail v.content :=
    groupAt_cons v tail v.content
  rw [ground.listEqBeq v.content] at hg
  have hg2 : groupAt (v :: tail) v.content
      = v.coords :: groupAt tail v.content := hg
  have hnil : groupAt tail v.content = [] := by
    refine groupAt_nil_of_not_mem tail v.content ?_
    intro hm
    match ground.mem_map_of HVec.content tail v.content hm with
    | ⟨w, hw, hwc⟩ =>
      have hlt := ht_strict d v tail hwid hprov w hw
      rw [hwc] at hlt
      exact absurd hlt (Nat.lt_irrefl _)
  rw [hg2, hnil]

/-! The two walk steps at one lowering: the settled read
transported through the closure hypothesis, and the pairing
carried across the transpose to the exchanged letters' action. -/

/-- The lowering image of a settled member is settled: the
letter-pair action's span transport at the stated list's own
closure. -/
private theorem lower_settle (d j : Nat) (L : List HVec) (u w : HVec)
    (hus : sized u) (hLsz : ∀ x ∈ L, sized x)
    (hLcl : ∀ x ∈ L, ∀ i < d, ∀ j < d, ¬ i = j →
      settledAt L (act i j x))
    (hjd : j + 1 < d) (hlow : lowerH j u = some w)
    (hu : settledAt L u) : settledAt L w := by
  have hspan := blockcount.span_of_settled L u hLsz hus hu
  have himg : ∀ x ∈ L, settledAt L (act (j + 1) j x) :=
    fun x hx => hLcl x hx (j + 1) hjd j (Nat.lt_of_succ_lt hjd)
      (Nat.succ_ne_self j)
  have htr := act_transport L (j + 1) j hLsz himg u.content u.coords
    hus hspan
  rw [moveAt_moveDn j u.content] at htr
  rw [blockcount.lowerH_eq hlow]
  refine Or.inr ?_
  show elim.spanRel
    (elim.matVec (units.matUnitAt (units.moveDn j u.content)
      u.content (j + 1) j) u.coords).length
    (groupAt L (units.moveDn j u.content))
    (elim.matVec (units.matUnitAt (units.moveDn j u.content)
      u.content (j + 1) j) u.coords)
  rw [units.matVec_matUnitAt_length]
  exact htr

/-- The pairing against a lowering image: the transpose's letter
exchange turns it into the pairing against the exchanged action on
the stated list's member, whose settled read the earlier member's
perpendicularity kills term by term. -/
private theorem lower_pair (d j : Nat) (L : List HVec) (u w x : HVec)
    (hus : sized u) (hud : u.content.length = d)
    (hLsz : ∀ y ∈ L, sized y)
    (hLcl : ∀ y ∈ L, ∀ i < d, ∀ j < d, ¬ i = j →
      settledAt L (act i j y))
    (hjd : j + 1 < d) (hlow : lowerH j u = some w)
    (hxL : x ∈ L) (hxc : x.content = w.content)
    (hih : ∀ y ∈ L, y.content = u.content →
      (elim.dotP y.coords u.coords).oneValue BPair.unit) :
    (elim.dotP x.coords w.coords).oneValue BPair.unit := by
  have hw := blockcount.lowerH_eq hlow
  have hocc := (lowerH_reads hlow).1
  rw [hw] at hxc
  have hxc' : x.content = units.moveDn j u.content := hxc
  have hxs : sized x := hLsz x hxL
  have hxlen : x.coords.length
      = (units.matUnitAt (units.moveDn j u.content) u.content
          (j + 1) j).length := by
    rw [units.length_matUnitAt, hxs, hxc']
  have hjc : j + 1 < u.content.length := by
    rw [hud]
    exact hjd
  have hjm : j < (units.moveDn j u.content).length := by
    rw [units.length_moveDn]
    exact Nat.lt_of_succ_lt hjc
  have hround : moveAt j (j + 1) (units.moveDn j u.content)
      = u.content := by
    rw [← moveAt_moveDn j u.content]
    exact moveAt_round_at j (j + 1) u.content hocc
  have hout := out_gen u.content (j + 1) j hjc (Nat.succ_ne_self j)
  rw [moveAt_moveDn j u.content] at hout
  have hout' := out_gen (units.moveDn j u.content) j (j + 1) hjm
    (fun he => Nat.succ_ne_self j he.symm)
  rw [hround] at hout'
  have htrd := units.matUnit_transpose_read
    (units.moveDn j u.content) u.content (j + 1) j hout hout'
  have hactc : (act j (j + 1) x).content = u.content := by
    show moveAt j (j + 1) x.content = u.content
    rw [hxc', hround]
  have hact : (act j (j + 1) x).coords
      = elim.matVec (units.matUnitAt u.content
          (units.moveDn j u.content) j (j + 1)) x.coords := by
    show elim.matVec (units.matUnitAt (moveAt j (j + 1) x.content)
      x.content j (j + 1)) x.coords = _
    rw [hxc', hround]
  have hset := hLcl x hxL j (Nat.lt_of_succ_lt hjd) (j + 1) hjd
    (fun he => Nat.succ_ne_self j he.symm)
  have key : (elim.dotP u.coords (act j (j + 1) x).coords).oneValue
      BPair.unit := by
    cases hset with
    | inl hu0 =>
      exact elim.dotP_null_tail_right u.coords _
        (unitTail_of_allU _ hu0)
    | inr hsp =>
      have hzlen : (act j (j + 1) x).coords.length
          = (monomialsAt u.content).length := by
        rw [hact, units.matVec_matUnitAt_length]
      rw [hzlen, hactc] at hsp
      obtain ⟨c₀, cs, hc₀, hcs, hone⟩ := elim.span_elim hsp
      refine ground.mul_cancel_unit hc₀ ?_
      refine BPair.oneValue_trans (BPair.oneValue_symm
        (elim.dotP_vecScale_right u.coords
          (act j (j + 1) x).coords c₀)) ?_
      refine BPair.oneValue_trans
        (elim.dotP_oneValue_right u.coords _ _ hone) ?_
      refine BPair.oneValue_trans (BPair.oneValue_of_eq
        (elim.dotP_comm u.coords _)) ?_
      refine BPair.oneValue_trans (BPair.oneValue_symm
        (elim.dotP_matVec (monomialsAt u.content).length cs
          (groupAt L u.content) u.coords
          (rowsLen_groupAt u.content L hLsz) hus hcs)) ?_
      refine BPair.oneValue_trans (elim.dotP_oneValue_right cs _ _
        (elim.matVec_dotPmap (groupAt L u.content) u.coords)) ?_
      refine elim.dotP_null_tail_right cs _
        (unitTail_rowmap (groupAt L u.content) u.coords ?_)
      intro k hk
      match groupAt_rows (fun y => y ∈ L) L (fun _ hy => hy)
          u.content k hk with
      | ⟨y, hyL, hyc, hrow⟩ =>
        rw [hrow]
        exact hih y hyL hyc
  rw [hw]
  show (elim.dotP x.coords
    (elim.matVec (units.matUnitAt (units.moveDn j u.content)
      u.content (j + 1) j) u.coords)).oneValue BPair.unit
  refine BPair.oneValue_trans (BPair.oneValue_of_eq
    (elim.dotP_comm x.coords _)) ?_
  refine BPair.oneValue_trans
    (elim.dotP_matVec_transpose (monomialsAt u.content).length
      (units.matUnitAt (units.moveDn j u.content) u.content
        (j + 1) j) u.coords x.coords
      (units.rowsLen_matUnitAt _ _ (j + 1) j) hus hxlen) ?_
  refine BPair.oneValue_trans (elim.dotP_oneValue_right u.coords _ _
    (elim.matVec_matOne _ _ _ htrd)) ?_
  rw [← hact]
  exact key

/-! The two walks along the pool's positions, the provenance the
descent: the settled read carried down for the first disjunct and
the perpendicularity for the second, each stepped at the position
its word is an image of. -/

/-- The settling walk: at the head settled in the stated list's
span, every pool position is. -/
private theorem settleGo (d : Nat) (v : HVec) (tail L : List HVec)
    (hsz : ∀ w ∈ v :: tail, sized w)
    (hprov : ∀ k, k < tail.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tail) i)
          = some (getAt (⟨[], []⟩ : HVec) tail k))
    (hLsz : ∀ x ∈ L, sized x)
    (hLcl : ∀ x ∈ L, ∀ i < d, ∀ j < d, ¬ i = j →
      settledAt L (act i j x))
    (hbase : settledAt L v) :
    ∀ m p : Nat, p ≤ m → p < (v :: tail).length →
      settledAt L (getAt (⟨[], []⟩ : HVec) (v :: tail) p)
  | 0, 0, _, _ => hbase
  | 0, _ + 1, hp, _ => absurd hp (Nat.not_succ_le_zero _)
  | _ + 1, 0, _, _ => hbase
  | m + 1, k + 1, hp, hlt => by
    have hk : k < tail.length := Nat.lt_of_succ_lt_succ hlt
    match hprov k hk with
    | ⟨i, hik, j, hjd, hlow⟩ =>
      have hip : i < (v :: tail).length :=
        Nat.lt_trans (Nat.lt_of_le_of_lt hik hk)
          (Nat.lt_succ_self tail.length)
      have hih := settleGo d v tail L hsz hprov hLsz hLcl hbase m i
        (Nat.le_trans hik (Nat.le_of_succ_le_succ hp)) hip
      have hum := ground.mem_getAt (⟨[], []⟩ : HVec) (v :: tail) i hip
      show settledAt L (getAt (⟨[], []⟩ : HVec) tail k)
      exact lower_settle d j L _ _ (hsz _ hum) hLsz hLcl hjd hlow hih

/-- The perpendicularity walk: at the head's content reading the
unit, every member of the stated list is perpendicular to every
pool position. -/
private theorem walkGo (d : Nat) (v : HVec) (tail L : List HVec)
    (hsz : ∀ w ∈ v :: tail, sized w)
    (hwid : ∀ w ∈ v :: tail, w.content.length = d)
    (hprov : ∀ k, k < tail.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tail) i)
          = some (getAt (⟨[], []⟩ : HVec) tail k))
    (hLsz : ∀ x ∈ L, sized x)
    (hLcl : ∀ x ∈ L, ∀ i < d, ∀ j < d, ¬ i = j →
      settledAt L (act i j x))
    (hbase : ∀ x ∈ L, x.content = v.content → poly.unitTail x.coords) :
    ∀ m p : Nat, p ≤ m → p < (v :: tail).length →
      ∀ x ∈ L, x.content
          = (getAt (⟨[], []⟩ : HVec) (v :: tail) p).content →
        (elim.dotP x.coords
          (getAt (⟨[], []⟩ : HVec) (v :: tail) p).coords).oneValue
          BPair.unit
  | 0, 0, _, _ => fun x hx hxc =>
    elim.dotP_null_tail_left x.coords v.coords (hbase x hx hxc)
  | 0, _ + 1, hp, _ => absurd hp (Nat.not_succ_le_zero _)
  | _ + 1, 0, _, _ => fun x hx hxc =>
    elim.dotP_null_tail_left x.coords v.coords (hbase x hx hxc)
  | m + 1, k + 1, hp, hlt => by
    intro x hxL hxc
    have hk : k < tail.length := Nat.lt_of_succ_lt_succ hlt
    match hprov k hk with
    | ⟨i, hik, j, hjd, hlow⟩ =>
      have hip : i < (v :: tail).length :=
        Nat.lt_trans (Nat.lt_of_le_of_lt hik hk)
          (Nat.lt_succ_self tail.length)
      have hih := walkGo d v tail L hsz hwid hprov hLsz hLcl hbase m i
        (Nat.le_trans hik (Nat.le_of_succ_le_succ hp)) hip
      have hum := ground.mem_getAt (⟨[], []⟩ : HVec) (v :: tail) i hip
      exact lower_pair d j L _ _ x (hsz _ hum) (hwid _ hum) hLsz hLcl
        hjd hlow hxL hxc hih

/-- The top content's trichotomy: at a stated content either some
member of the list carries it off the sum's unit, or every member
carrying it reads the unit tail. -/
private theorem topSplit (mu : List Nat) : ∀ L : List HVec,
    (∃ y, y ∈ L ∧ y.content = mu ∧ ¬ poly.unitTail y.coords)
      ∨ (∀ y ∈ L, y.content = mu → poly.unitTail y.coords)
  | [] => Or.inr (fun _ h => nomatch h)
  | z :: t => by
    by_cases hc : z.content = mu
    · by_cases hu : poly.unitTail z.coords
      · match topSplit mu t with
        | .inl ⟨y, hy, hyc, hyu⟩ =>
          exact Or.inl ⟨y, List.Mem.tail z hy, hyc, hyu⟩
        | .inr h => exact Or.inr (memAll_cons (fun _ => hu) h)
      · exact Or.inl ⟨z, List.Mem.head t, hc, hu⟩
    · match topSplit mu t with
      | .inl ⟨y, hy, hyc, hyu⟩ =>
        exact Or.inl ⟨y, List.Mem.tail z hy, hyc, hyu⟩
      | .inr h => exact Or.inr (memAll_cons (fun he => absurd he hc) h)

/-- `lem:blockirr`(i): at a stated list of span members closed
under the letter-pair actions, either every pool member joins the
list's own span or every member of the list reads the sum's
unit. -/
theorem irred (d : Nat) (v : HVec) (tail L : List HVec)
    (hsz : ∀ w ∈ v :: tail, sized w)
    (hwid : ∀ w ∈ v :: tail, w.content.length = d)
    (hprov : ∀ k, k < tail.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tail) i)
          = some (getAt (⟨[], []⟩ : HVec) tail k))
    (hLsz : ∀ x ∈ L, sized x)
    (hLmem : ∀ x ∈ L, settledAt (v :: tail) x)
    (hLcl : ∀ x ∈ L, ∀ i < d, ∀ j < d, ¬ i = j →
        settledAt L (act i j x)) :
    (∀ w ∈ v :: tail, settledAt L w)
      ∨ (∀ x ∈ L, poly.unitTail x.coords) := by
  match topSplit v.content L with
  | .inl ⟨y, hyL, hyc, hyu⟩ =>
    refine Or.inl ?_
    have hvs : sized v := hsz v (List.Mem.head tail)
    have hys : sized y := hLsz y hyL
    have hyn : y.coords.length = (monomialsAt v.content).length := by
      rw [hys, hyc]
    have hyG := blockcount.span_of_settled (v :: tail) y hsz hys (hLmem y hyL)
    rw [hyc, group_head d v tail hwid hprov] at hyG
    obtain ⟨c₀, cs, hc₀, hcs, hone⟩ := elim.span_elim hyG
    match cs, hcs, hone with
    | [], hcs, _ => exact Nat.noConfusion hcs
    | _ :: _ :: _, hcs, _ => exact Nat.noConfusion (Nat.succ.inj hcs)
    | [a], _, hone =>
      have hlen1 : (elim.vecScale a v.coords).length
          = (List.replicate (monomialsAt v.content).length
              BPair.unit).length := by
        rw [elim.length_vecScale, ground.length_replicate, hvs]
      have hlen2 : (elim.vecScale c₀ y.coords).length
          = (List.replicate (monomialsAt v.content).length
              BPair.unit).length := by
        rw [elim.length_vecScale, ground.length_replicate, hyn]
      have ha : ¬ a.oneValue BPair.unit := by
        intro ha0
        have hut : poly.unitTail
            (elim.combo (monomialsAt v.content).length [a]
              [v.coords]) :=
          elim.unitTail_vecAdd_of
            (elim.unitTail_vecScale_unit ha0 v.coords)
            (poly.unitTail_replicate _)
        have huy : poly.unitTail (elim.vecScale c₀ y.coords) :=
          poly.oneValue_unitTail hone hut
        have hnil : elim.spanRel (monomialsAt v.content).length
            ([] : elim.Mat) y.coords :=
          elim.span_intro _ [] y.coords trivial hyn
            ⟨c₀, [], hc₀, rfl,
             poly.unitTail_oneValue huy (poly.unitTail_replicate _)⟩
        exact hyu (elim.spanRel_nil_unit _ y.coords hnil)
      have hA : poly.oneValue (elim.vecScale a v.coords)
          (elim.combo (monomialsAt v.content).length [a]
            [v.coords]) :=
        poly.oneValue_symm
          (elim.vecAdd_null_right _ _ hlen1 (poly.unitTail_replicate _))
      have hB : poly.oneValue (elim.vecScale c₀ y.coords)
          (elim.combo (monomialsAt v.content).length [c₀]
            [y.coords]) :=
        poly.oneValue_symm
          (elim.vecAdd_null_right _ _ hlen2 (poly.unitTail_replicate _))
      have hspanv : elim.spanRel (monomialsAt v.content).length
          [y.coords] v.coords :=
        elim.span_intro _ [y.coords] v.coords ⟨hyn, trivial⟩ hvs
          ⟨a, [c₀], ha, rfl,
           poly.oneValue_trans hA
             (poly.oneValue_trans (poly.oneValue_symm hone) hB)⟩
      have hLGr : elim.rowsLen (monomialsAt v.content).length
          (groupAt L v.content) := rowsLen_groupAt v.content L hLsz
      have hyrow : elim.spanRel (monomialsAt v.content).length
          (groupAt L v.content) y.coords := by
        match group_index v.content y hyc L hyL with
        | ⟨k, hk, he⟩ =>
          have h := elim.spanRel_getAt (monomialsAt v.content).length
            (groupAt L v.content) k hk hLGr
          rw [he] at h
          exact h
      have hvL : elim.spanRel (monomialsAt v.content).length
          (groupAt L v.content) v.coords :=
        elim.spanRel_trans _ [y.coords] (groupAt L v.content)
          v.coords ⟨hyn, trivial⟩ hLGr
          (fun k hk =>
            match k, hk with
            | 0, _ => hyrow
            | _ + 1, hk =>
              absurd (Nat.lt_of_succ_lt_succ hk) (Nat.not_lt_zero _))
          hspanv
      have hbase : settledAt L v := by
        refine Or.inr ?_
        rw [hvs]
        exact hvL
      intro w hw
      match ground.getAt_of_mem (⟨[], []⟩ : HVec) hw with
      | ⟨p, hp, hpe⟩ =>
        rw [← hpe]
        exact settleGo d v tail L hsz hprov hLsz hLcl hbase p p
          (Nat.le_refl p) hp
  | .inr hall =>
    refine Or.inr ?_
    have walk : ∀ w ∈ v :: tail, ∀ x ∈ L, x.content = w.content →
        (elim.dotP x.coords w.coords).oneValue BPair.unit := by
      intro w hw
      match ground.getAt_of_mem (⟨[], []⟩ : HVec) hw with
      | ⟨p, hp, hpe⟩ =>
        rw [← hpe]
        exact walkGo d v tail L hsz hwid hprov hLsz hLcl hall p p
          (Nat.le_refl p) hp
    intro x hxL
    have hxs : sized x := hLsz x hxL
    have hxG := blockcount.span_of_settled (v :: tail) x hsz hxs (hLmem x hxL)
    obtain ⟨c₀, cs, hc₀, hcs, hone⟩ := elim.span_elim hxG
    refine elim.dotP_self_null x.coords ?_
    refine ground.mul_cancel_unit hc₀ ?_
    refine BPair.oneValue_trans (BPair.oneValue_symm
      (elim.dotP_vecScale_right x.coords x.coords c₀)) ?_
    refine BPair.oneValue_trans
      (elim.dotP_oneValue_right x.coords _ _ hone) ?_
    refine BPair.oneValue_trans (BPair.oneValue_of_eq
      (elim.dotP_comm x.coords _)) ?_
    refine BPair.oneValue_trans (BPair.oneValue_symm
      (elim.dotP_matVec (monomialsAt x.content).length cs
        (groupAt (v :: tail) x.content) x.coords
        (rowsLen_groupAt x.content (v :: tail) hsz) hxs hcs)) ?_
    refine BPair.oneValue_trans (elim.dotP_oneValue_right cs _ _
      (elim.matVec_dotPmap (groupAt (v :: tail) x.content)
        x.coords)) ?_
    refine elim.dotP_null_tail_right cs _
      (unitTail_rowmap (groupAt (v :: tail) x.content) x.coords ?_)
    intro k hk
    match groupAt_rows (fun w => w ∈ v :: tail) (v :: tail)
        (fun _ hw => hw) x.content k hk with
    | ⟨w, hwm, hwc, hrow⟩ =>
      rw [hrow, elim.dotP_comm w.coords x.coords]
      exact walk w hwm x hxL hwc.symm

/-! `lem:blockirr` clause (ii)'s kit: the scaling's composition and
its two congruences, the unit tail's scaling, the integral read
entrywise, and the square order's own length read. -/

/-! The cleared line at the head (`lem:blockirr`(ii)'s base) and
its transport down one lowering: the value's own settled read
solves the head's line at the one-member group, and the pairing
against the head turns the clearing scalars into the display's
two folds. -/

/-- The display at the head: the value's settled read at the top
content's one-member group, the clearing cancelled by the integral
read at the pairing against the head. -/
private theorem endo_base (d : Nat) (v : HVec) (tail : List HVec)
    (T : List Nat → elim.Mat)
    (hwid : ∀ w ∈ v :: tail, w.content.length = d)
    (hprov : ∀ k, k < tail.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tail) i)
          = some (getAt (⟨[], []⟩ : HVec) tail k))
    (hTv : elim.sqAt (T v.content) v.coords.length)
    (hval : settledAt (v :: tail)
      ⟨v.content, elim.matVec (T v.content) v.coords⟩) :
    poly.oneValue
      (elim.vecScale (elim.dotP v.coords v.coords)
        (elim.matVec (T v.content) v.coords))
      (elim.vecScale
        (elim.dotP (elim.matVec (T v.content) v.coords) v.coords)
        v.coords) := by
  have hN : (elim.matVec (T v.content) v.coords).length
      = v.coords.length := by
    rw [elim.matVec_length]
    exact elim.sqAt_len hTv
  cases hval with
  | inl hu =>
    have hut : poly.unitTail (elim.matVec (T v.content) v.coords) :=
      unitTail_of_allU _ hu
    refine poly.unitTail_oneValue (elim.unitTail_vecScale _ _ hut) ?_
    exact elim.unitTail_vecScale_unit
      (elim.dotP_null_tail_left _ v.coords hut) v.coords
  | inr hs =>
    have hs2 : elim.spanRel
        (elim.matVec (T v.content) v.coords).length
        (groupAt (v :: tail) v.content)
        (elim.matVec (T v.content) v.coords) := hs
    rw [group_head d v tail hwid hprov] at hs2
    obtain ⟨c₀, cs, hc₀, hcs, hone⟩ := elim.span_elim hs2
    match cs, hcs, hone with
    | [], hcs, _ => exact Nat.noConfusion hcs
    | _ :: _ :: _, hcs, _ => exact Nat.noConfusion (Nat.succ.inj hcs)
    | [a], _, hone =>
      have hlenR : (elim.vecScale a v.coords).length
          = (elim.combo (elim.matVec (T v.content) v.coords).length
              [] ([] : elim.Mat)).length := by
        rw [elim.length_vecScale,
          elim.length_combo (elim.matVec (T v.content) v.coords).length
            [] ([] : elim.Mat) trivial]
        exact hN.symm
      have hp1 : (elim.dotP v.coords (elim.vecScale c₀
            (elim.matVec (T v.content) v.coords))).oneValue
          (c₀ * elim.dotP
            (elim.matVec (T v.content) v.coords) v.coords) := by
        refine BPair.oneValue_trans
          (elim.dotP_vecScale_right v.coords
            (elim.matVec (T v.content) v.coords) c₀) ?_
        exact BPair.mul_congr (BPair.oneValue_refl c₀)
          (BPair.oneValue_of_eq (elim.dotP_comm v.coords _))
      have hp2 : (elim.dotP v.coords (elim.vecScale c₀
            (elim.matVec (T v.content) v.coords))).oneValue
          (a * elim.dotP v.coords v.coords) := by
        refine BPair.oneValue_trans
          (elim.dotP_oneValue_right v.coords _ _ hone) ?_
        refine BPair.oneValue_trans
          (elim.dotP_vecAdd v.coords _ _
            (elim.length_vecScale a v.coords)
            ((elim.length_combo
                (elim.matVec (T v.content) v.coords).length
                [] ([] : elim.Mat) trivial).trans hN)) ?_
        refine BPair.oneValue_trans
          (BPair.add_congr
            (elim.dotP_vecScale_right v.coords v.coords a)
            (elim.dotP_repl_unit v.coords _)) ?_
        exact BPair.add_unit _
      have hpair := BPair.oneValue_trans (BPair.oneValue_symm hp1) hp2
      have hL : poly.oneValue
          (elim.vecScale c₀ (elim.vecScale
            (elim.dotP v.coords v.coords)
            (elim.matVec (T v.content) v.coords)))
          (elim.vecScale (a * elim.dotP v.coords v.coords)
            v.coords) := by
        rw [elim.vecScale_vecScale, BPair.mul_comm c₀ _, ← elim.vecScale_vecScale]
        refine poly.oneValue_trans (elim.vecScale_oneValue _ _ _ hone) ?_
        refine poly.oneValue_trans
          (elim.vecScale_oneValue _ _ _
            (elim.vecAdd_null_right _ _ hlenR (poly.unitTail_replicate _))) ?_
        show poly.oneValue
          (elim.vecScale (elim.dotP v.coords v.coords)
            (elim.vecScale a v.coords))
          (elim.vecScale (a * elim.dotP v.coords v.coords) v.coords)
        rw [elim.vecScale_vecScale, BPair.mul_comm _ a]
        exact poly.oneValue_refl _
      have hR : poly.oneValue
          (elim.vecScale c₀ (elim.vecScale
            (elim.dotP (elim.matVec (T v.content) v.coords) v.coords)
            v.coords))
          (elim.vecScale (a * elim.dotP v.coords v.coords)
            v.coords) := by
        rw [elim.vecScale_vecScale]
        exact elim.vecScale_congr hpair v.coords
      exact elim.oneValue_unscale c₀ hc₀ _ _
        (poly.oneValue_trans hL (poly.oneValue_symm hR))

/-- The display's transport down one lowering: the intertwining
read moves the value through the lowering's matrix and the
scalings commute past it. -/
private theorem endo_step (d j : Nat) (T : List Nat → elim.Mat)
    (S S' : BPair) (u w : HVec)
    (hus : sized u)
    (hTu : elim.sqAt (T u.content) u.coords.length)
    (hmvu : ∀ i < d, ∀ j < d, ¬ i = j →
      poly.oneValue
        (elim.matVec
          (units.matUnitAt (moveAt i j u.content) u.content i j)
          (elim.matVec (T u.content) u.coords))
        (elim.matVec (T (moveAt i j u.content))
          (elim.matVec
            (units.matUnitAt (moveAt i j u.content) u.content i j)
            u.coords)))
    (hjd : j + 1 < d) (hlow : lowerH j u = some w)
    (hih : poly.oneValue
      (elim.vecScale S (elim.matVec (T u.content) u.coords))
      (elim.vecScale S' u.coords)) :
    poly.oneValue
      (elim.vecScale S (elim.matVec (T w.content) w.coords))
      (elim.vecScale S' w.coords) := by
  have hw := blockcount.lowerH_eq hlow
  have hmv := hmvu (j + 1) hjd j (Nat.lt_of_succ_lt hjd)
    (Nat.succ_ne_self j)
  rw [moveAt_moveDn j u.content] at hmv
  have hMr : elim.rowsLen (monomialsAt u.content).length
      (units.matUnitAt (units.moveDn j u.content) u.content
        (j + 1) j) :=
    units.rowsLen_matUnitAt _ _ (j + 1) j
  have hTul : (T u.content).length = u.coords.length := elim.sqAt_len hTu
  have hul : u.coords.length = (monomialsAt u.content).length := hus
  have hVl : (elim.vecScale S
      (elim.matVec (T u.content) u.coords)).length
      = (monomialsAt u.content).length := by
    rw [elim.length_vecScale, elim.matVec_length, hTul, hul]
  have hUl : (elim.vecScale S' u.coords).length
      = (monomialsAt u.content).length := by
    rw [elim.length_vecScale, hul]
  rw [hw]
  show poly.oneValue
    (elim.vecScale S (elim.matVec (T (units.moveDn j u.content))
      (elim.matVec (units.matUnitAt (units.moveDn j u.content)
        u.content (j + 1) j) u.coords)))
    (elim.vecScale S' (elim.matVec
      (units.matUnitAt (units.moveDn j u.content) u.content
        (j + 1) j) u.coords))
  refine poly.oneValue_trans
    (elim.vecScale_oneValue S _ _ (poly.oneValue_symm hmv)) ?_
  refine poly.oneValue_trans
    (poly.oneValue_symm
      (elim.matVec_vecScale_free _ S (elim.matVec (T u.content) u.coords))) ?_
  refine poly.oneValue_trans
    (elim.matVec_congr _ _ _ hih) ?_
  exact elim.matVec_vecScale_free _ S' u.coords

/-- The display's walk along the pool: the head's line carried
down the provenance, one intertwining step per word. -/
private theorem endoGo (d : Nat) (v : HVec) (tail : List HVec)
    (T : List Nat → elim.Mat)
    (hsz : ∀ w ∈ v :: tail, sized w)
    (hwid : ∀ w ∈ v :: tail, w.content.length = d)
    (hprov : ∀ k, k < tail.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tail) i)
          = some (getAt (⟨[], []⟩ : HVec) tail k))
    (hTsq : ∀ w ∈ v :: tail, elim.sqAt (T w.content) w.coords.length)
    (hmv : ∀ w ∈ v :: tail, ∀ i < d, ∀ j < d, ¬ i = j →
      poly.oneValue
        (elim.matVec
          (units.matUnitAt (moveAt i j w.content) w.content i j)
          (elim.matVec (T w.content) w.coords))
        (elim.matVec (T (moveAt i j w.content))
          (elim.matVec
            (units.matUnitAt (moveAt i j w.content) w.content i j)
            w.coords)))
    (hbase : poly.oneValue
      (elim.vecScale (elim.dotP v.coords v.coords)
        (elim.matVec (T v.content) v.coords))
      (elim.vecScale
        (elim.dotP (elim.matVec (T v.content) v.coords) v.coords)
        v.coords)) :
    ∀ m p : Nat, p ≤ m → p < (v :: tail).length →
      poly.oneValue
        (elim.vecScale (elim.dotP v.coords v.coords)
          (elim.matVec
            (T (getAt (⟨[], []⟩ : HVec) (v :: tail) p).content)
            (getAt (⟨[], []⟩ : HVec) (v :: tail) p).coords))
        (elim.vecScale
          (elim.dotP (elim.matVec (T v.content) v.coords) v.coords)
          (getAt (⟨[], []⟩ : HVec) (v :: tail) p).coords)
  | 0, 0, _, _ => hbase
  | 0, _ + 1, hp, _ => absurd hp (Nat.not_succ_le_zero _)
  | _ + 1, 0, _, _ => hbase
  | m + 1, k + 1, hp, hlt => by
    have hk : k < tail.length := Nat.lt_of_succ_lt_succ hlt
    match hprov k hk with
    | ⟨i, hik, j, hjd, hlow⟩ =>
      have hip : i < (v :: tail).length :=
        Nat.lt_trans (Nat.lt_of_le_of_lt hik hk)
          (Nat.lt_succ_self tail.length)
      have hih := endoGo d v tail T hsz hwid hprov hTsq hmv hbase m i
        (Nat.le_trans hik (Nat.le_of_succ_le_succ hp)) hip
      have hum := ground.mem_getAt (⟨[], []⟩ : HVec) (v :: tail) i hip
      have hwm := ground.mem_getAt (⟨[], []⟩ : HVec) (v :: tail) (k + 1) hlt
      show poly.oneValue
        (elim.vecScale (elim.dotP v.coords v.coords)
          (elim.matVec (T (getAt (⟨[], []⟩ : HVec) tail k).content)
            (getAt (⟨[], []⟩ : HVec) tail k).coords))
        (elim.vecScale
          (elim.dotP (elim.matVec (T v.content) v.coords) v.coords)
          (getAt (⟨[], []⟩ : HVec) tail k).coords)
      exact endo_step d j T _ _ _ _ (hsz _ hum) (hTsq _ hum)
        (hmv _ hum) hjd hlow hih

/-- `lem:blockirr`(ii): a matrix family with its values settled at
the members' own contents and the moved reads acts as the cleared
scalar — every value reads the head's line
`⟨v,v⟩·(T w) = ⟨T v, v⟩·w`. -/
theorem endo_scalar (d : Nat) (v : HVec) (tail : List HVec)
    (T : List Nat → elim.Mat)
    (hsz : ∀ w ∈ v :: tail, sized w)
    (hwid : ∀ w ∈ v :: tail, w.content.length = d)
    (hprov : ∀ k, k < tail.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tail) i)
          = some (getAt (⟨[], []⟩ : HVec) tail k))
    (hTsq : ∀ w ∈ v :: tail, elim.sqAt (T w.content) w.coords.length)
    (hval : settledAt (v :: tail)
      ⟨v.content, elim.matVec (T v.content) v.coords⟩)
    (hmv : ∀ w ∈ v :: tail, ∀ i < d, ∀ j < d, ¬ i = j →
      poly.oneValue
        (elim.matVec
          (units.matUnitAt (moveAt i j w.content) w.content i j)
          (elim.matVec (T w.content) w.coords))
        (elim.matVec (T (moveAt i j w.content))
          (elim.matVec
            (units.matUnitAt (moveAt i j w.content) w.content i j)
            w.coords))) :
    ∀ w ∈ v :: tail,
      poly.oneValue
        (elim.vecScale (elim.dotP v.coords v.coords)
          (elim.matVec (T w.content) w.coords))
        (elim.vecScale
          (elim.dotP (elim.matVec (T v.content) v.coords) v.coords)
          w.coords) := by
  intro w hw
  match ground.getAt_of_mem (⟨[], []⟩ : HVec) hw with
  | ⟨p, hp, hpe⟩ =>
    rw [← hpe]
    exact endoGo d v tail T hsz hwid hprov hTsq hmv
      (endo_base d v tail T hwid hprov
        (hTsq v (List.Mem.head tail)) hval)
      p p (Nat.le_refl p) hp

/-! `lem:blockirr` clause (iii)'s kit: the value family as a list,
its content groups the source groups under the value matrix, the
values' unit walk, and the nonvacant group's own member. -/

/-- The value list's content group is the source group under the
content's own matrix, the filter passing the values' contents. -/
private theorem valList_group (T : List Nat → elim.Mat)
    (mu : List Nat) : ∀ pool : List HVec,
    groupAt (pool.map (fun w =>
        (⟨w.content, elim.matVec (T w.content) w.coords⟩ : HVec))) mu
      = (groupAt pool mu).map (elim.matVec (T mu))
  | [] => rfl
  | z :: t => by
    show groupAt ((⟨z.content,
        elim.matVec (T z.content) z.coords⟩ : HVec)
        :: t.map (fun w =>
          (⟨w.content,
            elim.matVec (T w.content) w.coords⟩ : HVec))) mu
      = (groupAt (z :: t) mu).map (elim.matVec (T mu))
    rw [groupAt_cons (⟨z.content,
        elim.matVec (T z.content) z.coords⟩ : HVec) _ mu,
      groupAt_cons z t mu]
    show (match z.content == mu with
        | true => elim.matVec (T z.content) z.coords
            :: groupAt (t.map (fun w =>
              (⟨w.content,
                elim.matVec (T w.content) w.coords⟩ : HVec))) mu
        | false => groupAt (t.map (fun w =>
            (⟨w.content,
              elim.matVec (T w.content) w.coords⟩ : HVec))) mu)
      = (match z.content == mu with
        | true => z.coords :: groupAt t mu
        | false => groupAt t mu).map (elim.matVec (T mu))
    cases hb : z.content == mu with
    | true =>
      rw [ground.listBeqEq hb, valList_group T mu t]
      rfl
    | false =>
      rw [valList_group T mu t]

/-- A nonvacant span read names a member at the content: the
vacant group would read the unit tail. -/
private theorem group_member (pool : List HVec) (mu : List Nat)
    (N : Nat) (x : List BPair) (hx : ¬ poly.unitTail x)
    (h : elim.spanRel N (groupAt pool mu) x) :
    ∃ w, w ∈ pool ∧ w.content = mu := by
  cases hnil : groupAt pool mu with
  | nil =>
    rw [hnil] at h
    exact absurd (elim.spanRel_nil_unit N x h) hx
  | cons _ t =>
    match groupAt_rows (fun w => w ∈ pool) pool (fun _ hw => hw) mu 0
        (by rw [hnil]; exact Nat.succ_pos t.length) with
    | ⟨w, hw, hwc, _⟩ => exact ⟨w, hw, hwc⟩

/-- The values' unit walk: at the head's value on the sum's unit
every value is, the intertwining read carrying the unit tail down
one lowering at a time. -/
private theorem valUnitGo (d : Nat) (v : HVec) (tail : List HVec)
    (T : List Nat → elim.Mat)
    (hprov : ∀ k, k < tail.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tail) i)
          = some (getAt (⟨[], []⟩ : HVec) tail k))
    (hmv : ∀ w ∈ v :: tail, ∀ i < d, ∀ j < d, ¬ i = j →
      poly.oneValue
        (elim.matVec
          (units.matUnitAt (moveAt i j w.content) w.content i j)
          (elim.matVec (T w.content) w.coords))
        (elim.matVec (T (moveAt i j w.content))
          (elim.matVec
            (units.matUnitAt (moveAt i j w.content) w.content i j)
            w.coords)))
    (hbase : poly.unitTail (elim.matVec (T v.content) v.coords)) :
    ∀ m p : Nat, p ≤ m → p < (v :: tail).length →
      poly.unitTail
        (elim.matVec (T (getAt (⟨[], []⟩ : HVec) (v :: tail) p).content)
          (getAt (⟨[], []⟩ : HVec) (v :: tail) p).coords)
  | 0, 0, _, _ => hbase
  | 0, _ + 1, hp, _ => absurd hp (Nat.not_succ_le_zero _)
  | _ + 1, 0, _, _ => hbase
  | m + 1, k + 1, hp, hlt => by
    have hk : k < tail.length := Nat.lt_of_succ_lt_succ hlt
    match hprov k hk with
    | ⟨i, hik, j, hjd, hlow⟩ =>
      have hip : i < (v :: tail).length :=
        Nat.lt_trans (Nat.lt_of_le_of_lt hik hk)
          (Nat.lt_succ_self tail.length)
      have hih := valUnitGo d v tail T hprov hmv hbase m i
        (Nat.le_trans hik (Nat.le_of_succ_le_succ hp)) hip
      have hum := ground.mem_getAt (⟨[], []⟩ : HVec) (v :: tail) i hip
      have hmvi := hmv _ hum (j + 1) hjd j (Nat.lt_of_succ_lt hjd)
        (Nat.succ_ne_self j)
      rw [moveAt_moveDn j (getAt (⟨[], []⟩ : HVec) (v :: tail) i).content]
        at hmvi
      show poly.unitTail
        (elim.matVec (T (getAt (⟨[], []⟩ : HVec) tail k).content)
          (getAt (⟨[], []⟩ : HVec) tail k).coords)
      rw [blockcount.lowerH_eq hlow]
      exact poly.unitTail_oneValue_right
        (elim.matVec_null _ _ hih) hmvi

/-- The value list's closure: the intertwining read turns the
value's letter-pair image into the image's own value, and the
source's settled read maps through the content's matrix. -/
private theorem val_closed (d : Nat) (pool : List HVec)
    (T : List Nat → elim.Mat)
    (hsz : ∀ w ∈ pool, sized w)
    (hTsq : ∀ w ∈ pool, elim.sqAt (T w.content) w.coords.length)
    (hcl : ∀ w ∈ pool, ∀ i < d, ∀ j < d, ¬ i = j →
      settledAt pool (act i j w))
    (hmv : ∀ w ∈ pool, ∀ i < d, ∀ j < d, ¬ i = j →
      poly.oneValue
        (elim.matVec
          (units.matUnitAt (moveAt i j w.content) w.content i j)
          (elim.matVec (T w.content) w.coords))
        (elim.matVec (T (moveAt i j w.content))
          (elim.matVec
            (units.matUnitAt (moveAt i j w.content) w.content i j)
            w.coords))) :
    ∀ x ∈ pool.map (fun w =>
        (⟨w.content, elim.matVec (T w.content) w.coords⟩ : HVec)),
      ∀ i < d, ∀ j < d, ¬ i = j →
        settledAt (pool.map (fun w =>
          (⟨w.content, elim.matVec (T w.content) w.coords⟩ : HVec)))
          (act i j x) := by
  intro x hx i hi j hj hij
  match ground.mem_map_of _ pool x hx with
  | ⟨w, hw, hwx⟩ =>
    have hmvw := hmv w hw i hi j hj hij
    have hact : (act i j x).coords
        = elim.matVec
          (units.matUnitAt (moveAt i j w.content) w.content i j)
          (elim.matVec (T w.content) w.coords) := by
      rw [← hwx]
      rfl
    have hcont : (act i j x).content = moveAt i j w.content := by
      rw [← hwx]
      rfl
    have hlen : (act i j x).coords.length
        = (monomialsAt (moveAt i j w.content)).length := by
      rw [hact, units.matVec_matUnitAt_length]
    have hval : poly.oneValue (act i j x).coords
        (elim.matVec (T (moveAt i j w.content))
          (act i j w).coords) := by
      rw [hact]
      exact hmvw
    have hunit : poly.unitTail (act i j w).coords →
        settledAt (pool.map (fun w =>
          (⟨w.content,
            elim.matVec (T w.content) w.coords⟩ : HVec)))
          (act i j x) := by
      intro hu
      refine Or.inl (allU_of_unitTail _ ?_)
      refine poly.oneValue_unitTail hval ?_
      exact elim.matVec_null _ _ hu
    cases hcl w hw i hi j hj hij with
    | inl hu => exact hunit (unitTail_of_allU _ hu)
    | inr hs =>
      have hs2 : elim.spanRel (monomialsAt (moveAt i j w.content)).length
          (groupAt pool (moveAt i j w.content)) (act i j w).coords := by
        have hsz2 : (act i j w).coords.length
            = (monomialsAt (moveAt i j w.content)).length :=
          act_sized i j w
        rw [hsz2] at hs
        exact hs
      cases hnil : groupAt pool (moveAt i j w.content) with
      | nil =>
        rw [hnil] at hs2
        exact hunit (elim.spanRel_nil_unit _ _ hs2)
      | cons r t =>
        match groupAt_rows (fun z => sized z
            ∧ elim.sqAt (T z.content) z.coords.length) pool
            (fun z hz => ⟨hsz z hz, hTsq z hz⟩)
            (moveAt i j w.content) 0
            (by rw [hnil]; exact Nat.succ_pos t.length) with
        | ⟨z, ⟨hzs, hzq⟩, hzc, _⟩ =>
          have hTl : (T (moveAt i j w.content)).length
              = (monomialsAt (moveAt i j w.content)).length := by
            rw [← hzc, elim.sqAt_len hzq]
            exact hzs
          have hTr : elim.rowsLen
              (monomialsAt (moveAt i j w.content)).length
              (T (moveAt i j w.content)) := by
            have h := elim.rowsLen_of_sqAt hzq
            rw [hzs, hzc] at h
            exact h
          have hmap := elim.spanRel_matVec
            (monomialsAt (moveAt i j w.content)).length
            (groupAt pool (moveAt i j w.content))
            (act i j w).coords (T (moveAt i j w.content))
            (monomialsAt (moveAt i j w.content)).length hTl
            (rowsLen_groupAt _ pool hsz) (act_sized i j w) hs2
          rw [← valList_group T (moveAt i j w.content) pool] at hmap
          refine Or.inr ?_
          rw [hlen, hcont]
          exact elim.spanRel_congr _ _ _ _
            (poly.oneValue_symm hval) hmap hlen

/-- At a pool of unit tails a settled vector reads one: the
group's rows are null, so the cleared combination is. -/
private theorem settled_unit (pool : List HVec) (x : HVec)
    (hall : ∀ w ∈ pool, poly.unitTail w.coords)
    (h : settledAt pool x) : poly.unitTail x.coords := by
  cases h with
  | inl hu => exact unitTail_of_allU _ hu
  | inr hs =>
    obtain ⟨c₀, cs, hc₀, _, hone⟩ := elim.span_elim hs
    refine elim.unitTail_unscale c₀ hc₀ x.coords ?_
    refine poly.oneValue_unitTail hone ?_
    refine elim.unitTail_combo_rows _ cs (groupAt pool x.content) ?_
    intro k hk
    match groupAt_rows (fun w => poly.unitTail w.coords) pool hall
        x.content k hk with
    | ⟨w, hw, _, hrow⟩ =>
      rw [hrow]
      exact hw

/-- The unit head's pool: every word reads the unit tail, a null
vector's lowering images null. -/
private theorem poolUnitGo (d : Nat) (u : HVec) (tailu : List HVec)
    (hprov : ∀ k, k < tailu.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (u :: tailu) i)
          = some (getAt (⟨[], []⟩ : HVec) tailu k))
    (hbase : poly.unitTail u.coords) :
    ∀ m p : Nat, p ≤ m → p < (u :: tailu).length →
      poly.unitTail
        (getAt (⟨[], []⟩ : HVec) (u :: tailu) p).coords
  | 0, 0, _, _ => hbase
  | 0, _ + 1, hp, _ => absurd hp (Nat.not_succ_le_zero _)
  | _ + 1, 0, _, _ => hbase
  | m + 1, k + 1, hp, hlt => by
    have hk : k < tailu.length := Nat.lt_of_succ_lt_succ hlt
    match hprov k hk with
    | ⟨i, hik, _, _, hlow⟩ =>
      have hip : i < (u :: tailu).length :=
        Nat.lt_trans (Nat.lt_of_le_of_lt hik hk)
          (Nat.lt_succ_self tailu.length)
      have hih := poolUnitGo d u tailu hprov hbase m i
        (Nat.le_trans hik (Nat.le_of_succ_le_succ hp)) hip
      show poly.unitTail
        (getAt (⟨[], []⟩ : HVec) tailu k).coords
      rw [blockcount.lowerH_eq hlow]
      exact elim.matVec_null _ _ hih

/-- The target head reads off the sum's unit, derived at the
clause's own data: a unit head makes every word of the target pool
a unit tail, so every value settled there is one — against the
value off it. -/
private theorem head_off (d : Nat) (v : HVec) (tailv : List HVec)
    (u : HVec) (tailu : List HVec) (T : List Nat → elim.Mat)
    (hprovu : ∀ k, k < tailu.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (u :: tailu) i)
          = some (getAt (⟨[], []⟩ : HVec) tailu k))
    (hval : ∀ w ∈ v :: tailv,
      settledAt (u :: tailu)
        ⟨w.content, elim.matVec (T w.content) w.coords⟩)
    (hoff : ∃ w ∈ v :: tailv,
      ¬ poly.unitTail (elim.matVec (T w.content) w.coords)) :
    ¬ poly.unitTail u.coords := by
  intro hu
  match hoff with
  | ⟨w, hw, hwoff⟩ =>
    refine hwoff (settled_unit (u :: tailu) _ ?_ (hval w hw))
    intro z hz
    match ground.getAt_of_mem (⟨[], []⟩ : HVec) hz with
    | ⟨p, hp, hpe⟩ =>
      rw [← hpe]
      exact poolUnitGo d u tailu hprovu hu p p (Nat.le_refl p) hp

/-- `lem:blockirr`(iii): a matrix family from one span into
another, its values settled at the members' own contents with the
moved reads and one value off the sum's unit, forces the top
contents to agree. -/
theorem hom_content (d : Nat) (v : HVec) (tailv : List HVec)
    (u : HVec) (tailu : List HVec) (T : List Nat → elim.Mat)
    (hszv : ∀ w ∈ v :: tailv, sized w)
    (hwidv : ∀ w ∈ v :: tailv, w.content.length = d)
    (hprovv : ∀ k, k < tailv.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tailv) i)
          = some (getAt (⟨[], []⟩ : HVec) tailv k))
    (hclv : ∀ w ∈ v :: tailv, ∀ i < d, ∀ j < d, ¬ i = j →
      settledAt (v :: tailv) (act i j w))
    (hszu : ∀ w ∈ u :: tailu, sized w)
    (hwidu : ∀ w ∈ u :: tailu, w.content.length = d)
    (hprovu : ∀ k, k < tailu.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (u :: tailu) i)
          = some (getAt (⟨[], []⟩ : HVec) tailu k))
    (hTsq : ∀ w ∈ v :: tailv, elim.sqAt (T w.content) w.coords.length)
    (hval : ∀ w ∈ v :: tailv,
      settledAt (u :: tailu)
        ⟨w.content, elim.matVec (T w.content) w.coords⟩)
    (hmv : ∀ w ∈ v :: tailv, ∀ i < d, ∀ j < d, ¬ i = j →
      poly.oneValue
        (elim.matVec
          (units.matUnitAt (moveAt i j w.content) w.content i j)
          (elim.matVec (T w.content) w.coords))
        (elim.matVec (T (moveAt i j w.content))
          (elim.matVec
            (units.matUnitAt (moveAt i j w.content) w.content i j)
            w.coords)))
    (hoff : ∃ w ∈ v :: tailv,
      ¬ poly.unitTail (elim.matVec (T w.content) w.coords)) :
    v.content = u.content := by
  have huoff : ¬ poly.unitTail u.coords :=
    head_off d v tailv u tailu T hprovu hval hoff
  have htop : ¬ poly.unitTail
      (elim.matVec (T v.content) v.coords) := by
    intro hb
    match hoff with
    | ⟨w, hw, hwoff⟩ =>
      match ground.getAt_of_mem (⟨[], []⟩ : HVec) hw with
      | ⟨p, hp, hpe⟩ =>
        refine hwoff ?_
        rw [← hpe]
        exact valUnitGo d v tailv T hprovv hmv hb p p
          (Nat.le_refl p) hp
  have hLsz : ∀ x ∈ (v :: tailv).map (fun w =>
      (⟨w.content, elim.matVec (T w.content) w.coords⟩ : HVec)),
      sized x := by
    intro x hx
    match ground.mem_map_of _ (v :: tailv) x hx with
    | ⟨w, hw, hwx⟩ =>
      rw [← hwx]
      show (elim.matVec (T w.content) w.coords).length
        = (monomialsAt w.content).length
      rw [elim.matVec_length, elim.sqAt_len (hTsq w hw)]
      exact hszv w hw
  have hLmem : ∀ x ∈ (v :: tailv).map (fun w =>
      (⟨w.content, elim.matVec (T w.content) w.coords⟩ : HVec)),
      settledAt (u :: tailu) x := by
    intro x hx
    match ground.mem_map_of _ (v :: tailv) x hx with
    | ⟨w, hw, hwx⟩ =>
      rw [← hwx]
      exact hval w hw
  have hmain := irred d u tailu ((v :: tailv).map (fun w =>
      (⟨w.content, elim.matVec (T w.content) w.coords⟩ : HVec)))
    hszu hwidu hprovu hLsz hLmem
    (val_closed d (v :: tailv) T hszv hTsq hclv hmv)
  have hleft : ∀ w ∈ u :: tailu, settledAt ((v :: tailv).map
      (fun w => (⟨w.content,
        elim.matVec (T w.content) w.coords⟩ : HVec))) w := by
    cases hmain with
    | inl h => exact h
    | inr h =>
      exact absurd (h _ (ground.mem_map_to _ (List.Mem.head tailv))) htop
  have hwu : ∃ w, w ∈ v :: tailv ∧ w.content = u.content := by
    have hus := hleft u (List.Mem.head tailu)
    have hspan : elim.spanRel u.coords.length
        (groupAt ((v :: tailv).map (fun w =>
          (⟨w.content,
            elim.matVec (T w.content) w.coords⟩ : HVec)))
          u.content) u.coords := by
      cases hus with
      | inl hu0 => exact absurd (unitTail_of_allU _ hu0) huoff
      | inr hs => exact hs
    match group_member ((v :: tailv).map (fun w =>
        (⟨w.content, elim.matVec (T w.content) w.coords⟩ : HVec)))
        u.content u.coords.length u.coords huoff hspan with
    | ⟨x, hx, hxc⟩ =>
      match ground.mem_map_of _ (v :: tailv) x hx with
      | ⟨w, hw, hwx⟩ =>
        refine ⟨w, hw, ?_⟩
        rw [← hwx] at hxc
        exact hxc
  have hzv : ∃ z, z ∈ u :: tailu ∧ z.content = v.content := by
    have hvs := hval v (List.Mem.head tailv)
    have hspan : elim.spanRel
        (elim.matVec (T v.content) v.coords).length
        (groupAt (u :: tailu) v.content)
        (elim.matVec (T v.content) v.coords) := by
      cases hvs with
      | inl hu0 => exact absurd (unitTail_of_allU _ hu0) htop
      | inr hs => exact hs
    exact group_member (u :: tailu) v.content _ _ htop hspan
  match hwu, hzv with
  | ⟨w, hw, hwc⟩, ⟨z, hz, hzc⟩ =>
    cases hw with
    | head => exact hwc
    | tail _ hwt =>
      cases hz with
      | head => exact hzc.symm
      | tail _ hzt =>
        have h1 := ht_strict d v tailv hwidv hprovv w hwt
        have h2 := ht_strict d u tailu hwidu hprovu z hzt
        rw [hwc] at h1
        rw [hzc] at h2
        exact absurd (Nat.lt_trans h1 h2) (Nat.lt_irrefl _)

/-! `lem:blockirr`(iv)'s assembly tier: the pool as its head's word
images, the per-group word lists, the images' group memberships and
independence transported at the words' pairings
(`blockcount.wordGram`), and the count at the partition over the
occupied contents. -/

/-- The lowering image is the adjacent letter-pair action, the
positional bridge at the moved content. -/
private theorem lowerH_act {j : Nat} {x w : HVec}
    (h : lowerH j x = some w) : w = act (j + 1) j x := by
  rw [lowerH_eq h]
  show (⟨units.moveDn j x.content, _⟩ : HVec)
    = (⟨moveAt (j + 1) j x.content,
        elim.matVec (units.matUnitAt (moveAt (j + 1) j x.content)
          x.content (j + 1) j) x.coords⟩ : HVec)
  rw [moveAt_moveDn j x.content]

/-- A pool member at the provenance is its head's word image, the
letters at the adjacent bounds, the walk's own strong descent. -/
private theorem wordGo (d : Nat) (v : HVec) (tailv : List HVec)
    (hprov : ∀ k, k < tailv.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tailv) i)
          = some (getAt (⟨[], []⟩ : HVec) tailv k)) :
    ∀ (b k : Nat), k ≤ b → k < (v :: tailv).length →
      ∃ ws : List Nat, (∀ l ∈ ws, l + 1 < d)
        ∧ getAt (⟨[], []⟩ : HVec) (v :: tailv) k = wact ws v
  | _, 0, _, _ =>
    ⟨[], And.intro (fun _ hl => nomatch hl) rfl⟩
  | 0, k + 1, hkb, _ => absurd hkb (Nat.not_succ_le_zero k)
  | b + 1, k + 1, hkb, hk =>
    match hprov k (Nat.lt_of_succ_lt_succ hk) with
    | ⟨i, hik, j, hjd, hlow⟩ =>
      match wordGo d v tailv hprov b i
          (Nat.le_trans hik (Nat.le_of_succ_le_succ hkb))
          (Nat.lt_of_lt_of_le
            (Nat.lt_succ_of_le hik)
            (Nat.le_of_lt hk)) with
      | ⟨ws, hwsb, hwse⟩ =>
        ⟨j :: ws,
         fun l hl => match hl with
           | .head _ => hjd
           | .tail _ hlt => hwsb l hlt,
         by
           show getAt (⟨[], []⟩ : HVec) tailv k = wact (j :: ws) v
           rw [hwse] at hlow
           exact lowerH_act hlow⟩

/-- The pool's word list at a prefix, one word per member. -/
private theorem wordsUpTo (d : Nat) (v : HVec) (tailv : List HVec)
    (hprov : ∀ k, k < tailv.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tailv) i)
          = some (getAt (⟨[], []⟩ : HVec) tailv k)) :
    ∀ m, m ≤ (v :: tailv).length →
      ∃ wl : List (List Nat), wl.length = m
        ∧ ∀ k, k < m →
          (∀ l ∈ ground.getAt ([] : List Nat) wl k, l + 1 < d)
          ∧ getAt (⟨[], []⟩ : HVec) (v :: tailv) k
              = wact (ground.getAt ([] : List Nat) wl k) v
  | 0, _ => ⟨[], rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | m + 1, hm =>
    match wordsUpTo d v tailv hprov m (Nat.le_of_succ_le hm) with
    | ⟨wl, hwl, hprop⟩ =>
      match wordGo d v tailv hprov m m (Nat.le_refl m) hm with
      | ⟨ws, hwsb, hwse⟩ =>
        ⟨wl ++ [ws],
         by rw [ground.length_append, hwl]; rfl,
         fun k hk => by
           by_cases hkm : k < m
           · have hg : ground.getAt ([] : List Nat) (wl ++ [ws]) k
                 = ground.getAt ([] : List Nat) wl k := by
               rw [ground.getAt_append,
                 if_pos (show k < wl.length by rw [hwl]; exact hkm)]
             rw [hg]
             exact hprop k hkm
           · have hkm' : k = m :=
               Nat.le_antisymm (Nat.le_of_lt_succ hk)
                 (Nat.le_of_not_lt hkm)
             have hg : ground.getAt ([] : List Nat) (wl ++ [ws]) k
                 = ws := by
               rw [ground.getAt_append,
                 if_neg (show ¬ k < wl.length by
                   rw [hwl, hkm']; exact Nat.lt_irrefl m),
                 show k - wl.length = 0 by
                   rw [hwl, hkm']; exact Nat.sub_self m]
               rfl
             rw [hg, hkm']
             exact ⟨hwsb, hwse⟩⟩

/-- The pool is its head's word images, the map at the extracted
list with the letters at the adjacent bounds (`lem:blockirr`(iv)'s
word clause: the block's members are its words' images at its
top). -/
theorem pool_words (d : Nat) (v : HVec) (tailv : List HVec)
    (hprov : ∀ k, k < tailv.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tailv) i)
          = some (getAt (⟨[], []⟩ : HVec) tailv k)) :
    ∃ wl : List (List Nat),
      (v :: tailv) = wl.map (fun ws => wact ws v)
        ∧ ∀ ws ∈ wl, ∀ l ∈ ws, l + 1 < d :=
  match wordsUpTo d v tailv hprov (v :: tailv).length
      (Nat.le_refl _) with
  | ⟨wl, hwl, hprop⟩ =>
    ⟨wl,
     ground.getAt_ext (⟨[], []⟩ : HVec) (v :: tailv)
       (wl.map (fun ws => wact ws v))
       (by rw [ground.length_map, hwl])
       (fun k hk => by
         rw [ground.getAt_map ([] : List Nat) (⟨[], []⟩ : HVec)
           (fun ws => wact ws v) wl k
           (by rw [hwl]; exact hk)]
         exact (hprop k hk).2),
     fun ws hws =>
       match ground.getAt_of_mem ([] : List Nat) hws with
       | ⟨p, hp, hpe⟩ => by
         rw [← hpe]
         exact (hprop p (by rw [← hwl]; exact hp)).1⟩

/-- A word image's content moves with the head's, the chain's
congruence. -/
private theorem wact_content_congr (v u : HVec)
    (hc : v.content = u.content) :
    ∀ ws : List Nat, (wact ws v).content = (wact ws u).content :=
  fun ws => by rw [wact_content ws v, wact_content ws u, hc]

/-- A word image sits in its own content group's span, the head at
its listed row and the letters at the settled transport
(`lem:blockirr`(iv): the one word family at the top spans the
block's group group by group). -/
theorem word_span (d : Nat) (u : HVec) (tailu : List HVec)
    (hall : ∀ w ∈ u :: tailu, sized w)
    (hset : ∀ w ∈ u :: tailu, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt (u :: tailu) (act i j w)) :
    ∀ ws : List Nat, (∀ l ∈ ws, l + 1 < d) →
      elim.spanRel
        (monomialsAt (wact ws u).content).length
        (groupAt (u :: tailu) (wact ws u).content)
        (wact ws u).coords
  | [], _ => by
    have hg : groupAt (u :: tailu) u.content
        = u.coords :: groupAt tailu u.content := by
      rw [groupAt_cons, ground.listEqBeq u.content]
    have hrows : elim.rowsLen (monomialsAt u.content).length
        (groupAt (u :: tailu) u.content) :=
      rowsLen_groupAt u.content (u :: tailu) hall
    have hlt : 0 < (groupAt (u :: tailu) u.content).length := by
      rw [hg]
      exact Nat.succ_pos _
    have hgot := elim.spanRel_getAt
      (monomialsAt u.content).length
      (groupAt (u :: tailu) u.content) 0 hlt hrows
    rw [show ground.getAt ([] : List BPair)
        (groupAt (u :: tailu) u.content) 0 = u.coords by
      rw [hg]; rfl] at hgot
    exact hgot
  | j :: t, hb => by
    have hjd : j + 1 < d := hb j (List.Mem.head t)
    have hsp := word_span d u tailu hall hset t
      (fun l hl => hb l (List.Mem.tail j hl))
    have hx : (wact t u).coords.length
        = (monomialsAt (wact t u).content).length :=
      wact_sized t u (hall u (List.Mem.head tailu))
    have hres := act_transport (u :: tailu) (j + 1) j hall
      (fun w hw => hset w hw (j + 1) hjd j
        (Nat.lt_of_succ_lt hjd) (Nat.succ_ne_self j))
      (wact t u).content (wact t u).coords hx hsp
    exact hres

/-- The word rows at one content read the stated width. -/
private theorem rows_len_words (x : HVec) (mu : List Nat)
    (hsx : sized x) :
    ∀ bs : List (List Nat),
      (∀ ws ∈ bs, (wact ws x).content = mu) →
      elim.rowsLen (monomialsAt mu).length
        (bs.map (fun ws => (wact ws x).coords))
  | [], _ => trivial
  | b :: bs', h =>
    ⟨by
      have hs : (wact b x).coords.length
          = (monomialsAt (wact b x).content).length :=
        wact_sized b x hsx
      rw [hs, h b (List.Mem.head bs')],
     rows_len_words x mu hsx bs'
       (fun ws hw => h ws (List.Mem.tail b hw))⟩

/-- One row's pairing against a word combination transports across
the two tops at the cross-multiplied scale, `wordGram` termwise
with the pairing's bilinearity. -/
private theorem rowGram (d : Nat) (v u : HVec) (mu : List Nat)
    (hsv : sized v) (hsu : sized u)
    (hdv : v.content.length = d) (hvu : v.content = u.content)
    (htv : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j v).coords)
    (htu : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j u).coords)
    (a : List Nat) (hab : ∀ l ∈ a, l + 1 < d)
    (hac : (wact a v).content = mu) :
    ∀ (ds : List BPair) (bs : List (List Nat)),
      (∀ ws ∈ bs, (∀ l ∈ ws, l + 1 < d)
        ∧ (wact ws v).content = mu) →
      ((elim.dotP (wact a v).coords
          (elim.combo (monomialsAt mu).length ds
            (bs.map (fun ws => (wact ws v).coords))))
        * elim.dotP u.coords u.coords).oneValue
      ((elim.dotP (wact a u).coords
          (elim.combo (monomialsAt mu).length ds
            (bs.map (fun ws => (wact ws u).coords))))
        * elim.dotP v.coords v.coords)
  | [], bs, _ => by
    have h1 : (elim.dotP (wact a v).coords
        (List.replicate (monomialsAt mu).length
          BPair.unit)).oneValue BPair.unit :=
      elim.dotP_null_tail_right _ _
        (poly.unitTail_replicate (monomialsAt mu).length)
    have h2 : (elim.dotP (wact a u).coords
        (List.replicate (monomialsAt mu).length
          BPair.unit)).oneValue BPair.unit :=
      elim.dotP_null_tail_right _ _
        (poly.unitTail_replicate (monomialsAt mu).length)
    exact BPair.oneValue_trans
      (BPair.oneValue_trans (BPair.mul_congr_left h1)
        (BPair.unit_mul _))
      (BPair.oneValue_symm
        (BPair.oneValue_trans (BPair.mul_congr_left h2)
          (BPair.unit_mul _)))
  | _ :: _, [], _ => by
    have h1 : (elim.dotP (wact a v).coords
        (List.replicate (monomialsAt mu).length
          BPair.unit)).oneValue BPair.unit :=
      elim.dotP_null_tail_right _ _
        (poly.unitTail_replicate (monomialsAt mu).length)
    have h2 : (elim.dotP (wact a u).coords
        (List.replicate (monomialsAt mu).length
          BPair.unit)).oneValue BPair.unit :=
      elim.dotP_null_tail_right _ _
        (poly.unitTail_replicate (monomialsAt mu).length)
    exact BPair.oneValue_trans
      (BPair.oneValue_trans (BPair.mul_congr_left h1)
        (BPair.unit_mul _))
      (BPair.oneValue_symm
        (BPair.oneValue_trans (BPair.mul_congr_left h2)
          (BPair.unit_mul _)))
  | e :: ds', b :: bs', hbs => by
    have hbb : ∀ l ∈ b, l + 1 < d := (hbs b (List.Mem.head bs')).1
    have hbc : (wact b v).content = mu :=
      (hbs b (List.Mem.head bs')).2
    have hbs' : ∀ ws ∈ bs', (∀ l ∈ ws, l + 1 < d)
        ∧ (wact ws v).content = mu :=
      fun ws hw => hbs ws (List.Mem.tail b hw)
    have hacu : (wact a u).content = mu :=
      (wact_content_congr v u hvu a).symm.trans hac
    have hbcu : (wact b u).content = mu :=
      (wact_content_congr v u hvu b).symm.trans hbc
    have hrv : (wact a v).coords.length = (monomialsAt mu).length := by
      have hs : (wact a v).coords.length
          = (monomialsAt (wact a v).content).length :=
        wact_sized a v hsv
      rw [hs, hac]
    have hru : (wact a u).coords.length = (monomialsAt mu).length := by
      have hs : (wact a u).coords.length
          = (monomialsAt (wact a u).content).length :=
        wact_sized a u hsu
      rw [hs, hacu]
    have hbv : (wact b v).coords.length = (monomialsAt mu).length := by
      have hs : (wact b v).coords.length
          = (monomialsAt (wact b v).content).length :=
        wact_sized b v hsv
      rw [hs, hbc]
    have hbu : (wact b u).coords.length = (monomialsAt mu).length := by
      have hs : (wact b u).coords.length
          = (monomialsAt (wact b u).content).length :=
        wact_sized b u hsu
      rw [hs, hbcu]
    have hCv : (elim.combo (monomialsAt mu).length ds'
        (bs'.map (fun ws => (wact ws v).coords))).length
        = (monomialsAt mu).length :=
      elim.length_combo (monomialsAt mu).length ds' _
        (rows_len_words v mu hsv bs' (fun ws hw => (hbs' ws hw).2))
    have hCu : (elim.combo (monomialsAt mu).length ds'
        (bs'.map (fun ws => (wact ws u).coords))).length
        = (monomialsAt mu).length :=
      elim.length_combo (monomialsAt mu).length ds' _
        (rows_len_words u mu hsu bs' (fun ws hw =>
          (wact_content_congr v u hvu ws).symm.trans (hbs' ws hw).2))
    have hGv := blockcount.wordGram d v u hsv hsu hdv hvu htv htu
      a b hab hbb (hac.trans hbc.symm)
    have hIH := rowGram d v u mu hsv hsu hdv hvu htv htu a hab hac
      ds' bs' hbs'
    show ((elim.dotP (wact a v).coords
        (elim.vecAdd (elim.vecScale e (wact b v).coords)
          (elim.combo (monomialsAt mu).length ds'
            (bs'.map (fun ws => (wact ws v).coords)))))
      * elim.dotP u.coords u.coords).oneValue
      ((elim.dotP (wact a u).coords
        (elim.vecAdd (elim.vecScale e (wact b u).coords)
          (elim.combo (monomialsAt mu).length ds'
            (bs'.map (fun ws => (wact ws u).coords)))))
      * elim.dotP v.coords v.coords)
    have h1v := elim.dotP_vecAdd (wact a v).coords
      (elim.vecScale e (wact b v).coords)
      (elim.combo (monomialsAt mu).length ds'
        (bs'.map (fun ws => (wact ws v).coords)))
      (((elim.length_vecScale e _).trans hbv).trans hrv.symm)
      (hCv.trans hrv.symm)
    have h1u := elim.dotP_vecAdd (wact a u).coords
      (elim.vecScale e (wact b u).coords)
      (elim.combo (monomialsAt mu).length ds'
        (bs'.map (fun ws => (wact ws u).coords)))
      (((elim.length_vecScale e _).trans hbu).trans hru.symm)
      (hCu.trans hru.symm)
    have h2v := elim.dotP_vecScale_right (wact a v).coords
      (wact b v).coords e
    have h2u := elim.dotP_vecScale_right (wact a u).coords
      (wact b u).coords e
    refine BPair.oneValue_trans (BPair.mul_congr_left h1v) ?_
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans (BPair.mul_congr_left h1u) ?_
    rw [BPair.right_distrib, BPair.right_distrib]
    refine BPair.oneValue_symm ?_
    refine BPair.add_congr ?_ hIH
    refine BPair.oneValue_trans (BPair.mul_congr_left h2v) ?_
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans (BPair.mul_congr_left h2u) ?_
    rw [BPair.mul_assoc, BPair.mul_assoc]
    exact BPair.oneValue_symm
      (BPair.mul_congr (BPair.oneValue_refl e) hGv)

/-- Two word combinations' pairing transports across the two tops
at the cross-multiplied scale, `rowGram` row by row. -/
private theorem comboGram (d : Nat) (v u : HVec) (mu : List Nat)
    (hsv : sized v) (hsu : sized u)
    (hdv : v.content.length = d) (hvu : v.content = u.content)
    (htv : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j v).coords)
    (htu : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j u).coords)
    (bs : List (List Nat)) (ds : List BPair)
    (hbs : ∀ ws ∈ bs, (∀ l ∈ ws, l + 1 < d)
      ∧ (wact ws v).content = mu) :
    ∀ (cs : List BPair) (as : List (List Nat)),
      (∀ ws ∈ as, (∀ l ∈ ws, l + 1 < d)
        ∧ (wact ws v).content = mu) →
      ((elim.dotP
          (elim.combo (monomialsAt mu).length cs
            (as.map (fun ws => (wact ws v).coords)))
          (elim.combo (monomialsAt mu).length ds
            (bs.map (fun ws => (wact ws v).coords))))
        * elim.dotP u.coords u.coords).oneValue
      ((elim.dotP
          (elim.combo (monomialsAt mu).length cs
            (as.map (fun ws => (wact ws u).coords)))
          (elim.combo (monomialsAt mu).length ds
            (bs.map (fun ws => (wact ws u).coords))))
        * elim.dotP v.coords v.coords)
  | [], as, _ => by
    have h1 : (elim.dotP
        (List.replicate (monomialsAt mu).length BPair.unit)
        (elim.combo (monomialsAt mu).length ds
          (bs.map (fun ws => (wact ws v).coords)))).oneValue
        BPair.unit :=
      elim.dotP_null_tail_left _ _
        (poly.unitTail_replicate (monomialsAt mu).length)
    have h2 : (elim.dotP
        (List.replicate (monomialsAt mu).length BPair.unit)
        (elim.combo (monomialsAt mu).length ds
          (bs.map (fun ws => (wact ws u).coords)))).oneValue
        BPair.unit :=
      elim.dotP_null_tail_left _ _
        (poly.unitTail_replicate (monomialsAt mu).length)
    exact BPair.oneValue_trans
      (BPair.oneValue_trans (BPair.mul_congr_left h1)
        (BPair.unit_mul _))
      (BPair.oneValue_symm
        (BPair.oneValue_trans (BPair.mul_congr_left h2)
          (BPair.unit_mul _)))
  | _ :: _, [], _ => by
    have h1 : (elim.dotP
        (List.replicate (monomialsAt mu).length BPair.unit)
        (elim.combo (monomialsAt mu).length ds
          (bs.map (fun ws => (wact ws v).coords)))).oneValue
        BPair.unit :=
      elim.dotP_null_tail_left _ _
        (poly.unitTail_replicate (monomialsAt mu).length)
    have h2 : (elim.dotP
        (List.replicate (monomialsAt mu).length BPair.unit)
        (elim.combo (monomialsAt mu).length ds
          (bs.map (fun ws => (wact ws u).coords)))).oneValue
        BPair.unit :=
      elim.dotP_null_tail_left _ _
        (poly.unitTail_replicate (monomialsAt mu).length)
    exact BPair.oneValue_trans
      (BPair.oneValue_trans (BPair.mul_congr_left h1)
        (BPair.unit_mul _))
      (BPair.oneValue_symm
        (BPair.oneValue_trans (BPair.mul_congr_left h2)
          (BPair.unit_mul _)))
  | c :: cs', a :: as', has => by
    have haa : ∀ l ∈ a, l + 1 < d := (has a (List.Mem.head as')).1
    have hacv : (wact a v).content = mu :=
      (has a (List.Mem.head as')).2
    have has' : ∀ ws ∈ as', (∀ l ∈ ws, l + 1 < d)
        ∧ (wact ws v).content = mu :=
      fun ws hw => has ws (List.Mem.tail a hw)
    have hacu : (wact a u).content = mu :=
      (wact_content_congr v u hvu a).symm.trans hacv
    have hav : (wact a v).coords.length = (monomialsAt mu).length := by
      have hs : (wact a v).coords.length
          = (monomialsAt (wact a v).content).length :=
        wact_sized a v hsv
      rw [hs, hacv]
    have hau : (wact a u).coords.length = (monomialsAt mu).length := by
      have hs : (wact a u).coords.length
          = (monomialsAt (wact a u).content).length :=
        wact_sized a u hsu
      rw [hs, hacu]
    have hWv : (elim.combo (monomialsAt mu).length ds
        (bs.map (fun ws => (wact ws v).coords))).length
        = (monomialsAt mu).length :=
      elim.length_combo (monomialsAt mu).length ds _
        (rows_len_words v mu hsv bs (fun ws hw => (hbs ws hw).2))
    have hWu : (elim.combo (monomialsAt mu).length ds
        (bs.map (fun ws => (wact ws u).coords))).length
        = (monomialsAt mu).length :=
      elim.length_combo (monomialsAt mu).length ds _
        (rows_len_words u mu hsu bs (fun ws hw =>
          (wact_content_congr v u hvu ws).symm.trans (hbs ws hw).2))
    have hCv : (elim.combo (monomialsAt mu).length cs'
        (as'.map (fun ws => (wact ws v).coords))).length
        = (monomialsAt mu).length :=
      elim.length_combo (monomialsAt mu).length cs' _
        (rows_len_words v mu hsv as' (fun ws hw => (has' ws hw).2))
    have hCu : (elim.combo (monomialsAt mu).length cs'
        (as'.map (fun ws => (wact ws u).coords))).length
        = (monomialsAt mu).length :=
      elim.length_combo (monomialsAt mu).length cs' _
        (rows_len_words u mu hsu as' (fun ws hw =>
          (wact_content_congr v u hvu ws).symm.trans (has' ws hw).2))
    have hrow := rowGram d v u mu hsv hsu hdv hvu htv htu
      a haa hacv ds bs hbs
    have hIH := comboGram d v u mu hsv hsu hdv hvu htv htu
      bs ds hbs cs' as' has'
    show ((elim.dotP
        (elim.vecAdd (elim.vecScale c (wact a v).coords)
          (elim.combo (monomialsAt mu).length cs'
            (as'.map (fun ws => (wact ws v).coords))))
        (elim.combo (monomialsAt mu).length ds
          (bs.map (fun ws => (wact ws v).coords))))
      * elim.dotP u.coords u.coords).oneValue
      ((elim.dotP
        (elim.vecAdd (elim.vecScale c (wact a u).coords)
          (elim.combo (monomialsAt mu).length cs'
            (as'.map (fun ws => (wact ws u).coords))))
        (elim.combo (monomialsAt mu).length ds
          (bs.map (fun ws => (wact ws u).coords))))
      * elim.dotP v.coords v.coords)
    have h1v := elim.dotP_vecAdd_left
      (elim.vecScale c (wact a v).coords)
      (elim.combo (monomialsAt mu).length cs'
        (as'.map (fun ws => (wact ws v).coords)))
      (elim.combo (monomialsAt mu).length ds
        (bs.map (fun ws => (wact ws v).coords)))
      (Nat.le_of_eq (Eq.symm
        (((elim.length_vecScale c _).trans hav).trans hWv.symm)))
      (Nat.le_of_eq (Eq.symm (hCv.trans hWv.symm)))
    have h1u := elim.dotP_vecAdd_left
      (elim.vecScale c (wact a u).coords)
      (elim.combo (monomialsAt mu).length cs'
        (as'.map (fun ws => (wact ws u).coords)))
      (elim.combo (monomialsAt mu).length ds
        (bs.map (fun ws => (wact ws u).coords)))
      (Nat.le_of_eq (Eq.symm
        (((elim.length_vecScale c _).trans hau).trans hWu.symm)))
      (Nat.le_of_eq (Eq.symm (hCu.trans hWu.symm)))
    have h2v : (elim.dotP (elim.vecScale c (wact a v).coords)
        (elim.combo (monomialsAt mu).length ds
          (bs.map (fun ws => (wact ws v).coords)))).oneValue
        (c * elim.dotP (wact a v).coords
          (elim.combo (monomialsAt mu).length ds
            (bs.map (fun ws => (wact ws v).coords)))) := by
      rw [elim.dotP_comm]
      refine BPair.oneValue_trans
        (elim.dotP_vecScale_right _ _ c) ?_
      rw [elim.dotP_comm]
      exact BPair.oneValue_refl _
    have h2u : (elim.dotP (elim.vecScale c (wact a u).coords)
        (elim.combo (monomialsAt mu).length ds
          (bs.map (fun ws => (wact ws u).coords)))).oneValue
        (c * elim.dotP (wact a u).coords
          (elim.combo (monomialsAt mu).length ds
            (bs.map (fun ws => (wact ws u).coords)))) := by
      rw [elim.dotP_comm]
      refine BPair.oneValue_trans
        (elim.dotP_vecScale_right _ _ c) ?_
      rw [elim.dotP_comm]
      exact BPair.oneValue_refl _
    refine BPair.oneValue_trans (BPair.mul_congr_left h1v) ?_
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans (BPair.mul_congr_left h1u) ?_
    rw [BPair.right_distrib, BPair.right_distrib]
    refine BPair.oneValue_symm ?_
    refine BPair.add_congr ?_ hIH
    refine BPair.oneValue_trans (BPair.mul_congr_left h2v) ?_
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans (BPair.mul_congr_left h2u) ?_
    rw [BPair.mul_assoc, BPair.mul_assoc]
    exact BPair.oneValue_symm
      (BPair.mul_congr (BPair.oneValue_refl c) hrow)

/-- The group's images at the second top are independent: a null
combination transports across the Gram scale to the first group,
whose independence reads the coefficients back (`lem:blockirr`(iv):
the images independent at the one-value word pairings). -/
theorem image_indep (d : Nat) (v u : HVec) (mu : List Nat)
    (hsv : sized v) (hsu : sized u)
    (hdv : v.content.length = d) (hvu : v.content = u.content)
    (htv : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j v).coords)
    (htu : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j u).coords)
    (hoffu : ¬ (elim.dotP u.coords u.coords).oneValue BPair.unit)
    (gws : List (List Nat))
    (hgcb : ∀ ws ∈ gws, (∀ l ∈ ws, l + 1 < d)
      ∧ (wact ws v).content = mu)
    (G : elim.Mat)
    (hgrp : G = gws.map (fun ws => (wact ws v).coords))
    (hind : elim.indepRows (monomialsAt mu).length G) :
    elim.indepRows (monomialsAt mu).length
      (gws.map (fun ws => (wact ws u).coords)) := by
  refine elim.indep_intro _ _
    (rows_len_words u mu hsu gws (fun ws hw =>
      (wact_content_congr v u hvu ws).symm.trans (hgcb ws hw).2)) ?_
  intro cs hcl hnull
  have hself := comboGram d v u mu hsv hsu hdv hvu htv htu
    gws cs hgcb cs gws hgcb
  have hxx : (elim.dotP
      (elim.combo (monomialsAt mu).length cs
        (gws.map (fun ws => (wact ws u).coords)))
      (elim.combo (monomialsAt mu).length cs
        (gws.map (fun ws => (wact ws u).coords)))).oneValue
      BPair.unit :=
    elim.dotP_null_tail_right _ _ hnull
  have h2 : ((elim.dotP
      (elim.combo (monomialsAt mu).length cs
        (gws.map (fun ws => (wact ws u).coords)))
      (elim.combo (monomialsAt mu).length cs
        (gws.map (fun ws => (wact ws u).coords))))
      * elim.dotP v.coords v.coords).oneValue BPair.unit :=
    BPair.oneValue_trans (BPair.mul_congr_left hxx)
      (BPair.unit_mul _)
  have h3 := BPair.oneValue_trans hself h2
  have h4 : (elim.dotP u.coords u.coords
      * elim.dotP
        (elim.combo (monomialsAt mu).length cs
          (gws.map (fun ws => (wact ws v).coords)))
        (elim.combo (monomialsAt mu).length cs
          (gws.map (fun ws => (wact ws v).coords)))).oneValue
      BPair.unit := by
    rw [BPair.mul_comm]
    exact h3
  have h5 := mul_cancel_unit hoffu h4
  have h6 := elim.dotP_self_null _ h5
  rw [← hgrp] at h6
  refine elim.indep_elim hind cs ?_ h6
  rw [hgrp, ground.length_map]
  rw [ground.length_map] at hcl
  exact hcl

/-- The per-content count comparison: the first pool's group maps
to an independent list inside the second pool's group span, the
words' pairings the transport (`lem:blockirr`(iv): the occupancies
agreeing). -/
theorem occ_le (d : Nat) (v : HVec) (tailv : List HVec)
    (u : HVec) (tailu : List HVec)
    (hszv : ∀ w ∈ v :: tailv, sized w)
    (hprovv : ∀ k, k < tailv.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tailv) i)
          = some (getAt (⟨[], []⟩ : HVec) tailv k))
    (hindv : indepAll (v :: tailv))
    (htv : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j v).coords)
    (hszu : ∀ w ∈ u :: tailu, sized w)
    (hsetu : ∀ w ∈ u :: tailu, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt (u :: tailu) (act i j w))
    (hindu : indepAll (u :: tailu))
    (htu : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j u).coords)
    (hdv : v.content.length = d) (hvu : v.content = u.content) :
    ∀ mu : List Nat, occ mu (v :: tailv) ≤ occ mu (u :: tailu) := by
  intro mu
  match Nat.eq_zero_or_pos (occ mu (v :: tailv)) with
  | .inl hz =>
    rw [hz]
    exact Nat.zero_le _
  | .inr hpos =>
    have hmem : mu ∈ (v :: tailv).map HVec.content := by
      rw [occ_eq_countOf] at hpos
      exact mem_of_countOf_pos mu _ hpos
    match pool_words d v tailv hprovv with
    | ⟨wl, hpw, hwb⟩ =>
      match groupAt_map_congr (fun ws => wact ws v)
          (fun ws => wact ws v) (fun _ => rfl) mu wl with
      | ⟨gws, hg, _, hgm, hgc⟩ =>
        have hgrp : groupAt (v :: tailv) mu
            = gws.map (fun ws => (wact ws v).coords) := by
          rw [hpw]
          exact hg
        have hgcb : ∀ ws ∈ gws, (∀ l ∈ ws, l + 1 < d)
            ∧ (wact ws v).content = mu :=
          fun ws hw => ⟨hwb ws (hgm ws hw), hgc ws hw⟩
        have hgcu : ∀ ws ∈ gws, (wact ws u).content = mu :=
          fun ws hw =>
            (wact_content_congr v u hvu ws).symm.trans (hgc ws hw)
        have hindm := hindv mu hmem
        have hgu : groupAt (u :: tailu) u.content
            = u.coords :: groupAt tailu u.content := by
          rw [groupAt_cons, ground.listEqBeq u.content]
        have hoff0 : ¬ poly.unitTail u.coords := by
          have h := elim.indep_row_off
            (hindu u.content (List.Mem.head _)) 0
            (by rw [hgu]; exact Nat.succ_pos _)
          rw [show ground.getAt ([] : List BPair)
              (groupAt (u :: tailu) u.content) 0 = u.coords by
            rw [hgu]; rfl] at h
          exact h
        have hoffu : ¬ (elim.dotP u.coords
            u.coords).oneValue BPair.unit :=
          fun hh => hoff0 (elim.dotP_self_null u.coords hh)
        have hiA := image_indep d v u mu
          (hszv v (List.Mem.head tailv))
          (hszu u (List.Mem.head tailu)) hdv hvu htv htu hoffu
          gws hgcb (groupAt (v :: tailv) mu) hgrp hindm
        have hmemA : ∀ k,
            k < (gws.map (fun ws => (wact ws u).coords)).length →
            elim.spanRel (monomialsAt mu).length
              (groupAt (u :: tailu) mu)
              (ground.getAt ([] : List BPair)
                (gws.map (fun ws => (wact ws u).coords)) k) := by
          intro k hk
          have hk' : k < gws.length := by
            rw [ground.length_map] at hk
            exact hk
          rw [ground.getAt_map ([] : List Nat) ([] : List BPair)
            (fun ws => (wact ws u).coords) gws k hk']
          have hws := ground.mem_getAt ([] : List Nat) gws k hk'
          have hspan := word_span d u tailu hszu hsetu
            (ground.getAt ([] : List Nat) gws k) (hgcb _ hws).1
          rw [hgcu _ hws] at hspan
          exact hspan
        have hcount := elim.span_count_le (monomialsAt mu).length
          (gws.map (fun ws => (wact ws u).coords))
          (groupAt (u :: tailu) mu)
          (rows_len_words u mu (hszu u (List.Mem.head tailu))
            gws hgcu)
          (rowsLen_groupAt mu (u :: tailu) hszu)
          hiA hmemA
        rw [ground.length_map] at hcount
        have hv : occ mu (v :: tailv) = gws.length := by
          rw [← length_groupAt mu (v :: tailv), hgrp,
            ground.length_map]
        have hu' : (groupAt (u :: tailu) mu).length
            = occ mu (u :: tailu) :=
          length_groupAt mu (u :: tailu)
        rw [hv, ← hu']
        exact hcount

/-- Two blocks at one top content read one occupancy at every
content, the two group-count comparisons' meet
(`lem:blockirr`(iv)'s group counts, `occ_le` both ways). -/
theorem occ_eq (d : Nat) (v : HVec) (tailv : List HVec)
    (u : HVec) (tailu : List HVec)
    (hszv : ∀ w ∈ v :: tailv, sized w)
    (hwidv : ∀ w ∈ v :: tailv, w.content.length = d)
    (hprovv : ∀ k, k < tailv.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tailv) i)
          = some (getAt (⟨[], []⟩ : HVec) tailv k))
    (hindv : indepAll (v :: tailv))
    (hsetv : ∀ w ∈ v :: tailv, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt (v :: tailv) (act i j w))
    (htv : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j v).coords)
    (hszu : ∀ w ∈ u :: tailu, sized w)
    (hwidu : ∀ w ∈ u :: tailu, w.content.length = d)
    (hprovu : ∀ k, k < tailu.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (u :: tailu) i)
          = some (getAt (⟨[], []⟩ : HVec) tailu k))
    (hindu : indepAll (u :: tailu))
    (hsetu : ∀ w ∈ u :: tailu, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt (u :: tailu) (act i j w))
    (htu : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j u).coords)
    (hvu : v.content = u.content) :
    ∀ mu : List Nat, occ mu (v :: tailv) = occ mu (u :: tailu) :=
  fun mu =>
    Nat.le_antisymm
      (occ_le d v tailv u tailu hszv hprovv hindv htv
        hszu hsetu hindu htu
        (hwidv v (List.Mem.head tailv)) hvu mu)
      (occ_le d u tailu v tailv hszu hprovu hindu htu
        hszv hsetv hindv htv
        (hwidu u (List.Mem.head tailu)) hvu.symm mu)

/-- `lem:blockirr`(iv), one dimension per shape: two pools at the
span calculus's stated data whose heads read one content read one
count — content group by content group the word images read the
group's own Gram at the coefficient scale (`blockcount.wordGram`),
each group's images independent inside the partner's group at the
moved content, and the occupied contents' counts sum to the
dimensions at the orthogonal grading. -/
theorem dim_eq (d : Nat) (v : HVec) (tailv : List HVec)
    (u : HVec) (tailu : List HVec)
    (hszv : ∀ w ∈ v :: tailv, sized w)
    (hwidv : ∀ w ∈ v :: tailv, w.content.length = d)
    (hprovv : ∀ k, k < tailv.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tailv) i)
          = some (getAt (⟨[], []⟩ : HVec) tailv k))
    (hindv : indepAll (v :: tailv))
    (hsetv : ∀ w ∈ v :: tailv, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt (v :: tailv) (act i j w))
    (htv : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j v).coords)
    (hszu : ∀ w ∈ u :: tailu, sized w)
    (hwidu : ∀ w ∈ u :: tailu, w.content.length = d)
    (hprovu : ∀ k, k < tailu.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (u :: tailu) i)
          = some (getAt (⟨[], []⟩ : HVec) tailu k))
    (hindu : indepAll (u :: tailu))
    (hsetu : ∀ w ∈ u :: tailu, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt (u :: tailu) (act i j w))
    (htu : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j u).coords)
    (hvu : v.content = u.content) :
    (v :: tailv).length = (u :: tailu).length := by
  have hocc := occ_eq d v tailv u tailu hszv hwidv hprovv hindv
    hsetv htv hszu hwidu hprovu hindu hsetu htu hvu
  rw [← ground.length_map HVec.content (v :: tailv),
    ← ground.length_map HVec.content (u :: tailu)]
  exact ground.length_eq_of_countOf _ _ (fun x => by
    rw [← occ_eq_countOf x (v :: tailv),
      ← occ_eq_countOf x (u :: tailu)]
    exact hocc x)

end blockirr
