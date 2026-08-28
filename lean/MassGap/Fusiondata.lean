import MassGap.Blockirr
import MassGap.Tops
import MassGap.Orthsplit
/-!
`lem:blockcount`'s exhaustion tier, opened at the block dimension:
a stated top's closure pool reads the shape's own count
(`seedBlock_dim`, `lem:blockirr`(iv) at the two pools — the seed's
closure against the shape's `blockSpan`), the shape the content's
gap read (`places.shapeOf` at `lem:tops`(ii)'s dominance).  The
producer's top reads: each round's pick is a top (`pickTop_top`,
a raising strictly raising the height fold at
`lowerspan.ht_moveAt_raise`, so an occupier of the raised content
off the sum's unit would break the pick's maximality and the
raised group's rows read the unit tail, where the pair's closure
settles the image — `elim.spanRel_unit_of_units` at the unit-rowed
group), and the residual carrier keeps the carrier pack — the
enumerations (`residCarrier_sized`), the widths
(`residCarrier_width`), and the closure
(`residCarrier_closed`, `lem:orthsplit`'s
complement invariance at the stated lists) — so every produced
member is a top at the stated data (`exhaust_top`), the carrier's
off-unit binder off that clause's path.  The descent's
completeness: every stated member sits inside the produced blocks'
joined span (`exhaust_span` at the per-top block `blockOf` and its
join `blockJoin`), the
per-member identity the residual's join read back
(`elim.residV_expand`) at the block's collected group with the
residual recursed, and each round strictly shortens the carrier —
the pick's own residual reads the unit through the solve
(`lem:lowerspan`'s member-vector clause) — so the carrier's length
is the descent's fuel (`exhaustGo_span`).  The count's additivity
over the split is landed at the split's stated data
(`countAt_append`, `lem:blockcount`(ii)'s clause): the raising
kernels split at `top_split`'s mechanism run per adjacent move
(the discharge `cross_split`, each part's image inside its own
side's moved span with the two images perpendicular and their
join the sum's unit, the positive pairing withdrawing both), the
kernel dimensions add at the kernel lists
(`elim.kernelDim_rowJoin` at the two cross data), and the counts
read the graded dimensions at the collections' one count
(`elim.kernelDim_congr`).  A block reads its own count alone
(`countAt_block`, the closing display's delta): one at the head's
content — the top-content group the head's one-member line with
the stacked column at the unit through the closed pool's derived
top read (the pinned top binder fell to the derivation: the raised
content's group is vacant at the height fold and the closure
settles the image at the unit) — and nought at every other, an
occupied kernel coefficient handing an off-unit top whose closure
pool maps into the block at the identity family with the head
contents agreeing (`blockirr.hom_content`).  The descent's other
half is the orthogonality tier: against an external pool closed at
every letter pair, a carrier pairing that pool's content groups at
the sum's unit hands blocks pairing there too — the letter pair's
image walks its pairing across the transpose partner to the
reverse move of the paired row's own member (`unit_adjoint` at
`moveAt_round_at`), the seed's closure carries the display along
the provenance, and the residual carrier carries it onward at the
collected group.  The round's own block is the instance the
descent consumes, its residual carrier pairing that block at the
sum's unit outright (`elim.resid_perp` at
`elim.collect_span_row`), so the produced blocks are pairwise
perpendicular (`exhaust_perp`), every produced member settles in
the stated carrier (`exhaust_settle`, the provenance walk at the
carrier's closure with the residuals' spans composing along the
rounds), and the join is independent at every content
(`exhaust_indep`, `elim.indep_append_perp` at the split groups).
The exhaustion count lands at the descent's own read
(`countAt_exhaust`, `lem:blockcount`(ii)'s closing sentence): the
stated carrier's count is the produced tops' occupancy at the
content, each round's block reading one count at its head content
(`countAt_block`) with the counts adding over the orthogonal split
(`countAt_append`) and the round's congruence (`countAt_congr`)
carrying the carrier's read across the block joined to its residual
carrier — the left side the carrier's alone, and two carriers of
one span produce one occupancy (`occ_exhaust_congr`, the closing
sentence's "every").  The dimension display closes
the tier (`dimOf`, `dimOf_countAt`): the graded dimensions' fold
over the occupied contents reads the carrier's own counts against
the block dimensions, the collections' counts passing to the
produced join's groups at the two-list exchange
(`elim.span_count_eq` at `exhaust_span` and `exhaust_settle`, the
device `collect_blockJoin`), the
join's length partitioning over the contents
(`ground.countOf_partition` at the dedup index), and each per-top
block reading its shape's own pool count (`seedBlock_dim` at
`exhaust_top`, derived from the per-content agreement
`seedBlock_occ` at the joined partition).  The graded display
refines it per content (`gradedDim_countAt`,
`lem:blockcount`(ii)'s refining sentence): a content's dimension
over the carrier is the display's sum at the counts against the
blocks' occupancies, the join's occupancy split per top
(`occ_blockJoin`) with each block at its shape's own
(`seedBlock_occ`).  The fused carrier's independence and the fusion
identities close the tier: the bridge from the fusion count to the
fused pool's own count (`fusionCount_countAt`), the block's delta
at its row list (`countAt_blockSpan`), the unit shape's line
(`fusionCount_unit`), the flip assembled at the exchanged pair
list (`fusionCount_comm`), the block transport at a top's
provenance pool (`countAt_fused_block`), and the fused carrier's
dimension display (`fusionCount_dim`, `lem:blockcount`(iii)'s
fourth clause at M = W_a x W_b — the fused pool closed at the
letters' split folds and independent at every content, so (ii)'s
display applies with the counts the fusion counts themselves and
the other side the pair list's own count).  The exhaustion
expansion (`countAt_fused_exhaust`) reads the fused count as the
per-top display over the exhaustion's distinct contents at a
one-degree carrier, `con:places`' one-degree blocks the frame:
the degree binder is load-bearing, its isolating refusal at a
two-degree carrier pinned in the check module beside the per-top
summands the refusal leaves intact.  The associativity display
(`fusionCount_assoc`) closes on it: each pairing's sum is the
triple pool's count, the second pairing read across the flip
(`countAt_fused_comm` at `kernelDim_pairs_comm`) with the
composition associative at the arrangements' join
(`fusedAt_assoc`).
-/

namespace blockcount
open ground places

/-- A stated top's closure pool reads the shape's own occupancy
at every content: the seed's pool and the shape's `blockSpan` sit
at the stated data with the heads at one content, and
`lem:blockirr`(iv)'s group counts read one occupancy
(`blockirr.occ_eq` at the two stated carriers). -/
theorem seedBlock_occ (d : Nat) (w : HVec)
    (hsz : sized w) (hwd : w.content.length = d)
    (hoff : ¬ poly.unitTail w.coords)
    (htop : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j w).coords)
    (fuel : Nat) (hfuel : lowerspan.ht w.content ≤ fuel) :
    ∀ mu : List Nat,
    occ mu (closeSpan d fuel [w] [w])
      = occ mu (blockSpan (shapeOf w.content)) := by
  match lowerspan.seed_closed d fuel w hsz hwd hoff
      (fun jr hjr => htop (jr + 1) hjr jr (Nat.lt_succ_self jr))
      hfuel with
  | ⟨tail, htl, hszv, hwidv, hprovv, hindv, hsetv⟩ =>
    have hdom : ∀ k, k + 1 < w.content.length →
        ground.getAt 0 w.content (k + 1)
          ≤ ground.getAt 0 w.content k := by
      intro k hk
      refine tops.dominant d w hsz hwd hoff htop k ?_
      rw [← hwd]
      exact hk
    have hrl : rowList (shapeOf w.content) = w.content :=
      rowList_shapeOf w.content hdom
    have hlen_s : (shapeOf w.content).length = d := by
      rw [length_shapeOf]
      exact hwd
    have hsemu := blockSpan_sem (shapeOf w.content) lowerspan.ht
      (lowerspan.ht_nomove (shapeOf w.content).length)
      (lowerspan.ht_drop (shapeOf w.content).length)
      (lowerspan.ht_exh (shapeOf w.content))
      (exhibit_sized (shapeOf w.content))
      (exhibit_off_unit (shapeOf w.content))
    obtain ⟨hszu, hindu, hclu⟩ := hsemu
    have hwidu := blockSpan_width (shapeOf w.content)
    have hsetu0 : ∀ i j : Nat, i < d → j < d → ¬ i = j →
        ∀ x ∈ blockSpan (shapeOf w.content),
          settledAt (blockSpan (shapeOf w.content)) (act i j x) := by
      intro i j hi hj hij
      exact act_closed (shapeOf w.content) hszu hclu i j
        (by rw [hlen_s]; exact hi) (by rw [hlen_s]; exact hj) hij
    have htopu : ∀ j, j < d → ∀ i, i < j →
        poly.unitTail
          (act i j (exhibit (shapeOf w.content))).coords := by
      intro j hj i hij
      have h := exhibit_top_all (shapeOf w.content) i j hij
        (by rw [hlen_s]; exact hj)
      show poly.unitTail (elim.matVec (units.matUnitAt
        (moveAt i j (exhibit (shapeOf w.content)).content)
        (exhibit (shapeOf w.content)).content i j)
        (exhibit (shapeOf w.content)).coords)
      rw [content_exhibit]
      exact h
    have hvu : w.content
        = (exhibit (shapeOf w.content)).content := by
      rw [content_exhibit, hrl]
    match blockSpan_prov (shapeOf w.content) with
    | ⟨tailu, htu', hprovu⟩ =>
      rw [htu'] at hszu hindu hwidu
      have hsetu : ∀ x ∈ exhibit (shapeOf w.content) :: tailu,
          ∀ i, i < d → ∀ j, j < d → ¬ i = j →
          settledAt (exhibit (shapeOf w.content) :: tailu)
            (act i j x) := by
        intro x hx i hi j hj hij
        have h := hsetu0 i j hi hj hij x (by rw [htu']; exact hx)
        rw [htu'] at h
        exact h
      have hwidu' : ∀ x ∈ exhibit (shapeOf w.content) :: tailu,
          x.content.length = d :=
        fun x hx => (hwidu x hx).trans hlen_s
      have hprovu' : ∀ k, k < tailu.length →
          ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
            lowerH j (getAt (⟨[], []⟩ : HVec)
                (exhibit (shapeOf w.content) :: tailu) i)
              = some (getAt (⟨[], []⟩ : HVec) tailu k) := by
        intro k hk
        match hprovu k hk with
        | ⟨i, hik, j, hjd, hlow⟩ =>
          refine ⟨i, hik, j, ?_, hlow⟩
          rw [← hlen_s]
          exact hjd
      intro mu
      rw [htl, htu']
      exact blockirr.occ_eq d w tail
        (exhibit (shapeOf w.content)) tailu
        hszv hwidv hprovv hindv hsetv htop
        hszu hwidu' hprovu' hindu hsetu htopu hvu mu

/-- A stated top's closure pool reads the shape's own count: the
graded occupancies agree content by content (`seedBlock_occ`) and
two lists at one count per member are one length
(`ground.length_eq_of_countOf` at the content lists). -/
theorem seedBlock_dim (d : Nat) (w : HVec)
    (hsz : sized w) (hwd : w.content.length = d)
    (hoff : ¬ poly.unitTail w.coords)
    (htop : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j w).coords)
    (fuel : Nat) (hfuel : lowerspan.ht w.content ≤ fuel) :
    (closeSpan d fuel [w] [w]).length
      = (blockSpan (shapeOf w.content)).length := by
  have hocc := seedBlock_occ d w hsz hwd hoff htop fuel hfuel
  rw [← ground.length_map HVec.content (closeSpan d fuel [w] [w]),
    ← ground.length_map HVec.content
      (blockSpan (shapeOf w.content))]
  exact ground.length_eq_of_countOf _ _ (fun x => by
    rw [← occ_eq_countOf x (closeSpan d fuel [w] [w]),
      ← occ_eq_countOf x (blockSpan (shapeOf w.content))]
    exact hocc x)

/-! The exhaustion producer: the height-maximal occupied pick, the
per-content residual carrier, and the descent — `lem:blockcount`
(i)'s construction, each round one top with its block withdrawn at
the residuals. -/

/-- The pick: the height-maximal member off the unit tail, the
maximal occupied content's own witness. -/
def pickTop : List HVec → Option HVec
  | [] => none
  | v :: t =>
    match pickTop t with
    | none => if allU v.coords then none else some v
    | some w =>
      if allU v.coords then some w
      else if lowerspan.ht w.content < lowerspan.ht v.content
        then some v else some w

/-- The pick's one-step unfolding. -/
theorem pickTop_cons (v : HVec) (t : List HVec) :
    pickTop (v :: t)
      = match pickTop t with
        | none => if allU v.coords then none else some v
        | some w =>
          if allU v.coords then some w
          else if lowerspan.ht w.content < lowerspan.ht v.content
            then some v else some w := rfl

/-- The residual at a stated block: the member's
determinant-scaled perpendicular part against the block's
collected group at its own content, the joined-collection read's
residual (`lem:lowerspan`). -/
def residAt (B : List HVec) (x : HVec) : HVec :=
  ⟨x.content,
    elim.residV x.coords.length
      (elim.collectOf x.coords.length (groupAt B x.content))
      x.coords⟩

/-- The residual carrier: the members' residuals at the block, the
unit tails withdrawn. -/
def residCarrier (P B : List HVec) : List HVec :=
  (P.map (residAt B)).filter (fun x => ! allU x.coords)

/-- The block at a stated top: the seed's closure pool at the
content's height, `lem:lowerspan`'s W_v as a stated list. -/
def blockOf (d : Nat) (w : HVec) : List HVec :=
  closeSpan d (lowerspan.ht w.content) [w] [w]

/-- The block's own spelling as the seed's closure pool at the
content's height. -/
private theorem blockOf_eq (d : Nat) (w : HVec) :
    blockOf d w = closeSpan d (lowerspan.ht w.content) [w] [w] := rfl

/-- The descent: each round picks the height-maximal member, joins
its block's closure, and recurses on the residual carrier. -/
def exhaustGo (d : Nat) : Nat → List HVec → List HVec
  | 0, _ => []
  | fuel + 1, P =>
    match pickTop P with
    | none => []
    | some w =>
      w :: exhaustGo d fuel
        (residCarrier P
          (blockOf d w))

/-- The exhaustion: the descent at the carrier's own length. -/
def exhaust (d : Nat) (P : List HVec) : List HVec :=
  exhaustGo d P.length P

/-- The pick's case split at the head, iota-reduced. -/
private theorem pickTop_split (v : HVec) (t : List HVec) :
    (pickTop t = none
      ∧ pickTop (v :: t)
          = (if allU v.coords then none else some v))
    ∨ ∃ y, pickTop t = some y
      ∧ pickTop (v :: t)
          = (if allU v.coords then some y
            else if lowerspan.ht y.content < lowerspan.ht v.content
              then some v else some y) := by
  match hp : pickTop t with
  | none =>
    refine Or.inl ⟨rfl, ?_⟩
    rw [pickTop_cons, hp]
  | some y =>
    refine Or.inr ⟨y, rfl, ?_⟩
    rw [pickTop_cons, hp]

/-- A refused pick reads every member at the unit tail. -/
theorem pickTop_none : ∀ (P : List HVec),
    pickTop P = none → ∀ x ∈ P, allU x.coords = true
  | [], _, _, hx => nomatch hx
  | v :: t, h, x, hx => by
    match pickTop_split v t with
    | .inl ⟨hp, hc⟩ =>
      rw [hc] at h
      by_cases hu : allU v.coords
      · match hx with
        | .head _ => exact hu
        | .tail _ hxt => exact pickTop_none t hp x hxt
      · rw [if_neg hu] at h
        exact nomatch h
    | .inr ⟨y, hp, hc⟩ =>
      rw [hc] at h
      by_cases hu : allU v.coords
      · rw [if_pos hu] at h
        exact nomatch h
      · rw [if_neg hu] at h
        by_cases hlt : lowerspan.ht y.content
            < lowerspan.ht v.content
        · rw [if_pos hlt] at h
          exact nomatch h
        · rw [if_neg hlt] at h
          exact nomatch h

/-- The pick is a member. -/
theorem pickTop_mem : ∀ (P : List HVec) (w : HVec),
    pickTop P = some w → w ∈ P
  | [], _, h => nomatch h
  | v :: t, w, h => by
    match pickTop_split v t with
    | .inl ⟨hp, hc⟩ =>
      rw [hc] at h
      by_cases hu : allU v.coords
      · rw [if_pos hu] at h
        exact nomatch h
      · rw [if_neg hu] at h
        rw [show w = v from (Option.some.inj h).symm]
        exact List.Mem.head t
    | .inr ⟨y, hp, hc⟩ =>
      rw [hc] at h
      by_cases hu : allU v.coords
      · rw [if_pos hu] at h
        exact List.Mem.tail v
          (pickTop_mem t w (Option.some.inj h ▸ hp))
      · rw [if_neg hu] at h
        by_cases hlt : lowerspan.ht y.content
            < lowerspan.ht v.content
        · rw [if_pos hlt] at h
          rw [show w = v from (Option.some.inj h).symm]
          exact List.Mem.head t
        · rw [if_neg hlt] at h
          exact List.Mem.tail v
            (pickTop_mem t w (Option.some.inj h ▸ hp))

/-- The pick sits off the unit tail. -/
theorem pickTop_off : ∀ (P : List HVec) (w : HVec),
    pickTop P = some w → ¬ poly.unitTail w.coords
  | [], _, h => nomatch h
  | v :: t, w, h => by
    match pickTop_split v t with
    | .inl ⟨hp, hc⟩ =>
      rw [hc] at h
      by_cases hu : allU v.coords
      · rw [if_pos hu] at h
        exact nomatch h
      · rw [if_neg hu] at h
        rw [show w = v from (Option.some.inj h).symm]
        exact fun hui => hu (allU_of_unitTail v.coords hui)
    | .inr ⟨y, hp, hc⟩ =>
      rw [hc] at h
      by_cases hu : allU v.coords
      · rw [if_pos hu] at h
        exact pickTop_off t w (Option.some.inj h ▸ hp)
      · rw [if_neg hu] at h
        by_cases hlt : lowerspan.ht y.content
            < lowerspan.ht v.content
        · rw [if_pos hlt] at h
          rw [show w = v from (Option.some.inj h).symm]
          exact fun hui => hu (allU_of_unitTail v.coords hui)
        · rw [if_neg hlt] at h
          exact pickTop_off t w (Option.some.inj h ▸ hp)

/-- The pick's height is maximal among the members off the unit
tail. -/
theorem pickTop_max : ∀ (P : List HVec) (w : HVec),
    pickTop P = some w → ∀ x ∈ P, ¬ poly.unitTail x.coords →
      lowerspan.ht x.content ≤ lowerspan.ht w.content
  | [], _, h => nomatch h
  | v :: t, w, h => by
    match pickTop_split v t with
    | .inl ⟨hp, hc⟩ =>
      rw [hc] at h
      by_cases hu : allU v.coords
      · rw [if_pos hu] at h
        exact nomatch h
      · rw [if_neg hu] at h
        intro x hx hxoff
        match hx with
        | .head _ =>
          rw [show w = x from (Option.some.inj h).symm]
          exact Nat.le_refl _
        | .tail _ hxt =>
          exact absurd (unitTail_of_allU x.coords
            (pickTop_none t hp x hxt)) hxoff
    | .inr ⟨y, hp, hc⟩ =>
      rw [hc] at h
      by_cases hu : allU v.coords
      · rw [if_pos hu] at h
        intro x hx hxoff
        match hx with
        | .head _ =>
          exact absurd (unitTail_of_allU x.coords hu) hxoff
        | .tail _ hxt =>
          exact pickTop_max t w (Option.some.inj h ▸ hp) x hxt hxoff
      · rw [if_neg hu] at h
        by_cases hlt : lowerspan.ht y.content
            < lowerspan.ht v.content
        · rw [if_pos hlt] at h
          intro x hx hxoff
          match hx with
          | .head _ =>
            rw [show w = x from (Option.some.inj h).symm]
            exact Nat.le_refl _
          | .tail _ hxt =>
            have hy := pickTop_max t y hp x hxt hxoff
            rw [show w = v from (Option.some.inj h).symm]
            exact Nat.le_trans hy (Nat.le_of_lt hlt)
        · rw [if_neg hlt] at h
          intro x hx hxoff
          match hx with
          | .head _ =>
            rw [show w = y from (Option.some.inj h).symm]
            match Nat.lt_or_ge (lowerspan.ht y.content)
                (lowerspan.ht x.content) with
            | .inl hl => exact absurd hl hlt
            | .inr hge => exact hge
          | .tail _ hxt =>
            exact pickTop_max t w (Option.some.inj h ▸ hp) x hxt hxoff

/-! The residual carrier's reads: the members are the stated
carrier's residuals at the block's content groups off the unit
tail, and the invariants descend — the coordinate enumerations,
the widths, and the off-unit read; the closure at the letter
pairs is `lem:orthsplit`'s complement invariance at the stated
lists. -/

/-- The residual carrier's head split, iota-reduced. -/
private theorem residCarrier_split (x : HVec) (t B : List HVec) :
    (allU (residAt B x).coords = true
      ∧ residCarrier (x :: t) B = residCarrier t B)
    ∨ (allU (residAt B x).coords = false
      ∧ residCarrier (x :: t) B
          = residAt B x :: residCarrier t B) := by
  match hb : allU (residAt B x).coords with
  | true =>
    refine Or.inl ⟨rfl, ?_⟩
    show ((residAt B x :: t.map (residAt B)).filter
      (fun z => ! allU z.coords)) = _
    rw [ground.filter_cons (fun z => ! allU z.coords)
      (residAt B x) (t.map (residAt B)), hb]
    rfl
  | false =>
    refine Or.inr ⟨rfl, ?_⟩
    show ((residAt B x :: t.map (residAt B)).filter
      (fun z => ! allU z.coords)) = _
    rw [ground.filter_cons (fun z => ! allU z.coords)
      (residAt B x) (t.map (residAt B)), hb]
    rfl

/-- A residual carrier member is a stated member's residual off
the unit-family read. -/
private theorem residCarrier_mem : ∀ (P B : List HVec) (y : HVec),
    y ∈ residCarrier P B →
    allU y.coords = false ∧ ∃ x, x ∈ P ∧ y = residAt B x
  | [], _, _, hy => nomatch hy
  | x :: t, B, y, hy => by
    match residCarrier_split x t B with
    | .inl ⟨_, hc⟩ =>
      rw [hc] at hy
      match residCarrier_mem t B y hy with
      | ⟨hoff, z, hz, hyz⟩ =>
        exact ⟨hoff, z, List.Mem.tail x hz, hyz⟩
    | .inr ⟨hb, hc⟩ =>
      rw [hc] at hy
      match y, hy with
      | _, List.Mem.head _ => exact ⟨hb, x, List.Mem.head t, rfl⟩
      | y', List.Mem.tail _ hyt =>
        match residCarrier_mem t B y' hyt with
        | ⟨hoff, z, hz, hyz⟩ =>
          exact ⟨hoff, z, List.Mem.tail x hz, hyz⟩

/-- A stated member's residual off the unit-family read joins the
residual carrier. -/
private theorem residCarrier_mem_intro :
    ∀ (P B : List HVec) (x : HVec), x ∈ P →
    allU (residAt B x).coords = false →
    residAt B x ∈ residCarrier P B
  | [], _, _, hx, _ => nomatch hx
  | v :: t, B, x, hx, hoff => by
    match residCarrier_split v t B with
    | .inl ⟨hb, hc⟩ =>
      rw [hc]
      match x, hx, hoff with
      | _, List.Mem.head _, hoff' =>
        rw [hoff'] at hb
        exact Bool.noConfusion hb
      | x', List.Mem.tail _ hxt, hoff' =>
        exact residCarrier_mem_intro t B x' hxt hoff'
    | .inr ⟨hb, hc⟩ =>
      rw [hc]
      match x, hx, hoff with
      | _, List.Mem.head _, _ => exact List.Mem.head _
      | x', List.Mem.tail _ hxt, hoff' =>
        exact List.Mem.tail _
          (residCarrier_mem_intro t B x' hxt hoff')

/-- The residual carrier's members read the stated enumerations:
the residual keeps its member's coordinate width at the block
group's rows. -/
theorem residCarrier_sized (P B : List HVec)
    (hszP : ∀ x ∈ P, sized x) (hszB : ∀ x ∈ B, sized x) :
    ∀ y ∈ residCarrier P B, sized y := by
  intro y hy
  match residCarrier_mem P B y hy with
  | ⟨_, x, hxP, hyx⟩ =>
    rw [hyx]
    show (elim.residV x.coords.length
        (elim.collectOf x.coords.length (groupAt B x.content))
        x.coords).length
      = (places.monomialsAt (residAt B x).content).length
    have hLn : elim.rowsLen x.coords.length
        (groupAt B x.content) := by
      rw [hszP x hxP]
      exact rowsLen_groupAt x.content B hszB
    rw [elim.length_residV x.coords.length
      (elim.collectOf x.coords.length (groupAt B x.content))
      x.coords (elim.collect_rowsLen _ _ hLn) rfl]
    exact hszP x hxP

/-- The residual carrier's members read the stated width, the
contents the members' own. -/
theorem residCarrier_width (d : Nat) (P B : List HVec)
    (hwidP : ∀ x ∈ P, x.content.length = d) :
    ∀ y ∈ residCarrier P B, y.content.length = d := by
  intro y hy
  match residCarrier_mem P B y hy with
  | ⟨_, x, hxP, hyx⟩ =>
    rw [hyx]
    exact hwidP x hxP


/-- A span read passes to a stated equal width. -/
private theorem spanRel_cast (n m : Nat) (L : elim.Mat)
    (v : List BPair) (h : elim.spanRel n L v) (hnm : n = m) :
    elim.spanRel m L v := by
  rw [← hnm]
  exact h

/-- A span member sits in its family's collection span, the
joined-collection read's transport. -/
private theorem spanRel_collect (n : Nat) (L : elim.Mat)
    (v : List BPair) (hL : elim.rowsLen n L)
    (h : elim.spanRel n L v) :
    elim.spanRel n (elim.collectOf n L) v :=
  elim.spanRel_trans n L (elim.collectOf n L) v hL
    (elim.collect_rowsLen n L hL)
    (elim.collect_span_row n L hL) h

/-- The residual carrier's closure at the letter pairs,
`lem:orthsplit`'s complement invariance at the stated lists: a
residual's action image walks its pairing across the transpose
partner to the block's collected source group where the
perpendicular reads clear it (`orthsplit.perp_invariant`), its
span read transports through the stated carrier's own closure
with every source row read back through the residual's join
(`elim.residV_expand` at the collection, independent by
`elim.collect_indep`), and the perpendicular tail splits off the
joined span (`elim.span_perp_split`).  The two closure binders
are load-bearing, their isolating refusals committed; the
enumeration and width binders are `con:places`' member
definition, the stated data's frame. -/
theorem residCarrier_closed (d : Nat) (P B : List HVec)
    (hszP : ∀ x ∈ P, sized x)
    (hwidP : ∀ x ∈ P, x.content.length = d)
    (hclP : ∀ x ∈ P, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt P (act i j x))
    (hszB : ∀ x ∈ B, sized x)
    (hclB : ∀ x ∈ B, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt B (act i j x)) :
    ∀ y ∈ residCarrier P B, ∀ i, i < d → ∀ j, j < d →
      ¬ i = j → settledAt (residCarrier P B) (act i j y) := by
  intro y hy i hi j hj hij
  match residCarrier_mem P B y hy with
  | ⟨_, x, hxP, hyx⟩ =>
    subst hyx
    match Nat.eq_zero_or_pos (ground.getAt 0 x.content j) with
    | .inl hz =>
      exact Or.inl (allU_of_unitTail _
        (tops.act_null i j (residAt B x) hz))
    | .inr hjocc =>
      have hji : ¬ j = i := fun he => hij he.symm
      have hmuw : x.content.length = d := hwidP x hxP
      have hsx : x.coords.length
          = (places.monomialsAt x.content).length := hszP x hxP
      have hi' : i < x.content.length := by
        rw [hmuw]
        exact hi
      have hj' : j < x.content.length := by
        rw [hmuw]
        exact hj
      have hround : moveAt j i (moveAt i j x.content)
          = x.content := moveAt_round_at j i x.content hjocc
      have hszQ : ∀ v ∈ residCarrier P B, sized v :=
        residCarrier_sized P B hszP hszB
      have hGrows : elim.rowsLen x.coords.length
          (groupAt B x.content) := by
        rw [hsx]
        exact rowsLen_groupAt x.content B hszB
      have hCrows : elim.rowsLen x.coords.length
          (elim.collectOf x.coords.length
            (groupAt B x.content)) :=
        elim.collect_rowsLen _ _ hGrows
      have hrvlen : (residAt B x).coords.length
          = x.coords.length := by
        show (elim.residV x.coords.length
          (elim.collectOf x.coords.length (groupAt B x.content))
          x.coords).length = _
        exact elim.length_residV _ _ x.coords hCrows rfl
      have hQrows : elim.rowsLen
          (places.monomialsAt (moveAt i j x.content)).length
          (groupAt (residCarrier P B) (moveAt i j x.content)) :=
        rowsLen_groupAt (moveAt i j x.content)
          (residCarrier P B) hszQ
      have hBrows' : elim.rowsLen
          (places.monomialsAt (moveAt i j x.content)).length
          (groupAt B (moveAt i j x.content)) :=
        rowsLen_groupAt (moveAt i j x.content) B hszB
      have hQB : elim.rowsLen
          (places.monomialsAt (moveAt i j x.content)).length
          (groupAt (residCarrier P B) (moveAt i j x.content)
            ++ groupAt B (moveAt i j x.content)) :=
        elim.rowsLen_append _ hQrows hBrows'
      have himgB : ∀ v ∈ B, settledAt B (act i j v) :=
        fun v hv => hclB v hv i hi j hj hij
      have himgB' : ∀ v ∈ B, settledAt B (act j i v) :=
        fun v hv => hclB v hv j hj i hi hji
      -- the image's perpendicular read at the moved group
      have hperpB : ∀ k,
          k < (groupAt B (moveAt i j x.content)).length →
          (elim.dotP
            (elim.matVec (units.matUnitAt (moveAt i j x.content)
              x.content i j) (residAt B x).coords)
            (ground.getAt [] (groupAt B (moveAt i j x.content))
              k)).oneValue BPair.unit := by
        refine orthsplit.perp_invariant x.coords.length
          (units.matUnitAt (moveAt i j x.content) x.content i j)
          (units.matUnitAt x.content (moveAt i j x.content) j i)
          (elim.collectOf x.coords.length (groupAt B x.content))
          (groupAt B (moveAt i j x.content))
          (residAt B x).coords
          hCrows hrvlen ?_ ?_ ?_
        · intro k hk
          exact unit_adjoint i j x.content hi' hj' hij hjocc
            (residAt B x).coords
            (ground.getAt []
              (groupAt B (moveAt i j x.content)) k)
            (by rw [hrvlen]; exact hsx)
            (elim.rowsLen_getAt _ k hBrows' hk)
        · intro k hk
          have hrowlen : (ground.getAt []
              (groupAt B (moveAt i j x.content)) k).length
              = (places.monomialsAt
                  (moveAt i j x.content)).length :=
            elim.rowsLen_getAt _ k hBrows' hk
          have htr := act_transport B j i hszB himgB'
            (moveAt i j x.content)
            (ground.getAt []
              (groupAt B (moveAt i j x.content)) k)
            hrowlen
            (elim.spanRel_getAt _ _ k hk hBrows')
          rw [hround] at htr
          exact spanRel_collect x.coords.length
            (groupAt B x.content) _ hGrows
            (spanRel_cast _ _ _ _ htr hsx.symm)
        · intro k hk
          rw [elim.dotP_comm]
          exact elim.resid_perp x.coords.length
            (elim.collectOf x.coords.length
              (groupAt B x.content))
            x.coords hCrows rfl k hk
      -- the moved image of the stated member's span
      have hs2 : elim.spanRel
          (places.monomialsAt (moveAt i j x.content)).length
          (groupAt (residCarrier P B) (moveAt i j x.content)
            ++ groupAt B (moveAt i j x.content))
          (elim.matVec (units.matUnitAt (moveAt i j x.content)
            x.content i j) x.coords) := by
        have hsp := settled_to_span P (act i j x) hszP
          (act_sized i j x) (hclP x hxP i hi j hj hij)
        have hlen2 : (act i j x).coords.length
            = (places.monomialsAt (moveAt i j x.content)).length
            := by
          show (elim.matVec (units.matUnitAt
              (moveAt i j x.content) x.content i j)
              x.coords).length = _
          rw [units.matVec_matUnitAt_length]
        rw [hlen2] at hsp
        refine elim.spanRel_trans _
          (groupAt P (moveAt i j x.content)) _ _
          (rowsLen_groupAt (moveAt i j x.content) P hszP)
          hQB ?_ hsp
        intro k hk
        match groupAt_rows (fun v => v ∈ P) P (fun _ hv => hv)
            (moveAt i j x.content) k hk with
        | ⟨p, hpP, hpc, hprow⟩ =>
          rw [hprow]
          have hp_sx : p.coords.length
              = (places.monomialsAt (moveAt i j x.content)).length
              := by
            rw [hszP p hpP, hpc]
          have hCrows' : elim.rowsLen
              (places.monomialsAt (moveAt i j x.content)).length
              (elim.collectOf
                (places.monomialsAt (moveAt i j x.content)).length
                (groupAt B (moveAt i j x.content))) :=
            elim.collect_rowsLen _ _ hBrows'
          have hreq2 : (residAt B p).coords
              = elim.residV
                  (places.monomialsAt (moveAt i j x.content)).length
                  (elim.collectOf
                    (places.monomialsAt
                      (moveAt i j x.content)).length
                    (groupAt B (moveAt i j x.content)))
                  p.coords := by
            show elim.residV p.coords.length
              (elim.collectOf p.coords.length
                (groupAt B p.content)) p.coords = _
            rw [hp_sx, hpc]
          have hresidlen : (elim.residV
              (places.monomialsAt (moveAt i j x.content)).length
              (elim.collectOf
                (places.monomialsAt (moveAt i j x.content)).length
                (groupAt B (moveAt i j x.content)))
              p.coords).length
              = (places.monomialsAt (moveAt i j x.content)).length
              := elim.length_residV _ _ p.coords hCrows' hp_sx
          have he2 : elim.spanRel
              (places.monomialsAt (moveAt i j x.content)).length
              (groupAt (residCarrier P B) (moveAt i j x.content)
                ++ groupAt B (moveAt i j x.content))
              (elim.residV
                (places.monomialsAt (moveAt i j x.content)).length
                (elim.collectOf
                  (places.monomialsAt
                    (moveAt i j x.content)).length
                  (groupAt B (moveAt i j x.content)))
                p.coords) := by
            match hb : allU (residAt B p).coords with
            | true =>
              refine elim.spanRel_null _ _ _ ?_ hQB hresidlen
              rw [← hreq2]
              exact unitTail_of_allU _ hb
            | false =>
              have hmem := residCarrier_mem_intro P B p hpP hb
              have he2a := settled_to_span (residCarrier P B)
                (residAt B p) hszQ
                (hszQ (residAt B p) hmem)
                (member_settled (residCarrier P B) hszQ
                  (residAt B p) hmem)
              have hqlen : (residAt B p).coords.length
                  = (places.monomialsAt
                      (moveAt i j x.content)).length := by
                rw [hreq2]
                exact hresidlen
              have hqc : (residAt B p).content
                  = moveAt i j x.content := by
                show p.content = _
                exact hpc
              rw [hqlen, hqc, hreq2] at he2a
              exact elim.spanRel_mono _ _ _ _ hQrows hBrows' he2a
          have he3 : elim.spanRel
              (places.monomialsAt (moveAt i j x.content)).length
              (groupAt (residCarrier P B) (moveAt i j x.content)
                ++ groupAt B (moveAt i j x.content))
              (elim.combo
                (places.monomialsAt (moveAt i j x.content)).length
                (elim.adjP
                  (elim.gramM (elim.collectOf
                    (places.monomialsAt
                      (moveAt i j x.content)).length
                    (groupAt B (moveAt i j x.content))))
                  ((elim.collectOf
                    (places.monomialsAt
                      (moveAt i j x.content)).length
                    (groupAt B (moveAt i j x.content))).map
                    (fun r => elim.dotP r p.coords)))
                (elim.collectOf
                  (places.monomialsAt
                    (moveAt i j x.content)).length
                  (groupAt B (moveAt i j x.content)))) := by
            refine elim.spanRel_combo _ _ hQB _ _ hCrows' ?_
            intro k2 hk2
            exact elim.spanRel_mono_left _ _ _ _ hQrows hBrows'
              (elim.collect_row_span _ _ hBrows' k2 hk2)
          have he5 := elim.spanRel_congr _ _ _ _
            (poly.oneValue_symm
              (elim.residV_expand
                (places.monomialsAt (moveAt i j x.content)).length
                (elim.collectOf
                  (places.monomialsAt
                    (moveAt i j x.content)).length
                  (groupAt B (moveAt i j x.content)))
                p.coords hCrows' hp_sx))
            (elim.spanRel_add _ _ _ _ hQB hresidlen
              (elim.length_combo _ _ _ hCrows') he2 he3)
            (by rw [elim.length_vecScale, hp_sx])
          exact elim.spanRel_unscale _ _ _ p.coords
            (elim.indep_det _ _
              (elim.collect_indep _ _ hBrows'))
            he5
      -- the swapped combination's moved image
      have hc4 := elim.matVec_combo
        (units.matUnitAt (moveAt i j x.content) x.content i j)
        x.coords.length
        (elim.adjP
          (elim.gramM (elim.collectOf x.coords.length
            (groupAt B x.content)))
          ((elim.collectOf x.coords.length
            (groupAt B x.content)).map
            (fun r => elim.dotP r x.coords)))
        (elim.collectOf x.coords.length (groupAt B x.content))
        hCrows
      rw [units.length_matUnitAt] at hc4
      have hc5 : elim.spanRel
          (places.monomialsAt (moveAt i j x.content)).length
          (groupAt (residCarrier P B) (moveAt i j x.content)
            ++ groupAt B (moveAt i j x.content))
          (elim.combo
            (places.monomialsAt (moveAt i j x.content)).length
            (elim.adjP
              (elim.gramM (elim.collectOf x.coords.length
                (groupAt B x.content)))
              ((elim.collectOf x.coords.length
                (groupAt B x.content)).map
                (fun r => elim.dotP r x.coords)))
            ((elim.collectOf x.coords.length
              (groupAt B x.content)).map
              (elim.matVec (units.matUnitAt
                (moveAt i j x.content) x.content i j)))) := by
        refine elim.spanRel_combo _ _ hQB _ _
          (elim.rowsLen_map _ _ _ (fun x _ => (fun r => units.matVec_matUnitAt_length _ _ i j r) x))
          ?_
        intro k2 hk2
        have hk2' : k2 < (elim.collectOf x.coords.length
            (groupAt B x.content)).length := by
          rw [ground.length_map] at hk2
          exact hk2
        rw [ground.getAt_map ([] : List BPair) ([] : List BPair)
          (elim.matVec (units.matUnitAt (moveAt i j x.content)
            x.content i j))
          (elim.collectOf x.coords.length (groupAt B x.content))
          k2 hk2']
        have hrl : (ground.getAt []
            (elim.collectOf x.coords.length
              (groupAt B x.content)) k2).length
            = (places.monomialsAt x.content).length := by
          rw [elim.rowsLen_getAt _ k2 hCrows hk2']
          exact hsx
        have hrow := spanRel_cast x.coords.length
          (places.monomialsAt x.content).length
          (groupAt B x.content)
          (ground.getAt []
            (elim.collectOf x.coords.length
              (groupAt B x.content)) k2)
          (elim.spanRel_trans _ _ _ _ hCrows hGrows
            (fun k3 hk3 => elim.collect_row_span _ _ hGrows k3 hk3)
            (elim.spanRel_getAt _ _ k2 hk2' hCrows))
          hsx
        have htr := act_transport B i j hszB himgB x.content
          (ground.getAt []
            (elim.collectOf x.coords.length
              (groupAt B x.content)) k2)
          hrl hrow
        exact elim.spanRel_mono_left _ _ _ _ hQrows hBrows' htr
      have hsp2 : elim.spanRel
          (places.monomialsAt (moveAt i j x.content)).length
          (groupAt (residCarrier P B) (moveAt i j x.content)
            ++ groupAt B (moveAt i j x.content))
          (elim.matVec
            (units.matUnitAt (moveAt i j x.content) x.content i j)
            ((elim.combo x.coords.length
              (elim.adjP
                (elim.gramM (elim.collectOf x.coords.length
                  (groupAt B x.content)))
                ((elim.collectOf x.coords.length
                  (groupAt B x.content)).map
                  (fun r => elim.dotP r x.coords)))
              (elim.collectOf x.coords.length
                (groupAt B x.content))).map BPair.swap)) := by
        refine elim.spanRel_congr _ _ _ _
          (poly.oneValue_symm
            (poly.oneValue_trans
              (elim.matVec_congr _ _ _
                (elim.swapMap_scale _))
              (poly.oneValue_trans
                (elim.matVec_vecScale_free _ _ _)
                (elim.vecScale_oneValue _ _ _ hc4))))
          (elim.spanRel_scale _ _ _ _ hQB
            (by rw [elim.length_combo _ _ _
              (elim.rowsLen_map _ _ _ (fun x _ => (fun r =>
                  units.matVec_matUnitAt_length _ _ i j r) x))])
            hc5)
          (by rw [units.matVec_matUnitAt_length])
      -- the joined span of the image, and the perpendicular split
      have hb1 : poly.oneValue
          (elim.matVec (units.matUnitAt (moveAt i j x.content)
            x.content i j) (residAt B x).coords)
          (elim.vecAdd
            (elim.matVec (units.matUnitAt (moveAt i j x.content)
              x.content i j)
              (elim.vecScale
                (elim.detL (elim.gramM
                  (elim.collectOf x.coords.length
                    (groupAt B x.content))))
                x.coords))
            (elim.matVec (units.matUnitAt (moveAt i j x.content)
              x.content i j)
              ((elim.combo x.coords.length
                (elim.adjP
                  (elim.gramM (elim.collectOf x.coords.length
                    (groupAt B x.content)))
                  ((elim.collectOf x.coords.length
                    (groupAt B x.content)).map
                    (fun r => elim.dotP r x.coords)))
                (elim.collectOf x.coords.length
                  (groupAt B x.content))).map BPair.swap))) := by
        show poly.oneValue
          (elim.matVec (units.matUnitAt (moveAt i j x.content)
            x.content i j)
            (elim.vecAdd
              (elim.vecScale
                (elim.detL (elim.gramM
                  (elim.collectOf x.coords.length
                    (groupAt B x.content))))
                x.coords)
              ((elim.combo x.coords.length
                (elim.adjP
                  (elim.gramM (elim.collectOf x.coords.length
                    (groupAt B x.content)))
                  ((elim.collectOf x.coords.length
                    (groupAt B x.content)).map
                    (fun r => elim.dotP r x.coords)))
                (elim.collectOf x.coords.length
                  (groupAt B x.content))).map BPair.swap))) _
        refine elim.matVec_vecAdd _ x.coords.length
          (by rw [hsx]; exact units.rowsLen_matUnitAt _ _ i j)
          _ _ (elim.length_vecScale _ _) ?_
        rw [ground.length_map]
        exact elim.length_combo _ _ _ hCrows
      have hsp1 : elim.spanRel
          (places.monomialsAt (moveAt i j x.content)).length
          (groupAt (residCarrier P B) (moveAt i j x.content)
            ++ groupAt B (moveAt i j x.content))
          (elim.matVec (units.matUnitAt (moveAt i j x.content)
            x.content i j)
            (elim.vecScale
              (elim.detL (elim.gramM
                (elim.collectOf x.coords.length
                  (groupAt B x.content))))
              x.coords)) := by
        refine elim.spanRel_congr _ _ _ _
          (poly.oneValue_symm
            (elim.matVec_vecScale_free _ _ _))
          (elim.spanRel_scale _ _ _ _ hQB
            (by rw [units.matVec_matUnitAt_length]) hs2)
          (by rw [units.matVec_matUnitAt_length])
      have hspan_img := elim.spanRel_congr _ _ _ _
        (poly.oneValue_symm hb1)
        (elim.spanRel_add _ _ _ _ hQB
          (by rw [units.matVec_matUnitAt_length])
          (by rw [units.matVec_matUnitAt_length])
          hsp1 hsp2)
        (by rw [units.matVec_matUnitAt_length])
      -- the tail's rows are perpendicular to the head's
      have hperpA : ∀ j2, j2 < (groupAt (residCarrier P B)
          (moveAt i j x.content)).length →
          ∀ k2, k2 < (groupAt B (moveAt i j x.content)).length →
          (elim.dotP
            (ground.getAt [] (groupAt (residCarrier P B)
              (moveAt i j x.content)) j2)
            (ground.getAt [] (groupAt B (moveAt i j x.content))
              k2)).oneValue BPair.unit := by
        intro j2 hj2 k2 hk2
        match groupAt_rows (fun v => v ∈ residCarrier P B)
            (residCarrier P B) (fun _ hv => hv)
            (moveAt i j x.content) j2 hj2 with
        | ⟨q, hqQ, hqc, hqrow⟩ =>
          match residCarrier_mem P B q hqQ with
          | ⟨_, p2, hp2P, hqp2⟩ =>
            have hp2c : p2.content = moveAt i j x.content := by
              rw [← show q.content = p2.content from
                by rw [hqp2]; rfl]
              exact hqc
            have hp2_sx : p2.coords.length
                = (places.monomialsAt
                    (moveAt i j x.content)).length := by
              rw [hszP p2 hp2P, hp2c]
            have hqlen2 : q.coords.length
                = (places.monomialsAt
                    (moveAt i j x.content)).length := by
              rw [hqp2]
              show (elim.residV p2.coords.length
                (elim.collectOf p2.coords.length
                  (groupAt B p2.content)) p2.coords).length = _
              rw [elim.length_residV _ _ p2.coords
                (elim.collect_rowsLen _ _
                  (by rw [hszP p2 hp2P]
                      exact rowsLen_groupAt p2.content B hszB))
                rfl]
              exact hp2_sx
            have hperp0 : ∀ k3, k3 < (elim.collectOf
                (places.monomialsAt
                  (moveAt i j x.content)).length
                (groupAt B (moveAt i j x.content))).length →
                (elim.dotP q.coords (ground.getAt []
                  (elim.collectOf
                    (places.monomialsAt
                      (moveAt i j x.content)).length
                    (groupAt B (moveAt i j x.content)))
                  k3)).oneValue BPair.unit := by
              intro k3 hk3
              rw [elim.dotP_comm, hqp2]
              show (elim.dotP (ground.getAt []
                  (elim.collectOf
                    (places.monomialsAt
                      (moveAt i j x.content)).length
                    (groupAt B (moveAt i j x.content))) k3)
                (elim.residV p2.coords.length
                  (elim.collectOf p2.coords.length
                    (groupAt B p2.content))
                  p2.coords)).oneValue BPair.unit
              rw [hp2_sx, hp2c]
              exact elim.resid_perp _ _ p2.coords
                (elim.collect_rowsLen _ _ hBrows') hp2_sx k3 hk3
            rw [hqrow]
            exact elim.perp_span _
              (elim.collectOf
                (places.monomialsAt (moveAt i j x.content)).length
                (groupAt B (moveAt i j x.content)))
              q.coords _
              (elim.collect_rowsLen _ _ hBrows') hqlen2 hperp0
              (elim.collect_span_row _ _ hBrows' k2 hk2)
      -- the split, and the settled read
      refine Or.inr ?_
      show elim.spanRel
        (elim.matVec (units.matUnitAt (moveAt i j x.content)
          x.content i j) (residAt B x).coords).length
        (groupAt (residCarrier P B) (moveAt i j x.content))
        (elim.matVec (units.matUnitAt (moveAt i j x.content)
          x.content i j) (residAt B x).coords)
      rw [units.matVec_matUnitAt_length]
      exact elim.span_perp_split _ _ _ _ hQrows hBrows'
        hperpB hperpA hspan_img

/-- The pick is a top: the height-maximal member reads its every
raising image at the unit tail.  A raising strictly raises the
height fold (`lowerspan.ht_moveAt_raise`), so an occupier of the
raised content sits above the pick — off the unit tail it would
break the pick's maximality (`pickTop_max`), leaving the raised
group's rows unit-tailed row by row (`groupAt_rows` at the
occupier, the `allU` read its Bool spelling).  The pair's closure
then settles the image: the unit-family disjunct reads the tail
outright and the span disjunct forces it at the unit-rowed group
(`elim.spanRel_unit_of_units`).  The carrier's off-unit read is
off this clause's path, its binder dropped at that derivation. -/
theorem pickTop_top (d : Nat) (P : List HVec)
    (hwid : ∀ x ∈ P, x.content.length = d)
    (hcl : ∀ x ∈ P, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt P (act i j x))
    (w : HVec) (hp : pickTop P = some w) :
    ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j w).coords := by
  have hwP := pickTop_mem P w hp
  intro j hj i hij
  have hi : i < d := Nat.lt_trans hij hj
  have hij' : ¬ i = j :=
    fun he => absurd hij (by rw [he]; exact Nat.lt_irrefl j)
  have hrows : ∀ k, k < (groupAt P (moveAt i j w.content)).length →
      poly.unitTail (ground.getAt ([] : List BPair)
        (groupAt P (moveAt i j w.content)) k) := by
    intro k hk
    match groupAt_rows (fun v => v ∈ P) P (fun _ hv => hv)
        (moveAt i j w.content) k hk with
    | ⟨x, hxP, hxc, hrow⟩ =>
      rw [hrow]
      match hb : allU x.coords with
      | true => exact unitTail_of_allU x.coords hb
      | false =>
        have hxoff : ¬ poly.unitTail x.coords := by
          intro hu
          rw [allU_of_unitTail x.coords hu] at hb
          exact Bool.noConfusion hb
        have hraise : lowerspan.ht w.content
            < lowerspan.ht (moveAt i j w.content) :=
          lowerspan.ht_moveAt_raise i j w.content hij
            (by rw [hwid w hwP]; exact hj)
        have hle := pickTop_max P w hp x hxP hxoff
        rw [hxc] at hle
        exact absurd (Nat.lt_of_lt_of_le hraise hle)
          (Nat.lt_irrefl _)
  match hcl w hwP i hi j hj hij' with
  | Or.inl hu => exact unitTail_of_allU _ hu
  | Or.inr hs =>
    exact elim.spanRel_unit_of_units _ _ _ hrows hs

/-- The descent's round split, iota-reduced. -/
private theorem exhaustGo_split (d fuel : Nat) (P : List HVec) :
    (pickTop P = none ∧ exhaustGo d (fuel + 1) P = [])
    ∨ ∃ w0, pickTop P = some w0
      ∧ exhaustGo d (fuel + 1) P
          = w0 :: exhaustGo d fuel
              (residCarrier P
                (blockOf d w0)) := by
  match hp : pickTop P with
  | none =>
    refine Or.inl ⟨rfl, ?_⟩
    show (match pickTop P with
      | none => []
      | some w =>
        w :: exhaustGo d fuel
          (residCarrier P
            (blockOf d w))) = []
    rw [hp]
  | some w0 =>
    refine Or.inr ⟨w0, rfl, ?_⟩
    show (match pickTop P with
      | none => []
      | some w =>
        w :: exhaustGo d fuel
          (residCarrier P
            (blockOf d w))) = _
    rw [hp]

/-- Every produced member is a top at the stated data: each
round's pick reads its raising images at the unit tail
(`pickTop_top`), and the residual carrier keeps the invariants —
the enumerations, the widths, the off-unit read, and the closure
(`residCarrier_closed`) — so the descent's rounds read the one
pack throughout. -/
theorem exhaustGo_top (d : Nat) : ∀ (fuel : Nat) (P : List HVec),
    (∀ x ∈ P, sized x) →
    (∀ x ∈ P, x.content.length = d) →
    (∀ x ∈ P, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt P (act i j x)) →
    ∀ w ∈ exhaustGo d fuel P,
      sized w ∧ w.content.length = d
        ∧ (¬ poly.unitTail w.coords)
        ∧ ∀ j, j < d → ∀ i, i < j →
            poly.unitTail (act i j w).coords
  | 0, _, _, _, _, _, hw => nomatch hw
  | fuel + 1, P, hsz, hwid, hcl, w, hw => by
    match exhaustGo_split d fuel P with
    | .inl ⟨_, hc⟩ =>
      rw [hc] at hw
      exact nomatch hw
    | .inr ⟨w0, hp, hc⟩ =>
      rw [hc] at hw
      have hw0P := pickTop_mem P w0 hp
      have htop0 := pickTop_top d P hwid hcl w0 hp
      match hscl : lowerspan.seed_closed d
          (lowerspan.ht w0.content) w0 (hsz w0 hw0P)
          (hwid w0 hw0P) (pickTop_off P w0 hp)
          (fun jr hjr => htop0 (jr + 1) hjr jr
            (Nat.lt_succ_self jr))
          (Nat.le_refl _) with
      | ⟨tailB, htlB, hszB', _, _, _, hsetB'⟩ =>
      have hszB : ∀ v ∈ blockOf d w0, sized v := by
        rw [blockOf_eq, htlB]
        exact hszB'
      have hsetB : ∀ x ∈ blockOf d w0, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
          settledAt (blockOf d w0) (act i j x) := by
        rw [blockOf_eq, htlB]
        exact hsetB'
      match w, hw with
      | _, List.Mem.head _ =>
        exact ⟨hsz w0 hw0P, hwid w0 hw0P, pickTop_off P w0 hp,
          htop0⟩
      | w', List.Mem.tail _ hwt =>
        exact exhaustGo_top d fuel _
          (residCarrier_sized P _ hsz hszB)
          (residCarrier_width d P _ hwid)
          (residCarrier_closed d P _ hsz hwid hcl
            hszB hsetB)
          w' hwt

/-- The exhaustion's members are tops at the stated data, the
descent at the carrier's own length — `lem:blockcount`(i)'s
producer read, the maximal-content top each round's pick. -/
theorem exhaust_top (d : Nat) (P : List HVec)
    (hsz : ∀ x ∈ P, sized x)
    (hwid : ∀ x ∈ P, x.content.length = d)
    (hcl : ∀ x ∈ P, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt P (act i j x)) :
    ∀ w ∈ exhaust d P,
      sized w ∧ w.content.length = d
        ∧ (¬ poly.unitTail w.coords)
        ∧ ∀ j, j < d → ∀ i, i < j →
            poly.unitTail (act i j w).coords :=
  exhaustGo_top d P.length P hsz hwid hcl

/-! The descent's completeness, `lem:blockcount`(i)'s orthogonal
sum's span half: every stated member sits inside the produced
blocks' joined span.  The per-member identity is the residual's
join read back (`elim.residV_expand`) at the block's collected
group — the combination inside the block's group, the residual
recursed at the carrier's descent — and each round strictly
shortens the carrier: the pick is a member of its own block, so
its residual reads the unit through the solve (`lem:lowerspan`'s
member-vector clause), the descent closing at the carrier's
length. -/

/-- The produced blocks' join: each top's own closure concatenated
in the descent's order, the orthogonal sum's stated list. -/
def blockJoin (d : Nat) (ws : List HVec) : List HVec :=
  ws.flatMap (blockOf d)

/-- The residual carrier sits at or below the stated carrier's
length, the filter's own read. -/
private theorem residCarrier_len_le : ∀ (P B : List HVec),
    (residCarrier P B).length ≤ P.length
  | [], _ => Nat.le_refl 0
  | v :: t, B => by
    match residCarrier_split v t B with
    | .inl ⟨_, hc⟩ =>
      rw [hc]
      exact Nat.le_succ_of_le (residCarrier_len_le t B)
    | .inr ⟨_, hc⟩ =>
      rw [hc]
      exact Nat.succ_le_succ (residCarrier_len_le t B)

/-- A member whose residual reads the unit family shortens the
carrier strictly, its own entry withdrawn at the filter. -/
private theorem residCarrier_len_lt :
    ∀ (P B : List HVec) (x : HVec), x ∈ P →
    allU (residAt B x).coords = true →
    (residCarrier P B).length < P.length
  | [], _, _, hx, _ => nomatch hx
  | v :: t, B, x, hx, hall => by
    match residCarrier_split v t B with
    | .inl ⟨_, hc⟩ =>
      rw [hc]
      exact Nat.lt_succ_of_le (residCarrier_len_le t B)
    | .inr ⟨hb, hc⟩ =>
      rw [hc]
      match x, hx, hall with
      | _, List.Mem.head _, hall' =>
        rw [hall'] at hb
        exact Bool.noConfusion hb
      | x', List.Mem.tail _ hxt, hall' =>
        exact Nat.succ_lt_succ
          (residCarrier_len_lt t B x' hxt hall')

/-- The pick's residual at its own block reads the unit family: a
member vector puts the residual inside the span, where its
self-pairing reads that unit (`lem:lowerspan`). -/
private theorem pick_resid_unit (d : Nat) (P : List HVec)
    (hsz : ∀ x ∈ P, sized x)
    (hwid : ∀ x ∈ P, x.content.length = d)
    (w0 : HVec) (hp : pickTop P = some w0) :
    allU (residAt
      (blockOf d w0)
      w0).coords = true := by
  have hw0P := pickTop_mem P w0 hp
  obtain ⟨hszB, _, _, _⟩ := seedSpan_sem d
    (lowerspan.ht w0.content) lowerspan.ht w0
    (lowerspan.ht_nomove d) (lowerspan.ht_drop d)
    (hsz w0 hw0P) (hwid w0 hw0P) (pickTop_off P w0 hp)
    (Nat.le_refl _)
  have hw0B : w0 ∈ blockOf d w0 := by
    match seedSpan_prov d (lowerspan.ht w0.content) w0 with
    | ⟨tail, htl, _⟩ =>
      rw [blockOf_eq, htl]
      exact List.Mem.head tail
  have hspan := settled_to_span
    (blockOf d w0) w0 hszB
    (hsz w0 hw0P) (member_settled _ hszB w0 hw0B)
  exact allU_of_unitTail _ hspan.2.2

/-- The produced members keep the carrier's enumerations, widths
and off-unit reads through the rounds, the pick's own reads with
the residual carrier's.  Kept beside `exhaustGo_top` with the
reason derived: the top theorem's closure binder is off this
clause's path, so it cannot serve the completeness tier, and
folding the two leaves two recursions either way. -/
private theorem exhaustGo_pack (d : Nat) :
    ∀ (fuel : Nat) (P : List HVec),
    (∀ x ∈ P, sized x) →
    (∀ x ∈ P, x.content.length = d) →
    ∀ w ∈ exhaustGo d fuel P,
      sized w ∧ w.content.length = d
        ∧ ¬ poly.unitTail w.coords
  | 0, _, _, _, _, hw => nomatch hw
  | fuel + 1, P, hsz, hwid, w, hw => by
    match exhaustGo_split d fuel P with
    | .inl ⟨_, hc⟩ =>
      rw [hc] at hw
      exact nomatch hw
    | .inr ⟨w0, hp, hc⟩ =>
      rw [hc] at hw
      have hw0P := pickTop_mem P w0 hp
      obtain ⟨hszB, _, _, _⟩ := seedSpan_sem d
        (lowerspan.ht w0.content) lowerspan.ht w0
        (lowerspan.ht_nomove d) (lowerspan.ht_drop d)
        (hsz w0 hw0P) (hwid w0 hw0P) (pickTop_off P w0 hp)
        (Nat.le_refl _)
      match w, hw with
      | _, List.Mem.head _ =>
        exact ⟨hsz w0 hw0P, hwid w0 hw0P, pickTop_off P w0 hp⟩
      | w', List.Mem.tail _ hwt =>
        exact exhaustGo_pack d fuel _
          (residCarrier_sized P _ hsz hszB)
          (residCarrier_width d P _ hwid)
          w' hwt

/-- The join's members read the stated enumerations, each block's
own sized read at its top's data — the joined image family's
per-member read (`memAll_flatMap_of`). -/
private theorem blockJoin_sized (d : Nat) (ws : List HVec)
    (hp : ∀ w ∈ ws, sized w ∧ w.content.length = d
      ∧ ¬ poly.unitTail w.coords) :
    ∀ x ∈ blockJoin d ws, sized x :=
  memAll_flatMap_of sized
    (fun w => sized w ∧ w.content.length = d
      ∧ ¬ poly.unitTail w.coords)
    (fun w => blockOf d w)
    (fun w hw => by
      obtain ⟨hszB, _, _, _⟩ := seedSpan_sem d
        (lowerspan.ht w.content) lowerspan.ht w
        (lowerspan.ht_nomove d) (lowerspan.ht_drop d)
        hw.1 hw.2.1 hw.2.2 (Nat.le_refl _)
      exact hszB)
    ws hp

/-- A group's rows read a stated per-member span at the group's own
content: each row is a member's coordinate family at that content
(`groupAt_rows`), the member's width the enumeration's. -/
theorem group_span_rows (R S : List HVec) (mu : List Nat)
    (hszR : ∀ x ∈ R, sized x)
    (hspan : ∀ x ∈ R, elim.spanRel x.coords.length
      (groupAt S x.content) x.coords) :
    ∀ k, k < (groupAt R mu).length →
      elim.spanRel (places.monomialsAt mu).length (groupAt S mu)
        (ground.getAt ([] : List BPair) (groupAt R mu) k) := by
  intro k hk
  match groupAt_rows (fun v => v ∈ R) R (fun _ hv => hv)
      mu k hk with
  | ⟨y, hyR, hyc, hyrow⟩ =>
    rw [hyrow]
    have hy := hspan y hyR
    have hsy : y.coords.length
        = (places.monomialsAt y.content).length := hszR y hyR
    rw [hsy, hyc] at hy
    exact hy

/-- Every stated member sits inside the round's joined span: the
member's residual at the block either reads the unit tail — the
member already inside the block's group span — or joins the
residual carrier as its own row, and the residual's join read back
(`elim.residV_expand`) puts the member in the joined span, the
determinant withdrawn at the collection's independence. -/
private theorem carrier_span_split (P B : List HVec)
    (hszP : ∀ x ∈ P, sized x) (hszB : ∀ x ∈ B, sized x) :
    ∀ x ∈ P,
      elim.spanRel x.coords.length
        (groupAt (B ++ residCarrier P B) x.content) x.coords := by
  intro x hx
  have hQsz := residCarrier_sized P B hszP hszB
  have hsx : x.coords.length
      = (places.monomialsAt x.content).length := hszP x hx
  have hGrows : elim.rowsLen x.coords.length
      (groupAt B x.content) := by
    rw [hsx]
    exact rowsLen_groupAt x.content B hszB
  have hRrows : elim.rowsLen x.coords.length
      (groupAt (residCarrier P B) x.content) := by
    rw [hsx]
    exact rowsLen_groupAt x.content (residCarrier P B) hQsz
  have hJrows := elim.rowsLen_append x.coords.length hGrows hRrows
  rw [groupAt_append]
  match hb : allU (residAt B x).coords with
  | true =>
    exact elim.spanRel_mono x.coords.length _ _ x.coords
      hGrows hRrows ⟨hGrows, rfl, unitTail_of_allU _ hb⟩
  | false =>
    have hCrows := elim.collect_rowsLen x.coords.length _ hGrows
    have hreq : (residAt B x).coords
        = elim.residV x.coords.length
            (elim.collectOf x.coords.length
              (groupAt B x.content)) x.coords := rfl
    have hrvlen : (residAt B x).coords.length
        = x.coords.length := by
      rw [hreq]
      exact elim.length_residV _ _ x.coords hCrows rfl
    have hmem := residCarrier_mem_intro P B x hx hb
    have hself := settled_to_span (residCarrier P B) (residAt B x)
      hQsz (hQsz (residAt B x) hmem)
      (member_settled (residCarrier P B) hQsz (residAt B x) hmem)
    have hIH' : elim.spanRel x.coords.length
        (groupAt (residCarrier P B) x.content)
        (elim.residV x.coords.length
          (elim.collectOf x.coords.length (groupAt B x.content))
          x.coords) := by
      rw [← hreq]
      exact spanRel_cast _ _ _ _ hself hrvlen
    have hresid := elim.spanRel_mono_left x.coords.length
      _ _ _ hGrows hRrows hIH'
    have hcombo : elim.spanRel x.coords.length
        (groupAt B x.content
          ++ groupAt (residCarrier P B) x.content)
        (elim.combo x.coords.length
          (elim.adjP
            (elim.gramM (elim.collectOf x.coords.length
              (groupAt B x.content)))
            ((elim.collectOf x.coords.length
              (groupAt B x.content)).map
              (fun r => elim.dotP r x.coords)))
          (elim.collectOf x.coords.length
            (groupAt B x.content))) := by
      refine elim.spanRel_combo _ _ hJrows _ _ hCrows ?_
      intro k hk
      exact elim.spanRel_mono _ _ _ _ hGrows hRrows
        (elim.collect_row_span _ _ hGrows k hk)
    have hadd := elim.spanRel_add x.coords.length _ _ _ hJrows
      (elim.length_residV _ _ x.coords hCrows rfl)
      (elim.length_combo _ _ _ hCrows) hresid hcombo
    have hexp := elim.residV_expand x.coords.length
      (elim.collectOf x.coords.length (groupAt B x.content))
      x.coords hCrows rfl
    have hcongr := elim.spanRel_congr x.coords.length _ _ _
      (poly.oneValue_symm hexp) hadd
      (by rw [elim.length_vecScale])
    exact elim.spanRel_unscale x.coords.length _ _ x.coords
      (elim.indep_det _ _ (elim.collect_indep _ _ hGrows))
      hcongr

/-- The descent's completeness at the stated fuel: every carrier
member sits inside the produced blocks' joined span.  The
per-member identity is the residual's join read back
(`elim.residV_expand`) at the block's collected group — the
combination inside the block's group (`elim.collect_row_span`),
the residual the carrier's own member recursed — and the round
strictly shortens the carrier at the pick's unit residual
(`lem:lowerspan`'s member-vector clause), so the stated fuel
suffices.  The fuel binder is load-bearing, its refusal committed;
the enumeration and width binders are `con:places`' member
definition, the stated data's frame; the producer's off-unit and
closure binders are the orthogonality half's, not this clause's —
the positive pins at the unclosed and unit-bearing carriers
committed beside the batteries. -/
theorem exhaustGo_span (d : Nat) :
    ∀ (fuel : Nat) (P : List HVec),
    (∀ x ∈ P, sized x) →
    (∀ x ∈ P, x.content.length = d) →
    P.length ≤ fuel →
    ∀ x ∈ P,
      elim.spanRel x.coords.length
        (groupAt (blockJoin d (exhaustGo d fuel P)) x.content)
        x.coords
  | 0, [], _, _, _, _, hx => nomatch hx
  | 0, _ :: t, _, _, hfuel, _, _ =>
    absurd hfuel (Nat.not_succ_le_zero t.length)
  | fuel + 1, P, hsz, hwid, hfuel, x, hx => by
    match exhaustGo_split d fuel P with
    | .inl ⟨hpn, hc⟩ =>
      rw [hc]
      exact elim.spanRel_null x.coords.length _ x.coords
        (unitTail_of_allU x.coords (pickTop_none P hpn x hx))
        True.intro rfl
    | .inr ⟨w0, hp, hc⟩ =>
      rw [hc]
      have hw0P := pickTop_mem P w0 hp
      obtain ⟨hszB, _, _, _⟩ := seedSpan_sem d
        (lowerspan.ht w0.content) lowerspan.ht w0
        (lowerspan.ht_nomove d) (lowerspan.ht_drop d)
        (hsz w0 hw0P) (hwid w0 hw0P) (pickTop_off P w0 hp)
        (Nat.le_refl _)
      have hQsz := residCarrier_sized P (blockOf d w0) hsz hszB
      have hQwid := residCarrier_width d P (blockOf d w0) hwid
      have hQfuel : (residCarrier P (blockOf d w0)).length ≤ fuel :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le
          (residCarrier_len_lt P _ w0 hw0P
            (pick_resid_unit d P hsz hwid w0 hp))
          hfuel)
      have hRestSized : ∀ z ∈ blockJoin d
          (exhaustGo d fuel (residCarrier P (blockOf d w0))),
          sized z :=
        blockJoin_sized d _ (exhaustGo_pack d fuel _ hQsz hQwid)
      have hJszL : ∀ z ∈ blockOf d w0
          ++ blockJoin d (exhaustGo d fuel
            (residCarrier P (blockOf d w0))), sized z := by
        intro z hz
        match ground.mem_append_of _ _ hz with
        | Or.inl h => exact hszB z h
        | Or.inr h => exact hRestSized z h
      have hJszR : ∀ z ∈ blockOf d w0
          ++ residCarrier P (blockOf d w0), sized z := by
        intro z hz
        match ground.mem_append_of _ _ hz with
        | Or.inl h => exact hszB z h
        | Or.inr h => exact hQsz z h
      have hmem : ∀ y ∈ blockOf d w0
          ++ residCarrier P (blockOf d w0),
          elim.spanRel y.coords.length
            (groupAt (blockOf d w0 ++ blockJoin d (exhaustGo d fuel
              (residCarrier P (blockOf d w0)))) y.content)
            y.coords := by
        intro y hy
        have hyBrows : elim.rowsLen y.coords.length
            (groupAt (blockOf d w0) y.content) := by
          rw [hJszR y hy]
          exact rowsLen_groupAt y.content _ hszB
        have hyRrows : elim.rowsLen y.coords.length
            (groupAt (blockJoin d (exhaustGo d fuel
              (residCarrier P (blockOf d w0)))) y.content) := by
          rw [hJszR y hy]
          exact rowsLen_groupAt y.content _ hRestSized
        rw [groupAt_append]
        match ground.mem_append_of _ _ hy with
        | Or.inl h =>
          have hset := settled_to_span (blockOf d w0) y hszB
            (hszB y h) (member_settled (blockOf d w0) hszB y h)
          exact elim.spanRel_mono y.coords.length _ _ y.coords
            hyBrows hyRrows hset
        | Or.inr h =>
          exact elim.spanRel_mono_left y.coords.length _ _ _
            hyBrows hyRrows
            (exhaustGo_span d fuel _ hQsz hQwid hQfuel y h)
      have hsx : x.coords.length
          = (places.monomialsAt x.content).length := hsz x hx
      have hGrows : elim.rowsLen x.coords.length
          (groupAt (blockOf d w0
            ++ residCarrier P (blockOf d w0)) x.content) := by
        rw [hsx]
        exact rowsLen_groupAt x.content _ hJszR
      have hMrows : elim.rowsLen x.coords.length
          (groupAt (blockOf d w0
            ++ blockJoin d (exhaustGo d fuel
              (residCarrier P (blockOf d w0)))) x.content) := by
        rw [hsx]
        exact rowsLen_groupAt x.content _ hJszL
      have htrans := group_span_rows
        (blockOf d w0 ++ residCarrier P (blockOf d w0))
        (blockOf d w0 ++ blockJoin d (exhaustGo d fuel
          (residCarrier P (blockOf d w0))))
        x.content hJszR hmem
      show elim.spanRel x.coords.length
        (groupAt (blockOf d w0
          ++ blockJoin d (exhaustGo d fuel (residCarrier P
            (blockOf d w0))))
          x.content)
        x.coords
      refine elim.spanRel_trans x.coords.length _ _ x.coords
        hGrows hMrows ?_
        (carrier_span_split P (blockOf d w0) hsz hszB x hx)
      intro k hk
      rw [hsx]
      exact htrans k hk

/-- The exhaustion's completeness at the carrier's own length:
every stated member sits inside the produced blocks' joined span,
`lem:blockcount`(i)'s orthogonal sum's span half. -/
theorem exhaust_span (d : Nat) (P : List HVec)
    (hsz : ∀ x ∈ P, sized x)
    (hwid : ∀ x ∈ P, x.content.length = d) :
    ∀ x ∈ P,
      elim.spanRel x.coords.length
        (groupAt (blockJoin d (exhaust d P)) x.content)
        x.coords :=
  exhaustGo_span d P.length P hsz hwid (Nat.le_refl _)

/-- The raising kernels split at the orthogonal split,
`lem:blockcount`(ii)'s first clause: a top of the joined span
reads its two parts tops — the residual at the head's collected
group inside the tail's span alone (`elim.span_perp_split` at the
commuted join) with the projection combination inside the head's,
and each part's raising image sits in its own side's moved span
(`act_transport`), the two images perpendicular at the stated
groups (`elim.perp_span`), so the summed image's unit tail
withdraws each at the positive pairing
(`elim.vecAdd_perp_null`).  The closure binders enter at the
raising half alone, and the perpendicularity binders are the
split's own stated data; the enumeration binders are `con:places`'
member definition. -/
theorem top_split (d : Nat) (mu : List Nat) (A B : List HVec)
    (hszA : ∀ x ∈ A, sized x) (hszB : ∀ x ∈ B, sized x)
    (hclA : ∀ x ∈ A, ∀ j, j < d → ∀ i, i < j →
      settledAt A (act i j x))
    (hclB : ∀ x ∈ B, ∀ j, j < d → ∀ i, i < j →
      settledAt B (act i j x))
    (hperpMu : ∀ k, k < (groupAt A mu).length →
      ∀ l, l < (groupAt B mu).length →
      (elim.dotP (ground.getAt [] (groupAt A mu) k)
        (ground.getAt [] (groupAt B mu) l)).oneValue BPair.unit)
    (hperpUp : ∀ j, j < d → ∀ i, i < j →
      ∀ k, k < (groupAt A (moveAt i j mu)).length →
      ∀ l, l < (groupAt B (moveAt i j mu)).length →
      (elim.dotP (ground.getAt [] (groupAt A (moveAt i j mu)) k)
        (ground.getAt []
          (groupAt B (moveAt i j mu)) l)).oneValue BPair.unit)
    (v : List BPair)
    (hv : v.length = (places.monomialsAt mu).length)
    (hsp : elim.spanRel (places.monomialsAt mu).length
      (groupAt (A ++ B) mu) v)
    (htop : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (elim.matVec
        (units.matUnitAt (moveAt i j mu) mu i j) v)) :
    elim.spanRel (places.monomialsAt mu).length (groupAt B mu)
        (elim.residV (places.monomialsAt mu).length
          (elim.collectOf (places.monomialsAt mu).length
            (groupAt A mu)) v)
      ∧ (∀ j, j < d → ∀ i, i < j →
          poly.unitTail (elim.matVec
            (units.matUnitAt (moveAt i j mu) mu i j)
            (elim.residV (places.monomialsAt mu).length
              (elim.collectOf (places.monomialsAt mu).length
                (groupAt A mu)) v)))
      ∧ (∀ j, j < d → ∀ i, i < j →
          poly.unitTail (elim.matVec
            (units.matUnitAt (moveAt i j mu) mu i j)
            (elim.combo (places.monomialsAt mu).length
              (elim.adjP (elim.gramM
                (elim.collectOf (places.monomialsAt mu).length
                  (groupAt A mu)))
                ((elim.collectOf (places.monomialsAt mu).length
                  (groupAt A mu)).map
                  (fun r => elim.dotP r v)))
              (elim.collectOf (places.monomialsAt mu).length
                (groupAt A mu)))))
      ∧ elim.spanRel (places.monomialsAt mu).length (groupAt A mu)
          (elim.combo (places.monomialsAt mu).length
            (elim.adjP (elim.gramM
              (elim.collectOf (places.monomialsAt mu).length
                (groupAt A mu)))
              ((elim.collectOf (places.monomialsAt mu).length
                (groupAt A mu)).map
                (fun r => elim.dotP r v)))
            (elim.collectOf (places.monomialsAt mu).length
              (groupAt A mu))) := by
  have hArows : elim.rowsLen (places.monomialsAt mu).length
      (groupAt A mu) := rowsLen_groupAt mu A hszA
  have hBrows : elim.rowsLen (places.monomialsAt mu).length
      (groupAt B mu) := rowsLen_groupAt mu B hszB
  have hCrows := elim.collect_rowsLen
    (places.monomialsAt mu).length (groupAt A mu) hArows
  have hABrows := elim.rowsLen_append
    (places.monomialsAt mu).length hArows hBrows
  have hrlen : (elim.residV (places.monomialsAt mu).length
      (elim.collectOf (places.monomialsAt mu).length
        (groupAt A mu)) v).length
      = (places.monomialsAt mu).length :=
    elim.length_residV _ _ v hCrows hv
  have hclen : (elim.combo (places.monomialsAt mu).length
      (elim.adjP (elim.gramM
        (elim.collectOf (places.monomialsAt mu).length
          (groupAt A mu)))
        ((elim.collectOf (places.monomialsAt mu).length
          (groupAt A mu)).map (fun r => elim.dotP r v)))
      (elim.collectOf (places.monomialsAt mu).length
        (groupAt A mu))).length
      = (places.monomialsAt mu).length :=
    elim.length_combo _ _ _ hCrows
  have hsp' : elim.spanRel (places.monomialsAt mu).length
      (groupAt A mu ++ groupAt B mu) v := by
    rw [← groupAt_append]
    exact hsp
  have hcomboA : elim.spanRel (places.monomialsAt mu).length
      (groupAt A mu)
      (elim.combo (places.monomialsAt mu).length
        (elim.adjP (elim.gramM
          (elim.collectOf (places.monomialsAt mu).length
            (groupAt A mu)))
          ((elim.collectOf (places.monomialsAt mu).length
            (groupAt A mu)).map (fun r => elim.dotP r v)))
        (elim.collectOf (places.monomialsAt mu).length
          (groupAt A mu))) :=
    elim.spanRel_combo _ _ hArows _ _ hCrows
      (fun k hk => elim.collect_row_span _ _ hArows k hk)
  have hresidAB : elim.spanRel (places.monomialsAt mu).length
      (groupAt A mu ++ groupAt B mu)
      (elim.residV (places.monomialsAt mu).length
        (elim.collectOf (places.monomialsAt mu).length
          (groupAt A mu)) v) :=
    elim.spanRel_residV _ _ _ v hCrows hv hABrows
      (fun k hk => elim.spanRel_mono _ _ _ _ hArows hBrows
        (elim.collect_row_span _ _ hArows k hk))
      hsp'
  have hresidBA := elim.spanRel_append_comm
    (places.monomialsAt mu).length (groupAt A mu) (groupAt B mu)
    _ hArows hBrows hresidAB
  have hperpResidA : ∀ k, k < (groupAt A mu).length →
      (elim.dotP (elim.residV (places.monomialsAt mu).length
        (elim.collectOf (places.monomialsAt mu).length
          (groupAt A mu)) v)
        (ground.getAt [] (groupAt A mu) k)).oneValue
        BPair.unit := by
    intro k hk
    refine elim.perp_span (places.monomialsAt mu).length
      (elim.collectOf (places.monomialsAt mu).length
        (groupAt A mu)) _ _ hCrows hrlen ?_
      (elim.collect_span_row _ _ hArows k hk)
    intro k2 hk2
    rw [elim.dotP_comm]
    exact elim.resid_perp _ _ v hCrows hv k2 hk2
  have hc1 : elim.spanRel (places.monomialsAt mu).length
      (groupAt B mu)
      (elim.residV (places.monomialsAt mu).length
        (elim.collectOf (places.monomialsAt mu).length
          (groupAt A mu)) v) := by
    refine elim.span_perp_split _ _ _ _ hBrows hArows
      hperpResidA ?_ hresidBA
    intro j2 hj2 k2 hk2
    rw [elim.dotP_comm]
    exact hperpMu k2 hk2 j2 hj2
  have hboth : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (elim.matVec
        (units.matUnitAt (moveAt i j mu) mu i j)
        (elim.residV (places.monomialsAt mu).length
          (elim.collectOf (places.monomialsAt mu).length
            (groupAt A mu)) v))
      ∧ poly.unitTail (elim.matVec
        (units.matUnitAt (moveAt i j mu) mu i j)
        (elim.combo (places.monomialsAt mu).length
          (elim.adjP (elim.gramM
            (elim.collectOf (places.monomialsAt mu).length
              (groupAt A mu)))
            ((elim.collectOf (places.monomialsAt mu).length
              (groupAt A mu)).map (fun r => elim.dotP r v)))
          (elim.collectOf (places.monomialsAt mu).length
            (groupAt A mu)))) := by
    intro j hj i hij
    have hT : elim.rowsLen (places.monomialsAt mu).length
        (units.matUnitAt (moveAt i j mu) mu i j) :=
      units.rowsLen_matUnitAt _ _ i j
    have hAmoved : elim.rowsLen
        (places.monomialsAt (moveAt i j mu)).length
        (groupAt A (moveAt i j mu)) :=
      rowsLen_groupAt (moveAt i j mu) A hszA
    have hBmoved : elim.rowsLen
        (places.monomialsAt (moveAt i j mu)).length
        (groupAt B (moveAt i j mu)) :=
      rowsLen_groupAt (moveAt i j mu) B hszB
    have hRspan := act_transport B i j hszB
      (fun x hx => hclB x hx j hj i hij) mu _ hrlen hc1
    have hCspan := act_transport A i j hszA
      (fun x hx => hclA x hx j hj i hij) mu _ hclen hcomboA
    have himgCperpB : ∀ l,
        l < (groupAt B (moveAt i j mu)).length →
        (elim.dotP (ground.getAt []
          (groupAt B (moveAt i j mu)) l)
          (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
            (elim.combo (places.monomialsAt mu).length
              (elim.adjP (elim.gramM
                (elim.collectOf (places.monomialsAt mu).length
                  (groupAt A mu)))
                ((elim.collectOf (places.monomialsAt mu).length
                  (groupAt A mu)).map
                  (fun r => elim.dotP r v)))
              (elim.collectOf (places.monomialsAt mu).length
                (groupAt A mu))))).oneValue BPair.unit := by
      intro l hl
      refine elim.perp_span
        (places.monomialsAt (moveAt i j mu)).length
        (groupAt A (moveAt i j mu)) _ _ hAmoved
        (elim.rowsLen_getAt _ l hBmoved hl) ?_ hCspan
      intro k hk
      rw [elim.dotP_comm]
      exact hperpUp j hj i hij k hk l hl
    have hRC : (elim.dotP
        (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
          (elim.combo (places.monomialsAt mu).length
            (elim.adjP (elim.gramM
              (elim.collectOf (places.monomialsAt mu).length
                (groupAt A mu)))
              ((elim.collectOf (places.monomialsAt mu).length
                (groupAt A mu)).map (fun r => elim.dotP r v)))
            (elim.collectOf (places.monomialsAt mu).length
              (groupAt A mu))))
        (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
          (elim.residV (places.monomialsAt mu).length
            (elim.collectOf (places.monomialsAt mu).length
              (groupAt A mu)) v))).oneValue BPair.unit := by
      refine elim.perp_span
        (places.monomialsAt (moveAt i j mu)).length
        (groupAt B (moveAt i j mu)) _ _ hBmoved
        (by rw [units.matVec_matUnitAt_length]) ?_ hRspan
      intro l hl
      rw [elim.dotP_comm]
      exact himgCperpB l hl
    have hs1 := elim.matVec_vecAdd
      (units.matUnitAt (moveAt i j mu) mu i j)
      (places.monomialsAt mu).length hT _ _ hrlen hclen
    have hs2 := elim.matVec_congr
      (units.matUnitAt (moveAt i j mu) mu i j) _ _
      (poly.oneValue_symm (elim.residV_expand
        (places.monomialsAt mu).length
        (elim.collectOf (places.monomialsAt mu).length
          (groupAt A mu)) v hCrows hv))
    have hs3 := elim.matVec_vecScale_free (units.matUnitAt (moveAt i j mu) mu i j) (elim.detL (elim.gramM
        (elim.collectOf (places.monomialsAt mu).length
          (groupAt A mu)))) v
    have hsum : poly.unitTail (elim.vecAdd
        (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
          (elim.residV (places.monomialsAt mu).length
            (elim.collectOf (places.monomialsAt mu).length
              (groupAt A mu)) v))
        (elim.matVec (units.matUnitAt (moveAt i j mu) mu i j)
          (elim.combo (places.monomialsAt mu).length
            (elim.adjP (elim.gramM
              (elim.collectOf (places.monomialsAt mu).length
                (groupAt A mu)))
              ((elim.collectOf (places.monomialsAt mu).length
                (groupAt A mu)).map (fun r => elim.dotP r v)))
            (elim.collectOf (places.monomialsAt mu).length
              (groupAt A mu))))) :=
      poly.oneValue_unitTail (poly.oneValue_symm hs1)
        (poly.oneValue_unitTail (poly.oneValue_trans hs2 hs3)
          (elim.unitTail_vecScale _ _ (htop j hj i hij)))
    have hw := elim.vecAdd_perp_null _ _
      (by rw [units.matVec_matUnitAt_length,
        units.matVec_matUnitAt_length])
      hsum
      (by rw [elim.dotP_comm]; exact hRC)
    exact hw
  exact ⟨hc1,
    fun j hj i hij => (hboth j hj i hij).1,
    fun j hj i hij => (hboth j hj i hij).2,
    hcomboA⟩

/-! The count's additivity over the split, `lem:blockcount`(ii)'s
second clause: the two sides' cross data join at the collected
bases, the joined kernel's coefficients split at the seam, and the
counts add. -/

/-- The joined cross datum's kernel read splits at the seam: the
two sides' coefficient combinations sit in their own groups' spans,
their occupied adjacent raising images sit in the moved groups'
(`act_transport`) and are perpendicular there (`elim.perp_span`
twice at the stated split), so the summed image's unit tail
withdraws the first side's alone (`elim.vecAdd_perp_null`) and the
stacked read reassembles it (`units.stackedRaise_of`) —
`elim.kernelDim_rowJoin`'s hypothesis at the two cross data. -/
private theorem cross_split (mu : List Nat)
    (A B : List HVec)
    (hszA : ∀ x ∈ A, sized x) (hszB : ∀ x ∈ B, sized x)
    (hclA : ∀ x ∈ A, ∀ i, i + 1 < mu.length →
      settledAt A (act i (i + 1) x))
    (hclB : ∀ x ∈ B, ∀ i, i + 1 < mu.length →
      settledAt B (act i (i + 1) x))
    (hperpUp : ∀ i, i + 1 < mu.length →
      ∀ k, k < (groupAt A (moveAt i (i + 1) mu)).length →
      ∀ l, l < (groupAt B (moveAt i (i + 1) mu)).length →
      (elim.dotP
        (ground.getAt [] (groupAt A (moveAt i (i + 1) mu)) k)
        (ground.getAt []
          (groupAt B (moveAt i (i + 1) mu)) l)).oneValue
        BPair.unit) :
    ∀ v w : List BPair,
      v.length = (elim.collectOf (places.monomialsAt mu).length
        (groupAt A mu)).length →
      w.length = (elim.collectOf (places.monomialsAt mu).length
        (groupAt B mu)).length →
      poly.unitTail (elim.matVec
        (elim.rowJoin
          (elim.crossM (units.stackedRaise mu)
            (elim.collectOf (places.monomialsAt mu).length
              (groupAt A mu)))
          (elim.crossM (units.stackedRaise mu)
            (elim.collectOf (places.monomialsAt mu).length
              (groupAt B mu)))) (v ++ w)) →
      poly.unitTail (elim.matVec
        (elim.crossM (units.stackedRaise mu)
          (elim.collectOf (places.monomialsAt mu).length
            (groupAt A mu))) v) := by
  intro v w hv hw hjoin
  have hArows : elim.rowsLen (places.monomialsAt mu).length
      (groupAt A mu) := rowsLen_groupAt mu A hszA
  have hBrows : elim.rowsLen (places.monomialsAt mu).length
      (groupAt B mu) := rowsLen_groupAt mu B hszB
  have hCA := elim.collect_rowsLen (places.monomialsAt mu).length
    (groupAt A mu) hArows
  have hCB := elim.collect_rowsLen (places.monomialsAt mu).length
    (groupAt B mu) hBrows
  have hR := units.rowsLen_stackedRaise mu
  rw [← elim.crossM_append] at hjoin
  have h1 := poly.unitTail_oneValue_right hjoin
    (elim.matVec_crossM (places.monomialsAt mu).length
      (units.stackedRaise mu) _ (v ++ w) hR
      (elim.rowsLen_append (places.monomialsAt mu).length hCA hCB))
  have hsum := poly.unitTail_oneValue_right h1
    (elim.matVec_congr (units.stackedRaise mu) _ _
      (elim.combo_append (places.monomialsAt mu).length v _ w _
        hv hCA hCB))
  have hxA : (elim.combo (places.monomialsAt mu).length v
      (elim.collectOf (places.monomialsAt mu).length
        (groupAt A mu))).length = (places.monomialsAt mu).length :=
    elim.length_combo _ v _ hCA
  have hxB : (elim.combo (places.monomialsAt mu).length w
      (elim.collectOf (places.monomialsAt mu).length
        (groupAt B mu))).length = (places.monomialsAt mu).length :=
    elim.length_combo _ w _ hCB
  have hspA : elim.spanRel (places.monomialsAt mu).length
      (groupAt A mu)
      (elim.combo (places.monomialsAt mu).length v
        (elim.collectOf (places.monomialsAt mu).length
          (groupAt A mu))) :=
    elim.spanRel_combo _ _ hArows _ v hCA
      (fun k hk => elim.collect_row_span _ _ hArows k hk)
  have hspB : elim.spanRel (places.monomialsAt mu).length
      (groupAt B mu)
      (elim.combo (places.monomialsAt mu).length w
        (elim.collectOf (places.monomialsAt mu).length
          (groupAt B mu))) :=
    elim.spanRel_combo _ _ hBrows _ w hCB
      (fun k hk => elim.collect_row_span _ _ hBrows k hk)
  refine poly.oneValue_unitTail
    (elim.matVec_crossM (places.monomialsAt mu).length
      (units.stackedRaise mu) _ v hR hCA) ?_
  refine units.stackedRaise_of mu _ ?_
  intro i hi hocc
  rw [← moveAt_moveUp i mu]
  have hT : elim.rowsLen (places.monomialsAt mu).length
      (units.matUnitAt (moveAt i (i + 1) mu) mu i (i + 1)) :=
    units.rowsLen_matUnitAt _ _ i (i + 1)
  have hAmoved : elim.rowsLen
      (places.monomialsAt (moveAt i (i + 1) mu)).length
      (groupAt A (moveAt i (i + 1) mu)) :=
    rowsLen_groupAt (moveAt i (i + 1) mu) A hszA
  have hBmoved : elim.rowsLen
      (places.monomialsAt (moveAt i (i + 1) mu)).length
      (groupAt B (moveAt i (i + 1) mu)) :=
    rowsLen_groupAt (moveAt i (i + 1) mu) B hszB
  have hAspan := act_transport A i (i + 1) hszA
    (fun x hx => hclA x hx i hi) mu _ hxA hspA
  have hBspan := act_transport B i (i + 1) hszB
    (fun x hx => hclB x hx i hi) mu _ hxB hspB
  have himgAperpB : ∀ l,
      l < (groupAt B (moveAt i (i + 1) mu)).length →
      (elim.dotP
        (ground.getAt [] (groupAt B (moveAt i (i + 1) mu)) l)
        (elim.matVec
          (units.matUnitAt (moveAt i (i + 1) mu) mu i (i + 1))
          (elim.combo (places.monomialsAt mu).length v
            (elim.collectOf (places.monomialsAt mu).length
              (groupAt A mu))))).oneValue BPair.unit := by
    intro l hl
    refine elim.perp_span
      (places.monomialsAt (moveAt i (i + 1) mu)).length
      (groupAt A (moveAt i (i + 1) mu)) _ _ hAmoved
      (elim.rowsLen_getAt _ l hBmoved hl) ?_ hAspan
    intro k hk
    rw [elim.dotP_comm]
    exact hperpUp i hi k hk l hl
  have hperpImg : (elim.dotP
      (elim.matVec
        (units.matUnitAt (moveAt i (i + 1) mu) mu i (i + 1))
        (elim.combo (places.monomialsAt mu).length v
          (elim.collectOf (places.monomialsAt mu).length
            (groupAt A mu))))
      (elim.matVec
        (units.matUnitAt (moveAt i (i + 1) mu) mu i (i + 1))
        (elim.combo (places.monomialsAt mu).length w
          (elim.collectOf (places.monomialsAt mu).length
            (groupAt B mu))))).oneValue BPair.unit := by
    refine elim.perp_span
      (places.monomialsAt (moveAt i (i + 1) mu)).length
      (groupAt B (moveAt i (i + 1) mu)) _ _ hBmoved
      (by rw [units.matVec_matUnitAt_length]) ?_ hBspan
    intro l hl
    rw [elim.dotP_comm]
    exact himgAperpB l hl
  have hst := units.stackedRaise_to mu _ hsum i hi hocc
  rw [← moveAt_moveUp i mu] at hst
  have hsplit := poly.unitTail_oneValue_right hst
    (elim.matVec_vecAdd
      (units.matUnitAt (moveAt i (i + 1) mu) mu i (i + 1))
      (places.monomialsAt mu).length hT _ _ hxA hxB)
  exact (elim.vecAdd_perp_null _ _
    (by rw [units.matVec_matUnitAt_length,
      units.matVec_matUnitAt_length]) hsplit hperpImg).1

/-- The count adds over the split (`lem:blockcount`(ii)): the two
sides' kernel lists join to an independent spanning list of the
sum's kernel at the joined collected basis, the kernel dimensions
add (`elim.kernelDim_rowJoin`), and the counts read the graded
dimensions at the bases' one count (`elim.kernelDim_congr`,
`lem:lowerspan`'s two-list clause).  The binders: the enumeration
shapes are `con:places`' member-definition frame; `hclA`/`hclB`
are the closure's stated data at the adjacent moves
(`lem:lowerspan`: the raising kernel is the adjacent stack's);
`hperpMu`/`hperpUp` are the split's stated perpendicularity at
the content and its adjacent moves (`lem:blockcount`(ii)'s
orthogonal sum). -/
theorem countAt_append (mu : List Nat) (A B : List HVec)
    (hszA : ∀ x ∈ A, sized x) (hszB : ∀ x ∈ B, sized x)
    (hclA : ∀ x ∈ A, ∀ i, i + 1 < mu.length →
      settledAt A (act i (i + 1) x))
    (hclB : ∀ x ∈ B, ∀ i, i + 1 < mu.length →
      settledAt B (act i (i + 1) x))
    (hperpMu : ∀ k, k < (groupAt A mu).length →
      ∀ l, l < (groupAt B mu).length →
      (elim.dotP (ground.getAt [] (groupAt A mu) k)
        (ground.getAt [] (groupAt B mu) l)).oneValue BPair.unit)
    (hperpUp : ∀ i, i + 1 < mu.length →
      ∀ k, k < (groupAt A (moveAt i (i + 1) mu)).length →
      ∀ l, l < (groupAt B (moveAt i (i + 1) mu)).length →
      (elim.dotP
        (ground.getAt [] (groupAt A (moveAt i (i + 1) mu)) k)
        (ground.getAt []
          (groupAt B (moveAt i (i + 1) mu)) l)).oneValue
        BPair.unit) :
    countAt (A ++ B) mu = countAt A mu + countAt B mu := by
  have hszAB : ∀ x ∈ A ++ B, sized x := by
    intro x hx
    match ground.mem_append_of _ _ hx with
    | Or.inl h => exact hszA x h
    | Or.inr h => exact hszB x h
  have hArows : elim.rowsLen (places.monomialsAt mu).length
      (groupAt A mu) := rowsLen_groupAt mu A hszA
  have hBrows : elim.rowsLen (places.monomialsAt mu).length
      (groupAt B mu) := rowsLen_groupAt mu B hszB
  have hGrows : elim.rowsLen (places.monomialsAt mu).length
      (groupAt (A ++ B) mu) := rowsLen_groupAt mu (A ++ B) hszAB
  have hCA := elim.collect_rowsLen (places.monomialsAt mu).length
    (groupAt A mu) hArows
  have hCB := elim.collect_rowsLen (places.monomialsAt mu).length
    (groupAt B mu) hBrows
  have hCG := elim.collect_rowsLen (places.monomialsAt mu).length
    (groupAt (A ++ B) mu) hGrows
  have hL' := elim.rowsLen_append (places.monomialsAt mu).length
    hCA hCB
  have hR := units.rowsLen_stackedRaise mu
  have hperpC : ∀ k,
      k < (elim.collectOf (places.monomialsAt mu).length
        (groupAt A mu)).length →
      ∀ l, l < (elim.collectOf (places.monomialsAt mu).length
        (groupAt B mu)).length →
      (elim.dotP
        (ground.getAt []
          (elim.collectOf (places.monomialsAt mu).length
            (groupAt A mu)) k)
        (ground.getAt []
          (elim.collectOf (places.monomialsAt mu).length
            (groupAt B mu)) l)).oneValue BPair.unit := by
    intro k hk l hl
    have h1 : ∀ k2, k2 < (groupAt A mu).length →
        (elim.dotP (ground.getAt [] (groupAt A mu) k2)
          (ground.getAt []
            (elim.collectOf (places.monomialsAt mu).length
              (groupAt B mu)) l)).oneValue BPair.unit := by
      intro k2 hk2
      exact elim.perp_span (places.monomialsAt mu).length
        (groupAt B mu) _ _ hBrows
        (elim.rowsLen_getAt _ k2 hArows hk2)
        (fun l2 hl2 => hperpMu k2 hk2 l2 hl2)
        (elim.collect_row_span _ _ hBrows l hl)
    rw [elim.dotP_comm]
    refine elim.perp_span (places.monomialsAt mu).length
      (groupAt A mu) _ _ hArows
      (elim.rowsLen_getAt _ l hCB hl) ?_
      (elim.collect_row_span _ _ hArows k hk)
    intro k2 hk2
    rw [elim.dotP_comm]
    exact h1 k2 hk2
  have hiL' := elim.indep_append_perp (places.monomialsAt mu).length
    _ _ hCA hCB
    (elim.collect_indep _ _ hArows) (elim.collect_indep _ _ hBrows)
    hperpC
  have hGsplit : groupAt (A ++ B) mu
      = groupAt A mu ++ groupAt B mu := groupAt_append A B mu
  have hrowsG : ∀ k, k < (groupAt (A ++ B) mu).length →
      elim.spanRel (places.monomialsAt mu).length
        (elim.collectOf (places.monomialsAt mu).length
            (groupAt A mu)
          ++ elim.collectOf (places.monomialsAt mu).length
            (groupAt B mu))
        (ground.getAt [] (groupAt (A ++ B) mu) k) := by
    rw [hGsplit]
    refine ground.getAt_append_all ([] : List BPair)
      (elim.spanRel (places.monomialsAt mu).length _)
      (groupAt A mu) (groupAt B mu) ?_ ?_
    · intro k hk
      exact elim.spanRel_mono _ _ _ _ hCA hCB
        (elim.collect_span_row _ _ hArows k hk)
    · intro k hk
      exact elim.spanRel_mono_left _ _ _ _ hCA hCB
        (elim.collect_span_row _ _ hBrows k hk)
  have hmut : ∀ k,
      k < (elim.collectOf (places.monomialsAt mu).length
        (groupAt (A ++ B) mu)).length →
      elim.spanRel (places.monomialsAt mu).length
        (elim.collectOf (places.monomialsAt mu).length
            (groupAt A mu)
          ++ elim.collectOf (places.monomialsAt mu).length
            (groupAt B mu))
        (ground.getAt []
          (elim.collectOf (places.monomialsAt mu).length
            (groupAt (A ++ B) mu)) k) := by
    intro k hk
    exact elim.spanRel_trans (places.monomialsAt mu).length
      (groupAt (A ++ B) mu) _ _ hGrows hL' hrowsG
      (elim.collect_row_span _ _ hGrows k hk)
  have hrowsA : ∀ k, k < (groupAt A mu).length →
      elim.spanRel (places.monomialsAt mu).length
        (groupAt (A ++ B) mu)
        (ground.getAt [] (groupAt A mu) k) := by
    intro k hk
    rw [hGsplit]
    exact elim.spanRel_mono _ _ _ _ hArows hBrows
      (elim.spanRel_getAt _ (groupAt A mu) k hk hArows)
  have hrowsB : ∀ k, k < (groupAt B mu).length →
      elim.spanRel (places.monomialsAt mu).length
        (groupAt (A ++ B) mu)
        (ground.getAt [] (groupAt B mu) k) := by
    intro k hk
    rw [hGsplit]
    exact elim.spanRel_mono_left _ _ _ _ hArows hBrows
      (elim.spanRel_getAt _ (groupAt B mu) k hk hBrows)
  have hmut' : ∀ k,
      k < (elim.collectOf (places.monomialsAt mu).length
          (groupAt A mu)
        ++ elim.collectOf (places.monomialsAt mu).length
          (groupAt B mu)).length →
      elim.spanRel (places.monomialsAt mu).length
        (elim.collectOf (places.monomialsAt mu).length
          (groupAt (A ++ B) mu))
        (ground.getAt []
          (elim.collectOf (places.monomialsAt mu).length
              (groupAt A mu)
            ++ elim.collectOf (places.monomialsAt mu).length
              (groupAt B mu)) k) := by
    refine ground.getAt_append_all ([] : List BPair)
      (elim.spanRel (places.monomialsAt mu).length _) _ _ ?_ ?_
    · intro k hk
      refine elim.spanRel_trans (places.monomialsAt mu).length
        (groupAt (A ++ B) mu) _ _ hGrows hCG
        (fun k2 hk2 => elim.collect_span_row _ _ hGrows k2 hk2) ?_
      exact elim.spanRel_trans (places.monomialsAt mu).length
        (groupAt A mu) _ _ hArows hGrows hrowsA
        (elim.collect_row_span _ _ hArows k hk)
    · intro k hk
      refine elim.spanRel_trans (places.monomialsAt mu).length
        (groupAt (A ++ B) mu) _ _ hGrows hCG
        (fun k2 hk2 => elim.collect_span_row _ _ hGrows k2 hk2) ?_
      exact elim.spanRel_trans (places.monomialsAt mu).length
        (groupAt B mu) _ _ hBrows hGrows hrowsB
        (elim.collect_row_span _ _ hBrows k hk)
  have hcongr := elim.kernelDim_congr (places.monomialsAt mu).length
    (units.stackedRaise mu)
    (elim.collectOf (places.monomialsAt mu).length
      (groupAt (A ++ B) mu))
    (elim.collectOf (places.monomialsAt mu).length (groupAt A mu)
      ++ elim.collectOf (places.monomialsAt mu).length
        (groupAt B mu))
    hR hCG hL' (elim.collect_indep _ _ hGrows) hiL' hmut hmut'
  have hjoin := elim.kernelDim_rowJoin
    (elim.collectOf (places.monomialsAt mu).length
        (groupAt A mu)).length
    (elim.collectOf (places.monomialsAt mu).length
        (groupAt B mu)).length
    (elim.crossM (units.stackedRaise mu)
      (elim.collectOf (places.monomialsAt mu).length
        (groupAt A mu)))
    (elim.crossM (units.stackedRaise mu)
      (elim.collectOf (places.monomialsAt mu).length
        (groupAt B mu)))
    (elim.rowsLen_crossM _ _) (elim.rowsLen_crossM _ _)
    ((elim.length_crossM _ _).trans (elim.length_crossM _ _).symm)
    (cross_split mu A B hszA hszB hclA hclB hperpUp)
  show elim.kernelDim
      (elim.collectOf (places.monomialsAt mu).length
        (groupAt (A ++ B) mu)).length
      (elim.crossM (units.stackedRaise mu)
        (elim.collectOf (places.monomialsAt mu).length
          (groupAt (A ++ B) mu)))
    = elim.kernelDim
        (elim.collectOf (places.monomialsAt mu).length
        (groupAt A mu)).length
        (elim.crossM (units.stackedRaise mu)
          (elim.collectOf (places.monomialsAt mu).length
            (groupAt A mu)))
      + elim.kernelDim
          (elim.collectOf (places.monomialsAt mu).length
        (groupAt B mu)).length
          (elim.crossM (units.stackedRaise mu)
            (elim.collectOf (places.monomialsAt mu).length
              (groupAt B mu)))
  rw [hcongr, hjoin, elim.crossM_append, ground.length_append]

/-! The block's own count, `lem:blockcount`(ii)'s closing display:
at the span calculus's stated pool the count is one at the head's
content — the head's one-member line collected whole with its
stacked column at the sum's unit — and nought at every other
content, where a kernel coefficient would forge a top whose own
closure pool maps into the block at the identity family. -/

/-- The one-column cross datum's rows read the stacked action's
entries: at a unit-tailed image every row is its entry's own
one-member family, so the rows read the sum's unit. -/
private theorem crossOne_rows : ∀ (R : elim.Mat) (c : List BPair),
    poly.unitTail (elim.matVec R c) →
    ∀ k, k < (elim.crossM R [c]).length →
      poly.unitTail (ground.getAt ([] : List BPair)
        (elim.crossM R [c]) k)
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | r :: _, c, h, 0, _ => by
    have h1 : (elim.dotN r c).oneValue BPair.unit := h.1
    exact ⟨h1, trivial⟩
  | _ :: R, c, h, k + 1, hk => by
    exact crossOne_rows R c h.2 k (Nat.lt_of_succ_lt_succ hk)

/-- The head is a top at the stated pool (`lem:tops`(i)'s read at
the vacant raised groups, `tops.vacant_settled`): a raised content
sits above the head at the height fold
(`lowerspan.ht_moveAt_raise`) with every word strictly below it
(`blockirr.ht_strict`), so the raised content's group is vacant
and the closure's settled image reads the sum's unit. -/
private theorem head_top (d : Nat) (v : HVec) (tail : List HVec)
    (hwid : ∀ w ∈ v :: tail, w.content.length = d)
    (hprov : ∀ k, k < tail.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tail) i)
          = some (getAt (⟨[], []⟩ : HVec) tail k))
    (hcl : ∀ w ∈ v :: tail, ∀ i < d, ∀ j < d, ¬ i = j →
      settledAt (v :: tail) (act i j w))
    (i j : Nat) (hij : i < j) (hj : j < d) :
    poly.unitTail (act i j v).coords := by
  have hvw : v.content.length = d := hwid v (List.Mem.head tail)
  have hrise : lowerspan.ht v.content
      < lowerspan.ht (moveAt i j v.content) :=
    lowerspan.ht_moveAt_raise i j v.content hij
      (by rw [hvw]; exact hj)
  have hnm : ¬ (moveAt i j v.content)
      ∈ (v :: tail).map HVec.content := by
    intro hm
    match ground.mem_map_of HVec.content (v :: tail) _ hm with
    | ⟨w, hw, hwc⟩ =>
      cases hw with
      | head =>
        have heq : lowerspan.ht v.content
            = lowerspan.ht (moveAt i j v.content) :=
          congrArg lowerspan.ht hwc
        rw [← heq] at hrise
        exact absurd hrise (Nat.lt_irrefl _)
      | tail _ hwt =>
        have hlt := blockirr.ht_strict d v tail hwid hprov w hwt
        rw [hwc] at hlt
        exact absurd (Nat.lt_trans hrise hlt) (Nat.lt_irrefl _)
  have hocc : occ (moveAt i j v.content) (v :: tail) = 0 := by
    rw [← length_groupAt, groupAt_nil_of_not_mem _ _ hnm]
    rfl
  exact tops.vacant_settled (v :: tail) v i j
    (hcl v (List.Mem.head tail) i (Nat.lt_trans hij hj) j hj
      (Nat.ne_of_lt hij))
    hocc

/-- The count at the head's content is one: the top-content group
is the head's one-member line (`blockirr.group_head`), the
collection keeps it at the off-unit read, and the stacked column's
entries read the sum's unit through the derived top read, so the
rank is nought at the one collected column. -/
private theorem count_head (d : Nat) (v : HVec) (tail : List HVec)
    (hsz : ∀ w ∈ v :: tail, sized w)
    (hwid : ∀ w ∈ v :: tail, w.content.length = d)
    (hprov : ∀ k, k < tail.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tail) i)
          = some (getAt (⟨[], []⟩ : HVec) tail k))
    (hcl : ∀ w ∈ v :: tail, ∀ i < d, ∀ j < d, ¬ i = j →
      settledAt (v :: tail) (act i j w))
    (hoff : ¬ poly.unitTail v.coords) :
    countAt (v :: tail) v.content = 1 := by
  have hszv : v.coords.length = (monomialsAt v.content).length :=
    hsz v (List.Mem.head tail)
  have hgh : groupAt (v :: tail) v.content = [v.coords] :=
    blockirr.group_head d v tail hwid hprov
  have hstack : poly.unitTail
      (elim.matVec (units.stackedRaise v.content) v.coords) := by
    refine units.stackedRaise_of v.content v.coords ?_
    intro i hi _
    have hj : i + 1 < d := by
      rw [← hwid v (List.Mem.head tail)]
      exact hi
    have h := head_top d v tail hwid hprov hcl i (i + 1)
      (Nat.lt_succ_self i) hj
    have h' : poly.unitTail (elim.matVec
        (units.matUnitAt (moveAt i (i + 1) v.content) v.content
          i (i + 1)) v.coords) := h
    rw [moveAt_moveUp i v.content] at h'
    exact h'
  have hrank : elim.rank (elim.crossM (units.stackedRaise v.content)
      [v.coords]) = 0 :=
    elim.rank_null _ (crossOne_rows _ _ hstack)
  show elim.kernelDim
      (elim.collectOf (monomialsAt v.content).length
        (groupAt (v :: tail) v.content)).length
      (elim.crossM (units.stackedRaise v.content)
        (elim.collectOf (monomialsAt v.content).length
          (groupAt (v :: tail) v.content))) = 1
  rw [hgh, elim.collect_single (monomialsAt v.content).length
    v.coords hszv hoff]
  show ([v.coords].length
    - elim.rank (elim.crossM (units.stackedRaise v.content)
        [v.coords])) = 1
  rw [hrank]
  rfl

/-- A closure pool's members settle in the stated pool: the seed
settles, and a lowering image of a settled member settles at the
closed pool's own transport (`act_transport` at the closure's
stated data), the provenance walked position by position. -/
private theorem prov_settle (d : Nat) (P : List HVec)
    (hsz : ∀ w ∈ P, sized w)
    (hcl : ∀ w ∈ P, ∀ i < d, ∀ j < d, ¬ i = j →
      settledAt P (act i j w))
    (z : HVec) (tz : List HVec)
    (hprovz : ∀ k, k < tz.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (z :: tz) i)
          = some (getAt (⟨[], []⟩ : HVec) tz k))
    (hszz : sized z) (hwdz : z.content.length = d)
    (hsetz : settledAt P z) :
    ∀ y ∈ z :: tz, sized y ∧ y.content.length = d
      ∧ settledAt P y := by
  refine prov_all d z tz _ hprovz ⟨hszz, hwdz, hsetz⟩ ?_
  intro a b j hjd hq hlw
  have hjlt : j < d := Nat.lt_trans (Nat.lt_succ_self j) hjd
  have hjne : ¬ j + 1 = j := fun he =>
    absurd he (Nat.succ_ne_self j)
  have himg : ∀ y ∈ P, settledAt P (act (j + 1) j y) :=
    fun y hy => hcl y hy (j + 1) hjd j hjlt hjne
  have hspan : elim.spanRel (monomialsAt a.content).length
      (groupAt P a.content) a.coords := by
    have h := settled_to_span P a hsz hq.1 hq.2.2
    rw [hq.1] at h
    exact h
  have htr := act_transport P (j + 1) j hsz himg
    a.content a.coords hq.1 hspan
  rw [moveAt_moveDn j a.content] at htr
  rw [lowerH_eq hlw]
  refine ⟨?_, ?_, ?_⟩
  · show (elim.matVec (units.matUnitAt (units.moveDn j a.content)
      a.content (j + 1) j) a.coords).length
      = (monomialsAt (units.moveDn j a.content)).length
    exact units.matVec_matUnitAt_length _ _ (j + 1) j a.coords
  · show (units.moveDn j a.content).length = d
    rw [units.length_moveDn]
    exact hq.2.1
  · refine Or.inr ?_
    show elim.spanRel (elim.matVec (units.matUnitAt
        (units.moveDn j a.content) a.content (j + 1) j)
        a.coords).length
      (groupAt P (units.moveDn j a.content))
      (elim.matVec (units.matUnitAt (units.moveDn j a.content)
        a.content (j + 1) j) a.coords)
    rw [units.matVec_matUnitAt_length]
    exact htr

/-- A stacked-kernel coefficient family is a top at its content:
the occupied adjacent moves read the kernel condition
(`units.stackedRaise_to`), the unoccupied ones the action's own
vacancy (`units.matVec_null_unocc`). -/
private theorem seed_top (d : Nat) (mu : List Nat) (x : List BPair)
    (hmud : mu.length = d)
    (hstack : poly.unitTail
      (elim.matVec (units.stackedRaise mu) x)) :
    ∀ jr, jr + 1 < d →
      poly.unitTail (act jr (jr + 1) (⟨mu, x⟩ : HVec)).coords := by
  intro jr hjr
  show poly.unitTail (elim.matVec (units.matUnitAt
    (moveAt jr (jr + 1) mu) mu jr (jr + 1)) x)
  match Nat.eq_zero_or_pos (ground.getAt 0 mu (jr + 1)) with
  | .inl hz => exact units.matVec_null_unocc _ mu jr (jr + 1) hz x
  | .inr hocc =>
    have h := units.stackedRaise_to mu x hstack jr
      (by rw [hmud]; exact hjr) hocc
    rw [← moveAt_moveUp jr mu] at h
    exact h

/-- An off-unit vector at a stated content, stacked to the sum's
unit and settled in the pool, reads the head's own content: its
seed-closure pool carries the span calculus's stated data
(`seedSpan_sem`, `seedSpan_prov`, `pool_act_closed` at the derived
top read), every member settles in the pool, and the identity
family maps it into the pool at `blockirr.hom_content`. -/
private theorem seed_forge (d : Nat) (v : HVec) (tail : List HVec)
    (hsz : ∀ w ∈ v :: tail, sized w)
    (hwid : ∀ w ∈ v :: tail, w.content.length = d)
    (hprov : ∀ k, k < tail.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tail) i)
          = some (getAt (⟨[], []⟩ : HVec) tail k))
    (hcl : ∀ w ∈ v :: tail, ∀ i < d, ∀ j < d, ¬ i = j →
      settledAt (v :: tail) (act i j w))
    (mu : List Nat) (hmud : mu.length = d) (x : List BPair)
    (hxlen : x.length = (monomialsAt mu).length)
    (hxoff : ¬ poly.unitTail x)
    (hstack : poly.unitTail
      (elim.matVec (units.stackedRaise mu) x))
    (hspan : elim.spanRel (monomialsAt mu).length
      (groupAt (v :: tail) mu) x) :
    mu = v.content := by
  have hsz0 : sized (⟨mu, x⟩ : HVec) := hxlen
  have hset0 : settledAt (v :: tail) (⟨mu, x⟩ : HVec) := by
    refine Or.inr ?_
    show elim.spanRel x.length (groupAt (v :: tail) mu) x
    rw [hxlen]
    exact hspan
  have htop0 := seed_top d mu x hmud hstack
  match lowerspan.seed_closed d (lowerspan.ht mu)
      (⟨mu, x⟩ : HVec) hsz0 hmud hxoff htop0 (Nat.le_refl _) with
  | ⟨t0, ht0, hsz0all, hwid0, hprov0, _, hclv⟩ =>
    have hsettle := prov_settle d (v :: tail) hsz hcl
      (⟨mu, x⟩ : HVec) t0
      hprov0 hsz0 hmud hset0
    have hTsq : ∀ w ∈ (⟨mu, x⟩ : HVec) :: t0,
        elim.sqAt (elim.idList (monomialsAt w.content).length)
          w.coords.length := by
      intro w hw
      rw [hsz0all w hw]
      exact elim.sqAt_idList _
    have hval : ∀ w ∈ (⟨mu, x⟩ : HVec) :: t0,
        settledAt (v :: tail)
          (⟨w.content, elim.matVec
            (elim.idList (monomialsAt w.content).length)
            w.coords⟩ : HVec) := by
      intro w hw
      have hws := hsz0all w hw
      have hlen : (elim.matVec
          (elim.idList (monomialsAt w.content).length)
          w.coords).length = (monomialsAt w.content).length := by
        rw [elim.matVec_length, elim.length_idList]
      have hone := elim.matVec_idList
        (monomialsAt w.content).length w.coords hws
      have hspanw : elim.spanRel (monomialsAt w.content).length
          (groupAt (v :: tail) w.content) w.coords := by
        have h := settled_to_span (v :: tail) w hsz hws
          (hsettle w hw).2.2
        rw [hws] at h
        exact h
      refine Or.inr ?_
      show elim.spanRel (elim.matVec
          (elim.idList (monomialsAt w.content).length)
          w.coords).length (groupAt (v :: tail) w.content)
        (elim.matVec (elim.idList (monomialsAt w.content).length)
          w.coords)
      rw [hlen]
      exact elim.spanRel_congr _ _ w.coords _
        (poly.oneValue_symm hone) hspanw hlen
    have hmv : ∀ w ∈ (⟨mu, x⟩ : HVec) :: t0, ∀ i < d, ∀ j < d,
        ¬ i = j →
        poly.oneValue
          (elim.matVec
            (units.matUnitAt (moveAt i j w.content) w.content i j)
            (elim.matVec
              (elim.idList (monomialsAt w.content).length)
              w.coords))
          (elim.matVec
            (elim.idList
              (monomialsAt (moveAt i j w.content)).length)
            (elim.matVec
              (units.matUnitAt (moveAt i j w.content) w.content i j)
              w.coords)) := by
      intro w hw i _ j _ _
      have hws := hsz0all w hw
      have h1 := elim.matVec_idList (monomialsAt w.content).length
        w.coords hws
      have hLs := elim.matVec_congr
        (units.matUnitAt (moveAt i j w.content) w.content i j)
        (elim.matVec (elim.idList (monomialsAt w.content).length)
          w.coords) w.coords h1
      have hRs := elim.matVec_idList
        (monomialsAt (moveAt i j w.content)).length
        (elim.matVec
          (units.matUnitAt (moveAt i j w.content) w.content i j)
          w.coords)
        (units.matVec_matUnitAt_length _ _ i j w.coords)
      exact poly.oneValue_trans hLs (poly.oneValue_symm hRs)
    have hoffv : ∃ w ∈ (⟨mu, x⟩ : HVec) :: t0,
        ¬ poly.unitTail (elim.matVec
          (elim.idList (monomialsAt w.content).length)
          w.coords) := by
      refine ⟨(⟨mu, x⟩ : HVec), List.Mem.head t0, ?_⟩
      intro hu
      exact hxoff (poly.oneValue_unitTail
        (poly.oneValue_symm
          (elim.matVec_idList (monomialsAt mu).length x hxlen)) hu)
    exact blockirr.hom_content d (⟨mu, x⟩ : HVec) t0 v tail
      (fun c => elim.idList (monomialsAt c).length)
      hsz0all hwid0 hprov0 hclv hsz hwid hprov hTsq hval hmv hoffv

/-- The count off the head's content is nought: a content the pool
does not carry reads the vacant group and the vacant collection,
and at an occupied group an empty kernel list is forced — a member
would hand an off-unit vector stacked to the sum's unit inside the
group's span, forging the head's own content against the case. -/
private theorem count_off (d : Nat) (v : HVec) (tail : List HVec)
    (hsz : ∀ w ∈ v :: tail, sized w)
    (hwid : ∀ w ∈ v :: tail, w.content.length = d)
    (hprov : ∀ k, k < tail.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tail) i)
          = some (getAt (⟨[], []⟩ : HVec) tail k))
    (hcl : ∀ w ∈ v :: tail, ∀ i < d, ∀ j < d, ¬ i = j →
      settledAt (v :: tail) (act i j w))
    (mu : List Nat) (hne : ¬ mu = v.content) :
    countAt (v :: tail) mu = 0 := by
  match Nat.eq_zero_or_pos
      (ground.countOf mu ((v :: tail).map HVec.content)) with
  | .inr hpos =>
    have hmem := ground.mem_of_countOf_pos mu
      ((v :: tail).map HVec.content) hpos
    have hmud : mu.length = d := by
      match ground.mem_map_of HVec.content (v :: tail) mu hmem with
      | ⟨y, hy, hyc⟩ =>
        have h := hwid y hy
        rw [hyc] at h
        exact h
    have hG : elim.rowsLen (monomialsAt mu).length
        (groupAt (v :: tail) mu) :=
      rowsLen_groupAt mu (v :: tail) hsz
    have hL : elim.rowsLen (monomialsAt mu).length
        (elim.collectOf (monomialsAt mu).length
          (groupAt (v :: tail) mu)) :=
      elim.collect_rowsLen _ _ hG
    have hR : elim.rowsLen (monomialsAt mu).length
        (units.stackedRaise mu) := units.rowsLen_stackedRaise mu
    show elim.kernelDim
      (elim.collectOf (monomialsAt mu).length
        (groupAt (v :: tail) mu)).length
      (elim.crossM (units.stackedRaise mu)
        (elim.collectOf (monomialsAt mu).length
          (groupAt (v :: tail) mu))) = 0
    rw [← elim.kernelList_dim
      (elim.collectOf (monomialsAt mu).length
        (groupAt (v :: tail) mu)).length
      (elim.crossM (units.stackedRaise mu)
        (elim.collectOf (monomialsAt mu).length
          (groupAt (v :: tail) mu)))]
    match Nat.eq_zero_or_pos (elim.kernelList
        (elim.collectOf (monomialsAt mu).length
          (groupAt (v :: tail) mu)).length
        (elim.crossM (units.stackedRaise mu)
          (elim.collectOf (monomialsAt mu).length
            (groupAt (v :: tail) mu)))).length with
    | .inl hz => exact hz
    | .inr hp =>
      exfalso
      refine hne ?_
      have hKr : elim.rowsLen
          (elim.collectOf (monomialsAt mu).length
            (groupAt (v :: tail) mu)).length
          (elim.crossM (units.stackedRaise mu)
            (elim.collectOf (monomialsAt mu).length
              (groupAt (v :: tail) mu))) :=
        elim.rowsLen_crossM _ _
      have hcoff := elim.indep_row_off
        (elim.kernelList_indep _ _ hKr) 0 hp
      have hclen := elim.rowsLen_getAt _ 0
        (elim.kernelList_rowsLen _ _) hp
      have hker := elim.kernelList_members _ _ hKr 0 hp
      refine seed_forge d v tail hsz hwid hprov hcl mu hmud
        (elim.combo (monomialsAt mu).length
          (ground.getAt ([] : List BPair)
            (elim.kernelList
              (elim.collectOf (monomialsAt mu).length
                (groupAt (v :: tail) mu)).length
              (elim.crossM (units.stackedRaise mu)
                (elim.collectOf (monomialsAt mu).length
                  (groupAt (v :: tail) mu)))) 0)
          (elim.collectOf (monomialsAt mu).length
            (groupAt (v :: tail) mu)))
        (elim.length_combo _ _ _ hL) ?_ ?_ ?_
      · intro hu
        exact hcoff (elim.indep_elim
          (elim.collect_indep _ _ hG) _ hclen hu)
      · exact poly.unitTail_oneValue_right hker
          (elim.matVec_crossM (monomialsAt mu).length
            (units.stackedRaise mu)
            (elim.collectOf (monomialsAt mu).length
              (groupAt (v :: tail) mu)) _ hR hL)
      · exact elim.spanRel_combo (monomialsAt mu).length
          (groupAt (v :: tail) mu) hG
          (elim.collectOf (monomialsAt mu).length
            (groupAt (v :: tail) mu)) _ hL
          (elim.collect_row_span (monomialsAt mu).length
            (groupAt (v :: tail) mu) hG)
  | .inl hz =>
    have hg : groupAt (v :: tail) mu = [] :=
      groupAt_nil_of_countOf _ _ hz
    show elim.kernelDim
      (elim.collectOf (monomialsAt mu).length
        (groupAt (v :: tail) mu)).length
      (elim.crossM (units.stackedRaise mu)
        (elim.collectOf (monomialsAt mu).length
          (groupAt (v :: tail) mu))) = 0
    rw [hg]
    show (0 : Nat) - elim.rank (elim.crossM (units.stackedRaise mu)
      (elim.collectOf (monomialsAt mu).length ([] : elim.Mat))) = 0
    exact Nat.zero_sub _

/-- A block reads its own count alone (`lem:blockcount`(ii)'s
closing display, N_λ(W_u) = δ): at the span calculus's stated pool
the count is one at the head's content — the top-content group the
head's one-member line (`blockirr.group_head`), the collection its
own, the stacked column at the unit through the closed pool's
derived top read — and nought at every other content: an occupied
kernel coefficient would hand an off-unit top whose own closure
pool maps into the block at the identity family, and the head
contents agree (`blockirr.hom_content`), against the case.  The
head is a top BECAUSE the pool is a closed provenance pool: the
raised content sits one above at the height fold
(`lowerspan.ht_moveAt_raise`) with every word strictly below
(`blockirr.ht_strict`), so its group is vacant and the closure
reads the image at the unit; the pinned top binder fell to that
derivation.  Binders: hsz/hwid/hprov the span calculus's stated
data (`lem:lowerspan`'s frame); hcl the closure's stated data,
load-bearing with its committed refusal; hoff load-bearing with
its committed refusal. -/
theorem countAt_block (d : Nat) (v : HVec) (tail : List HVec)
    (hsz : ∀ w ∈ v :: tail, sized w)
    (hwid : ∀ w ∈ v :: tail, w.content.length = d)
    (hprov : ∀ k, k < tail.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tail) i)
          = some (getAt (⟨[], []⟩ : HVec) tail k))
    (hcl : ∀ w ∈ v :: tail, ∀ i < d, ∀ j < d, ¬ i = j →
      settledAt (v :: tail) (act i j w))
    (hoff : ¬ poly.unitTail v.coords)
    (mu : List Nat) :
    countAt (v :: tail) mu = if mu = v.content then 1 else 0 := by
  by_cases hmu : mu = v.content
  · rw [if_pos hmu, hmu]
    exact count_head d v tail hsz hwid hprov hcl hoff
  · rw [if_neg hmu]
    exact count_off d v tail hsz hwid hprov hcl mu hmu

/-! The block's own count at the shapes' own carriers, and the
fusion identities at the exhaustion tier: the fusion
count is the fused pool's own count at the target content, the
shape's block reads the Kronecker delta at its row list, and the
unit shape's line reads the first factor back. -/

/-- The fusion count is the fused pool's own count at the target
content: the display's pair list is independent, so the count's
collection keeps it whole (`lem:blockcount`(iii)).  Binders: the
one letter width `hba` is load-bearing with its committed
refusal; the two blocks' own independence
is derived, not stated — `lowerspan.spanReads` reads it off the
guard's maintained independence — and the members' widths and one
degree are the span's own reads (`blockSpan_width`,
`blockSpan_degree`). -/
theorem fusionCount_countAt (a b c : Shape)
    (hba : b.length = a.length) :
    fusionCount a b c
      = countAt (fusedAt (blockSpan a) (blockSpan b)) (rowList c) :=
  (countAt_pairs (blockSpan a) (blockSpan b) (rowList c)
    (tensor_indep (blockSpan a) (blockSpan b) (rowList c) a.length
      (degree a) (blockSpan_width a)
      (fun w hw => (blockSpan_width b w hw).trans hba)
      (blockSpan_degree a) (lowerspan.spanReads a).2.1
      (lowerspan.spanReads b).2.1)).symm

/-- `lem:blockcount`(iii)'s first identity at the flip of factors:
the arrangements' exchange maps each pair to the exchanged pair at
the commuted coordinate products, commuting with every raising at
the exchanged Leibniz places, a kernel family reading across at the
exchanged coefficients, the two kernel dimensions one count.
Binders: the one letter width `hba` is load-bearing with its
committed refusal, a wider second shape at a second occupied
letter parting the two orders' counts; the two blocks' own
independence is derived, not
stated — `lowerspan.spanReads` reads it off the guard's maintained
independence — and the members' widths and one degree are the
span's own reads (`blockSpan_width`, `blockSpan_degree`). -/
theorem fusionCount_comm (a b c : Shape)
    (hba : b.length = a.length) :
    fusionCount a b c = fusionCount b a c := by
  show elim.kernelDim
      (pairsAt (blockSpan a) (blockSpan b) (rowList c)).length
      (elim.crossM (units.stackedRaise (rowList c))
        ((pairsAt (blockSpan a) (blockSpan b) (rowList c)).map
          HVec.coords))
    = elim.kernelDim
      (pairsAt (blockSpan b) (blockSpan a) (rowList c)).length
      (elim.crossM (units.stackedRaise (rowList c))
        ((pairsAt (blockSpan b) (blockSpan a) (rowList c)).map
          HVec.coords))
  exact kernelDim_pairs_comm (blockSpan a) (blockSpan b)
    (rowList c) a.length (degree a) (degree b) (blockSpan_width a)
    (fun w hw => (blockSpan_width b w hw).trans hba)
    (blockSpan_degree a) (blockSpan_degree b)
    (lowerspan.spanReads a).2.1 (lowerspan.spanReads b).2.1

/-- The shape's own block reads the Kronecker delta at its row list
(`lem:blockcount`(ii)'s closing display, `N_λ(W_{t_λ}) = δ`): the
span is the exhibit's provenance pool, so `countAt_block` reads one
count at the head's content and nought at every other, and the
head's content is the shape's row list (`content_exhibit`).  The
stated data are the span's own reads throughout — the enumerations
and the group independence at `lowerspan.spanReads`, the widths at
`blockSpan_width`, the closure at `lowerspan.act_closed_def`, the
head off the unit tail at `exhibit_off_unit` — so the display
carries no binder of its own. -/
theorem countAt_blockSpan (s : Shape) (mu : List Nat) :
    countAt (blockSpan s) mu = if mu = rowList s then 1 else 0 := by
  match blockSpan_prov s with
  | ⟨tailu, htu, hprovu⟩ =>
    have hsz : ∀ w ∈ exhibit s :: tailu, sized w := by
      intro w hw
      exact (lowerspan.spanReads s).1 w (by rw [htu]; exact hw)
    have hwid : ∀ w ∈ exhibit s :: tailu,
        w.content.length = s.length := by
      intro w hw
      exact blockSpan_width s w (by rw [htu]; exact hw)
    have hcl : ∀ w ∈ exhibit s :: tailu, ∀ i < s.length,
        ∀ j < s.length, ¬ i = j →
        settledAt (exhibit s :: tailu) (act i j w) := by
      intro w hw i hi j hj hij
      have h := lowerspan.act_closed_def s i j hi hj hij w
        (by rw [htu]; exact hw)
      rw [htu] at h
      exact h
    have h := countAt_block s.length (exhibit s) tailu hsz hwid
      hprovu hcl (exhibit_off_unit s) mu
    rw [content_exhibit s] at h
    rw [htu]
    exact h

private theorem fusedAt_single (w : HVec) :
    ∀ A : List HVec, fusedAt A [w] = A.map (fun v => tensorH v w)
  | [] => rfl
  | v :: A => by
    show tensorH v w :: fusedAt A [w]
      = tensorH v w :: A.map (fun v => tensorH v w)
    rw [fusedAt_single w A]

private theorem countAt_fused_unitShape (n : Nat) (A : List HVec)
    (hszA : ∀ v ∈ A, sized v)
    (hwidA : ∀ v ∈ A, v.content.length = n) (mu : List Nat) :
    countAt (fusedAt A [exhibit (List.replicate n 0)]) mu
      = countAt A mu := by
  have hR : fusedAt A [exhibit (List.replicate n 0)]
      = A.map (fun v => tensorH v (exhibit (List.replicate n 0))) :=
    fusedAt_single (exhibit (List.replicate n 0)) A
  have hpair : ∀ v ∈ A,
      (tensorH v (exhibit (List.replicate n 0))).content = v.content
        ∧ poly.oneValue v.coords
          (tensorH v (exhibit (List.replicate n 0))).coords :=
    fun v hv => tensorH_unitShape n v (hszA v hv) (hwidA v hv)
  have hlen : ∀ v ∈ A,
      (tensorH v (exhibit (List.replicate n 0))).coords.length
        = v.coords.length := by
    intro v hv
    rw [tensorH_sized v (exhibit (List.replicate n 0)),
      (hpair v hv).1]
    exact (hszA v hv).symm
  have hszR : ∀ x ∈ fusedAt A [exhibit (List.replicate n 0)],
      sized x := by
    intro x hx
    rw [hR] at hx
    match ground.mem_map_of _ A x hx with
    | ⟨v, _, hvx⟩ =>
      rw [← hvx]
      exact tensorH_sized v (exhibit (List.replicate n 0))
  refine countAt_congr mu _ A hszR hszA ?_ ?_
  · refine group_span_rows _ A mu hszR ?_
    intro x hx
    rw [hR] at hx
    match ground.mem_map_of _ A x hx with
    | ⟨v, hv, hvx⟩ =>
      rw [← hvx, (hpair v hv).1, hlen v hv]
      exact elim.spanRel_congr v.coords.length (groupAt A v.content)
        v.coords (tensorH v (exhibit (List.replicate n 0))).coords
        (hpair v hv).2
        (settled_to_span A v hszA (hszA v hv)
          (member_settled A hszA v hv))
        (hlen v hv)
  · refine group_span_rows A _ mu hszA ?_
    intro v hv
    have hxm : tensorH v (exhibit (List.replicate n 0))
        ∈ fusedAt A [exhibit (List.replicate n 0)] := by
      rw [hR]
      exact ground.mem_map_to _ hv
    have hx := settled_to_span _
      (tensorH v (exhibit (List.replicate n 0))) hszR
      (tensorH_sized v (exhibit (List.replicate n 0)))
      (member_settled _ hszR _ hxm)
    rw [(hpair v hv).1, hlen v hv] at hx
    exact elim.spanRel_congr v.coords.length
      (groupAt (fusedAt A [exhibit (List.replicate n 0)])
        v.content)
      (tensorH v (exhibit (List.replicate n 0))).coords v.coords
      (poly.oneValue_symm (hpair v hv).2) hx rfl

set_option linter.unusedVariables false in
/-- The unit shape's line reads the first factor back
(`lem:blockcount`(iii)'s third identity): the vacant occupancy
family carries no column, so its exhibit is the scalar one
(`blockSpan_unitShape` — every letter unoccupied, no interior
lowering present, the closure's first round refusing outright), and
a tensor against it keeps the first factor's content and reads its
coordinates at the vacant second arrangement
(`tensorH_unitShape`).  So the fused pool's content group is the
block's own group row for row up to one value, the count transports
(`countAt_congr` at `elim.spanRel_getAt` and `elim.spanRel_congr`
in both directions), and the read is (ii)'s closing display at the
block itself (`countAt_blockSpan`), the row lists reading their
shapes back (`places.rowList_inj`).  `hca` is the frame
(`con:places`' one letter width): it is unrefusable — at a ragged
`c` the fused contents carry the first shape's width, no pair row
matches the target's row list, and both sides read nought — and the
proof consumes it nowhere; the probes stand in ChecksFusiondata
beside the pins. -/
theorem fusionCount_unit (a c : Shape)
    (hca : c.length = a.length) :
    fusionCount a (List.replicate a.length 0) c
      = if c = a then 1 else 0 := by
  rw [fusionCount_countAt a (List.replicate a.length 0) c
      (ground.length_replicate (0 : Nat) a.length),
    blockSpan_unitShape a.length,
    countAt_fused_unitShape a.length (blockSpan a)
      (lowerspan.spanReads a).1 (blockSpan_width a) (rowList c),
    countAt_blockSpan a (rowList c)]
  by_cases hc : c = a
  · rw [if_pos hc, if_pos (congrArg rowList hc)]
  · rw [if_neg hc, if_neg (fun h => hc (rowList_inj c a h))]

/-! `lem:orthsplit`'s read along the descent, `lem:blockcount`(i)'s
orthogonal sum: against an external pool closed at every letter
pair, a carrier whose members pair its content groups at the sum's
unit hands blocks whose every member pairs there too — the seed's
closure walks the display through the lowering moves
(`act_perp` at the transpose partner, `pool_perp` along the
provenance) and the residual carrier keeps it (`elim.resid_perp_ext` at
the collected group).  The round's own block is the instance the
descent consumes: its residual carrier pairs it at the unit
outright (`resid_perp_own`), so the produced blocks are pairwise
perpendicular, they settle in the stated carrier, and their join
is independent at every content. -/

/-- The block's stated data at a round's pick: the seed's closure
pool reads the enumerations, the widths, the group independence
and the interior closure, its every member settles in the stated
carrier, the pick heads the pool with the words' provenance behind
it, and the head is a top — the pick's own top read
(`pickTop_top`) handing `lem:lowerspan`'s seed clause, the
provenance walk (`prov_settle`) the settled half.  The head shape
and the provenance are the block tier's own consumption
(`countAt_block`, `countAt_fused_block`). -/
private theorem block_pack (d : Nat) (P : List HVec)
    (hsz : ∀ x ∈ P, sized x)
    (hwid : ∀ x ∈ P, x.content.length = d)
    (hcl : ∀ x ∈ P, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt P (act i j x))
    (w0 : HVec) (hp : pickTop P = some w0) :
    (∀ v ∈ blockOf d w0, sized v)
      ∧ (∀ v ∈ blockOf d w0, v.content.length = d)
      ∧ indepAll (blockOf d w0)
      ∧ (∀ x ∈ blockOf d w0, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
          settledAt (blockOf d w0) (act i j x))
      ∧ (∀ y ∈ blockOf d w0, settledAt P y)
      ∧ (∀ j, j < d → ∀ i, i < j →
          poly.unitTail (act i j w0).coords)
      ∧ ∃ tailB, blockOf d w0 = w0 :: tailB
          ∧ ∀ k, k < tailB.length →
            ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
              lowerH j (getAt (⟨[], []⟩ : HVec) (w0 :: tailB) i)
                = some (getAt (⟨[], []⟩ : HVec) tailB k) := by
  have hw0P := pickTop_mem P w0 hp
  have htop0 := pickTop_top d P hwid hcl w0 hp
  match lowerspan.seed_closed d (lowerspan.ht w0.content) w0
      (hsz w0 hw0P) (hwid w0 hw0P) (pickTop_off P w0 hp)
      (fun jr hjr => htop0 (jr + 1) hjr jr (Nat.lt_succ_self jr))
      (Nat.le_refl _) with
  | ⟨tailB, htlB, hszB, hwidB, hprovB, hindB, hsetB⟩ =>
    have hstl := prov_settle d P hsz hcl w0 tailB hprovB
      (hsz w0 hw0P) (hwid w0 hw0P) (member_settled P hsz w0 hw0P)
    refine ⟨?_, ?_, ?_, ?_, ?_, htop0, tailB, ?_, hprovB⟩
    · rw [blockOf_eq, htlB]
      exact hszB
    · rw [blockOf_eq, htlB]
      exact hwidB
    · rw [blockOf_eq, htlB]
      exact hindB
    · rw [blockOf_eq, htlB]
      exact hsetB
    · rw [blockOf_eq, htlB]
      exact fun y hy => (hstl y hy).2.2
    · rw [blockOf_eq, htlB]

/-- The letter pair's image keeps a stated perpendicular read: at
a vacant second letter the image reads the unit tail outright
(`units.matVec_null_unocc`) and every pairing closes there; at an
occupied one the pairing walks across the transpose partner
(`unit_adjoint`) to the reverse move of the paired row's own
member, which the pool's closure settles at the round trip's
content (`moveAt_round_at`), and the stated perpendicularity
closes it through the span (`elim.perp_span`). -/
private theorem act_perp (d : Nat) (B : List HVec)
    (hszB : ∀ x ∈ B, sized x)
    (hclB : ∀ x ∈ B, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt B (act i j x))
    (nu : List Nat) (hnu : nu.length = d) (c : List BPair)
    (hc : c.length = (places.monomialsAt nu).length)
    (hperp : ∀ k, k < (groupAt B nu).length →
      (elim.dotP c (ground.getAt [] (groupAt B nu) k)).oneValue
        BPair.unit)
    (i j : Nat) (hi : i < d) (hj : j < d) (hij : ¬ i = j) :
    ∀ k, k < (groupAt B (moveAt i j nu)).length →
      (elim.dotP
        (elim.matVec (units.matUnitAt (moveAt i j nu) nu i j) c)
        (ground.getAt [] (groupAt B (moveAt i j nu)) k)).oneValue
        BPair.unit := by
  intro k hk
  match Nat.eq_zero_or_pos (ground.getAt 0 nu j) with
  | .inl hz =>
    exact elim.dotP_null_tail_left _ _
      (units.matVec_null_unocc (moveAt i j nu) nu i j hz c)
  | .inr hjocc =>
    have hji : ¬ j = i := fun he => hij he.symm
    have hi' : i < nu.length := by
      rw [hnu]
      exact hi
    have hj' : j < nu.length := by
      rw [hnu]
      exact hj
    have hBrows : elim.rowsLen
        (places.monomialsAt (moveAt i j nu)).length
        (groupAt B (moveAt i j nu)) :=
      rowsLen_groupAt (moveAt i j nu) B hszB
    have hrowlen : (ground.getAt ([] : List BPair)
        (groupAt B (moveAt i j nu)) k).length
        = (places.monomialsAt (moveAt i j nu)).length :=
      elim.rowsLen_getAt _ k hBrows hk
    have hround : moveAt j i (moveAt i j nu) = nu :=
      moveAt_round_at j i nu hjocc
    have hspan : elim.spanRel (places.monomialsAt nu).length
        (groupAt B nu)
        (elim.matVec (units.matUnitAt nu (moveAt i j nu) j i)
          (ground.getAt [] (groupAt B (moveAt i j nu)) k)) := by
      have htr := act_transport B j i hszB
        (fun v hv => hclB v hv j hj i hi hji) (moveAt i j nu)
        (ground.getAt [] (groupAt B (moveAt i j nu)) k) hrowlen
        (elim.spanRel_getAt _ _ k hk hBrows)
      rw [hround] at htr
      exact htr
    refine BPair.oneValue_trans
      (unit_adjoint i j nu hi' hj' hij hjocc c
        (ground.getAt [] (groupAt B (moveAt i j nu)) k) hc
        hrowlen) ?_
    exact elim.perp_span (places.monomialsAt nu).length
      (groupAt B nu) c _ (rowsLen_groupAt nu B hszB) hc hperp
      hspan

/-- The seed's closure pool keeps a stated perpendicular read: the
seed's own display is the base and each lowering is the letter
pair `(j + 1, j)`'s image, both letters below the width and
distinct, so `act_perp` walks the display through the provenance
(`prov_all`). -/
private theorem pool_perp (d : Nat) (B : List HVec)
    (hszB : ∀ x ∈ B, sized x)
    (hclB : ∀ x ∈ B, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt B (act i j x))
    (w0 : HVec) (hsz0 : sized w0) (hwid0 : w0.content.length = d)
    (hperp0 : ∀ k, k < (groupAt B w0.content).length →
      (elim.dotP w0.coords
        (ground.getAt [] (groupAt B w0.content) k)).oneValue
        BPair.unit)
    (tailv : List HVec)
    (hprov : ∀ k, k < tailv.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (w0 :: tailv) i)
          = some (getAt (⟨[], []⟩ : HVec) tailv k)) :
    ∀ y ∈ w0 :: tailv, sized y ∧ y.content.length = d
      ∧ ∀ k, k < (groupAt B y.content).length →
          (elim.dotP y.coords
            (ground.getAt [] (groupAt B y.content) k)).oneValue
            BPair.unit := by
  refine prov_all d w0 tailv _ hprov ⟨hsz0, hwid0, hperp0⟩ ?_
  intro a b j hjd hq hlw
  have hjlt : j < d := Nat.lt_trans (Nat.lt_succ_self j) hjd
  have hjne : ¬ j + 1 = j := fun he =>
    absurd he (Nat.succ_ne_self j)
  have hstep := act_perp d B hszB hclB a.content hq.2.1 a.coords
    hq.1 hq.2.2 (j + 1) j hjd hjlt hjne
  rw [moveAt_moveDn j a.content] at hstep
  rw [lowerH_eq hlw]
  refine ⟨?_, ?_, ?_⟩
  · show (elim.matVec (units.matUnitAt (units.moveDn j a.content)
      a.content (j + 1) j) a.coords).length
      = (places.monomialsAt (units.moveDn j a.content)).length
    exact units.matVec_matUnitAt_length _ _ (j + 1) j a.coords
  · show (units.moveDn j a.content).length = d
    rw [units.length_moveDn]
    exact hq.2.1
  · exact hstep

/-- The residual carrier keeps a stated perpendicular read: a
member's residual pairs an external row through its own stated
display and the block's, the collected rows carried across the
group's span (`elim.perp_span` at `elim.collect_row_span`) and the
residual assembled at `elim.resid_perp_ext`. -/
private theorem carrier_perp_step (B Q Bl : List HVec)
    (hszB : ∀ x ∈ B, sized x)
    (hszQ : ∀ x ∈ Q, sized x)
    (hszBl : ∀ x ∈ Bl, sized x)
    (hQperp : ∀ x ∈ Q, ∀ k, k < (groupAt B x.content).length →
      (elim.dotP x.coords
        (ground.getAt [] (groupAt B x.content) k)).oneValue
        BPair.unit)
    (hBperp : ∀ x ∈ Bl, ∀ k, k < (groupAt B x.content).length →
      (elim.dotP x.coords
        (ground.getAt [] (groupAt B x.content) k)).oneValue
        BPair.unit) :
    ∀ y ∈ residCarrier Q Bl, ∀ k,
      k < (groupAt B y.content).length →
      (elim.dotP y.coords
        (ground.getAt [] (groupAt B y.content) k)).oneValue
        BPair.unit := by
  intro y hy k hk
  match residCarrier_mem Q Bl y hy with
  | ⟨_, x, hxQ, hyx⟩ =>
    subst hyx
    have hsx : x.coords.length
        = (places.monomialsAt x.content).length := hszQ x hxQ
    have hGrows : elim.rowsLen x.coords.length
        (groupAt Bl x.content) := by
      rw [hsx]
      exact rowsLen_groupAt x.content Bl hszBl
    have hCrows := elim.collect_rowsLen x.coords.length
      (groupAt Bl x.content) hGrows
    have hBrows : elim.rowsLen x.coords.length
        (groupAt B x.content) := by
      rw [hsx]
      exact rowsLen_groupAt x.content B hszB
    have hrlen : (ground.getAt ([] : List BPair)
        (groupAt B x.content) k).length = x.coords.length :=
      elim.rowsLen_getAt _ k hBrows hk
    have hGr : ∀ k2, k2 < (groupAt Bl x.content).length →
        (elim.dotP (ground.getAt ([] : List BPair)
          (groupAt B x.content) k)
          (ground.getAt [] (groupAt Bl x.content) k2)).oneValue
          BPair.unit := by
      intro k2 hk2
      match groupAt_rows (fun v => v ∈ Bl) Bl (fun _ hv => hv)
          x.content k2 hk2 with
      | ⟨q, hqBl, hqc, hqrow⟩ =>
        rw [hqrow, elim.dotP_comm]
        have h := hBperp q hqBl
        rw [hqc] at h
        exact h k hk
    have hCr : ∀ k2, k2 < (elim.collectOf x.coords.length
        (groupAt Bl x.content)).length →
        (elim.dotP (ground.getAt []
          (elim.collectOf x.coords.length
            (groupAt Bl x.content)) k2)
          (ground.getAt [] (groupAt B x.content) k)).oneValue
          BPair.unit := by
      intro k2 hk2
      rw [elim.dotP_comm]
      exact elim.perp_span x.coords.length (groupAt Bl x.content)
        _ _ hGrows hrlen hGr
        (elim.collect_row_span _ _ hGrows k2 hk2)
    show (elim.dotP (elim.residV x.coords.length
        (elim.collectOf x.coords.length (groupAt Bl x.content))
        x.coords)
      (ground.getAt [] (groupAt B x.content) k)).oneValue
      BPair.unit
    exact elim.resid_perp_ext x.coords.length _ x.coords _ hCrows rfl
      hrlen (hQperp x hxQ k hk) hCr

/-- The residual carrier pairs its own block at the sum's unit:
the residual sits against every collected row (`elim.resid_perp`)
and each group row sits inside the collection's span
(`elim.collect_span_row`), so `elim.perp_span` closes the display
at the block's own group. -/
private theorem resid_perp_own (Q Bl : List HVec)
    (hszQ : ∀ x ∈ Q, sized x) (hszBl : ∀ x ∈ Bl, sized x) :
    ∀ y ∈ residCarrier Q Bl, ∀ k,
      k < (groupAt Bl y.content).length →
      (elim.dotP y.coords
        (ground.getAt [] (groupAt Bl y.content) k)).oneValue
        BPair.unit := by
  intro y hy k hk
  match residCarrier_mem Q Bl y hy with
  | ⟨_, x, hxQ, hyx⟩ =>
    subst hyx
    have hsx : x.coords.length
        = (places.monomialsAt x.content).length := hszQ x hxQ
    have hGrows : elim.rowsLen x.coords.length
        (groupAt Bl x.content) := by
      rw [hsx]
      exact rowsLen_groupAt x.content Bl hszBl
    have hCrows := elim.collect_rowsLen x.coords.length
      (groupAt Bl x.content) hGrows
    have hrlen : (elim.residV x.coords.length
        (elim.collectOf x.coords.length (groupAt Bl x.content))
        x.coords).length = x.coords.length :=
      elim.length_residV _ _ x.coords hCrows rfl
    show (elim.dotP (elim.residV x.coords.length
        (elim.collectOf x.coords.length (groupAt Bl x.content))
        x.coords)
      (ground.getAt [] (groupAt Bl x.content) k)).oneValue
      BPair.unit
    refine elim.perp_span x.coords.length
      (elim.collectOf x.coords.length (groupAt Bl x.content))
      _ _ hCrows hrlen ?_
      (elim.collect_span_row _ _ hGrows k hk)
    intro k2 hk2
    rw [elim.dotP_comm]
    exact elim.resid_perp x.coords.length _ x.coords hCrows rfl
      k2 hk2

/-- The descent keeps a stated perpendicular read: each round's
block carries the pick's own display through the closure
(`pool_perp`) and the residual carrier carries it to the next
round (`carrier_perp_step`), so every member of the produced
blocks' join pairs the external pool's groups at the sum's
unit. -/
private theorem exhaustGo_perp (d : Nat) (B : List HVec)
    (hszB : ∀ x ∈ B, sized x)
    (hclB : ∀ x ∈ B, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt B (act i j x)) :
    ∀ (fuel : Nat) (Q : List HVec),
    (∀ x ∈ Q, sized x) →
    (∀ x ∈ Q, x.content.length = d) →
    (∀ x ∈ Q, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt Q (act i j x)) →
    (∀ x ∈ Q, ∀ k, k < (groupAt B x.content).length →
      (elim.dotP x.coords
        (ground.getAt [] (groupAt B x.content) k)).oneValue
        BPair.unit) →
    ∀ y ∈ blockJoin d (exhaustGo d fuel Q), ∀ k,
      k < (groupAt B y.content).length →
      (elim.dotP y.coords
        (ground.getAt [] (groupAt B y.content) k)).oneValue
        BPair.unit
  | 0, _, _, _, _, _, _, hy => nomatch hy
  | fuel + 1, Q, hsz, hwid, hcl, hperp, y, hy => by
    match exhaustGo_split d fuel Q with
    | .inl ⟨_, hcn⟩ =>
      rw [hcn] at hy
      exact nomatch hy
    | .inr ⟨w0, hp, hcn⟩ =>
      rw [hcn] at hy
      have hw0Q := pickTop_mem Q w0 hp
      obtain ⟨hszBl, _, _, hclBl, _, _, _⟩ :=
        block_pack d Q hsz hwid hcl w0 hp
      have hBlperp : ∀ x ∈ blockOf d w0, ∀ k,
          k < (groupAt B x.content).length →
          (elim.dotP x.coords
            (ground.getAt [] (groupAt B x.content) k)).oneValue
            BPair.unit := by
        match seedSpan_prov d (lowerspan.ht w0.content) w0 with
        | ⟨tailB, htlB, hprovB⟩ =>
          intro x hx
          have hpp := pool_perp d B hszB hclB w0 (hsz w0 hw0Q)
            (hwid w0 hw0Q) (hperp w0 hw0Q) tailB hprovB
          refine (hpp x ?_).2.2
          rw [← htlB]
          exact hx
      have hy' : y ∈ blockOf d w0
          ++ blockJoin d (exhaustGo d fuel
            (residCarrier Q (blockOf d w0))) := hy
      match ground.mem_append_of _ _ hy' with
      | Or.inl hh => exact hBlperp y hh
      | Or.inr ht =>
        exact exhaustGo_perp d B hszB hclB fuel _
          (residCarrier_sized Q (blockOf d w0) hsz hszBl)
          (residCarrier_width d Q (blockOf d w0) hwid)
          (residCarrier_closed d Q (blockOf d w0) hsz hwid hcl
            hszBl hclBl)
          (carrier_perp_step B Q (blockOf d w0) hszB hsz hszBl
            hperp hBlperp)
          y ht

/-- A listed top's block sits inside the produced blocks' join, the
joined image family's membership read. -/
private theorem mem_blockJoin_mem (d : Nat) :
    ∀ (ws : List HVec), ∀ w ∈ ws, ∀ y ∈ blockOf d w,
      y ∈ blockJoin d ws
  | [], _, hw, _, _ => nomatch hw
  | v :: t, w, hw, y, hy => by
    show y ∈ blockOf d v ++ blockJoin d t
    match w, hw with
    | _, List.Mem.head _ => exact List.mem_append_left _ hy
    | w', List.Mem.tail _ hwt =>
      exact List.mem_append_right _
        (mem_blockJoin_mem d t w' hwt y hy)

/-- The produced blocks are pairwise perpendicular along the
descent: a later round's block sits inside the join the workhorse
reads against the earlier round's own block, whose display at the
earlier round's residual carrier is that carrier's own
(`resid_perp_own`). -/
private theorem exhaustGo_perp_pair (d : Nat) :
    ∀ (fuel : Nat) (Q : List HVec),
    (∀ x ∈ Q, sized x) →
    (∀ x ∈ Q, x.content.length = d) →
    (∀ x ∈ Q, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt Q (act i j x)) →
    ∀ (a b : Nat), a < b → b < (exhaustGo d fuel Q).length →
    ∀ y ∈ blockOf d (ground.getAt (⟨[], []⟩ : HVec)
        (exhaustGo d fuel Q) b), ∀ k,
      k < (groupAt (blockOf d (ground.getAt (⟨[], []⟩ : HVec)
        (exhaustGo d fuel Q) a)) y.content).length →
      (elim.dotP y.coords (ground.getAt []
        (groupAt (blockOf d (ground.getAt (⟨[], []⟩ : HVec)
          (exhaustGo d fuel Q) a)) y.content) k)).oneValue
        BPair.unit
  | 0, _, _, _, _, _, b, _, hb, _, _ =>
    absurd hb (Nat.not_lt_zero b)
  | fuel + 1, Q, hsz, hwid, hcl, a, b, hab, hb, y, hy => by
    match exhaustGo_split d fuel Q with
    | .inl ⟨_, hcn⟩ =>
      rw [hcn] at hb
      exact absurd hb (Nat.not_lt_zero b)
    | .inr ⟨w0, hp, hcn⟩ =>
      rw [hcn] at hb hy ⊢
      obtain ⟨hszBl, _, _, hclBl, _, _, _⟩ :=
        block_pack d Q hsz hwid hcl w0 hp
      have hQsz := residCarrier_sized Q (blockOf d w0) hsz hszBl
      have hQwid := residCarrier_width d Q (blockOf d w0) hwid
      have hQcl := residCarrier_closed d Q (blockOf d w0) hsz hwid
        hcl hszBl hclBl
      match b, hab, hb, hy with
      | 0, hab0, _, _ => exact absurd hab0 (Nat.not_lt_zero a)
      | b' + 1, hab1, hb1, hy1 =>
        have hb1' : b' < (exhaustGo d fuel
            (residCarrier Q (blockOf d w0))).length :=
          Nat.lt_of_succ_lt_succ hb1
        match a, hab1 with
        | 0, _ =>
          exact exhaustGo_perp d (blockOf d w0) hszBl hclBl fuel _
            hQsz hQwid hQcl
            (resid_perp_own Q (blockOf d w0) hsz hszBl) y
            (mem_blockJoin_mem d _ _
              (ground.mem_getAt (⟨[], []⟩ : HVec) _ b' hb1') y hy1)
        | a' + 1, hab2 =>
          exact exhaustGo_perp_pair d fuel _ hQsz hQwid hQcl a' b'
            (Nat.lt_of_succ_lt_succ hab2) hb1' y hy1

/-- The produced blocks are pairwise perpendicular, the orthogonal
sum's read (`lem:blockcount`(i)): a later block's rows against an
earlier block's read the sum's unit at every content, the
complement's invariance (`lem:orthsplit`) run along the descent. -/
theorem exhaust_perp (d : Nat) (P : List HVec)
    (hsz : ∀ x ∈ P, sized x)
    (hwid : ∀ x ∈ P, x.content.length = d)
    (hcl : ∀ x ∈ P, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt P (act i j x))
    (a b : Nat) (hab : a < b) (hb : b < (exhaust d P).length)
    (nu : List Nat) :
    ∀ k, k < (groupAt (blockOf d
        (ground.getAt (⟨[], []⟩ : HVec) (exhaust d P) a)) nu).length →
    ∀ l, l < (groupAt (blockOf d
        (ground.getAt (⟨[], []⟩ : HVec) (exhaust d P) b)) nu).length →
      (elim.dotP
        (ground.getAt [] (groupAt (blockOf d
          (ground.getAt (⟨[], []⟩ : HVec) (exhaust d P) a)) nu) k)
        (ground.getAt [] (groupAt (blockOf d
          (ground.getAt (⟨[], []⟩ : HVec) (exhaust d P) b)) nu) l)).oneValue
        BPair.unit := by
  intro k hk l hl
  match groupAt_rows
      (fun v => v ∈ blockOf d (ground.getAt (⟨[], []⟩ : HVec)
        (exhaust d P) b))
      (blockOf d (ground.getAt (⟨[], []⟩ : HVec) (exhaust d P) b))
      (fun _ hv => hv) nu l hl with
  | ⟨y, hyB, hyc, hyrow⟩ =>
    rw [hyrow, elim.dotP_comm]
    have h := exhaustGo_perp_pair d P.length P hsz hwid hcl a b
      hab hb y hyB
    rw [hyc] at h
    exact h k hk

/-- A settled read composes along the carriers: at a pool whose
every member settles in a second pool, a settled vector settles
there too — the unit-family disjunct transports outright and the
span disjunct rides the transitivity at the members' settled rows
(`elim.spanRel_trans`). -/
private theorem settled_compose (Q P : List HVec)
    (hszQ : ∀ x ∈ Q, sized x) (hszP : ∀ x ∈ P, sized x)
    (hQP : ∀ q ∈ Q, settledAt P q)
    (y : HVec) (hszy : sized y) (h : settledAt Q y) :
    settledAt P y := by
  match h with
  | Or.inl hu => exact Or.inl hu
  | Or.inr hs =>
    refine Or.inr ?_
    have hQrows : elim.rowsLen y.coords.length
        (groupAt Q y.content) := by
      rw [hszy]
      exact rowsLen_groupAt y.content Q hszQ
    have hProws : elim.rowsLen y.coords.length
        (groupAt P y.content) := by
      rw [hszy]
      exact rowsLen_groupAt y.content P hszP
    refine elim.spanRel_trans y.coords.length (groupAt Q y.content)
      (groupAt P y.content) y.coords hQrows hProws ?_ hs
    intro k hk
    match groupAt_rows (fun v => v ∈ Q) Q (fun _ hv => hv)
        y.content k hk with
    | ⟨q, hqQ, hqc, hqrow⟩ =>
      rw [hqrow]
      have h2 := settled_to_span P q hszP (hszQ q hqQ) (hQP q hqQ)
      rw [hqc] at h2
      have hqlen : q.coords.length = y.coords.length := by
        rw [hszQ q hqQ, hqc, ← hszy]
      exact spanRel_cast _ _ _ _ h2 hqlen

/-- The residual carrier's members settle in the stated pool: the
member's own coordinates sit in its content group's span and the
block's rows sit there too, so the residual — the collection's
residual at that member — stays inside it
(`elim.spanRel_residV`). -/
private theorem residCarrier_settled (P Q Bl : List HVec)
    (hszP : ∀ x ∈ P, sized x)
    (hszQ : ∀ x ∈ Q, sized x)
    (hszBl : ∀ x ∈ Bl, sized x)
    (hQP : ∀ x ∈ Q, settledAt P x)
    (hBlP : ∀ x ∈ Bl, settledAt P x) :
    ∀ y ∈ residCarrier Q Bl, settledAt P y := by
  intro y hy
  match residCarrier_mem Q Bl y hy with
  | ⟨_, x, hxQ, hyx⟩ =>
    subst hyx
    have hsx : x.coords.length
        = (places.monomialsAt x.content).length := hszQ x hxQ
    have hGrows : elim.rowsLen x.coords.length
        (groupAt Bl x.content) := by
      rw [hsx]
      exact rowsLen_groupAt x.content Bl hszBl
    have hCrows := elim.collect_rowsLen x.coords.length
      (groupAt Bl x.content) hGrows
    have hProws : elim.rowsLen x.coords.length
        (groupAt P x.content) := by
      rw [hsx]
      exact rowsLen_groupAt x.content P hszP
    have hxspan : elim.spanRel x.coords.length
        (groupAt P x.content) x.coords :=
      settled_to_span P x hszP (hszQ x hxQ) (hQP x hxQ)
    have hGspan : ∀ k, k < (groupAt Bl x.content).length →
        elim.spanRel x.coords.length (groupAt P x.content)
          (ground.getAt [] (groupAt Bl x.content) k) := by
      intro k hk
      match groupAt_rows (fun v => v ∈ Bl) Bl (fun _ hv => hv)
          x.content k hk with
      | ⟨q, hqBl, hqc, hqrow⟩ =>
        rw [hqrow]
        have h2 := settled_to_span P q hszP (hszBl q hqBl)
          (hBlP q hqBl)
        rw [hqc] at h2
        have hqlen : q.coords.length = x.coords.length := by
          rw [hszBl q hqBl, hqc, ← hsx]
        exact spanRel_cast _ _ _ _ h2 hqlen
    have hCspan : ∀ k, k < (elim.collectOf x.coords.length
        (groupAt Bl x.content)).length →
        elim.spanRel x.coords.length (groupAt P x.content)
          (ground.getAt [] (elim.collectOf x.coords.length
            (groupAt Bl x.content)) k) :=
      fun k hk => elim.spanRel_trans _ (groupAt Bl x.content) _ _
        hGrows hProws hGspan
        (elim.collect_row_span _ _ hGrows k hk)
    have hres := elim.spanRel_residV x.coords.length
      (elim.collectOf x.coords.length (groupAt Bl x.content))
      (groupAt P x.content) x.coords hCrows rfl hProws hCspan
      hxspan
    refine Or.inr ?_
    show elim.spanRel (elim.residV x.coords.length
        (elim.collectOf x.coords.length (groupAt Bl x.content))
        x.coords).length (groupAt P x.content)
      (elim.residV x.coords.length
        (elim.collectOf x.coords.length (groupAt Bl x.content))
        x.coords)
    rw [elim.length_residV _ _ x.coords hCrows rfl]
    exact hres

/-- The descent's blocks settle in the stated carrier: the round's
pick is a carrier member and its closure walks the settled read
through the provenance (`block_pack`), while the residual
carrier's members settle in the carrier
(`residCarrier_settled`), so the later rounds' settled reads
compose back (`settled_compose`). -/
private theorem exhaustGo_settle (d : Nat) :
    ∀ (fuel : Nat) (P : List HVec),
    (∀ x ∈ P, sized x) →
    (∀ x ∈ P, x.content.length = d) →
    (∀ x ∈ P, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt P (act i j x)) →
    ∀ y ∈ blockJoin d (exhaustGo d fuel P),
      sized y ∧ y.content.length = d ∧ settledAt P y
  | 0, _, _, _, _, _, hy => nomatch hy
  | fuel + 1, P, hsz, hwid, hcl, y, hy => by
    match exhaustGo_split d fuel P with
    | .inl ⟨_, hcn⟩ =>
      rw [hcn] at hy
      exact nomatch hy
    | .inr ⟨w0, hp, hcn⟩ =>
      rw [hcn] at hy
      obtain ⟨hszBl, hwidBl, _, hclBl, hsetBl, _, _⟩ :=
        block_pack d P hsz hwid hcl w0 hp
      have hy' : y ∈ blockOf d w0
          ++ blockJoin d (exhaustGo d fuel
            (residCarrier P (blockOf d w0))) := hy
      match ground.mem_append_of _ _ hy' with
      | Or.inl hh =>
        exact ⟨hszBl y hh, hwidBl y hh, hsetBl y hh⟩
      | Or.inr ht =>
        have hQsz := residCarrier_sized P (blockOf d w0) hsz hszBl
        have hQwid := residCarrier_width d P (blockOf d w0) hwid
        have hQcl := residCarrier_closed d P (blockOf d w0) hsz
          hwid hcl hszBl hclBl
        have hIH := exhaustGo_settle d fuel _ hQsz hQwid hQcl y ht
        refine ⟨hIH.1, hIH.2.1, ?_⟩
        exact settled_compose _ P hQsz hsz
          (residCarrier_settled P P (blockOf d w0) hsz hsz hszBl
            (member_settled P hsz) hsetBl)
          y hIH.1 hIH.2.2

/-- Every produced block member settles in the stated carrier: the
seed is a carrier member's own read and the closure's lowerings
settle at the carrier's closure (`lem:lowerspan`). -/
theorem exhaust_settle (d : Nat) (P : List HVec)
    (hsz : ∀ x ∈ P, sized x)
    (hwid : ∀ x ∈ P, x.content.length = d)
    (hcl : ∀ x ∈ P, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt P (act i j x)) :
    ∀ y ∈ blockJoin d (exhaust d P),
      sized y ∧ y.content.length = d ∧ settledAt P y :=
  exhaustGo_settle d P.length P hsz hwid hcl

/-- The descent's join is independent at every content: the round's
block is independent at its own closure data (`block_pack`), the
rest of the descent by the recursion, and the two sides are
perpendicular at every content (the workhorse at the round's own
block), so the joined group is independent
(`elim.indep_append_perp` at `groupAt_append`). -/
private theorem exhaustGo_indep (d : Nat) :
    ∀ (fuel : Nat) (Q : List HVec),
    (∀ x ∈ Q, sized x) →
    (∀ x ∈ Q, x.content.length = d) →
    (∀ x ∈ Q, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt Q (act i j x)) →
    indepAll (blockJoin d (exhaustGo d fuel Q))
  | 0, _, _, _, _ => by
    intro mu hmu
    exact nomatch hmu
  | fuel + 1, Q, hsz, hwid, hcl => by
    match exhaustGo_split d fuel Q with
    | .inl ⟨_, hcn⟩ =>
      rw [hcn]
      intro mu hmu
      exact nomatch hmu
    | .inr ⟨w0, hp, hcn⟩ =>
      rw [hcn]
      obtain ⟨hszBl, _, hindBl, hclBl, _, _, _⟩ :=
        block_pack d Q hsz hwid hcl w0 hp
      have hQsz := residCarrier_sized Q (blockOf d w0) hsz hszBl
      have hQwid := residCarrier_width d Q (blockOf d w0) hwid
      have hQcl := residCarrier_closed d Q (blockOf d w0) hsz hwid
        hcl hszBl hclBl
      have hIH := exhaustGo_indep d fuel _ hQsz hQwid hQcl
      have hCsz : ∀ z ∈ blockJoin d (exhaustGo d fuel
          (residCarrier Q (blockOf d w0))), sized z :=
        blockJoin_sized d _ (exhaustGo_pack d fuel _ hQsz hQwid)
      have hperpC : ∀ z ∈ blockJoin d (exhaustGo d fuel
          (residCarrier Q (blockOf d w0))), ∀ k,
          k < (groupAt (blockOf d w0) z.content).length →
          (elim.dotP z.coords (ground.getAt []
            (groupAt (blockOf d w0) z.content) k)).oneValue
            BPair.unit :=
        exhaustGo_perp d (blockOf d w0) hszBl hclBl fuel _
          hQsz hQwid hQcl
          (resid_perp_own Q (blockOf d w0) hsz hszBl)
      intro mu _
      show elim.indepRows (places.monomialsAt mu).length
        (groupAt (blockOf d w0 ++ blockJoin d (exhaustGo d fuel
          (residCarrier Q (blockOf d w0)))) mu)
      rw [groupAt_append]
      refine elim.indep_append_perp (places.monomialsAt mu).length
        _ _ (rowsLen_groupAt mu _ hszBl) (rowsLen_groupAt mu _ hCsz)
        (indepAll_all hindBl mu) (indepAll_all hIH mu) ?_
      intro k hk l hl
      match groupAt_rows (fun v => v ∈ blockJoin d (exhaustGo d fuel
          (residCarrier Q (blockOf d w0))))
          (blockJoin d (exhaustGo d fuel
            (residCarrier Q (blockOf d w0))))
          (fun _ hv => hv) mu l hl with
      | ⟨z, hzC, hzc, hzrow⟩ =>
        rw [hzrow, elim.dotP_comm]
        have h := hperpC z hzC
        rw [hzc] at h
        exact h k hk

/-- The produced blocks' join is independent at every content, the
orthogonal sum's graded count read: per-block independence at the
closure's own data with the blocks pairwise perpendicular
(`elim.indep_append_perp`). -/
theorem exhaust_indep (d : Nat) (P : List HVec)
    (hsz : ∀ x ∈ P, sized x)
    (hwid : ∀ x ∈ P, x.content.length = d)
    (hcl : ∀ x ∈ P, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt P (act i j x)) :
    indepAll (blockJoin d (exhaust d P)) :=
  exhaustGo_indep d P.length P hsz hwid hcl

/-! The exhaustion count, `lem:blockcount`(ii)'s closing sentence:
the stated carrier's count reads the produced tops' occupancy at
the content — each round's block reads one count at its own head
content, the counts add over the orthogonal split, and the round's
congruence carries the carrier's own read across the join. -/

/-- A carrier at the sum's unit throughout reads the count at
nought: every group row is unit-tailed, the collection is vacant
(`elim.collect_nil_of_units`), and the kernel dimension reads the
vacant list's own. -/
theorem countAt_of_units (Q : List HVec) (mu : List Nat)
    (hrows : ∀ k, k < (groupAt Q mu).length →
      poly.unitTail (ground.getAt ([] : List BPair)
        (groupAt Q mu) k)) : countAt Q mu = 0 := by
  have hc := elim.collect_nil_of_units
    (places.monomialsAt mu).length (groupAt Q mu) hrows
  show elim.kernelDim
    (elim.collectOf (places.monomialsAt mu).length
        (groupAt Q mu)).length
    (elim.crossM (units.stackedRaise mu)
      (elim.collectOf (places.monomialsAt mu).length
        (groupAt Q mu))) = 0
  rw [hc]
  show (0 : Nat) - elim.rank (elim.crossM (units.stackedRaise mu)
    (elim.collectOf (places.monomialsAt mu).length
      ([] : elim.Mat))) = 0
  exact Nat.zero_sub _

/-- A member-level perpendicular display reads at the group level:
a row of the second carrier's group at a content is that carrier's
own member at it, so the stated display closes the pairing
(`elim.dotP_comm` at the flip). -/
private theorem perp_group_pair (Bl R : List HVec)
    (h : ∀ y ∈ R, ∀ k, k < (groupAt Bl y.content).length →
      (elim.dotP y.coords
        (ground.getAt [] (groupAt Bl y.content) k)).oneValue
        BPair.unit)
    (nu : List Nat) :
    ∀ k, k < (groupAt Bl nu).length →
    ∀ l, l < (groupAt R nu).length →
      (elim.dotP (ground.getAt [] (groupAt Bl nu) k)
        (ground.getAt [] (groupAt R nu) l)).oneValue
        BPair.unit := by
  intro k hk l hl
  match groupAt_rows (fun v => v ∈ R) R (fun _ hv => hv)
      nu l hl with
  | ⟨y, hyR, hyc, hyrow⟩ =>
    rw [hyrow, elim.dotP_comm]
    have hy := h y hyR
    rw [hyc] at hy
    exact hy k hk

/-- The all-pairs closure reads at the adjacent moves bounded by a
stated content's own length: inside the letter width the closure's
own data, and at or beyond it the action is vacant at the width's
entry default (`ground.getAt_over` at `tops.act_null`). -/
private theorem adj_closed_of (d : Nat) (R : List HVec)
    (hwid : ∀ x ∈ R, x.content.length = d)
    (hcl : ∀ x ∈ R, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt R (act i j x)) :
    ∀ x ∈ R, ∀ i : Nat,
      settledAt R (act i (i + 1) x) := by
  intro x hx i
  match Nat.lt_or_ge (i + 1) d with
  | .inl hlt =>
    exact hcl x hx i (Nat.lt_trans (Nat.lt_succ_self i) hlt)
      (i + 1) hlt (Nat.ne_of_lt (Nat.lt_succ_self i))
  | .inr hge =>
    refine Or.inl (allU_of_unitTail _
      (tops.act_null i (i + 1) x ?_))
    exact ground.getAt_over 0 x.content (i + 1)
      (by rw [hwid x hx]; exact hge)

/-- The exhaustion count at the stated fuel: the refused round
reads both sides at nought (`countAt_of_units`), and a round's pick
splits the carrier's count at the block joined to its residual
carrier — the congruence at the two-sided spans (`countAt_congr`),
the counts adding over the orthogonal split (`countAt_append`), the
block's own delta at its head content (`countAt_block`), and the
residual carrier recursed at the strictly shortened length. -/
private theorem countAt_exhaustGo (d : Nat) (mu : List Nat) :
    ∀ (fuel : Nat) (Q : List HVec),
    (∀ x ∈ Q, sized x) →
    (∀ x ∈ Q, x.content.length = d) →
    (∀ x ∈ Q, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt Q (act i j x)) →
    Q.length ≤ fuel →
    countAt Q mu = occ mu (exhaustGo d fuel Q)
  | 0, [], _, _, _, _ => by
    show countAt ([] : List HVec) mu = 0
    exact countAt_of_units [] mu (fun _ hk => nomatch hk)
  | 0, _ :: t, _, _, _, hfuel =>
    absurd hfuel (Nat.not_succ_le_zero t.length)
  | fuel + 1, Q, hsz, hwid, hcl, hfuel => by
    match exhaustGo_split d fuel Q with
    | .inl ⟨hpn, hc⟩ =>
      rw [hc]
      show countAt Q mu = 0
      refine countAt_of_units Q mu ?_
      intro k hk
      match groupAt_rows (fun v => v ∈ Q) Q (fun _ hv => hv)
          mu k hk with
      | ⟨y, hyQ, _, hyrow⟩ =>
        rw [hyrow]
        exact unitTail_of_allU y.coords (pickTop_none Q hpn y hyQ)
    | .inr ⟨w0, hp, hc⟩ =>
      rw [hc]
      have hw0Q := pickTop_mem Q w0 hp
      have htop0 := pickTop_top d Q hwid hcl w0 hp
      obtain ⟨hszBl, hwidBl, _, hclBl, hsetBl, _, _⟩ :=
        block_pack d Q hsz hwid hcl w0 hp
      have hQsz := residCarrier_sized Q (blockOf d w0) hsz hszBl
      have hQwid := residCarrier_width d Q (blockOf d w0) hwid
      have hQcl := residCarrier_closed d Q (blockOf d w0) hsz hwid
        hcl hszBl hclBl
      have hQfuel : (residCarrier Q (blockOf d w0)).length ≤ fuel :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le
          (residCarrier_len_lt Q _ w0 hw0Q
            (pick_resid_unit d Q hsz hwid w0 hp)) hfuel)
      have hszJ : ∀ x ∈ blockOf d w0 ++ residCarrier Q (blockOf d w0),
          sized x := by
        intro x hxJ
        match ground.mem_append_of _ _ hxJ with
        | Or.inl hh => exact hszBl x hh
        | Or.inr ht => exact hQsz x ht
      have hsetJ : ∀ y ∈ blockOf d w0
          ++ residCarrier Q (blockOf d w0),
          elim.spanRel y.coords.length (groupAt Q y.content)
            y.coords := by
        intro y hy
        match ground.mem_append_of _ _ hy with
        | Or.inl hh =>
          exact settled_to_span Q y hsz (hszBl y hh) (hsetBl y hh)
        | Or.inr ht =>
          exact settled_to_span Q y hsz (hQsz y ht)
            (residCarrier_settled Q Q (blockOf d w0) hsz hsz hszBl
              (member_settled Q hsz) hsetBl y ht)
      have hcong : countAt Q mu
          = countAt (blockOf d w0
              ++ residCarrier Q (blockOf d w0)) mu :=
        countAt_congr mu Q _ hsz hszJ
          (group_span_rows Q _ mu hsz
            (carrier_span_split Q (blockOf d w0) hsz hszBl))
          (group_span_rows _ Q mu hszJ hsetJ)
      have hperp := perp_group_pair (blockOf d w0)
        (residCarrier Q (blockOf d w0))
        (resid_perp_own Q (blockOf d w0) hsz hszBl)
      have hsplit : countAt (blockOf d w0
            ++ residCarrier Q (blockOf d w0)) mu
          = countAt (blockOf d w0) mu
            + countAt (residCarrier Q (blockOf d w0)) mu :=
        countAt_append mu (blockOf d w0)
          (residCarrier Q (blockOf d w0)) hszBl hQsz
          (fun x hx i _ => adj_closed_of d (blockOf d w0)
            hwidBl hclBl x hx i)
          (fun x hx i _ => adj_closed_of d
            (residCarrier Q (blockOf d w0))
            hQwid hQcl x hx i)
          (hperp mu)
          (fun i _ => hperp (moveAt i (i + 1) mu))
      match lowerspan.seed_closed d (lowerspan.ht w0.content) w0
          (hsz w0 hw0Q) (hwid w0 hw0Q) (pickTop_off Q w0 hp)
          (fun jr hjr => htop0 (jr + 1) hjr jr
            (Nat.lt_succ_self jr))
          (Nat.le_refl _) with
      | ⟨tailB, htlB, hszB', hwidB', hprovB', _, hsetB'⟩ =>
        have hhead : countAt (blockOf d w0) mu
            = if mu = w0.content then 1 else 0 := by
          rw [blockOf_eq, htlB]
          exact countAt_block d w0 tailB hszB' hwidB' hprovB'
            hsetB' (pickTop_off Q w0 hp) mu
        have hIH := countAt_exhaustGo d mu fuel
          (residCarrier Q (blockOf d w0)) hQsz hQwid hQcl hQfuel
        show countAt Q mu
          = (if w0.content = mu then 1 else 0)
            + occ mu (exhaustGo d fuel
                (residCarrier Q (blockOf d w0)))
        rw [hcong, hsplit, hhead, hIH]
        by_cases hmu : mu = w0.content
        · rw [if_pos hmu, if_pos hmu.symm]
        · rw [if_neg hmu, if_neg (fun he => hmu he.symm)]

/-- The count is the exhaustion's own block count
(`lem:blockcount`(ii)'s closing sentence): at the stated carrier
the kernel-dimension read equals the produced tops' occupancy at
the content — the descent's blocks read one count each at their
own head contents (`countAt_block`) with the counts adding over
the orthogonal split (`countAt_append`) and the carrier's own read
riding the spans' congruence (`countAt_congr`); the left side is
the carrier's read alone, so every exhaustion of every carrier of
one span reads it, the congruence the "every".  Binders: hsz/hwid
the member-entry enumeration (`con:places`; `con:gentable`'s
coordinate list); hcl the closure read's stated data
(`lem:blockirr`), load-bearing with its committed refusal. -/
theorem countAt_exhaust (d : Nat) (P : List HVec)
    (hsz : ∀ x ∈ P, sized x)
    (hwid : ∀ x ∈ P, x.content.length = d)
    (hcl : ∀ x ∈ P, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt P (act i j x))
    (mu : List Nat) :
    countAt P mu = occ mu (exhaust d P) :=
  countAt_exhaustGo d mu P.length P hsz hwid hcl (Nat.le_refl _)

/-- Every exhaustion reads the one block count, the closing
sentence's "every" (`lem:blockcount`(ii)): two stated carriers of
one span produce one occupancy at every content, each the shared
count's own read (`countAt_exhaust` at `countAt_congr`, the
count's well-definedness). -/
theorem occ_exhaust_congr (d : Nat) (P P' : List HVec)
    (mu : List Nat)
    (hsz : ∀ x ∈ P, sized x) (hsz' : ∀ x ∈ P', sized x)
    (hwid : ∀ x ∈ P, x.content.length = d)
    (hwid' : ∀ x ∈ P', x.content.length = d)
    (hcl : ∀ x ∈ P, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt P (act i j x))
    (hcl' : ∀ x ∈ P', ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt P' (act i j x))
    (h1 : ∀ k, k < (groupAt P mu).length →
      elim.spanRel (places.monomialsAt mu).length (groupAt P' mu)
        (ground.getAt [] (groupAt P mu) k))
    (h2 : ∀ k, k < (groupAt P' mu).length →
      elim.spanRel (places.monomialsAt mu).length (groupAt P mu)
        (ground.getAt [] (groupAt P' mu) k)) :
    occ mu (exhaust d P) = occ mu (exhaust d P') := by
  rw [← countAt_exhaust d P hsz hwid hcl mu,
    ← countAt_exhaust d P' hsz' hwid' hcl' mu]
  exact countAt_congr mu P P' hsz hsz' h1 h2

/-- The produced tops' fold regroups at the occupied contents'
index with the counts the carrier's own: any per-content weight's
fold over the exhaustion is the counted fold over the distinct
contents (`ground.famFold_partition` at `countAt_exhaust`). -/
private theorem exhaust_regroup (d : Nat) (P : List HVec)
    (hsz : ∀ x ∈ P, sized x)
    (hwid : ∀ x ∈ P, x.content.length = d)
    (hcl : ∀ x ∈ P, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt P (act i j x)) (F : List Nat → Nat) :
    ground.famFold Nat.add 0 (fun w => F w.content) (exhaust d P)
      = ground.famFold Nat.add 0 (fun nu => countAt P nu * F nu)
          (ground.dedupL ((exhaust d P).map HVec.content)) := by
  rw [← ground.famFold_map Nat.add 0 F HVec.content (exhaust d P),
    ground.famFold_partition F ((exhaust d P).map HVec.content)
      (ground.dedupL ((exhaust d P).map HVec.content))
      (fun x _ => ground.countOf_dedupL_le x _)
      (fun x hx => ground.mem_dedupL hx)]
  refine ground.famFold_congr_all Nat.add 0 _ _ ?_
    (ground.dedupL ((exhaust d P).map HVec.content))
  intro nu
  rw [← occ_eq_countOf nu (exhaust d P),
    ← countAt_exhaust d P hsz hwid hcl nu]

/-! The dimension display, `lem:blockcount`(ii): the graded
dimensions' fold over the occupied contents reads the carrier's own
counts against the block dimensions — the collections' counts pass
to the produced join's groups at the two-list exchange, the join's
length partitions over the contents, the per-top blocks read the
shapes' pool counts, and the tops' contents regroup at the
occupied contents' index. -/

/-- The dimension at a stated carrier: the graded dimensions'
fold over the occupied contents, each the collection's count
(`lem:lowerspan`'s joined-collection read). -/
def dimOf (pool : List HVec) : Nat :=
  ground.famFold Nat.add 0 (fun mu => dimAt pool mu)
    (ground.dedupL (pool.map HVec.content))

/-- A member's content is occupied in its own carrier, the
structural count's head read. -/
private theorem occ_pos_of_mem (l : List HVec) (y : HVec)
    (hy : y ∈ l) : 0 < occ y.content l := by
  rw [occ_eq_countOf]
  exact ground.countOf_pos_of_mem (ground.mem_map_to HVec.content hy)

/-- The collection's count passes to the produced join's group:
each list's rows sit in the other's span and each is independent,
the two-list exchange (`elim.span_count_eq` at `exhaust_span` and
`exhaust_settle`). -/
private theorem collect_blockJoin (d : Nat) (P : List HVec)
    (hsz : ∀ x ∈ P, sized x)
    (hwid : ∀ x ∈ P, x.content.length = d)
    (hcl : ∀ x ∈ P, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt P (act i j x)) (mu : List Nat) :
    dimAt P mu
      = (groupAt (blockJoin d (exhaust d P)) mu).length := by
  have hBJsz : ∀ y ∈ blockJoin d (exhaust d P), sized y :=
    fun y hy => (exhaust_settle d P hsz hwid hcl y hy).1
  have hBJset : ∀ y ∈ blockJoin d (exhaust d P), settledAt P y :=
    fun y hy => (exhaust_settle d P hsz hwid hcl y hy).2.2
  have hG : elim.rowsLen (places.monomialsAt mu).length
      (groupAt P mu) := rowsLen_groupAt mu P hsz
  have hA := elim.collect_rowsLen _ _ hG
  have hB : elim.rowsLen (places.monomialsAt mu).length
      (groupAt (blockJoin d (exhaust d P)) mu) :=
    rowsLen_groupAt mu _ hBJsz
  refine elim.span_count_eq (places.monomialsAt mu).length _ _
    hA hB (elim.collect_indep _ _ hG)
    (indepAll_all (exhaust_indep d P hsz hwid hcl) mu) ?_ ?_
  · intro k hk
    exact elim.spanRel_trans _ (groupAt P mu) _ _ hG hB
      (group_span_rows P (blockJoin d (exhaust d P)) mu hsz
        (exhaust_span d P hsz hwid))
      (elim.collect_row_span _ _ hG k hk)
  · intro k hk
    exact elim.spanRel_trans _ (groupAt P mu) _ _ hG hA
      (fun k2 hk2 => elim.collect_span_row _ _ hG k2 hk2)
      (group_span_rows (blockJoin d (exhaust d P)) P mu hBJsz
        (fun y hy =>
          settled_to_span P y hsz (hBJsz y hy) (hBJset y hy))
        k hk)

/-- The join's occupancy splits per top, the keyed union's count
read. -/
private theorem occ_blockJoin (d : Nat) (mu : List Nat)
    (ws : List HVec) :
    occ mu (blockJoin d ws)
      = ground.famFold Nat.add 0
          (fun w => occ mu (blockOf d w)) ws := by
  rw [occ_eq_countOf]
  show ground.countOf mu
    ((ws.flatMap (blockOf d)).map HVec.content) = _
  rw [ground.map_flatMap (blockOf d) HVec.content ws,
    ground.countOf_flatMap mu
      (fun w => (blockOf d w).map HVec.content) ws]
  exact ground.famFold_congr_all Nat.add 0 _ _
    (fun w => (occ_eq_countOf mu (blockOf d w)).symm) ws

/-- The dimension display (`lem:blockcount`(ii)):
dim M = sum over the contents of N_mu(M) at the block dimension
d_mu, the coefficients the carrier's own counts
(`countAt_exhaust`) and the block dimensions the shapes' pool
counts (`seedBlock_dim` at `lem:blockirr`(iv)).  The sum's stated
carrier is the tex's own sentence: one summand per distinct top
content of the exhaustion, each a shape's row list at the
dominance read (`lem:tops`(ii)), and a shape off the tops'
contents reading its count at the unit, the vacant collected
group's kernel — `countAt_exhaust` at the vacant occupancy. -/
theorem dimOf_countAt (d : Nat) (P : List HVec)
    (hsz : ∀ x ∈ P, sized x)
    (hwid : ∀ x ∈ P, x.content.length = d)
    (hcl : ∀ x ∈ P, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt P (act i j x)) :
    dimOf P = ground.famFold Nat.add 0
      (fun mu => countAt P mu * (blockSpan (shapeOf mu)).length)
      (ground.dedupL ((exhaust d P).map HVec.content)) := by
  -- the collections' counts at the produced join's groups
  have hstep1 : ∀ mu : List Nat,
      dimAt P mu
        = (groupAt (blockJoin d (exhaust d P)) mu).length :=
    collect_blockJoin d P hsz hwid hcl
  -- the produced members' contents are the carrier's own
  have hcov : ∀ y ∈ blockJoin d (exhaust d P),
      y.content ∈ P.map HVec.content := by
    intro y hy
    match Nat.eq_zero_or_pos
        (ground.countOf y.content (P.map HVec.content)) with
    | .inr hp => exact ground.mem_of_countOf_pos _ _ hp
    | .inl hz =>
      exfalso
      have hg : groupAt P y.content = [] :=
        groupAt_nil_of_countOf P y.content hz
      have h0 : occ y.content (blockJoin d (exhaust d P)) = 0 := by
        rw [← length_groupAt, ← hstep1 y.content]
        show (elim.collectOf
          (places.monomialsAt y.content).length
          (groupAt P y.content)).length = 0
        rw [hg]
        rfl
      have hpos := occ_pos_of_mem (blockJoin d (exhaust d P)) y hy
      rw [h0] at hpos
      exact absurd hpos (Nat.lt_irrefl 0)
  have hcovD : ∀ x ∈ (blockJoin d (exhaust d P)).map HVec.content,
      x ∈ ground.dedupL (P.map HVec.content) := by
    intro x hx
    match ground.mem_map_of HVec.content _ x hx with
    | ⟨y, hy, hyc⟩ =>
      rw [← hyc]
      exact ground.mem_dedupL (hcov y hy)
  -- the join's length partitions over the occupied contents
  have hstep2 : ground.famFold Nat.add 0
      (fun mu => (groupAt (blockJoin d (exhaust d P)) mu).length)
      (ground.dedupL (P.map HVec.content))
      = (blockJoin d (exhaust d P)).length := by
    rw [ground.famFold_congr_all Nat.add 0 _
      (fun mu => ground.countOf mu
        ((blockJoin d (exhaust d P)).map HVec.content))
      (fun mu => by rw [length_groupAt, occ_eq_countOf])
      (ground.dedupL (P.map HVec.content)),
      ground.countOf_partition
        ((blockJoin d (exhaust d P)).map HVec.content)
        (ground.dedupL (P.map HVec.content))
        (fun x _ => ground.countOf_dedupL_le x _) hcovD,
      ground.length_map HVec.content (blockJoin d (exhaust d P))]
  -- the join's length as the per-top blocks' fold
  have hstep3 : (blockJoin d (exhaust d P)).length
      = ground.famFold Nat.add 0 (fun w => (blockOf d w).length)
        (exhaust d P) := by
    rw [← ground.famFold_length (blockJoin d (exhaust d P))]
    show ground.famFold Nat.add 0 (fun _ => (1 : Nat))
      ((exhaust d P).flatMap (blockOf d)) = _
    rw [ground.famFold_flatMap (fun _ => (1 : Nat)) (blockOf d)
      (exhaust d P)]
    exact ground.famFold_congr_all Nat.add 0 _ _
      (fun w => ground.famFold_length (blockOf d w)) (exhaust d P)
  -- each block reads its shape's own pool count
  have hstep4 : ground.famFold Nat.add 0
      (fun w => (blockOf d w).length) (exhaust d P)
      = ground.famFold Nat.add 0
        (fun w => (blockSpan (shapeOf w.content)).length)
        (exhaust d P) := by
    refine ground.famFold_congr_members Nat.add 0 _ _
      (exhaust d P) ?_
    intro w hw
    obtain ⟨hszw, hwidw, hoffw, htopw⟩ := exhaust_top d P hsz hwid
      hcl w (ground.mem_of_countOf_pos w (exhaust d P) hw)
    exact seedBlock_dim d w hszw hwidw hoffw htopw
      (lowerspan.ht w.content) (Nat.le_refl _)
  show ground.famFold Nat.add 0 (fun mu => dimAt P mu)
    (ground.dedupL (P.map HVec.content)) = _
  rw [ground.famFold_congr_all Nat.add 0 _
      (fun mu => (groupAt (blockJoin d (exhaust d P)) mu).length)
      hstep1 (ground.dedupL (P.map HVec.content)),
    hstep2, hstep3, hstep4,
    exhaust_regroup d P hsz hwid hcl
      (fun nu => (blockSpan (shapeOf nu)).length)]

/-- The graded display (`lem:blockcount`(ii)'s refining sentence):
a content's dimension over the stated carrier is the display's sum
at the carrier's own counts against the blocks' occupancies at the
content — the collection's count passes to the produced join's
group (`collect_blockJoin`), the join's occupancy splits per top
(`occ_blockJoin`), each block reads its shape's own occupancy
(`seedBlock_occ` at `exhaust_top`'s data), and the tops' contents
regroup at the occupied contents' index with the counts the
carrier's own (`countAt_exhaust`). -/
theorem gradedDim_countAt (d : Nat) (P : List HVec)
    (hsz : ∀ x ∈ P, sized x)
    (hwid : ∀ x ∈ P, x.content.length = d)
    (hcl : ∀ x ∈ P, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt P (act i j x)) (mu : List Nat) :
    dimAt P mu
      = ground.famFold Nat.add 0
          (fun nu => countAt P nu
            * occ mu (blockSpan (shapeOf nu)))
          (ground.dedupL ((exhaust d P).map HVec.content)) := by
  -- each produced block reads its shape's own occupancy
  have hstep4 : ground.famFold Nat.add 0
      (fun w => occ mu (blockOf d w)) (exhaust d P)
      = ground.famFold Nat.add 0
        (fun w => occ mu (blockSpan (shapeOf w.content)))
        (exhaust d P) := by
    refine ground.famFold_congr_members Nat.add 0 _ _
      (exhaust d P) ?_
    intro w hw
    obtain ⟨hszw, hwidw, hoffw, htopw⟩ := exhaust_top d P hsz hwid
      hcl w (ground.mem_of_countOf_pos w (exhaust d P) hw)
    exact seedBlock_occ d w hszw hwidw hoffw htopw
      (lowerspan.ht w.content) (Nat.le_refl _) mu
  rw [collect_blockJoin d P hsz hwid hcl mu,
    length_groupAt mu (blockJoin d (exhaust d P)),
    occ_blockJoin d mu (exhaust d P), hstep4,
    exhaust_regroup d P hsz hwid hcl
      (fun nu => occ mu (blockSpan (shapeOf nu)))]

/-! `lem:blockcount`(iii)'s block transport: a provenance pool at a
top reads the fused count at the shape's own block.  The pool is
its head's word images (`blockirr.pool_words`); the fused count
collapses to the pair list's raw kernel dimension at the pairs'
independence (`countAt_pairs` at `tensor_indep`); the one word
family read at the shape's own top carries that dimension across
(`kernelDim_pairs_words`, the pairs' independence transported by
`tensor_indep_words`); and the word images at that top and the
shape's `blockSpan` span one another content by content
(`blockirr.word_span` with the saturation at the agreeing
occupancies, `blockirr.occ_le` both ways), so the two fused pools'
counts are one value (`tensor_span` both ways at
`countAt_congr`). -/

/-- An independent list inside a second list's span, at or above the
second's count, spans it back: a refused row would join the first
list one past its count while still sitting in the second's span,
against the exchange bound (`elim.indep_extend` at
`elim.span_count_le`; `lem:lowerspan`'s exchange clause). -/
private theorem span_saturate (n : Nat) (A B : elim.Mat)
    (hA : elim.rowsLen n A) (hB : elim.rowsLen n B)
    (hiA : elim.indepRows n A)
    (hAB : ∀ k, k < A.length → elim.spanRel n B (getAt [] A k))
    (hcount : B.length ≤ A.length) :
    ∀ k, k < B.length → elim.spanRel n A (getAt [] B k) := by
  intro k hk
  match (inferInstance : Decidable
      (elim.spanRel n A (getAt ([] : List BPair) B k))) with
  | isTrue h => exact h
  | isFalse hns =>
    exfalso
    have hv : (getAt ([] : List BPair) B k).length = n :=
      elim.rowsLen_getAt B k hB hk
    have hext := elim.indep_extend n A (getAt [] B k) hA hv hiA hns
    have hrows : elim.rowsLen n (A ++ [getAt ([] : List BPair) B k]) :=
      elim.rowsLen_append n hA ⟨hv, trivial⟩
    have hspan : ∀ j,
        j < (A ++ [getAt ([] : List BPair) B k]).length →
        elim.spanRel n B
          (getAt [] (A ++ [getAt ([] : List BPair) B k]) j) := by
      intro j hj
      rw [ground.length_append] at hj
      rw [ground.getAt_append]
      by_cases hjA : j < A.length
      · rw [if_pos hjA]
        exact hAB j hjA
      · rw [if_neg hjA,
          show j - A.length = 0 by
            rw [show j = A.length from
              Nat.le_antisymm (Nat.le_of_lt_succ hj)
                (Nat.le_of_not_lt hjA)]
            exact Nat.sub_self A.length]
        show elim.spanRel n B
          (getAt [] [getAt ([] : List BPair) B k] 0)
        exact elim.spanRel_getAt n B k hk hB
    have hle := elim.span_count_le n
      (A ++ [getAt ([] : List BPair) B k]) B hrows hB hext hspan
    rw [ground.length_append] at hle
    exact Nat.not_succ_le_self A.length (Nat.le_trans hle hcount)

/-- A provenance pool's members read the head's own degree: every
member is a lowering image at an occupied letter, and the adjacent
lowering keeps the content's total (`units.sumNat_moveDn`). -/
private theorem prov_degree (d : Nat) (v : HVec) (tail : List HVec)
    (hwid : ∀ w ∈ v :: tail, w.content.length = d)
    (hprov : ∀ k, k < tail.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tail) i)
          = some (getAt (⟨[], []⟩ : HVec) tail k)) :
    ∀ (b k : Nat), k ≤ b → k < (v :: tail).length →
      sumNat (getAt (⟨[], []⟩ : HVec) (v :: tail) k).content
        = sumNat v.content
  | _, 0, _, _ => rfl
  | 0, _ + 1, hkb, _ => absurd hkb (Nat.not_succ_le_zero _)
  | b + 1, k + 1, hkb, hk =>
    match hprov k (Nat.lt_of_succ_lt_succ hk) with
    | ⟨i, hik, j, hjd, hlow⟩ =>
      match lowerH_reads hlow with
      | ⟨hocc, hcont⟩ => by
        have hi : i < (v :: tail).length :=
          Nat.lt_of_lt_of_le (Nat.lt_succ_of_le hik) (Nat.le_of_lt hk)
        have hwi : (getAt (⟨[], []⟩ : HVec) (v :: tail) i).content.length
            = d := hwid _ (ground.mem_getAt _ (v :: tail) i hi)
        show sumNat (getAt (⟨[], []⟩ : HVec) tail k).content
          = sumNat v.content
        rw [hcont,
          units.sumNat_moveDn j
            (getAt (⟨[], []⟩ : HVec) (v :: tail) i).content
            (by rw [hwi]; exact hjd) hocc]
        exact prov_degree d v tail hwid hprov b i
          (Nat.le_trans hik (Nat.le_of_succ_le_succ hkb)) hi

/-- A fused pool's content group sits in a second fused pool's at
the same second factor: each row is a tensor of a first-factor
member against a pool member, the first factor inside the second
list's own content group span and the pool member inside its own,
and the collecting read carries the tensor into the fused group
(`con:places`' collecting sentence at `tensor_span`). -/
private theorem fused_span_of (d : Nat) (P Q C : List HVec)
    (dd : List Nat)
    (hszQ : ∀ x ∈ Q, sized x) (hszC : ∀ y ∈ C, sized y)
    (hwidP : ∀ x ∈ P, x.content.length = d)
    (hwidQ : ∀ x ∈ Q, x.content.length = d)
    (hwidC : ∀ y ∈ C, y.content.length = d)
    (hspan : ∀ x ∈ P, elim.spanRel (monomialsAt x.content).length
      (groupAt Q x.content) x.coords) :
    ∀ k, k < (groupAt (fusedAt P C) dd).length →
      elim.spanRel (monomialsAt dd).length (groupAt (fusedAt Q C) dd)
        (getAt [] (groupAt (fusedAt P C) dd) k) := by
  intro k hk
  match groupAt_rows (fun x => x ∈ fusedAt P C) (fusedAt P C)
      (fun _ h => h) dd k hk with
  | ⟨x, hxm, hxc, hxr⟩ =>
    match fusedAt_mem P C x hxm with
    | ⟨a, y, haP, hyC, hax⟩ =>
      have hcont : List.zipWith (fun p q => p + q) a.content
          y.content = dd := by
        rw [← hxc, ← hax]
        rfl
      rw [hxr, ← hax, ← hcont]
      exact tensor_span Q C d hszQ hszC hwidQ hwidC a.content
        y.content (hwidP a haP) (hwidC y hyC) a.coords y.coords
        (hspan a haP) (spanRel_groupAt_mem C y hyC hszC)

/-- `lem:blockcount`(iii)'s transport passage: a provenance pool at
a top reads the fused count at the shape's own block.  The pool is
its head's word images (`blockirr.pool_words`), the fused count
collapses to the pair list's raw kernel dimension at the pairs'
independence (`countAt_pairs` at `tensor_indep`), the one word
family read at the shape's own top carries that dimension across
(`kernelDim_pairs_words`, the pairs' independence transported at
`tensor_indep_words`), and the word images at that top and the
shape's `blockSpan` span one another content by content — the
images inside the block's groups (`blockirr.word_span`), the
images' groups independent at the word pairings
(`blockirr.image_indep`), and the occupancies agreeing
(`blockirr.occ_le`) so a refused block row would extend the images
past their own count inside their span — and the collecting read
lifts both spans to the fused pools (`tensor_span`), the two counts
one value (`countAt_congr`).  The pool binders are
`blockirr.dim_eq`'s one-pool set; the `C` data is the shared
second factor's frame at `con:places`' one letter width. -/
theorem countAt_fused_block (d : Nat) (v : HVec) (tail : List HVec)
    (hsz : ∀ w ∈ v :: tail, sized w)
    (hwid : ∀ w ∈ v :: tail, w.content.length = d)
    (hprov : ∀ k, k < tail.length →
      ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
        lowerH j (getAt (⟨[], []⟩ : HVec) (v :: tail) i)
          = some (getAt (⟨[], []⟩ : HVec) tail k))
    (hind : indepAll (v :: tail))
    (hset : ∀ w ∈ v :: tail, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt (v :: tail) (act i j w))
    (htop : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j v).coords)
    (C : List HVec)
    (hszC : ∀ y ∈ C, sized y)
    (hwidC : ∀ y ∈ C, y.content.length = d)
    (hiC : indepAll C)
    (dd : List Nat) :
    countAt (fusedAt (v :: tail) C) dd
      = countAt (fusedAt (blockSpan (places.shapeOf v.content)) C)
        dd := by
  have hszv : sized v := hsz v (List.Mem.head tail)
  have hwd : v.content.length = d := hwid v (List.Mem.head tail)
  have hgv : groupAt (v :: tail) v.content
      = v.coords :: groupAt tail v.content := by
    rw [groupAt_cons, ground.listEqBeq v.content]
  have hoff : ¬ poly.unitTail v.coords := by
    have h := elim.indep_row_off
      (indepAll_all hind v.content) 0
      (by rw [hgv]; exact Nat.succ_pos _)
    rw [show getAt ([] : List BPair) (groupAt (v :: tail) v.content) 0
        = v.coords by rw [hgv]; rfl] at h
    exact h
  have hdom : ∀ k, k + 1 < v.content.length →
      getAt 0 v.content (k + 1) ≤ getAt 0 v.content k := by
    intro k hk
    refine tops.dominant d v hszv hwd hoff htop k ?_
    rw [← hwd]
    exact hk
  have hrl : rowList (shapeOf v.content) = v.content :=
    rowList_shapeOf v.content hdom
  have hlen_s : (shapeOf v.content).length = d := by
    rw [length_shapeOf]
    exact hwd
  have hsu : sized (exhibit (shapeOf v.content)) :=
    exhibit_sized (shapeOf v.content)
  have hoffu : ¬ poly.unitTail (exhibit (shapeOf v.content)).coords :=
    exhibit_off_unit (shapeOf v.content)
  obtain ⟨hszu0, hindu0, hclu⟩ := blockSpan_sem (shapeOf v.content)
    lowerspan.ht (lowerspan.ht_nomove (shapeOf v.content).length)
    (lowerspan.ht_drop (shapeOf v.content).length)
    (lowerspan.ht_exh (shapeOf v.content)) hsu hoffu
  have hwidu0 := blockSpan_width (shapeOf v.content)
  have hsetu0 : ∀ i j : Nat, i < d → j < d → ¬ i = j →
      ∀ x ∈ blockSpan (shapeOf v.content),
        settledAt (blockSpan (shapeOf v.content)) (act i j x) := by
    intro i j hi hj hij
    exact act_closed (shapeOf v.content) hszu0 hclu i j
      (by rw [hlen_s]; exact hi) (by rw [hlen_s]; exact hj) hij
  have htopu : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail
        (act i j (exhibit (shapeOf v.content))).coords := by
    intro j hj i hij
    have h := exhibit_top_all (shapeOf v.content) i j hij
      (by rw [hlen_s]; exact hj)
    show poly.unitTail (elim.matVec (units.matUnitAt
      (moveAt i j (exhibit (shapeOf v.content)).content)
      (exhibit (shapeOf v.content)).content i j)
      (exhibit (shapeOf v.content)).coords)
    rw [content_exhibit]
    exact h
  have hvu : v.content = (exhibit (shapeOf v.content)).content := by
    rw [content_exhibit, hrl]
  have hdu : (exhibit (shapeOf v.content)).content.length = d := by
    rw [← hvu]
    exact hwd
  match blockSpan_prov (shapeOf v.content) with
  | ⟨tailu, htu', hprovu⟩ =>
    rw [htu'] at hszu0 hindu0 hwidu0
    have hsetu : ∀ x ∈ exhibit (shapeOf v.content) :: tailu,
        ∀ i, i < d → ∀ j, j < d → ¬ i = j →
        settledAt (exhibit (shapeOf v.content) :: tailu)
          (act i j x) := by
      intro x hx i hi j hj hij
      have h := hsetu0 i j hi hj hij x (by rw [htu']; exact hx)
      rw [htu'] at h
      exact h
    have hwidu : ∀ x ∈ exhibit (shapeOf v.content) :: tailu,
        x.content.length = d :=
      fun x hx => (hwidu0 x hx).trans hlen_s
    have hprovu' : ∀ k, k < tailu.length →
        ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
          lowerH j (getAt (⟨[], []⟩ : HVec)
              (exhibit (shapeOf v.content) :: tailu) i)
            = some (getAt (⟨[], []⟩ : HVec) tailu k) := by
      intro k hk
      match hprovu k hk with
      | ⟨i, hik, j, hjd, hlow⟩ =>
        refine ⟨i, hik, j, ?_, hlow⟩
        rw [← hlen_s]
        exact hjd
    match blockirr.pool_words d v tail hprov with
    | ⟨wl, hpw, hwb⟩ =>
      have hwcont : ∀ ws : List Nat, (wact ws v).content
          = (wact ws (exhibit (shapeOf v.content))).content := by
        intro ws
        rw [wact_content ws v,
          wact_content ws (exhibit (shapeOf v.content)), ← hvu]
      have hszPu : ∀ w ∈ wl.map
          (fun ws => wact ws (exhibit (shapeOf v.content))),
          sized w := by
        intro w hw
        match ground.mem_map_of _ wl w hw with
        | ⟨ws, _, he⟩ =>
          rw [← he]
          exact wact_sized ws _ hsu
      have hwidPu : ∀ w ∈ wl.map
          (fun ws => wact ws (exhibit (shapeOf v.content))),
          w.content.length = d := by
        intro w hw
        match ground.mem_map_of _ wl w hw with
        | ⟨ws, _, he⟩ =>
          rw [← he, wact_content_len]
          exact hdu
      have hdegv : ∀ w ∈ v :: tail,
          sumNat w.content = sumNat v.content := by
        intro w hw
        match ground.getAt_of_mem (⟨[], []⟩ : HVec) hw with
        | ⟨k, hk, he⟩ =>
          rw [← he]
          exact prov_degree d v tail hwid hprov k k (Nat.le_refl k) hk
      have hindT : elim.indepRows (monomialsAt dd).length
          ((pairsAt (v :: tail) C dd).map HVec.coords) :=
        tensor_indep (v :: tail) C dd d (sumNat v.content) hwid
          hwidC hdegv hind hiC
      have hindTw : elim.indepRows (monomialsAt dd).length
          ((pairsAt (wl.map (fun ws => wact ws v)) C dd).map
            HVec.coords) := by
        rw [← hpw]
        exact hindT
      have hindU := tensor_indep_words d v
        (exhibit (shapeOf v.content)) hszv hsu hwd hvu htop htopu
        hoffu wl hwb C hszC hwidC dd hindTw
      rw [countAt_pairs (v :: tail) C dd hindT, hpw,
        kernelDim_pairs_words d v (exhibit (shapeOf v.content))
          hszv hsu hwd hvu htop htopu hoff hoffu wl hwb C hszC
          hwidC dd,
        ← countAt_pairs
          (wl.map (fun ws => wact ws (exhibit (shapeOf v.content))))
          C dd hindU, htu']
      refine countAt_congr dd _ _
        (fun x hx => fusedAt_sized _ C x hx)
        (fun x hx => fusedAt_sized _ C x hx) ?_ ?_
      · refine fused_span_of d _ _ C dd hszu0 hszC hwidPu hwidu
          hwidC ?_
        intro x hx
        match ground.mem_map_of _ wl x hx with
        | ⟨ws, hws, he⟩ =>
          rw [← he]
          exact blockirr.word_span d (exhibit (shapeOf v.content))
            tailu hszu0 hsetu ws (hwb ws hws)
      · refine fused_span_of d _ _ C dd hszPu hszC hwidu hwidPu
          hwidC ?_
        intro b hb
        match groupAt_map_congr (fun ws => wact ws v)
            (fun ws => wact ws (exhibit (shapeOf v.content)))
            hwcont b.content wl with
        | ⟨sub, hgvS, hguS, hsubmem, hsubcon⟩ =>
          have hgcb : ∀ ws ∈ sub, (∀ l ∈ ws, l + 1 < d)
              ∧ (wact ws v).content = b.content :=
            fun ws hws => ⟨hwb ws (hsubmem ws hws), hsubcon ws hws⟩
          have hgrpv : groupAt (v :: tail) b.content
              = sub.map (fun ws => (wact ws v).coords) := by
            rw [hpw]
            exact hgvS
          have hiA : elim.indepRows (monomialsAt b.content).length
              (groupAt (wl.map (fun ws =>
                wact ws (exhibit (shapeOf v.content)))) b.content) := by
            rw [hguS]
            exact blockirr.image_indep d v
              (exhibit (shapeOf v.content)) b.content hszv hsu hwd
              hvu htop htopu
              (fun hh => hoffu (elim.dotP_self_null _ hh))
              sub hgcb (groupAt (v :: tail) b.content) hgrpv
              (indepAll_all hind b.content)
          have hAB : ∀ k, k < (groupAt (wl.map (fun ws =>
                wact ws (exhibit (shapeOf v.content)))) b.content).length →
              elim.spanRel (monomialsAt b.content).length
                (groupAt (exhibit (shapeOf v.content) :: tailu)
                  b.content)
                (getAt [] (groupAt (wl.map (fun ws =>
                  wact ws (exhibit (shapeOf v.content)))) b.content) k) := by
            intro k hk
            rw [hguS] at hk ⊢
            rw [ground.length_map] at hk
            rw [ground.getAt_map ([] : List Nat) ([] : List BPair)
              (fun ws => (wact ws
                (exhibit (shapeOf v.content))).coords) sub k hk]
            have hws := ground.mem_getAt ([] : List Nat) sub k hk
            have hsp := blockirr.word_span d
              (exhibit (shapeOf v.content)) tailu hszu0 hsetu
              (getAt ([] : List Nat) sub k) (hgcb _ hws).1
            rw [show (wact (getAt ([] : List Nat) sub k)
                  (exhibit (shapeOf v.content))).content = b.content
              from (hwcont _).symm.trans (hgcb _ hws).2] at hsp
            exact hsp
          have hcount : (groupAt (exhibit (shapeOf v.content)
                :: tailu) b.content).length
              ≤ (groupAt (wl.map (fun ws =>
                wact ws (exhibit (shapeOf v.content))))
                b.content).length := by
            rw [hguS, ground.length_map,
              show sub.length = (groupAt (v :: tail) b.content).length
                from by rw [hgrpv, ground.length_map],
              length_groupAt b.content
                (exhibit (shapeOf v.content) :: tailu),
              length_groupAt b.content (v :: tail)]
            exact blockirr.occ_le d (exhibit (shapeOf v.content))
              tailu v tail hszu0 hprovu' hindu0 htopu hsz hset hind
              htop hdu hvu.symm b.content
          have hsat := span_saturate (monomialsAt b.content).length
            (groupAt (wl.map (fun ws =>
              wact ws (exhibit (shapeOf v.content)))) b.content)
            (groupAt (exhibit (shapeOf v.content) :: tailu)
              b.content)
            (rowsLen_groupAt b.content _ hszPu)
            (rowsLen_groupAt b.content _ hszu0) hiA hAB hcount
          match ground.getAt_of_mem ([] : List BPair)
            (show b.coords ∈ groupAt
                (exhibit (shapeOf v.content) :: tailu) b.content from
              ground.mem_map_to HVec.coords
                (ground.mem_filter_to
                  (fun w => w.content == b.content) hb
                  (ground.listEqBeq b.content))) with
          | ⟨k, hk, he⟩ =>
            rw [← he]
            exact hsat k hk


/-! `lem:blockcount`(iii)'s expansion over the exhaustion: at a
one-degree carrier the fused count reads the display's sum, one
summand per distinct top content of the exhaustion — the carrier
and its blocks' join span each other with the fused pools riding
the spans (`tensor_span` at `fused_span_of`), the join's fused
count adds over the blocks at the fused pools' perpendicularity,
the factors' pairings' products at the shared degree
(`countAt_append`), each block's fused count transports to its
shape's own (`countAt_fused_block`), and the per-top folds regroup
at the occupied contents with the multiplicities the carrier's own
counts (`countAt_exhaust`). -/

/-- A block at a stated top: the seed closure's stated data at the
top's own reads, the transport's binder list off the pick. -/
private theorem blockOf_data (d : Nat) (w : HVec)
    (hszw : sized w) (hwidw : w.content.length = d)
    (hoffw : ¬ poly.unitTail w.coords)
    (htopw : ∀ j, j < d → ∀ i, i < j →
      poly.unitTail (act i j w).coords) :
    ∃ tailB, blockOf d w = w :: tailB
      ∧ (∀ v ∈ w :: tailB, sized v)
      ∧ (∀ v ∈ w :: tailB, v.content.length = d)
      ∧ indepAll (w :: tailB)
      ∧ (∀ x ∈ w :: tailB, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
          settledAt (w :: tailB) (act i j x))
      ∧ ∀ k, k < tailB.length →
          ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
            lowerH j (getAt (⟨[], []⟩ : HVec) (w :: tailB) i)
              = some (getAt (⟨[], []⟩ : HVec) tailB k) :=
  match lowerspan.seed_closed d (lowerspan.ht w.content) w hszw
      hwidw hoffw
      (fun jr hjr => htopw (jr + 1) hjr jr (Nat.lt_succ_self jr))
      (Nat.le_refl _) with
  | ⟨tailB, htlB, hszB, hwidB, hprovB, hindB, hsetB⟩ =>
    ⟨tailB, (blockOf_eq d w).trans htlB, hszB, hwidB, hindB,
      hsetB, hprovB⟩

/-- A settled member of a one-degree carrier reads the unit family
or the carrier's own degree: an occupied group names a carrier
content, and a vacant group's span forces the unit family. -/
private theorem join_degree (kP : Nat) (P : List HVec)
    (hdeg : ∀ x ∈ P, sumNat x.content = kP)
    (y : HVec) (hset : settledAt P y) :
    poly.unitTail y.coords ∨ sumNat y.content = kP := by
  match hset with
  | Or.inl hu => exact Or.inl (unitTail_of_allU y.coords hu)
  | Or.inr hs =>
    match Nat.eq_zero_or_pos
        (ground.countOf y.content (P.map HVec.content)) with
    | .inr hp =>
      match ground.mem_map_of HVec.content P y.content
          (ground.mem_of_countOf_pos y.content _ hp) with
      | ⟨x, hxP, hxc⟩ =>
        refine Or.inr ?_
        rw [← hxc]
        exact hdeg x hxP
    | .inl hz =>
      refine Or.inl ?_
      rw [groupAt_nil_of_countOf P y.content hz] at hs
      match elim.span_elim hs with
      | ⟨c0, cs, hc0, hcl, hone⟩ =>
        rw [ground.nil_of_length_zero cs hcl] at hone
        refine elim.unitTail_unscale c0 hc0 y.coords ?_
        refine poly.unitTail_oneValue_right ?_
          (poly.oneValue_symm hone)
        show poly.unitTail (List.replicate y.coords.length
          BPair.unit)
        exact poly.unitTail_replicate _

/-- The fused pools' cross perpendicularity at a shared degree:
two carriers whose members pair at the sum's unit at every shared
content hand their fused pools the read at every content, the
factors' pairings' products (`lem:blockcount`(iii)'s split). -/
private theorem fused_perp (d kP : Nat) (X Y C : List HVec)
    (hszX : ∀ x ∈ X, sized x) (hszY : ∀ x ∈ Y, sized x)
    (hszC : ∀ y ∈ C, sized y)
    (hwidX : ∀ x ∈ X, x.content.length = d)
    (hwidY : ∀ x ∈ Y, x.content.length = d)
    (hwidC : ∀ y ∈ C, y.content.length = d)
    (hdX : ∀ x ∈ X, poly.unitTail x.coords ∨ sumNat x.content = kP)
    (hdY : ∀ x ∈ Y, poly.unitTail x.coords ∨ sumNat x.content = kP)
    (hperp : ∀ x ∈ X, ∀ y ∈ Y, x.content = y.content →
      (elim.dotP x.coords y.coords).oneValue BPair.unit)
    (m : List Nat) :
    ∀ k, k < (groupAt (fusedAt X C) m).length →
    ∀ l, l < (groupAt (fusedAt Y C) m).length →
      (elim.dotP (ground.getAt [] (groupAt (fusedAt X C) m) k)
        (ground.getAt [] (groupAt (fusedAt Y C) m) l)).oneValue
        BPair.unit := by
  intro k hk l hl
  match groupAt_rows (fun x => x ∈ fusedAt X C) (fusedAt X C)
      (fun _ h => h) m k hk with
  | ⟨p, hpm, hpc, hpr⟩ =>
    match groupAt_rows (fun x => x ∈ fusedAt Y C) (fusedAt Y C)
        (fun _ h => h) m l hl with
    | ⟨q, hqm, hqc, hqr⟩ =>
      rw [hpr, hqr]
      match fusedAt_mem X C p hpm, fusedAt_mem Y C q hqm with
      | ⟨a, y, haX, hyC, hay⟩, ⟨b, z, hbY, hzC, hbz⟩ =>
        rw [← hay, ← hbz]
        have hsa := hszX a haX
        have hsb := hszY b hbY
        have hsy := hszC y hyC
        have hsz2 := hszC z hzC
        have hlay : a.content.length = y.content.length := by
          rw [hwidX a haX, hwidC y hyC]
        have hlbz : b.content.length = z.content.length := by
          rw [hwidY b hbY, hwidC z hzC]
        match hdX a haX with
        | Or.inl hna =>
          refine elim.dotP_null_tail_left _ _ ?_
          exact (tensorH_unitTail a y hsa hsy hlay).2 (Or.inl hna)
        | Or.inr hdega =>
          match hdY b hbY with
          | Or.inl hnb =>
            refine elim.dotP_null_tail_right _ _ ?_
            exact (tensorH_unitTail b z hsb hsz2 hlbz).2
              (Or.inl hnb)
          | Or.inr hdegb =>
            have hcc : (tensorH a y).content
                = (tensorH b z).content := by
              rw [hay, hbz, hpc, hqc]
            by_cases hab : a.content = b.content
            · have hyz : y.content = z.content := by
                refine zipWith_add_cancelL a.content y.content
                  z.content d (hwidX a haX) (hwidC y hyC)
                  (hwidC z hzC) ?_
                show List.zipWith (fun p q => p + q) a.content
                    y.content
                  = List.zipWith (fun p q => p + q) a.content
                    z.content
                have h1 : (tensorH a y).content
                    = List.zipWith (fun p q => p + q) a.content
                      y.content := content_tensorH a y
                have h2 : (tensorH b z).content
                    = List.zipWith (fun p q => p + q) b.content
                      z.content := content_tensorH b z
                rw [← h1, hab, ← h2, hcc]
              refine BPair.oneValue_trans
                (dotP_tensorH a y b z hsa hsy hsb hsz2 hlay hab
                  hyz) ?_
              refine BPair.oneValue_trans
                (BPair.mul_congr (hperp a haX b hbY hab)
                  (BPair.oneValue_refl _)) ?_
              exact BPair.unit_mul _
            · exact dotP_tensorH_off a y b z hlay hlbz
                (hdega.trans hdegb.symm) hcc hab

/-- The fused pool's closure at every adjacent letter: in the
letter range the split folds close (`fused_closed`), and past the
width the consumed letter is vacant and the image reads the unit
family outright. -/
private theorem fused_settled_adj (d : Nat) (X C : List HVec)
    (hszX : ∀ x ∈ X, sized x) (hszC : ∀ y ∈ C, sized y)
    (hwidX : ∀ x ∈ X, x.content.length = d)
    (hwidC : ∀ y ∈ C, y.content.length = d)
    (hclX : ∀ x ∈ X, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt X (act i j x))
    (hclC : ∀ y ∈ C, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt C (act i j y))
    (x : HVec) (hx : x ∈ fusedAt X C) (i : Nat) :
    settledAt (fusedAt X C) (act i (i + 1) x) := by
  by_cases hi : i + 1 < d
  · exact fused_closed d X C hszX hszC hwidX hwidC hclX hclC x hx
      i (Nat.lt_of_succ_lt hi) (i + 1) hi
      (fun h => absurd h (Nat.ne_of_lt (Nat.lt_succ_self i)))
  · refine Or.inl (allU_of_unitTail _ ?_)
    show poly.unitTail (elim.matVec
      (units.matUnitAt (moveAt i (i + 1) x.content) x.content i
        (i + 1)) x.coords)
    refine units.matVec_null_unocc _ _ i (i + 1) ?_ x.coords
    have hw : x.content.length = d :=
      fusedAt_width d X C hwidX hwidC x hx
    refine ground.getAt_over 0 x.content (i + 1) ?_
    rw [hw]
    exact Nat.le_of_not_lt hi

/-- A settled member keeps its read at a wider pool: the group
grows with the pool and the span keeps its members
(`elim.spanRel_trans` at the rows' own memberships). -/
private theorem settled_super (Q P : List HVec)
    (hszQ : ∀ x ∈ Q, sized x) (hszP : ∀ x ∈ P, sized x)
    (hsub : ∀ x ∈ Q, x ∈ P)
    (y : HVec) (hsy : sized y) (h : settledAt Q y) :
    settledAt P y := by
  refine Or.inr ?_
  refine elim.spanRel_trans y.coords.length
    (groupAt Q y.content) (groupAt P y.content) y.coords
    (by rw [hsy]; exact rowsLen_groupAt y.content Q hszQ)
    (by rw [hsy]; exact rowsLen_groupAt y.content P hszP)
    ?_ (settled_to_span Q y hszQ hsy h)
  intro k hk
  match groupAt_rows (fun x => x ∈ Q) Q (fun _ h => h) y.content
      k hk with
  | ⟨x, hxQ, hxc, hxr⟩ =>
    rw [hxr]
    have hmemP : x.coords ∈ groupAt P y.content := by
      refine ground.mem_map_to HVec.coords ?_
      refine ground.mem_filter_to
        (fun w => w.content == y.content) (hsub x hxQ) ?_
      rw [hxc]
      exact ground.listEqBeq y.content
    match ground.getAt_of_mem ([] : List BPair) hmemP with
    | ⟨j, hj, hje⟩ =>
      rw [← hje]
      refine elim.spanRel_getAt y.coords.length _ j hj ?_
      rw [hsy]
      exact rowsLen_groupAt y.content P hszP

/-- The join's fused count adds over the blocks: pairwise
perpendicular block pools at one shared degree split the fused
count, one summand per top (`countAt_append` at the fused pools'
perpendicularity, the factors' pairings' products). -/
private theorem countAt_fused_join (d kP : Nat) (C : List HVec)
    (hszC : ∀ y ∈ C, sized y)
    (hwidC : ∀ y ∈ C, y.content.length = d)
    (hclC : ∀ y ∈ C, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt C (act i j y))
    (dd : List Nat) :
    ∀ ts : List HVec,
    (∀ w ∈ ts, sized w ∧ w.content.length = d
      ∧ ¬ poly.unitTail w.coords
      ∧ ∀ j, j < d → ∀ i, i < j →
          poly.unitTail (act i j w).coords) →
    (∀ w ∈ ts, ∀ x ∈ blockOf d w,
      sized x ∧ x.content.length = d
        ∧ (poly.unitTail x.coords ∨ sumNat x.content = kP)) →
    (∀ a, a < ts.length → ∀ b, b < ts.length → ¬ a = b →
      ∀ x ∈ blockOf d (getAt (⟨[], []⟩ : HVec) ts a),
      ∀ y ∈ blockOf d (getAt (⟨[], []⟩ : HVec) ts b),
        x.content = y.content →
        (elim.dotP x.coords y.coords).oneValue BPair.unit) →
    countAt (fusedAt (blockJoin d ts) C) dd
      = ground.famFold Nat.add 0
          (fun w => countAt (fusedAt (blockOf d w) C) dd) ts
  | [], _, _, _ => by
    show elim.kernelDim 0
      (elim.crossM (units.stackedRaise dd) []) = 0
    exact Nat.zero_sub _
  | w :: ts, hpack, hblk, hperp => by
    obtain ⟨hszw, hwidw, hoffw, htopw⟩ :=
      hpack w (List.Mem.head ts)
    obtain ⟨tailB, hbeq, hszB, hwidB, hindB, hsetB, hprovB⟩ :=
      blockOf_data d w hszw hwidw hoffw htopw
    have hblk0 := hblk w (List.Mem.head ts)
    have hszX : ∀ x ∈ blockOf d w, sized x :=
      fun x hx => (hblk0 x hx).1
    have hwidX : ∀ x ∈ blockOf d w, x.content.length = d :=
      fun x hx => (hblk0 x hx).2.1
    have hdX : ∀ x ∈ blockOf d w,
        poly.unitTail x.coords ∨ sumNat x.content = kP :=
      fun x hx => (hblk0 x hx).2.2
    have hclX : ∀ x ∈ blockOf d w, ∀ i, i < d → ∀ j, j < d →
        ¬ i = j → settledAt (blockOf d w) (act i j x) := by
      rw [hbeq]
      exact hsetB
    have hjm : ∀ y ∈ blockJoin d ts,
        ∃ t, t ∈ ts ∧ y ∈ blockOf d t :=
      fun y hy => ground.mem_flatMap_of (blockOf d) ts y hy
    have hszY : ∀ y ∈ blockJoin d ts, sized y := fun y hy =>
      match hjm y hy with
      | ⟨t, ht, hyt⟩ => (hblk t (List.Mem.tail w ht) y hyt).1
    have hwidY : ∀ y ∈ blockJoin d ts, y.content.length = d :=
      fun y hy =>
        match hjm y hy with
        | ⟨t, ht, hyt⟩ => (hblk t (List.Mem.tail w ht) y hyt).2.1
    have hdY : ∀ y ∈ blockJoin d ts,
        poly.unitTail y.coords ∨ sumNat y.content = kP :=
      fun y hy =>
        match hjm y hy with
        | ⟨t, ht, hyt⟩ => (hblk t (List.Mem.tail w ht) y hyt).2.2
    have hclY : ∀ y ∈ blockJoin d ts, ∀ i, i < d → ∀ j, j < d →
        ¬ i = j → settledAt (blockJoin d ts) (act i j y) := by
      intro y hy i hi j hj hij
      match hjm y hy with
      | ⟨t, ht, hyt⟩ =>
        obtain ⟨hszt, hwidt, hofft, htopt⟩ :=
          hpack t (List.Mem.tail w ht)
        obtain ⟨tailT, hteq, hszT, hwidT, hindT, hsetT, hprovT⟩ :=
          blockOf_data d t hszt hwidt hofft htopt
        have hset1 : settledAt (blockOf d t) (act i j y) := by
          rw [hteq]
          refine hsetT y ?_ i hi j hj hij
          rw [← hteq]
          exact hyt
        refine settled_super (blockOf d t) (blockJoin d ts)
          (fun x hx => (hblk t (List.Mem.tail w ht) x hx).1)
          hszY
          (fun x hx => ground.mem_flatMap_to (blockOf d) ht hx)
          (act i j y) ?_ hset1
        exact act_sized i j y
    have hperpXY : ∀ x ∈ blockOf d w, ∀ y ∈ blockJoin d ts,
        x.content = y.content →
        (elim.dotP x.coords y.coords).oneValue BPair.unit := by
      intro x hx y hy hc
      match hjm y hy with
      | ⟨t, ht, hyt⟩ =>
        match ground.getAt_of_mem (⟨[], []⟩ : HVec) ht with
        | ⟨k, hk, he⟩ =>
          refine hperp 0 (Nat.succ_pos ts.length) (k + 1)
            (Nat.succ_lt_succ hk) (fun h => Nat.noConfusion h)
            x hx y ?_ hc
          show y ∈ blockOf d (getAt (⟨[], []⟩ : HVec) ts k)
          rw [he]
          exact hyt
    have hszFA : ∀ x ∈ fusedAt (blockOf d w) C, sized x := by
      intro x hx
      match fusedAt_mem _ _ x hx with
      | ⟨a, y, _, _, he⟩ =>
        rw [← he]
        exact tensorH_sized a y
    have hszFB : ∀ x ∈ fusedAt (blockJoin d ts) C, sized x := by
      intro x hx
      match fusedAt_mem _ _ x hx with
      | ⟨a, y, _, _, he⟩ =>
        rw [← he]
        exact tensorH_sized a y
    show countAt (fusedAt (blockOf d w ++ blockJoin d ts) C) dd
      = countAt (fusedAt (blockOf d w) C) dd
        + ground.famFold Nat.add 0
            (fun w => countAt (fusedAt (blockOf d w) C) dd) ts
    rw [fusedAt_append C (blockOf d w) (blockJoin d ts),
      countAt_append dd (fusedAt (blockOf d w) C)
        (fusedAt (blockJoin d ts) C) hszFA hszFB
        (fun x hx i _ => fused_settled_adj d (blockOf d w) C hszX
          hszC hwidX hwidC hclX hclC x hx i)
        (fun x hx i _ => fused_settled_adj d (blockJoin d ts) C
          hszY hszC hwidY hwidC hclY hclC x hx i)
        (fused_perp d kP (blockOf d w) (blockJoin d ts) C hszX
          hszY hszC hwidX hwidY hwidC hdX hdY hperpXY dd)
        (fun i _ => fused_perp d kP (blockOf d w)
          (blockJoin d ts) C hszX hszY hszC hwidX hwidY hwidC
          hdX hdY hperpXY (moveAt i (i + 1) dd)),
      countAt_fused_join d kP C hszC hwidC hclC dd ts
        (fun t ht => hpack t (List.Mem.tail w ht))
        (fun t ht => hblk t (List.Mem.tail w ht))
        (fun a ha b hb hab x hx y hy hc =>
          hperp (a + 1) (Nat.succ_lt_succ ha) (b + 1)
            (Nat.succ_lt_succ hb)
            (fun h => hab (Nat.succ.inj h)) x hx y hy hc)]

/-- The expansion over the exhaustion (`lem:blockcount`(iii)'s
associativity passage): at a one-degree carrier the fused count
reads the display's sum, one summand per distinct top content of
the exhaustion, the multiplicities the carrier's own counts.  The
carrier and its blocks' join span each other with the fused pools
riding the spans (`fused_span_of` at `countAt_congr`), the join's
fused count adds over the blocks at the fused pools'
perpendicularity (`countAt_fused_join`), each block transports to
its shape's own (`countAt_fused_block`), and the per-top folds
regroup at the occupied contents (`countAt_exhaust`).  The degree
binder `hdeg` is load-bearing (`con:places`' one-degree blocks):
its committed refusal reads a mixed-degree carrier whose blocks'
fused pools interfere across the splits. -/
theorem countAt_fused_exhaust (d kP : Nat) (P : List HVec)
    (hsz : ∀ x ∈ P, sized x)
    (hwid : ∀ x ∈ P, x.content.length = d)
    (hdeg : ∀ x ∈ P, ground.sumNat x.content = kP)
    (hcl : ∀ x ∈ P, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt P (act i j x))
    (C : List HVec)
    (hszC : ∀ y ∈ C, sized y)
    (hwidC : ∀ y ∈ C, y.content.length = d)
    (hclC : ∀ y ∈ C, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt C (act i j y))
    (hiC : indepAll C)
    (dd : List Nat) :
    countAt (fusedAt P C) dd
      = ground.famFold Nat.add 0
          (fun mu => countAt P mu
            * countAt (fusedAt (blockSpan (places.shapeOf mu)) C)
              dd)
          (ground.dedupL ((exhaust d P).map HVec.content)) := by
  have hts := exhaust_top d P hsz hwid hcl
  have hstl := exhaust_settle d P hsz hwid hcl
  have hszBJ : ∀ y ∈ blockJoin d (exhaust d P), sized y :=
    fun y hy => (hstl y hy).1
  have hwidBJ : ∀ y ∈ blockJoin d (exhaust d P),
      y.content.length = d :=
    fun y hy => (hstl y hy).2.1
  have hszF1 : ∀ x ∈ fusedAt P C, sized x := by
    intro x hx
    match fusedAt_mem _ _ x hx with
    | ⟨a, y, _, _, he⟩ =>
      rw [← he]
      exact tensorH_sized a y
  have hszF2 : ∀ x ∈ fusedAt (blockJoin d (exhaust d P)) C,
      sized x := by
    intro x hx
    match fusedAt_mem _ _ x hx with
    | ⟨a, y, _, _, he⟩ =>
      rw [← he]
      exact tensorH_sized a y
  have hS1 : countAt (fusedAt P C) dd
      = countAt (fusedAt (blockJoin d (exhaust d P)) C) dd := by
    refine countAt_congr dd _ _ hszF1 hszF2 ?_ ?_
    · refine fused_span_of d P (blockJoin d (exhaust d P)) C dd
        hszBJ hszC hwid hwidBJ hwidC ?_
      intro x hx
      have h := exhaust_span d P hsz hwid x hx
      rw [show x.coords.length
          = (places.monomialsAt x.content).length
        from hsz x hx] at h
      exact h
    · refine fused_span_of d (blockJoin d (exhaust d P)) P C dd
        hsz hszC hwidBJ hwid hwidC ?_
      intro y hy
      have h := settled_to_span P y hsz (hszBJ y hy)
        (hstl y hy).2.2
      rw [show y.coords.length
          = (places.monomialsAt y.content).length
        from hszBJ y hy] at h
      exact h
  have hS2 : countAt (fusedAt (blockJoin d (exhaust d P)) C) dd
      = ground.famFold Nat.add 0
          (fun w => countAt (fusedAt (blockOf d w) C) dd)
          (exhaust d P) := by
    refine countAt_fused_join d kP C hszC hwidC hclC dd
      (exhaust d P) hts ?_ ?_
    · intro w hw x hx
      have h := hstl x
        (ground.mem_flatMap_to (blockOf d) hw hx)
      exact ⟨h.1, h.2.1, join_degree kP P hdeg x h.2.2⟩
    · intro a ha b hb hab x hx y hy hc
      have hgx : x.coords ∈ groupAt
          (blockOf d (getAt (⟨[], []⟩ : HVec) (exhaust d P) a))
          x.content := by
        refine ground.mem_map_to HVec.coords ?_
        exact ground.mem_filter_to
          (fun w => w.content == x.content) hx
          (ground.listEqBeq x.content)
      have hgy : y.coords ∈ groupAt
          (blockOf d (getAt (⟨[], []⟩ : HVec) (exhaust d P) b))
          x.content := by
        refine ground.mem_map_to HVec.coords ?_
        refine ground.mem_filter_to
          (fun w => w.content == x.content) hy ?_
        rw [← hc]
        exact ground.listEqBeq x.content
      match ground.getAt_of_mem ([] : List BPair) hgx,
          ground.getAt_of_mem ([] : List BPair) hgy with
      | ⟨k, hk, hke⟩, ⟨l, hl, hle⟩ =>
        match Nat.lt_or_ge a b with
        | Or.inl haltb =>
          have h := exhaust_perp d P hsz hwid hcl a b haltb hb
            x.content k hk l hl
          rw [hke, hle] at h
          exact h
        | Or.inr hge =>
          have hblta : b < a :=
            match Nat.lt_or_ge b a with
            | Or.inl h => h
            | Or.inr h => absurd (Nat.le_antisymm hge h)
                (fun he => hab he.symm)
          have h := exhaust_perp d P hsz hwid hcl b a hblta ha
            x.content l hl k hk
          rw [hke, hle] at h
          rw [elim.dotP_comm x.coords y.coords]
          exact h
  have hS3 : ground.famFold Nat.add 0
      (fun w => countAt (fusedAt (blockOf d w) C) dd)
      (exhaust d P)
      = ground.famFold Nat.add 0
        (fun w => countAt
          (fusedAt (blockSpan (places.shapeOf w.content)) C) dd)
        (exhaust d P) := by
    refine ground.famFold_congr_members Nat.add 0 _ _ _ ?_
    intro w hw
    obtain ⟨hszw, hwidw, hoffw, htopw⟩ :=
      hts w (ground.mem_of_countOf_pos w _ hw)
    obtain ⟨tailB, hbeq, hszB, hwidB, hindB, hsetB, hprovB⟩ :=
      blockOf_data d w hszw hwidw hoffw htopw
    rw [hbeq]
    exact countAt_fused_block d w tailB hszB hwidB hprovB hindB
      hsetB htopw C hszC hwidC hiC dd
  rw [hS1, hS2, hS3,
    exhaust_regroup d P hsz hwid hcl
      (fun nu => countAt
        (fusedAt (blockSpan (places.shapeOf nu)) C) dd)]

/-! `lem:blockcount`(iii)'s dimension clause: the fused carrier's
own dimension read two ways at the pair list's count, the two
blocks' counts' product. -/

/-- The fused pool's stated data at two shapes' blocks: the
enumerations, the widths, the interior closure at every distinct
letter pair, and the content groups' independence — the two
blocks' own reads (`lowerspan.spanReads`, `blockSpan_width`,
`blockSpan_degree`, `lowerspan.act_closed_def`) carried across by
`fused_closed` and `fused_indepAll`. -/
theorem fusedSpan_pack (a b : Shape)
    (hba : b.length = a.length) :
    (∀ x ∈ fusedAt (blockSpan a) (blockSpan b), sized x)
      ∧ (∀ x ∈ fusedAt (blockSpan a) (blockSpan b),
          x.content.length = a.length)
      ∧ (∀ x ∈ fusedAt (blockSpan a) (blockSpan b), ∀ i, i < a.length →
          ∀ j, j < a.length → ¬ i = j →
          settledAt (fusedAt (blockSpan a) (blockSpan b)) (act i j x))
      ∧ indepAll (fusedAt (blockSpan a) (blockSpan b)) := by
  have hwidB : ∀ w ∈ blockSpan b, w.content.length = a.length :=
    fun w hw => (blockSpan_width b w hw).trans hba
  have hclB : ∀ w ∈ blockSpan b, ∀ i, i < a.length → ∀ j,
      j < a.length → ¬ i = j →
      settledAt (blockSpan b) (act i j w) := by
    intro w hw i hi j hj hij
    exact lowerspan.act_closed_def b i j (by rw [hba]; exact hi)
      (by rw [hba]; exact hj) hij w hw
  refine ⟨fusedAt_sized (blockSpan a) (blockSpan b),
    fusedAt_width a.length (blockSpan a) (blockSpan b)
      (blockSpan_width a) hwidB,
    fused_closed a.length (blockSpan a) (blockSpan b)
      (lowerspan.spanReads a).1 (lowerspan.spanReads b).1
      (blockSpan_width a) hwidB
      (fun v hv i hi j hj hij =>
        lowerspan.act_closed_def a i j hi hj hij v hv)
      hclB,
    fused_indepAll a.length (degree a) (blockSpan a) (blockSpan b)
      (blockSpan_width a) hwidB (blockSpan_degree a)
      (lowerspan.spanReads a).2.1 (lowerspan.spanReads b).2.1⟩

/-- A fused pool's exhaustion tops read their shapes back: each
produced top is dominant at the derived read (`tops.dominant` at
`exhaust_top`), so its content is its shape's own row list
(`places.rowList_shapeOf`). -/
theorem exhaust_rowList_shapeOf (d : Nat) (P : List HVec)
    (hsz : ∀ x ∈ P, sized x)
    (hwid : ∀ x ∈ P, x.content.length = d)
    (hcl : ∀ x ∈ P, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt P (act i j x)) :
    ∀ mu ∈ (exhaust d P).map HVec.content,
      rowList (shapeOf mu) = mu := by
  intro mu hmu
  match ground.mem_map_of HVec.content (exhaust d P) mu hmu with
  | ⟨w, hw, hwc⟩ =>
    obtain ⟨hszw, hwidw, hoffw, htopw⟩ := exhaust_top d P hsz hwid
      hcl w hw
    rw [← hwc]
    refine rowList_shapeOf w.content ?_
    intro k hk
    refine tops.dominant d w hszw hwidw hoffw htopw k ?_
    rw [← hwidw]
    exact hk

/-- The exhaustion's contents keep the stated width, the mapped
read of the produced members' own (`exhaust_top`). -/
theorem exhaust_width (d : Nat) (P : List HVec)
    (hsz : ∀ x ∈ P, sized x)
    (hwid : ∀ x ∈ P, x.content.length = d)
    (hcl : ∀ x ∈ P, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
      settledAt P (act i j x)) :
    ∀ mu ∈ (exhaust d P).map HVec.content, mu.length = d := by
  intro mu hmu
  match ground.mem_map_of HVec.content (exhaust d P) mu hmu with
  | ⟨w, hw, hwc⟩ =>
    rw [← hwc]
    exact (exhaust_top d P hsz hwid hcl w hw).2.1

/-! The channels' own reads at the fused carrier: a channel's
occupied block content is a content of the pool itself
(`gradedDim_countAt` at the graded display), and the exhaustion's
contents carry the two factors' degree total
(`fusedAt_degree`). -/

/-- A channel's occupied block content at an occupied channel
count is a content of the fused pool: the channel's summand in the
graded display is a lower bound on the content's dimension, and an
independent pool's dimension is its occupancy. -/
theorem channel_content (a b : Shape) (hba : b.length = a.length)
    (nu : List Nat)
    (hnu : nu ∈ ground.dedupL ((exhaust a.length
      (fusedAt (blockSpan a) (blockSpan b))).map HVec.content))
    (hcp : 0 < countAt (fusedAt (blockSpan a) (blockSpan b)) nu)
    (m : List Nat) (hm : 0 < occ m (blockSpan (places.shapeOf nu))) :
    0 < ground.countOf m
      ((fusedAt (blockSpan a) (blockSpan b)).map HVec.content) := by
  obtain ⟨hszP, hwidP, hclP, hiP⟩ := fusedSpan_pack a b hba
  have hle := ground.famFold_mem_le
    (fun nu' => countAt (fusedAt (blockSpan a) (blockSpan b)) nu'
      * occ m (blockSpan (places.shapeOf nu')))
    (ground.dedupL ((exhaust a.length
      (fusedAt (blockSpan a) (blockSpan b))).map HVec.content)) nu hnu
  rw [← gradedDim_countAt a.length
    (fusedAt (blockSpan a) (blockSpan b)) hszP hwidP hclP m] at hle
  have hpos : 0 < dimAt (fusedAt (blockSpan a) (blockSpan b)) m :=
    Nat.lt_of_lt_of_le (Nat.mul_pos hcp hm) hle
  rw [dimAt_occ (fusedAt (blockSpan a) (blockSpan b)) hiP m,
    occ_eq_countOf] at hpos
  exact hpos

/-- The exhaustion's contents carry the fused pool's degree: a
content is a pool content — its own channel count and its block's
top line are occupied — and the tensor's contents sum the two
factors' box totals. -/
theorem exhaust_degree (a b : Shape) (hba : b.length = a.length) :
    ∀ mu ∈ (exhaust a.length
      (fusedAt (blockSpan a) (blockSpan b))).map HVec.content,
      ground.sumNat mu = places.degree a + places.degree b := by
  intro mu hmu
  obtain ⟨hszP, hwidP, hclP, _⟩ := fusedSpan_pack a b hba
  have hrl := exhaust_rowList_shapeOf a.length
    (fusedAt (blockSpan a) (blockSpan b)) hszP hwidP hclP mu hmu
  have hcnt : 0 < countAt (fusedAt (blockSpan a) (blockSpan b)) mu := by
    rw [countAt_exhaust a.length (fusedAt (blockSpan a) (blockSpan b))
        hszP hwidP hclP mu, occ_eq_countOf]
    exact ground.countOf_pos_of_mem hmu
  have htop : ground.countOf (places.rowList (places.shapeOf mu))
      ((blockSpan (places.shapeOf mu)).map HVec.content) = 1 :=
    lowerspan.topRead_def (places.shapeOf mu)
  rw [hrl] at htop
  have hoccS : 0 < occ mu (blockSpan (places.shapeOf mu)) := by
    rw [occ_eq_countOf, htop]
    exact Nat.succ_pos 0
  have hposc := channel_content a b hba mu (ground.mem_dedupL hmu)
    hcnt mu hoccS
  obtain ⟨x, hx, hxc⟩ := ground.mem_map_of HVec.content
    (fusedAt (blockSpan a) (blockSpan b)) mu
    (ground.mem_of_countOf_pos mu _ hposc)
  rw [← hxc]
  exact fusedAt_degree a.length (places.degree a) (places.degree b)
    (blockSpan a) (blockSpan b) (blockSpan_width a)
    (fun w hw => (blockSpan_width b w hw).trans hba)
    (blockSpan_degree a) (blockSpan_degree b) x hx

/-- The fusion count is the fused pool's occupancy at the target's
row list: the count read at the exhaustion's contents, the two
reads one datum (`lem:blockcount`(ii)'s exhaustion at the stated
pair list). -/
theorem fusionCount_countOf (a b c : Shape)
    (hba : b.length = a.length) :
    fusionCount a b c
      = ground.countOf (places.rowList c)
        ((exhaust a.length
          (fusedAt (blockSpan a) (blockSpan b))).map
          HVec.content) := by
  obtain ⟨hszP, hwidP, hclP, _⟩ := fusedSpan_pack a b hba
  rw [fusionCount_countAt a b c hba,
    countAt_exhaust a.length (fusedAt (blockSpan a) (blockSpan b))
      hszP hwidP hclP (places.rowList c),
    occ_eq_countOf (places.rowList c)
      (exhaust a.length (fusedAt (blockSpan a) (blockSpan b)))]

/-- The dimension display at the fused carrier
(`lem:blockcount`(iii)'s fourth clause, dim(W_a ⊗ W_b) read at
(ii) with M = W_a x W_b): the graded fold of the fusion counts
against the block dimensions reads the two blocks' counts'
product.  The fused carrier is closed at the letters' split folds
(`con:units`, `fused_closed`) and its content groups are
independent (`fused_indepAll`), so (ii)'s display applies
(`dimOf_countAt`) with the counts the fusion counts themselves
(`fusionCount_countAt` at the tops' own row lists); on the other
side the collection keeps every group whole
(`elim.collect_keep`), the groups' counts partition the pool
(`ground.countOf_partition`), and the pool's own count is the pair
list's (`length_fusedAt`).  The one letter width `hba` is
load-bearing with its committed refusal, the check module's own
record. -/
theorem fusionCount_dim (a b : Shape)
    (hba : b.length = a.length) :
    ground.famFold Nat.add 0
      (fun mu => fusionCount a b (places.shapeOf mu)
        * (blockSpan (places.shapeOf mu)).length)
      (ground.dedupL
        ((exhaust a.length
          (fusedAt (blockSpan a) (blockSpan b))).map HVec.content))
    = (blockSpan a).length * (blockSpan b).length := by
  obtain ⟨hszP, hwidP, hclP, hiP⟩ := fusedSpan_pack a b hba
  have hrl := exhaust_rowList_shapeOf a.length
    (fusedAt (blockSpan a) (blockSpan b)) hszP hwidP hclP
  -- the counts are the fusion counts at the tops' own row lists
  have hcount : ground.famFold Nat.add 0
      (fun mu => countAt (fusedAt (blockSpan a) (blockSpan b)) mu
        * (blockSpan (shapeOf mu)).length)
      (ground.dedupL ((exhaust a.length
        (fusedAt (blockSpan a) (blockSpan b))).map HVec.content))
      = ground.famFold Nat.add 0
        (fun mu => fusionCount a b (shapeOf mu)
          * (blockSpan (shapeOf mu)).length)
        (ground.dedupL ((exhaust a.length
          (fusedAt (blockSpan a) (blockSpan b))).map
          HVec.content)) := by
    refine ground.famFold_congr_members Nat.add 0 _ _ _ ?_
    intro mu hmu
    rw [fusionCount_countAt a b (shapeOf mu) hba,
      hrl mu (ground.mem_of_dedupL
        (ground.mem_of_countOf_pos mu _ hmu))]
  -- the dimension reads the pool's own count
  have hprod : dimOf (fusedAt (blockSpan a) (blockSpan b))
      = (blockSpan a).length * (blockSpan b).length := by
    show ground.famFold Nat.add 0
      (fun mu => (elim.collectOf (places.monomialsAt mu).length
        (groupAt (fusedAt (blockSpan a) (blockSpan b)) mu)).length)
      (ground.dedupL
        ((fusedAt (blockSpan a) (blockSpan b)).map HVec.content))
      = _
    rw [ground.famFold_congr_members Nat.add 0 _
        (fun mu => ground.countOf mu
          ((fusedAt (blockSpan a) (blockSpan b)).map HVec.content))
        _ (fun mu _ => by
          show dimAt (fusedAt (blockSpan a) (blockSpan b)) mu
            = ground.countOf mu
              ((fusedAt (blockSpan a) (blockSpan b)).map HVec.content)
          rw [dimAt_occ (fusedAt (blockSpan a) (blockSpan b)) hiP mu,
            occ_eq_countOf]),
      ground.countOf_partition
        ((fusedAt (blockSpan a) (blockSpan b)).map HVec.content)
        (ground.dedupL
          ((fusedAt (blockSpan a) (blockSpan b)).map HVec.content))
        (fun x _ => ground.countOf_dedupL_le x _)
        (fun x hx => ground.mem_dedupL hx),
      ground.length_map HVec.content
        (fusedAt (blockSpan a) (blockSpan b)),
      length_fusedAt (blockSpan b) (blockSpan a)]
  rw [← hcount, ← dimOf_countAt a.length
      (fusedAt (blockSpan a) (blockSpan b)) hszP hwidP hclP,
    hprod]

/-- The fused pools' flip at stated data: the count reads one
value in either order, the pair lists' kernel dimensions one count
(`kernelDim_pairs_comm` at the pools' independence). -/
private theorem countAt_fused_comm (d kX kY : Nat)
    (X Y : List HVec) (cc : List Nat)
    (hwidX : ∀ v ∈ X, v.content.length = d)
    (hwidY : ∀ w ∈ Y, w.content.length = d)
    (hdegX : ∀ v ∈ X, sumNat v.content = kX)
    (hdegY : ∀ w ∈ Y, sumNat w.content = kY)
    (hiX : indepAll X) (hiY : indepAll Y) :
    countAt (fusedAt X Y) cc = countAt (fusedAt Y X) cc := by
  rw [countAt_pairs X Y cc
      (tensor_indep X Y cc d kX hwidX hwidY hdegX hiX hiY),
    countAt_pairs Y X cc
      (tensor_indep Y X cc d kY hwidY hwidX hdegY hiY hiX)]
  exact kernelDim_pairs_comm X Y cc d kX kY hwidX hwidY hdegX
    hdegY hiX hiY

set_option linter.unusedVariables false in
/-- The associativity display (`lem:blockcount`(iii)'s second
identity): the two pairings' sums read one value, each the triple
pool's count through the expansion — the first pairing at the
fused carrier's exhaustion, the second across the flip with the
composition associative at the arrangements' join
(`fusedAt_assoc`; `countAt_fused_comm`), the displays' folds the
fusion counts at the tops' own row lists.  Binders: `hba` and
`hca` are load-bearing with their committed refusals, a wider
factor at a second occupied letter parting the two sums; the
target's width `hea` is the frame, unrefusable — an off-width
target's row list empties both pair lists and both sums read the
sum's unit — its probe record the check module's. -/
theorem fusionCount_assoc (a b c e : Shape)
    (hba : b.length = a.length) (hca : c.length = a.length)
    (hea : e.length = a.length) :
    ground.famFold Nat.add 0
      (fun mu => fusionCount a b (places.shapeOf mu)
        * fusionCount (places.shapeOf mu) c e)
      (ground.dedupL
        ((exhaust a.length
          (fusedAt (blockSpan a) (blockSpan b))).map HVec.content))
    = ground.famFold Nat.add 0
      (fun mu => fusionCount b c (places.shapeOf mu)
        * fusionCount a (places.shapeOf mu) e)
      (ground.dedupL
        ((exhaust a.length
          (fusedAt (blockSpan b) (blockSpan c))).map
          HVec.content)) := by
  have hcb : c.length = b.length := hca.trans hba.symm
  obtain ⟨hszP1, hwidP1, hclP1, hiP1⟩ := fusedSpan_pack a b hba
  obtain ⟨hszP2, hwidP2b, hclP2b, hiP2⟩ := fusedSpan_pack b c hcb
  have hwidP2 : ∀ x ∈ fusedAt (blockSpan b) (blockSpan c),
      x.content.length = a.length :=
    fun x hx => (hwidP2b x hx).trans hba
  have hclP2 : ∀ x ∈ fusedAt (blockSpan b) (blockSpan c),
      ∀ i, i < a.length → ∀ j, j < a.length → ¬ i = j →
      settledAt (fusedAt (blockSpan b) (blockSpan c))
        (act i j x) :=
    fun x hx i hi j hj hij => hclP2b x hx i
      (by rw [hba]; exact hi) j (by rw [hba]; exact hj) hij
  have hdegP1 : ∀ x ∈ fusedAt (blockSpan a) (blockSpan b),
      sumNat x.content = degree a + degree b :=
    fusedAt_degree a.length (degree a) (degree b) _ _
      (blockSpan_width a)
      (fun w hw => (blockSpan_width b w hw).trans hba)
      (blockSpan_degree a) (blockSpan_degree b)
  have hdegP2 : ∀ x ∈ fusedAt (blockSpan b) (blockSpan c),
      sumNat x.content = degree b + degree c := by
    intro x hx
    refine fusedAt_degree b.length (degree b) (degree c) _ _
      (blockSpan_width b)
      (fun w hw => (blockSpan_width c w hw).trans hcb)
      (blockSpan_degree b) (blockSpan_degree c) x hx
  have hrl1 := exhaust_rowList_shapeOf a.length
    (fusedAt (blockSpan a) (blockSpan b)) hszP1 hwidP1 hclP1
  have hrl2 := exhaust_rowList_shapeOf a.length
    (fusedAt (blockSpan b) (blockSpan c)) hszP2 hwidP2 hclP2
  have hwidT1 : ∀ mu ∈ (exhaust a.length
      (fusedAt (blockSpan a) (blockSpan b))).map HVec.content,
      mu.length = a.length := by
    intro mu hmu
    match ground.mem_map_of HVec.content _ mu hmu with
    | ⟨w, hw, hwc⟩ =>
      rw [← hwc]
      exact (exhaust_top a.length _ hszP1 hwidP1 hclP1 w hw).2.1
  have hwidT2 : ∀ mu ∈ (exhaust a.length
      (fusedAt (blockSpan b) (blockSpan c))).map HVec.content,
      mu.length = a.length := by
    intro mu hmu
    match ground.mem_map_of HVec.content _ mu hmu with
    | ⟨w, hw, hwc⟩ =>
      rw [← hwc]
      exact (exhaust_top a.length _ hszP2 hwidP2 hclP2 w hw).2.1
  have hL : ground.famFold Nat.add 0
      (fun mu => fusionCount a b (places.shapeOf mu)
        * fusionCount (places.shapeOf mu) c e)
      (ground.dedupL
        ((exhaust a.length
          (fusedAt (blockSpan a) (blockSpan b))).map HVec.content))
      = countAt (fusedAt (fusedAt (blockSpan a) (blockSpan b))
          (blockSpan c)) (rowList e) := by
    rw [ground.famFold_congr_members Nat.add 0 _
      (fun mu => countAt (fusedAt (blockSpan a) (blockSpan b)) mu
        * countAt (fusedAt (blockSpan (places.shapeOf mu))
            (blockSpan c)) (rowList e))
      _ ?_]
    · exact (countAt_fused_exhaust a.length
        (degree a + degree b)
        (fusedAt (blockSpan a) (blockSpan b)) hszP1 hwidP1 hdegP1
        hclP1 (blockSpan c) (lowerspan.spanReads c).1
        (fun w hw => (blockSpan_width c w hw).trans hca)
        (fun w hw i hi j hj hij =>
          lowerspan.act_closed_def c i j
            (by rw [hca]; exact hi) (by rw [hca]; exact hj) hij
            w hw)
        (lowerspan.spanReads c).2.1 (rowList e)).symm
    · intro mu hmu
      have hmem := ground.mem_of_dedupL
        (ground.mem_of_countOf_pos mu _ hmu)
      have hlen : (places.shapeOf mu).length = a.length := by
        rw [length_shapeOf]
        exact hwidT1 mu hmem
      rw [fusionCount_countAt a b (places.shapeOf mu) hba,
        hrl1 mu hmem,
        fusionCount_countAt (places.shapeOf mu) c e
          (hca.trans hlen.symm)]
  have hR : ground.famFold Nat.add 0
      (fun mu => fusionCount b c (places.shapeOf mu)
        * fusionCount a (places.shapeOf mu) e)
      (ground.dedupL
        ((exhaust a.length
          (fusedAt (blockSpan b) (blockSpan c))).map HVec.content))
      = countAt (fusedAt (fusedAt (blockSpan b) (blockSpan c))
          (blockSpan a)) (rowList e) := by
    rw [ground.famFold_congr_members Nat.add 0 _
      (fun mu => countAt (fusedAt (blockSpan b) (blockSpan c)) mu
        * countAt (fusedAt (blockSpan (places.shapeOf mu))
            (blockSpan a)) (rowList e))
      _ ?_]
    · exact (countAt_fused_exhaust a.length
        (degree b + degree c)
        (fusedAt (blockSpan b) (blockSpan c)) hszP2 hwidP2 hdegP2
        hclP2 (blockSpan a) (lowerspan.spanReads a).1
        (blockSpan_width a)
        (fun w hw i hi j hj hij =>
          lowerspan.act_closed_def a i j hi hj hij w hw)
        (lowerspan.spanReads a).2.1 (rowList e)).symm
    · intro mu hmu
      have hmem := ground.mem_of_dedupL
        (ground.mem_of_countOf_pos mu _ hmu)
      have hlen : (places.shapeOf mu).length = a.length := by
        rw [length_shapeOf]
        exact hwidT2 mu hmem
      rw [fusionCount_countAt b c (places.shapeOf mu) hcb,
        hrl2 mu hmem,
        fusionCount_comm a (places.shapeOf mu) e hlen,
        fusionCount_countAt (places.shapeOf mu) a e hlen.symm]
  rw [hL, hR,
    fusedAt_assoc a.length (blockSpan b) (blockSpan c)
      (lowerspan.spanReads b).1 (lowerspan.spanReads c).1
      (fun w hw => (blockSpan_width b w hw).trans hba)
      (fun w hw => (blockSpan_width c w hw).trans hca)
      (blockSpan a) (lowerspan.spanReads a).1 (blockSpan_width a)]
  exact countAt_fused_comm a.length (degree a)
    (degree b + degree c) (blockSpan a)
    (fusedAt (blockSpan b) (blockSpan c)) (rowList e)
    (blockSpan_width a) hwidP2 (blockSpan_degree a) hdegP2
    (lowerspan.spanReads a).2.1
    (fused_indepAll b.length (degree b) _ _ (blockSpan_width b)
      (fun w hw => (blockSpan_width c w hw).trans hcb)
      (blockSpan_degree b) (lowerspan.spanReads b).2.1
      (lowerspan.spanReads c).2.1)

end blockcount
